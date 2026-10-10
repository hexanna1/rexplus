#pragma once
#include "completion_position.hpp"
#include <algorithm>
#include <array>
#include <bit>
#include <chrono>
#include <cstdint>
#include <deque>
#include <iostream>
#include <limits>
#include <memory>
#include <stdexcept>
#include <span>
#include <string>
#include <type_traits>
#include <vector>
#include "completion_kernel_bounds.hpp"
#include "completion_avoider.hpp"
#include "completion_edge_view.hpp"
#include "completion_label_folding.hpp"

namespace rexplus::completion {

struct Hypergraph
{
    std::uint32_t edge_block;
    std::uint32_t edge_offset;
    std::uint32_t edge_count;
    std::uint32_t active;
    std::array<std::uint8_t, 2> known{};
    std::array<std::uint8_t, 2> wins{};
};
static_assert(sizeof(Hypergraph) == 20);

struct PoolAllocation
{
    std::uint64_t limit = 0;
    std::uint64_t allocated = 0;

    void require(std::uint64_t bytes) const
    {
        if (limit && bytes > limit - allocated)
            throw SearchBudgetReached("pool");
    }

    void add(std::uint64_t bytes)
    {
        allocated += bytes;
    }
};

template <class T> struct PoolAllocator
{
    using value_type = T;
    PoolAllocation* allocation;

    explicit PoolAllocator(PoolAllocation* allocation) : allocation(allocation) {}
    template <class U>
    PoolAllocator(const PoolAllocator<U>& other) : allocation(other.allocation)
    {
    }

    T* allocate(std::size_t count)
    {
        const std::uint64_t bytes = count * sizeof(T);
        allocation->require(bytes);
        T* result = std::allocator<T>{}.allocate(count);
        allocation->add(bytes);
        return result;
    }

    void deallocate(T* data, std::size_t count) noexcept
    {
        std::allocator<T>{}.deallocate(data, count);
        allocation->allocated -= count * sizeof(T);
    }

    template <class U> bool operator==(const PoolAllocator<U>& other) const
    {
        return allocation == other.allocation;
    }
};

template <class Word> struct PoolEdgeDeleter
{
    PoolAllocation* allocation;
    std::uint32_t capacity;

    void operator()(Word* data) const noexcept
    {
        delete[] data;
        allocation->allocated -= std::uint64_t{capacity} * sizeof(Word);
    }
};

class HypergraphBlocks
{
public:
    explicit HypergraphBlocks(PoolAllocation* allocation)
        : allocation(allocation), blocks(PoolAllocator<Block>(allocation))
    {
    }

    std::size_t size() const
    {
        return count;
    }

    Hypergraph& operator[](std::size_t id)
    {
        return blocks[id >> BlockBits].get()[id & (BlockSize - 1)];
    }

    const Hypergraph& operator[](std::size_t id) const
    {
        return blocks[id >> BlockBits].get()[id & (BlockSize - 1)];
    }

    void push_back(Hypergraph graph)
    {
        if (!(count & (BlockSize - 1)))
        {
            // Fixed blocks avoid reserving a second large graph array while
            // the first one is still charged against the physical pool cap.
            constexpr auto bytes = std::uint64_t{BlockSize} * sizeof(Hypergraph);
            allocation->require(bytes);
            auto* data = std::allocator<Hypergraph>{}.allocate(BlockSize);
            allocation->add(bytes);
            Block block(data, Deleter{allocation});
            blocks.push_back(std::move(block));
        }
        std::construct_at(blocks.back().get() + (count & (BlockSize - 1)), graph);
        ++count;
    }

private:
    static constexpr unsigned BlockBits = 16;
    static constexpr std::uint32_t BlockSize = 1U << BlockBits;

    struct Deleter
    {
        PoolAllocation* allocation;
        void operator()(Hypergraph* data) const noexcept
        {
            std::allocator<Hypergraph>{}.deallocate(data, BlockSize);
            allocation->allocated -= std::uint64_t{BlockSize} * sizeof(Hypergraph);
        }
    };

    using Block = std::unique_ptr<Hypergraph[], Deleter>;
    static_assert(std::is_trivially_destructible_v<Hypergraph>);
    PoolAllocation* allocation;
    std::vector<Block, PoolAllocator<Block>> blocks;
    std::size_t count = 0;
};

class HypergraphPool
{
public:
    explicit HypergraphPool(std::uint64_t byte_limit = 0, bool fold_labels = false)
        : allocation{byte_limit}, fold_labels(fold_labels), graphs(&allocation),
          edge_blocks(PoolAllocator<EdgeBlock<std::uint32_t>>(&allocation)),
          short_edge_blocks(PoolAllocator<EdgeBlock<std::uint16_t>>(&allocation)),
          medium_edge_blocks(PoolAllocator<EdgeBlock<PackedEdge24>>(&allocation)),
          index_hashes(PoolAllocator<std::uint32_t>(&allocation)),
          index_ids(PoolAllocator<std::uint32_t>(&allocation))
    {
    }

    std::uint32_t intern(std::vector<std::uint32_t> edges)
    {
        return intern(std::span<std::uint32_t>(edges));
    }

    std::uint32_t intern(std::span<std::uint32_t> edges)
    {
        // Packing preserves numeric edge order.
        std::uint32_t support = 0;
        for (std::uint32_t edge : edges)
            support |= edge;
        if (support & (support + 1))
        {
            const auto width = std::bit_width(support);
            std::uint32_t holes =
                width == 32 ? ~support : ((std::uint32_t{1} << width) - 1) & ~support;
            // Delete missing labels from high to low. Whole-edge shifts
            // preserve order and avoid visiting every set bit of every edge.
            while (holes)
            {
                const auto hole = std::bit_width(holes) - 1;
                const std::uint32_t low = (std::uint32_t{1} << hole) - 1;
                for (auto& edge : edges)
                    edge = (edge & low) | ((edge >> 1) & ~low);
                holes &= ~(std::uint32_t{1} << hole);
            }
        }
        if (fold_labels)
            completion_label_folding::relabel(edges, std::popcount(support));
        const std::uint32_t hash = edge_hash(edges);
        if (index_hashes.empty())
            resize_index(1024);
        if (const std::uint32_t found = find(hash, edges); found != Missing)
            return found;
        if constexpr (sizeof(std::size_t) > sizeof(std::uint32_t))
            if (graphs.size() >= std::uint64_t{1} << 32)
                throw std::overflow_error("too many distinct hypergraphs");
        if (((graphs.size() + 1) * 4) > (index_hashes.size() * 3))
            resize_index(index_hashes.size() * 2);
        std::uint32_t active = 0;
        for (std::uint32_t edge : edges)
            active |= edge;
        const auto id = static_cast<std::uint32_t>(graphs.size());
        const auto [block, offset] = active <= 0xffff ? append_edges(edges, short_edge_blocks)
                                     : active <= 0xffffff
                                         ? append_edges(edges, medium_edge_blocks)
                                         : append_edges(edges, edge_blocks);
        graphs.push_back(
            Hypergraph{block, offset, static_cast<std::uint32_t>(edges.size()), active});
        insert_index(hash, id);
        return id;
    }

    std::uint32_t lookup(std::span<const std::uint32_t> edges) const
    {
        return find(edge_hash(edges), edges);
    }

    Hypergraph& operator[](std::uint32_t id)
    {
        return graphs[id];
    }

    const Hypergraph& operator[](std::uint32_t id) const
    {
        return graphs[id];
    }

    DecodedEdges edges(std::uint32_t id) const
    {
        const Hypergraph& graph = graphs[id];
        if (graph.active <= 0xffff)
            return DecodedEdges(std::span<const std::uint16_t>(
                short_edge_blocks[graph.edge_block].data.get() + graph.edge_offset,
                graph.edge_count));
        if (graph.active <= 0xffffff)
            return DecodedEdges(std::span<const PackedEdge24>(
                medium_edge_blocks[graph.edge_block].data.get() + graph.edge_offset,
                graph.edge_count));
        return DecodedEdges(std::span<const std::uint32_t>(
            edge_blocks[graph.edge_block].data.get() + graph.edge_offset, graph.edge_count));
    }

    std::uint64_t size() const
    {
        return graphs.size();
    }

private:
    static constexpr std::uint32_t Missing = std::numeric_limits<std::uint32_t>::max();
    static constexpr std::uint32_t EdgeBlockWords = 1 << 20;

    template <class Word> struct EdgeBlock
    {
        std::unique_ptr<Word[], PoolEdgeDeleter<Word>> data;
        std::uint32_t capacity;
        std::uint32_t used;
    };

    template <class Word> static std::uint64_t hash_edges(std::span<Word> edges)
    {
        std::uint64_t value = edges.size();
        for (std::uint32_t edge : edges)
            value = (value ^ edge) * 0x9e3779b97f4a7c15ULL;
        value ^= value >> 30;
        value *= 0xbf58476d1ce4e5b9ULL;
        value ^= value >> 27;
        value *= 0x94d049bb133111ebULL;
        return value ^ (value >> 31);
    }

    template <class Word> static std::uint32_t edge_hash(std::span<Word> edges)
    {
        const std::uint32_t hash = hash_edges(edges);
        return hash ? hash : 1;
    }

    std::uint32_t find(std::uint32_t hash, std::span<const std::uint32_t> sought) const
    {
        const std::size_t mask = index_hashes.size() - 1;
        std::size_t slot = hash & mask;
        while (index_hashes[slot])
        {
            const std::uint32_t id = index_ids[slot];
            if (index_hashes[slot] == hash && equal_edges(id, sought))
                return id;
            slot = (slot + 1) & mask;
        }
        return Missing;
    }

    void insert_index(std::uint32_t hash, std::uint32_t id)
    {
        const std::size_t mask = index_hashes.size() - 1;
        std::size_t slot = hash & mask;
        while (index_hashes[slot])
            slot = (slot + 1) & mask;
        index_hashes[slot] = hash;
        index_ids[slot] = id;
    }

    void resize_index(std::size_t capacity)
    {
        // Refusal retains the current index. Transfer fingerprints when both
        // tables fit; otherwise release the old arrays and reconstruct them
        // from immutable families without a temporary allocation overlap.
        const auto released = std::uint64_t{sizeof(std::uint32_t)}
                              * (index_hashes.capacity() + index_ids.capacity());
        const auto replacement = std::uint64_t{sizeof(std::uint32_t)} * capacity * 2;
        allocation.require(replacement - released);
        if (!allocation.limit || replacement <= allocation.limit - allocation.allocated)
        {
            auto transferred_hashes = std::move(index_hashes);
            auto transferred_ids = std::move(index_ids);
            index_hashes.assign(capacity, 0);
            index_ids.resize(capacity);
            for (std::size_t slot = 0; slot < transferred_hashes.size(); ++slot)
                if (transferred_hashes[slot])
                    insert_index(transferred_hashes[slot], transferred_ids[slot]);
            return;
        }
        {
            decltype(index_hashes) release_hashes(index_hashes.get_allocator());
            decltype(index_ids) release_ids(index_ids.get_allocator());
            release_hashes.swap(index_hashes);
            release_ids.swap(index_ids);
        }
        index_hashes.assign(capacity, 0);
        index_ids.resize(capacity);
        for (std::uint32_t id = 0; id < graphs.size(); ++id)
        {
            const auto& graph = graphs[id];
            std::uint32_t hash;
            if (graph.active <= 0xffff)
            {
                const auto* first =
                    short_edge_blocks[graph.edge_block].data.get() + graph.edge_offset;
                hash = edge_hash(std::span<const std::uint16_t>(first, graph.edge_count));
            }
            else if (graph.active <= 0xffffff)
            {
                const auto* first =
                    medium_edge_blocks[graph.edge_block].data.get() + graph.edge_offset;
                hash = edge_hash(std::span<const PackedEdge24>(first, graph.edge_count));
            }
            else
            {
                const auto* first =
                    edge_blocks[graph.edge_block].data.get() + graph.edge_offset;
                hash = edge_hash(std::span<const std::uint32_t>(first, graph.edge_count));
            }
            insert_index(hash, id);
        }
    }

    bool equal_edges(std::uint32_t id, std::span<const std::uint32_t> sought) const
    {
        const auto& graph = graphs[id];
        if (graph.edge_count != sought.size())
            return false;
        if (graph.active <= 0xffff)
        {
            const auto* first =
                short_edge_blocks[graph.edge_block].data.get() + graph.edge_offset;
            return std::equal(first, first + graph.edge_count, sought.begin());
        }
        if (graph.active <= 0xffffff)
        {
            const auto* first =
                medium_edge_blocks[graph.edge_block].data.get() + graph.edge_offset;
            return std::equal(first, first + graph.edge_count, sought.begin());
        }
        const auto* first = edge_blocks[graph.edge_block].data.get() + graph.edge_offset;
        return std::equal(first, first + graph.edge_count, sought.begin());
    }

    template <class Word>
    std::pair<std::uint32_t, std::uint32_t>
    reserve_edges(std::uint32_t count,
                  std::vector<EdgeBlock<Word>, PoolAllocator<EdgeBlock<Word>>>& blocks)
    {
        if (blocks.empty() || blocks.back().capacity - blocks.back().used < count)
        {
            if constexpr (sizeof(std::size_t) > sizeof(std::uint32_t))
                if (blocks.size() >= std::uint64_t{1} << 32)
                    throw std::overflow_error("too many hypergraph edge blocks");
            const std::uint32_t capacity = std::max(EdgeBlockWords, count);
            const std::uint64_t bytes = std::uint64_t{capacity} * sizeof(Word);
            allocation.require(bytes);
            auto data = std::make_unique_for_overwrite<Word[]>(capacity);
            allocation.add(bytes);
            blocks.push_back(
                {{data.release(), PoolEdgeDeleter<Word>{&allocation, capacity}}, capacity, 0});
        }
        auto& block = blocks.back();
        const std::uint32_t offset = block.used;
        block.used += count;
        return {static_cast<std::uint32_t>(blocks.size() - 1), offset};
    }

    template <class Word>
    std::pair<std::uint32_t, std::uint32_t>
    append_edges(std::span<const std::uint32_t> edges,
                 std::vector<EdgeBlock<Word>, PoolAllocator<EdgeBlock<Word>>>& blocks)
    {
        if (edges.size() > std::numeric_limits<std::uint32_t>::max())
            throw std::overflow_error("hypergraph has too many edges");
        const auto location = reserve_edges(static_cast<std::uint32_t>(edges.size()), blocks);
        std::copy(
            edges.begin(), edges.end(), blocks[location.first].data.get() + location.second);
        return location;
    }

    PoolAllocation allocation;
    bool fold_labels;
    // Recursive calls retain IDs and edge-block spans, never graph references.
    HypergraphBlocks graphs;
    std::vector<EdgeBlock<std::uint32_t>, PoolAllocator<EdgeBlock<std::uint32_t>>> edge_blocks;
    std::vector<EdgeBlock<std::uint16_t>, PoolAllocator<EdgeBlock<std::uint16_t>>>
        short_edge_blocks;
    std::vector<EdgeBlock<PackedEdge24>, PoolAllocator<EdgeBlock<PackedEdge24>>>
        medium_edge_blocks;
    std::vector<std::uint32_t, PoolAllocator<std::uint32_t>> index_hashes;
    std::vector<std::uint32_t, PoolAllocator<std::uint32_t>> index_ids;
};

namespace completion_bounds {
using Edge = std::uint32_t;
constexpr std::uint64_t Half = std::uint64_t{1} << 31;
constexpr std::uint64_t weight(Edge edge)
{
    return std::uint64_t{1} << (32 - std::popcount(edge));
}
struct Certificate
{
    int winner = -1; // 0 White, 1 Black
    std::array<Edge, 32> edges{};
    std::size_t count = 0;
};

inline Certificate bound(std::span<const Edge> edges, std::vector<Edge>& order)
{
    Certificate result;
    Edge active = 0;
    int smallest = 32;
    for (auto edge : edges)
    {
        active |= edge;
        smallest = std::min(smallest, std::popcount(edge));
    }
    // Each selected edge contributes at most 2^-smallest per smallest
    // vertices. If this packing upper bound is at most one half, no
    // disjoint subfamily can certify the Black bound.
    // A disjoint subfamily weakens White's connection predicate. Its
    // Black-only value therefore bounds the full family in Black's favor.
    if (std::uint64_t(std::popcount(active)) > smallest * (std::uint64_t{1} << (smallest - 1)))
    {
        order.assign(edges.begin(), edges.end());
        std::sort(order.begin(), order.end(), [](Edge a, Edge b) {
            const int sa = std::popcount(a), sb = std::popcount(b);
            return sa != sb ? sa < sb : a < b;
        });
        Edge used = 0;
        std::uint64_t total = 0;
        for (auto edge : order)
        {
            if (used & edge)
                continue;
            used |= edge;
            total += weight(edge);
            result.edges[result.count++] = edge;
            if (total > Half)
            {
                result.winner = 1;
                return result;
            }
            if (std::popcount(active & ~used) < smallest)
                break;
        }
    }

    result.count = 0;
    // Component cores strengthen the predicate: every original edge
    // contains its component's core. A White-only core game bounds the
    // original in White's favor. Distinct component cores are disjoint.
    std::array<Edge, 32> component{}, core{};
    std::size_t count = 0;
    for (auto edge : edges)
    {
        Edge vertices = edge, intersection = edge;
        for (std::size_t i = 0; i < count;)
        {
            if (!(component[i] & vertices))
            {
                ++i;
                continue;
            }
            vertices |= component[i];
            intersection &= core[i];
            --count;
            component[i] = component[count];
            core[i] = core[count];
        }
        // Further intersections cannot restore a lost vertex. An empty
        // core fails; a singleton core already weighs one half.
        if (std::popcount(intersection) < 2)
            return result;
        component[count] = vertices;
        core[count++] = intersection;
    }
    std::uint64_t total = 0;
    for (std::size_t i = 0; i < count; ++i)
        total += weight(core[i]);
    if (total < Half)
    {
        result.winner = 0;
        result.count = count;
        std::copy_n(core.begin(), count, result.edges.begin());
    }
    return result;
}

inline Edge winning_batch(Edge remaining, const Certificate& certificate)
{
    Edge active = 0, largest = 0;
    for (std::size_t i = 0; i < certificate.count; ++i)
    {
        const auto edge = certificate.edges[i];
        active |= edge;
        if (std::popcount(edge) > std::popcount(largest))
            largest = edge;
    }
    // Removing a largest disjoint edge or shortening a largest core changes
    // dyadic weight by its smallest unit, at most the distance to one half.
    // Consume all other physical cells outside the residual support before
    // handing over: equality leaves an active P, without a dead option.
    if (certificate.winner == 1)
        return remaining & ~(active & ~largest);
    return (remaining & ~active) | (largest & -largest);
}
} // namespace completion_bounds

// In an antichain, an unchanged F disappears after White takes c exactly
// when E\F={c} for some original E. Intersecting the incidence sets of all
// vertices of E except c finds those F for every c together. The caller
// supplies at most 64 edges, so each incidence set fits in one word.
inline void white_cofactor_omissions(std::span<const std::uint32_t> edges,
                              std::array<std::uint64_t, 32>& omitted)
{
    std::array<std::uint64_t, 32> incidence{};
    omitted.fill(0);
    for (std::size_t i = 0; i < edges.size(); ++i)
        for (auto work = edges[i]; work; work &= work - 1)
            incidence[std::countr_zero(work)] |= std::uint64_t{1} << i;
    const auto all =
        edges.size() == 64 ? ~std::uint64_t{0} : (std::uint64_t{1} << edges.size()) - 1;
    for (auto edge : edges)
    {
        std::array<unsigned, 32> cells;
        std::array<std::uint64_t, 33> prefix;
        unsigned count = 0;
        prefix[0] = all;
        for (auto work = edge; work; work &= work - 1)
        {
            const auto cell = std::countr_zero(work);
            cells[count] = cell;
            prefix[count + 1] = prefix[count] & incidence[cell];
            ++count;
        }
        auto suffix = all;
        while (count)
        {
            const auto cell = cells[--count];
            omitted[cell] |= prefix[count] & suffix & ~incidence[cell];
            suffix &= incidence[cell];
        }
    }
}

enum class CertificatePolicy { All, Proof };

class ProofExporter;

class Solver
{
public:
    explicit Solver(std::uint64_t pool_byte_limit = 0,
                    CertificatePolicy certificate_policy = CertificatePolicy::All,
                    bool fold_labels = false)
        : pool(pool_byte_limit, fold_labels), certificate_policy(certificate_policy)
    {
    }

    void begin_query(double seconds = 0)
    {
        budget = SearchBudget(seconds);
        query_calls = 0;
    }

    const SearchBudget& query_budget() const { return budget; }

    bool
    solve(std::uint32_t remaining, const std::vector<std::uint32_t>& edges, bool black_turn)
    {
        check_time();
        std::uint32_t active = 0;
        for (std::uint32_t edge : edges)
            active |= edge;
        const std::uint32_t id = pool.intern(edges);
        return win(id, (remaining & ~active) != 0, black_turn);
    }

    std::uint64_t states() const
    {
        return solved_states;
    }
    std::uint64_t hypergraphs() const
    {
        return pool.size();
    }
    std::uint32_t
    winning_batch(std::uint32_t remaining, std::vector<std::uint32_t> edges, bool black_turn)
    {
        if (!solve(remaining, edges, black_turn))
            return 0;
        if (certificate_policy == CertificatePolicy::All)
        {
            if (!black_turn && completion_avoider::white_only(edges))
                return completion_avoider::white_batch(remaining, edges);
            const auto kernel = completion_kernels::bound(edges);
            if (kernel.winner == int(black_turn))
                return remaining & ~kernel.keep;
        }
        const auto certificate = completion_bounds::bound(edges, bound_order);
        if (certificate.winner == int(black_turn))
            return completion_bounds::winning_batch(remaining, certificate);
        std::uint32_t batch = 0;
        for (;;)
        {
            std::uint32_t active = 0;
            for (std::uint32_t edge : edges)
                active |= edge;
            const std::uint32_t dead = remaining & ~active;
            bool continued = false;
            // Witnesses use physical labels; value queries pack them.
            std::vector<std::uint32_t> choices;
            if (dead)
                choices.push_back(dead & -dead);
            for (auto work = active; work; work &= work - 1)
                choices.push_back(work & -work);
            for (std::uint32_t cell : choices)
            {
                const std::uint32_t taken = cell & dead ? dead : cell;
                std::vector<std::uint32_t> child;
                if (cell & dead)
                    child = edges;
                else if (black_turn)
                {
                    child = black_child(edges, cell);
                    if (child.empty())
                        continue;
                }
                else
                {
                    bool legal;
                    child = white_child(edges, cell, legal);
                    if (!legal)
                        continue;
                }
                const std::uint32_t rest = remaining & ~taken;
                if (!solve(rest, child, !black_turn))
                    return batch | taken;
                if (solve(rest, child, black_turn))
                {
                    batch |= taken;
                    remaining = rest;
                    edges = std::move(child);
                    continued = true;
                    break;
                }
            }
            if (!continued)
                throw std::logic_error("winning state has no winning batch");
        }
    }

private:
    friend class ProofExporter;

    static std::vector<std::uint32_t>
    white_child(std::span<const std::uint32_t> edges, std::uint32_t cell, bool& legal)
    {
        std::vector<std::uint32_t> result;
        result.reserve(edges.size());
        legal = true;
        for (std::uint32_t edge : edges)
        {
            if (!(edge & cell))
                continue;
            if (edge == cell)
            {
                legal = false;
                return {};
            }
            result.push_back(edge & ~cell);
        }
        const auto reduced_count = result.size();
        for (std::uint32_t edge : edges)
        {
            if (edge & cell)
                continue;
            bool dominated = false;
            for (std::size_t i = 0; i < reduced_count; ++i)
                if (!(result[i] & ~edge))
                {
                    dominated = true;
                    break;
                }
            if (!dominated)
                result.push_back(edge);
        }
        std::inplace_merge(result.begin(), result.begin() + reduced_count, result.end());
        return result;
    }

    static std::vector<std::uint32_t> black_child(std::span<const std::uint32_t> edges,
                                                  std::uint32_t cell)
    {
        std::vector<std::uint32_t> result;
        result.reserve(edges.size());
        for (std::uint32_t edge : edges)
            if (!(edge & cell))
                result.push_back(edge);
        return result;
    }

    // Classify the continue/end predicate while constructing a legal child.
    // Q(turn) = !F(opponent) || F(turn) is unchanged by physical dead cells.
    // A singleton makes an active game Black-only unless it is the sole cell
    // (P); a common vertex makes it White-only. Unknown families are interned.
    struct ElementaryChild
    {
        std::uint32_t common = ~std::uint32_t{0};
        bool singleton = false;
        std::uint32_t add(std::uint32_t edge)
        {
            common &= edge;
            singleton |= std::has_single_bit(edge);
            return edge;
        }
        std::uint32_t add_black(std::uint32_t edge)
        {
            // Deleting entire terms cannot create a singleton.
            common &= edge;
            return edge;
        }
        int q(std::span<const std::uint32_t> edges, bool black_turn) const
        {
            if (edges.size() == 1 && std::has_single_bit(edges[0]))
                return 1; // Active P: either mover can end here.
            if (singleton)
                return black_turn;
            if (common)
                return !black_turn;
            return -1;
        }
    };
    static int elementary_child_q(std::span<const std::uint32_t> edges, bool black_turn)
    {
        ElementaryChild summary;
        for (auto edge : edges)
            if (black_turn)
                summary.add_black(edge);
            else
                summary.add(edge);
        return summary.q(edges, black_turn);
    }

    bool win(std::uint32_t id, bool isolates, bool black_turn)
    {
        if (budget.limited() && (query_calls++ & 1023) == 0)
            check_time();
        const int turn = black_turn ? 1 : 0;
        const std::uint8_t state = std::uint8_t{1} << isolates;
        if (pool[id].known[turn] & state)
            return pool[id].wins[turn] & state;

        // Dead cells preserve the continue/end predicate.
        if (isolates)
        {
            const bool result = !win(id, false, !black_turn) || win(id, false, black_turn);
            remember(id, turn, state, result);
            return result;
        }

        const std::uint32_t active = pool[id].active;
        const auto frame_storage = pool.edges(id);
        const auto frame_edges = frame_storage.view();
        // Avoid rescanning once the opposite active outcome is known.
        // Partial deductions can leave useful cutoffs untried here.
        if (!(pool[id].known[!turn] & 1))
        {
            // A common vertex lets White leave only that vertex; a singleton
            // edge lets Black do the same. Neither player can win a one-cell
            // active game. These are start-of-turn values without dead cells.
            std::uint32_t common = active;
            std::uint32_t seen = 0;
            int maximum_size = 0;
            bool singleton = false;
            bool disjoint = true;
            std::uint64_t avoider_mass = 0;
            for (std::uint32_t edge : frame_edges)
            {
                common &= edge;
                singleton |= std::has_single_bit(edge);
                disjoint &= !(seen & edge);
                seen |= edge;
                maximum_size = std::max(maximum_size, std::popcount(edge));
                if (avoider_mass <= completion_avoider::Half)
                    avoider_mass += std::uint64_t{1} << (32 - std::popcount(edge));
            }
            if (std::has_single_bit(active) || singleton || common || (disjoint && active))
            {
                bool black_wins = false;
                bool white_wins = false;
                if (!std::has_single_bit(active))
                {
                    if (singleton)
                        black_wins = true;
                    else if (common)
                        white_wins = true;
                    else
                    {
                        // Disjoint edges have dyadic weight sum 2^(-|edge|).
                        // Relative to one half: greater favors Black, smaller
                        // favors White, and equality is a P-position.
                        std::uint64_t weight = 0;
                        for (std::uint32_t edge : frame_edges)
                            weight += std::uint64_t{1} << (maximum_size - std::popcount(edge));
                        const auto half = std::uint64_t{1} << (maximum_size - 1);
                        black_wins = weight > half;
                        white_wins = weight < half;
                    }
                }
                remember(id, 1, state, black_wins);
                remember(id, 0, state, white_wins);
                return black_turn ? black_wins : white_wins;
            }
            if (avoider_mass < completion_avoider::Half)
            {
                remember(id, 1, state, false);
                remember(id, 0, state, true);
                return !black_turn;
            }
            if (avoider_mass == completion_avoider::Half)
            {
                // Every active Black placement deletes positive mass,
                // leaving the strict White-only potential criterion.
                remember(id, 1, state, false);
                if (black_turn)
                    return false;
            }
            const auto kernel = completion_kernels::bound(frame_edges);
            if (kernel.winner != -1
                && (certificate_policy == CertificatePolicy::All
                    || std::popcount(kernel.keep) <= 5))
            {
                remember(id, 1, state, kernel.winner == 1);
                remember(id, 0, state, kernel.winner == 0);
                return kernel.winner == int(black_turn);
            }
            const auto certificate = completion_bounds::bound(frame_edges, bound_order);
            if (certificate.winner != -1)
            {
                remember(id, 1, state, certificate.winner == 1);
                remember(id, 0, state, certificate.winner == 0);
                return certificate.winner == int(black_turn);
            }
        }
        const auto potential = completion_avoider::one_step(frame_edges, !black_turn);
        if (potential.black_loses)
        {
            remember(id, 1, state, false);
            if (potential.white_wins)
                remember(id, 0, state, true);
            if (black_turn || potential.white_wins)
                return !black_turn;
        }
        // Dyadic completion mass ranks choices without changing their values.
        // Small games cost less to solve in their existing label order.
        std::array<unsigned, 32> choices;
        unsigned choice_count = 0, choice_index = 0;
        if (std::popcount(active) > 7)
        {
            std::array<std::uint64_t, 32> influence{};
            for (auto edge : frame_edges)
            {
                const auto weight = std::uint64_t{1} << (32 - std::popcount(edge));
                for (auto work = edge; work; work &= work - 1)
                    influence[std::countr_zero(work)] += weight;
            }
            for (auto work = active; work; work &= work - 1)
                choices[choice_count++] = std::countr_zero(work);
            std::sort(choices.begin(), choices.begin() + choice_count, [&](auto a, auto b) {
                return influence[a] != influence[b] ? influence[a] < influence[b] : a < b;
            });
        }
        std::array<std::uint64_t, 32> omitted;
        bool omissions_ready = false;
        unsigned white_choices = 0;
        for (auto work = active; work;)
        {
            std::uint32_t cell;
            if (choice_count)
            {
                do
                {
                    cell = std::uint32_t{1} << choices[choice_index++];
                } while (!(work & cell));
            }
            else
                cell = work & -work;
            // If every edge containing this cell also contains v, taking
            // this cell is at least as good as taking v for either player.
            std::uint32_t dominated = active;
            for (std::uint32_t edge : frame_edges)
            {
                if (edge & cell)
                    dominated &= edge;
                if (dominated == cell)
                    break;
            }
            work &= ~dominated;
            std::uint32_t child_id;
            const auto edges = frame_edges;
            constexpr std::size_t StackEdges = 64;
            if (edges.size() <= StackEdges)
            {
                // Every used entry is written before access. Only the used
                // prefixes enter the merge and the persistent pool.
                ElementaryChild summary;
                std::array<std::uint32_t, StackEdges> child, reduced, unchanged;
                std::size_t count = 0;
                if (black_turn)
                {
                    for (auto edge : edges)
                        if (!(edge & cell))
                            child[count++] = summary.add_black(edge);
                    if (!count)
                        continue;
                }
                else
                {
                    std::size_t reduced_count = 0, unchanged_count = 0;
                    bool legal = true;
                    // Share minimization across several White cofactors.
                    // Delay construction while a short search can still win.
                    ++white_choices;
                    if (!omissions_ready && white_choices >= 3 && edges.size() >= 12
                        && std::popcount(work) >= 3)
                    {
                        white_cofactor_omissions(edges, omitted);
                        omissions_ready = true;
                    }
                    if (omissions_ready)
                    {
                        const auto all = edges.size() == 64
                                             ? ~std::uint64_t{0}
                                             : (std::uint64_t{1} << edges.size()) - 1;
                        for (auto keep = all & ~omitted[std::countr_zero(cell)]; keep;
                             keep &= keep - 1)
                        {
                            const auto edge = edges[std::countr_zero(keep)];
                            if (edge == cell)
                            {
                                legal = false;
                                break;
                            }
                            if (edge & cell)
                                reduced[reduced_count++] = summary.add(edge & ~cell);
                            else
                                unchanged[unchanged_count++] = summary.add(edge);
                        }
                    }
                    else
                    {
                        for (auto edge : edges)
                        {
                            if (!(edge & cell))
                                continue;
                            if (edge == cell)
                            {
                                legal = false;
                                break;
                            }
                            reduced[reduced_count++] = summary.add(edge & ~cell);
                        }
                        if (!legal)
                            continue;
                        for (auto edge : edges)
                        {
                            if (edge & cell)
                                continue;
                            bool dominated = false;
                            for (std::size_t j = 0; j < reduced_count; ++j)
                                if (!(reduced[j] & ~edge))
                                {
                                    dominated = true;
                                    break;
                                }
                            if (!dominated)
                                unchanged[unchanged_count++] = summary.add(edge);
                        }
                    }
                    if (!legal)
                        continue;
                    std::merge(reduced.begin(),
                               reduced.begin() + reduced_count,
                               unchanged.begin(),
                               unchanged.begin() + unchanged_count,
                               child.begin());
                    count = reduced_count + unchanged_count;
                }
                if (certificate_policy == CertificatePolicy::All)
                {
                    const int q = summary.q(std::span<const std::uint32_t>(child.data(), count),
                                            black_turn);
                    if (q != -1)
                    {
                        if (q)
                        {
                            remember(id, turn, state, true);
                            return true;
                        }
                        continue;
                    }
                }
                child_id = pool.intern(std::span<std::uint32_t>(child.data(), count));
            }
            else
            {
                std::vector<std::uint32_t> child;
                if (black_turn)
                {
                    child = black_child(edges, cell);
                    if (child.empty())
                        continue;
                }
                else
                {
                    bool legal;
                    child = white_child(edges, cell, legal);
                    if (!legal)
                        continue;
                }
                if (certificate_policy == CertificatePolicy::All)
                {
                    const int q = elementary_child_q(child, black_turn);
                    if (q != -1)
                    {
                        if (q)
                        {
                            remember(id, turn, state, true);
                            return true;
                        }
                        continue;
                    }
                }
                child_id = pool.intern(std::move(child));
            }
            if (!win(child_id, false, !black_turn) || win(child_id, false, black_turn))
            {
                remember(id, turn, state, true);
                // Unfilling the winner's own stone preserves a color-only
                // child, including any newly dead physical options.
                if (!(pool[id].known[!turn] & state) && (pool[child_id].known[turn] & 1)
                    && (pool[child_id].wins[turn] & 1) && (pool[child_id].known[!turn] & 1)
                    && !(pool[child_id].wins[!turn] & 1))
                    remember(id, !turn, state, false);
                return true;
            }
        }
        remember(id, turn, state, false);
        return false;
    }

    void remember(std::uint32_t id, int turn, std::uint8_t state, bool win)
    {
        Hypergraph& graph = pool[id];
        graph.known[turn] |= state;
        if (win)
            graph.wins[turn] |= state;
        ++solved_states;
    }

    void check_time() const { budget.check(); }

    HypergraphPool pool;
    CertificatePolicy certificate_policy;
    std::vector<std::uint32_t> bound_order;
    std::uint64_t solved_states = 0;
    std::uint64_t query_calls = 0;
    SearchBudget budget;
};

} // namespace rexplus::completion
