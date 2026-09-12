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
#include <vector>

namespace {

int Size;
int Cells;
std::uint64_t Board;
std::uint64_t InitialBlack;
std::uint64_t InitialWhite;
std::uint64_t Empty;
int EmptyCells;
std::uint32_t CompactMask;
std::uint64_t Left;
std::uint64_t Right;

constexpr std::uint64_t bit(int point) { return std::uint64_t{1} << point; }

std::vector<std::uint64_t> make_neighbors()
{
    std::vector<std::uint64_t> result(Cells);
    constexpr std::array<std::pair<int, int>, 6> directions{{
        {0, 1}, {0, -1}, {1, 0}, {-1, 0}, {-1, 1}, {1, -1}}};
    for (int point = 0; point < Cells; ++point)
    {
        const int row = point / Size;
        const int column = point % Size;
        for (auto [dr, dc] : directions)
            if (const int rr = row + dr, cc = column + dc;
                rr >= 0 && rr < Size && cc >= 0 && cc < Size)
                result[point] |= bit(rr * Size + cc);
    }
    return result;
}

std::vector<std::uint64_t> Neighbors;

bool connected(std::uint64_t stones, int color)
{
    const std::uint64_t first = color == 0 ? bit(Size) - 1 : Left;
    const std::uint64_t second = color == 0
        ? first << (Cells - Size) : Right;
    std::uint64_t frontier = stones & first;
    std::uint64_t seen = frontier;
    while (frontier)
    {
        if (frontier & second)
            return true;
        std::uint64_t adjacent = 0;
        for (auto work = frontier; work; work &= work - 1)
            adjacent |= Neighbors[std::countr_zero(work)];
        frontier = adjacent & stones & ~seen;
        seen |= frontier;
    }
    return false;
}

std::vector<std::uint64_t> make_empty_cells()
{
    std::vector<std::uint64_t> result;
    result.reserve(EmptyCells);
    for (auto work = Empty; work; work &= work - 1)
        result.push_back(work & -work);
    return result;
}

std::vector<std::uint64_t> EmptyCell;

std::uint64_t expand(std::uint32_t compact)
{
    std::uint64_t result = 0;
    for (auto work = compact; work; work &= work - 1)
        result |= EmptyCell[std::countr_zero(work)];
    return result;
}

std::string board_names(std::uint64_t stones)
{
    std::string result;
    for (auto work = stones; work; work &= work - 1)
    {
        const int point = std::countr_zero(work);
        if (!result.empty())
            result += ',';
        result += char('a' + point % Size);
        result += std::to_string(point / Size + 1);
    }
    return result.empty() ? "-" : result;
}

std::string names(std::uint32_t compact)
{
    return board_names(expand(compact));
}

std::vector<std::uint32_t> minimal_completions()
{
    std::array<std::uint32_t, 64> weight{};
    for (int i = 0; i < EmptyCells; ++i)
        weight[std::countr_zero(EmptyCell[i])] = std::uint32_t{1} << i;
    std::array<std::vector<std::uint32_t>, 64> carriers;
    std::deque<std::pair<int, std::uint32_t>> queue;
    std::vector<std::uint32_t> result;
    auto insert = [](auto& family, std::uint32_t carrier) {
        for (std::uint32_t edge : family)
            if (!(edge & ~carrier))
                return false;
        std::erase_if(family, [carrier](std::uint32_t edge) {
            return !(carrier & ~edge);
        });
        family.push_back(carrier);
        return true;
    };
    for (auto work = Left & ~InitialBlack; work; work &= work - 1)
    {
        const int point = std::countr_zero(work);
        insert(carriers[point], weight[point]);
        queue.emplace_back(point, weight[point]);
    }
    while (!queue.empty())
    {
        auto [point, carrier] = queue.front();
        queue.pop_front();
        if (std::find(carriers[point].begin(), carriers[point].end(), carrier)
            == carriers[point].end())
            continue;
        bool finished = false;
        for (std::uint32_t edge : result)
            if (!(edge & ~carrier))
            {
                finished = true;
                break;
            }
        if (finished)
            continue;
        if (bit(point) & Right)
        {
            insert(result, carrier);
            continue;
        }
        for (auto work = Neighbors[point] & ~InitialBlack;
             work; work &= work - 1)
        {
            const int next = std::countr_zero(work);
            const auto extension = carrier | weight[next];
            if (insert(carriers[next], extension))
                queue.emplace_back(next, extension);
        }
    }
    std::sort(result.begin(), result.end());
    return result;
}

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

class HypergraphPool
{
public:
    std::uint32_t intern(std::vector<std::uint32_t> edges)
    {
        // Packing preserves numeric edge order.
        std::uint32_t support = 0;
        for (std::uint32_t edge : edges)
            support |= edge;
        if (support & (support + 1))
        {
            std::array<std::uint32_t, 32> mapping{};
            std::uint32_t target = 1;
            for (auto work = support; work; work &= work - 1, target <<= 1)
                mapping[std::countr_zero(work)] = target;
            for (std::uint32_t& edge : edges)
            {
                std::uint32_t packed = 0;
                for (auto work = edge; work; work &= work - 1)
                    packed |= mapping[std::countr_zero(work)];
                edge = packed;
            }
        }
        const std::uint32_t hash = edge_hash(edges);
        if (index_hashes.empty())
            resize_index(1024);
        if (const std::uint32_t found = find(hash, edges);
            found != Missing)
            return found;
        if constexpr (sizeof(std::size_t) > sizeof(std::uint32_t))
            if (graphs.size() >= std::uint64_t{1} << 32)
                throw std::overflow_error("too many distinct hypergraphs");
        std::uint32_t active = 0;
        for (std::uint32_t edge : edges)
            active |= edge;
        const auto id = static_cast<std::uint32_t>(graphs.size());
        const auto [block, offset] = append_edges(edges);
        graphs.push_back(Hypergraph{
            block, offset, static_cast<std::uint32_t>(edges.size()), active});
        if ((graphs.size() * 4) > (index_hashes.size() * 3))
            resize_index(index_hashes.size() * 2);
        insert_index(hash, id);
        return id;
    }

    Hypergraph& operator[](std::uint32_t id)
    {
        return graphs[id];
    }

    std::span<const std::uint32_t> edges(std::uint32_t id) const
    {
        const Hypergraph& graph = graphs[id];
        return {edge_blocks[graph.edge_block].data.get() + graph.edge_offset,
                graph.edge_count};
    }

    std::uint64_t size() const { return graphs.size(); }

    std::uint64_t bytes() const
    {
        std::uint64_t result = graphs.size() * sizeof(Hypergraph);
        for (const EdgeBlock& block : edge_blocks)
            result += std::uint64_t{block.capacity} * sizeof(std::uint32_t);
        result += std::uint64_t{index_hashes.capacity()
                               + index_ids.capacity()}
            * sizeof(std::uint32_t);
        return result;
    }

private:
    static constexpr std::uint32_t Missing =
        std::numeric_limits<std::uint32_t>::max();
    static constexpr std::uint32_t EdgeBlockWords = 1 << 20;

    struct EdgeBlock
    {
        std::unique_ptr<std::uint32_t[]> data;
        std::uint32_t capacity;
        std::uint32_t used;
    };

    static std::uint64_t hash_edges(
        std::span<const std::uint32_t> edges)
    {
        std::uint64_t value = edges.size();
        for (std::uint32_t edge : edges)
        {
            value ^= edge + 0x9e3779b97f4a7c15ULL
                + (value << 6) + (value >> 2);
            value ^= value >> 30;
            value *= 0xbf58476d1ce4e5b9ULL;
            value ^= value >> 27;
            value *= 0x94d049bb133111ebULL;
            value ^= value >> 31;
        }
        return value;
    }

    static std::uint32_t edge_hash(
        std::span<const std::uint32_t> edges)
    {
        const std::uint32_t hash = hash_edges(edges);
        return hash ? hash : 1;
    }

    std::uint32_t find(std::uint32_t hash,
                       std::span<const std::uint32_t> sought) const
    {
        const std::size_t mask = index_hashes.size() - 1;
        std::size_t slot = hash & mask;
        while (index_hashes[slot])
        {
            const std::uint32_t id = index_ids[slot];
            if (index_hashes[slot] == hash
                && std::ranges::equal(edges(id), sought))
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
        std::vector<std::uint32_t> old_hashes = std::move(index_hashes);
        std::vector<std::uint32_t> old_ids = std::move(index_ids);
        index_hashes.assign(capacity, 0);
        index_ids.resize(capacity);
        for (std::size_t slot = 0; slot < old_hashes.size(); ++slot)
            if (old_hashes[slot])
                insert_index(old_hashes[slot], old_ids[slot]);
    }

    std::pair<std::uint32_t, std::uint32_t> append_edges(
        std::span<const std::uint32_t> edges)
    {
        if (edges.size() > std::numeric_limits<std::uint32_t>::max())
            throw std::overflow_error("hypergraph has too many edges");
        const std::uint32_t count = static_cast<std::uint32_t>(edges.size());
        if (edge_blocks.empty()
            || edge_blocks.back().capacity - edge_blocks.back().used < count)
        {
            if constexpr (sizeof(std::size_t) > sizeof(std::uint32_t))
                if (edge_blocks.size() >= std::uint64_t{1} << 32)
                    throw std::overflow_error(
                        "too many hypergraph edge blocks");
            const std::uint32_t capacity = std::max(EdgeBlockWords, count);
            edge_blocks.push_back({
                std::make_unique_for_overwrite<std::uint32_t[]>(capacity),
                capacity, 0});
        }
        EdgeBlock& block = edge_blocks.back();
        const std::uint32_t offset = block.used;
        std::copy(edges.begin(), edges.end(), block.data.get() + offset);
        block.used += count;
        return {static_cast<std::uint32_t>(edge_blocks.size() - 1), offset};
    }

    std::deque<Hypergraph> graphs;
    std::vector<EdgeBlock> edge_blocks;
    std::vector<std::uint32_t> index_hashes;
    std::vector<std::uint32_t> index_ids;
};

class Solver
{
public:
    bool solve(std::uint32_t remaining,
               const std::vector<std::uint32_t>& edges,
               bool black_turn)
    {
        std::uint32_t active = 0;
        for (std::uint32_t edge : edges)
            active |= edge;
        const std::uint32_t id = pool.intern(edges);
        return win(id, (remaining & ~active) != 0, black_turn);
    }

    std::uint64_t states() const { return solved_states; }
    std::uint64_t hypergraphs() const { return pool.size(); }
    std::uint64_t bytes() const { return pool.bytes(); }

    std::uint32_t winning_batch(
        std::uint32_t remaining, std::vector<std::uint32_t> edges,
        bool black_turn)
    {
        if (!solve(remaining, edges, black_turn))
            return 0;
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
    static std::vector<std::uint32_t> white_child(
        std::span<const std::uint32_t> edges, std::uint32_t cell,
        bool& legal)
    {
        std::vector<std::uint32_t> reduced;
        reduced.reserve(edges.size());
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
            reduced.push_back(edge & ~cell);
        }
        // Only shortened edges can dominate unchanged edges.
        std::vector<std::uint32_t> result = reduced;
        for (std::uint32_t edge : edges)
        {
            if (edge & cell)
                continue;
            bool dominated = false;
            for (std::uint32_t kept : reduced)
                if (!(kept & ~edge))
                {
                    dominated = true;
                    break;
                }
            if (!dominated)
                result.push_back(edge);
        }
        std::inplace_merge(result.begin(), result.begin() + reduced.size(),
                           result.end());
        return result;
    }

    static std::vector<std::uint32_t> black_child(
        std::span<const std::uint32_t> edges, std::uint32_t cell)
    {
        std::vector<std::uint32_t> result;
        result.reserve(std::count_if(
            edges.begin(), edges.end(), [cell](std::uint32_t edge) {
                return !(edge & cell);
            }));
        for (std::uint32_t edge : edges)
            if (!(edge & cell))
                result.push_back(edge);
        return result;
    }

    bool win(std::uint32_t id, bool isolates, bool black_turn)
    {
        const int turn = black_turn ? 1 : 0;
        const std::uint8_t state = std::uint8_t{1} << isolates;
        if (pool[id].known[turn] & state)
            return pool[id].wins[turn] & state;

        // Dead cells preserve the continue/end predicate.
        if (isolates)
        {
            const bool result = !win(id, false, !black_turn)
                                || win(id, false, black_turn);
            remember(id, turn, state, result);
            return result;
        }

        const std::uint32_t active = pool[id].active;
        for (auto work = active; work;)
        {
            const std::uint32_t cell = work & -work;
            // Vertices with identical edge incidence are interchangeable.
            std::uint32_t twins = active;
            for (std::uint32_t edge : pool.edges(id))
            {
                twins &= edge & cell ? edge : ~edge;
                if (twins == cell)
                    break;
            }
            work &= ~twins;
            std::vector<std::uint32_t> child;
            if (black_turn)
            {
                child = black_child(pool.edges(id), cell);
                if (child.empty())
                    continue;
            }
            else
            {
                bool legal;
                child = white_child(pool.edges(id), cell, legal);
                if (!legal)
                    continue;
            }
            const std::uint32_t child_id = pool.intern(std::move(child));
            if (!win(child_id, false, !black_turn)
                || win(child_id, false, black_turn))
            {
                remember(id, turn, state, true);
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

    HypergraphPool pool;
    std::uint64_t solved_states = 0;
};

void initialize_board(int size)
{
    if (size < 1 || size > 8)
        throw std::invalid_argument("board size must be in 1..8");
    Size = size;
    Cells = Size * Size;
    Board = Cells == 64 ? ~std::uint64_t{0} : bit(Cells) - 1;
    Left = 0;
    for (int row = 0; row < Size; ++row)
        Left |= bit(row * Size);
    Right = Left << (Size - 1);
    Neighbors = make_neighbors();
}

std::uint64_t parse_cells(const std::string& text)
{
    if (text == "-" || text.empty())
        return 0;
    std::uint64_t result = 0;
    std::size_t start = 0;
    for (;;)
    {
        const std::size_t end = text.find(',', start);
        const std::string name = text.substr(
            start, end == std::string::npos ? end : end - start);
        if (name.size() < 2 || name[0] < 'a' || name[0] >= 'a' + Size)
            throw std::invalid_argument("invalid cell: " + name);
        int row = 0;
        for (std::size_t index = 1; index < name.size(); ++index)
        {
            if (name[index] < '0' || name[index] > '9')
                throw std::invalid_argument("invalid cell: " + name);
            row = 10 * row + name[index] - '0';
        }
        if (row < 1 || row > Size)
            throw std::invalid_argument("invalid cell: " + name);
        const std::uint64_t cell = bit((row - 1) * Size + name[0] - 'a');
        if (result & cell)
            throw std::invalid_argument("duplicate cell: " + name);
        result |= cell;
        if (end == std::string::npos)
            return result;
        start = end + 1;
        if (start == text.size())
            throw std::invalid_argument("empty cell after comma");
    }
}

void initialize_position(const std::string& black,
                         const std::string& white)
{
    InitialBlack = parse_cells(black);
    InitialWhite = parse_cells(white);
    if ((InitialBlack & InitialWhite)
        || connected(InitialBlack, 0) || connected(InitialWhite, 1))
        throw std::invalid_argument("initial position is terminal or overlaps");
    Empty = Board & ~(InitialBlack | InitialWhite);
    if (!connected(InitialWhite | Empty, 1))
        throw std::invalid_argument("White has no completion");
    EmptyCells = std::popcount(Empty);
    if (EmptyCells > 32)
        throw std::invalid_argument(
            "completion construction supports at most 32 empty cells");
    CompactMask = EmptyCells == 32 ? ~std::uint32_t{0}
                                  : (std::uint32_t{1} << EmptyCells) - 1;
    EmptyCell = make_empty_cells();
}

} // namespace

int main(int argc, char** argv)
{
    try
    {
        if (argc != 5 || (std::string(argv[4]) != "black"
                          && std::string(argv[4]) != "white"))
            throw std::invalid_argument(
                "usage: rexplus_hypergraph N BLACK_CELLS WHITE_CELLS "
                "black|white (use - for an empty set)");
        initialize_board(std::stoi(argv[1]));
        initialize_position(argv[2], argv[3]);
        const bool black_turn = std::string(argv[4]) == "black";
        const auto started = std::chrono::steady_clock::now();
        const auto edges = minimal_completions();
        Solver solver;
        const bool mover_wins = solver.solve(
            CompactMask, edges, black_turn);
        std::cout << "board_size " << Size << '\n'
                  << "black " << board_names(InitialBlack) << '\n'
                  << "white " << board_names(InitialWhite) << '\n'
                  << "to_play " << (black_turn ? "black\n" : "white\n")
                  << "result " << (mover_wins ? "win\n" : "loss\n")
                  << "minimal_completions " << edges.size() << '\n'
                  << "hypergraphs " << solver.hypergraphs() << '\n'
                  << "states " << solver.states() << '\n'
                  << "seconds "
                  << std::chrono::duration<double>(
                         std::chrono::steady_clock::now() - started).count()
                  << '\n';
        if (mover_wins)
            std::cout << "winning_batch "
                      << names(solver.winning_batch(
                             CompactMask, edges, black_turn))
                      << '\n';
        return 0;
    }
    catch (const std::exception& error)
    {
        std::cerr << "error: " << error.what() << '\n';
        return 2;
    }
}
