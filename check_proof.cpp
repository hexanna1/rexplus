// Independent proof checker with bounded whole-batch kernel checks.
#include "physical_connectivity.hpp"
#include <fstream>
#include <limits>
#include <ranges>
#include <sstream>
#include "proof_stream.hpp"
#include "small_kernel_check.hpp"

using selfdual::bit;
using selfdual::Board;
using selfdual::connected;
using selfdual::ConnectivityBDD;
using selfdual::FrontierConnectivity;
using selfdual::initialize_board;
using selfdual::parse_cells;

namespace proofcheck {
using Edge = std::uint32_t;
enum class Kind : std::uint8_t {
    Missing,
    Simple,
    Bound,
    Win,
    Loss,
    Dead,
    Unfill,
    Avoider,
    Potential,
    Kernel
};
struct Fact
{
    Kind kind = Kind::Missing;
    bool value = false;
    unsigned mode = 0, winner = 0;
    Edge cell = 0, keep = 0;
    std::uint32_t dependency = 0, child_graph = 0;
    std::vector<std::uint32_t> data;
    std::uint64_t bijection = 0;
};
struct Graph
{
    std::vector<Edge> edges;
    Edge active = 0;
    bool present = false;
    std::uint8_t emitted = 0, wins = 0, required = 0, required_values = 0, simple_flags = 0,
                 potential_flags = 0;
};
[[noreturn]] void fail(const std::string& message)
{
    throw std::runtime_error(message);
}
void require(bool condition, const char* message)
{
    if (!condition)
        fail(message);
}

struct PhysicalRoot
{
    unsigned size = 0, turn = 0;
    bool result = false;
    std::string black, white;
    std::vector<unsigned> variables;
    std::uint32_t root = 0;
    Edge support = 0;
    std::uint64_t root_bijection = 0;
};

struct Proof
{
    unsigned size = 0, turn = 0;
    bool result = false;
    std::string black, white;
    std::vector<unsigned> variables;
    std::uint32_t root = 0;
    Edge support = 0;
    std::uint64_t root_bijection = 0;
    std::vector<Graph> graphs;
    bool complete = false;
    std::uint64_t physical_roots_bound = 0;
    std::uint64_t facts_checked = 0, cofactor_checks = 0, dominance_checks = 0;
    std::vector<Edge> cofactor_candidates, cofactor_result;
    small_kernel::Verifier kernel_verifier;

    static void check_family(const Graph& g)
    {
        require(!g.edges.empty(), "nonterminal proof has an empty connection family");
        require(std::is_sorted(g.edges.begin(), g.edges.end()), "edges are not ordered");
        require(!(g.active & (g.active + 1)), "graph labels are not packed");
        for (std::size_t i = 0; i < g.edges.size(); ++i)
        {
            require(g.edges[i] != 0, "nonterminal proof has an empty edge");
            // In increasing unsigned order, a strict subset must be earlier.
            for (std::size_t j = i + 1; j < g.edges.size(); ++j)
                require((g.edges[i] & ~g.edges[j]) != 0, "edge family is not an antichain");
        }
    }

    static void check_mapping(std::span<const Edge> mapping, Edge source, Edge target)
    {
        require(mapping.size() == std::size_t(std::popcount(source)),
                "bijection has the wrong domain size");
        Edge image = 0;
        for (auto label : mapping)
        {
            require(label < 32, "bijection target exceeds graph labels");
            const auto cell = Edge{1} << label;
            require(!(cell & image), "bijection is not injective");
            image |= cell;
        }
        require(image == target, "bijection is not onto the exact child support");
    }

    static std::array<Edge, 32> decode_mapping(std::uint64_t word, Edge source, Edge target)
    {
        const auto count = unsigned(std::popcount(source));
        std::array<Edge, 32> mapping{};
        if (!word)
        {
            for (unsigned i = 0; i < count; ++i)
                mapping[i] = i;
        }
        else
        {
            require(count <= 16, "nonidentity bijection exceeds sixteen labels");
            if (count < 16)
                require(!(word >> (4 * count)), "bijection has unused high bits");
            for (unsigned i = 0; i < count; ++i)
                mapping[i] = (word >> (4 * i)) & 15;
        }
        check_mapping(std::span<const Edge>(mapping).first(count), source, target);
        return mapping;
    }

    static void
    map_edges(std::vector<Edge>& edges, Edge source, Edge target, std::span<const Edge> mapping)
    {
        check_mapping(mapping, source, target);
        std::array<Edge, 32> images{};
        unsigned rank = 0;
        for (auto work = source; work; work &= work - 1, ++rank)
            images[std::countr_zero(work)] = Edge{1} << mapping[rank];
        for (auto& edge : edges)
        {
            Edge mapped = 0;
            for (auto work = edge; work; work &= work - 1)
                mapped |= images[std::countr_zero(work)];
            edge = mapped;
        }
        std::sort(edges.begin(), edges.end());
    }

    void read(std::istream& source)
    {
        complete = false;
        proof_io::DecimalInput input(source);
        std::string tag;
        std::uint64_t declared_graphs = 0, declared_facts = 0;
        enum class Prefix { Position, Variables, InitialGraph, Root, Body };
        auto prefix = Prefix::Position;
        bool ended = false;
        Fact fact_buffer;
        while (input >> tag)
        {
            if (tag == "end")
            {
                require(prefix == Prefix::Body, "end record before the complete proof prefix");
                input >> declared_graphs >> declared_facts;
                require(bool(input), "incomplete proof end record");
                ended = true;
                break;
            }
            if (tag == "position")
            {
                require(prefix == Prefix::Position,
                        "position record is duplicated or out of order");
                int value = 0;
                input >> size >> black >> white >> turn >> value;
                require(bool(input), "incomplete position record");
                require(size >= 1 && size <= 8 && turn < 2, "invalid physical position");
                require(value == 0 || value == 1, "invalid root Boolean");
                result = value;
                prefix = Prefix::Variables;
            }
            else if (tag == "variables")
            {
                require(prefix == Prefix::Variables,
                        "variables record is duplicated or out of order");
                unsigned count = 0;
                input >> count;
                require(bool(input) && count <= 32, "invalid physical variable count");
                variables.resize(count);
                for (auto& point : variables)
                    input >> point;
                prefix = Prefix::InitialGraph;
            }
            else if (tag == "root")
            {
                require(prefix == Prefix::Root, "root record is duplicated or out of order");
                input >> root >> support;
                require(bool(input), "incomplete root record");
                input >> root_bijection;
                require(bool(input), "incomplete root bijection");
                prefix = Prefix::Body;
            }
            else if (tag == "g")
            {
                require(prefix == Prefix::InitialGraph || prefix == Prefix::Body,
                        "graph record before the physical prefix");
                std::uint32_t id = 0;
                unsigned count = 0;
                input >> id >> count;
                require(bool(input), "incomplete graph record");
                require(id == graphs.size(), "graph records must have consecutive identifiers");
                graphs.emplace_back();
                auto& g = graphs.back();
                g.present = true;
                g.edges.resize(count);
                for (auto& edge : g.edges)
                {
                    input >> edge;
                    g.active |= edge;
                }
                require(bool(input), "incomplete graph edges");
                check_family(g);
                if (prefix == Prefix::InitialGraph)
                    prefix = Prefix::Root;
            }
            else if (tag == "f")
            {
                require(prefix == Prefix::Body, "fact record before the complete proof prefix");
                std::uint32_t id = 0;
                unsigned value = 0;
                std::string kind;
                input >> id >> value >> kind;
                require(bool(input), "incomplete fact record");
                require(id / 4 < graphs.size(), "missing fact graph");
                require(!(graphs[id / 4].emitted & (1U << (id % 4))), "duplicate fact record");
                auto& f = fact_buffer;
                f.kind = Kind::Missing;
                f.data.clear();
                require(value <= 1, "invalid proof Boolean");
                f.value = value;
                if (kind == "simple")
                    f.kind = Kind::Simple;
                else if (kind == "avoider")
                    f.kind = Kind::Avoider;
                else if (kind == "potential")
                    f.kind = Kind::Potential;
                else if (kind == "kernel")
                {
                    f.kind = Kind::Kernel;
                    input >> f.winner >> f.keep;
                    require(bool(input), "incomplete kernel record");
                }
                else if (kind == "bound")
                {
                    f.kind = Kind::Bound;
                    unsigned count = 0;
                    input >> f.winner >> count;
                    require(bool(input), "incomplete bound record");
                    f.data.resize(count);
                    for (auto& edge : f.data)
                        input >> edge;
                }
                else if (kind == "win")
                {
                    f.kind = Kind::Win;
                    input >> f.cell >> f.mode >> f.dependency;
                    input >> f.bijection;
                    require(f.cell < 32, "proof cell index exceeds the graph word");
                    f.cell = Edge{1} << f.cell;
                }
                else if (kind == "loss")
                {
                    f.kind = Kind::Loss;
                    input >> f.mode;
                    require(bool(input) && f.mode <= 32, "invalid loss branch count");
                    f.data.resize(std::size_t(f.mode) * 6);
                    for (std::size_t start = 0; start < f.data.size(); start += 6)
                    {
                        for (unsigned field = 0; field < 4; ++field)
                            input >> f.data[start + field];
                        std::uint64_t word = 0;
                        input >> word;
                        require(bool(input), "incomplete losing bijection");
                        f.data[start + 4] = word;
                        f.data[start + 5] = word >> 32;
                        require(f.data[start] < 32, "proof cell index exceeds the graph word");
                        f.data[start] = Edge{1} << f.data[start];
                    }
                }
                else if (kind == "unfill")
                {
                    f.kind = Kind::Unfill;
                    input >> f.cell >> f.child_graph;
                    f.data.resize(2);
                    input >> f.data[0] >> f.data[1] >> f.bijection;
                    require(bool(input), "incomplete own-unfill record");
                    require(f.cell < 32, "proof cell index exceeds the graph word");
                    f.cell = Edge{1} << f.cell;
                }
                else if (kind == "dead")
                {
                    f.kind = Kind::Dead;
                    input >> f.mode;
                    require(bool(input) && f.mode <= 2, "invalid dead-option rule");
                    f.data.resize(f.mode == 2 ? 2 : 1);
                    for (auto& entry : f.data)
                        input >> entry;
                }
                else
                    fail("unknown proof rule: " + kind);
                require(bool(input), "incomplete proof rule");
                verify(id, f);
            }
            else
                fail("unknown proof record: " + tag);
            require(bool(input), "incomplete proof record");
        }
        require(ended, "missing proof end record");
        require(!(input >> tag) && input.at_end(), "records after the proof end");
        require(declared_graphs == graphs.size(), "wrong proof graph count");
        require(declared_facts == facts_checked, "wrong proof fact count");
        for (const auto& g : graphs)
        {
            require(g.present, "missing graph record");
            require(!(g.required & ~g.emitted), "missing required proof fact");
            require(!((g.wins ^ g.required_values) & g.required),
                    "dependency has the wrong outcome");
        }
        require(root / 4 < graphs.size(), "missing root graph");
        physical_equality();
        require(graphs[root / 4].emitted & (1U << (root % 4)), "missing root proof fact");
        require(bool(graphs[root / 4].wins & (1U << (root % 4))) == result,
                "root outcome differs from requested result");
        complete = true;
    }

    static std::optional<std::array<bool, 2>> elementary(Graph& g)
    {
        if (g.simple_flags == 1)
            return std::nullopt;
        if (g.simple_flags & 2)
            return std::array<bool, 2>{bool(g.simple_flags & 4), bool(g.simple_flags & 8)};
        auto remember = [&](bool white, bool black) {
            g.simple_flags = 2 | (white ? 4 : 0) | (black ? 8 : 0);
            return std::array<bool, 2>{white, black};
        };
        if (std::popcount(g.active) == 1)
            return remember(false, false);
        Edge common = g.active, used = 0;
        bool singleton = false, disjoint = true;
        std::uint64_t weight = 0;
        for (auto edge : g.edges)
        {
            common &= edge;
            singleton |= std::popcount(edge) == 1;
            disjoint &= !(edge & used);
            used |= edge;
            weight += std::uint64_t{1} << (32 - std::popcount(edge));
        }
        if (singleton)
            return remember(false, true);
        if (common)
            return remember(true, false);
        if (disjoint)
            return remember(weight<(std::uint64_t{1} << 31), weight>(std::uint64_t{1} << 31));
        g.simple_flags = 1;
        return std::nullopt;
    }

    static bool legal(const Graph& g, Edge cell, unsigned t)
    {
        if (!std::has_single_bit(cell) || !(cell & g.active))
            return false;
        if (!t)
            return std::find(g.edges.begin(), g.edges.end(), cell) == g.edges.end();
        return std::any_of(
            g.edges.begin(), g.edges.end(), [=](Edge edge) { return !(edge & cell); });
    }
    std::span<const Edge> child(const Graph& g, Edge cell, unsigned t)
    {
        auto& result = cofactor_result;
        result.clear();
        if (t)
        {
            // Deleting minterms preserves an already audited antichain and order.
            for (auto edge : g.edges)
                if (!(edge & cell))
                    result.push_back(edge);
            return result;
        }
        auto& candidates = cofactor_candidates;
        candidates.clear();
        for (auto edge : g.edges)
            candidates.push_back(edge & ~cell);
        std::sort(candidates.begin(), candidates.end());
        // A proper subset has a smaller unsigned mask. Thus every potential
        // dominator is earlier, and no retained term needs later removal.
        for (auto edge : candidates)
            if (std::none_of(result.begin(), result.end(), [=](Edge earlier) {
                    return !(earlier & ~edge);
                }))
                result.push_back(edge);
        return result;
    }
    void cofactor(
        const Graph& g, Edge cell, unsigned t, std::uint32_t child_id, std::uint64_t bijection)
    {
        require(legal(g, cell, t), "proof placement loses immediately");
        require(child_id < graphs.size() && graphs[child_id].present, "missing child graph");
        child(g, cell, t);
        Edge source = 0;
        for (auto edge : cofactor_result)
            source |= edge;
        const auto mapping = decode_mapping(bijection, source, graphs[child_id].active);
        map_edges(cofactor_result,
                  source,
                  graphs[child_id].active,
                  std::span<const Edge>(mapping).first(std::popcount(source)));
        require(std::ranges::equal(cofactor_result, graphs[child_id].edges),
                "child graph is not the claimed Boolean cofactor under the bijection");
        require(std::popcount(graphs[child_id].active) < std::popcount(g.active),
                "placement does not lower proof rank");
        ++cofactor_checks;
    }
    void dependency(std::uint32_t fid, std::uint32_t gid, unsigned t, bool value)
    {
        require(fid == 4 * gid + 2 * t, "wrong child turn or dead option");
        require(gid < graphs.size() && graphs[gid].present,
                "dependency graph must be emitted before the fact");
        auto& g = graphs[gid];
        const auto flag = std::uint8_t{1} << (fid % 4);
        require(!(g.required & flag) || bool(g.required_values & flag) == value,
                "conflicting required outcomes");
        g.required |= flag;
        if (value)
            g.required_values |= flag;
        if (g.emitted & flag)
            require(bool(g.wins & flag) == value, "dependency has the wrong outcome");
    }

    bool one_step_black(Graph& graph) const
    {
        // Every first Black assignment leaves strict Avoider potential.
        // A longer Black batch only deletes more completion terms.
        if (graph.potential_flags & 1)
            return graph.potential_flags & 2;
        graph.potential_flags |= 1;
        constexpr auto half = std::uint64_t{1} << 31;
        for (auto work = graph.active; work; work &= work - 1)
        {
            const Edge cell = work & -work;
            std::uint64_t mass = 0;
            for (auto edge : graph.edges)
                if (!(edge & cell))
                {
                    mass += std::uint64_t{1} << (32 - std::popcount(edge));
                    if (mass >= half)
                        return false;
                }
        }
        graph.potential_flags |= 2;
        return true;
    }
    bool one_step_white(Graph& graph) const
    {
        // Rebuild each raw White cofactor independently of the producer's
        // pair-incidence formula. Keeping redundant terms is conservative.
        if (graph.potential_flags & 4)
            return graph.potential_flags & 8;
        graph.potential_flags |= 4;
        constexpr auto half = std::uint64_t{1} << 31;
        for (auto first = graph.active; first; first &= first - 1)
        {
            const Edge white = first & -first;
            if (std::find(graph.edges.begin(), graph.edges.end(), white) != graph.edges.end())
                continue;
            std::uint64_t mass = 0;
            std::array<std::uint64_t, 32> incidence{};
            for (auto edge : graph.edges)
            {
                const auto reduced = edge & ~white;
                const auto weight = std::uint64_t{1} << (32 - std::popcount(reduced));
                mass += weight;
                for (auto work = reduced; work; work &= work - 1)
                    incidence[std::countr_zero(work)] += weight;
            }
            std::uint64_t minimum = mass;
            // Include cells made semantically dead by this White assignment.
            for (auto work = graph.active & ~white; work; work &= work - 1)
                minimum = std::min(minimum, incidence[std::countr_zero(work)]);
            if (mass - minimum < half)
            {
                graph.potential_flags |= 8;
                return true;
            }
        }
        return false;
    }

    void verify(std::uint32_t fid, const Fact& f)
    {
        require(fid / 4 < graphs.size(), "missing fact graph");
        auto& g = graphs[fid / 4];
        require(g.present && f.kind != Kind::Missing, "missing proof fact graph");
        const unsigned t = (fid / 2) % 2, dead = fid % 2;
        if (f.kind == Kind::Potential)
        {
            require(f.value == (t == 0), "one-step potential has the wrong outcome");
            if (t == 1)
                require(one_step_black(g), "Black potential child is not strict");
            if (t == 0 || dead)
                require(one_step_white(g), "White potential move is missing");
        }
        else if (f.kind == Kind::Avoider)
        {
            std::uint64_t mass = 0;
            constexpr auto half = std::uint64_t{1} << 31;
            for (auto edge : g.edges)
            {
                mass += std::uint64_t{1} << (32 - std::popcount(edge));
                require(mass <= half, "Avoider potential exceeds one half");
            }
            require((mass < half && f.value == (t == 0))
                        || (mass == half && !dead && t == 1 && !f.value),
                    "invalid Avoider potential outcome");
        }
        else if (f.kind == Kind::Dead)
        {
            require(dead == 1 && f.mode <= 2, "invalid dead-option rule");
            if (f.mode == 0)
            {
                require(f.value, "dead end rule cannot prove a loss");
                dependency(f.data[0], fid / 4, !t, false);
            }
            else if (f.mode == 1)
            {
                require(f.value, "dead continuation rule cannot prove a loss");
                dependency(f.data[0], fid / 4, t, true);
            }
            else
            {
                require(!f.value, "dead loss rule cannot prove a win");
                dependency(f.data[0], fid / 4, !t, true);
                dependency(f.data[1], fid / 4, t, false);
            }
        }
        else
        {
            require(!dead, "active rule used for a physical dead option");
            if (f.kind == Kind::Simple)
            {
                const auto values = elementary(g);
                require(values && (*values)[t] == f.value, "invalid elementary certificate");
            }
            else if (f.kind == Kind::Kernel)
            {
                require(f.winner < 2 && f.value == (t == f.winner),
                        "kernel has the wrong winner");
                require(kernel_verifier.certify(g.edges, g.active, f.keep, f.winner == 1),
                        "small physical kernel does not certify a color-only value");
            }
            else if (f.kind == Kind::Bound)
            {
                require(f.winner < 2 && f.value == (t == f.winner),
                        "bound has the wrong winner");
                Edge used = 0;
                std::uint64_t weight = 0;
                require(!f.data.empty(), "empty structural certificate");
                for (auto edge : f.data)
                {
                    require(edge && !(edge & ~g.active) && !(edge & used),
                            "bound family is not disjoint on the same variables");
                    used |= edge;
                    weight += std::uint64_t{1} << (32 - std::popcount(edge));
                    if (f.winner)
                        require(std::find(g.edges.begin(), g.edges.end(), edge)
                                    != g.edges.end(),
                                "Black bound edge is not in the original family");
                }
                if (f.winner)
                    require(weight > (std::uint64_t{1} << 31),
                            "Black bound is not above one half");
                else
                {
                    require(weight < (std::uint64_t{1} << 31),
                            "White bound is not below one half");
                    for (auto edge : g.edges)
                        require(std::any_of(f.data.begin(),
                                            f.data.end(),
                                            [=](Edge core) { return !(core & ~edge); }),
                                "White cores do not cover every original edge");
                }
            }
            else if (f.kind == Kind::Win)
            {
                require(f.value && f.mode < 2, "invalid winning option");
                const auto child_id = f.dependency / 4;
                cofactor(g, f.cell, t, child_id, f.bijection);
                dependency(f.dependency, child_id, f.mode ? t : !t, f.mode);
            }
            else if (f.kind == Kind::Unfill)
            {
                require(!f.value, "own-unfill rule cannot prove a win");
                require(f.data.size() == 2, "invalid own-unfill dependencies");
                cofactor(g, f.cell, !t, f.child_graph, f.bijection);
                dependency(f.data[0], f.child_graph, !t, true);
                dependency(f.data[1], f.child_graph, t, false);
            }
            else if (f.kind == Kind::Loss)
            {
                require(!f.value, "invalid losing option list");
                Edge represented = 0;
                require(f.data.size() == std::size_t(f.mode) * 6, "invalid losing branch list");
                for (std::size_t offset = 0; offset < f.data.size(); offset += 6)
                {
                    const auto cell = f.data[offset], child_id = f.data[offset + 1];
                    const auto word = std::uint64_t{f.data[offset + 4]}
                                      | (std::uint64_t{f.data[offset + 5]} << 32);
                    require(!(represented & cell), "duplicate losing representative");
                    represented |= cell;
                    cofactor(g, cell, t, child_id, word);
                    dependency(f.data[offset + 2], child_id, !t, true);
                    dependency(f.data[offset + 3], child_id, t, false);
                }
                // Inc(c) subset Inc(v) is exactly membership of v in the
                // intersection of all edges containing c. Check every omitted
                // legal placement against this independently reconstructed set.
                Edge covered = represented;
                for (auto creators = represented; creators; creators &= creators - 1)
                {
                    const auto creator = creators & -creators;
                    Edge victims = g.active;
                    for (auto edge : g.edges)
                        if (edge & creator)
                            victims &= edge;
                    dominance_checks += std::popcount(victims & ~covered);
                    covered |= victims;
                }
                for (auto cells = g.active & ~represented; cells; cells &= cells - 1)
                {
                    const auto victim = cells & -cells;
                    if (legal(g, victim, t))
                        require(covered & victim,
                                "losing proof omits a legal undominated placement");
                }
            }
            else
                fail("unknown active proof rule");
        }
        const auto flag = std::uint8_t{1} << (fid % 4);
        g.emitted |= flag;
        if (f.value)
            g.wins |= flag;
        require(!(g.required & flag) || bool(g.required_values & flag) == f.value,
                "fact contradicts a required outcome");
        ++facts_checked;
    }

    void bind_roots(std::istream& source)
    {
        require(complete, "physical bindings require a completely checked DAG");
        proof_io::DecimalInput input(source);
        std::string tag;
        unsigned count = 0;
        while (input >> tag)
        {
            require(tag == "position", "physical binding must begin with position");
            PhysicalRoot binding;
            int value = 0;
            input >> binding.size >> binding.black >> binding.white >> binding.turn >> value;
            require(bool(input), "incomplete physical binding position");
            require(binding.size >= 1 && binding.size <= 8 && binding.turn < 2,
                    "invalid physical binding position");
            require(value == 0 || value == 1, "invalid physical binding Boolean");
            binding.result = value;
            unsigned variables_count = 0;
            input >> tag >> variables_count;
            require(bool(input) && tag == "variables" && variables_count <= 32,
                    "invalid physical binding variables");
            binding.variables.resize(variables_count);
            for (auto& point : binding.variables)
                input >> point;
            input >> tag >> binding.root >> binding.support >> binding.root_bijection;
            require(bool(input) && tag == "root", "incomplete physical binding root");
            require(binding.root / 4 < graphs.size(), "missing physical binding graph");
            const auto& graph = graphs[binding.root / 4];
            const auto flag = std::uint8_t{1} << (binding.root % 4);
            require(graph.emitted & flag, "physical binding fact was not checked");
            require(bool(graph.wins & flag) == binding.result,
                    "physical binding outcome differs from the checked fact");
            physical_equality(binding);
            ++count;
            ++physical_roots_bound;
            std::cout << "bound_root " << physical_roots_bound << ' ' << binding.size << ' '
                      << binding.black << ' ' << binding.white << ' ' << binding.turn << ' '
                      << binding.result << ' ' << binding.root << ' ' << binding.support << ' '
                      << binding.root_bijection << '\n';
        }
        require(input.at_end(), "invalid physical binding token");
        require(count, "physical binding file is empty");
    }

    void physical_equality()
    {
        physical_equality(PhysicalRoot{
            size, turn, result, black, white, variables, root, support, root_bijection});
    }

    void physical_equality(const PhysicalRoot& binding)
    {
        const auto size = binding.size, turn = binding.turn;
        const auto& black = binding.black;
        const auto& white = binding.white;
        const auto& variables = binding.variables;
        const auto root = binding.root, support = binding.support;
        const auto root_bijection = binding.root_bijection;

        initialize_board(size);
        const auto black_mask = parse_cells(black), white_mask = parse_cells(white);
        require(!(black_mask & white_mask), "physical colors overlap");
        require(!connected(black_mask, 0) && !connected(white_mask, 1),
                "physical position is already terminal");
        const auto empty = Board & ~(black_mask | white_mask);
        require(variables.size() <= 32 && variables.size() == std::size_t(std::popcount(empty)),
                "physical variable list is incomplete");
        std::uint64_t listed = 0;
        for (auto point : variables)
        {
            require(point < size * size && (empty & bit(point)) && !(listed & bit(point)),
                    "physical variable map is not a bijection");
            listed |= bit(point);
        }
        const Edge all = variables.size() == 32 ? ~Edge{0} : (Edge{1} << variables.size()) - 1;
        require(!(support & ~all), "root support exceeds physical variables");
        require((root / 2) % 2 == turn && (root % 2) == bool(all & ~support),
                "root has the wrong player or dead option");
        const auto& g = graphs[root / 4];
        require(std::popcount(support) == std::popcount(g.active),
                "root support has the wrong size");
        const auto root_mapping = decode_mapping(root_bijection, support, g.active);
        std::vector<unsigned> physical(std::popcount(support));
        unsigned rank = 0;
        for (auto cells = support; cells; cells &= cells - 1, ++rank)
            physical[root_mapping[rank]] = variables[std::countr_zero(cells)];
        ConnectivityBDD bdd(30, 2000000);
        FrontierConnectivity frontier(bdd, true);
        const auto connected_root = frontier.build(black_mask, white_mask);
        std::unordered_map<std::uint64_t, std::uint32_t> or_cache;
        auto unite = [&](auto&& self, std::uint32_t a, std::uint32_t b) -> std::uint32_t {
            if (a == 1 || b == 1)
                return 1;
            if (!a)
                return b;
            if (!b || a == b)
                return a;
            if (a > b)
                std::swap(a, b);
            const auto key = (std::uint64_t{a} << 32) | b;
            if (const auto found = or_cache.find(key); found != or_cache.end())
                return found->second;
            const int variable = std::countr_zero(bdd.support(a) | bdd.support(b));
            const auto low =
                self(self, bdd.cofactor(a, variable, false), bdd.cofactor(b, variable, false));
            const auto high =
                self(self, bdd.cofactor(a, variable, true), bdd.cofactor(b, variable, true));
            const auto result = bdd.make(variable, low, high);
            or_cache.emplace(key, result);
            return result;
        };
        std::uint32_t family_root = 0;
        for (auto edge : g.edges)
        {
            std::uint64_t variables_in_edge = 0;
            for (auto cells = edge; cells; cells &= cells - 1)
                variables_in_edge |= frontier.ordered(bit(physical[std::countr_zero(cells)]));
            std::uint32_t conjunction = 1;
            while (variables_in_edge)
            {
                const int variable = std::bit_width(variables_in_edge) - 1;
                conjunction = bdd.make(variable, 0, conjunction);
                variables_in_edge &= ~bit(variable);
            }
            family_root = unite(unite, family_root, conjunction);
        }
        require(family_root == connected_root,
                "root family differs from physical White connectivity");
        std::cout << "initial_bdd_nodes " << bdd.size() << '\n';
    }
};
} // namespace proofcheck

int main(int argc, char** argv)
{
    std::ios::sync_with_stdio(false);
    std::cin.tie(nullptr);
    try
    {
        proofcheck::require(
            argc >= 2,
            "usage: rexplus_proof_checker PROOF [--reserve-graphs COUNT] [--bind-roots FILE]");
        proofcheck::Proof proof;
        std::vector<std::string> bindings;
        for (int i = 2; i < argc; ++i)
        {
            const std::string option = argv[i];
            proofcheck::require(i + 1 < argc, "checker option has no value");
            if (option == "--reserve-graphs")
                proof.graphs.reserve(std::stoull(argv[++i]));
            else if (option == "--bind-roots")
                bindings.emplace_back(argv[++i]);
            else
                proofcheck::fail("unknown checker option: " + option);
        }
        if (std::string(argv[1]) == "-")
        {
            proof_io::StdinBuffer buffer;
            std::istream input(&buffer);
            proof.read(input);
        }
        else
        {
            std::ifstream input(argv[1]);
            proofcheck::require(bool(input), "cannot open proof");
            // Reserve exact graph storage from the footer for large saved proofs.
            input.seekg(0, std::ios::end);
            const auto bytes = input.tellg();
            input.seekg(bytes > std::streamoff(256) ? bytes - std::streamoff(256)
                                                    : std::streampos(0));
            std::string line;
            std::uint64_t graph_count = 0;
            while (std::getline(input, line))
                if (line.starts_with("end "))
                {
                    std::istringstream footer(line);
                    std::string tag;
                    footer >> tag >> graph_count;
                }
            input.clear();
            input.seekg(0);
            proof.graphs.reserve(graph_count);
            proof.read(input);
        }
        for (const auto& path : bindings)
        {
            std::ifstream input(path);
            proofcheck::require(bool(input), "cannot open physical binding file");
            proof.bind_roots(input);
        }
        if (proof.physical_roots_bound)
            std::cout << "additional_physical_roots " << proof.physical_roots_bound << '\n';
        std::cout << "verified " << (proof.result ? "win" : "loss") << "\nfacts "
                  << proof.facts_checked << "\ncofactors " << proof.cofactor_checks
                  << "\ndominance_implications " << proof.dominance_checks << '\n';
        return 0;
    }
    catch (const std::exception& error)
    {
        std::cerr << "rejected " << error.what() << '\n';
        return 2;
    }
    catch (const selfdual::PhysicalLimit&)
    {
        std::cerr << "incomplete initial BDD equivalence check\n";
        return 1;
    }
}

