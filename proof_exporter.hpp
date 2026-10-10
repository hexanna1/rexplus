#pragma once
#include "completion_hypergraph.hpp"
#include <ostream>

namespace rexplus::completion {
class ProofExporter
{
public:
    ProofExporter(const Solver& solver, std::ostream& output)
        : solver(solver), output(output), exported(solver.pool.size(), Missing),
          emitted(solver.pool.size(), 0)
    {
    }

    void write(const Position& position, std::uint32_t remaining, std::vector<std::uint32_t> edges, bool black)
    {
        std::uint32_t support = 0;
        for (auto edge : edges)
            support |= edge;
        const auto root_mapping = canonicalize(edges);
        const auto root_id = solver.pool.lookup(edges);
        if (root_id == Missing)
            throw std::logic_error("root absent from exact pool");
        const Node root{root_id, black, (remaining & ~support) != 0};
        const bool value = exact(root);
        output << "position " << position.size << ' ' << position.board_names(position.black) << ' '
               << position.board_names(position.white) << ' ' << int(black) << ' ' << int(value) << '\n';
        output << "variables " << position.empty_cells.size();
        for (auto cell : position.empty_cells)
            output << ' ' << std::countr_zero(cell);
        output << '\n';
        graph_id(root_id);
        output << "root " << fact_id(root) << ' ' << support;
        write_mapping(root_mapping);
        output << '\n';
        emit(root);
        output << "end " << graph_count << ' ' << fact_count << '\n';
        output.flush();
        if (!output)
            throw std::runtime_error("proof output failed");
    }

    std::uint64_t graphs() const
    {
        return graph_count;
    }
    std::uint64_t facts() const
    {
        return fact_count;
    }

private:
    static constexpr std::uint32_t Missing = ~std::uint32_t{0};
    struct Node
    {
        std::uint32_t graph;
        bool black;
        bool dead;
    };
    struct Mapping
    {
        unsigned count = 0;
        std::array<unsigned, 32> target{};
    };
    struct Branch
    {
        unsigned cell;
        std::uint32_t child;
        Node opposite, self;
        Mapping mapping;
    };

    void write_mapping(const Mapping& mapping)
    {
        bool identity = true;
        for (unsigned i = 0; i < mapping.count; ++i)
            identity &= mapping.target[i] == i;
        std::uint64_t word = 0;
        if (!identity)
        {
            if (mapping.count > 16)
                throw std::logic_error("nonidentity proof map exceeds sixteen labels");
            for (unsigned i = 0; i < mapping.count; ++i)
                word |= std::uint64_t{mapping.target[i]} << (4 * i);
        }
        output << ' ' << word;
    }

    bool known(Node node) const
    {
        return solver.pool[node.graph].known[node.black] & (1U << node.dead);
    }

    bool exact(Node node) const
    {
        if (!known(node))
            throw std::logic_error("required proof fact is unfinished");
        return solver.pool[node.graph].wins[node.black] & (1U << node.dead);
    }

    std::uint32_t graph_id(std::uint32_t native)
    {
        auto& id = exported[native];
        if (id == Missing)
        {
            id = graph_count++;
            const auto edges = solver.pool.edges(native);
            output << "g " << id << ' ' << edges.size();
            for (auto edge : edges)
                output << ' ' << edge;
            output << '\n';
        }
        return id;
    }

    std::uint64_t fact_id(Node node) const
    {
        if (exported[node.graph] == Missing)
            throw std::logic_error("fact graph has no exported ID");
        return std::uint64_t{exported[node.graph]} * 4 + 2 * unsigned(node.black)
               + unsigned(node.dead);
    }

    static Mapping canonicalize(std::vector<std::uint32_t>& edges)
    {
        std::uint32_t support = 0;
        for (auto edge : edges)
            support |= edge;
        Mapping result;
        result.count = std::popcount(support);
        std::array<std::uint32_t, 32> image{};
        unsigned rank = 0;
        for (auto work = support; work; work &= work - 1, ++rank)
            image[std::countr_zero(work)] = std::uint32_t{1} << rank;
        for (auto& edge : edges)
        {
            std::uint32_t packed = 0;
            for (auto work = edge; work; work &= work - 1)
                packed |= image[std::countr_zero(work)];
            edge = packed;
        }
        completion_label_folding::relabel(edges, result.count, &result.target);
        return result;
    }

    std::vector<std::uint32_t> representatives(std::uint32_t id) const
    {
        const auto active = solver.pool[id].active;
        std::vector<unsigned> order;
        std::array<std::uint64_t, 32> influence{};
        for (auto work = active; work; work &= work - 1)
            order.push_back(std::countr_zero(work));
        if (order.size() > 7)
        {
            for (auto edge : solver.pool.edges(id))
            {
                const auto weight = std::uint64_t{1} << (32 - std::popcount(edge));
                for (auto work = edge; work; work &= work - 1)
                    influence[std::countr_zero(work)] += weight;
            }
            std::sort(order.begin(), order.end(), [&](auto a, auto b) {
                return influence[a] != influence[b] ? influence[a] < influence[b] : a < b;
            });
        }
        std::vector<std::uint32_t> result;
        auto work = active;
        for (auto vertex : order)
        {
            const auto cell = std::uint32_t{1} << vertex;
            if (!(work & cell))
                continue;
            result.push_back(cell);
            auto dominated = active;
            for (auto edge : solver.pool.edges(id))
                if (edge & cell)
                    dominated &= edge;
            work &= ~dominated;
        }
        return result;
    }

    bool elementary(std::uint32_t id) const
    {
        const auto active = solver.pool[id].active;
        std::uint32_t common = active, seen = 0;
        bool singleton = false, disjoint = true;
        for (auto edge : solver.pool.edges(id))
        {
            common &= edge;
            singleton |= std::has_single_bit(edge);
            disjoint &= !(seen & edge);
            seen |= edge;
        }
        return std::has_single_bit(active) || singleton || common || (disjoint && active);
    }

    std::uint32_t
    child(std::uint32_t id, std::uint32_t cell, bool black, bool& legal, Mapping& mapping) const
    {
        std::vector<std::uint32_t> edges;
        if (black)
        {
            edges = Solver::black_child(solver.pool.edges(id), cell);
            legal = !edges.empty();
        }
        else
            edges = Solver::white_child(solver.pool.edges(id), cell, legal);
        if (!legal)
            return Missing;
        mapping = canonicalize(edges);
        return solver.pool.lookup(edges);
    }

    bool emit_unfill(Node node, std::span<Node> dependencies, std::size_t& dependency_count)
    {
        for (auto cell : representatives(node.graph))
        {
            bool legal;
            Mapping mapping;
            const auto next = child(node.graph, cell, !node.black, legal, mapping);
            if (!legal || next == Missing)
                continue;
            const Node winner{next, !node.black, false};
            const Node loser{next, node.black, false};
            if (!known(winner) || !known(loser) || !exact(winner) || exact(loser))
                continue;
            graph_id(next);
            dependencies[dependency_count++] = winner;
            dependencies[dependency_count++] = loser;
            output << "f " << fact_id(node) << " 0 unfill " << std::countr_zero(cell) << ' '
                   << exported[next] << ' ' << fact_id(winner) << ' ' << fact_id(loser);
            write_mapping(mapping);
            output << '\n';
            return true;
        }
        return false;
    }

    void emit(Node node)
    {
        const auto bit = 1U << (2 * unsigned(node.black) + unsigned(node.dead));
        if (emitted[node.graph] & bit)
            return;
        const bool value = exact(node);
        emitted[node.graph] |= bit;
        ++fact_count;
        graph_id(node.graph);
        std::array<Node, 64> dependencies;
        std::size_t dependency_count = 0;
        const auto potential = completion_avoider::one_step(solver.pool.edges(node.graph),
                                                            node.dead || !node.black);
        const bool potential_proves =
            value == !node.black
            && (node.black ? potential.black_loses && (!node.dead || potential.white_wins)
                           : potential.white_wins);
        if (potential_proves)
            output << "f " << fact_id(node) << ' ' << int(value) << " potential\n";
        else if (node.dead)
        {
            const Node opposite{node.graph, !node.black, false};
            const Node self{node.graph, node.black, false};
            int mode;
            if (value)
            {
                if (known(opposite) && !exact(opposite))
                {
                    mode = 0;
                    dependencies[dependency_count++] = opposite;
                }
                else if (known(self) && exact(self))
                {
                    mode = 1;
                    dependencies[dependency_count++] = self;
                }
                else
                    throw std::logic_error("dead win has no exact proof dependency");
            }
            else
            {
                if (!exact(opposite) || exact(self))
                    throw std::logic_error("dead loss proof predicates disagree");
                mode = 2;
                dependencies[dependency_count++] = opposite;
                dependencies[dependency_count++] = self;
            }
            output << "f " << fact_id(node) << ' ' << int(value) << " dead " << mode;
            for (std::size_t i = 0; i < dependency_count; ++i)
                output << ' ' << fact_id(dependencies[i]);
            output << '\n';
        }
        else if (elementary(node.graph))
            output << "f " << fact_id(node) << ' ' << int(value) << " simple\n";
        else
        {
            std::vector<std::uint32_t> bound_order;
            const auto certificate =
                completion_bounds::bound(solver.pool.edges(node.graph), bound_order);
            const auto kernel = completion_kernels::bound(solver.pool.edges(node.graph));
            if (kernel.winner >= 0 && std::popcount(kernel.keep) <= 5)
            {
                if (value != (kernel.winner == int(node.black)))
                    throw std::logic_error("kernel proof disagrees with exact fact");
                output << "f " << fact_id(node) << ' ' << int(value) << " kernel "
                       << kernel.winner << ' ' << kernel.keep << '\n';
            }
            else if (certificate.winner >= 0)
            {
                if (value != (certificate.winner == int(node.black)))
                    throw std::logic_error("structural proof disagrees with exact fact");
                output << "f " << fact_id(node) << ' ' << int(value) << " bound "
                       << certificate.winner << ' ' << certificate.count;
                for (std::size_t i = 0; i < certificate.count; ++i)
                    output << ' ' << certificate.edges[i];
                output << '\n';
            }
            else if (value)
            {
                bool found = false;
                for (auto cell : representatives(node.graph))
                {
                    bool legal;
                    Mapping mapping;
                    const auto next = child(node.graph, cell, node.black, legal, mapping);
                    if (!legal || next == Missing)
                        continue;
                    const Node opposite{next, !node.black, false};
                    const Node self{next, node.black, false};
                    int mode;
                    if (known(opposite) && !exact(opposite))
                    {
                        mode = 0;
                        dependencies[dependency_count++] = opposite;
                    }
                    else if (known(self) && exact(self))
                    {
                        mode = 1;
                        dependencies[dependency_count++] = self;
                    }
                    else
                        continue;
                    graph_id(next);
                    output << "f " << fact_id(node) << " 1 win " << std::countr_zero(cell)
                           << ' ' << mode << ' ' << fact_id(dependencies[0]);
                    write_mapping(mapping);
                    output << '\n';
                    found = true;
                    break;
                }
                if (!found)
                    throw std::logic_error("winning state has no stored proof branch");
            }
            else if (!emit_unfill(node, dependencies, dependency_count))
            {
                std::array<Branch, 32> branches;
                std::size_t count = 0;
                for (auto cell : representatives(node.graph))
                {
                    bool legal;
                    Mapping mapping;
                    const auto next = child(node.graph, cell, node.black, legal, mapping);
                    if (!legal)
                        continue;
                    if (next == Missing)
                        throw std::logic_error("loss child absent from exact pool");
                    const Node opposite{next, !node.black, false};
                    const Node self{next, node.black, false};
                    if (!exact(opposite) || exact(self))
                        throw std::logic_error("loss proof child predicates disagree");
                    graph_id(next);
                    branches[count++] =
                        Branch{unsigned(std::countr_zero(cell)), next, opposite, self, mapping};
                    dependencies[dependency_count++] = opposite;
                    dependencies[dependency_count++] = self;
                }
                output << "f " << fact_id(node) << " 0 loss " << count;
                for (std::size_t i = 0; i < count; ++i)
                {
                    const auto& branch = branches[i];
                    output << ' ' << branch.cell << ' ' << exported[branch.child] << ' '
                           << fact_id(branch.opposite) << ' ' << fact_id(branch.self);
                    write_mapping(branch.mapping);
                }
                output << '\n';
            }
        }
        for (std::size_t i = 0; i < dependency_count; ++i)
            emit(dependencies[i]);
    }

    const Solver& solver;
    std::ostream& output;
    std::vector<std::uint32_t> exported;
    std::vector<std::uint8_t> emitted;
    std::uint32_t graph_count = 0;
    std::uint64_t fact_count = 0;
};
} // namespace rexplus::completion
