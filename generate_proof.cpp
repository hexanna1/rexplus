#include "completion_hypergraph.hpp"
#include "proof_exporter.hpp"
#include "search_limits.hpp"
#include <fstream>

using namespace rexplus::completion;

int main(int argc, char** argv)
{
    std::ios::sync_with_stdio(false);
    std::cin.tie(nullptr);
    try
    {
        if (argc < 6 || argc > 8)
            throw std::invalid_argument("usage: rexplus_proof_generator N BLACK WHITE "
                                        "black|white OUTPUT [SECONDS] [POOL_MB]");
        Position position(std::stoi(argv[1]));
        position.set_position(argv[2], argv[3]);
        const std::string turn = argv[4];
        if (turn != "black" && turn != "white")
            throw std::invalid_argument("turn must be black or white");
        const bool black = turn == "black";
        const auto memory = argc > 7 ? search_limits::pool_bytes(argv[7]) : 512ULL << 20;
        const auto seconds = argc > 6 ? search_limits::seconds(argv[6]) : 30;
        Solver solver(memory, CertificatePolicy::Proof, true);
        solver.begin_query(seconds);
        const auto edges = position.minimal_completions(solver.query_budget());
        const bool value = solver.solve(position.remaining, edges, black);
        std::ofstream file;
        std::ostream* output = &std::cout;
        const bool stream = std::string(argv[5]) == "-";
        if (!stream)
        {
            file.open(argv[5]);
            if (!file)
                throw std::runtime_error("cannot open proof output");
            output = &file;
        }
        ProofExporter exporter(solver, *output);
        exporter.write(position, position.remaining, edges, black);
        auto& summary = stream ? std::cerr : std::cout;
        summary
            << "result " << (value ? "win" : "loss") << "\nproof_graphs " << exporter.graphs()
            << "\nproof_facts " << exporter.facts() << "\nsearch_graphs "
            << solver.hypergraphs() << "\nsearch_states " << solver.states() << '\n';
        return 0;
    }
    catch (const SearchBudgetReached& budget)
    {
        auto& summary = argc > 5 && std::string(argv[5]) == "-" ? std::cerr : std::cout;
        summary << "result unknown\nbudget " << budget.what() << '\n';
        return 1;
    }
    catch (const std::exception& error)
    {
        std::cerr << "error: " << error.what() << '\n';
        return 2;
    }
}
