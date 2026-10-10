#include "completion_hypergraph.hpp"
#include "search_limits.hpp"

using namespace rexplus::completion;

int main(int argc, char** argv)
{
    std::ios::sync_with_stdio(false);
    try
    {
        if (argc < 5)
            throw std::invalid_argument("usage: rexplus_hypergraph N BLACK WHITE black|white "
                                        "[--time SECONDS] [--pool-mb MB] [--fold-labels]");
        Position position(std::stoi(argv[1]));
        position.set_position(argv[2], argv[3]);
        const std::string turn = argv[4];
        if (turn != "black" && turn != "white")
            throw std::invalid_argument("turn must be black or white");
        const bool black = turn == "black";
        double seconds = 0;
        std::uint64_t memory = 0;
        bool fold = false;
        for (int i = 5; i < argc; ++i)
        {
            const std::string option = argv[i];
            if (option == "--fold-labels")
                fold = true;
            else if (option == "--time" || option == "--pool-mb")
            {
                if (++i == argc)
                    throw std::invalid_argument("missing value for " + option);
                if (option == "--time")
                    seconds = search_limits::seconds(argv[i]);
                else
                    memory = search_limits::pool_bytes(argv[i]);
            }
            else
                throw std::invalid_argument("unknown option: " + option);
        }
        Solver solver(memory, CertificatePolicy::All, fold);
        solver.begin_query(seconds);
        const auto edges = position.minimal_completions(solver.query_budget());
        const bool value = solver.solve(position.remaining, edges, black);
        const auto batch = value ? solver.winning_batch(position.remaining, edges, black) : 0;
        std::cout
            << "board_size " << position.size << '\n'
            << "black " << position.board_names(position.black) << '\n'
            << "white " << position.board_names(position.white) << '\n'
            << "to_play " << turn << '\n'
            << "result " << (value ? "win" : "loss") << '\n'
            << "minimal_completions " << edges.size() << '\n'
            << "hypergraphs " << solver.hypergraphs() << '\n'
            << "states " << solver.states() << '\n';
        if (value)
            std::cout << "winning_batch " << position.names(batch) << '\n';
        return 0;
    }
    catch (const SearchBudgetReached& budget)
    {
        std::cout << "result unknown\nbudget " << budget.what() << '\n';
        return 1;
    }
    catch (const std::exception& error)
    {
        std::cerr << "error: " << error.what() << '\n';
        return 2;
    }
}
