// A physical self-dual tail certifies a winning Rex+ prefix, by existence.
#include "physical_connectivity.hpp"
#include <functional>
#include <sstream>
using namespace selfdual;
int main(int argc, char** argv)
{
    try
    {
        require(argc == 2, "usage: rexplus_prefix_checker CERTIFICATE|- ");
        std::ifstream file;
        std::istream* input = &std::cin;
        if (std::string(argv[1]) != "-")
        {
            file.open(argv[1]);
            require(bool(file), "cannot open certificate");
            input = &file;
        }
        auto& in = *input;
        std::string tag, black_text, white_text, prefix_text;
        int size = 0, turn = -1, result = -1;
        in >> tag >> size >> black_text >> white_text >> turn >> result;
        require(bool(in) && tag == "position", "missing position record");
        require((turn == 0 || turn == 1) && result == 1, "certificate must claim a mover win");
        initialize_board(size);
        const auto black = parse_cells(black_text), white = parse_cells(white_text);
        require(!(black & white), "position colors overlap");
        require(!connected(black, 0) && !connected(white, 1), "initial position is terminal");
        in >> tag >> prefix_text;
        require(bool(in) && tag == "prefix", "missing prefix record");
        const auto prefix = parse_cells(prefix_text);
        require(prefix && !(prefix & (black | white)),
                "prefix must be nonempty and physically legal");
        const auto child_black = black | (turn == 0 ? prefix : 0),
                   child_white = white | (turn == 1 ? prefix : 0);
        require(!connected(child_black, 0) && !connected(child_white, 1),
                "prefix connects its mover's goals");
        const auto empty = Board & ~(child_black | child_white);
        unsigned count = 0;
        in >> tag >> count;
        require(bool(in) && tag == "mapping" && count == unsigned(std::popcount(empty)),
                "mapping must cover the full physical child domain");
        std::array<unsigned, 64> physical_map{};
        std::uint64_t image = 0;
        for (auto work = empty; work; work &= work - 1)
        {
            const unsigned p = std::countr_zero(work);
            unsigned q = 64;
            in >> q;
            require(bool(in) && q < unsigned(Cells), "invalid mapped cell");
            require((empty & bit(q)) && !(image & bit(q)),
                    "mapping is not a physical bijection");
            image |= bit(q);
            physical_map[p] = q;
        }
        require(image == empty, "mapping is not onto");
        in >> tag;
        require(bool(in) && tag == "end", "missing end record");
        require(!(in >> tag), "trailing certificate record");
        ConnectivityBDD bdd(60, 2000000);
        FrontierConnectivity frontier(bdd, true);
        const auto root = frontier.build(child_black, child_white);
        require(root >= 2, "prefix reaches a terminal Boolean predicate");
        std::array<unsigned, 64> permutation{}, inverse{};
        for (auto work = empty; work; work &= work - 1)
        {
            const unsigned p = std::countr_zero(work);
            const unsigned a = std::countr_zero(frontier.ordered(bit(p))),
                           b = std::countr_zero(frontier.ordered(bit(physical_map[p])));
            permutation[a] = b;
            inverse[b] = a;
        }
        std::unordered_map<std::uint64_t, bool> memo;
        std::uint64_t comparisons = 0;
        std::function<bool(std::uint32_t, std::uint32_t)> dual_equal = [&](auto a, auto b) {
            if (a < 2 && b < 2)
                return a + b == 1;
            const auto key = (std::uint64_t{a} << 32) | b;
            if (const auto it = memo.find(key); it != memo.end())
                return it->second;
            ++comparisons;
            auto support = bdd.support(a);
            for (auto work = bdd.support(b); work; work &= work - 1)
                support |= bit(inverse[std::countr_zero(work)]);
            require(support != 0, "nonterminal without support");
            const unsigned p = std::countr_zero(support), q = permutation[p];
            const bool value =
                dual_equal(bdd.cofactor(a, p, false), bdd.cofactor(b, q, true))
                && dual_equal(bdd.cofactor(a, p, true), bdd.cofactor(b, q, false));
            memo.emplace(key, value);
            return value;
        };
        require(dual_equal(root, root),
                "physical tail predicate is not color-self-dual under mapping");
        // Color exchange maps every legal complete batch to a legal complete batch
        // on this SAME physical domain. Hence its two mover-relative values agree.
        // The mover's prefix can end if the opponent loses, or continue if the mover
        // wins. !F(opponent) || F(mover) is therefore true in either possible case.
        std::cout << "{\"checked\":true,\"size\":" << size << ",\"black\":\"" << black_text
                  << "\",\"white\":\"" << white_text << "\",\"turn\":" << turn
                  << ",\"result\":1,\"prefix\":\"" << prefix_text
                  << "\",\"physical_empty_count\":" << count
                  << ",\"physical_dead_count\":" << count - std::popcount(bdd.support(root))
                  << ",\"bdd_nodes\":" << bdd.size() << ",\"dual_pair_checks\":" << comparisons
                  << ",\"frontier_states\":" << frontier.frontier_states() << "}\n";
        return 0;
    }
    catch (const PhysicalLimit&)
    {
        std::cerr << "Boolean audit resource limit\n";
        return 2;
    }
    catch (const std::exception& e)
    {
        std::cerr << e.what() << '\n';
        return 1;
    }
}
