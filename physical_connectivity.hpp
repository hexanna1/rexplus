#pragma once
// Exact physical Boolean connectivity; no game-solving recurrence is included.
#include <algorithm>
#include <array>
#include <bit>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <optional>
#include <span>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <vector>
namespace selfdual {
using Edge = std::uint32_t;
struct PhysicalLimit
{
};
[[noreturn]] inline void fail(const std::string& message)
{
    throw std::runtime_error(message);
}
inline void require(bool condition, const char* message)
{
    if (!condition)
        fail(message);
}
inline int Size, Cells;
inline std::uint64_t Board, Left, Right;
constexpr std::uint64_t bit(int point)
{
    return std::uint64_t{1} << point;
}
inline std::vector<std::uint64_t> Neighbors;
std::vector<std::uint64_t> make_neighbors()
{
    std::vector<std::uint64_t> result(Cells);
    constexpr std::array<std::pair<int, int>, 6> directions{
        {{0, 1}, {0, -1}, {1, 0}, {-1, 0}, {-1, 1}, {1, -1}}};
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
bool connected(std::uint64_t stones, int color)
{
    const std::uint64_t first = color == 0 ? bit(Size) - 1 : Left;
    const std::uint64_t second = color == 0 ? first << (Cells - Size) : Right;
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
        const std::string name =
            text.substr(start, end == std::string::npos ? end : end - start);
        if (name.size() != 2 || name[0] < 'a' || name[0] >= 'a' + Size
            || name[1] < '1' || name[1] > '0' + Size)
            throw std::invalid_argument("invalid cell: " + name);
        const std::uint64_t cell = bit((name[1] - '1') * Size + name[0] - 'a');
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
class ConnectivityBDD
{
public:
    struct Node
    {
        std::uint64_t support = 0;
        std::uint32_t low = 0, high = 0, normalized = 0;
        std::uint8_t variable = 0;
    };
    ConnectivityBDD(double seconds, std::size_t limit) : node_limit(limit)
    {
        nodes.resize(2);
        index.resize(1024);
        cofactors.resize(1 << 20);
        if (seconds > 0)
            deadline = std::chrono::steady_clock::now()
                       + std::chrono::duration_cast<std::chrono::steady_clock::duration>(
                           std::chrono::duration<double>(seconds));
    }
    void poll()
    {
        if ((++operations & 2047) == 0 && deadline != std::chrono::steady_clock::time_point{}
            && std::chrono::steady_clock::now() >= deadline)
            throw PhysicalLimit{};
    }
    std::uint32_t make(int variable, std::uint32_t low, std::uint32_t high)
    {
        poll();
        if (low == high)
            return low;
        auto slot = node_hash(variable, low, high) & (index.size() - 1);
        while (index[slot])
        {
            const auto id = index[slot];
            const auto& node = nodes[id];
            if (node.variable == variable && node.low == low && node.high == high)
                return id;
            slot = (slot + 1) & (index.size() - 1);
        }
        if (nodes.size() >= node_limit)
            throw PhysicalLimit{};
        const auto id = static_cast<std::uint32_t>(nodes.size());
        nodes.push_back({bit(variable) | nodes[low].support | nodes[high].support,
                         low,
                         high,
                         0,
                         static_cast<std::uint8_t>(variable)});
        index[slot] = id;
        if (nodes.size() * 4 > index.size() * 3)
            grow_index();
        return id;
    }
    std::uint32_t cofactor(std::uint32_t id, int variable, bool present)
    {
        poll();
        if (!(nodes[id].support & bit(variable)))
            return id;
        const auto key = (std::uint64_t{id} << 7) | (variable << 1) | present;
        const auto home = node_hash(key & 127, key >> 7, 0) & (cofactors.size() - 1);
        for (std::size_t offset = 0; offset < 4; ++offset)
        {
            const auto& entry = cofactors[(home + offset) & (cofactors.size() - 1)];
            if (!entry.key)
                break;
            if (entry.key == key)
                return entry.result;
        }
        const Node node = nodes[id];
        const auto result = node.variable == variable
                                ? (present ? node.high : node.low)
                                : make(node.variable,
                                       cofactor(node.low, variable, present),
                                       cofactor(node.high, variable, present));
        auto target = home;
        for (std::size_t offset = 0; offset < 4; ++offset)
        {
            const auto slot = (home + offset) & (cofactors.size() - 1);
            if (!cofactors[slot].key || cofactors[slot].key == key)
            {
                target = slot;
                break;
            }
        }
        if (!cofactors[target].key)
            ++cofactor_entries;
        cofactors[target] = {key, result};
        return result;
    }
    std::uint64_t support(std::uint32_t id) const
    {
        return nodes[id].support;
    }
    static std::uint64_t node_hash(int variable, std::uint32_t low, std::uint32_t high)
    {
        auto value = (std::uint64_t{low} << 32) | high;
        value ^= std::uint64_t(variable) * 0x9e3779b97f4a7c15ULL;
        value ^= value >> 30;
        value *= 0xbf58476d1ce4e5b9ULL;
        value ^= value >> 27;
        value *= 0x94d049bb133111ebULL;
        return value ^ (value >> 31);
    }
    void grow_index()
    {
        index.assign(index.size() * 2, 0);
        for (std::uint32_t id = 2; id < nodes.size(); ++id)
        {
            const auto& node = nodes[id];
            auto slot = node_hash(node.variable, node.low, node.high) & (index.size() - 1);
            while (index[slot])
                slot = (slot + 1) & (index.size() - 1);
            index[slot] = id;
        }
    }
    std::size_t size() const
    {
        return nodes.size();
    }

private:
    std::vector<Node> nodes;
    std::vector<std::uint32_t> index;
    struct CofactorEntry
    {
        std::uint64_t key = 0;
        std::uint32_t result = 0;
    };
    std::vector<CofactorEntry> cofactors;
    std::size_t cofactor_entries = 0, node_limit;
    std::uint64_t operations = 0;
    std::chrono::steady_clock::time_point deadline{};
};
class FrontierConnectivity
{
public:
    FrontierConnectivity(ConnectivityBDD& manager, bool diagonal)
        : bdd(manager), neighbors(make_neighbors())
    {
        if (diagonal)
        {
            for (int d = 0; d < 2 * Size - 1; ++d)
                for (int row = 0; row < Size; ++row)
                    if (d - row >= 0 && d - row < Size)
                        order.push_back(row * Size + d - row);
        }
        else
            for (int point = 0; point < Cells; ++point)
                order.push_back(point);
        for (int level = 0; level < Cells; ++level)
            rank[order[level]] = level;
        frontier.resize(Cells + 1);
        memo.resize(Cells);
        for (int level = 0; level <= Cells; ++level)
            for (int previous = 0; previous < level; ++previous)
            {
                const int point = order[previous];
                bool needed = false;
                for (auto work = neighbors[point]; work; work &= work - 1)
                    needed |= rank[std::countr_zero(work)] >= level;
                if (needed)
                    frontier[level].push_back(point);
            }
    }

    std::uint32_t build(std::uint64_t black, std::uint64_t white)
    {
        fixed_black = black;
        fixed_white = white;
        for (auto& table : memo)
            table.clear();
        return visit(0, 0x21);
    }

    std::uint64_t ordered(std::uint64_t physical) const
    {
        std::uint64_t result = 0;
        for (auto work = physical; work; work &= work - 1)
            result |= bit(rank[std::countr_zero(work)]);
        return result;
    }

    std::uint64_t physical(std::uint64_t ordered_mask) const
    {
        std::uint64_t result = 0;
        for (auto work = ordered_mask; work; work &= work - 1)
            result |= bit(order[std::countr_zero(work)]);
        return result;
    }

    std::uint64_t frontier_states() const
    {
        std::uint64_t count = 0;
        for (const auto& table : memo)
            count += table.size();
        return count;
    }

private:
    std::uint32_t visit(int level, std::uint64_t signature)
    {
        bdd.poll();
        if (level == Cells)
            return 0;
        if (const auto found = memo[level].find(signature); found != memo[level].end())
            return found->second;
        const int point = order[level];
        auto branch = [&](bool present) {
            std::array<int, 16> labels{};
            const int previous_count = static_cast<int>(frontier[level].size()) + 2;
            int largest = 0;
            for (int slot = 0; slot < previous_count; ++slot)
            {
                labels[slot] = (signature >> (slot * 4)) & 15;
                largest = std::max(largest, labels[slot]);
            }
            labels[previous_count] = present ? largest + 1 : 0;
            auto join = [&](int slot) {
                const int from = labels[slot], to = labels[previous_count];
                if (!from || !to || from == to)
                    return;
                for (int i = 0; i <= previous_count; ++i)
                    if (labels[i] == from)
                        labels[i] = to;
            };
            if (present)
            {
                if (bit(point) & Left)
                    join(0);
                if (bit(point) & Right)
                    join(1);
                for (int slot = 2; slot < previous_count; ++slot)
                    if (neighbors[point] & bit(frontier[level][slot - 2]))
                        join(slot);
                if (labels[0] == labels[1])
                    return std::uint32_t{1};
            }
            std::array<int, 16> canonical{};
            int next_label = 0;
            std::uint64_t next_signature = 0;
            auto append = [&](int label, int slot) {
                if (label && !canonical[label])
                    canonical[label] = ++next_label;
                next_signature |= std::uint64_t(canonical[label]) << (slot * 4);
            };
            append(labels[0], 0);
            append(labels[1], 1);
            int slot = 2;
            for (int next_point : frontier[level + 1])
            {
                int label = labels[previous_count];
                if (next_point != point)
                {
                    const auto found =
                        std::find(frontier[level].begin(), frontier[level].end(), next_point);
                    label = labels[2 + (found - frontier[level].begin())];
                }
                append(label, slot++);
            }
            return visit(level + 1, next_signature);
        };
        std::uint32_t result;
        if (fixed_black & bit(point))
            result = branch(false);
        else if (fixed_white & bit(point))
            result = branch(true);
        else
        {
            const auto low = branch(false);
            const auto high = branch(true);
            result = bdd.make(level, low, high);
        }
        memo[level].emplace(signature, result);
        return result;
    }

    ConnectivityBDD& bdd;
    std::vector<std::uint64_t> neighbors;
    std::vector<int> order;
    std::array<int, 64> rank{};
    std::vector<std::vector<int>> frontier;
    std::vector<std::unordered_map<std::uint64_t, std::uint32_t>> memo;
    std::uint64_t fixed_black = 0, fixed_white = 0;
};

} // namespace selfdual
