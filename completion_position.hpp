#pragma once
#include "search_budget.hpp"
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <deque>
#include <stdexcept>
#include <string>
#include <vector>

namespace rexplus::completion {

constexpr std::uint64_t bit(int point) { return std::uint64_t{1} << point; }

struct Position
{
    int size = 0;
    int cells = 0;
    std::uint64_t board = 0;
    std::uint64_t left = 0;
    std::uint64_t right = 0;
    std::vector<std::uint64_t> neighbors;
    std::uint64_t black = 0;
    std::uint64_t white = 0;
    std::uint64_t empty = 0;
    int empty_count = 0;
    std::uint32_t remaining = 0;
    std::vector<std::uint64_t> empty_cells;

    std::vector<std::uint64_t> make_neighbors() const
    {
        std::vector<std::uint64_t> result(cells);
        constexpr std::array<std::pair<int, int>, 6> directions{{
            {0, 1}, {0, -1}, {1, 0}, {-1, 0}, {-1, 1}, {1, -1}}};
        for (int point = 0; point < cells; ++point)
        {
            const int row = point / size;
            const int column = point % size;
            for (auto [dr, dc] : directions)
                if (const int rr = row + dr, cc = column + dc;
                    rr >= 0 && rr < size && cc >= 0 && cc < size)
                    result[point] |= bit(rr * size + cc);
        }
        return result;
    }

    bool connected(std::uint64_t stones, int color) const
    {
        const std::uint64_t first = color == 0 ? bit(size) - 1 : left;
        const std::uint64_t second = color == 0
            ? first << (cells - size) : right;
        std::uint64_t frontier = stones & first;
        std::uint64_t seen = frontier;
        while (frontier)
        {
            if (frontier & second)
                return true;
            std::uint64_t adjacent = 0;
            for (auto work = frontier; work; work &= work - 1)
                adjacent |= neighbors[std::countr_zero(work)];
            frontier = adjacent & stones & ~seen;
            seen |= frontier;
        }
        return false;
    }

    std::vector<std::uint64_t> make_empty_cells() const
    {
        std::vector<std::uint64_t> result;
        result.reserve(empty_count);
        for (auto work = empty; work; work &= work - 1)
            result.push_back(work & -work);
        return result;
    }

    std::uint64_t expand(std::uint32_t compact) const
    {
        std::uint64_t result = 0;
        for (auto work = compact; work; work &= work - 1)
            result |= empty_cells[std::countr_zero(work)];
        return result;
    }

    std::string board_names(std::uint64_t stones) const
    {
        std::string result;
        for (auto work = stones; work; work &= work - 1)
        {
            const int point = std::countr_zero(work);
            if (!result.empty())
                result += ',';
            result += char('a' + point % size);
            result += std::to_string(point / size + 1);
        }
        return result.empty() ? "-" : result;
    }

    std::string names(std::uint32_t compact) const
    {
        return board_names(expand(compact));
    }

    std::vector<std::uint32_t> minimal_completions(const SearchBudget& budget = {}) const
    {
        std::array<std::uint32_t, 64> weight{};
        for (int i = 0; i < empty_count; ++i)
            weight[std::countr_zero(empty_cells[i])] = std::uint32_t{1} << i;
        std::array<std::vector<std::uint32_t>, 64> carriers;
        std::deque<std::pair<int, std::uint32_t>> queue;
        std::vector<std::uint32_t> result;
        std::uint64_t work_count = 0;
        auto check = [&] { if ((work_count++ & 1023) == 0) budget.check(); };
        budget.check();
        auto insert = [&](auto& family, std::uint32_t carrier) {
            check();
            for (std::uint32_t edge : family)
            {
                check();
                if (!(edge & ~carrier)) return false;
            }
            std::erase_if(family, [&](std::uint32_t edge) {
                check();
                return !(carrier & ~edge);
            });
            family.push_back(carrier);
            return true;
        };
        for (auto work = left & ~black; work; work &= work - 1)
        {
            const int point = std::countr_zero(work);
            insert(carriers[point], weight[point]);
            queue.emplace_back(point, weight[point]);
        }
        while (!queue.empty())
        {
            check();
            auto [point, carrier] = queue.front();
            queue.pop_front();
            if (std::find(carriers[point].begin(), carriers[point].end(), carrier)
                == carriers[point].end())
                continue;
            bool finished = false;
            for (std::uint32_t edge : result)
            {
                check();
                if (!(edge & ~carrier))
                {
                    finished = true;
                    break;
                }
            }
            if (finished)
                continue;
            if (bit(point) & right)
            {
                insert(result, carrier);
                continue;
            }
            for (auto work = neighbors[point] & ~black;
                 work; work &= work - 1)
            {
                const int next = std::countr_zero(work);
                const auto extension = carrier | weight[next];
                if (insert(carriers[next], extension))
                    queue.emplace_back(next, extension);
            }
        }
        std::sort(result.begin(), result.end());
        budget.check();
        return result;
    }

    explicit Position(int board_size)
    {
        if (board_size < 1 || board_size > 8)
            throw std::invalid_argument("board size must be in 1..8");
        size = board_size;
        cells = size * size;
        board = cells == 64 ? ~std::uint64_t{0} : bit(cells) - 1;
        left = 0;
        for (int row = 0; row < size; ++row)
            left |= bit(row * size);
        right = left << (size - 1);
        neighbors = make_neighbors();
    }

    std::uint64_t parse_cells(const std::string& text) const
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
            if (name.size() != 2 || name[0] < 'a' || name[0] >= 'a' + size
                || name[1] < '1' || name[1] > '0' + size)
                throw std::invalid_argument("invalid cell: " + name);
            const std::uint64_t cell = bit((name[1] - '1') * size + name[0] - 'a');
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

    void set_position(const std::string& black_cells,
                      const std::string& white_cells)
    {
        black = parse_cells(black_cells);
        white = parse_cells(white_cells);
        if ((black & white)
            || connected(black, 0) || connected(white, 1))
            throw std::invalid_argument("initial position is terminal or overlaps");
        empty = board & ~(black | white);
        if (!connected(white | empty, 1))
            throw std::invalid_argument("White has no completion");
        empty_count = std::popcount(empty);
        if (empty_count > 32)
            throw std::invalid_argument(
                "completion construction supports at most 32 empty cells");
        remaining = empty_count == 32 ? ~std::uint32_t{0}
                                      : (std::uint32_t{1} << empty_count) - 1;
        empty_cells = make_empty_cells();
    }
};

} // namespace rexplus::completion
