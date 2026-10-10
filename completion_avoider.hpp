#pragma once
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <span>

namespace completion_avoider {
using Edge = std::uint32_t;
constexpr std::uint64_t Half = std::uint64_t{1} << 31;

// The monotone Avoider-Enforcer potential criterion. Overlap is allowed.
inline bool white_only(std::span<const Edge> edges)
{
    std::uint64_t total = 0;
    for (auto edge : edges)
    {
        total += std::uint64_t{1} << (32 - std::popcount(edge));
        if (total >= Half)
            return false;
    }
    return true;
}

// With potential below one half, one minimum-incidence cell wins.
// A physical dead cell has zero incidence and is a valid choice too.
inline Edge white_batch(Edge remaining, std::span<const Edge> edges)
{
    std::array<std::uint64_t, 32> incidence{};
    for (auto edge : edges)
    {
        const auto weight = std::uint64_t{1} << (32 - std::popcount(edge));
        for (auto work = edge; work; work &= work - 1)
            incidence[std::countr_zero(work)] += weight;
    }
    Edge chosen = remaining & -remaining;
    for (auto work = remaining; work; work &= work - 1)
    {
        const auto cell = work & -work;
        if (incidence[std::countr_zero(cell)] < incidence[std::countr_zero(chosen)])
            chosen = cell;
    }
    return chosen;
}

struct Certificate
{
    bool black_loses = false;
    bool white_wins = false;
};

// A first Black placement deletes its incident terms. A White placement x
// doubles their weights; a subsequent Black placement y then removes the
// original incidence of y plus the incidence shared by x and y. Keep the raw
// terms: minimizing either cofactor could only strengthen these bounds.
inline Certificate one_step(std::span<const Edge> edges, bool need_white)
{
    std::uint64_t mass = 0;
    Edge active = 0;
    std::array<std::uint64_t, 32> incidence{};
    for (auto edge : edges)
    {
        const auto weight = std::uint64_t{1} << (32 - std::popcount(edge));
        mass += weight;
        active |= edge;
        for (auto work = edge; work; work &= work - 1)
            incidence[std::countr_zero(work)] += weight;
    }
    if (mass < Half)
        return {true, true};

    auto minimum = mass;
    for (auto work = active; work; work &= work - 1)
        minimum = std::min(minimum, incidence[std::countr_zero(work)]);
    if (mass - minimum >= Half)
        return {};
    if (!need_white)
        return {true, false};

    for (auto work = active; work; work &= work - 1)
    {
        const Edge cell = work & -work;
        if (std::find(edges.begin(), edges.end(), cell) != edges.end())
            continue;
        std::array<std::uint64_t, 32> shared{};
        for (auto edge : edges)
        {
            if (!(edge & cell))
                continue;
            const auto weight = std::uint64_t{1} << (32 - std::popcount(edge));
            for (auto tail = edge; tail; tail &= tail - 1)
                shared[std::countr_zero(tail)] += weight;
        }
        const auto after_white = mass + incidence[std::countr_zero(cell)];
        auto least_removed = after_white;
        for (auto tail = active & ~cell; tail; tail &= tail - 1)
        {
            const auto point = std::countr_zero(tail);
            least_removed = std::min(least_removed, incidence[point] + shared[point]);
        }
        if (after_white - least_removed < Half)
            return {true, true};
    }
    return {true, false};
}
} // namespace completion_avoider
