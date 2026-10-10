#pragma once
#include <array>
#include <bit>
#include <cstdint>
#include <span>

namespace completion_kernels {
using Edge = std::uint32_t;
enum class Kind : std::uint8_t {
    None,
    Triangle,
    PairGraph,
    PairProjection,
    Star,
    StarIndependent,
    StarPacking,
    DualTriangle,
    DualPairGraph,
    DualPairProjection,
    DualStar
};
struct Certificate
{
    int winner = -1;
    Edge keep = 0;
    Kind kind = Kind::None;
    Edge seed = 0;
    Edge extra = 0;
};
struct PairGraph
{
    std::array<Edge, 32> neighbors{};
    Edge active = 0, common = ~Edge{0};
    void add(Edge edge)
    {
        const Edge a = edge & -edge, b = edge ^ a;
        neighbors[std::countr_zero(a)] |= b;
        neighbors[std::countr_zero(b)] |= a;
        active |= edge;
        common &= edge;
    }
    Edge triangle() const
    {
        for (auto work = active; work; work &= work - 1)
        {
            const Edge a = work & -work;
            for (auto tail = neighbors[std::countr_zero(a)] & ~(a - 1); tail; tail &= tail - 1)
            {
                const Edge b = tail & -tail;
                const Edge c = neighbors[std::countr_zero(a)] & neighbors[std::countr_zero(b)];
                if (c)
                    return a | b | (c & -c);
            }
        }
        return 0;
    }
    Edge outside_pair(Edge vertices) const
    {
        for (auto work = active & ~vertices; work; work &= work - 1)
        {
            const Edge a = work & -work;
            const Edge b = neighbors[std::countr_zero(a)];
            if (b)
                return a | (b & -b);
        }
        return 0;
    }
    Edge matching(Edge& first_pair) const
    {
        for (auto work = active; work; work &= work - 1)
        {
            const Edge a = work & -work;
            for (auto tail = neighbors[std::countr_zero(a)]; tail; tail &= tail - 1)
            {
                const Edge first = a | (tail & -tail);
                for (auto other = active & ~first; other; other &= other - 1)
                {
                    const Edge c = other & -other;
                    const Edge d = neighbors[std::countr_zero(c)] & ~first;
                    if (d)
                    {
                        first_pair = first;
                        return first | c | (d & -d);
                    }
                }
            }
        }
        return 0;
    }
};

inline Certificate bound(std::span<const Edge> edges)
{
    if (edges.empty())
        return {};
    Edge active = 0, first = edges.front();
    PairGraph pairs;
    for (auto edge : edges)
    {
        active |= edge;
        const int size = std::popcount(edge);
        if (size == 2)
            pairs.add(edge);
        if (size < std::popcount(first))
            first = edge;
    }
    const int n = std::popcount(active), pn = std::popcount(pairs.active);
    if (n > 3)
        if (const auto triangle = pairs.triangle())
            return {1, triangle, Kind::Triangle};
    if (!pairs.common && pn >= 4)
    {
        Edge seed = 0;
        const auto kernel = pairs.matching(seed);
        if (pn >= 5)
            return {1, kernel, Kind::PairGraph, seed, pairs.outside_pair(kernel)};
        PairGraph projection;
        for (auto edge : edges)
        {
            const auto part = edge & kernel;
            if (std::popcount(part) < 2)
                return {1, kernel, Kind::PairProjection, seed};
            if (std::popcount(part) == 2)
                projection.add(part);
        }
        if (projection.triangle())
            return {1, kernel, Kind::PairProjection, seed};
    }
    if (std::has_single_bit(pairs.common))
    {
        const Edge center = pairs.common;
        const Edge leaves = pairs.neighbors[std::countr_zero(center)];
        // An r-leaf pair-star has value 1-2^-r. An independent r-cell
        // edge adds 2^(1-r); deleting one leaf leaves active value one.
        for (auto edge : edges)
        {
            if (edge & center)
                continue;
            const int size = std::popcount(edge);
            auto available = leaves & ~edge;
            if (std::popcount(available) < size)
                continue;
            Edge chosen = 0;
            for (int i = 0; i < size; ++i)
            {
                const Edge leaf = available & -available;
                chosen |= leaf;
                available ^= leaf;
            }
            // A one-leaf star vanishes, so consume its dead center too.
            const Edge keep = (size == 1 ? Edge{0} : center) | (chosen & (chosen - 1)) | edge;
            return {1, keep, Kind::StarIndependent, center, edge};
        }
        const int leaf_count = std::popcount(leaves);
        if (leaf_count >= 2)
        {
            Edge used = center | leaves, largest = 0;
            std::uint64_t total = 0;
            const auto threshold = std::uint64_t{1} << (31 - leaf_count);
            for (auto edge : edges)
            {
                if (edge & used)
                    continue;
                used |= edge;
                total += std::uint64_t{1} << (32 - std::popcount(edge));
                if (std::popcount(edge) > std::popcount(largest))
                    largest = edge;
                // Short edges were handled above. The surplus over the
                // threshold is at least the smallest packed edge weight.
                if (total > threshold)
                    return {1, used & ~largest, Kind::StarPacking, center, largest};
            }
        }
        for (auto edge : edges)
            if (!(edge & ~leaves) && std::popcount(edge) + 1 < n)
                return {1, center | edge, Kind::Star, center};
    }

    // Enumerate all two-element transversals through a smallest edge.
    PairGraph transversals;
    for (auto work = first; work; work &= work - 1)
    {
        const Edge cell = work & -work;
        Edge other = active & ~cell;
        for (auto edge : edges)
        {
            if (!(edge & cell))
                other &= edge;
            if (!other)
                break;
        }
        for (auto tail = other; tail; tail &= tail - 1)
        {
            const Edge second = tail & -tail;
            if (!(second & first) || cell < second)
                transversals.add(cell | second);
        }
    }
    if (n > 3)
        if (const auto triangle = transversals.triangle())
            return {0, triangle, Kind::DualTriangle};
    const int tn = std::popcount(transversals.active);
    if (!transversals.common && tn >= 4)
    {
        Edge seed = 0;
        const auto kernel = transversals.matching(seed);
        if (tn >= 5)
            return {0, kernel, Kind::DualPairGraph, seed, transversals.outside_pair(kernel)};
        if (pn < 4)
            return {0, kernel, Kind::DualPairProjection, seed};
    }
    if (std::has_single_bit(transversals.common))
    {
        const Edge center = transversals.common;
        const Edge leaves = transversals.neighbors[std::countr_zero(center)];
        if (std::popcount(leaves) >= 2)
        {
            bool hits = true;
            for (auto edge : edges)
                if (!(edge & leaves))
                {
                    hits = false;
                    break;
                }
            if (hits)
            {
                Edge kernel = center | leaves;
                if (kernel != active)
                    return {0, kernel, Kind::DualStar, center};
                const Edge removable = leaves & ~pairs.neighbors[std::countr_zero(center)];
                if (removable && std::popcount(leaves) >= 3)
                    return {0, kernel & ~(removable & -removable), Kind::DualStar, center};
            }
        }
    }
    return {};
}
} // namespace completion_kernels
