#pragma once
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <span>

namespace completion_label_folding {

// Relabel an already packed domain. This is partial folding: equal refinement
// scores retain their current order. The pool still compares every edge.
inline void relabel(std::span<std::uint32_t> edges,
                    unsigned count,
                    std::array<unsigned, 32>* permutation = nullptr)
{
    if (permutation)
        for (unsigned i = 0; i < count; ++i)
            (*permutation)[i] = i;
    if (count < 5 || count > 16)
        return;

    std::array<std::uint64_t, 32> key{}, next{}, mixed{};
    std::array<unsigned, 32> order{}, target{};
    for (auto edge : edges)
    {
        const auto weight = std::uint64_t{1} << (32 - std::popcount(edge));
        for (auto work = edge; work; work &= work - 1)
            key[std::countr_zero(work)] += weight;
    }
    auto mix = [](std::uint64_t value) {
        value ^= value >> 30;
        value *= 0xbf58476d1ce4e5b9ULL;
        value ^= value >> 27;
        value *= 0x94d049bb133111ebULL;
        return value ^ (value >> 31);
    };
    // One incidence-refinement round. Scores determine only a permutation;
    // collisions can reduce folding, but cannot identify different families.
    for (unsigned i = 0; i < count; ++i)
        mixed[i] = mix(key[i]);
    for (auto edge : edges)
    {
        std::uint64_t code = std::popcount(edge);
        for (auto work = edge; work; work &= work - 1)
            code += mixed[std::countr_zero(work)];
        code = mix(code);
        for (auto work = edge; work; work &= work - 1)
            next[std::countr_zero(work)] += code;
    }
    for (unsigned i = 0; i < count; ++i)
    {
        key[i] = mix(key[i]) + next[i];
        order[i] = i;
    }
    std::sort(order.begin(), order.begin() + count, [&](unsigned a, unsigned b) {
        return key[a] != key[b] ? key[a] < key[b] : a < b;
    });
    bool changed = false;
    for (unsigned i = 0; i < count; ++i)
    {
        target[order[i]] = i;
        changed |= order[i] != i;
    }
    if (permutation)
        *permutation = target;
    if (!changed)
        return;

    std::array<std::array<std::uint32_t, 16>, 4> remap{};
    for (unsigned part = 0; part < 4; ++part)
        for (unsigned value = 1; value < 16; ++value)
        {
            const unsigned cell = part * 4 + std::countr_zero(value);
            remap[part][value] = remap[part][value & (value - 1)]
                                 | (cell < count ? std::uint32_t{1} << target[cell] : 0);
        }
    for (auto& edge : edges)
        edge = remap[0][edge & 15] | remap[1][(edge >> 4) & 15] | remap[2][(edge >> 8) & 15]
               | remap[3][(edge >> 12) & 15];
    // Both sorts use stack storage and perform no allocation.
    std::sort(edges.begin(), edges.end());
}

} // namespace completion_label_folding
