#pragma once

#include <array>
#include <bit>
#include <cstdint>
#include <span>
#include <unordered_map>

namespace small_kernel {

// Colors follow the native proof format: White is zero, Black is one.
// The truth table is always the White-connectivity predicate. Physical
// variables that disappear from that predicate still count toward its arity.
// A batch winning for exactly one color proves that color alone wins: in an
// N position the unique winning complete batch is the same for both colors
// (Keras, Theorem 3.1). The verifier checks that batch directly on a small
// retained physical domain, without recognizing a producer kernel pattern.
class Verifier
{
public:
    Verifier()
    {
        cache.reserve(8192);
    }

    bool certify(std::span<const std::uint32_t> edges,
                 std::uint32_t active,
                 std::uint32_t keep,
                 bool winner_is_black)
    {
        const unsigned winner = winner_is_black;
        if ((keep & ~active) || std::popcount(keep) > 5)
            return false;
        const auto batch = active & ~keep;
        if (!batch)
            return false;

        std::array<std::uint32_t, 5> labels{};
        unsigned count = 0;
        for (auto cells = keep; cells; cells &= cells - 1)
            labels[count++] = cells & -cells;

        const auto all = full_table(count);
        std::uint32_t after_black = 0;
        std::uint32_t after_white = 0;
        for (auto edge : edges)
        {
            auto term = all;
            for (unsigned variable = 0; variable < count; ++variable)
                if (edge & labels[variable])
                    term &= columns[variable];
            after_white |= term;
            if (!(edge & batch))
                after_black |= term;
        }

        const auto winner_child = winner ? after_black : after_white;
        const auto other_child = winner ? after_white : after_black;
        if (constant(count, winner_child))
            return false;
        if (outcomes(count, winner_child) & (1U << (winner ^ 1U)))
            return false;

        // The same batch must fail for the other color. It may be illegal;
        // otherwise it must hand the turn to a winning original winner.
        if (constant(count, other_child))
            return true;
        return outcomes(count, other_child) & (1U << winner);
    }

    std::size_t cached_functions() const
    {
        return cache.size();
    }

private:
    // Literal minimax over every nonempty complete batch. This deliberately
    // uses neither the producer's continue/end recurrence nor its pruning.
    // Return bit zero for White WIN and bit one for Black WIN.
    unsigned outcomes(unsigned count, std::uint32_t truth)
    {
        const auto key = (std::uint64_t{count} << 32) | truth;
        if (const auto found = cache.find(key); found != cache.end())
            return found->second;

        unsigned result = 0;
        const auto domain = (1U << count) - 1;
        for (auto batch = domain; batch; batch = (batch - 1) & domain)
        {
            const auto child_count = count - std::popcount(batch);
            for (unsigned color = 0; color < 2; ++color)
            {
                if (result & (1U << color))
                    continue;
                const auto child = cofactor(count, truth, batch, color == 0);
                if (!constant(child_count, child)
                    && !(outcomes(child_count, child) & (1U << (color ^ 1U))))
                    result |= 1U << color;
            }
            if (result == 3)
                break;
        }
        cache.emplace(key, result);
        return result;
    }

    static constexpr std::array<std::uint32_t, 5> columns{
        0xaaaaaaaaU, 0xccccccccU, 0xf0f0f0f0U, 0xff00ff00U, 0xffff0000U};

    static std::uint32_t full_table(unsigned count)
    {
        return count == 5 ? ~std::uint32_t{0} : (1U << (1U << count)) - 1;
    }

    static bool constant(unsigned count, std::uint32_t truth)
    {
        return !truth || truth == full_table(count);
    }

    static std::uint32_t
    cofactor(unsigned count, std::uint32_t truth, unsigned batch, bool white)
    {
        const auto child_count = count - std::popcount(batch);
        std::uint32_t child = 0;
        for (unsigned assignment = 0; assignment < (1U << child_count); ++assignment)
        {
            unsigned original = white ? batch : 0;
            unsigned next = 0;
            for (unsigned variable = 0; variable < count; ++variable)
            {
                if (batch & (1U << variable))
                    continue;
                if (assignment & (1U << next))
                    original |= 1U << variable;
                ++next;
            }
            if (truth & (1U << original))
                child |= 1U << assignment;
        }
        return child;
    }

    std::unordered_map<std::uint64_t, unsigned char> cache;
};

} // namespace small_kernel
