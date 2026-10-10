#pragma once
#include <cstdint>
#include <type_traits>

struct PackedEdge24
{
    std::uint8_t bytes[3];
    PackedEdge24() = default;
    PackedEdge24(std::uint32_t value) noexcept
        : bytes{static_cast<std::uint8_t>(value),
                static_cast<std::uint8_t>(value >> 8),
                static_cast<std::uint8_t>(value >> 16)}
    {
    }
    operator std::uint32_t() const noexcept
    {
        return std::uint32_t{bytes[0]} | (std::uint32_t{bytes[1]} << 8)
               | (std::uint32_t{bytes[2]} << 16);
    }
};
static_assert(sizeof(PackedEdge24) == 3);
static_assert(alignof(PackedEdge24) == 1);
static_assert(std::is_trivially_copyable_v<PackedEdge24>);
