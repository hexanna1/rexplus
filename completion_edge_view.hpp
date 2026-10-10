#pragma once

#include "completion_packed_edge.hpp"
#include <algorithm>
#include <array>
#include <cstdint>
#include <span>
#include <utility>
#include <vector>

// An expanded frame owns its narrow-to-wide decoding. Access derives the
// pointer from this object's storage, so copying/moving/NRVO are all safe.
// Wide arena spans remain direct and stable across recursive pool growth.
class DecodedEdges
{
public:
    explicit DecodedEdges(std::span<const std::uint32_t> edges)
        : wide(edges), count(edges.size())
    {
    }

    explicit DecodedEdges(std::span<const std::uint16_t> edges) : count(edges.size())
    {
        if (count > StackEdges)
            large.resize(count);
        std::copy(edges.begin(), edges.end(), mutable_data());
    }

    explicit DecodedEdges(std::span<const PackedEdge24> edges) : count(edges.size())
    {
        if (count > StackEdges)
            large.resize(count);
        std::copy(edges.begin(), edges.end(), mutable_data());
    }

    DecodedEdges(const DecodedEdges& other)
        : wide(other.wide), count(other.count), large(other.large)
    {
        if (!wide.data() && count <= StackEdges)
            std::copy_n(other.small.data(), count, small.data());
    }
    DecodedEdges(DecodedEdges&& other) noexcept
        : wide(other.wide), count(other.count), large(std::move(other.large))
    {
        if (!wide.data() && count <= StackEdges)
            std::copy_n(other.small.data(), count, small.data());
        other.wide = {};
        other.count = 0;
    }
    DecodedEdges& operator=(const DecodedEdges& other)
    {
        if (this != &other)
        {
            large = other.large;
            wide = other.wide;
            count = other.count;
            if (!wide.data() && count <= StackEdges)
                std::copy_n(other.small.data(), count, small.data());
        }
        return *this;
    }
    DecodedEdges& operator=(DecodedEdges&& other) noexcept
    {
        if (this != &other)
        {
            wide = other.wide;
            count = other.count;
            large = std::move(other.large);
            if (!wide.data() && count <= StackEdges)
                std::copy_n(other.small.data(), count, small.data());
            other.wide = {};
            other.count = 0;
        }
        return *this;
    }

    std::size_t size() const
    {
        return count;
    }
    bool empty() const
    {
        return count == 0;
    }
    const std::uint32_t* data() const
    {
        return wide.data() ? wide.data() : count > StackEdges ? large.data() : small.data();
    }
    const std::uint32_t* begin() const
    {
        return data();
    }
    const std::uint32_t* end() const
    {
        return data() + count;
    }
    const std::uint32_t& operator[](std::size_t index) const
    {
        return data()[index];
    }
    std::span<const std::uint32_t> view() const
    {
        return {data(), count};
    }
    operator std::span<const std::uint32_t>() const
    {
        return view();
    }

private:
    static constexpr std::size_t StackEdges = 256;
    std::uint32_t* mutable_data()
    {
        return count > StackEdges ? large.data() : small.data();
    }
    std::span<const std::uint32_t> wide{};
    std::size_t count;
    std::array<std::uint32_t, StackEdges> small;
    std::vector<std::uint32_t> large;
};
