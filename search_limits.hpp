#pragma once

#include <charconv>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <limits>
#include <stdexcept>
#include <string>

namespace search_limits {

inline double seconds(const std::string& value)
{
    std::size_t used = 0;
    double parsed = 0;
    try
    {
        parsed = std::stod(value, &used);
    }
    catch (const std::exception&)
    {
        throw std::invalid_argument("invalid search time");
    }
    const double maximum =
        std::chrono::duration<double>(std::chrono::steady_clock::duration::max()).count();
    if (used != value.size() || !std::isfinite(parsed) || parsed < 0 || parsed >= maximum)
        throw std::invalid_argument("invalid search time");
    return parsed;
}

inline std::uint64_t pool_bytes(const std::string& value)
{
    std::uint64_t megabytes = 0;
    const auto [end, error] =
        std::from_chars(value.data(), value.data() + value.size(), megabytes);
    if (error != std::errc{} || end != value.data() + value.size()
        || megabytes > (std::numeric_limits<std::uint64_t>::max() >> 20))
        throw std::invalid_argument("invalid pool size");
    return megabytes << 20;
}

} // namespace search_limits
