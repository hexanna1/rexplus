#pragma once
#include <chrono>
#include <cmath>
#include <stdexcept>
#include <exception>

namespace rexplus::completion {

struct SearchBudgetReached : std::exception
{
    explicit SearchBudgetReached(const char* cause) : cause(cause) {}
    const char* what() const noexcept override { return cause; }
    const char* cause;
};

class SearchBudget
{
public:
    SearchBudget(double seconds = 0)
    {
        using Clock = std::chrono::steady_clock;
        const double maximum = std::chrono::duration<double>(Clock::duration::max()).count();
        if (!std::isfinite(seconds) || seconds < 0 || seconds >= maximum)
            throw std::invalid_argument("invalid search time");
        if (seconds > 0)
        {
            const auto now = Clock::now();
            const auto span = std::chrono::duration_cast<Clock::duration>(
                std::chrono::duration<double>(seconds));
            deadline = now > Clock::time_point::max() - span
                ? Clock::time_point::max() : now + span;
        }
    }

    bool limited() const { return deadline != std::chrono::steady_clock::time_point{}; }
    bool expired() const
    {
        return limited() && std::chrono::steady_clock::now() >= deadline;
    }
    void check() const
    {
        if (expired())
            throw SearchBudgetReached("time");
    }

private:
    std::chrono::steady_clock::time_point deadline{};
};

} // namespace rexplus::completion
