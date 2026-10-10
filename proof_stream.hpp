#pragma once

#include <array>
#include <cstdio>
#include <cstdint>
#include <istream>
#include <limits>
#include <string>
#include <type_traits>
#include <streambuf>

namespace proof_io {

class StdinBuffer final : public std::streambuf
{
    std::array<char, 65536> bytes;

public:
    StdinBuffer()
    {
        setg(bytes.data(), bytes.data(), bytes.data());
    }

protected:
    int_type underflow() override
    {
        if (gptr() < egptr())
            return traits_type::to_int_type(*gptr());
        const auto count = std::fread(bytes.data(), 1, bytes.size(), stdin);
        if (!count)
            return traits_type::eof();
        setg(bytes.data(), bytes.data(), bytes.data() + count);
        return traits_type::to_int_type(*gptr());
    }
};

// Decimal proof tokens, bounded buffering, and explicit malformed/EOF distinction.
class DecimalInput
{
    std::streambuf* source;
    std::array<char, 65536> buffer;
    const char* current = buffer.data();
    const char* end = buffer.data();
    bool failed = false, ended = false;
    static bool space(unsigned char c)
    {
        return c == ' ' || unsigned(c) - 9 <= 4;
    }
    bool refill()
    {
        const auto count = source->sgetn(buffer.data(), buffer.size());
        current = buffer.data();
        end = current + count;
        ended = count == 0;
        return !ended;
    }
    bool begin()
    {
        if (failed)
            return false;
        for (;;)
        {
            while (current != end && space(static_cast<unsigned char>(*current)))
                ++current;
            if (current != end)
            {
                const auto c = static_cast<unsigned char>(*current);
                if (c < 32 || c >= 127)
                {
                    failed = true;
                    return false;
                }
                return true;
            }
            if (!refill())
            {
                failed = true;
                return false;
            }
        }
    }

public:
    explicit DecimalInput(std::istream& input) : source(input.rdbuf()) {}
    explicit operator bool() const
    {
        return !failed;
    }
    bool at_end() const
    {
        return ended;
    }
    DecimalInput& operator>>(std::string& value)
    {
        value.clear();
        if (!begin())
            return *this;
        for (;;)
        {
            const char* start = current;
            while (current != end && !space(static_cast<unsigned char>(*current)))
            {
                const auto c = static_cast<unsigned char>(*current);
                if (c < 32 || c >= 127)
                {
                    failed = true;
                    return *this;
                }
                ++current;
            }
            value.append(start, current);
            if (current != end || !refill())
                return *this;
        }
    }
    template <class Integer>
        requires std::is_integral_v<Integer>
    DecimalInput& operator>>(Integer& value)
    {
        if (!begin())
            return *this;
        using U = std::make_unsigned_t<Integer>;
        constexpr U maximum = std::numeric_limits<Integer>::max();
        U parsed = 0;
        bool digit_seen = false;
        for (;;)
        {
            while (current != end)
            {
                const auto c = static_cast<unsigned char>(*current);
                const auto digit = unsigned(c) - unsigned('0');
                if (digit > 9)
                {
                    if (space(c) && digit_seen)
                        value = Integer(parsed);
                    else
                        failed = true;
                    return *this;
                }
                if (parsed > maximum / 10 || (parsed == maximum / 10 && digit > maximum % 10))
                {
                    failed = true;
                    return *this;
                }
                parsed = U(parsed * 10 + U(c - '0'));
                digit_seen = true;
                ++current;
            }
            if (!refill())
            {
                if (!digit_seen)
                    failed = true;
                else
                    value = Integer(parsed);
                return *this;
            }
        }
    }
};

} // namespace proof_io
