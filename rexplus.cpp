#include <algorithm>
#include <array>
#include <bit>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <iomanip>
#include <initializer_list>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <string>
#include <string_view>
#include <tuple>
#include <unordered_set>
#include <unordered_map>
#include <vector>

namespace {

enum class Result : std::uint8_t { Loss = 0, Win = 1, Unknown = 2 };

const char* result_name(Result result)
{
    if (result == Result::Win)
        return "win";
    if (result == Result::Loss)
        return "loss";
    return "unknown";
}

struct Outcome
{
    Result black;
    Result white;
};

struct WinningSet
{
    Result result;
    std::vector<int> cells;
};

std::uint64_t mix64(std::uint64_t value)
{
    value ^= value >> 30;
    value *= 0xbf58476d1ce4e5b9ULL;
    value ^= value >> 27;
    value *= 0x94d049bb133111ebULL;
    return value ^ (value >> 31);
}

struct Key
{
    std::uint64_t black;
    std::uint64_t white;

    bool operator==(const Key& other) const
    {
        return black == other.black && white == other.white;
    }
};

std::uint64_t key_hash(const Key& key)
{
    return mix64(key.black ^ std::rotl(key.white, 23));
}

class TranspositionTable
{
public:
    TranspositionTable(int cells, std::size_t megabytes)
        : compact(cells <= 36)
    {
        constexpr std::size_t Scale = 1024ULL * 1024ULL;
        if (megabytes > std::numeric_limits<std::size_t>::max() / Scale)
            throw std::invalid_argument("transposition table is too large");
        std::size_t entry_size = compact ? sizeof(std::uint64_t)
                                         : sizeof(WideEntry);
        const std::size_t requested = megabytes * Scale / entry_size;
        std::size_t count = 1;
        while (count < requested && count < (std::size_t(1) << 34))
            count <<= 1;
        if (count > requested && count > 1)
            count >>= 1;
        count = std::max<std::size_t>(count, 1024);
        if (compact)
            compact_entries.resize(count);
        else
            wide_entries.resize(count);
        mask = count - 1;
    }

    bool find(const Key& key, std::uint64_t code,
              int color, Result& result, Result* other_result = nullptr,
              bool* other_witness = nullptr) const
    {
        if (other_result)
            *other_result = Result::Unknown;
        if (other_witness)
            *other_witness = false;
        if (!compact)
            return find_wide(key, color, result, other_result,
                             other_witness);
        const std::size_t home = mix64(code) & mask;
        const std::uint64_t wanted = code << MetaBits;
        for (std::size_t offset = 0; offset < ProbeCount; ++offset)
        {
            const std::uint64_t entry =
                compact_entries[(home + offset) & mask];
            if ((entry & ~MetaMask) == wanted)
            {
                const std::uint8_t known = entry & KnownMask;
                const std::uint8_t wins = (entry >> 2) & KnownMask;
                if (other_result || other_witness)
                {
                    const std::uint8_t other_bit =
                        std::uint8_t(1) << (color ^ 1);
                    if (other_result && (known & other_bit))
                        *other_result = wins & other_bit
                            ? Result::Win : Result::Loss;
                    if (other_witness)
                        *other_witness = entry
                            & (std::uint64_t(other_bit) << 4);
                }
                const std::uint8_t bit = std::uint8_t(1) << color;
                if (!(known & bit))
                    return false;
                result = wins & bit ? Result::Win : Result::Loss;
                return true;
            }
        }
        return false;
    }

    void store(const Key& key, std::uint64_t code, int color, Result result,
               bool witness = false)
    {
        if (!compact)
        {
            store_wide(key, color, result, witness);
            return;
        }
        const std::uint64_t wanted = code << MetaBits;
        const std::size_t home = mix64(code) & mask;
        std::size_t target = home;
        for (std::size_t offset = 0; offset < ProbeCount; ++offset)
        {
            const std::size_t index = (home + offset) & mask;
            const std::uint64_t entry = compact_entries[index];
            if (!entry || (entry & ~MetaMask) == wanted)
            {
                target = index;
                break;
            }
        }
        std::uint64_t entry = compact_entries[target];
        if ((entry & ~MetaMask) != wanted)
            entry = wanted;
        const std::uint64_t known_bit = std::uint64_t(1) << color;
        const std::uint64_t win_bit = std::uint64_t(1) << (color + 2);
        entry |= known_bit;
        if (result == Result::Win)
            entry |= win_bit;
        else
        {
            entry &= ~win_bit;
            entry &= ~(std::uint64_t(1) << (color + 4));
        }
        if (witness)
            entry |= std::uint64_t(1) << (color + 4);
        compact_entries[target] = entry;
    }

    std::size_t bytes() const
    {
        return compact ? compact_entries.size() * sizeof(std::uint64_t)
                       : wide_entries.size() * sizeof(WideEntry);
    }

private:
    static constexpr std::size_t ProbeCount = 8;
    static constexpr int MetaBits = 6;
    static constexpr std::uint64_t MetaMask = 0x3f;
    static constexpr std::uint8_t KnownMask = 0x3;

    struct WideEntry
    {
        Key key{};
        bool valid = false;
        std::uint8_t known = 0;
        std::uint8_t wins = 0;
        std::uint8_t witnesses = 0;
    };

    bool find_wide(const Key& key, int color, Result& result,
                   Result* other_result, bool* other_witness) const
    {
        const std::size_t home = key_hash(key) & mask;
        for (std::size_t offset = 0; offset < ProbeCount; ++offset)
        {
            const WideEntry& entry = wide_entries[(home + offset) & mask];
            if (entry.valid && entry.key == key)
            {
                if (other_result || other_witness)
                {
                    const std::uint8_t other_bit =
                        std::uint8_t(1) << (color ^ 1);
                    if (other_result && (entry.known & other_bit))
                        *other_result = entry.wins & other_bit
                            ? Result::Win : Result::Loss;
                    if (other_witness)
                        *other_witness = entry.witnesses & other_bit;
                }
                const std::uint8_t bit = std::uint8_t(1) << color;
                if (!(entry.known & bit))
                    return false;
                result = entry.wins & bit ? Result::Win : Result::Loss;
                return true;
            }
        }
        return false;
    }

    void store_wide(const Key& key, int color, Result result, bool witness)
    {
        const std::size_t home = key_hash(key) & mask;
        std::size_t target = home;
        for (std::size_t offset = 0; offset < ProbeCount; ++offset)
        {
            const std::size_t index = (home + offset) & mask;
            WideEntry& entry = wide_entries[index];
            if (!entry.valid || entry.key == key)
            {
                target = index;
                break;
            }
        }
        WideEntry& entry = wide_entries[target];
        if (!entry.valid || !(entry.key == key))
        {
            entry.key = key;
            entry.known = 0;
            entry.wins = 0;
            entry.witnesses = 0;
            entry.valid = true;
        }
        const std::uint8_t bit = std::uint8_t(1) << color;
        entry.known |= bit;
        if (result == Result::Win)
            entry.wins |= bit;
        else
        {
            entry.wins &= ~bit;
            entry.witnesses &= ~bit;
        }
        if (witness)
            entry.witnesses |= bit;
    }

    bool compact;
    std::vector<std::uint64_t> compact_entries;
    std::vector<WideEntry> wide_entries;
    std::size_t mask = 0;
};

class WinningSetTable
{
public:
    WinningSetTable(int cells, std::size_t megabytes)
    {
        if (cells > 30 || megabytes == 0)
            return;
        constexpr std::size_t Scale = 1024ULL * 1024ULL;
        const std::size_t requested = megabytes * Scale / sizeof(Entry);
        std::size_t count = 1;
        while (count < requested && count < (std::size_t(1) << 34))
            count <<= 1;
        if (count > requested && count > 1)
            count >>= 1;
        entries.resize(std::max<std::size_t>(count, 1024));
        mask = entries.size() - 1;
    }

    bool find(std::uint64_t code, int color, std::uint64_t& cells) const
    {
        if (entries.empty())
            return false;
        const std::uint64_t tag = ((code << 1) | color) + 1;
        const std::size_t home = mix64(tag) & mask;
        for (std::size_t offset = 0; offset < ProbeCount; ++offset)
        {
            const Entry& entry = entries[(home + offset) & mask];
            if (entry.tag == tag)
            {
                cells = entry.cells;
                return true;
            }
            if (!entry.tag)
                return false;
        }
        return false;
    }

    void store(std::uint64_t code, int color, std::uint64_t cells)
    {
        if (entries.empty() || !cells)
            return;
        const std::uint64_t tag = ((code << 1) | color) + 1;
        const std::size_t home = mix64(tag) & mask;
        std::size_t target = home;
        for (std::size_t offset = 0; offset < ProbeCount; ++offset)
        {
            const std::size_t index = (home + offset) & mask;
            if (!entries[index].tag || entries[index].tag == tag)
            {
                target = index;
                break;
            }
        }
        entries[target] = {tag, static_cast<std::uint32_t>(cells)};
    }

    std::size_t bytes() const { return entries.size() * sizeof(Entry); }

private:
    static constexpr std::size_t ProbeCount = 4;
    struct Entry
    {
        std::uint64_t tag = 0;
        std::uint32_t cells = 0;
    };
    std::vector<Entry> entries;
    std::size_t mask = 0;
};

class MonotoneTable
{
public:
    MonotoneTable(int cells, std::size_t megabytes)
        : compact(cells <= 30), cell_count(cells)
    {
        constexpr std::size_t Scale = 1024ULL * 1024ULL;
        if (megabytes > std::numeric_limits<std::size_t>::max() / Scale)
            throw std::invalid_argument("monotone table is too large");
        const std::size_t bytes = megabytes * Scale;
        if (compact)
        {
            std::size_t bucket_count = 1024;
            const std::size_t bucket_budget = bytes / 4;
            while (bucket_count
                   <= bucket_budget / (2 * sizeof(std::uint32_t)))
                bucket_count <<= 1;
            heads.assign(bucket_count, None);
            bucket_mask = bucket_count - 1;
            const std::size_t record_bytes =
                bytes > bucket_count * sizeof(std::uint32_t)
                ? bytes - bucket_count * sizeof(std::uint32_t) : 0;
            record_capacity = std::min<std::size_t>(
                std::max<std::size_t>(record_bytes / sizeof(Record), 1024),
                std::numeric_limits<std::uint32_t>::max());
            records.reserve(record_capacity);
            board_mask = (std::uint64_t(1) << cell_count) - 1;
            return;
        }

        const std::size_t requested = bytes / sizeof(WideEntry);
        std::size_t count = 1;
        while (count < requested && count < (std::size_t(1) << 34))
            count <<= 1;
        if (count > requested && count > 1)
            count >>= 1;
        wide_entries.resize(std::max<std::size_t>(count, 1024));
        bucket_mask = wide_entries.size() - 1;
    }

    bool find(const Key& key, int color, Result& result) const
    {
        if (!compact)
            return find_wide(key, color, result);
        const std::uint64_t occupied = key.black | key.white;
        const std::uint64_t query_own = color == 0 ? key.black : key.white;
        std::uint32_t index = heads[bucket(occupied, color)];
        while (index != None)
        {
            const Record& record = records[index];
            const std::uint64_t known_occupied =
                record.data & board_mask;
            const int known_color = (record.data >> (2 * cell_count)) & 1;
            if (known_occupied == occupied && known_color == color)
            {
                const std::uint64_t known_own =
                    (record.data >> cell_count) & board_mask;
                const bool win =
                    (record.data >> (2 * cell_count + 1)) & 1;
                if (win && (query_own & ~known_own) == 0)
                {
                    result = Result::Win;
                    return true;
                }
                if (!win && (known_own & ~query_own) == 0)
                {
                    result = Result::Loss;
                    return true;
                }
            }
            index = record.next;
        }
        return false;
    }

    bool find_witness(const Key& key, int color,
                      std::uint64_t& witness) const
    {
        if (!compact)
            return false;
        const std::uint64_t occupied = key.black | key.white;
        const std::uint64_t own = color == 0 ? key.black : key.white;
        std::uint32_t index = heads[bucket(occupied, color)];
        while (index != None)
        {
            const Record& record = records[index];
            const std::uint64_t known_occupied = record.data & board_mask;
            const std::uint64_t known_own =
                (record.data >> cell_count) & board_mask;
            const int known_color =
                (record.data >> (2 * cell_count)) & 1;
            const bool known_win =
                (record.data >> (2 * cell_count + 1)) & 1;
            if (known_occupied == occupied && known_color == color
                && known_win && record.witness
                && known_own == own)
            {
                witness = record.witness;
                return true;
            }
            index = record.next;
        }
        return false;
    }

    void store(const Key& key, int color, Result result,
               std::uint64_t witness = 0)
    {
        if (!compact)
        {
            store_wide(key, color, result);
            return;
        }
        const std::uint64_t occupied = key.black | key.white;
        const std::uint64_t own = color == 0 ? key.black : key.white;
        const bool win = result == Result::Win;
        const std::size_t home = bucket(occupied, color);
        std::uint32_t current = heads[home];
        std::uint32_t previous = None;
        while (current != None)
        {
            Record& record = records[current];
            const std::uint32_t next = record.next;
            const std::uint64_t known_occupied = record.data & board_mask;
            const int known_color = (record.data >> (2 * cell_count)) & 1;
            const bool known_win =
                (record.data >> (2 * cell_count + 1)) & 1;
            if (known_occupied == occupied && known_color == color
                && known_win == win)
            {
                const std::uint64_t known_own =
                    (record.data >> cell_count) & board_mask;
                const bool known_dominates = win
                    ? (own & ~known_own) == 0
                    : (known_own & ~own) == 0;
                if (known_dominates)
                {
                    if (win && witness && known_own == own)
                        record.witness = static_cast<std::uint32_t>(witness);
                    return;
                }
                const bool new_dominates = win
                    ? (known_own & ~own) == 0
                    : (own & ~known_own) == 0;
                if (new_dominates)
                {
                    if (previous == None)
                        heads[home] = next;
                    else
                        records[previous].next = next;
                    record.next = free_head;
                    free_head = current;
                    current = next;
                    continue;
                }
            }
            previous = current;
            current = next;
        }

        const std::uint64_t data = occupied | (own << cell_count)
            | (std::uint64_t(color) << (2 * cell_count))
            | (std::uint64_t(win) << (2 * cell_count + 1));
        std::uint32_t index;
        if (records.size() < record_capacity)
        {
            index = static_cast<std::uint32_t>(records.size());
            records.push_back({data, heads[home],
                               static_cast<std::uint32_t>(witness)});
        }
        else if (free_head != None)
        {
            index = free_head;
            free_head = records[index].next;
            records[index] = {data, heads[home],
                              static_cast<std::uint32_t>(witness)};
        }
        else
            return;
        heads[home] = index;
    }

    std::size_t bytes() const
    {
        return compact
            ? heads.size() * sizeof(std::uint32_t)
                + records.capacity() * sizeof(Record)
            : wide_entries.size() * sizeof(WideEntry);
    }

private:
    static constexpr std::size_t ProbeCount = 16;
    static constexpr std::uint32_t None = 0xffffffffU;

    struct Record
    {
        std::uint64_t data;
        std::uint32_t next;
        std::uint32_t witness;
    };

    struct WideEntry
    {
        Key key{};
        bool valid = false;
        std::uint8_t known = 0;
        std::uint8_t wins = 0;
    };

    std::size_t bucket(std::uint64_t occupied, int color) const
    {
        return mix64(occupied
                     ^ (std::uint64_t(color) * 0x9e3779b97f4a7c15ULL))
            & bucket_mask;
    }

    bool find_wide(const Key& key, int color, Result& result) const
    {
        const std::uint64_t occupied = key.black | key.white;
        const std::size_t home = bucket(occupied, color);
        for (std::size_t offset = 0; offset < ProbeCount; ++offset)
        {
            const WideEntry& entry =
                wide_entries[(home + offset) & bucket_mask];
            if (!entry.valid
                || (entry.key.black | entry.key.white) != occupied)
                continue;
            const std::uint8_t bit = std::uint8_t(1) << color;
            if (!(entry.known & bit))
                continue;
            const std::uint64_t query_own = color == 0 ? key.black : key.white;
            const std::uint64_t known_own =
                color == 0 ? entry.key.black : entry.key.white;
            if ((entry.wins & bit) && (query_own & ~known_own) == 0)
            {
                result = Result::Win;
                return true;
            }
            if (!(entry.wins & bit) && (known_own & ~query_own) == 0)
            {
                result = Result::Loss;
                return true;
            }
        }
        return false;
    }

    void store_wide(const Key& key, int color, Result result)
    {
        const std::uint64_t occupied = key.black | key.white;
        const std::size_t home = bucket(occupied, color);
        std::size_t target = home;
        for (std::size_t offset = 0; offset < ProbeCount; ++offset)
        {
            const std::size_t index = (home + offset) & bucket_mask;
            WideEntry& entry = wide_entries[index];
            if (!entry.valid || entry.key == key)
            {
                target = index;
                break;
            }
        }
        WideEntry& entry = wide_entries[target];
        if (!entry.valid || !(entry.key == key))
        {
            entry.key = key;
            entry.known = 0;
            entry.wins = 0;
            entry.valid = true;
        }
        const std::uint8_t bit = std::uint8_t(1) << color;
        entry.known |= bit;
        if (result == Result::Win)
            entry.wins |= bit;
        else
            entry.wins &= ~bit;
    }

    bool compact;
    int cell_count;
    std::uint64_t board_mask = 0;
    std::vector<std::uint32_t> heads;
    std::vector<Record> records;
    std::uint32_t free_head = None;
    std::size_t record_capacity = 0;
    std::vector<WideEntry> wide_entries;
    std::size_t bucket_mask = 0;
};

class Board
{
public:
    explicit Board(int size)
        : n(size), cells(size >= 1 && size <= 8 ? size * size : 0)
    {
        if (n < 1 || n > 8)
            throw std::invalid_argument("board size must be in 1..8");
        board_mask = cells == 64 ? ~std::uint64_t(0)
                                 : (std::uint64_t(1) << cells) - 1;
        for (int row = 0; row < n; ++row)
            for (int col = 0; col < n; ++col)
            {
                const int point = index(col, row);
                std::uint64_t adjacent = 0;
                constexpr int dc[] = {1, -1, 0, 0, 1, -1};
                constexpr int dr[] = {0, 0, 1, -1, -1, 1};
                for (int direction = 0; direction < 6; ++direction)
                {
                    const int next_col = col + dc[direction];
                    const int next_row = row + dr[direction];
                    if (inside(next_col, next_row))
                        adjacent |= bit(index(next_col, next_row));
                }
                neighbors[point] = adjacent;
                transform[0][point] = point;
                transform[1][point] = index(n - 1 - col, n - 1 - row);
                transform[2][point] = index(row, col);
                transform[3][point] = index(n - 1 - row, n - 1 - col);
            }
        std::array<std::uint64_t, 64> powers{};
        powers[0] = 1;
        for (int point = 1; point < cells; ++point)
            powers[point] = powers[point - 1] * 3;
        for (int symmetry = 0; symmetry < 4; ++symmetry)
            for (int point = 0; point < cells; ++point)
                transformed_power[symmetry][point] =
                    powers[transform[symmetry][point]];
        for (int value = 0; value < n; ++value)
        {
            north |= bit(index(value, 0));
            south |= bit(index(value, n - 1));
            west |= bit(index(0, value));
            east |= bit(index(n - 1, value));
        }
    }

    int index(int col, int row) const { return row * n + col; }
    bool inside(int col, int row) const
    {
        return col >= 0 && col < n && row >= 0 && row < n;
    }
    static std::uint64_t bit(int point) { return std::uint64_t(1) << point; }

    bool connected(std::uint64_t stones, int color) const
    {
        const std::uint64_t first = color == 0 ? north : west;
        const std::uint64_t second = color == 0 ? south : east;
        std::uint64_t frontier = stones & first;
        std::uint64_t seen = frontier;
        while (frontier)
        {
            if (frontier & second)
                return true;
            frontier = adjacent(frontier) & stones & ~seen;
            seen |= frontier;
        }
        return false;
    }

    std::uint64_t adjacent(std::uint64_t stones) const
    {
        return (((stones & ~east) << 1)
                | ((stones & ~west) >> 1)
                | (stones << n)
                | (stones >> n)
                | ((stones & ~(north | east)) >> (n - 1))
                | ((stones & ~(south | west)) << (n - 1)))
            & board_mask;
    }

    std::uint64_t connecting_moves(std::uint64_t stones, int color) const
    {
        const std::uint64_t first = color == 0 ? north : west;
        const std::uint64_t second = color == 0 ? south : east;
        auto closure = [&](std::uint64_t frontier) {
            std::uint64_t seen = frontier;
            while (frontier)
            {
                frontier = adjacent(frontier) & stones & ~seen;
                seen |= frontier;
            }
            return seen;
        };
        const std::uint64_t from_first = closure(stones & first);
        const std::uint64_t from_second = closure(stones & second);
        const std::uint64_t touches_first = first | adjacent(from_first);
        const std::uint64_t touches_second = second | adjacent(from_second);
        return touches_first & touches_second & ~stones;
    }

    std::uint64_t terminal_trap(std::uint64_t own,
                                std::uint64_t other, int color) const
    {
        // Leave the opponent one empty cell that completes its connection.
        // Taking every other empty cell is safe and leaves no legal reply.
        const std::uint64_t empty = board_mask & ~(own | other);
        if (std::popcount(empty) < 2)
            return 0;
        std::uint64_t pivots =
            connecting_moves(other, color ^ 1) & empty;
        while (pivots)
        {
            const std::uint64_t pivot = pivots & -pivots;
            pivots &= pivots - 1;
            const std::uint64_t response = empty & ~pivot;
            if (!connected(own | response, color))
                return response;
        }
        return 0;
    }

    std::uint64_t disjoint_pair_reserve(std::uint64_t stones,
                                        std::uint64_t blocked,
                                        int color) const
    {
        const std::uint64_t empty = board_mask & ~(stones | blocked);
        if (std::popcount(empty) < 4)
            return 0;
        const std::uint64_t pivots = connecting_moves(stones, color) & empty;
        std::array<std::uint64_t, 36> graph{};
        std::uint64_t first_work = empty;
        while (first_work)
        {
            const std::uint64_t first = first_work & -first_work;
            first_work &= first_work - 1;
            const int first_point = std::countr_zero(first);
            std::uint64_t seconds = pivots & first
                ? empty & ~first
                : connecting_moves(stones | first, color) & empty & ~first;
            seconds &= ~((first << 1) - 1);
            graph[first_point] |= seconds;
            while (seconds)
            {
                const std::uint64_t second = seconds & -seconds;
                seconds &= seconds - 1;
                graph[std::countr_zero(second)] |= first;
            }
        }
        first_work = empty;
        while (first_work)
        {
            const std::uint64_t first = first_work & -first_work;
            first_work &= first_work - 1;
            std::uint64_t seconds =
                graph[std::countr_zero(first)] & first_work;
            while (seconds)
            {
                const std::uint64_t second = seconds & -seconds;
                seconds &= seconds - 1;
                const std::uint64_t remaining = empty & ~(first | second);
                std::uint64_t third_work = remaining;
                while (third_work)
                {
                    const std::uint64_t third = third_work & -third_work;
                    third_work &= third_work - 1;
                    const std::uint64_t fourth =
                        graph[std::countr_zero(third)] & remaining;
                    if (fourth)
                        return first | second | third | (fourth & -fourth);
                }
            }
        }
        return 0;
    }

    std::uint64_t disjoint_pair_trap(std::uint64_t own,
                                     std::uint64_t other, int color) const
    {
        const std::uint64_t empty = board_mask & ~(own | other);
        if (std::popcount(empty) < 5)
            return 0;
        const std::uint64_t reserve =
            disjoint_pair_reserve(other, own, color ^ 1);
        if (!reserve)
            return 0;
        const std::uint64_t response = empty & ~reserve;
        return response && !connected(own | response, color)
            ? response : 0;
    }

    std::uint64_t simplicial_cells(std::uint64_t own,
                                   std::uint64_t other, int color) const
    {
        if (cells > 36)
            return 0;
        const std::array<std::uint64_t, 38> graph =
            connection_graph(own, other, color);
        const std::uint64_t empty = board_mask & ~(own | other);
        std::uint64_t simplicial = 0;
        std::uint64_t work = empty;
        while (work)
        {
            const int point = std::countr_zero(work);
            work &= work - 1;
            bool clique = true;
            const std::uint64_t boundary = graph[point];
            std::uint64_t boundary_work = boundary;
            while (boundary_work && clique)
            {
                const int vertex = std::countr_zero(boundary_work);
                boundary_work &= boundary_work - 1;
                clique = ((boundary & ~bit(vertex)) & ~graph[vertex]) == 0;
            }
            if (clique)
                simplicial |= bit(point);
        }
        return simplicial;
    }

    std::uint64_t transformed(std::uint64_t stones, int symmetry) const
    {
        std::uint64_t output = 0;
        while (stones)
        {
            const int point = std::countr_zero(stones);
            stones &= stones - 1;
            output |= bit(transform[symmetry][point]);
        }
        return output;
    }

    struct Position
    {
        std::uint64_t black = 0;
        std::uint64_t white = 0;
        std::array<std::uint64_t, 4> black_symmetry{};
        std::array<std::uint64_t, 4> white_symmetry{};
        std::array<std::uint64_t, 4> code{};
        std::array<std::uint64_t, 4> occupied_code{};
    };

    Position position(std::uint64_t black, std::uint64_t white) const
    {
        Position result;
        result.black = black;
        result.white = white;
        std::uint64_t work = black;
        while (work)
        {
            const int point = std::countr_zero(work);
            work &= work - 1;
            for (int symmetry = 0; symmetry < 4; ++symmetry)
            {
                const std::uint64_t value =
                    transformed_power[symmetry][point];
                result.black_symmetry[symmetry] |=
                    bit(transform[symmetry][point]);
                result.code[symmetry] += value;
                result.occupied_code[symmetry] += value;
            }
        }
        work = white;
        while (work)
        {
            const int point = std::countr_zero(work);
            work &= work - 1;
            for (int symmetry = 0; symmetry < 4; ++symmetry)
            {
                const std::uint64_t value =
                    transformed_power[symmetry][point];
                result.white_symmetry[symmetry] |=
                    bit(transform[symmetry][point]);
                result.code[symmetry] += 2 * value;
                result.occupied_code[symmetry] += value;
            }
        }
        return result;
    }

    void place(Position& position, int point, int color) const
    {
        (color == 0 ? position.black : position.white) |= bit(point);
        for (int symmetry = 0; symmetry < 4; ++symmetry)
        {
            const std::uint64_t value = transformed_power[symmetry][point];
            (color == 0 ? position.black_symmetry[symmetry]
                        : position.white_symmetry[symmetry])
                |= bit(transform[symmetry][point]);
            position.code[symmetry] += (color == 0 ? value : 2 * value);
            position.occupied_code[symmetry] += value;
        }
    }

    void unplace(Position& position, int point, int color) const
    {
        (color == 0 ? position.black : position.white) &= ~bit(point);
        for (int symmetry = 0; symmetry < 4; ++symmetry)
        {
            const std::uint64_t value = transformed_power[symmetry][point];
            (color == 0 ? position.black_symmetry[symmetry]
                        : position.white_symmetry[symmetry])
                &= ~bit(transform[symmetry][point]);
            position.code[symmetry] -= (color == 0 ? value : 2 * value);
            position.occupied_code[symmetry] -= value;
        }
    }

    struct Canonical
    {
        Key key;
        int color;
        std::uint64_t code;
        int symmetry;
    };

    Canonical canonical(const Position& position, int color,
                        bool use_symmetry, bool need_key) const
    {
        Canonical best{{position.black, position.white}, color,
                       position.code[0], 0};
        if (!use_symmetry)
            return best;
        if (cells <= 36)
        {
            int best_symmetry = 0;
            for (int symmetry = 1; symmetry < 4; ++symmetry)
            {
                const bool swaps = symmetry >= 2;
                const std::uint64_t next_code = swaps
                    ? 3 * position.occupied_code[symmetry]
                        - position.code[symmetry]
                    : position.code[symmetry];
                const int next_color = swaps ? color ^ 1 : color;
                if (std::tie(next_code, next_color)
                    < std::tie(best.code, best.color))
                {
                    best.code = next_code;
                    best.color = next_color;
                    best_symmetry = symmetry;
                    best.symmetry = symmetry;
                }
            }
            if (need_key && best_symmetry != 0)
            {
                best.key.black = position.black_symmetry[best_symmetry];
                best.key.white = position.white_symmetry[best_symmetry];
                if (best_symmetry >= 2)
                    std::swap(best.key.black, best.key.white);
            }
            return best;
        }
        for (int symmetry = 1; symmetry < 4; ++symmetry)
        {
            std::uint64_t next_black = position.black_symmetry[symmetry];
            std::uint64_t next_white = position.white_symmetry[symmetry];
            const bool swaps = symmetry >= 2;
            if (swaps)
                std::swap(next_black, next_white);
            const int next_color = swaps ? color ^ 1 : color;
            const Key candidate{next_black, next_white};
            if (std::tie(candidate.black, candidate.white, next_color)
                < std::tie(best.key.black, best.key.white, best.color))
                best = {candidate, next_color, 0, symmetry};
        }
        return best;
    }

    std::string cell_name(int point) const
    {
        return std::string(1, static_cast<char>('a' + point % n))
            + std::to_string(point / n + 1);
    }

    int parse_cell(std::string_view name) const
    {
        if (name.size() < 2 || name[0] < 'a' || name[0] >= 'a' + n)
            throw std::invalid_argument("invalid cell: " + std::string(name));
        int row = 0;
        for (std::size_t i = 1; i < name.size(); ++i)
        {
            if (name[i] < '0' || name[i] > '9')
                throw std::invalid_argument("invalid cell: " + std::string(name));
            const int digit = name[i] - '0';
            if (row > (std::numeric_limits<int>::max() - digit) / 10)
                throw std::invalid_argument("invalid cell: " + std::string(name));
            row = row * 10 + digit;
        }
        if (row < 1 || row > n)
            throw std::invalid_argument("invalid cell: " + std::string(name));
        return index(name[0] - 'a', row - 1);
    }

    int n;
    int cells;
    std::uint64_t board_mask = 0;
    std::array<std::uint64_t, 64> neighbors{};
    std::uint64_t north = 0;
    std::uint64_t south = 0;
    std::uint64_t west = 0;
    std::uint64_t east = 0;
    std::array<std::array<std::uint8_t, 64>, 4> transform{};
    std::array<std::array<std::uint64_t, 64>, 4> transformed_power{};

private:
    std::array<std::uint64_t, 38> connection_graph(
        std::uint64_t own, std::uint64_t other, int color) const
    {
        std::array<std::uint64_t, 38> graph{};
        const std::uint64_t empty = board_mask & ~(own | other);
        std::uint64_t work = empty;
        while (work)
        {
            const int point = std::countr_zero(work);
            work &= work - 1;
            graph[point] = neighbors[point] & empty;
            const std::uint64_t point_bit = bit(point);
            if (color == 0)
            {
                if (point_bit & north)
                {
                    graph[point] |= bit(cells);
                    graph[cells] |= point_bit;
                }
                if (point_bit & south)
                {
                    graph[point] |= bit(cells + 1);
                    graph[cells + 1] |= point_bit;
                }
            }
            else
            {
                if (point_bit & west)
                {
                    graph[point] |= bit(cells);
                    graph[cells] |= point_bit;
                }
                if (point_bit & east)
                {
                    graph[point] |= bit(cells + 1);
                    graph[cells + 1] |= point_bit;
                }
            }
        }

        std::uint64_t remaining = own;
        while (remaining)
        {
            const std::uint64_t seed = bit(std::countr_zero(remaining));
            std::uint64_t component = 0;
            std::uint64_t frontier = seed;
            while (frontier)
            {
                component |= frontier;
                remaining &= ~frontier;
                frontier = adjacent(frontier) & remaining;
            }

            std::uint64_t boundary = adjacent(component) & empty;
            if (color == 0 ? component & north : component & west)
                boundary |= bit(cells);
            if (color == 0 ? component & south : component & east)
                boundary |= bit(cells + 1);
            std::uint64_t boundary_work = boundary;
            while (boundary_work)
            {
                const int first = std::countr_zero(boundary_work);
                boundary_work &= boundary_work - 1;
                graph[first] |= boundary & ~bit(first);
            }
        }
        return graph;
    }
};

struct SearchStats
{
    std::uint64_t boards = 0;
    std::uint64_t tt_hits = 0;
    std::uint64_t monotone_hits = 0;
    std::uint64_t cross_turn_queries = 0;
    std::uint64_t cross_turn_cutoffs = 0;
    std::uint64_t cross_turn_witness_hits = 0;
    std::uint64_t cross_turn_witness_misses = 0;
    std::uint64_t cell_trials = 0;
    std::uint64_t self_connections = 0;
    std::uint64_t terminal_traps = 0;
    std::uint64_t disjoint_pair_traps = 0;
    std::uint64_t dead_calls = 0;
    std::uint64_t dead_cutoffs = 0;
    std::uint64_t dead_stones = 0;
    std::uint64_t root_sets = 0;
};

std::vector<std::uint64_t> symmetric_root_candidates(const Board& board)
{
    std::vector<std::uint64_t> orbits;
    std::uint64_t remaining = board.board_mask;
    while (remaining)
    {
        const std::uint64_t seed = remaining & -remaining;
        std::uint64_t orbit = 0;
        for (int symmetry = 0; symmetry < 4; ++symmetry)
            orbit |= board.transformed(seed, symmetry);
        orbits.push_back(orbit);
        remaining &= ~orbit;
    }
    if (orbits.size() >= 63)
        throw std::logic_error("too many empty-board symmetry orbits");

    std::vector<std::uint64_t> candidates;
    const std::uint64_t count = std::uint64_t(1) << orbits.size();
    candidates.reserve(count - 1);
    for (std::uint64_t choice = 1; choice < count; ++choice)
    {
        std::uint64_t cells = 0;
        for (std::size_t index = 0; index < orbits.size(); ++index)
            if (choice & (std::uint64_t(1) << index))
                cells |= orbits[index];
        if (!board.connected(cells, 0) && !board.connected(cells, 1))
            candidates.push_back(cells);
    }
    std::stable_sort(candidates.begin(), candidates.end(),
                     [](std::uint64_t left, std::uint64_t right) {
                         return std::popcount(left) > std::popcount(right);
                     });
    return candidates;
}

std::size_t winning_set_megabytes(int cells, std::size_t total, bool enabled)
{
    const std::size_t monotone_share = total / 2;
    if (!enabled || cells > 30 || monotone_share <= 1)
        return 0;
    return std::min(monotone_share - 1,
                    std::max<std::size_t>(total / 32, 1));
}

struct SolverConfig
{
    int size;
    std::size_t tt_megabytes = 256;
    bool symmetry = true;
    bool cross_turn = false;
    bool alternate_order = false;
};

class Solver
{
public:
    explicit Solver(const SolverConfig& config, double seconds = 0,
                    std::uint64_t board_limit = 0)
        : board(config.size),
          tt(config.size * config.size, config.tt_megabytes / 2),
          monotone(config.size * config.size,
                   std::max<std::size_t>(
                       config.tt_megabytes / 2
                           - winning_set_megabytes(
                               config.size * config.size,
                               config.tt_megabytes, config.cross_turn),
                       1)),
          witnesses(config.size * config.size,
                    winning_set_megabytes(
                        config.size * config.size, config.tt_megabytes,
                        config.cross_turn)),
          use_symmetry(config.symmetry
                       && config.size * config.size <= 30),
          use_cross_turn(config.cross_turn
                         && config.size * config.size <= 30),
          alternate_branch_order(config.alternate_order)
    {
        build_order();
        begin_query(seconds, board_limit);
    }

    void begin_query(double seconds, std::uint64_t board_limit)
    {
        end_first_search = board.n <= 5;
        reset_query(seconds, board_limit);
    }

    void begin_attempt(double seconds, std::uint64_t board_limit,
                       int attempt)
    {
        end_first_search = (board.n <= 5)
            ^ (alternate_branch_order && (attempt & 1));
        reset_query(seconds, board_limit);
    }

private:
    void reset_query(double seconds, std::uint64_t board_limit)
    {
        stats = {};
        max_boards = board_limit;
        aborted = false;
        deadline = {};
        if (seconds > 0)
        {
            const auto now = std::chrono::steady_clock::now();
            const auto span =
                std::chrono::duration_cast<std::chrono::steady_clock::duration>(
                    std::chrono::duration<double>(seconds));
            deadline = span > std::chrono::steady_clock::time_point::max() - now
                ? std::chrono::steady_clock::time_point::max() : now + span;
        }
    }

public:
    Outcome solve_board(std::uint64_t black, std::uint64_t white)
    {
        if (!(black | white))
        {
            const Result result = solve_symmetric_empty();
            return {result, result};
        }
        const Result black_result = solve(black, white, 0);
        if (aborted)
            return {black_result, Result::Unknown};
        return {black_result, solve(black, white, 1)};
    }

    Result solve(std::uint64_t black, std::uint64_t white, int turn)
    {
        if (board.connected(black, 0))
            return turn == 0 ? Result::Loss : Result::Win;
        if (board.connected(white, 1))
            return turn == 1 ? Result::Loss : Result::Win;
        if (!(black | white))
            return solve_symmetric_empty();
        return search(board.position(black, white), turn);
    }

    const Board board;
    SearchStats stats;

    std::size_t tt_bytes() const
    {
        return tt.bytes() + monotone.bytes() + witnesses.bytes();
    }

private:
    struct MoveList
    {
        const int* begin() const { return points.data(); }
        const int* end() const { return points.data() + count; }

        std::array<int, 64> points{};
        int count = 0;
    };

    struct PlacedResult
    {
        Result result;
        std::uint64_t continuation_cells;
        bool ended;
    };

    Result solve_symmetric_empty()
    {
        const Board::Position empty = board.position(0, 0);
        const Board::Canonical root = board.canonical(
            empty, 0, use_symmetry, true);
        Result cached;
        if (tt.find(root.key, root.code, root.color, cached))
        {
            ++stats.tt_hits;
            return cached;
        }

        // In an N-position Theorem 3.1 gives one common winning set. Empty-
        // board symmetries make that unique set a union of complete orbits.
        const std::vector<std::uint64_t> candidates =
            symmetric_root_candidates(board);

        bool unknown = false;
        for (std::uint64_t cells : candidates)
        {
            ++stats.root_sets;
            const Result reply = search(board.position(cells, 0), 1);
            if (reply == Result::Loss)
            {
                store(root, Result::Win, cells);
                return Result::Win;
            }
            if (reply == Result::Unknown)
            {
                unknown = true;
                if (aborted)
                    return Result::Unknown;
            }
        }
        if (unknown)
            return Result::Unknown;
        store(root, Result::Loss, 0);
        return Result::Loss;
    }

    Result search(const Board::Position& input, int color)
    {
        Board::Position position = input;
        return search_inplace(position, color, true, nullptr);
    }

    Result search_inplace(Board::Position& position, int color,
                          bool allow_cross_turn,
                          std::uint64_t* winning_cells)
    {
        if (winning_cells)
            *winning_cells = 0;
        if (aborted)
            return Result::Unknown;

        const Board::Canonical canonical =
            board.canonical(position, color, use_symmetry, true);
        Result cached;
        bool opposite_witness = false;
        const bool found = use_cross_turn
            ? tt.find(canonical.key, canonical.code, canonical.color, cached,
                      nullptr, &opposite_witness)
            : tt.find(canonical.key, canonical.code, canonical.color, cached);
        if (found)
        {
            ++stats.tt_hits;
            return cached;
        }

        if (monotone.find(canonical.key, canonical.color, cached))
        {
            ++stats.monotone_hits;
            return cached;
        }

        if (allow_cross_turn && use_cross_turn
            && opposite_witness)
        {
            Result inferred;
            std::uint64_t inferred_cells = 0;
            if (infer_from_opponent(position, color,
                                    inferred, inferred_cells))
            {
                ++stats.cross_turn_cutoffs;
                if (winning_cells)
                    *winning_cells = inferred_cells;
                store(canonical, inferred, inferred_cells);
                return inferred;
            }
            if (aborted)
                return Result::Unknown;
        }

        if (max_boards && stats.boards >= max_boards)
        {
            aborted = true;
            return Result::Unknown;
        }
        if ((stats.boards & 0x3ff) == 0 && time_expired())
            return Result::Unknown;
        ++stats.boards;

        // A legal set move can be ordered cell by cell. A safe final set has
        // only safe prefixes, so for player p and a first cell x:
        // W_p(B) = W_p(B + p{x}) or not W_(1-p)(B + p{x}).
        // This folds all nonempty subsets into two recursive edges per cell.
        const std::uint64_t own =
            color == 0 ? position.black : position.white;
        const std::uint64_t other =
            color == 0 ? position.white : position.black;
        const std::uint64_t trap =
            board.terminal_trap(own, other, color);
        if (trap)
        {
            ++stats.terminal_traps;
            if (winning_cells)
                *winning_cells = trap;
            store(canonical, Result::Win, trap);
            return Result::Win;
        }
        const std::uint64_t pair_trap =
            board.disjoint_pair_trap(own, other, color);
        if (pair_trap)
        {
            ++stats.disjoint_pair_traps;
            if (winning_cells)
                *winning_cells = pair_trap;
            store(canonical, Result::Win, pair_trap);
            return Result::Win;
        }
        std::uint64_t dead = 0;
        const int empties = board.cells
            - std::popcount(position.black | position.white);
        if (board.cells <= 36 && empties <= 12)
        {
            ++stats.dead_calls;
            dead = board.simplicial_cells(
                position.black, position.white, 0)
                & board.simplicial_cells(position.white, position.black, 1);
        }
        if (dead)
        {
            ++stats.dead_cutoffs;
            stats.dead_stones += std::popcount(dead);
            std::uint64_t work = dead;
            while (work)
            {
                const int point = std::countr_zero(work);
                work &= work - 1;
                board.place(position, point, color);
            }

            std::uint64_t continuation_cells = 0;
            const Result continuation = search_inplace(
                position, color, allow_cross_turn, &continuation_cells);
            Result end = Result::Unknown;
            if (!aborted && continuation != Result::Win)
                end = search_inplace(position, color ^ 1,
                                     allow_cross_turn, nullptr);

            work = dead;
            while (work)
            {
                const int point = std::countr_zero(work);
                work &= work - 1;
                board.unplace(position, point, color);
            }
            if (aborted)
                return Result::Unknown;
            if (continuation == Result::Win || end == Result::Loss)
            {
                const std::uint64_t cells = continuation == Result::Win
                    ? (continuation_cells ? dead | continuation_cells : 0)
                    : dead;
                if (winning_cells)
                    *winning_cells = cells;
                store(canonical, Result::Win, cells);
                return Result::Win;
            }
            if (continuation == Result::Unknown || end == Result::Unknown)
                return Result::Unknown;
            store(canonical, Result::Loss, 0);
            return Result::Loss;
        }

        const std::uint64_t connecting = board.connecting_moves(
            color == 0 ? position.black : position.white, color);
        const MoveList moves =
            ordered_moves(position.black, position.white, color);
        bool unknown = false;
        for (int move : moves)
        {
            ++stats.cell_trials;
            if (connecting & Board::bit(move))
            {
                ++stats.self_connections;
                continue;
            }
            board.place(position, move, color);
            auto evaluate = [&](bool end_first) {
                bool branch_unknown = false;
                auto try_end = [&]() -> PlacedResult {
                    const Result end = search_inplace(
                        position, color ^ 1, allow_cross_turn, nullptr);
                    if (end == Result::Loss)
                        return {Result::Win, 0, true};
                    if (end == Result::Unknown)
                        branch_unknown = true;
                    return {Result::Loss, 0, false};
                };
                auto try_continue = [&]() -> PlacedResult {
                    std::uint64_t cells = 0;
                    const Result continuation = search_inplace(
                        position, color, allow_cross_turn, &cells);
                    if (continuation == Result::Win)
                        return {Result::Win, cells, false};
                    if (continuation == Result::Unknown)
                        branch_unknown = true;
                    return {Result::Loss, 0, false};
                };
                PlacedResult first = end_first ? try_end() : try_continue();
                if (first.result == Result::Win || aborted)
                    return first;
                PlacedResult second = end_first ? try_continue() : try_end();
                if (second.result == Result::Win || aborted)
                    return second;
                return PlacedResult{branch_unknown ? Result::Unknown
                                                   : Result::Loss,
                                    0, false};
            };
            const PlacedResult placed = evaluate(end_first_search);
            board.unplace(position, move, color);
            if (aborted)
                return Result::Unknown;
            if (placed.result == Result::Win)
            {
                const std::uint64_t cells = placed.ended
                    ? Board::bit(move)
                    : placed.continuation_cells
                        ? placed.continuation_cells | Board::bit(move) : 0;
                if (winning_cells)
                    *winning_cells = cells;
                store(canonical, Result::Win, cells);
                return Result::Win;
            }
            if (placed.result == Result::Unknown)
                unknown = true;
        }
        if (unknown)
            return Result::Unknown;
        store(canonical, Result::Loss, 0);
        return Result::Loss;
    }

    bool infer_from_opponent(Board::Position& position, int color,
                             Result& inferred, std::uint64_t& winning_cells)
    {
        ++stats.cross_turn_queries;
        const int opponent = color ^ 1;
        std::uint64_t set_cells = 0;
        if (find_witness(position, opponent, set_cells))
            ++stats.cross_turn_witness_hits;
        else
        {
            ++stats.cross_turn_witness_misses;
            return false;
        }
        const std::uint64_t occupied = position.black | position.white;
        if (!set_cells || (set_cells & occupied))
            return false;

        const std::uint64_t own = color == 0 ? position.black : position.white;
        if (board.connected(own | set_cells, color))
        {
            inferred = Result::Loss;
            winning_cells = 0;
            return true;
        }

        std::uint64_t work = set_cells;
        while (work)
        {
            const int point = std::countr_zero(work);
            work &= work - 1;
            board.place(position, point, color);
        }
        const Result child =
            search_inplace(position, opponent, false, nullptr);
        work = set_cells;
        while (work)
        {
            const int point = std::countr_zero(work);
            work &= work - 1;
            board.unplace(position, point, color);
        }
        if (child == Result::Unknown)
            return false;
        inferred = child == Result::Loss ? Result::Win : Result::Loss;
        winning_cells = inferred == Result::Win ? set_cells : 0;
        return true;
    }

    bool find_witness(const Board::Position& position, int color,
                      std::uint64_t& cells) const
    {
        const Board::Canonical canonical =
            board.canonical(position, color, use_symmetry, true);
        if (find_exact_witness(canonical, cells))
            return true;
        std::uint64_t transformed_cells = 0;
        if (!monotone.find_witness(canonical.key, canonical.color,
                                   transformed_cells))
            return false;
        cells = board.transformed(transformed_cells, canonical.symmetry);
        return true;
    }

    bool find_exact_witness(const Board::Canonical& canonical,
                            std::uint64_t& cells) const
    {
        std::uint64_t transformed_cells = 0;
        if (!witnesses.find(canonical.code, canonical.color,
                            transformed_cells))
            return false;
        cells = board.transformed(transformed_cells, canonical.symmetry);
        return true;
    }

    void store(const Board::Canonical& canonical, Result result,
               std::uint64_t winning_cells)
    {
        const std::uint64_t transformed_cells = winning_cells
            ? board.transformed(winning_cells, canonical.symmetry) : 0;

        tt.store(canonical.key, canonical.code, canonical.color, result,
                 winning_cells != 0);
        witnesses.store(canonical.code, canonical.color,
                        transformed_cells);
        monotone.store(canonical.key, canonical.color, result,
                       transformed_cells);
    }

    bool time_expired()
    {
        if (aborted)
            return true;
        if (deadline != std::chrono::steady_clock::time_point{}
            && std::chrono::steady_clock::now() >= deadline)
            aborted = true;
        return aborted;
    }

    void build_order()
    {
        base_order.resize(board.cells);
        for (int point = 0; point < board.cells; ++point)
            base_order[point] = point;
        std::stable_sort(base_order.begin(), base_order.end(), [&](int a, int b) {
            auto center_distance = [&](int point) {
                const int col = point % board.n;
                const int row = point / board.n;
                return std::abs(2 * col - board.n + 1)
                    + std::abs(2 * row - board.n + 1);
            };
            return center_distance(a) < center_distance(b);
        });
    }

    MoveList ordered_moves(std::uint64_t black, std::uint64_t white,
                           int color) const
    {
        const std::uint64_t occupied = black | white;
        const std::uint64_t own = color == 0 ? black : white;
        const std::uint64_t opponent = color == 0 ? white : black;
        MoveList moves;
        std::array<int, 64> scores{};
        constexpr std::array<std::int8_t, 35> weights = {
            0, 15, -112, 127, 2, -1, 1, 1, -3, -2, -3, -3,
            -4, 4, 2, 4, -3, -1, -1, -2, 0, 1, -3, -8, 8,
            -3, -7, 5, -3, -4, 5, 7, -6, 5, 10};
        constexpr std::array<int, 6> dx = {1, -1, 0, 0, 1, -1};
        constexpr std::array<int, 6> dy = {0, 0, 1, -1, -1, 1};
        auto insert = [&](int point, int score) {
            int index = moves.count;
            while (index > 0 && score > scores[index - 1])
            {
                scores[index] = scores[index - 1];
                moves.points[index] = moves.points[index - 1];
                --index;
            }
            scores[index] = score;
            moves.points[index] = point;
            ++moves.count;
        };
        for (int point : base_order)
        {
            if (occupied & Board::bit(point))
                continue;
            const int own_neighbors = std::popcount(board.neighbors[point] & own);
            const int opponent_neighbors =
                std::popcount(board.neighbors[point] & opponent);
            int score = -4 * opponent_neighbors - own_neighbors;
            if (board.n != 5)
            {
                insert(point, score);
                continue;
            }
            const int physical_x = point % board.n;
            const int physical_y = point / board.n;
            const int x = color == 0 ? physical_x : physical_y;
            const int y = color == 0 ? physical_y : physical_x;
            score = weights[4] * 18 * (x - 2)
                + weights[5] * 18 * (y - 2)
                + weights[6] * 18 * std::abs(x - 2)
                + weights[7] * 18 * std::abs(y - 2)
                + weights[8] * 36 * (x == 0)
                + weights[9] * 36 * (x == 4)
                + weights[10] * 36 * (y == 0)
                + weights[11] * 36 * (y == 4)
                + weights[12] * 6 * own_neighbors
                + weights[13] * 6 * opponent_neighbors
                + weights[14] * own_neighbors * own_neighbors
                + weights[15] * opponent_neighbors * opponent_neighbors
                + weights[16] * own_neighbors * opponent_neighbors;
            for (int direction = 0; direction < 6; ++direction)
            {
                const int physical_dx = color == 0
                    ? dx[direction] : dy[direction];
                const int physical_dy = color == 0
                    ? dy[direction] : dx[direction];
                const int xx = physical_x + physical_dx;
                const int yy = physical_y + physical_dy;
                const int offset = 17 + 3 * direction;
                if (!board.inside(xx, yy))
                    score += weights[offset + 2] * 36;
                else
                {
                    const std::uint64_t cell =
                        Board::bit(board.index(xx, yy));
                    if (cell & own)
                        score += weights[offset] * 36;
                    else if (cell & opponent)
                        score += weights[offset + 1] * 36;
                }
            }
            insert(point, score);
        }
        return moves;
    }

    TranspositionTable tt;
    MonotoneTable monotone;
    WinningSetTable witnesses;
    bool use_symmetry;
    bool use_cross_turn;
    bool alternate_branch_order;
    bool end_first_search = false;
    std::uint64_t max_boards = 0;
    bool aborted = false;
    std::chrono::steady_clock::time_point deadline{};
    std::vector<int> base_order;
};

std::uint64_t parse_u64(const std::string& value, const char* option)
{
    if (value.empty()
        || std::any_of(value.begin(), value.end(), [](unsigned char character) {
               return character < '0' || character > '9';
           }))
        throw std::invalid_argument(std::string("invalid ") + option);
    std::size_t used = 0;
    unsigned long long parsed = 0;
    try
    {
        parsed = std::stoull(value, &used);
    }
    catch (const std::exception&)
    {
        throw std::invalid_argument(std::string("invalid ") + option);
    }
    if (used != value.size())
        throw std::invalid_argument(std::string("invalid ") + option);
    return parsed;
}

std::size_t parse_megabytes(const std::string& value)
{
    const std::uint64_t parsed = parse_u64(value, "--tt-mb");
    constexpr std::size_t Scale = 1024ULL * 1024ULL;
    if (parsed > std::numeric_limits<std::size_t>::max() / Scale)
        throw std::invalid_argument("--tt-mb is too large");
    return static_cast<std::size_t>(parsed);
}

double parse_seconds(const std::string& value)
{
    std::size_t used = 0;
    double parsed = 0;
    try
    {
        parsed = std::stod(value, &used);
    }
    catch (const std::exception&)
    {
        throw std::invalid_argument("invalid --time");
    }
    const double maximum = std::chrono::duration<double>(
        std::chrono::steady_clock::duration::max()).count();
    if (used != value.size() || !std::isfinite(parsed)
        || parsed < 0 || parsed > maximum)
        throw std::invalid_argument("invalid --time");
    return parsed;
}

std::uint64_t parse_cells(const Board& board, const std::string& text)
{
    if (text.empty() || text == "-")
        return 0;
    std::uint64_t stones = 0;
    std::size_t start = 0;
    while (start < text.size())
    {
        const std::size_t end = text.find(',', start);
        const std::string_view cell(
            text.data() + start,
            (end == std::string::npos ? text.size() : end) - start);
        const int point = board.parse_cell(cell);
        const std::uint64_t mask = Board::bit(point);
        if (stones & mask)
            throw std::invalid_argument("duplicate cell: " + std::string(cell));
        stones |= mask;
        if (end == std::string::npos)
            break;
        start = end + 1;
        if (start == text.size())
            throw std::invalid_argument("empty cell after comma");
    }
    return stones;
}

} // namespace

int main(int argc, char** argv)
{
    try
    {
        if (argc < 2)
            throw std::invalid_argument(
                "usage: rexplus_solver N --black CELLS --white CELLS "
                "--to-play black|white");
        const int size = std::stoi(argv[1]);
        std::string black_text = "-", white_text = "-";
        int turn = 0, attempts = 1;
        std::size_t memory = 256;
        double seconds = 0;
        bool list = false;
        for (int i = 2; i < argc; ++i)
        {
            const std::string option = argv[i];
            if (option == "--list-candidates")
            {
                list = true;
                continue;
            }
            if (++i == argc)
                throw std::invalid_argument("missing option value");
            const std::string value = argv[i];
            if (option == "--black")
                black_text = value;
            else if (option == "--white")
                white_text = value;
            else if (option == "--to-play")
            {
                if (value != "black" && value != "white")
                    throw std::invalid_argument("invalid player");
                turn = value == "white";
            }
            else if (option == "--tt-mb")
                memory = parse_megabytes(value);
            else if (option == "--time")
                seconds = parse_seconds(value);
            else if (option == "--attempts")
                attempts = std::stoi(value);
            else
                throw std::invalid_argument("unknown option: " + option);
        }
        Board board(size);
        if (list)
        {
            const auto candidates = symmetric_root_candidates(board);
            std::cout << "candidate_count " << candidates.size() << '\n';
            for (std::size_t i = 0; i < candidates.size(); ++i)
            {
                std::cout << "candidate " << i + 1 << " black";
                for (auto work = candidates[i]; work; work &= work - 1)
                    std::cout << ' ' << board.cell_name(std::countr_zero(work));
                std::cout << '\n';
            }
            return 0;
        }
        const auto black = parse_cells(board, black_text);
        const auto white = parse_cells(board, white_text);
        Solver solver({.size = size, .tt_megabytes = memory,
                       .cross_turn = true, .alternate_order = true});
        Result result = Result::Unknown;
        for (int i = 0; i < attempts && result == Result::Unknown; ++i)
        {
            solver.begin_attempt(seconds, 0, i);
            result = solver.solve(black, white, turn);
        }
        std::cout << "result " << result_name(result) << '\n';
        return result == Result::Unknown ? 1 : 0;
    }
    catch (const std::exception& error)
    {
        std::cerr << "error: " << error.what() << '\n';
        return 2;
    }
}
