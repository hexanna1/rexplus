#!/usr/bin/env python3
"""Generate and independently check the complete 6x6 Rex+ result."""

from __future__ import annotations

import argparse
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
from dataclasses import dataclass
import json
import math
from pathlib import Path
import subprocess
import sys
import tempfile
import time


ROOT = Path(__file__).resolve().parent
BOARD = frozenset(range(36))
PREFIX_CANDIDATE = 2042
HEAVY_CANDIDATES = frozenset((1966, 2021, 2022, 2026, 2044))
# Start the longest independent proof searches first.
HEAVY_JOBS = ((2044, (2044,)), (2026, (2026,)),
              (1966, (1966, 2021)), (2022, (2022,)))


class VerificationError(RuntimeError):
    pass


@dataclass(frozen=True)
class Tail:
    candidate: int
    black: tuple[int, ...]
    white: tuple[int, ...]
    direct: bool


def cells(text: str) -> tuple[int, ...]:
    if text == "-":
        return ()
    words = text.replace(",", " ").split()
    result = []
    for word in words:
        if (len(word) != 2 or word[0] not in "abcdef"
                or word[1] not in "123456"):
            raise VerificationError(f"invalid cell: {word!r}")
        result.append(6 * (int(word[1]) - 1) + ord(word[0]) - ord("a"))
    if not result or len(result) != len(set(result)):
        raise VerificationError(f"empty or repeated cells: {text!r}")
    return tuple(sorted(result))


def names(points: tuple[int, ...]) -> str:
    return ",".join(chr(ord("a") + point % 6) + str(point // 6 + 1)
                    for point in points) or "-"


def connected(points: tuple[int, ...], color: int) -> bool:
    stones = set(points)
    seen = {point for point in stones
            if (point // 6 if color == 0 else point % 6) == 0}
    frontier = list(seen)
    for point in frontier:
        row, column = divmod(point, 6)
        if (row if color == 0 else column) == 5:
            return True
        for dr, dc in ((0, 1), (0, -1), (1, 0),
                       (-1, 0), (1, -1), (-1, 1)):
            rr, cc = row + dr, column + dc
            neighbor = 6 * rr + cc
            if (0 <= rr < 6 and 0 <= cc < 6 and neighbor in stones
                    and neighbor not in seen):
                seen.add(neighbor)
                frontier.append(neighbor)
    return False


def candidates() -> dict[int, tuple[int, ...]]:
    """Enumerate invariant batches independently of the C++ implementation."""
    remaining = set(BOARD)
    orbits = []
    while remaining:
        point = min(remaining)
        row, column = divmod(point, 6)
        orbit = {point, 35 - point, 6 * column + row,
                 6 * (5 - column) + 5 - row}
        orbits.append(orbit)
        remaining -= orbit

    batches = []
    for choice in range(1, 1 << len(orbits)):
        batch = set()
        for index, orbit in enumerate(orbits):
            if choice & (1 << index):
                batch.update(orbit)
        ordered = tuple(sorted(batch))
        if not connected(ordered, 0) and not connected(ordered, 1):
            batches.append(ordered)
    batches.sort(key=len, reverse=True)
    if len(orbits) != 12 or len(batches) != 2047:
        raise VerificationError("independent opening enumeration is incomplete")
    return dict(enumerate(batches, 1))


def run(command: list[str], timeout: float) -> str:
    try:
        completed = subprocess.run(
            command, text=True, encoding="ascii", capture_output=True,
            check=False, timeout=timeout)
    except (OSError, subprocess.TimeoutExpired) as error:
        raise VerificationError(f"failed command: {' '.join(command)}") from error
    if completed.returncode:
        raise VerificationError(
            completed.stderr.strip() or completed.stdout.strip()
            or f"failed command: {' '.join(command)}")
    return completed.stdout


def output_value(output: str, field: str) -> str:
    values = [line.partition(" ")[2] for line in output.splitlines()
              if line.partition(" ")[0] == field]
    if len(values) != 1:
        raise VerificationError(f"missing or repeated process field: {field}")
    return values[0]


def compare_candidates(solver: Path, inventory: dict[int, tuple[int, ...]]) -> None:
    lines = run([str(solver), "6", "--list-candidates"], 30).splitlines()
    if not lines or lines[0] != "candidate_count 2047":
        raise VerificationError("native candidate count disagrees")
    native = {}
    for line in lines[1:]:
        words = line.split()
        if len(words) < 4 or words[0] != "candidate" or words[2] != "black":
            raise VerificationError("invalid native candidate listing")
        number = int(words[1])
        if number in native:
            raise VerificationError("repeated native candidate")
        native[number] = cells(" ".join(words[3:]))
    if native != inventory:
        raise VerificationError("native candidate IDs disagree with coordinates")


def read_hints(path: Path, inventory: dict[int, tuple[int, ...]],
               direct: bool, count: int) -> dict[int, Tail]:
    result = {}
    for line in path.read_text(encoding="ascii").splitlines():
        if not line or line.startswith("#"):
            continue
        words = line.split()
        if len(words) != 2:
            raise VerificationError(f"invalid move hint in {path.name}")
        number = int(words[0])
        if number not in inventory or number in result:
            raise VerificationError(f"invalid or repeated candidate {number}")
        black = inventory[number]
        white = cells(words[1])
        if (not white or set(black) & set(white) or connected(black, 0)
                or connected(white, 1) or 36 - len(black) - len(white) > 32):
            raise VerificationError(f"illegal physical tail for candidate {number}")
        result[number] = Tail(number, black, white, direct)
    if len(result) != count:
        raise VerificationError(f"incomplete move hints in {path.name}")
    return result


def read_prefix(path: Path, inventory: dict[int, tuple[int, ...]]) -> tuple[int, ...]:
    lines = path.read_text(encoding="ascii").splitlines()
    if len(lines) != 4 or lines[3] != "end":
        raise VerificationError("invalid prefix certificate")
    position = lines[0].split()
    if (len(position) != 6 or position[:2] != ["position", "6"]
            or cells(position[2]) != inventory[PREFIX_CANDIDATE]
            or cells(position[3]) or position[4:] != ["1", "1"]):
        raise VerificationError("prefix certificate is not bound to candidate 2042")
    words = lines[1].split()
    if len(words) != 2 or words[0] != "prefix":
        raise VerificationError("missing physical White prefix")
    prefix = cells(words[1])
    black = inventory[PREFIX_CANDIDATE]
    if not prefix or set(black) & set(prefix) or connected(prefix, 1):
        raise VerificationError("physical White prefix is illegal")
    mapping = lines[2].split()
    empty = BOARD - set(black) - set(prefix)
    if (len(mapping) != len(empty) + 2 or mapping[0] != "mapping"
            or int(mapping[1]) != len(empty)
            or set(map(int, mapping[2:])) != empty):
        raise VerificationError("prefix mapping does not cover the physical domain")
    return prefix


def binding_rows(path: Path, expected: list[Tail]) -> list[list[str]]:
    lines = path.read_text(encoding="ascii").splitlines()
    if len(lines) != 3 * len(expected):
        raise VerificationError(f"incomplete physical bindings in {path.name}")
    positions = []
    for index, tail in enumerate(expected):
        position = lines[3 * index].split()
        if (len(position) != 6 or position[:2] != ["position", "6"]
                or cells(position[2]) != tail.black
                or cells(position[3]) != tail.white
                or position[4:] != ["1", "0"]):
            raise VerificationError(f"physical binding differs for {tail.candidate}")
        empty = sorted(BOARD - set(tail.black) - set(tail.white))
        variables = lines[3 * index + 1].split()
        root = lines[3 * index + 2].split()
        if (variables != ["variables", str(len(empty))] + list(map(str, empty))
                or root != ["root", "2", str((1 << len(empty)) - 1), "0"]):
            raise VerificationError(f"incorrect root map for {tail.candidate}")
        positions.append(position[1:])
    return positions


def inspect(args: argparse.Namespace) -> tuple[dict[int, Tail], tuple[int, ...]]:
    inventory = candidates()
    compare_candidates(args.build_dir / "rexplus_solver", inventory)
    direct = read_hints(args.certificates / "six-direct.txt", inventory, True, 1926)
    hard = read_hints(args.certificates / "six-hypergraph.txt", inventory, False, 120)
    if (set(direct) & set(hard)
            or set(direct) | set(hard) != set(inventory) - {PREFIX_CANDIDATE}
            or not HEAVY_CANDIDATES <= set(hard)
            or inventory[PREFIX_CANDIDATE] != cells("a1,f6")):
        raise VerificationError("move hints do not cover the opening inventory")
    prefix = read_prefix(args.certificates / "six-prefix.txt", inventory)
    tails = direct | hard
    for candidate, claims in HEAVY_JOBS:
        binding_rows(args.certificates / f"six-bindings-{candidate}.txt",
                     [tails[number] for number in claims])
    return tails, prefix


def check_prefix(args: argparse.Namespace, prefix: tuple[int, ...]) -> dict:
    output = run([str(args.build_dir / "rexplus_prefix_checker"),
                  str(args.certificates / "six-prefix.txt")], 90)
    report = json.loads(output)
    if (report.get("checked") is not True or report.get("size") != 6
            or cells(report.get("black", "-")) != cells("a1,f6")
            or cells(report.get("white", "-")) or report.get("turn") != 1
            or report.get("result") != 1
            or cells(report.get("prefix", "-")) != prefix):
        raise VerificationError("independent prefix check disagreed")
    return report


def native_attempt(tail: Tail, args: argparse.Namespace, pool_mb: int) -> bool:
    if tail.direct:
        command = [str(args.build_dir / "rexplus_solver"), "6",
                   "--black", names(tail.black), "--white", names(tail.white),
                   "--to-play", "black", "--time", str(args.native_seconds),
                   "--tt-mb", str(pool_mb), "--attempts", "1"]
    else:
        command = [str(args.build_dir / "rexplus_hypergraph"), "6",
                   names(tail.black), names(tail.white), "black",
                   "--time", str(args.native_seconds), "--pool-mb", str(pool_mb),
                   "--fold-labels"]
    try:
        completed = subprocess.run(
            command, text=True, encoding="ascii", capture_output=True,
            check=False, timeout=args.native_seconds + 30)
    except subprocess.TimeoutExpired:
        return False
    except OSError as error:
        raise VerificationError(f"cannot run {command[0]}") from error
    result = output_value(completed.stdout, "result")
    if completed.returncode == 1 and result == "unknown":
        return False
    if completed.returncode != 0 or result != "loss":
        raise VerificationError(
            f"candidate {tail.candidate}: exact native loss was not established; "
            f"{completed.stderr.strip() or completed.stdout.strip()}")
    return True


def check_native(tail: Tail, args: argparse.Namespace) -> int:
    initial = (min(args.direct_tt_mb, args.native_pool_mb)
               if tail.direct else args.native_pool_mb)
    if native_attempt(tail, args, initial):
        return tail.candidate
    if initial != args.native_pool_mb and native_attempt(tail, args, args.native_pool_mb):
        return tail.candidate
    raise VerificationError(f"candidate {tail.candidate}: native search is incomplete")


def parallel_results(function, items, workers: int):
    """Keep at most one running operation per worker, including queued work."""
    remaining = iter(items)
    with ThreadPoolExecutor(max_workers=workers) as executor:
        pending = set()
        for _ in range(workers):
            item = next(remaining, None)
            if item is not None:
                pending.add(executor.submit(function, item))
        while pending:
            done, pending = wait(pending, return_when=FIRST_COMPLETED)
            for future in done:
                yield future.result()
                item = next(remaining, None)
                if item is not None:
                    pending.add(executor.submit(function, item))


def check_native_tails(tails: dict[int, Tail], args: argparse.Namespace) -> dict:
    selected = [tail for number, tail in sorted(tails.items())
                if number not in HEAVY_CANDIDATES]
    checked = set()
    for number in parallel_results(lambda tail: check_native(tail, args),
                                   selected, args.jobs):
        checked.add(number)
        if len(checked) % 128 == 0 or len(checked) == len(selected):
            print(f"native tails: {len(checked)}/{len(selected)}", flush=True)
    if checked != {tail.candidate for tail in selected}:
        raise VerificationError("native searches did not cover the selected tails")
    return {"direct_tails": 1926, "hypergraph_tails": 115}


def run_proof_pipeline(generator: list[str], checker: list[str], timeout: float) -> dict:
    """Stream a fresh proof directly to its independent checker."""
    deadline = time.monotonic() + timeout
    producer = consumer = None
    with tempfile.TemporaryFile() as producer_errors:
        try:
            producer = subprocess.Popen(
                generator, stdout=subprocess.PIPE, stderr=producer_errors)
            consumer = subprocess.Popen(
                checker, stdin=producer.stdout, stdout=subprocess.PIPE,
                stderr=subprocess.PIPE, text=True, encoding="ascii")
            producer.stdout.close()
            output, errors = consumer.communicate(timeout=timeout)
            producer.wait(timeout=max(0.001, deadline - time.monotonic()))
        except (OSError, subprocess.TimeoutExpired) as error:
            raise VerificationError("proof generation or checking did not finish") from error
        finally:
            for process in (consumer, producer):
                if process is not None and process.poll() is None:
                    process.kill()
                    process.wait()
        producer_errors.seek(0)
        generator_output = producer_errors.read().decode("ascii", errors="replace")
    if producer.returncode != 0 or consumer.returncode != 0:
        raise VerificationError(
            f"proof generator exited {producer.returncode}, "
            f"checker exited {consumer.returncode}: "
            f"{generator_output.strip()} {errors.strip()}")
    if (output_value(generator_output, "result") != "loss"
            or output_value(output, "verified") != "loss"):
        raise VerificationError("fresh proof did not establish the required loss")
    return {"generator_output": generator_output, "checker_output": output}


def check_heavy(job, tails: dict[int, Tail], args: argparse.Namespace) -> dict:
    """Generate one DAG and bind its checked result to the physical tails."""
    candidate, claims = job
    tail = tails[candidate]
    bindings = args.certificates / f"six-bindings-{candidate}.txt"
    expected = binding_rows(bindings, [tails[number] for number in claims])
    generator = [str(args.build_dir / "rexplus_proof_generator"), "6",
                 names(tail.black), names(tail.white), "black", "-",
                 str(args.proof_seconds), str(args.proof_pool_mb)]
    checker = [str(args.build_dir / "rexplus_proof_checker"), "-",
               "--bind-roots", str(bindings)]
    report = run_proof_pipeline(generator, checker, args.proof_seconds + 90)
    output = report["checker_output"]
    bound = [line.split() for line in output.splitlines()
             if line.startswith("bound_root ")]
    actual = []
    for index, words in enumerate(bound, 1):
        if len(words) != 10 or words[1] != str(index):
            raise VerificationError("invalid checked physical root report")
        actual.append(words[2:7])
    if actual != expected:
        raise VerificationError(f"candidate {candidate}: physical bindings disagree")
    if (int(output_value(output, "additional_physical_roots")) != len(expected)
            or int(output_value(output, "facts")) < 1
            or int(output_value(output, "cofactors")) < 0):
        raise VerificationError("fresh proof checker report is incomplete")
    report.update(candidate=candidate, physical_tails=list(claims),
                  facts=int(output_value(output, "facts")),
                  cofactors=int(output_value(output, "cofactors")))
    print(f"fresh proof {candidate}: checked tails {', '.join(map(str, claims))}",
          flush=True)
    return report


def arguments() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--build-dir", type=Path, default=ROOT / "build")
    parser.add_argument("--certificates", type=Path, default=ROOT / "certificates")
    parser.add_argument("--jobs", type=int, choices=(1, 2), default=2,
                        help="concurrent native searches or proof pipelines (default: 2)")
    parser.add_argument("--native-seconds", type=float, default=15,
                        help="search budget for each native attempt (default: 15)")
    parser.add_argument("--native-pool-mb", type=int, default=512,
                        help="native hypergraph pool and direct retry budget (default: 512)")
    parser.add_argument("--direct-tt-mb", type=int, default=16,
                        help="initial direct-tail table budget (default: 16)")
    parser.add_argument("--proof-seconds", type=float, default=600,
                        help="search budget for each proof generator (default: 600)")
    parser.add_argument("--proof-pool-mb", type=int, default=4096,
                        help="pool budget for each proof generator (default: 4096)")
    parser.add_argument("--inventory-only", action="store_true",
                        help="check candidate and move coverage without recomputing values")
    parser.add_argument("--report", type=Path,
                        help="also save the small final JSON report")
    args = parser.parse_args()
    if (not math.isfinite(args.native_seconds) or args.native_seconds <= 0
            or not math.isfinite(args.proof_seconds) or args.proof_seconds <= 0
            or min(args.native_pool_mb, args.direct_tt_mb, args.proof_pool_mb) < 1):
        parser.error("search budgets must be finite and positive")
    return args


def main() -> int:
    args = arguments()
    tails, prefix = inspect(args)
    print("inventory: 2,047 candidates, 1,926 direct tails, 120 hard tails, "
          "one self-dual prefix", flush=True)
    if args.inventory_only:
        print("Inventory checked; no tail values or proof DAGs were recomputed.")
        return 0

    native = check_native_tails(tails, args)
    prefix_report = check_prefix(args, prefix)
    print("candidate 2042: physical self-dual prefix checked", flush=True)
    proofs = list(parallel_results(lambda job: check_heavy(job, tails, args),
                                  HEAVY_JOBS, args.jobs))
    covered = {number for proof in proofs for number in proof["physical_tails"]}
    if covered != HEAVY_CANDIDATES:
        raise VerificationError("fresh proof pipelines did not cover all heavy tails")
    report = {"result": "P", "candidate_count": 2047,
              "native": native, "prefix": prefix_report,
              "proofs": sorted(proofs, key=lambda proof: proof["candidate"])}
    if args.report:
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(json.dumps(report, indent=2) + "\n", encoding="ascii")
    print(json.dumps(report, indent=2), flush=True)
    print("6x6 Rex+: P; either player loses when moving first.")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (VerificationError, ValueError, OSError) as error:
        print(f"verification failed: {error}", file=sys.stderr)
        raise SystemExit(1)
