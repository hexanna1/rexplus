#!/usr/bin/env python3
"""Reproduce the exact 5x5 classification."""

from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
import re
import subprocess
import sys


ROOT = Path(__file__).resolve().parent
SOLVER = ROOT / "build" / "rexplus_solver"
HYPERGRAPH = ROOT / "build" / "rexplus_hypergraph"
WITNESSES = ROOT / "certificates" / "first-move-witnesses.txt"
HARD_ROOTS = ROOT / "certificates" / "hard-roots.txt"
EQUIVALENCE = ROOT / "audit_hypergraph.py"
CELL = re.compile(r"[a-e][1-5]")


class VerificationError(RuntimeError):
    pass


def records(path: Path) -> tuple[dict[str, str], list[dict[str, str]]]:
    blocks = path.read_text(encoding="ascii").strip().split("\n\n")

    def fields(block: str) -> dict[str, str]:
        result: dict[str, str] = {}
        for line in block.splitlines():
            key, separator, value = line.partition(" ")
            if not separator or key in result:
                raise VerificationError(f"invalid record in {path}")
            result[key] = value
        return result

    return fields(blocks[0]), [fields(block) for block in blocks[1:]]


def cells(text: str) -> tuple[str, ...]:
    if text == "-":
        return ()
    result = tuple(text.replace(",", " ").split())
    if (not result or len(result) != len(set(result))
            or any(CELL.fullmatch(cell) is None for cell in result)):
        raise VerificationError(f"invalid cells: {text!r}")
    return result


def connected(names: tuple[str, ...], color: str) -> bool:
    stones = {(ord(name[0]) - ord("a"), int(name[1]) - 1)
              for name in names}
    if color == "black":
        frontier = {point for point in stones if point[1] == 0}
        target = lambda point: point[1] == 4
    else:
        frontier = {point for point in stones if point[0] == 0}
        target = lambda point: point[0] == 4
    seen = set(frontier)
    while frontier:
        point = frontier.pop()
        if target(point):
            return True
        column, row = point
        for dc, dr in ((-1, 0), (-1, 1), (0, -1),
                       (0, 1), (1, -1), (1, 0)):
            neighbor = column + dc, row + dr
            if neighbor in stones and neighbor not in seen:
                seen.add(neighbor)
                frontier.add(neighbor)
    return False


def run(command: list[str], timeout: float | None = None) -> str:
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


def output_fields(text: str) -> dict[str, str]:
    result: dict[str, str] = {}
    for line in text.splitlines():
        key, separator, value = line.partition(" ")
        if separator:
            result[key] = value
    return result


def query_candidates() -> dict[int, tuple[str, ...]]:
    output = run([str(SOLVER), "5", "--list-candidates"], 30)
    lines = output.splitlines()
    if not lines or lines[0] != "candidate_count 255":
        raise VerificationError("unexpected candidate count")
    result: dict[int, tuple[str, ...]] = {}
    for line in lines[1:]:
        words = line.split()
        if len(words) < 4 or words[0] != "candidate" or words[2] != "black":
            raise VerificationError("invalid candidate listing")
        result[int(words[1])] = cells(" ".join(words[3:]))
    if set(result) != set(range(1, 256)):
        raise VerificationError("candidate listing is incomplete")
    return result


def inspect_artifacts() -> tuple[list[dict[str, str]], list[dict[str, str]]]:
    candidates = query_candidates()
    witness_header, witnesses = records(WITNESSES)
    if witness_header != {"board_size": "5", "exact_white_win_count": "253"}:
        raise VerificationError("invalid witness header")
    expected_witness_fields = {
        "candidate", "black", "white_reply", "to_play", "result"}
    seen: set[int] = set()
    for witness in witnesses:
        if set(witness) != expected_witness_fields:
            raise VerificationError("invalid witness fields")
        candidate = int(witness["candidate"])
        black = cells(witness["black"])
        white = cells(witness["white_reply"])
        if (candidate in seen or candidates.get(candidate) != black
                or set(black) & set(white)
                or connected(black, "black") or connected(white, "white")
                or witness["to_play"] != "black"
                or witness["result"] != "loss"):
            raise VerificationError(f"invalid witness {candidate}")
        seen.add(candidate)
    if seen != set(range(1, 256)) - {251, 255}:
        raise VerificationError("witness coverage is incomplete")

    hard_header, hard_roots = records(HARD_ROOTS)
    if hard_header != {"board_size": "5", "exact_root_count": "2"}:
        raise VerificationError("invalid hard-root header")
    if {int(root["candidate"]) for root in hard_roots} != {251, 255}:
        raise VerificationError("hard-root coverage is incomplete")
    for root in hard_roots:
        candidate = int(root["candidate"])
        black = cells(root["black"])
        batch = cells(root["winning_batch"])
        if (candidates[candidate] != black or set(black) & set(batch)
                or connected(batch, "white") or root["white"] != "-"
                or root["to_play"] != "white" or root["result"] != "win"):
            raise VerificationError(f"invalid hard root {candidate}")
    return witnesses, hard_roots


def inspect_hypergraph_engine() -> None:
    for size in (2, 3, 4):
        for turn in ("black", "white"):
            outcome = output_fields(run([
                str(SOLVER), str(size), "--black", "-", "--white", "-",
                "--to-play", turn, "--tt-mb", "64"], 30))
            if outcome.get("result") != "loss":
                raise VerificationError(f"empty {size}x{size} {turn} is not losing")
    fixtures = (
        (3, "b1,a2", "a1,b2"),
        (4, "b1,c1,b3,b4", "b2,d2,c3,a4"),
        (6, "b1,b2,f2,c3,a4,a5,c5,d5,f5,a6,e6,f6",
         "a1,e1,f1,a2,e2,d3,e3,b4,f4,b5,b6,c6"),
    )
    for size, black, white in fixtures:
        for turn in ("black", "white"):
            quotient = output_fields(run([
                str(HYPERGRAPH), str(size), black, white, turn], 30))
            direct = output_fields(run([
                str(SOLVER), str(size), "--black", black,
                "--white", white, "--to-play", turn,
                "--tt-mb", "16"], 30))
            if quotient.get("result") != direct.get("result"):
                raise VerificationError(
                    f"{size}x{size} {turn} hypergraph result disagreed")


def replay_witness(witness: dict[str, str]) -> int:
    candidate = int(witness["candidate"])
    black = ",".join(cells(witness["black"]))
    white = ",".join(cells(witness["white_reply"]))
    output = run([
        str(SOLVER), "5", "--black", black,
        "--white", white, "--to-play", "black",
        "--tt-mb", "256", "--time", "120", "--attempts", "2"], 270)
    if output_fields(output).get("result") != "loss":
        raise VerificationError(f"candidate {candidate} replay disagreed")
    return candidate


def replay_hard_root(root: dict[str, str]) -> int:
    output = output_fields(run([
        str(HYPERGRAPH), "5", root["black"], root["white"],
        root["to_play"]]))
    for field in ("result", "winning_batch", "minimal_completions"):
        if output.get(field) != root[field]:
            raise VerificationError(
                f"candidate {root['candidate']} {field} disagreed")
    return int(root["candidate"])


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--jobs", type=int, default=8)
    arguments = parser.parse_args()
    if arguments.jobs < 1:
        raise VerificationError("--jobs must be positive")

    witnesses, hard_roots = inspect_artifacts()
    inspect_hypergraph_engine()
    equivalence = run([sys.executable, "-B", str(EQUIVALENCE)], 60).strip()
    if equivalence != "verified 11741 positions and both turns":
        raise VerificationError("completion-hypergraph equivalence failed")
    print("checked records, smaller empty boards, and engine agreement")

    completed = 0
    with ThreadPoolExecutor(max_workers=arguments.jobs) as executor:
        pending = {executor.submit(replay_witness, witness): witness
                   for witness in witnesses}
        for future in as_completed(pending):
            future.result()
            completed += 1
            if completed % 25 == 0 or completed == len(witnesses):
                print(f"replayed {completed}/253 handed roots", flush=True)
    for root in hard_roots:
        candidate = replay_hard_root(root)
        print(f"replayed hard root {candidate}", flush=True)
    print("verified all 255 exact roots")


if __name__ == "__main__":
    try:
        main()
    except VerificationError as error:
        print(f"error: {error}", file=sys.stderr)
        raise SystemExit(1)
