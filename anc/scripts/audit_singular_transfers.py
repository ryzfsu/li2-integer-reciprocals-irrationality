#!/usr/bin/env python3
"""Inventory every smoothing/transfer contact in the printed TeX source.

This is a fail-closed inventory, not a proof checker.  It records the source
line for each keyword family so a human audit can compare the disposition in
the research note with the actual argument.
"""
from __future__ import annotations

from pathlib import Path
import re


ROOT = Path(__file__).resolve().parents[2] / "source"
PATTERNS = {
    "P0 collar/source": re.compile(
        r"collar|source segment|primitive|Lipschitz|Poisson.*integral",
        re.I,
    ),
    "P0 smoothing/sweep": re.compile(
        r"smoothing|sweep|harmonic measure|tube transfer|Green|barrier",
        re.I,
    ),
    "V endpoint/circle": re.compile(
        r"endpoint|circle|Poisson|density|disk|bisection|support",
        re.I,
    ),
    "HP contour/endpoint": re.compile(
        r"contour|endpoint cell|bounded variation|Euler|singular|rectangle",
        re.I,
    ),
}


def main() -> None:
    hits: list[tuple[str, str, int, str]] = []
    for path in sorted(ROOT.rglob("*.tex")):
        lines = path.read_text(encoding="utf-8").splitlines()
        for line_no, line in enumerate(lines, 1):
            for category, pattern in PATTERNS.items():
                if pattern.search(line):
                    hits.append((category, str(path.relative_to(ROOT)), line_no, line.strip()))
    if not hits:
        raise SystemExit("FAIL: no transfer/singularity locations found")
    for category, path, line_no, line in hits:
        print(f"{category}\t{path}:{line_no}\t{line}")
    print(f"PASS: {len(hits)} classified source-line hits across {len({p for _, p, _, _ in hits})} TeX files")


if __name__ == "__main__":
    main()
