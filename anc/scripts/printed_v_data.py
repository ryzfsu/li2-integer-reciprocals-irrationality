"""Exact decoder for the human-readable V reference tables in the paper."""
from __future__ import annotations

from fractions import Fraction
import re


def _decimal_table_rows(body: str) -> list[int]:
    """Read signed base-ten integer cells from a printed table body."""
    return [int(token) for token in re.findall(r"(?<![A-Za-z])[-+]?\d+", body)]


def decode_rows(text: str):
    """Decode only the printed decimal table format; encoded fallbacks fail."""
    chains: dict[tuple[int, str], list[tuple[object, object]]] = {}
    poissons: dict[int, list[tuple[object, object, object]]] = {}
    chain_pattern = re.compile(
        r"\\begin\{VChainTable\}\{(\d+)\}\{([^}]+)\}"
        r"\{(\d+)\}\{(-?\d+)\}\{(\d+)\}\{(-?\d+)\}"
        r"(.*?)\\end\{VChainTable\}", re.S)
    for match in chain_pattern.finditer(text):
        q, support, count, start, corr_j, corr_r, body = match.groups()
        if support.strip() == r"z\in[-q,-3/5]":
            support = "z_real"
        q, count, start, corr_j, corr_r = map(
            int, (q, count, start, corr_j, corr_r))
        values = _decimal_table_rows(body)
        if len(values) != 2 * count:
            raise ValueError(
                f"q={q} {support}: {len(values)} cells != {2 * count}")
        endpoint_den = 50_000_000_000_000
        coarse_den = 100_000_000
        previous = Fraction(start, endpoint_den)
        correction = Fraction(corr_r, endpoint_den)
        records = []
        for index in range(count):
            length, mass_delta = values[2 * index:2 * index + 2]
            length = Fraction(length, coarse_den)
            if corr_j == index + 1:
                length += correction
            following = previous + length
            records.append((previous, following,
                            Fraction(mass_delta, coarse_den)))
            previous = following
        chains[(q, support)] = records

    poisson_pattern = re.compile(
        r"\\begin\{VPoissonTable\}\{(\d+)\}\{(\d+)\}\{(\d+)\}"
        r"(.*?)\\end\{VPoissonTable\}", re.S)
    for match in poisson_pattern.finditer(text):
        q, count, prefix_count = map(int, match.groups()[:3])
        values = _decimal_table_rows(match.group(4))
        if len(values) != 3 * prefix_count:
            raise ValueError(
                f"q={q} Poisson: {len(values)} cells != {3 * prefix_count}")
        prefix = []
        previous = (Fraction(0), Fraction(0), Fraction(0))
        for index in range(prefix_count):
            delta = tuple(Fraction(values[3 * index + j], 100_000_000)
                          for j in range(3))
            current = tuple(previous[j] + delta[j] for j in range(3))
            prefix.append(current)
            previous = current
        if count != 2 * prefix_count - 1:
            raise ValueError(f"q={q} Poisson: bad prefix/full count")
        poissons[q] = prefix + [
            (a, -b, w) for a, b, w in reversed(prefix[:-1])]

    expected_q = set(range(2, 8))
    if (set(q for q, _ in chains) != expected_q or len(chains) != 18
            or set(poissons) != expected_q):
        raise ValueError("printed decimal tables do not cover q=2,...,7")

    out = {}
    for (q, support), records in chains.items():
        out[(q, support)] = [
            (index + 1, a, b, delta)
            for index, (a, b, delta) in enumerate(records)]
    for q, records in poissons.items():
        out[(q, "z_poisson")] = [
            (index + 1, a, b, mass)
            for index, (a, b, mass) in enumerate(records)]

    # Printed mass columns are increments between successive interval masses.
    for q in expected_q:
        for support in ("x", "y", "z_real"):
            cumulative = Fraction(0)
            converted = []
            for index, a, b, delta in out[(q, support)]:
                cumulative += delta
                converted.append((index, a, b, cumulative))
            out[(q, support)] = converted
    return out
