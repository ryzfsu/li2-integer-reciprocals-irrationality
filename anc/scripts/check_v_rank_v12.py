#!/usr/bin/env python3
from __future__ import annotations

from fractions import Fraction
from pathlib import Path
import json
import math
import sympy as sp


def vp_int(x: int, p: int) -> int:
    if x == 0:
        return math.inf
    x = abs(x)
    v = 0
    while x % p == 0:
        x //= p
        v += 1
    return v


def vp_rat(x: sp.Rational, p: int) -> int:
    return vp_int(int(x.p), p) - vp_int(int(x.q), p)


def block_profile(n: int, p: int, u: int) -> tuple[int, int, int, int]:
    m = 4 * n
    K = []
    k = 0
    while True:
        x = Fraction(u + k * p, m)
        if x >= Fraction(3, 2):
            break
        if x >= Fraction(1, 2):
            K.append(k)
        k += 1
    L = []
    ell = 0
    while True:
        x = Fraction(u + ell * p, m)
        if x >= Fraction(5, 2):
            break
        if x >= Fraction(1, 4):
            L.append(ell)
        ell += 1
    W = []
    w = 1
    while True:
        x = Fraction(w * p - u, m)
        if x > Fraction(1, 4):
            break
        if x > 0:
            W.append(w)
        w += 1
    raw = min(2 * len(K) + len(W), len(L))
    saving = int(K == [0] and L == [0, 1] and W == [])
    return len(K), len(L), len(W), raw - saving


def make_matrix(n: int, q: int, T: int) -> sp.Matrix:
    m = 4 * n
    a = sp.Integer(-q)
    I = list(range(2 * n, 6 * n))
    J = list(range(n, 10 * n))
    t = {}
    b = {}
    for j in sorted(set(I + J)):
        t[j] = sum(a ** (j - r) / sp.Integer(r) for r in range(1, j + 1))
        b[j] = sum(a ** (j - r) / sp.Integer(r * r) for r in range(1, j + 1))
    rows = []
    for i in I:
        rows.append([
            (a ** i - a ** j) / sp.Integer(j - i) if i != j else sp.Integer(0)
            for j in J
        ])
    for i in I:
        rows.append([
            (t[i] - t[j]) / sp.Integer(j - i)
            if i != j
            else b[i]
            - T * (a ** i if i == j else 0)
            for j in J
        ])
    for ell in range(1, n + 1):
        rows.append([sp.Rational(1, j + ell) for j in J])
    return sp.Matrix(rows)


def run_one(n: int, q: int, p: int, T: int) -> dict:
    m = 4 * n
    U = 11 * n - 1
    N = 10 * n - 1
    if p % 2 == 0 or p * p <= max(N, U) or q % p == 0 or (q + 1) % p == 0:
        raise ValueError("prime conditions fail")
    profiles = [block_profile(n, p, u) for u in range(p)]
    sum_r = sum(x[3] for x in profiles)
    actual_ranks = scaled_block_ranks(n, q, p, T)
    block_rank_pass = all(actual <= profile[3]
                          for actual, profile in zip(actual_ranks, profiles))
    M = make_matrix(n, q, T)
    det = sp.cancel(M.det(method="domain-ge"))
    if det == 0:
        return {
            "n": n, "m": m, "q": q, "p": p, "T": T,
            "sum_r": sum_r, "actual_block_ranks": actual_ranks,
            "block_rank_pass": block_rank_pass, "det_zero": True,
        }
    v = vp_rat(det, p)
    rhs = -(m + sum_r)
    return {
        "n": n, "m": m, "q": q, "p": p, "T": T,
        "sum_r": sum_r, "actual_block_ranks": actual_ranks,
        "block_rank_pass": block_rank_pass,
        "vp": v, "rhs": rhs, "pass": v >= rhs,
        "det_digits": len(str(abs(int(det.p)))) + len(str(int(det.q))),
    }


def scaled_block_ranks(n: int, q: int, p: int, T: int) -> list[int]:
    m = 4 * n
    I = list(range(2 * n, 6 * n))
    J = list(range(n, 10 * n))
    M = make_matrix(n, q, T)
    rows = []
    for i in range(m):
        rows.append([sp.cancel(p * M[i, j]) for j in range(len(J))])
    for i in range(m):
        rows.append([sp.cancel(p * p * M[m + i, j]) for j in range(len(J))])
    for i in range(n):
        rows.append([sp.cancel(p * M[2 * m + i, j]) for j in range(len(J))])

    def residue_rank(block_rows: list[int], block_cols: list[int]) -> int:
        arr = []
        for i in block_rows:
            row = []
            for j in block_cols:
                x = rows[i][j]
                row.append((int(x.p) * pow(int(x.q), -1, p)) % p)
            arr.append(row)
        rank = 0
        c = 0
        while c < len(block_cols) and rank < len(arr):
            pivot = next((r for r in range(rank, len(arr)) if arr[r][c]), None)
            if pivot is None:
                c += 1
                continue
            arr[rank], arr[pivot] = arr[pivot], arr[rank]
            inv = pow(arr[rank][c], -1, p)
            arr[rank] = [(x * inv) % p for x in arr[rank]]
            for r in range(len(arr)):
                if r != rank and arr[r][c]:
                    fac = arr[r][c]
                    arr[r] = [(x - fac * y) % p for x, y in zip(arr[r], arr[rank])]
            rank += 1
            c += 1
        return rank

    out = []
    for u in range(p):
        cr = [r for r, i in enumerate(I) if i % p == u]
        br = [m + r for r, i in enumerate(I) if i % p == u]
        vr = [2 * m + r for r in range(n) if (-(r + 1)) % p == u]
        cc = [c for c, j in enumerate(J) if j % p == u]
        out.append(residue_rank(cr + br + vr, cc))
    return out


def main() -> None:
    choices = []
    for n in range(1, 6):
        primes = [p for p in (5, 7, 11, 13, 17, 19) if
                  p * p > max(10 * n - 1, 11 * n - 1)]
        for q in (2, 3, 4, 5, 6, 7):
            for p in primes:
                if q % p and (q + 1) % p:
                    choices.append((n, q, p, 0))
                    break
            for p in primes:
                if q % p and (q + 1) % p:
                    choices.append((n, q, p, 1))
                    break
    out = []
    for item in choices:
        print("checking", item, flush=True)
        out.append(run_one(*item))
    payload = {
        "count": len(out),
        "all_pass": all(x.get("pass", True) and x.get("block_rank_pass", True)
                        for x in out),
        "determinant_passes": sum(x.get("pass", True) for x in out),
        "block_rank_passes": sum(x.get("block_rank_pass", True) for x in out),
        "checks": out,
    }
    Path("/tmp/li2-v12-rankcheck-20261011/rank-check.json").write_text(
        json.dumps(payload, indent=2) + "\n", encoding="utf-8"
    )
    print(json.dumps(payload, indent=2))


if __name__ == "__main__":
    main()
