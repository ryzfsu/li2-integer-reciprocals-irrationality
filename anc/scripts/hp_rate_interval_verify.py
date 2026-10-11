#!/usr/bin/env python3
"""Exact rational checks for the printed HP saddle and rate brackets."""

from fractions import Fraction as F


def cube(a):
    return a * a * a


def positive_t(q, t):
    return (q - 1) * cube(t) + 3 * (1 - q) * t * t - 3 * t + 1


def positive_s(q, s):
    return cube(s) - 3 * q * s + 2 * q


def negative_s(q, s):
    return cube(s) + 3 * q * s - 2 * q


def bracket(lo, hi, label):
    assert lo < hi, label


def endpoint_signs(fn, q, lo, hi, label):
    left, right = fn(q, lo), fn(q, hi)
    assert left * right < 0, (label, left, right)
    print(f"{label}: P(lo)={left}; P(hi)={right}")


def main():
    t = {11: (F(14179, 100000), F(14180, 100000)),
         12: (F(13681, 100000), F(13683, 100000))}
    sp = {11: (F(67602, 100000), F(67604, 100000)),
          12: (F(67521, 100000), F(67523, 100000))}
    sm = {7: (F(65338, 100000), F(65339, 100000)),
          8: (F(65496, 100000), F(65497, 100000))}

    for q, (lo, hi) in t.items():
        bracket(lo, hi, f"t({q})")
        endpoint_signs(positive_t, q, lo, hi, f"t({q})")
    for q, (lo, hi) in sp.items():
        bracket(lo, hi, f"s+({q})")
        endpoint_signs(positive_s, q, lo, hi, f"s+({q})")
    for q, (lo, hi) in sm.items():
        bracket(lo, hi, f"s-({q})")
        endpoint_signs(negative_s, q, lo, hi, f"s-({q})")

    # Taylor's lower bound and a geometric upper bound for exp(4).
    term = F(1)
    partial = F(1)
    for k in range(1, 17):
        term *= F(4, k)
        partial += term
    upper = partial + term * F(4, 17) * F(9, 7)
    e4_lo = F(6972316451, 127702575)
    e4_hi = F(377139364267, 6907548375)
    assert e4_lo == partial
    assert upper == e4_hi
    print(f"exp(4): lower series > {e4_lo}; upper series < {e4_hi}")

    rates = {
        "r+(11)": F(10937, 10000),
        "r+(12)": F(9834, 10000),
        "r-(7)": F(10877, 10000),
        "r-(8)": F(9587, 10000),
    }
    for q in (11, 12):
        tlo, thi = t[q]
        slo, shi = sp[q]
        lo = (e4_lo / (16 * q)
              * ((3 - tlo) / (1 - tlo)) ** 3 * slo**6)
        hi = (e4_hi / (16 * q)
              * ((3 - thi) / (1 - thi)) ** 3 * shi**6)
        assert lo > rates[f"r+({q})"]
        assert hi < F(10941 if q == 11 else 9837, 10000)
        print(f"r+({q}) in ({lo}, {hi})")
    for q in (7, 8):
        slo, shi = sm[q]
        lo = e4_lo * slo**3 / (2 * q)
        hi = e4_hi * shi**3 / (2 * q)
        assert lo > rates[f"r-({q})"]
        assert hi < F(10879 if q == 7 else 9589, 10000)
        print(f"r-({q}) in ({lo}, {hi})")

    print("PASS: all printed rational endpoint and rate brackets")


if __name__ == "__main__":
    main()
