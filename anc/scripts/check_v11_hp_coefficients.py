#!/usr/bin/env python3
"""Finite exact regression checks for the v11 HP coefficient displays.

These checks do not prove the all-degree identities; those derivations are
given in hp-tail.tex.
"""

from fractions import Fraction as F
from math import comb, factorial


def harmonic(n):
    return sum((F(1, k) for k in range(1, n + 1)), F(0))


def residue(m, j):
    if j < 0 or j > m:
        return F(0), F(0)
    u = -F(factorial(3 * m + 1 - j), factorial(j) ** 2 * factorial(m - j) ** 3)
    v_over_u = 3 * harmonic(m - j) - 2 * harmonic(j) - harmonic(3 * m + 1 - j)
    return u, u * v_over_u


def h(m):
    return 3 * harmonic(m) - harmonic(3 * m + 1)


def delta(m):
    return h(m + 1) - h(m)


def r(m):
    return F(m**3, 3 * m + 1)


def c(m):
    return F(2) + F(3, m) - F(1, 3 * m + 1)


def main():
    for n in range(101):
        u_nn, v_nn = residue(n, n)
        u_n1n1, v_n1n1 = residue(n + 1, n + 1)
        u_nn1, v_nn1 = residue(n, n - 1)
        u_n1n, v_n1n = residue(n + 1, n)
        pi0 = v_n1n1 * u_nn - v_nn * u_n1n1
        pi1 = (v_n1n1 * u_nn1 + v_n1n * u_nn
               - v_nn * u_n1n - v_nn1 * u_n1n1)
        b = comb(2 * n + 1, n)
        expected_pi0 = -b * b * (12 * n + 17)
        expected_pi1 = (b * b * (2 * n + 1) * (n + 1)
                        * ((n + 1) * (12 * n + 17) + (21 * n + 29)))
        assert pi0 == expected_pi0, (n, pi0, expected_pi0)
        assert pi1 == expected_pi1, (n, pi1, expected_pi1)

        m = max(1, n)
        u_m0, v_m0 = residue(m, 0)
        u_m1, v_m1 = residue(m, 1)
        u_next0, v_next0 = residue(m + 1, 0)
        u_next1, v_next1 = residue(m + 1, 1)
        U_m = F(factorial(3 * m + 1), factorial(m) ** 3)
        U_next = F(factorial(3 * (m + 1) + 1), factorial(m + 1) ** 3)
        M0 = v_m0 * u_next0 - u_m0 * v_next0
        M1 = v_m0 * u_next1 + v_m1 * u_next0 - u_m0 * v_next1 - u_m1 * v_next0
        assert M0 == -U_m * U_next * delta(m), (m, M0)
        assert M1 == U_m * U_next * (
            -delta(m) * (r(m) + r(m + 1))
            + r(m + 1) * c(m + 1) - r(m) * c(m)
        ), (m, M1)

        theta = (
            -delta(n + 1) * (r(n + 1) + r(n + 2))
            + r(n + 2) * c(n + 2) - r(n + 1) * c(n + 1)
        ) / delta(n + 1) - F(8 * (n + 1), 9)
        expected_theta = F(
            1728 * n**4 + 11520 * n**3 + 28140 * n**2 + 29965 * n + 11770,
            18 * (3 * n + 4) ** 2 * (27 * n**2 + 108 * n + 104),
        )
        assert theta == expected_theta, (n, theta, expected_theta)

    print("PASS: exact Fraction regressions for HP coefficient displays, n=0..100")
    print("Scope: finite regression only; the all-degree proof is in hp-tail.tex.")


if __name__ == "__main__":
    main()
