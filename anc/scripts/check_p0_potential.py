#!/usr/bin/env python3
"""Independent high-precision quadrature check of the Appendix C P0 formulas."""
from __future__ import annotations

import argparse
from fractions import Fraction as F
import json
from pathlib import Path

import mpmath as mp
import paper_only_replay as replay


def mpq(q: F):
    return mp.mpf(q.numerator) / q.denominator


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--tex-root", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--dps", type=int, default=60)
    args = parser.parse_args()
    mp.mp.dps = args.dps

    main_tex, _ = replay.input_tree(args.tex_root / "main.tex")
    ref = replay.p0_table(main_tex, 2)
    den = ref["denominator"]
    masses = [F(w, den) for w in ref["contour_mass"]]
    xi, aa, bb = (mpq(F(x)) for x in ref["geom"])
    c, d = (aa + bb) / 2, (aa - bb) / 2
    rho = d / c
    theta = [mp.pi * (2 * j + 1) / 64 for j in range(64)]
    mass = sum(mpq(w) for w in masses)
    moment = [mp.mpf(0)] + [
        mp.mpf(49 - n) / 49
        * sum(mpq(w) * mp.cos(n * theta[j]) for j, w in enumerate(masses))
        for n in range(1, 49)
    ]

    def density(t):
        total = mp.mpf(0)
        for j, weight in enumerate(masses):
            if not weight:
                continue
            x = t - theta[j]
            sine = mp.sin(x / 2)
            kernel = (mp.sin(49 * x / 2) / sine) ** 2 / 49 if sine else mp.mpf(49)
            total += mpq(weight) * kernel
        return total / (2 * mp.pi)

    def contour(t):
        return xi + c * mp.e ** (1j * t) + d * mp.e ** (-1j * t)

    def direct(point):
        return mp.quad(
            lambda t: mp.log(abs(point - contour(t))) * density(t),
            mp.linspace(0, 2 * mp.pi, 65),
        )

    def inside(point):
        w = (point - xi) / c
        polys = [mp.mpf(2), w]
        for n in range(2, 49):
            polys.append(w * polys[-1] - rho * polys[-2])
        return mass * mp.log(c) - sum(
            moment[n] * polys[n] / n for n in range(1, 49)
        )

    def reflected_exterior(t):
        u = t + xi
        delta = mp.sqrt(u * u - 4 * c * d)
        s = -2 * c / (u + delta)
        return (mass * mp.log((u + delta) / 2)
                - sum((1 + rho**n) * moment[n] / n * s**n
                      for n in range(1, 49)))

    checks = []
    for point in (mp.mpf("0.5"),):
        actual, formula = direct(point), inside(point)
        error = abs(actual - formula)
        if error >= mp.mpf("1e-40"):
            raise AssertionError(f"interior t={point}: error {mp.nstr(error, 20)}")
        checks.append({"point": str(point), "type": "interior",
                       "direct": mp.nstr(actual, args.dps - 5),
                       "formula": mp.nstr(formula, args.dps - 5),
                       "absolute_difference": mp.nstr(error, 12)})
    t = mp.mpf("3")
    actual, formula = direct(-t), reflected_exterior(t)
    error = abs(actual - formula)
    if error >= mp.mpf("1e-40"):
        raise AssertionError(f"exterior point -{t}: error {mp.nstr(error, 20)}")
    checks.append({"point": str(-t), "type": "reflected exterior",
                   "direct": mp.nstr(actual, args.dps - 5),
                   "formula": mp.nstr(formula, args.dps - 5),
                   "absolute_difference": mp.nstr(error, 12)})

    result = {"status": "PASS", "precision_digits": args.dps,
              "quadrature": "mpmath over 64 equal subintervals",
              "checks": checks}
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
