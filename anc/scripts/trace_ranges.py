#!/usr/bin/env python3
"""Check printed source markers and table ranges; this is not a proof checker.

This script checks that expected labels, range rows, and seed rows occur in
the TeX. It does not verify determinant identities, valuation bounds, analytic
estimates, or directed interval calculations. Those claims require the paper
proofs and the separate numerical replay.
"""
from __future__ import annotations

import argparse
from fractions import Fraction as F
from hashlib import sha256
from pathlib import Path
import json
import re

def need(ok: bool, msg: str) -> None:
    if not ok:
        raise AssertionError(msg)

def parse_decimal(s: str) -> F:
    return F(s.strip())

def main() -> None:
    parser = argparse.ArgumentParser()
    default_root = Path(__file__).resolve().parents[2] / 'source'
    parser.add_argument('--tex-root', type=Path, default=default_root)
    parser.add_argument('--out', type=Path,
                        default=Path('/tmp/li2-alln-v10-source-check'))
    args = parser.parse_args()
    root = args.tex_root.resolve()
    paths = {
        'main.tex': root / 'main.tex',
        'v-analytic.tex': root / 'chapters/v-analytic.tex',
        'v-arithmetic.tex': root / 'chapters/v-arithmetic.tex',
        'nonvanishing.tex': root / 'chapters/nonvanishing.tex',
    }
    for path in paths.values():
        need(path.is_file(), f'missing source file: {path}')
    MAIN, VA, VR, NV = paths.values()
    texts = {p.name: p.read_text() for p in (MAIN, VA, VR, NV)}
    main_text, va, vr, nv = texts['main.tex'], texts['v-analytic.tex'], texts['v-arithmetic.tex'], texts['nonvanishing.tex']
    # The literal V determinant and its dimensions occur in the arithmetic chapter.
    for token in ('G_m(T;a)=\\det\\begin{bmatrix}C(a)\\',
                  'A_{ij}=a^i\\delta_{ij}',
                  '\\label{lem:v-formal-divisor}',
                  '\\label{prop:v-fixed-arithmetic}'):
        need(token in vr, f'missing V source token: {token}')
    # All-m analytic bridge and strict alpha comparison are explicit in the current chapter.
    for token in ('\\label{lem:v-concavity}', '\\label{lem:v-potential-modulus}',
                  '\\label{subsec:v-allm-proof}', '\\label{eq:v-allm-bound}',
                  'let $\\alpha_q$ be the strict lower endpoints',
                  'smoothing estimate below'):
        need(token in va, f'missing analytic bridge token: {token}')
    # Parse each q row of the directed table and verify strict decimal margin.
    rows = {}
    row_re = re.compile(
        r'(?m)^([2-7])&.*?\$>([0-9.]+)\$&\$<[0-9.]+\$.*?\$>([0-9.]+)\$\\\\')
    for m in row_re.finditer(va):
        q = int(m.group(1)); alpha = parse_decimal(m.group(2)); margin = parse_decimal(m.group(3))
        rows[q] = {'alpha': str(alpha), 'margin': str(margin)}
    need(set(rows) == set(range(2, 8)), f'analytic q rows: {sorted(rows)}')
    need(all(F(rows[q]['margin']) > 0 for q in rows), 'non-strict analytic margin')
    # Fixed-base arithmetic: exceptional sets and rate rows are both printed for q=2..7.
    for literal in (r'3&\{2,3\}&4&\{2,5\}',
                    r'5&\{2,3,5\}&6&\{2,3,7\}',
                    r'7&\{2,7\}&&',
                    r'The \(q=2\) row is \(\{2,3\}\)'):
        need(literal in vr, f'missing exceptional-set literal: {literal}')
    need('\\begin{proposition}[fixed-base arithmetic transfer]' in vr, 'missing fixed-base proposition')
    need('formal term contributes' in vr and 'exceptional-prime cost' in vr,
         'split exceptional-prime bounds missing')
    # V seed table: each row gives a base, an auxiliary prime, and a nonzero seed.
    seed_re = re.compile(r'(?m)^([2-7)&]+)&\$-([2-7])\$&([0-9]+)&')
    seeds = {}
    for m in seed_re.finditer(nv):
        seeds[int(m.group(2))] = int(m.group(3))
    need(set(seeds) == set(range(2, 8)), f'V seeds: {sorted(seeds)}')
    need('negative-base eventual nonvanishing' in nv and '\\label{eq:v-frobenius}' in nv,
         'V eventual nonvanishing statement missing')
    # All six q values are named in the analytic and nonvanishing quantifiers.
    need('q=2,\\ldots,7' in va and 'r\\in\\{2,3,4,5,6,7\\}' in nv,
         'q range quantifier missing')
    # The theorem source now claims all nonzero integers and no stale open claim remains.
    need('every nonzero integer $n$' in main_text and 'negative-middle work item' not in main_text,
         'main theorem still has old open boundary')
    need('Theorem~\\ref{thm:main}' in main_text and 'a\\le-8' in main_text,
         'tail coverage missing')
    result = {
        'status': 'PASS',
        'q_values': list(range(2, 8)),
        'rows': rows,
        'seed_primes': seeds,
        'literal_determinant': 'V G_m(T;a) from chapters/v-arithmetic.tex',
        'interfaces': ['formal divisor and denominator',
                       'fixed-base residue/outer/PNT estimates',
                       'directed full-support field bounds and all-m smoothing',
                       'eventual nonvanishing sequence'],
        'scope': ('textual source consistency only; not a proof or numerical '
                  'verification'),
        'sha256': {p.relative_to(root.parent).as_posix(): sha256(p.read_bytes()).hexdigest()
                   for p in (MAIN, VA, VR, NV)},
    }
    args.out.mkdir(parents=True, exist_ok=True)
    (args.out / 'range_trace.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()
