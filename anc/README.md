# Ancillary files for the reciprocal-dilogarithm paper (v12)

The directed numerical bounds in the paper are computer-assisted.  The
replay uses Python 3.12, python-flint 0.9.0, and outward-rounded Arb
intervals.  It reads the ordinary decimal and rational tables printed in the
paper; it does not read an optimizer checkpoint or a binary-encoded data
block.

The P0 evaluator reconstructs the two endpoint measures, the Fejer contour,
the finite Fourier/Joukowski moments, and the interval primitives.  It then
replays the contour, pinned, and frequency directed bounds.  The V evaluator
decodes the printed `VChainTable` and `VPoissonTable` blocks.  Chain headers
give the endpoint, scale, and one fine-grid correction.  Poisson rows are
successive increments followed by the prescribed conjugate completion.  The
endpoint boxes near zero and the deterministic midpoint subdivision are
checked exactly as specified in Appendix C.

From the extracted package root, run:

```text
PYTHONPATH=anc/scripts \
python3 anc/scripts/paper_only_replay.py \
  --tex-root source \
  --out /tmp/li2-paper-replay
```

The run is successful only when `verification.json` has `"status": "PASS"`.
`SCRIPTS_SHA256SUMS` covers every Python script in this directory. The final
version-specific receipt and cell ledgers are under
`logs/final-paper-only-replay-v12/`; earlier receipts are retained as history.

`check_p0_potential.py` independently compares the printed P0 potential
formulas with high-precision quadrature at one interior and one reflected
exterior point.  `check_q4_rate.py` checks the fixed-base rate calculation.
`trace_ranges.py` checks textual labels and table ranges only; it is not a
proof checker and does not verify any mathematical estimate.

The v12 replay also reads and checks the printed six-row (Q_{q,-})
lower-bound table in `v-analytic.tex` independently of the alpha table.

`audit_singular_transfers.py` inventories every TeX source line mentioning a
smoothing, sweep, harmonic-measure, tube, endpoint, or logarithmic contact.
Its deterministic output is `logs/v12/singular-transfer-inventory.tsv`; the
mathematical disposition of those locations is recorded in the linked
research note. This inventory is an audit aid and is not counted as a
certificate leaf.

The v11 regression scripts `check_v11_hp_coefficients.py` and
`hp_rate_interval_verify.py` perform exact rational checks of the displayed
HP coefficient identities for indices 0 through 100 and of the printed
saddle/rate endpoint brackets, respectively.  These are finite regression
checks; the all-degree arguments remain in `source/chapters/hp-tail.tex`.
The v11 replay receipt remains in `checks/v11-verification.json`. The final
v12 receipt and P0 directed cell ledgers are in
`logs/final-paper-only-replay-v12/`; exact v12 regression outputs are in
`logs/v12/`.
