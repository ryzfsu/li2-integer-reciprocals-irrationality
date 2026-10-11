# v12 Verification Environment

Date: 2026-10-11 (America/New_York)

The final paper-only directed replay ran under `nice -n 10` with Python 3.12.3
and python-flint 0.9.0 (Arb outward-rounded intervals). Its receipt is
`logs/final-paper-only-replay-v12/verification.json`; the ten printed TeX
SHA-256 values match the source tree. The P0 cell ledgers are stored beside
the receipt. The replay also checks the six printed V energy lower endpoints
independently of the alpha table.

The finite HP rational regressions ran under `nice -n 10` using
Python's standard-library `fractions.Fraction`. Their logs are in
`logs/v12/`; they check the displayed formulas over the stated finite ranges
only and do not replace the all-degree proofs in the paper.

The clean PDF build uses pdfTeX 1.40.25 (TeX Live 2023/Debian) and latexmk
4.83 from an empty output directory. The exact command is in
`build/COMMAND.txt`. The final log has no undefined references. It reports one
1.55368 pt overfull vertical box on page 29; the rendered page was inspected
and shows no clipping or overlap. Nonfatal hyperref PDF-string and legacy
amsmath warnings remain.
