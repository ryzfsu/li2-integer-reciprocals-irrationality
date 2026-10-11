# v13 Verification Environment

Date: 2026-10-11 (America/New_York)

The final paper-only directed replay ran under `nice -n 10` with Python 3.12.3
and python-flint 0.9.0 (Arb outward-rounded intervals). The receipt is
`paper-only-replay/verification.json`; it records `PASS`, a runtime of
318.6678 seconds, and hashes for all ten TeX files. Both P0 endpoints and all
six V base certificates reproduced from the printed tables; each cap check
was strict.

The clean PDF build uses pdfTeX 1.40.25 (TeX Live 2023/Debian) and latexmk
4.83 from an empty output directory. Its final PDF has 57 pages. The log has
no undefined references or overfull horizontal boxes. Nonfatal legacy
amsmath and PDF-string warnings remain. Rendered pages 7, 23, and 32 are
included under `reviews/visual-v13-20261011/`.
