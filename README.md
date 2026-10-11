# Irrationality of the dilogarithm at reciprocals of integers

Ruiyi Zhang

DOI: [10.5281/zenodo.23296412](https://doi.org/10.5281/zenodo.23296412)

The manuscript proves that `Li_2(1/n)` is irrational for every nonzero integer `n`.

The proof combines a determinant criterion with exact fixed-base integerization,
logarithmic-potential estimates, Frobenius nonvanishing and a three-form Hermite-Padé
construction. The finite positive range is treated by a common variational problem and two
endpoint certificates; the negative middle range by signed contour integrals at the six bases
`-2, ..., -7`; the two remaining tails by an explicit Hermite-Padé estimate. Every numerical
constant is given as a rational bound or an explicitly directed interval.

## Contents

- `main.pdf` (57 pages)
- `source/` - LaTeX source: `main.tex` and `chapters/`
- `anc/` - the ancillary files: the paper-only replay (`scripts/`), its logs and receipts
  (`logs/`, `checks/`) and `SCRIPTS_SHA256SUMS`. See `anc/README.md`.
- `SHA256SUMS`

## Build

    cd source
    pdflatex main.tex
    pdflatex main.tex

## Checks

Python 3.12 with python-flint 0.9.0. From the repository root:

    PYTHONPATH=anc/scripts python3 anc/scripts/paper_only_replay.py \
      --tex-root source --out /tmp/li2-paper-replay

The run succeeds when `verification.json` reports `"status": "PASS"` (about five minutes).

## Citation

Ruiyi Zhang, *Irrationality of the dilogarithm at reciprocals of integers*, preprint, Zenodo, 2026. https://doi.org/10.5281/zenodo.23296412

```bibtex
@misc{zhang2026li2reciprocals,
  author    = {Zhang, Ruiyi},
  title     = {Irrationality of the dilogarithm at reciprocals of integers},
  year      = {2026},
  publisher = {Zenodo},
  note      = {Preprint},
  doi       = {10.5281/zenodo.23296412},
  url       = {https://doi.org/10.5281/zenodo.23296412}
}
```
