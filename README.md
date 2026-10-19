# Irrationality of the dilogarithm at reciprocals of integers

Ruiyi Zhang

DOI: [10.5281/zenodo.23296411](https://doi.org/10.5281/zenodo.23296411)

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
- `lean/` - Lean 4 formalization of the main theorem (see below and `lean/README.md`)
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

## Lean formalization

`lean/` contains a Lean 4 formalization of the main theorem (Lean 4.35.0-rc4,
Mathlib `25e572b8`). The formal statement is

```lean
theorem li2_inv_irrational (n : ℤ) (hn : n ≠ 0) :
    Irrational (∑' k : ℕ, ((n : ℝ)⁻¹) ^ (k + 1) / ((k : ℝ) + 1) ^ 2)
```

The only hypothesis is `n ≠ 0`. The proof depends only on the axioms `propext`,
`Classical.choice` and `Quot.sound`. The independent `nanoda` kernel accepts the
complete proof (127,511 declarations), and the Lean kernel accepts it through the
`comparator` tool; the receipts are in `lean/verification/`.

The formalization follows the case split of the paper:

| range of `n` | argument | main Lean theorem |
|---|---|---|
| `n = 1`, `n = -1` | `Li_2(±1)` is a rational multiple of `π²` | `irrational_pi_sq` |
| `n = 2` | the case `1/2` | `li2_half_irrational_unconditional` |
| `3 ≤ n ≤ 11` | endpoint certificates (positive range) | `l1_endpoint_criterion` |
| `-7 ≤ n ≤ -2` | signed contour certificates | `l1_endpoint_criterion` |
| `n ≥ 12`, `n ≤ -8` | Hermite-Padé tails | `hp_tail_irrational` |

Several certificates use an equivalent intermediate construction instead of the
printed one (for example, a different grid or truncation). `lean/RELEASE_NOTES.md`
lists all sixteen differences. The formalization also found one misprint: in
`source/chapters/v-analytic.tex` (line 366, row 6 of the table), the lower bound
`3.26092` should read `3.26091` and the margin `0.15632` should read `0.15631`. The
margin stays positive, so the argument is unchanged. `lean/README.md` explains how
to build and check the proof.

## Citation

Ruiyi Zhang, *Irrationality of the dilogarithm at reciprocals of integers*, preprint, Zenodo, 2026. https://doi.org/10.5281/zenodo.23296411

```bibtex
@misc{zhang2026li2reciprocals,
  author    = {Zhang, Ruiyi},
  title     = {Irrationality of the dilogarithm at reciprocals of integers},
  year      = {2026},
  publisher = {Zenodo},
  note      = {Preprint},
  doi       = {10.5281/zenodo.23296411},
  url       = {https://doi.org/10.5281/zenodo.23296411}
}
```
