# Third-party notices

The Li2Lean proof build depends only on Mathlib (and Mathlib's own pinned
dependencies). Source code from the third-party projects below is included or
adapted in this repository under the Apache License, Version 2.0. The full
license text is in `LICENSES/Apache-2.0.txt`.

## 1. PrimeNumberTheoremAnd

- Upstream: https://github.com/AlexKontorovich/PrimeNumberTheoremAnd
- Commit: `c39a751132c88b6e8080b74c74023fd95b3d8be0`
- Authors: organized by Alex Kontorovich and Terence Tao, with contributors
- License: Apache-2.0 (upstream `LICENSE`, copied unmodified to
  `Li2Lean/Vendor/PNT/LICENSE` and `LICENSES/Apache-2.0.txt`); upstream has no
  NOTICE file.
- Purpose: `chebyshev_asymptotic : θ ~[atTop] id`, consumed only by
  `Li2Lean/Kit/PNTAdapter.lean` to discharge the `hPNT` contract.

Vendored files (copied and modified):

| Upstream path | Local path |
|---|---|
| `PrimeNumberTheoremAnd/Consequences.lean` | `Li2Lean/Vendor/PNT/Consequences.lean` |
| `PrimeNumberTheoremAnd/Wiener.lean` | `Li2Lean/Vendor/PNT/Wiener.lean` |
| `PrimeNumberTheoremAnd/Fourier.lean` | `Li2Lean/Vendor/PNT/Fourier.lean` |
| `PrimeNumberTheoremAnd/Sobolev.lean` | `Li2Lean/Vendor/PNT/Sobolev.lean` |
| `PrimeNumberTheoremAnd/SmoothExistence.lean` | `Li2Lean/Vendor/PNT/SmoothExistence.lean` |
| `PrimeNumberTheoremAnd/Mathlib/Algebra/Notation/Support.lean` | `Li2Lean/Vendor/PNT/Mathlib/Algebra/Notation/Support.lean` |
| `PrimeNumberTheoremAnd/Mathlib/Analysis/Asymptotics/Asymptotics.lean` | `Li2Lean/Vendor/PNT/Mathlib/Analysis/Asymptotics/Asymptotics.lean` |
| `PrimeNumberTheoremAnd/Mathlib/Analysis/SpecialFunctions/Log/Basic.lean` | `Li2Lean/Vendor/PNT/Mathlib/Analysis/SpecialFunctions/Log/Basic.lean` |
| `PrimeNumberTheoremAnd/Rectangle.lean` | `Li2Lean/Vendor/PNT/Rectangle.lean` |
| `PrimeNumberTheoremAnd/ResidueCalcOnRectangles.lean` | `Li2Lean/Vendor/PNT/ResidueCalcOnRectangles.lean` |

Modifications (2026-10-13):

- module paths and imports renamed from `PrimeNumberTheoremAnd.*` to
  `Li2Lean.Vendor.PNT.*`;
- `import Batteries.Tactic.Lemma` and `set_option lang.lemmaCmd true` removed
  (2026-10-15; `lemma` is provided by Mathlib), so no file imports anything
  outside Mathlib and this repository;
- `import Architect` removed, with every `@[blueprint ...]` attribute and
  `blueprint_comment` block (documentation metadata only);
- `Consequences.lean` truncated after `chebyshev_asymptotic`; its unused
  `import PrimeNumberTheoremAnd.Defs` removed (`Defs.lean` is not vendored);
- `Wiener.lean` truncated after `WeakPNT`; `prelim_decay_2`,
  `AbsolutelyContinuous`, `prelim_decay_3`, `decay_alt` removed (the two
  `prelim_decay_*` theorems have no proof upstream and unused by `WeakPNT`);
- `Rectangle.lean` retains the rectangle definitions and supporting lemmas; `ResidueCalcOnRectangles.lean` retains the rectangle integral, Cauchy-Goursat, and simple-pole sections (upstream lines 1-335 and 443-660). The pull-to-neighborhood and global sum-residue sections are omitted.
- a provenance header added to each file.

Retained declarations keep their upstream names (root namespace), statements
and proofs. See also `Li2Lean/Vendor/PNT/NOTICE`.

## 2. openai/math (Catalan 005)

- Upstream: https://github.com/openai/math
- Commit: `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`
- License: Apache-2.0 (repository-level; the source files carry no per-file
  copyright header)
- No openai/math module is imported; nothing below is a build dependency.

| Local file | Relation | Upstream reference |
|---|---|---|
| `Li2Lean/Kit/LogMonomial.lean` | adapted (generic power-log moment lemma `integral_pow_neg_log`) | `lean/OAI/NumberTheory/Catalan/Analysis/LogMonomial.lean` |
| `Li2Lean/Kit/GlobalApproximation.lean` | organization informed by the evaluator pattern; no source copied | Catalan 005 finite potential and interval soundness layers |
| `Li2Lean/P0/PinnedResidualEvaluator.lean` | shape of positive-log cell and interval composition informed; no source copied | `BarrierChebyshevLogFormula.lean`, `BarrierLogRatConstants.lean`, `ManuscriptBarrierFieldIntervals.lean` |
| `Li2Lean/P0/Tube.lean` | generic measure/integral packaging pattern informed (`sweptMeasure`); no source copied | Catalan 005 measure/integral packaging |

Modifications to the adapted file: restricted to the single generic lemma
(with its integrability helper), placed in namespace `Li2Lean.Kit`, header
`Adapted from openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb:<path>`
added.

## Build-time tools (not part of the proof build)

`leanprover/comparator` (commit `ca04cfc72b550331658ec314bf47685281bfd4bf`)
is an acceptance-checking tool for `Challenge`/`Solution`; it is no longer a
`require` of `lakefile.toml` and no project file imports it.
