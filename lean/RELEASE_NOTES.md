# Li2(1/n) Release Candidate Notes

## Source

- Source commit: `f9768a9c1db0f24ef5cef62a5ada4642e6c89524`.
- Solution import closure: 1603 modules, with no missing internal source.
- `lake build Solution Challenge`: passed.
- `#print axioms li2_inv_irrational`: exactly `propext`, `Classical.choice`, and
  `Quot.sound`.
- Challenge and Solution have identical normalized theorem statements.

## Differences from v13

The following table records the sixteen certificate and interface differences
identified against the v13 formulation. A relation of “equivalent” means that
the Lean certificate proves the same mathematical conclusion by a different
intermediate construction.

| # | Topic | v13 reference | Lean certificate | Relation |
|---|---|---|---|---|
| D1 | D_q energy series truncation and tail | `certificate-algorithm.tex:117-121`, degree 420 and geometric tail | `Li2Lean/V/EnergyCertI/IEnergyEval.lean:86-93`, `Li2Lean/B3/DEdBridge.lean:32-47`, degree 50 with an alternating remainder | Equivalent certificate |
| D2 | V circle-cell parametrization | `z = (3/5) e^{i pi t}` cells | `Li2Lean/V/EnergyCert/FieldEval.lean:94-95`, rational quarter parameters and `Li2Lean/B3/V13ArcCell.lean:797` | Equivalent re-gridding |
| D3 | V log-interval split | One `log(3/5)` interval | Separate `vLogRF` and `vLogRE` chains | Equivalent implementation detail |
| D4 | q = 11 frequency penalty table | 16384 equal cells and `h_mu = 1217/200` | Printed prefix rows with three-piece splits, followed by 44 tail cells at floor `1217/200`; penalty mass `437939106871569/409600000000000` | Equivalent re-gridding |
| D5 | q = 11 contour floor | v13 contour nodes and Fourier constants | `Li2Lean/P0/Q11CA/Contour/Q11GammaContourCertificate.lean:7-28`, reflection, Taylor bound, and the checked 48-entry table | Equivalent certificate |
| D6 | q11 BTab index 47 data | Generated table entry | `Li2Lean/P0/Q11CA/Contour/Q11BTab.lean:61`, checked at `:74-79` | Corrected generated data |
| D7 | alpha_6 | `v-analytic.tex:366`, lower bound `3.26092` and margin `0.15632` | `Li2Lean/V/EnergyCertI/Consts.lean:74-81` and related bounds use `3.26091` and margin `0.15631` | Paper erratum |
| D8 | Seed row residues modulo `p_r` | `nonvanishing.tex:170-198`, printed residue table | `Li2Lean/B3/H3RowResidueZMod.lean:12-31` and q-specific files use modular LU certificates and an inverse Vandermonde | Equivalent method |
| D9 | Frobenius block sign | `nonvanishing.tex:248-252`, symbolic sign `epsilon_{r,k}` | `Li2Lean/B3/VScaledConstantUnit.lean:33-36` and `Li2Lean/B3/VActualFrobeniusAssembly.lean:46` keep the sign symbolic | Faithful |
| D10 | H4 fixed-base arithmetic rate | `v-arithmetic.tex:353-421`, limsup rate with a PNT error term | `Li2Lean/B3/H4RateBudgetBridge.lean:9-13` and `Li2Lean/B3/H4PrimeSumMajorantProof.lean:13-27` use an eventual rate and an all-n majorant | Equivalent rate bound |
| D11 | P0 uniform determinant bound | `p0-analytic.tex`, `eq:p0-q-uniform-det` | `Li2Lean/AllN/ProducerAssembly.lean:55-67` uses the paper-faithful `P0PaperAnalyticEstimate` | Faithful |
| D12 | P0 coefficient step | `|G_m(beta)| <= E_m(infinity)` and the finite-H comparison | `Li2Lean/P0/CoefficientStepMain.lean:126-134` uses `E_m(infinity)` directly | Faithful |
| D13 | V S0 transfer and `phiMax` | `v-analytic.tex:106-145,522-610` | `Li2Lean/B3/S0ActualInterface.lean:269-283` permits the corrected n-dependent `phiMax` | Faithful corrected shape |
| D14 | P0 reference qLog bound | v10/v13 enclosure `qLogLower = -0.438334707` | `Li2Lean/P0/CA/Receipt/Receipt.lean:65-71` uses the weaker `-11/25`, absorbed by the available slack | Valid weaker intermediate |
| D15 | P0 source diagonal `p0BQQ` | v13 source formula | `Li2Lean/P0/Source.lean:286-309` uses the corrected transcription and a regression check | Lean transcription correction |
| D16 | HP positive tail for `a >= 12` | v13 HP-tail beta certificate | `Li2Lean/AllN/Producers.lean:236-257,857-863` uses the refined constant `M = 154/1000` and rate `0.99241` at `q = 12` | Refined certificate |

### Alpha-6 erratum

At `v-analytic.tex:366`, the printed lower bound `3.26092` should be
`3.26091`. Consequently the printed margin `0.15632` should be `0.15631`.
The Lean constants use the corrected values.

## Kernel-portability changes for nanoda

An independent check with nanoda 0.4.19 found that three proofs made that
checker reduce a concrete 9 by 9 determinant symbolically, which overflowed its
16 MiB worker stack or exhausted memory. The Lean kernel accepted the original
proofs. The statements are unchanged; only the proofs were rewritten:

- `Li2Lean.B3.q2_determinant_good`: the matrix is rewritten to its explicit
  value before the denominator condition is unfolded, so definitional
  unfolding only meets a rational literal.
- `Li2Lean.B3.q2_seed_residue_det_eq_four`: the residue matrix is first
  identified entrywise with the explicit matrix, so the final step is a
  syntactic match.
- `Li2Lean.vTwoSeed_det_zero`: the nested row-operation reduction is replaced
  by an explicit LU factorisation modulo 11 (rows 2 and 3 swapped,
  det U = 7, sign -1, so det = -7 = 4), checked entry by entry by kernel
  evaluation.

Each of the three declarations, exported on its own, now checks in nanoda in
under two seconds.

## Independent verification

The comparator performs its own export and the Lean-kernel check with nanoda
disabled. Nanoda checks a separate `lean4export` export of the Solution
closure (SHA-256 recorded in `verification/export.sha256`) with the same three
permitted axioms. The two checks are independent; their results are recorded
in `verification/`.
