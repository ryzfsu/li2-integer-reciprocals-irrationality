/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang

H6 ball-bound side, all six bases q = 2..7.

For each H6 leaf this module produces, at the exact row source used by the
leaf template and for an arbitrary base-range proof `hq`:

* `Ax Av Az`, their nonnegativity, the three sharp `VBallBound` proofs and
  `sigma_eq : vSigma q = sigmaBudget Ax Av Az`
  (sharp constants `A_x = 2 H_x`, `A_v = 2 H_v`, `A_z0 = 2 H_z + P_q`,
  then `Az := v13AzSolved q Ax Av ≥ A_z0`; v13 `v-analytic.tex:412-437`);
* `dual_admissible` via `signedVReferenceIntegrable_of_ballBound`;
* `EnergyTotalSoundnessFact` via `v13_total_fact_of_ballBound`
  (NOT `v13_total_fact`: that one consumes a finished `V13NumericCertificates`,
  whose `energy_lower` field is itself derived from the total fact);
* a `V13NumericCertificates` builder in which only energy_lower, the three
  global field bounds, the two endpoint disks are still explicit;
* the missing finite row bundles `q2_field_row_facts`, `q5_field_row_facts`
  and the q3 row-source transports.

The generic analytic content (sharp chain bound through `chainCellsOK`,
circle-arc/Poisson ball bound, `v13AzSolved`, per-q `decide +kernel` checks,
uniform theorem `v13RefMeasure_ball_and_sigma`) lives in the S5 file
`V13BallGeneric.lean`, imported after the
three renames listed in the proof plan section 3 (name clashes with master's
`H6S5BallBounds` / `VBallBoundAdd`).

Exact-rational numerics (sigma_check.py, sigma_check_output.txt in this
directory): the slack `Az_solved - A_z0` is positive for every q:
q2 1.168e-6, q3 6.990e-6, q4 1.734e-5, q5 4.655e-5, q6 4.672e-5, q7 3.601e-6.

All names below resolve in the release closure; transport details are recorded
as ordinary implementation notes.
-/

import Li2Lean.B3.V13BallGeneric   -- de-conflicted generic ball-bound module
import Li2Lean.B3.V13TotalIdentity
import Li2Lean.B3.ReferenceDualIntegrable
import Li2Lean.B3.ReferencePackageLeafTemplates   -- q2/q6/q7 row bounds and normalizations
import Li2Lean.B3.H6ReferencePackageTemplates     -- q5 row bounds
import Li2Lean.B3.Q2ReferenceNormalizationAdapter
import Li2Lean.B3.Q3ReferenceRowBounds
import Li2Lean.B3.Q3ReferenceNormalizationBridge
import Li2Lean.B3.Q4ReferenceNormalization
import Li2Lean.B3.Q5ReferenceNormalization
import Li2Lean.B3.F6Alpha
import Li2Lean.B3.H6Q3FieldRowFacts
import Li2Lean.B3.H6Q4FieldRowFacts
import Li2Lean.B3.H6Q6FieldRowFacts
import Li2Lean.B3.H6Q7FieldRowFacts

namespace Li2Lean.B3

noncomputable section

open MeasureTheory Set
open V
open V.EnergyCertI
open V.EnergyCertI.IK

/-! ## 1. q-generic S5 closers -/

/-- `dual_admissible` from the three S5 ball bounds. -/
theorem v13_s5_dual_admissible {q : ℕ} {hq : SignedVBaseRange q}
    (R : V13DecodedRows q) (rows : V13DecodedRowBounds q R)
    (N : V13MeasureNormalization hq (v13RefRaw R)) :
    SignedVReferenceIntegrable (v13RefMeasure R N) := by
  obtain ⟨hAx, hAv, hAz, hx, hv, hz, -⟩ := v13RefMeasure_ball_and_sigma R N
  exact signedVReferenceIntegrable_of_ballBound R rows N hAx hAv hAz hx hv hz

/-- Same-measure total fact from the S5 ball bounds and the finite row bundle.
The Poisson hypothesis `hnorm : ∀ c ∈ R.data.full, ‖v13PoissonPoint c‖ < 3/5`
used throughout `V13TotalIdentity` is discharged there from
`hR.full_rows_data` (`v13PrOk_props`, last conjunct), i.e. from the field
`full_ok : R.data.full.all v13PrOk = true` proved by `decide +kernel`. -/
theorem v13_s5_total_fact {q : ℕ} {hq : SignedVBaseRange q}
    (R : V13DecodedRows q) (hR : V13FieldRowFacts R)
    (rows : V13DecodedRowBounds q R)
    (N : V13MeasureNormalization hq (v13RefRaw R))
    (plan : List (EKind × Nat × Nat × Int)) :
    EnergyTotalSoundnessFact (v13RefMeasure R N) R.data plan
      (vEnergyTerm q R.data) := by
  obtain ⟨hAx, hAv, hAz, hx, hv, hz, -⟩ := v13RefMeasure_ball_and_sigma R N
  exact v13_total_fact_of_ballBound R hR rows N hAx hAv hAz hx hv hz plan

/-- `V13NumericCertificates` with all ball/sigma/dual fields filled by S5.
Only the energy lower bound, the three global field bounds, the alpha
inequality and the two endpoint disks stay explicit. -/
noncomputable def v13NumericCertificates_of_s5 {q : ℕ} {hq : SignedVBaseRange q}
    (R : V13DecodedRows q) (rows : V13DecodedRowBounds q R)
    (N : V13MeasureNormalization hq (v13RefRaw R))
    (energy_lower : ((vQlow q : ℚ) : ℝ) <
      V.signedVQuadratic (v13RefMeasure R N))
    (x_field : ∀ t : ℝ, t ∈ Set.Ioc (0 : ℝ) 1 →
      V.signedVFullFieldX (v13RefMeasure R N) (t : ℂ) < (vKx q : ℝ))
    (v_field : ∀ t : ℝ, t ∈ Set.Ioc (0 : ℝ) 1 →
      V.signedVFullFieldV (v13RefMeasure R N) (t : ℂ) < (vKv q : ℝ))
    (z_field : ∀ w ∈ V.vContourTrace q,
      V.signedVFullFieldZ (v13RefMeasure R N) w < (vKz q : ℝ))
    (alpha_le : vAlpha q ≤ (vQlow q : ℝ) - 3 / 2 * Real.log q -
      (vKx q : ℝ) - 5 / 4 * (vKv q : ℝ) - (vKz q : ℝ))
    (x_endpoint_disk : ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ ≤ 1 / 250 →
      V.signedVFullFieldX (v13RefMeasure R N) w ≤ (vEx q : ℝ))
    (v_endpoint_disk : ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ ≤ 1 / 250 →
      V.signedVFullFieldV (v13RefMeasure R N) w ≤ (vEv q : ℝ)) :
    V13NumericCertificates q hq R where
  rows := rows
  normalization := N
  Ax := v13Ax q
  Av := v13Av q
  Az := v13Az q
  Ax_nonneg := v13Ax_nonneg q
  Av_nonneg := v13Av_nonneg q
  Az_nonneg := v13Az_nonneg hq
  x_ball := (v13RefMeasure_ball_and_sigma R N).2.2.2.1
  v_ball := (v13RefMeasure_ball_and_sigma R N).2.2.2.2.1
  z_ball := (v13RefMeasure_ball_and_sigma R N).2.2.2.2.2.1
  sigma_eq := v13_sigma_eq q
  energy_lower := energy_lower
  x_field := x_field
  v_field := v_field
  z_field := z_field
  alpha_le := alpha_le
  x_endpoint_disk := x_endpoint_disk
  v_endpoint_disk := v_endpoint_disk
  dual_admissible := v13_s5_dual_admissible R rows N

/-- The builder keeps the supplied normalization, so every ledger field stated
at `v13RefMeasure R C.normalization` is definitionally a field at `N`. -/
@[simp] theorem v13NumericCertificates_of_s5_normalization
    {q : ℕ} {hq : SignedVBaseRange q}
    (R : V13DecodedRows q) (rows : V13DecodedRowBounds q R)
    (N : V13MeasureNormalization hq (v13RefRaw R)) (el xf vf zf al xd vd) :
    (v13NumericCertificates_of_s5 R rows N el xf vf zf al xd vd).normalization = N :=
  rfl

/-! ## 2. Missing finite row bundles -/

/-! ### q = 3 row-source transport

`H6Q3FieldRowFacts`, `Q3ReferenceRowBounds` and
`Q3ReferenceNormalizationBridge` are stated at `q3DecodedRows`, while the leaf
template `v13_reference_package_input_q3_of_v13_certificates` uses
`q3DecodedReferenceRows`.  Both are `{ data := q3D, source := _ }`; every
statement below only reads `.data`, so the transport is definitional
(structure-literal unfolding + proof irrelevance of `source`). -/

theorem q3_field_row_facts_reference :
    V13FieldRowFacts q3DecodedReferenceRows :=
  q3_field_row_facts   -- definitional transport; fields read `.data`

theorem q3_decoded_row_bounds_reference :
    V13DecodedRowBounds 3 q3DecodedReferenceRows :=
  q3_decoded_row_bounds   -- definitional transport (fields read `.data` only)

theorem q3ReferenceNormalization_reference_of_hq (hq : SignedVBaseRange 3) :
    V13MeasureNormalization hq (v13RefRaw q3DecodedReferenceRows) :=
  q3ReferenceNormalization_of_hq hq   -- `v13RefRaw` reads `.data` only

/-! ### q = 2 finite row bundle (mirrors `H6Q4FieldRowFacts` line by line).
The q2 headers are qualified because `Li2Lean.V.Q2Certificate` also defines
`q2XHeader`/`q2XEntries` (`H6S5BallBounds` does the same). -/

set_option maxHeartbeats 2000000 in
theorem q2_field_row_facts : V13FieldRowFacts q2ReferenceRows := by
  refine {
    x_cells := ?_
    v_cells := ?_
    z_cells := ?_
    x_rows := ?_
    v_rows := ?_
    z_rows := ?_
    x_jump := ?_
    v_jump := ?_
    z_jump := ?_
    pre_ok := ?_
    full_ok := ?_ }
  · change ∀ c ∈ v13ChainCells q2D.xp, 0 ≤ c.left ∧ c.left ≤ c.right ∧ 0 ≤ c.density
    norm_num [q2D, mkIData, v13ChainCells, v13ChainCellsAux, chainCP,
      V.EnergyCertI.q2XHeader, V.EnergyCertI.q2XEntries, chainCoords, chainMassU,
      densI, jumpsI,
      Li2Lean.V.Q2Certificate.decodeChain,
      Li2Lean.V.Q2Certificate.decodeChainAux,
      Li2Lean.V.Q2Certificate.correctedLength,
      Li2Lean.V.Q2Certificate.scaleLength,
      Li2Lean.V.Q2Certificate.scaleMass, IK.val, qadd, qsub, qneg, qmul, U]
  · change ∀ c ∈ v13ChainCells q2D.vp, 0 ≤ c.left ∧ c.left ≤ c.right ∧ 0 ≤ c.density
    norm_num [q2D, mkIData, v13ChainCells, v13ChainCellsAux, chainCP,
      V.EnergyCertI.q2YHeader, V.EnergyCertI.q2YEntries, chainCoords, chainMassU,
      densI, jumpsI,
      Li2Lean.V.Q2Certificate.decodeChain,
      Li2Lean.V.Q2Certificate.decodeChainAux,
      Li2Lean.V.Q2Certificate.correctedLength,
      Li2Lean.V.Q2Certificate.scaleLength,
      Li2Lean.V.Q2Certificate.scaleMass, IK.val, qadd, qsub, qneg, qmul, U]
  · change ∀ c ∈ v13ChainCells q2D.zp, c.left ≤ c.right ∧ 0 ≤ c.density
    norm_num [q2D, mkIData, v13ChainCells, v13ChainCellsAux, chainCP,
      V.EnergyCertI.q2ZHeader, V.EnergyCertI.q2ZEntries, chainCoords, chainMassU,
      densI, jumpsI,
      Li2Lean.V.Q2Certificate.decodeChain,
      Li2Lean.V.Q2Certificate.decodeChainAux,
      Li2Lean.V.Q2Certificate.correctedLength,
      Li2Lean.V.Q2Certificate.scaleLength,
      Li2Lean.V.Q2Certificate.scaleMass, IK.val, qadd, qsub, qneg, qmul, U]
  · change ∀ p ∈ q2D.xp, 0 ≤ p.e.1 ∧ 0 < p.e.2 ∧ 0 < p.J.2
    norm_num [q2D, mkIData, chainCP, V.EnergyCertI.q2XHeader,
      V.EnergyCertI.q2XEntries, chainCoords, chainMassU, densI, jumpsI,
      Li2Lean.V.Q2Certificate.decodeChain,
      Li2Lean.V.Q2Certificate.decodeChainAux,
      Li2Lean.V.Q2Certificate.correctedLength,
      Li2Lean.V.Q2Certificate.scaleLength,
      Li2Lean.V.Q2Certificate.scaleMass, IK.val, qadd, qsub, qneg, qmul, U]
  · change ∀ p ∈ q2D.vp, 0 ≤ p.e.1 ∧ 0 < p.e.2 ∧ 0 < p.J.2
    norm_num [q2D, mkIData, chainCP, V.EnergyCertI.q2YHeader,
      V.EnergyCertI.q2YEntries, chainCoords, chainMassU, densI, jumpsI,
      Li2Lean.V.Q2Certificate.decodeChain,
      Li2Lean.V.Q2Certificate.decodeChainAux,
      Li2Lean.V.Q2Certificate.correctedLength,
      Li2Lean.V.Q2Certificate.scaleLength,
      Li2Lean.V.Q2Certificate.scaleMass, IK.val, qadd, qsub, qneg, qmul, U]
  · change ∀ p ∈ q2D.zp, 0 < p.e.2 ∧ 0 < p.J.2
    norm_num [q2D, mkIData, chainCP, V.EnergyCertI.q2ZHeader,
      V.EnergyCertI.q2ZEntries, chainCoords, chainMassU, densI, jumpsI,
      Li2Lean.V.Q2Certificate.decodeChain,
      Li2Lean.V.Q2Certificate.decodeChainAux,
      Li2Lean.V.Q2Certificate.correctedLength,
      Li2Lean.V.Q2Certificate.scaleLength,
      Li2Lean.V.Q2Certificate.scaleMass, IK.val, qadd, qsub, qneg, qmul, U]
  · change (q2D.xp.map fun p => IK.val p.J).sum = 0
    norm_num [q2D, mkIData, chainCP, V.EnergyCertI.q2XHeader,
      V.EnergyCertI.q2XEntries, chainCoords, chainMassU, densI, jumpsI,
      Li2Lean.V.Q2Certificate.decodeChain,
      Li2Lean.V.Q2Certificate.decodeChainAux,
      Li2Lean.V.Q2Certificate.correctedLength,
      Li2Lean.V.Q2Certificate.scaleLength,
      Li2Lean.V.Q2Certificate.scaleMass, IK.val, qadd, qsub, qneg, qmul, U]
  · change (q2D.vp.map fun p => IK.val p.J).sum = 0
    norm_num [q2D, mkIData, chainCP, V.EnergyCertI.q2YHeader,
      V.EnergyCertI.q2YEntries, chainCoords, chainMassU, densI, jumpsI,
      Li2Lean.V.Q2Certificate.decodeChain,
      Li2Lean.V.Q2Certificate.decodeChainAux,
      Li2Lean.V.Q2Certificate.correctedLength,
      Li2Lean.V.Q2Certificate.scaleLength,
      Li2Lean.V.Q2Certificate.scaleMass, IK.val, qadd, qsub, qneg, qmul, U]
  · change (q2D.zp.map fun p => IK.val p.J).sum = 0
    norm_num [q2D, mkIData, chainCP, V.EnergyCertI.q2ZHeader,
      V.EnergyCertI.q2ZEntries, chainCoords, chainMassU, densI, jumpsI,
      Li2Lean.V.Q2Certificate.decodeChain,
      Li2Lean.V.Q2Certificate.decodeChainAux,
      Li2Lean.V.Q2Certificate.correctedLength,
      Li2Lean.V.Q2Certificate.scaleLength,
      Li2Lean.V.Q2Certificate.scaleMass, IK.val, qadd, qsub, qneg, qmul, U]
  · decide +kernel
  · decide +kernel

/-! ### q = 5 finite row bundle (same template). -/

set_option maxHeartbeats 2000000 in
theorem q5_field_row_facts : V13FieldRowFacts q5DecodedReferenceRows := by
  refine {
    x_cells := ?_
    v_cells := ?_
    z_cells := ?_
    x_rows := ?_
    v_rows := ?_
    z_rows := ?_
    x_jump := ?_
    v_jump := ?_
    z_jump := ?_
    pre_ok := ?_
    full_ok := ?_ }
  · change ∀ c ∈ v13ChainCells q5D.xp, 0 ≤ c.left ∧ c.left ≤ c.right ∧ 0 ≤ c.density
    norm_num [q5D, mkIData, v13ChainCells, v13ChainCellsAux, chainCP,
      V.EnergyCertI.q5XHeader, V.EnergyCertI.q5XEntries, chainCoords, chainMassU,
      densI, jumpsI,
      Li2Lean.V.Q2Certificate.decodeChain,
      Li2Lean.V.Q2Certificate.decodeChainAux,
      Li2Lean.V.Q2Certificate.correctedLength,
      Li2Lean.V.Q2Certificate.scaleLength,
      Li2Lean.V.Q2Certificate.scaleMass, IK.val, qadd, qsub, qneg, qmul, U]
  · change ∀ c ∈ v13ChainCells q5D.vp, 0 ≤ c.left ∧ c.left ≤ c.right ∧ 0 ≤ c.density
    norm_num [q5D, mkIData, v13ChainCells, v13ChainCellsAux, chainCP,
      V.EnergyCertI.q5YHeader, V.EnergyCertI.q5YEntries, chainCoords, chainMassU,
      densI, jumpsI,
      Li2Lean.V.Q2Certificate.decodeChain,
      Li2Lean.V.Q2Certificate.decodeChainAux,
      Li2Lean.V.Q2Certificate.correctedLength,
      Li2Lean.V.Q2Certificate.scaleLength,
      Li2Lean.V.Q2Certificate.scaleMass, IK.val, qadd, qsub, qneg, qmul, U]
  · change ∀ c ∈ v13ChainCells q5D.zp, c.left ≤ c.right ∧ 0 ≤ c.density
    norm_num [q5D, mkIData, v13ChainCells, v13ChainCellsAux, chainCP,
      V.EnergyCertI.q5ZHeader, V.EnergyCertI.q5ZEntries, chainCoords, chainMassU,
      densI, jumpsI,
      Li2Lean.V.Q2Certificate.decodeChain,
      Li2Lean.V.Q2Certificate.decodeChainAux,
      Li2Lean.V.Q2Certificate.correctedLength,
      Li2Lean.V.Q2Certificate.scaleLength,
      Li2Lean.V.Q2Certificate.scaleMass, IK.val, qadd, qsub, qneg, qmul, U]
  · change ∀ p ∈ q5D.xp, 0 ≤ p.e.1 ∧ 0 < p.e.2 ∧ 0 < p.J.2
    norm_num [q5D, mkIData, chainCP, V.EnergyCertI.q5XHeader,
      V.EnergyCertI.q5XEntries, chainCoords, chainMassU, densI, jumpsI,
      Li2Lean.V.Q2Certificate.decodeChain,
      Li2Lean.V.Q2Certificate.decodeChainAux,
      Li2Lean.V.Q2Certificate.correctedLength,
      Li2Lean.V.Q2Certificate.scaleLength,
      Li2Lean.V.Q2Certificate.scaleMass, IK.val, qadd, qsub, qneg, qmul, U]
  · change ∀ p ∈ q5D.vp, 0 ≤ p.e.1 ∧ 0 < p.e.2 ∧ 0 < p.J.2
    norm_num [q5D, mkIData, chainCP, V.EnergyCertI.q5YHeader,
      V.EnergyCertI.q5YEntries, chainCoords, chainMassU, densI, jumpsI,
      Li2Lean.V.Q2Certificate.decodeChain,
      Li2Lean.V.Q2Certificate.decodeChainAux,
      Li2Lean.V.Q2Certificate.correctedLength,
      Li2Lean.V.Q2Certificate.scaleLength,
      Li2Lean.V.Q2Certificate.scaleMass, IK.val, qadd, qsub, qneg, qmul, U]
  · change ∀ p ∈ q5D.zp, 0 < p.e.2 ∧ 0 < p.J.2
    norm_num [q5D, mkIData, chainCP, V.EnergyCertI.q5ZHeader,
      V.EnergyCertI.q5ZEntries, chainCoords, chainMassU, densI, jumpsI,
      Li2Lean.V.Q2Certificate.decodeChain,
      Li2Lean.V.Q2Certificate.decodeChainAux,
      Li2Lean.V.Q2Certificate.correctedLength,
      Li2Lean.V.Q2Certificate.scaleLength,
      Li2Lean.V.Q2Certificate.scaleMass, IK.val, qadd, qsub, qneg, qmul, U]
  · change (q5D.xp.map fun p => IK.val p.J).sum = 0
    norm_num [q5D, mkIData, chainCP, V.EnergyCertI.q5XHeader,
      V.EnergyCertI.q5XEntries, chainCoords, chainMassU, densI, jumpsI,
      Li2Lean.V.Q2Certificate.decodeChain,
      Li2Lean.V.Q2Certificate.decodeChainAux,
      Li2Lean.V.Q2Certificate.correctedLength,
      Li2Lean.V.Q2Certificate.scaleLength,
      Li2Lean.V.Q2Certificate.scaleMass, IK.val, qadd, qsub, qneg, qmul, U]
  · change (q5D.vp.map fun p => IK.val p.J).sum = 0
    norm_num [q5D, mkIData, chainCP, V.EnergyCertI.q5YHeader,
      V.EnergyCertI.q5YEntries, chainCoords, chainMassU, densI, jumpsI,
      Li2Lean.V.Q2Certificate.decodeChain,
      Li2Lean.V.Q2Certificate.decodeChainAux,
      Li2Lean.V.Q2Certificate.correctedLength,
      Li2Lean.V.Q2Certificate.scaleLength,
      Li2Lean.V.Q2Certificate.scaleMass, IK.val, qadd, qsub, qneg, qmul, U]
  · change (q5D.zp.map fun p => IK.val p.J).sum = 0
    norm_num [q5D, mkIData, chainCP, V.EnergyCertI.q5ZHeader,
      V.EnergyCertI.q5ZEntries, chainCoords, chainMassU, densI, jumpsI,
      Li2Lean.V.Q2Certificate.decodeChain,
      Li2Lean.V.Q2Certificate.decodeChainAux,
      Li2Lean.V.Q2Certificate.correctedLength,
      Li2Lean.V.Q2Certificate.scaleLength,
      Li2Lean.V.Q2Certificate.scaleMass, IK.val, qadd, qsub, qneg, qmul, U]
  · decide +kernel
  · decide +kernel

/-! ## 3. Per-q instances at the leaf row sources

Row sources (must match the leaf templates):
q2 `q2ReferenceRows`, q3 `q3DecodedReferenceRows`, q4 `q4DecodedRows`,
q5 `q5DecodedReferenceRows`, q6 `q6DecodedReferenceRows`, q7 `q7ReferenceRows`.

q4 row bounds `q4_decoded_row_bounds_leaf` and `q4ReferenceNormalization_of_hq`
live in `ReferencePackageLeafQ4.lean` itself, so the q4 instances take the
row bounds as an argument (pass `q4_decoded_row_bounds_leaf` in the leaf) and
inline the normalization transport. -/

/-! ### Normalizations at an arbitrary `hq` (proof irrelevance). -/

theorem q4ReferenceNormalization_s5 (hq : SignedVBaseRange 4) :
    V13MeasureNormalization hq (v13RefRaw q4DecodedRows) :=
  q4ReferenceNormalization   -- same transport as `q4ReferenceNormalization_of_hq`

theorem q5ReferenceNormalization_s5 (hq : SignedVBaseRange 5) :
    V13MeasureNormalization hq (v13RefRaw q5DecodedReferenceRows) :=
  q5ReferenceNormalization   -- goal is stated at `q5RawReferenceMeasures`

theorem q6ReferenceNormalization_s5 (hq : SignedVBaseRange 6) :
    V13MeasureNormalization hq (v13RefRaw q6DecodedReferenceRows) :=
  q6_normalization_leaf

theorem q7ReferenceNormalization_s5 (hq : SignedVBaseRange 7) :
    V13MeasureNormalization hq (v13RefRaw q7ReferenceRows) :=
  q7_normalization_leaf

/-! ### dual_admissible per q -/

theorem q2_s5_dual_admissible (hq : SignedVBaseRange 2) :
    SignedVReferenceIntegrable
      (v13RefMeasure q2ReferenceRows (q2ReferenceNormalization_of_hq hq)) :=
  v13_s5_dual_admissible q2ReferenceRows q2_decoded_row_bounds_leaf _

theorem q3_s5_dual_admissible (hq : SignedVBaseRange 3) :
    SignedVReferenceIntegrable
      (v13RefMeasure q3DecodedReferenceRows
        (q3ReferenceNormalization_reference_of_hq hq)) :=
  v13_s5_dual_admissible q3DecodedReferenceRows q3_decoded_row_bounds_reference _

theorem q4_s5_dual_admissible (hq : SignedVBaseRange 4)
    (rows : V13DecodedRowBounds 4 q4DecodedRows) :
    SignedVReferenceIntegrable
      (v13RefMeasure q4DecodedRows (q4ReferenceNormalization_s5 hq)) :=
  v13_s5_dual_admissible q4DecodedRows rows _

theorem q5_s5_dual_admissible (hq : SignedVBaseRange 5) :
    SignedVReferenceIntegrable
      (v13RefMeasure q5DecodedReferenceRows (q5ReferenceNormalization_s5 hq)) :=
  v13_s5_dual_admissible q5DecodedReferenceRows q5_decoded_row_bounds_template _

theorem q6_s5_dual_admissible (hq : SignedVBaseRange 6) :
    SignedVReferenceIntegrable
      (v13RefMeasure q6DecodedReferenceRows (q6ReferenceNormalization_s5 hq)) :=
  v13_s5_dual_admissible q6DecodedReferenceRows q6_decoded_row_bounds_template _

theorem q7_s5_dual_admissible (hq : SignedVBaseRange 7) :
    SignedVReferenceIntegrable
      (v13RefMeasure q7ReferenceRows (q7ReferenceNormalization_s5 hq)) :=
  v13_s5_dual_admissible q7ReferenceRows q7_decoded_row_bounds_leaf _

/-! ### Total facts per q (any plan; the leaves use `planOf R.data q`,
`q2EnergyPlan`, `q5EnergyPlan`, `q6EnergyPlan`, `q7EnergyPlan`). -/

theorem q2_s5_total (hq : SignedVBaseRange 2)
    (plan : List (EKind × Nat × Nat × Int)) :
    EnergyTotalSoundnessFact
      (v13RefMeasure q2ReferenceRows (q2ReferenceNormalization_of_hq hq))
      q2ReferenceRows.data plan (vEnergyTerm 2 q2ReferenceRows.data) :=
  v13_s5_total_fact q2ReferenceRows q2_field_row_facts
    q2_decoded_row_bounds_leaf _ plan

theorem q3_s5_total (hq : SignedVBaseRange 3)
    (plan : List (EKind × Nat × Nat × Int)) :
    EnergyTotalSoundnessFact
      (v13RefMeasure q3DecodedReferenceRows
        (q3ReferenceNormalization_reference_of_hq hq))
      q3DecodedReferenceRows.data plan
      (vEnergyTerm 3 q3DecodedReferenceRows.data) :=
  v13_s5_total_fact q3DecodedReferenceRows q3_field_row_facts_reference
    q3_decoded_row_bounds_reference _ plan
  -- the q3 template states `total` with `q3D` in place of
  -- `q3DecodedReferenceRows.data`; both reduce to `q3D` (`exact` / `simpa`).

theorem q4_s5_total (hq : SignedVBaseRange 4)
    (rows : V13DecodedRowBounds 4 q4DecodedRows)
    (plan : List (EKind × Nat × Nat × Int)) :
    EnergyTotalSoundnessFact
      (v13RefMeasure q4DecodedRows (q4ReferenceNormalization_s5 hq))
      q4DecodedRows.data plan (vEnergyTerm 4 q4DecodedRows.data) :=
  v13_s5_total_fact q4DecodedRows q4_field_row_facts rows _ plan

theorem q5_s5_total (hq : SignedVBaseRange 5)
    (plan : List (EKind × Nat × Nat × Int)) :
    EnergyTotalSoundnessFact
      (v13RefMeasure q5DecodedReferenceRows (q5ReferenceNormalization_s5 hq))
      q5DecodedReferenceRows.data plan
      (vEnergyTerm 5 q5DecodedReferenceRows.data) :=
  v13_s5_total_fact q5DecodedReferenceRows q5_field_row_facts
    q5_decoded_row_bounds_template _ plan

theorem q6_s5_total (hq : SignedVBaseRange 6)
    (plan : List (EKind × Nat × Nat × Int)) :
    EnergyTotalSoundnessFact
      (v13RefMeasure q6DecodedReferenceRows (q6ReferenceNormalization_s5 hq))
      q6DecodedReferenceRows.data plan
      (vEnergyTerm 6 q6DecodedReferenceRows.data) :=
  v13_s5_total_fact q6DecodedReferenceRows q6_field_row_facts
    q6_decoded_row_bounds_template _ plan

theorem q7_s5_total (hq : SignedVBaseRange 7)
    (plan : List (EKind × Nat × Nat × Int)) :
    EnergyTotalSoundnessFact
      (v13RefMeasure q7ReferenceRows (q7ReferenceNormalization_s5 hq))
      q7ReferenceRows.data plan (vEnergyTerm 7 q7ReferenceRows.data) :=
  v13_s5_total_fact q7ReferenceRows q7_field_row_facts
    q7_decoded_row_bounds_leaf _ plan

/-! ### Numeric certificates per q (ball, sigma, dual, and explicit field inputs). -/

noncomputable def q2_s5_numeric_certificates (hq : SignedVBaseRange 2)
    (energy_lower : ((vQlow 2 : ℚ) : ℝ) < V.signedVQuadratic
      (v13RefMeasure q2ReferenceRows (q2ReferenceNormalization_of_hq hq)))
    (x_field : ∀ t : ℝ, t ∈ Set.Ioc (0 : ℝ) 1 → V.signedVFullFieldX
      (v13RefMeasure q2ReferenceRows (q2ReferenceNormalization_of_hq hq)) (t : ℂ) <
        (vKx 2 : ℝ))
    (v_field : ∀ t : ℝ, t ∈ Set.Ioc (0 : ℝ) 1 → V.signedVFullFieldV
      (v13RefMeasure q2ReferenceRows (q2ReferenceNormalization_of_hq hq)) (t : ℂ) <
        (vKv 2 : ℝ))
    (z_field : ∀ w ∈ V.vContourTrace 2, V.signedVFullFieldZ
      (v13RefMeasure q2ReferenceRows (q2ReferenceNormalization_of_hq hq)) w <
        (vKz 2 : ℝ))
    (x_disk : ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ ≤ 1 / 250 → V.signedVFullFieldX
      (v13RefMeasure q2ReferenceRows (q2ReferenceNormalization_of_hq hq)) w ≤
        (vEx 2 : ℝ))
    (v_disk : ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ ≤ 1 / 250 → V.signedVFullFieldV
      (v13RefMeasure q2ReferenceRows (q2ReferenceNormalization_of_hq hq)) w ≤
        (vEv 2 : ℝ)) :
    V13NumericCertificates 2 hq q2ReferenceRows :=
  v13NumericCertificates_of_s5 q2ReferenceRows q2_decoded_row_bounds_leaf
    (q2ReferenceNormalization_of_hq hq) energy_lower x_field v_field z_field
    v13_alpha_le_q2 x_disk v_disk   -- as in the master q6 template (F6Alpha)

/-- q3: same as q2 with `q3DecodedReferenceRows`. -/
noncomputable def q3_s5_numeric_certificates (hq : SignedVBaseRange 3)
    (energy_lower : ((vQlow 3 : ℚ) : ℝ) < V.signedVQuadratic
      (v13RefMeasure q3DecodedReferenceRows (q3ReferenceNormalization_reference_of_hq hq)))
    (x_field : ∀ t : ℝ, t ∈ Set.Ioc (0 : ℝ) 1 → V.signedVFullFieldX
      (v13RefMeasure q3DecodedReferenceRows
        (q3ReferenceNormalization_reference_of_hq hq)) (t : ℂ) < (vKx 3 : ℝ))
    (v_field : ∀ t : ℝ, t ∈ Set.Ioc (0 : ℝ) 1 → V.signedVFullFieldV
      (v13RefMeasure q3DecodedReferenceRows
        (q3ReferenceNormalization_reference_of_hq hq)) (t : ℂ) < (vKv 3 : ℝ))
    (z_field : ∀ w ∈ V.vContourTrace 3, V.signedVFullFieldZ
      (v13RefMeasure q3DecodedReferenceRows
        (q3ReferenceNormalization_reference_of_hq hq)) w < (vKz 3 : ℝ))
    (x_disk : ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ ≤ 1 / 250 → V.signedVFullFieldX
      (v13RefMeasure q3DecodedReferenceRows
        (q3ReferenceNormalization_reference_of_hq hq)) w ≤ (vEx 3 : ℝ))
    (v_disk : ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ ≤ 1 / 250 → V.signedVFullFieldV
      (v13RefMeasure q3DecodedReferenceRows
        (q3ReferenceNormalization_reference_of_hq hq)) w ≤ (vEv 3 : ℝ)) :
    V13NumericCertificates 3 hq q3DecodedReferenceRows :=
  v13NumericCertificates_of_s5 q3DecodedReferenceRows q3_decoded_row_bounds_reference
    (q3ReferenceNormalization_reference_of_hq hq) energy_lower x_field v_field z_field
    v13_alpha_le_q3 x_disk v_disk   -- as in the master q6 template (F6Alpha)

/-- q4: rows are an argument (`q4_decoded_row_bounds_leaf`, defined in LeafQ4). -/
noncomputable def q4_s5_numeric_certificates (hq : SignedVBaseRange 4)
    (rows : V13DecodedRowBounds 4 q4DecodedRows)
    (energy_lower : ((vQlow 4 : ℚ) : ℝ) < V.signedVQuadratic
      (v13RefMeasure q4DecodedRows (q4ReferenceNormalization_s5 hq)))
    (x_field : ∀ t : ℝ, t ∈ Set.Ioc (0 : ℝ) 1 → V.signedVFullFieldX
      (v13RefMeasure q4DecodedRows (q4ReferenceNormalization_s5 hq)) (t : ℂ) <
        (vKx 4 : ℝ))
    (v_field : ∀ t : ℝ, t ∈ Set.Ioc (0 : ℝ) 1 → V.signedVFullFieldV
      (v13RefMeasure q4DecodedRows (q4ReferenceNormalization_s5 hq)) (t : ℂ) <
        (vKv 4 : ℝ))
    (z_field : ∀ w ∈ V.vContourTrace 4, V.signedVFullFieldZ
      (v13RefMeasure q4DecodedRows (q4ReferenceNormalization_s5 hq)) w <
        (vKz 4 : ℝ))
    (x_disk : ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ ≤ 1 / 250 → V.signedVFullFieldX
      (v13RefMeasure q4DecodedRows (q4ReferenceNormalization_s5 hq)) w ≤
        (vEx 4 : ℝ))
    (v_disk : ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ ≤ 1 / 250 → V.signedVFullFieldV
      (v13RefMeasure q4DecodedRows (q4ReferenceNormalization_s5 hq)) w ≤
        (vEv 4 : ℝ)) :
    V13NumericCertificates 4 hq q4DecodedRows :=
  v13NumericCertificates_of_s5 q4DecodedRows rows
    (q4ReferenceNormalization_s5 hq) energy_lower x_field v_field z_field
    v13_alpha_le_q4 x_disk v_disk   -- as in the master q6 template (F6Alpha)
  -- x_disk in the release: `q4_x_endpoint_disk_of_hq` (LeafQ4:110) at
  -- `q4ReferenceNormalization_of_hq hq`, defeq to `q4ReferenceNormalization_s5 hq`.

noncomputable def q5_s5_numeric_certificates (hq : SignedVBaseRange 5)
    (energy_lower : ((vQlow 5 : ℚ) : ℝ) < V.signedVQuadratic
      (v13RefMeasure q5DecodedReferenceRows (q5ReferenceNormalization_s5 hq)))
    (x_field : ∀ t : ℝ, t ∈ Set.Ioc (0 : ℝ) 1 → V.signedVFullFieldX
      (v13RefMeasure q5DecodedReferenceRows (q5ReferenceNormalization_s5 hq)) (t : ℂ) <
        (vKx 5 : ℝ))
    (v_field : ∀ t : ℝ, t ∈ Set.Ioc (0 : ℝ) 1 → V.signedVFullFieldV
      (v13RefMeasure q5DecodedReferenceRows (q5ReferenceNormalization_s5 hq)) (t : ℂ) <
        (vKv 5 : ℝ))
    (z_field : ∀ w ∈ V.vContourTrace 5, V.signedVFullFieldZ
      (v13RefMeasure q5DecodedReferenceRows (q5ReferenceNormalization_s5 hq)) w <
        (vKz 5 : ℝ))
    (x_disk : ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ ≤ 1 / 250 → V.signedVFullFieldX
      (v13RefMeasure q5DecodedReferenceRows (q5ReferenceNormalization_s5 hq)) w ≤
        (vEx 5 : ℝ))
    (v_disk : ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ ≤ 1 / 250 → V.signedVFullFieldV
      (v13RefMeasure q5DecodedReferenceRows (q5ReferenceNormalization_s5 hq)) w ≤
        (vEv 5 : ℝ)) :
    V13NumericCertificates 5 hq q5DecodedReferenceRows :=
  v13NumericCertificates_of_s5 q5DecodedReferenceRows q5_decoded_row_bounds_template
    (q5ReferenceNormalization_s5 hq) energy_lower x_field v_field z_field
    v13_alpha_le_q5 x_disk v_disk   -- as in the master q6 template (F6Alpha)

noncomputable def q6_s5_numeric_certificates (hq : SignedVBaseRange 6)
    (energy_lower : ((vQlow 6 : ℚ) : ℝ) < V.signedVQuadratic
      (v13RefMeasure q6DecodedReferenceRows (q6ReferenceNormalization_s5 hq)))
    (x_field : ∀ t : ℝ, t ∈ Set.Ioc (0 : ℝ) 1 → V.signedVFullFieldX
      (v13RefMeasure q6DecodedReferenceRows (q6ReferenceNormalization_s5 hq)) (t : ℂ) <
        (vKx 6 : ℝ))
    (v_field : ∀ t : ℝ, t ∈ Set.Ioc (0 : ℝ) 1 → V.signedVFullFieldV
      (v13RefMeasure q6DecodedReferenceRows (q6ReferenceNormalization_s5 hq)) (t : ℂ) <
        (vKv 6 : ℝ))
    (z_field : ∀ w ∈ V.vContourTrace 6, V.signedVFullFieldZ
      (v13RefMeasure q6DecodedReferenceRows (q6ReferenceNormalization_s5 hq)) w <
        (vKz 6 : ℝ))
    (x_disk : ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ ≤ 1 / 250 → V.signedVFullFieldX
      (v13RefMeasure q6DecodedReferenceRows (q6ReferenceNormalization_s5 hq)) w ≤
        (vEx 6 : ℝ))
    (v_disk : ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ ≤ 1 / 250 → V.signedVFullFieldV
      (v13RefMeasure q6DecodedReferenceRows (q6ReferenceNormalization_s5 hq)) w ≤
        (vEv 6 : ℝ)) :
    V13NumericCertificates 6 hq q6DecodedReferenceRows :=
  v13NumericCertificates_of_s5 q6DecodedReferenceRows q6_decoded_row_bounds_template
    (q6ReferenceNormalization_s5 hq) energy_lower x_field v_field z_field
    v13_alpha_le_q6 x_disk v_disk

noncomputable def q7_s5_numeric_certificates (hq : SignedVBaseRange 7)
    (energy_lower : ((vQlow 7 : ℚ) : ℝ) < V.signedVQuadratic
      (v13RefMeasure q7ReferenceRows (q7ReferenceNormalization_s5 hq)))
    (x_field : ∀ t : ℝ, t ∈ Set.Ioc (0 : ℝ) 1 → V.signedVFullFieldX
      (v13RefMeasure q7ReferenceRows (q7ReferenceNormalization_s5 hq)) (t : ℂ) <
        (vKx 7 : ℝ))
    (v_field : ∀ t : ℝ, t ∈ Set.Ioc (0 : ℝ) 1 → V.signedVFullFieldV
      (v13RefMeasure q7ReferenceRows (q7ReferenceNormalization_s5 hq)) (t : ℂ) <
        (vKv 7 : ℝ))
    (z_field : ∀ w ∈ V.vContourTrace 7, V.signedVFullFieldZ
      (v13RefMeasure q7ReferenceRows (q7ReferenceNormalization_s5 hq)) w <
        (vKz 7 : ℝ))
    (x_disk : ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ ≤ 1 / 250 → V.signedVFullFieldX
      (v13RefMeasure q7ReferenceRows (q7ReferenceNormalization_s5 hq)) w ≤
        (vEx 7 : ℝ))
    (v_disk : ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ ≤ 1 / 250 → V.signedVFullFieldV
      (v13RefMeasure q7ReferenceRows (q7ReferenceNormalization_s5 hq)) w ≤
        (vEv 7 : ℝ)) :
    V13NumericCertificates 7 hq q7ReferenceRows :=
  v13NumericCertificates_of_s5 q7ReferenceRows q7_decoded_row_bounds_leaf
    (q7ReferenceNormalization_s5 hq) energy_lower x_field v_field z_field
    v13_alpha_le_q7 x_disk v_disk   -- as in the master q6 template (F6Alpha)

/-! ## 4. How a leaf uses this module (no assembly here; see H6Q4Closure)

```
-- inside v13_reference_package_input_qN_closed hq:
let N    := qNReferenceNormalization_s5 hq          -- (q2: q2ReferenceNormalization_of_hq hq)
have T   := qN_s5_total hq PLAN                     -- PLAN = planOf R.data N / qNEnergyPlan
have EL  := qN_energy_lower_of_shard_and_total ... ENERGY T   -- existing bridges
let C    := qN_s5_numeric_certificates hq EL XF VF ZF XD VD
exact <template> C lr lr_sound FIELD_x .. FIELD_zpos ENERGY T
```
`T` is stated at `v13RefMeasure R N`; the template asks for it at
`v13RefMeasure R C.normalization`, which reduces to `N`
(`v13NumericCertificates_of_s5_normalization`, `rfl`). -/

end

end Li2Lean.B3

#print axioms Li2Lean.B3.v13_s5_dual_admissible
#print axioms Li2Lean.B3.v13_s5_total_fact
#print axioms Li2Lean.B3.v13NumericCertificates_of_s5
#print axioms Li2Lean.B3.q2_field_row_facts
#print axioms Li2Lean.B3.q5_field_row_facts
