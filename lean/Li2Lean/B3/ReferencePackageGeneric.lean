/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Generic construction of the signed-V reference package from one decoded row
source.  The row bounds are the finite decoder checks; the remaining fields
are explicit numerical and analytic certificates.  This module performs only
the common assembly from v13 `v-reference-data.tex:1-430` and
`v-analytic.tex:339-491`.
-/

import Li2Lean.B3.ReferencePackageProducer
import Li2Lean.B3.ReferenceMeasureAtomless
import Li2Lean.B3.ReferenceMeasureSupportCircle
import Li2Lean.B3.EnergySoundnessMeasureFacts

namespace Li2Lean

noncomputable section

namespace B3

open MeasureTheory Set
open V

/-! The only q-specific row obligations needed by the common support proof. -/

structure V13DecodedRowBounds (q : ℕ) (D : V13DecodedRows q) where
  x_low : ∀ c ∈ v13ChainCells D.data.xp,
    vXLow q ≤ c.left ∧ c.right ≤ 1
  x_full : ∀ c ∈ v13ChainCells D.data.xp,
    0 ≤ c.left ∧ c.right ≤ 1
  v_low : ∀ c ∈ v13ChainCells D.data.vp,
    vVLow q ≤ c.left ∧ c.right ≤ 1
  v_full : ∀ c ∈ v13ChainCells D.data.vp,
    0 ≤ c.left ∧ c.right ≤ 1
  z_source : ∀ c ∈ v13ChainCells D.data.zp,
    (-(q : ℝ)) ≤ c.left ∧ c.right ≤ -(3 / 5 : ℝ)

/-! Numeric and analytic certificates for one fixed decoded source.  The
normalization and all evaluator fields remain inputs: no field below is
manufactured from a row count or from a q case split. -/

structure V13NumericCertificates (q : ℕ) (hq : SignedVBaseRange q)
    (D : V13DecodedRows q) where
  rows : V13DecodedRowBounds q D
  normalization : V13MeasureNormalization hq (v13RefRaw D)
  Ax : ℝ
  Av : ℝ
  Az : ℝ
  Ax_nonneg : 0 ≤ Ax
  Av_nonneg : 0 ≤ Av
  Az_nonneg : 0 ≤ Az
  x_ball : VBallBound (v13RefMeasure D normalization).μx Ax
  v_ball : VBallBound (v13RefMeasure D normalization).μv Av
  z_ball : VBallBound (v13RefMeasure D normalization).μz Az
  sigma_eq : vSigma q = sigmaBudget Ax Av Az
  energy_lower : ((vQlow q : ℚ) : ℝ) <
    V.signedVQuadratic (v13RefMeasure D normalization)
  x_field : ∀ t : ℝ, t ∈ Set.Ioc (0 : ℝ) 1 →
    V.signedVFullFieldX (v13RefMeasure D normalization) (t : ℂ) <
      (vKx q : ℝ)
  v_field : ∀ t : ℝ, t ∈ Set.Ioc (0 : ℝ) 1 →
    V.signedVFullFieldV (v13RefMeasure D normalization) (t : ℂ) <
      (vKv q : ℝ)
  z_field : ∀ w ∈ V.vContourTrace q,
    V.signedVFullFieldZ (v13RefMeasure D normalization) w < (vKz q : ℝ)
  alpha_le : vAlpha q ≤ (vQlow q : ℝ) - 3 / 2 * Real.log q -
    (vKx q : ℝ) - 5 / 4 * (vKv q : ℝ) - (vKz q : ℝ)
  x_endpoint_disk : ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ ≤ 1 / 250 →
    V.signedVFullFieldX (v13RefMeasure D normalization) w ≤ (vEx q : ℝ)
  v_endpoint_disk : ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ ≤ 1 / 250 →
    V.signedVFullFieldV (v13RefMeasure D normalization) w ≤ (vEv q : ℝ)
  dual_admissible :
    SignedVReferenceIntegrable (v13RefMeasure D normalization)

/-! Common constructor.  The support and atomless clauses are proved once
from the decoded-row bounds and the generic measure lemmas. -/

noncomputable def vReferencePackage_of_rows
    {q : ℕ} {hq : SignedVBaseRange q}
    (D : V13DecodedRows q)
    (C : V13NumericCertificates q hq D) : VReferencePackage q hq := by
  let ν : V.SignedVMeasures := v13RefMeasure D C.normalization
  have hs := v13RefMeasure_supports_of_bounds D C.normalization
    (vXLow q) (vVLow q) C.rows.x_low C.rows.x_full
    C.rows.v_low C.rows.v_full C.rows.z_source
  have ha := v13RefMeasure_atomless D C.normalization
  refine {
    measure := ν
    Ax := C.Ax
    Av := C.Av
    Az := C.Az
    facts := ?_ }
  refine {
    q_eq := ?_
    x_support_low := ?_
    v_support_low := ?_
    z_support_source := ?_
    x_support := ?_
    v_support := ?_
    z_support := ?_
    x_atomless := ?_
    v_atomless := ?_
    z_atomless := ?_
    Ax_nonneg := C.Ax_nonneg
    Av_nonneg := C.Av_nonneg
    Az_nonneg := C.Az_nonneg
    x_ball := C.x_ball
    v_ball := C.v_ball
    z_ball := C.z_ball
    sigma_eq := C.sigma_eq
    energy_lower := C.energy_lower
    x_field := C.x_field
    v_field := C.v_field
    z_field := C.z_field
    alpha_le := C.alpha_le
    x_endpoint_disk := C.x_endpoint_disk
    v_endpoint_disk := C.v_endpoint_disk
    dual_admissible := C.dual_admissible }
  · rfl
  · exact hs.1
  · exact hs.2.1
  · exact hs.2.2.1
  · exact hs.2.2.2.1
  · exact hs.2.2.2.2.1
  · exact hs.2.2.2.2.2
  · exact ha.1
  · exact ha.2.1
  · exact ha.2.2

/-! The ledger-level adapter keeps qlow, cell/shard, and total soundness
explicit while reusing the same package constructor. -/

noncomputable def v13ReferencePackageInput_of_rows
    {q : ℕ} {hq : SignedVBaseRange q}
    (D : V13DecodedRows q)
    (C : V13NumericCertificates q hq D)
    (lr : V.EnergyCertI.IK.IV)
    (lr_sound : V.EnergyCertI.IK.IV.mem lr (Real.log (3 / 5 : ℝ)))
    (plan : List (V.EnergyCertI.EKind × ℕ × ℕ × Int))
    (term : V.EnergyCertI.EKind → ℕ → ℝ)
    (qlow_value : V.EnergyCertI.IK.val (V.EnergyCertI.qlowQ q) =
      (vQlow q : ℝ))
    (field_x : CellSoundnessOn (pieceDomain q .x).1 (pieceDomain q .x).2
      (V.EnergyCertI.fieldUB D.data q lr .x)
      (fun t => V.signedVFullFieldX
        (v13RefMeasure D C.normalization) (t : ℂ)))
    (field_vlo : CellSoundnessOn (pieceDomain q .vlo).1 (pieceDomain q .vlo).2
      (V.EnergyCertI.fieldUB D.data q lr .vlo)
      (fun t => V.signedVFullFieldV
        (v13RefMeasure D C.normalization) (t : ℂ)))
    (field_vhi : CellSoundnessOn (pieceDomain q .vhi).1 (pieceDomain q .vhi).2
      (V.EnergyCertI.fieldUB D.data q lr .vhi)
      (fun t => V.signedVFullFieldV
        (v13RefMeasure D C.normalization) (t : ℂ)))
    (field_zneg : CellSoundnessOn (pieceDomain q .zneg).1 (pieceDomain q .zneg).2
      (V.EnergyCertI.fieldUB D.data q lr .zneg)
      (fun t => V.signedVFullFieldZ
        (v13RefMeasure D C.normalization) (t : ℂ)))
    (field_zpos : CellSoundnessOn (pieceDomain q .zpos).1 (pieceDomain q .zpos).2
      (V.EnergyCertI.fieldUB D.data q lr .zpos)
      (fun t => V.signedVFullFieldZ
        (v13RefMeasure D C.normalization) (t : ℂ)))
    (energy : EnergyShardSoundnessFact D.data q lr plan term)
    (total : EnergyTotalSoundnessFact
      (v13RefMeasure D C.normalization) D.data plan term) :
    V13ReferencePackageInput q hq := by
  let P : VReferencePackage q hq := vReferencePackage_of_rows D C
  refine ⟨⟨P, D, lr, lr_sound, plan, term, qlow_value,
    field_x, field_vlo, field_vhi, field_zneg, field_zpos, energy, ?_⟩⟩
  have hP : P.measure = v13RefMeasure D C.normalization := by
    rfl
  rw [hP]
  exact total

/-! The G3 binding keeps the cell, shard, and total witnesses attached to the
same decoded source and reference measure.  It only projects the existing
certificate interfaces; the witnesses remain explicit construction inputs.
This is the common binding used by the q-specific ledgers in
`v13/v-analytic.tex:339-491`. -/
noncomputable def v13ReferencePackageInput_of_soundness
    {q : ℕ} {hq : SignedVBaseRange q}
    (D : V13DecodedRows q)
    (C : V13NumericCertificates q hq D)
    (lr : V.EnergyCertI.IK.IV)
    (lr_sound : V.EnergyCertI.IK.IV.mem lr (Real.log (3 / 5 : ℝ)))
    (plan : List (V.EnergyCertI.EKind × ℕ × ℕ × Int))
    (term : V.EnergyCertI.EKind → ℕ → ℝ)
    (qlow_value : V.EnergyCertI.IK.val (V.EnergyCertI.qlowQ q) =
      (vQlow q : ℝ))
    (fields : VFieldCellSoundness D.data q lr
      (v13RefMeasure D C.normalization))
    (shards : EnergyShardSoundness D.data q lr plan term)
    (total : SignedQuadraticTotalIdentity
      (v13RefMeasure D C.normalization) D.data plan term) :
    V13ReferencePackageInput q hq := by
  rcases fieldUB_sound_on fields with ⟨field_x, field_vlo, field_vhi,
    field_zneg, field_zpos⟩
  exact v13ReferencePackageInput_of_rows D C lr lr_sound plan term qlow_value
    field_x field_vlo field_vhi field_zneg field_zpos
    shards.toFact total.toFact

end B3

end

end Li2Lean

#print axioms Li2Lean.B3.vReferencePackage_of_rows
#print axioms Li2Lean.B3.v13ReferencePackageInput_of_rows
