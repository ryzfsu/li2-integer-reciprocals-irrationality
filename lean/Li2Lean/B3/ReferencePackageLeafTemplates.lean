/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B3.ReferencePackageGeneric
import Li2Lean.B3.ReferencePackagePinnedAdapter
import Li2Lean.B3.Q2ReferencePackageFacts
import Li2Lean.B3.Q6ReferenceMeasureFacts
import Li2Lean.B3.Q6ReferenceSupportLow
import Li2Lean.B3.ReferenceDualIntegrable
import Li2Lean.B3.Q7ReferenceMeasureFacts
import Li2Lean.B3.Q7ReferenceNormalization
import Li2Lean.B3.F6Alpha
import Li2Lean.B3.V13ReferenceEnergyTerm
import Li2Lean.V.EnergyCertI.Q2Assembly
import Li2Lean.V.EnergyCertI.Q6Assembly
import Li2Lean.V.EnergyCertI.Q7Assembly

/-!
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 License.

Shared lower-layer templates for the q-indexed reference-package leaves.
This module contains only finite row facts and construction-bound adapters;
the public leaves and q-specific closure files depend on it.
-/

namespace Li2Lean.B3

noncomputable section

open V
open V.EnergyCertI
open V.EnergyCertI.IK
theorem q2_decoded_row_bounds_leaf :
    V13DecodedRowBounds 2 q2ReferenceRows := by
  refine {
    x_low := ?_
    x_full := ?_
    v_low := ?_
    v_full := ?_
    z_source := ?_ }
  · intro c hc
    have h := v13_q2_x_bounds c hc
    have hlow : (vXLow 2 : ℝ) = (3349365000000 : ℝ) / (5 * 10 ^ 13) := by
      norm_num [vXLow]
    simpa [q2ReferenceRows_data, hlow] using h
  · intro c hc
    simpa [q2ReferenceRows_data] using v13_q2_x_full_bounds c hc
  · intro c hc
    have h := v13_q2_v_bounds c hc
    simpa [q2ReferenceRows_data, vVLow] using h
  · intro c hc
    simpa [q2ReferenceRows_data] using v13_q2_v_full_bounds c hc
  · intro c hc
    simpa [q2ReferenceRows_data] using v13_q2_z_source_bounds c hc

/-! A q2 ledger template with the v13 plan and term family fixed at the
decoded rows.  The remaining F/E/T witnesses are explicit arguments; this
definition cannot close the q2 leaf by manufacturing any of them. -/
noncomputable def v13_reference_package_input_q2_of_v13_certificates
    {hq : SignedVBaseRange 2}
    (C : V13NumericCertificates 2 hq q2ReferenceRows)
    (lr : V.EnergyCertI.IK.IV)
    (lr_sound : V.EnergyCertI.IK.IV.mem lr (Real.log (3 / 5 : ℝ)))
    (field_x : CellSoundnessFact q2ReferenceRows.data 2 lr
      (V.EnergyCertI.fieldUB q2ReferenceRows.data 2 lr .x)
      (V.EnergyCertI.kxQ 2)
      (fun t => V.signedVFullFieldX
        (v13RefMeasure q2ReferenceRows C.normalization) (t : ℂ)))
    (field_vlo : CellSoundnessFact q2ReferenceRows.data 2 lr
      (V.EnergyCertI.fieldUB q2ReferenceRows.data 2 lr .vlo)
      (V.EnergyCertI.kvQ 2)
      (fun t => V.signedVFullFieldV
        (v13RefMeasure q2ReferenceRows C.normalization) (t : ℂ)))
    (field_vhi : CellSoundnessFact q2ReferenceRows.data 2 lr
      (V.EnergyCertI.fieldUB q2ReferenceRows.data 2 lr .vhi)
      (V.EnergyCertI.kvQ 2)
      (fun t => V.signedVFullFieldV
        (v13RefMeasure q2ReferenceRows C.normalization) (t : ℂ)))
    (field_zneg : CellSoundnessFact q2ReferenceRows.data 2 lr
      (V.EnergyCertI.fieldUB q2ReferenceRows.data 2 lr .zneg)
      (V.EnergyCertI.kzQ 2)
      (fun t => V.signedVFullFieldZ
        (v13RefMeasure q2ReferenceRows C.normalization) (t : ℂ)))
    (field_zpos : CellSoundnessFact q2ReferenceRows.data 2 lr
      (V.EnergyCertI.fieldUB q2ReferenceRows.data 2 lr .zpos)
      (V.EnergyCertI.kzQ 2)
      (fun t => V.signedVFullFieldZ
        (v13RefMeasure q2ReferenceRows C.normalization) (t : ℂ)))
    (energy : EnergyShardSoundnessFact q2ReferenceRows.data 2 lr
      V.EnergyCertI.q2EnergyPlan
      (fun k i => vEnergyTerm 2 q2ReferenceRows.data k i))
    (total : EnergyTotalSoundnessFact
      (v13RefMeasure q2ReferenceRows C.normalization) q2ReferenceRows.data
      V.EnergyCertI.q2EnergyPlan
      (fun k i => vEnergyTerm 2 q2ReferenceRows.data k i)) :
    V13ReferencePackageInput 2 hq := by
  exact v13ReferencePackageInput_of_rows q2ReferenceRows C lr lr_sound
    V.EnergyCertI.q2EnergyPlan
    (fun k i => vEnergyTerm 2 q2ReferenceRows.data k i)
    q2ReferenceQLowValue field_x.toOn field_vlo.toOn field_vhi.toOn field_zneg.toOn
    field_zpos.toOn
    energy total
theorem q6_decoded_row_bounds_template :
    V13DecodedRowBounds 6 q6DecodedReferenceRows := by
  refine {
    x_low := ?_
    x_full := ?_
    v_low := ?_
    v_full := ?_
    z_source := ?_ }
  · intro c hc
    have h := v13_q6_x_bounds c (by simpa [q6DecodedReferenceRows] using hc)
    simpa [q6DecodedReferenceRows] using h
  · intro c hc
    have h := v13_q6_x_bounds c (by simpa [q6DecodedReferenceRows] using hc)
    constructor
    · have h0 : (0 : ℝ) ≤ vXLow 6 := by norm_num [vXLow]
      exact h0.trans h.1
    · exact h.2
  · intro c hc
    have h := v13_q6_v_bounds c (by simpa [q6DecodedReferenceRows] using hc)
    simpa [q6DecodedReferenceRows] using h
  · intro c hc
    have h := v13_q6_v_bounds c (by simpa [q6DecodedReferenceRows] using hc)
    constructor
    · have h0 : (0 : ℝ) ≤ vVLow 6 := by norm_num [vVLow]
      exact h0.trans h.1
    · exact h.2
  · intro c hc
    simpa [q6DecodedReferenceRows] using
      v13_q6_z_source_bounds c (by simpa [q6DecodedReferenceRows] using hc)

theorem q6ReferenceMeasure_qlow_value :
    IK.val (qlowQ 6) = (vQlow 6 : ℝ) := by
  norm_num [IK.val, qlowQ, vQlow]

theorem q6_normalization_leaf :
    V13MeasureNormalization q6ReferenceBaseRange
      (v13RefRaw q6DecodedReferenceRows) :=
  q6ReferenceNormalization

noncomputable def v13_reference_package_input_q6_template
    {hq : SignedVBaseRange 6}
    (C : V13NumericCertificates 6 hq q6DecodedReferenceRows)
    (lr : IV)
    (lr_sound : IV.mem lr (Real.log (3 / 5 : ℝ)))
    (field_x : CellSoundnessOn (pieceDomain 6 .x).1 (pieceDomain 6 .x).2
      (fieldUB q6DecodedReferenceRows.data 6 lr .x)
      (fun t => V.signedVFullFieldX
        (v13RefMeasure q6DecodedReferenceRows C.normalization) (t : ℂ)))
    (field_vlo : CellSoundnessOn (pieceDomain 6 .vlo).1 (pieceDomain 6 .vlo).2
      (fieldUB q6DecodedReferenceRows.data 6 lr .vlo)
      (fun t => V.signedVFullFieldV
        (v13RefMeasure q6DecodedReferenceRows C.normalization) (t : ℂ)))
    (field_vhi : CellSoundnessOn (pieceDomain 6 .vhi).1 (pieceDomain 6 .vhi).2
      (fieldUB q6DecodedReferenceRows.data 6 lr .vhi)
      (fun t => V.signedVFullFieldV
        (v13RefMeasure q6DecodedReferenceRows C.normalization) (t : ℂ)))
    (field_zneg : CellSoundnessOn (pieceDomain 6 .zneg).1 (pieceDomain 6 .zneg).2
      (fieldUB q6DecodedReferenceRows.data 6 lr .zneg)
      (fun t => V.signedVFullFieldZ
        (v13RefMeasure q6DecodedReferenceRows C.normalization) (t : ℂ)))
    (field_zpos : CellSoundnessOn (pieceDomain 6 .zpos).1 (pieceDomain 6 .zpos).2
      (fieldUB q6DecodedReferenceRows.data 6 lr .zpos)
      (fun t => V.signedVFullFieldZ
        (v13RefMeasure q6DecodedReferenceRows C.normalization) (t : ℂ)))
    (energy : EnergyShardSoundnessFact q6DecodedReferenceRows.data 6 lr
      q6EnergyPlan (vEnergyTerm 6 q6DecodedReferenceRows.data))
    (total : EnergyTotalSoundnessFact
      (v13RefMeasure q6DecodedReferenceRows C.normalization)
      q6DecodedReferenceRows.data q6EnergyPlan
      (vEnergyTerm 6 q6DecodedReferenceRows.data)) :
    V13ReferencePackageInput 6 hq := by
  exact v13ReferencePackageInput_of_rows q6DecodedReferenceRows C lr lr_sound
    q6EnergyPlan (vEnergyTerm 6 q6DecodedReferenceRows.data)
    q6ReferenceMeasure_qlow_value field_x field_vlo field_vhi field_zneg field_zpos
    energy total
/-! The concrete q7 decoder bounds used by the rows field of C. This finite -/
set_option maxHeartbeats 2000000 in
theorem q7_decoded_row_bounds_leaf :
    V13DecodedRowBounds 7 q7ReferenceRows := by
  refine {
    x_low := ?_
    x_full := ?_
    v_low := ?_
    v_full := ?_
    z_source := ?_ }
  · intro c hc
    have hc' : c ∈ v13ChainCells q7D.xp := by
      simpa only [q7ReferenceRows] using hc
    have h := v13_q7_x_bounds c hc'
    simpa [q7ReferenceRows, vXLow] using h
  · intro c hc
    have hc' : c ∈ v13ChainCells q7D.xp := by
      simpa only [q7ReferenceRows] using hc
    have h := v13_q7_x_bounds c hc'
    have hlow : (0 : ℝ) ≤ vXLow 7 := by norm_num [vXLow]
    exact ⟨hlow.trans (by simpa [q7ReferenceRows, vXLow] using h.1), h.2⟩
  · intro c hc
    have hc' : c ∈ v13ChainCells q7D.vp := by
      simpa only [q7ReferenceRows] using hc
    have h := v13_q7_v_bounds c hc'
    simpa [q7ReferenceRows, vVLow] using h
  · intro c hc
    have hc' : c ∈ v13ChainCells q7D.vp := by
      simpa only [q7ReferenceRows] using hc
    have h := v13_q7_v_bounds c hc'
    have hlow : (0 : ℝ) ≤ vVLow 7 := by norm_num [vVLow]
    exact ⟨hlow.trans (by simpa [q7ReferenceRows, vVLow] using h.1), h.2⟩
  · intro c hc
    have hc' : c ∈ v13ChainCells q7D.zp := by
      simpa only [q7ReferenceRows] using hc
    simpa [q7ReferenceRows] using v13_q7_z_source_bounds c hc'

/-! The concrete q7 normalization supplies the normalization field of C;
the remaining numeric and analytic certificate fields stay explicit. -/
theorem q7_normalization_leaf :
    V13MeasureNormalization q7ReferenceBaseRange
      (v13RefRaw q7ReferenceRows) :=
  q7ReferenceNormalization
noncomputable def v13_reference_package_input_q7_template
    {hq : SignedVBaseRange 7}
    (C : V13NumericCertificates 7 hq q7ReferenceRows)
    (lr : IV)
    (lr_sound : IV.mem lr (Real.log (3 / 5 : ℝ)))
    (field_x : CellSoundnessOn (pieceDomain 7 .x).1 (pieceDomain 7 .x).2
      (fieldUB q7ReferenceRows.data 7 lr .x)
      (fun t => V.signedVFullFieldX
        (v13RefMeasure q7ReferenceRows C.normalization) (t : ℂ)))
    (field_vlo : CellSoundnessOn (pieceDomain 7 .vlo).1 (pieceDomain 7 .vlo).2
      (fieldUB q7ReferenceRows.data 7 lr .vlo)
      (fun t => V.signedVFullFieldV
        (v13RefMeasure q7ReferenceRows C.normalization) (t : ℂ)))
    (field_vhi : CellSoundnessOn (pieceDomain 7 .vhi).1 (pieceDomain 7 .vhi).2
      (fieldUB q7ReferenceRows.data 7 lr .vhi)
      (fun t => V.signedVFullFieldV
        (v13RefMeasure q7ReferenceRows C.normalization) (t : ℂ)))
    (field_zneg : CellSoundnessOn (pieceDomain 7 .zneg).1 (pieceDomain 7 .zneg).2
      (fieldUB q7ReferenceRows.data 7 lr .zneg)
      (fun t => V.signedVFullFieldZ
        (v13RefMeasure q7ReferenceRows C.normalization) (t : ℂ)))
    (field_zpos : CellSoundnessOn (pieceDomain 7 .zpos).1 (pieceDomain 7 .zpos).2
      (fieldUB q7ReferenceRows.data 7 lr .zpos)
      (fun t => V.signedVFullFieldZ
        (v13RefMeasure q7ReferenceRows C.normalization) (t : ℂ)))
    (energy : EnergyShardSoundnessFact q7ReferenceRows.data 7 lr
      q7EnergyPlan (vEnergyTerm 7 q7ReferenceRows.data))
    (total : EnergyTotalSoundnessFact
      (v13RefMeasure q7ReferenceRows C.normalization)
      q7ReferenceRows.data q7EnergyPlan
      (vEnergyTerm 7 q7ReferenceRows.data)) :
    V13ReferencePackageInput 7 hq := by
  exact v13ReferencePackageInput_of_rows q7ReferenceRows C lr lr_sound
    q7EnergyPlan (vEnergyTerm 7 q7ReferenceRows.data)
    q7ReferenceMeasure_qlow_value
    field_x field_vlo field_vhi field_zneg field_zpos
    energy total


end

end Li2Lean.B3

#print axioms Li2Lean.B3.q2_decoded_row_bounds_leaf
#print axioms Li2Lean.B3.v13_reference_package_input_q2_of_v13_certificates
#print axioms Li2Lean.B3.q6_decoded_row_bounds_template
#print axioms Li2Lean.B3.q6ReferenceMeasure_qlow_value
#print axioms Li2Lean.B3.q6_normalization_leaf
#print axioms Li2Lean.B3.v13_reference_package_input_q6_template
#print axioms Li2Lean.B3.q7_decoded_row_bounds_leaf
#print axioms Li2Lean.B3.q7_normalization_leaf
#print axioms Li2Lean.B3.v13_reference_package_input_q7_template
