/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B3.ReferencePackagePinnedAdapter
import Li2Lean.B3.ReferencePackageGeneric
import Li2Lean.B3.Q2ReferencePackageFacts
import Li2Lean.B3.Q5ReferencePackageAssembly
import Li2Lean.B3.Q5ReferenceSupport
import Li2Lean.V.EnergyCertI.Q2Assembly
import Li2Lean.V.EnergyCertI.Q5Assembly

namespace Li2Lean.B3

noncomputable section

open V
open V.EnergyCertI
open V.EnergyCertI.IK

/-! The q2/q5 adapters below fix the plan and term to the decoded source.
They leave every analytic, shard, and total-identity witness explicit. -/

noncomputable def v13_reference_package_input_q2_template
    {hq : SignedVBaseRange 2}
    (C : V13NumericCertificates 2 hq q2ReferenceRows)
    (lr : IV)
    (lr_sound : IV.mem lr (Real.log (3 / 5 : ℝ)))
    (field_x : CellSoundnessOn (pieceDomain 2 .x).1 (pieceDomain 2 .x).2
      (fieldUB q2ReferenceRows.data 2 lr .x)
      (fun t => V.signedVFullFieldX
        (v13RefMeasure q2ReferenceRows C.normalization) (t : ℂ)))
    (field_vlo : CellSoundnessOn (pieceDomain 2 .vlo).1 (pieceDomain 2 .vlo).2
      (fieldUB q2ReferenceRows.data 2 lr .vlo)
      (fun t => V.signedVFullFieldV
        (v13RefMeasure q2ReferenceRows C.normalization) (t : ℂ)))
    (field_vhi : CellSoundnessOn (pieceDomain 2 .vhi).1 (pieceDomain 2 .vhi).2
      (fieldUB q2ReferenceRows.data 2 lr .vhi)
      (fun t => V.signedVFullFieldV
        (v13RefMeasure q2ReferenceRows C.normalization) (t : ℂ)))
    (field_zneg : CellSoundnessOn (pieceDomain 2 .zneg).1 (pieceDomain 2 .zneg).2
      (fieldUB q2ReferenceRows.data 2 lr .zneg)
      (fun t => V.signedVFullFieldZ
        (v13RefMeasure q2ReferenceRows C.normalization) (t : ℂ)))
    (field_zpos : CellSoundnessOn (pieceDomain 2 .zpos).1 (pieceDomain 2 .zpos).2
      (fieldUB q2ReferenceRows.data 2 lr .zpos)
      (fun t => V.signedVFullFieldZ
        (v13RefMeasure q2ReferenceRows C.normalization) (t : ℂ)))
    (energy : EnergyShardSoundnessFact q2ReferenceRows.data 2 lr
      q2EnergyPlan (vEnergyTerm 2 q2ReferenceRows.data))
    (total : EnergyTotalSoundnessFact
      (v13RefMeasure q2ReferenceRows C.normalization) q2ReferenceRows.data
      q2EnergyPlan (vEnergyTerm 2 q2ReferenceRows.data)) :
    V13ReferencePackageInput 2 hq := by
  apply v13ReferencePackageInput_of_pinned q2ReferenceRows C lr lr_sound
    q2ReferenceQLowValue field_x field_vlo field_vhi field_zneg field_zpos
  · simpa [planOf] using energy
  · simpa [planOf] using total

theorem q5_decoded_row_bounds_template :
    V13DecodedRowBounds 5 q5DecodedReferenceRows := by
  refine {
    x_low := ?_
    x_full := ?_
    v_low := ?_
    v_full := ?_
    z_source := ?_ }
  · intro c hc
    have h := v13_q5_x_bounds c hc
    simpa [q5DecodedReferenceRows_data, vXLow] using h
  · intro c hc
    simpa [q5DecodedReferenceRows_data] using v13_q5_x_full_bounds c hc
  · intro c hc
    have h := v13_q5_v_bounds c hc
    simpa [q5DecodedReferenceRows_data, vVLow] using h
  · intro c hc
    simpa [q5DecodedReferenceRows_data] using v13_q5_v_full_bounds c hc
  · intro c hc
    simpa [q5DecodedReferenceRows_data] using v13_q5_z_source_bounds c hc

/-! The q5 package projection is construction-backed once the numeric
certificates have been supplied.  In particular, this does not manufacture
the F/E/T ledger: those fields remain in `C` and are checked by the generic
constructor.  The rows are the decoded q5 tables from `v-reference-data.tex:
224-292`, while the fixed plan and term below come from the generated
v13 evaluator (`v-arithmetic.tex:389-407`, `v-analytic.tex:18-48`). -/
noncomputable def v13_reference_package_q5_of_numeric_certificates
    {hq : SignedVBaseRange 5}
    (C : V13NumericCertificates 5 hq q5DecodedReferenceRows) :
    VReferencePackage 5 hq :=
  vReferencePackage_of_rows q5DecodedReferenceRows C

noncomputable def v13_reference_package_input_q5_template
    {hq : SignedVBaseRange 5}
    (C : V13NumericCertificates 5 hq q5DecodedReferenceRows)
    (lr : IV)
    (lr_sound : IV.mem lr (Real.log (3 / 5 : ℝ)))
    (field_x : CellSoundnessOn (pieceDomain 5 .x).1 (pieceDomain 5 .x).2
      (fieldUB q5DecodedReferenceRows.data 5 lr .x)
      (fun t => V.signedVFullFieldX
        (v13RefMeasure q5DecodedReferenceRows C.normalization) (t : ℂ)))
    (field_vlo : CellSoundnessOn (pieceDomain 5 .vlo).1 (pieceDomain 5 .vlo).2
      (fieldUB q5DecodedReferenceRows.data 5 lr .vlo)
      (fun t => V.signedVFullFieldV
        (v13RefMeasure q5DecodedReferenceRows C.normalization) (t : ℂ)))
    (field_vhi : CellSoundnessOn (pieceDomain 5 .vhi).1 (pieceDomain 5 .vhi).2
      (fieldUB q5DecodedReferenceRows.data 5 lr .vhi)
      (fun t => V.signedVFullFieldV
        (v13RefMeasure q5DecodedReferenceRows C.normalization) (t : ℂ)))
    (field_zneg : CellSoundnessOn (pieceDomain 5 .zneg).1 (pieceDomain 5 .zneg).2
      (fieldUB q5DecodedReferenceRows.data 5 lr .zneg)
      (fun t => V.signedVFullFieldZ
        (v13RefMeasure q5DecodedReferenceRows C.normalization) (t : ℂ)))
    (field_zpos : CellSoundnessOn (pieceDomain 5 .zpos).1 (pieceDomain 5 .zpos).2
      (fieldUB q5DecodedReferenceRows.data 5 lr .zpos)
      (fun t => V.signedVFullFieldZ
        (v13RefMeasure q5DecodedReferenceRows C.normalization) (t : ℂ)))
    (energy : EnergyShardSoundnessFact q5DecodedReferenceRows.data 5 lr
      q5EnergyPlan (vEnergyTerm 5 q5DecodedReferenceRows.data))
    (total : EnergyTotalSoundnessFact
      (v13RefMeasure q5DecodedReferenceRows C.normalization)
      q5DecodedReferenceRows.data q5EnergyPlan
      (vEnergyTerm 5 q5DecodedReferenceRows.data)) :
    V13ReferencePackageInput 5 hq := by
  apply v13ReferencePackageInput_of_pinned q5DecodedReferenceRows C lr lr_sound
    q5ReferenceMeasure_qlow_value field_x field_vlo field_vhi field_zneg field_zpos
  · simpa [planOf] using energy
  · simpa [planOf] using total

end

end Li2Lean.B3

#print axioms Li2Lean.B3.q5_decoded_row_bounds_template
#print axioms Li2Lean.B3.v13_reference_package_q5_of_numeric_certificates
#print axioms Li2Lean.B3.v13_reference_package_input_q2_template
#print axioms Li2Lean.B3.v13_reference_package_input_q5_template
