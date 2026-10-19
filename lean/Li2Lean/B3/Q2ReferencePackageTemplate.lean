/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 License.

The q = 2 reference-package template.  This file only binds the concrete
v13 q2 rows, normalization, plan, and term to the generic certificate
constructor.  The analytic ball, field, endpoint, integrability, shard, and
total witnesses remain explicit inputs.

The construction follows v13 `v-reference-data.tex:1-83` and
`v-analytic.tex:339-386`.
-/

import Li2Lean.B3.ReferencePackageLeafTemplates
import Li2Lean.B3.ReferencePackageGeneric
import Li2Lean.B3.ReferenceDualIntegrable
import Li2Lean.B3.Q2EnergyLowerBridge
import Li2Lean.B3.F6Alpha

namespace Li2Lean

noncomputable section

namespace B3

open MeasureTheory Set
open V
open V.EnergyCertI
open V.EnergyCertI.IK

/-- Bind the real q = 2 certificate fields to the fixed v13 construction.

The `VBallBound` and endpoint hypotheses are attached to the same normalized
measure used by the energy and field hypotheses.  The plan and term are fixed
to the checked q2 tables, so this adapter cannot silently substitute another
finite certificate.  The remaining witnesses are exactly the finite and
analytic inputs required by the generic package constructor.
-/
noncomputable def q2_reference_package_input_of_soundness
    (hq : SignedVBaseRange 2)
    (lr : IV)
    (lr_sound : IK.IV.mem lr (Real.log (3 / 5 : ℝ)))
    (Ax Av Az : ℝ)
    (hAx : 0 ≤ Ax)
    (hAv : 0 ≤ Av)
    (hAz : 0 ≤ Az)
    (N : V13MeasureNormalization hq (v13RefRaw q2ReferenceRows))
    (hx_ball : VBallBound (v13RefMeasure q2ReferenceRows N).μx Ax)
    (hv_ball : VBallBound (v13RefMeasure q2ReferenceRows N).μv Av)
    (hz_ball : VBallBound (v13RefMeasure q2ReferenceRows N).μz Az)
    (hsigma : vSigma 2 = sigmaBudget Ax Av Az)
    (hx_disk : ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ ≤ 1 / 250 →
      V.signedVFullFieldX (v13RefMeasure q2ReferenceRows N) w ≤ (vEx 2 : ℝ))
    (hv_disk : ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ ≤ 1 / 250 →
      V.signedVFullFieldV (v13RefMeasure q2ReferenceRows N) w ≤ (vEv 2 : ℝ))
    (hx_field : ∀ t : ℝ, t ∈ Set.Ioc (0 : ℝ) 1 →
      V.signedVFullFieldX (v13RefMeasure q2ReferenceRows N) (t : ℂ) < (vKx 2 : ℝ))
    (hv_field : ∀ t : ℝ, t ∈ Set.Ioc (0 : ℝ) 1 →
      V.signedVFullFieldV (v13RefMeasure q2ReferenceRows N) (t : ℂ) < (vKv 2 : ℝ))
    (hz_field : ∀ w ∈ V.vContourTrace 2,
      V.signedVFullFieldZ (v13RefMeasure q2ReferenceRows N) w < (vKz 2 : ℝ))
    (field_x : CellSoundnessOn (pieceDomain 2 .x).1 (pieceDomain 2 .x).2
      (V.EnergyCertI.fieldUB q2ReferenceRows.data 2 lr .x)
      (fun t => V.signedVFullFieldX
        (v13RefMeasure q2ReferenceRows N) (t : ℂ)))
    (field_vlo : CellSoundnessOn (pieceDomain 2 .vlo).1 (pieceDomain 2 .vlo).2
      (V.EnergyCertI.fieldUB q2ReferenceRows.data 2 lr .vlo)
      (fun t => V.signedVFullFieldV
        (v13RefMeasure q2ReferenceRows N) (t : ℂ)))
    (field_vhi : CellSoundnessOn (pieceDomain 2 .vhi).1 (pieceDomain 2 .vhi).2
      (V.EnergyCertI.fieldUB q2ReferenceRows.data 2 lr .vhi)
      (fun t => V.signedVFullFieldV
        (v13RefMeasure q2ReferenceRows N) (t : ℂ)))
    (field_zneg : CellSoundnessOn (pieceDomain 2 .zneg).1 (pieceDomain 2 .zneg).2
      (V.EnergyCertI.fieldUB q2ReferenceRows.data 2 lr .zneg)
      (fun t => V.signedVFullFieldZ
        (v13RefMeasure q2ReferenceRows N) (t : ℂ)))
    (field_zpos : CellSoundnessOn (pieceDomain 2 .zpos).1 (pieceDomain 2 .zpos).2
      (V.EnergyCertI.fieldUB q2ReferenceRows.data 2 lr .zpos)
      (fun t => V.signedVFullFieldZ
        (v13RefMeasure q2ReferenceRows N) (t : ℂ)))
    (henergy : EnergyShardSoundnessFact q2ReferenceRows.data 2 lr
      q2EnergyPlan (vEnergyTerm 2 q2ReferenceRows.data))
    (htotal : EnergyTotalSoundnessFact (v13RefMeasure q2ReferenceRows N)
      q2ReferenceRows.data q2EnergyPlan (vEnergyTerm 2 q2ReferenceRows.data)) :
    V13ReferencePackageInput 2 hq := by
  have hdual := signedVReferenceIntegrable_of_ballBound
    q2ReferenceRows q2_decoded_row_bounds_leaf N hAx hAv hAz
    hx_ball hv_ball hz_ball
  let C : V13NumericCertificates 2 hq q2ReferenceRows := {
    rows := q2_decoded_row_bounds_leaf
    normalization := N
    Ax := Ax
    Av := Av
    Az := Az
    Ax_nonneg := hAx
    Av_nonneg := hAv
    Az_nonneg := hAz
    x_ball := hx_ball
    v_ball := hv_ball
    z_ball := hz_ball
    sigma_eq := hsigma
    energy_lower := q2_energy_lower_of_shard_and_total hq N lr henergy htotal
    x_field := hx_field
    v_field := hv_field
    z_field := hz_field
    alpha_le := v13_alpha_le_q2
    x_endpoint_disk := hx_disk
    v_endpoint_disk := hv_disk
    dual_admissible := hdual }
  exact v13ReferencePackageInput_of_rows q2ReferenceRows C lr lr_sound
    q2EnergyPlan (vEnergyTerm 2 q2ReferenceRows.data) q2ReferenceQLowValue
    field_x field_vlo field_vhi field_zneg field_zpos henergy htotal

end B3

end

end Li2Lean

#print axioms Li2Lean.B3.q2_reference_package_input_of_soundness
