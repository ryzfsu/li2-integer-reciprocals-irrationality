/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
-- q = 5 construction-bound reference-package leaf.
import Li2Lean.B3.ReferencePackageLeafTemplates
import Li2Lean.B3.H6ReferencePackageTemplates
import Li2Lean.B3.ReferenceDualIntegrable
import Li2Lean.B3.Q5EnergyLowerBridge
import Li2Lean.B3.F6Alpha
import Li2Lean.B3.ReferencePackageGeneric
import Li2Lean.B3.ReferencePackagePinnedAdapter
import Li2Lean.B3.V13FieldCellGeneric
import Li2Lean.B3.H6CertBridges
import Li2Lean.B3.H6CertQ5
import Li2Lean.B3.H6BallSigmaPerQ
import Li2Lean.B3.V13DqSeries

namespace Li2Lean.B3

noncomputable section

open V
open V.EnergyCertI
open V.EnergyCertI.IK

/-! Bind the q = 5 construction to the generic package constructor. Every
analytic and finite witness is an explicit argument attached to the same
normalized measure; in particular the Poisson part of the z ball bound is not
silently inferred from the decoded row count. -/
noncomputable def q5_reference_package_input_of_soundness
    (hq : SignedVBaseRange 5)
    (lr : IV)
    (lr_sound : IV.mem lr (Real.log (3 / 5 : ℝ)))
    (Ax Av Az : ℝ)
    (hAx : 0 ≤ Ax)
    (hAv : 0 ≤ Av)
    (hAz : 0 ≤ Az)
    (N : V13MeasureNormalization hq (v13RefRaw q5DecodedReferenceRows))
    (hx_ball : VBallBound (v13RefMeasure q5DecodedReferenceRows N).μx Ax)
    (hv_ball : VBallBound (v13RefMeasure q5DecodedReferenceRows N).μv Av)
    (hz_ball : VBallBound (v13RefMeasure q5DecodedReferenceRows N).μz Az)
    (hsigma : vSigma 5 = sigmaBudget Ax Av Az)
    (hx_disk : ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ ≤ 1 / 250 →
      V.signedVFullFieldX (v13RefMeasure q5DecodedReferenceRows N) w ≤ (vEx 5 : ℝ))
    (hv_disk : ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ ≤ 1 / 250 →
      V.signedVFullFieldV (v13RefMeasure q5DecodedReferenceRows N) w ≤ (vEv 5 : ℝ))
    (hx_field : ∀ t : ℝ, t ∈ Set.Ioc (0 : ℝ) 1 →
      V.signedVFullFieldX (v13RefMeasure q5DecodedReferenceRows N) (t : ℂ) < (vKx 5 : ℝ))
    (hv_field : ∀ t : ℝ, t ∈ Set.Ioc (0 : ℝ) 1 →
      V.signedVFullFieldV (v13RefMeasure q5DecodedReferenceRows N) (t : ℂ) < (vKv 5 : ℝ))
    (hz_field : ∀ w ∈ V.vContourTrace 5,
      V.signedVFullFieldZ (v13RefMeasure q5DecodedReferenceRows N) w < (vKz 5 : ℝ))
    (field_x : CellSoundnessOn (pieceDomain 5 .x).1 (pieceDomain 5 .x).2
      (fieldUB q5DecodedReferenceRows.data 5 lr .x)
      (fun t => V.signedVFullFieldX
        (v13RefMeasure q5DecodedReferenceRows N) (t : ℂ)))
    (field_vlo : CellSoundnessOn (pieceDomain 5 .vlo).1 (pieceDomain 5 .vlo).2
      (fieldUB q5DecodedReferenceRows.data 5 lr .vlo)
      (fun t => V.signedVFullFieldV
        (v13RefMeasure q5DecodedReferenceRows N) (t : ℂ)))
    (field_vhi : CellSoundnessOn (pieceDomain 5 .vhi).1 (pieceDomain 5 .vhi).2
      (fieldUB q5DecodedReferenceRows.data 5 lr .vhi)
      (fun t => V.signedVFullFieldV
        (v13RefMeasure q5DecodedReferenceRows N) (t : ℂ)))
    (field_zneg : CellSoundnessOn (pieceDomain 5 .zneg).1 (pieceDomain 5 .zneg).2
      (fieldUB q5DecodedReferenceRows.data 5 lr .zneg)
      (fun t => V.signedVFullFieldZ
        (v13RefMeasure q5DecodedReferenceRows N) (t : ℂ)))
    (field_zpos : CellSoundnessOn (pieceDomain 5 .zpos).1 (pieceDomain 5 .zpos).2
      (fieldUB q5DecodedReferenceRows.data 5 lr .zpos)
      (fun t => V.signedVFullFieldZ
        (v13RefMeasure q5DecodedReferenceRows N) (t : ℂ)))
    (henergy : EnergyShardSoundnessFact q5DecodedReferenceRows.data 5 lr
      q5EnergyPlan (vEnergyTerm 5 q5DecodedReferenceRows.data))
    (htotal : EnergyTotalSoundnessFact
      (v13RefMeasure q5DecodedReferenceRows N)
      q5DecodedReferenceRows.data q5EnergyPlan
      (vEnergyTerm 5 q5DecodedReferenceRows.data)) :
    V13ReferencePackageInput 5 hq := by
  have hdual := signedVReferenceIntegrable_of_ballBound
    q5DecodedReferenceRows q5_decoded_row_bounds_template N hAx hAv hAz
    hx_ball hv_ball hz_ball
  have henergy_lower := q5_energy_lower_of_shard_and_total
    hq N lr henergy htotal
  let C : V13NumericCertificates 5 hq q5DecodedReferenceRows := {
    rows := q5_decoded_row_bounds_template
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
    energy_lower := henergy_lower
    x_field := hx_field
    v_field := hv_field
    z_field := hz_field
    alpha_le := v13_alpha_le_q5
    x_endpoint_disk := hx_disk
    v_endpoint_disk := hv_disk
    dual_admissible := hdual }
  exact v13ReferencePackageInput_of_rows q5DecodedReferenceRows C lr lr_sound
    q5EnergyPlan (vEnergyTerm 5 q5DecodedReferenceRows.data)
    q5ReferenceMeasure_qlow_value field_x field_vlo field_vhi field_zneg
    field_zpos henergy htotal

/-- Closure target for the public q = 5 leaf. -/
noncomputable def v13_reference_package_input_q5_closed
    (hq : SignedVBaseRange 5) : V13ReferencePackageInput 5 hq := by
  let N := q5ReferenceNormalization_s5 hq
  have hrows := q5_decoded_row_bounds_template
  obtain ⟨hAx, hAv, hAz, hxb, hvb, hzb, hsigma⟩ :=
    v13RefMeasure_ball_and_sigma q5DecodedReferenceRows N
  have hxe := H6CertQ5.x_endpoint_disk hrows N
  have hve := H6CertQ5.v_endpoint_disk hrows N
  have hmx : IK.val q5DecodedReferenceRows.data.mx = 1 := by
    have h : q5D.mx = (50000000000000, 50000000000000) := by decide +kernel
    change IK.val q5D.mx = 1
    rw [h]
    norm_num [IK.val]
  have hmv : IK.val q5DecodedReferenceRows.data.mv = 5 / 4 := by
    have h : q5D.mv = (62500000000000, 50000000000000) := by decide +kernel
    change IK.val q5D.mv = 5 / 4
    rw [h]
    norm_num [IK.val]
  have hseries : V13DqSeries q5DecodedReferenceRows N :=
    DqSeries.v13_dq_series_core q5DecodedReferenceRows q5_field_row_facts hrows N hmx hmv
  have henergy := H6CertQ5.energy N hseries
  have htotal := v13_total_fact_of_ballBound q5DecodedReferenceRows q5_field_row_facts hrows N
    hAx hAv hAz hxb hvb hzb (planOf q5DecodedReferenceRows.data 5)
  have hlower := h6_energy_lower q5DecodedReferenceRows N (planOf q5DecodedReferenceRows.data 5)
    henergy htotal
    (by simpa [planOf_q5, q5DecodedReferenceRows_data] using q5EnergyPlan_tiles)
    (by simpa [planOf_q5] using q5EnergyClaims_gt_qlow)
    (by norm_num [qlowQ]) q5ReferenceMeasure_qlow_value
  let C := h6_numeric_certificates q5DecodedReferenceRows q5_field_row_facts hrows N
    (v13Ax 5) (v13Av 5) (v13Az 5) hAx hAv hAz hxb hvb hzb hsigma hlower
    (H6CertQ5.x_field N hxe) (H6CertQ5.v_field N hve)
    (H6CertQ5.z_field N) (by simpa using v13_alpha_le_q5) hxe hve
  have hc := H6CertQ5.cells N h6_vLogRE_sound
  exact v13ReferencePackageInput_of_pinned q5DecodedReferenceRows C vLogRE h6_vLogRE_sound
    q5ReferenceMeasure_qlow_value hc.x hc.vlo hc.vhi hc.zneg hc.zpos henergy htotal

end

end Li2Lean.B3

#print axioms Li2Lean.B3.v13_reference_package_input_q5_closed
