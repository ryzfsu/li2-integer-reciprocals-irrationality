/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
-- q = 7 construction-bound reference-package leaf.
import Li2Lean.B3.ReferencePackageLeafTemplates
import Li2Lean.B3.ReferencePackageGeneric
import Li2Lean.B3.ReferencePackagePinnedAdapter
import Li2Lean.B3.H6BallSigmaPerQ
import Li2Lean.B3.H6CertBridges
import Li2Lean.B3.H6CertQ7
import Li2Lean.B3.V13DqSeries
import Li2Lean.B3.Q7EnergyLowerBridge
import Li2Lean.V.EnergyCertI.ISoundGlue

namespace Li2Lean.B3

open V
open V.EnergyCertI
open V.EnergyCertI.IK

noncomputable section

/-- Closure target for the public q = 7 leaf. -/
noncomputable def v13_reference_package_input_q7_closed
    (hq : SignedVBaseRange 7) : V13ReferencePackageInput 7 hq := by
  let N := q7ReferenceNormalization_s5 hq
  have hrows := q7_decoded_row_bounds_leaf
  obtain ⟨hAx, hAv, hAz, hxb, hvb, hzb, hsigma⟩ :=
    v13RefMeasure_ball_and_sigma q7ReferenceRows N
  have hxe := H6CertQ7.x_endpoint_disk hrows N
  have hve := H6CertQ7.v_endpoint_disk hrows N
  have hmx : IK.val q7ReferenceRows.data.mx = 1 := by
    have h : q7D.mx = (50000000000000, 50000000000000) := by decide +kernel
    change IK.val q7D.mx = 1
    rw [h]
    norm_num [IK.val]
  have hmv : IK.val q7ReferenceRows.data.mv = 5 / 4 := by
    have h : q7D.mv = (62500000000000, 50000000000000) := by decide +kernel
    change IK.val q7D.mv = 5 / 4
    rw [h]
    norm_num [IK.val]
  have hseries : V13DqSeries q7ReferenceRows N :=
    DqSeries.v13_dq_series_core q7ReferenceRows q7_field_row_facts hrows N hmx hmv
  have henergy := H6CertQ7.energy N hseries
  have htotal := v13_total_fact_of_ballBound q7ReferenceRows q7_field_row_facts hrows N
    hAx hAv hAz hxb hvb hzb (planOf q7ReferenceRows.data 7)
  have hlower := h6_energy_lower q7ReferenceRows N (planOf q7ReferenceRows.data 7) henergy htotal
    (by simpa [planOf_q7, q7ReferenceRows] using q7EnergyPlan_tiles)
    (by simpa [planOf_q7] using q7EnergyClaims_gt_qlow)
    (by norm_num [qlowQ]) q7ReferenceMeasure_qlow_value
  let C := h6_numeric_certificates q7ReferenceRows q7_field_row_facts hrows N
    (v13Ax 7) (v13Av 7) (v13Az 7) hAx hAv hAz hxb hvb hzb hsigma hlower
    (H6CertQ7.x_field N hxe) (H6CertQ7.v_field N hve)
    (H6CertQ7.z_field N) (by simpa using v13_alpha_le_q7) hxe hve
  have hc := H6CertQ7.cells N h6_vLogRE_sound
  exact v13ReferencePackageInput_of_pinned q7ReferenceRows C vLogRE h6_vLogRE_sound
    q7ReferenceMeasure_qlow_value hc.x hc.vlo hc.vhi hc.zneg hc.zpos henergy htotal

end

end Li2Lean.B3

#print axioms Li2Lean.B3.v13_reference_package_input_q7_closed
