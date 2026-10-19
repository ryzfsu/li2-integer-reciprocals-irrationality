/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
-- q = 3 construction-bound reference-package leaf.
import Li2Lean.B3.ReferencePackageLeafTemplates
import Li2Lean.B3.ReferencePackageQ3Template
import Li2Lean.B3.Q3EnergyLowerBridge
import Li2Lean.B3.H6BallSigmaPerQ
import Li2Lean.B3.H6CertQ3
import Li2Lean.B3.H6CertBridges
import Li2Lean.B3.V13DqSeries
import Li2Lean.V.EnergyCertI.Q3Assembly
import Li2Lean.V.EnergyCertI.ISoundGlue

namespace Li2Lean.B3

noncomputable section
open V
open V.EnergyCertI
open V.EnergyCertI.IK

/-- Closure target for the public q = 3 leaf. -/
noncomputable def v13_reference_package_input_q3_closed
    (hq : SignedVBaseRange 3) : V13ReferencePackageInput 3 hq := by
  let N := q3ReferenceNormalization_of_hq hq
  have hrows := q3_decoded_row_bounds
  have q3DecodedRows_data : q3DecodedRows.data = q3D := rfl
  obtain ⟨hAx, hAv, hAz, hxb, hvb, hzb, hsigma⟩ :=
    v13RefMeasure_ball_and_sigma q3DecodedRows N
  have hxe := H6CertQ3.x_endpoint_disk hrows N
  have hve := H6CertQ3.v_endpoint_disk hrows N
  have hmx : IK.val q3DecodedRows.data.mx = 1 := by
    have h : q3D.mx = (50000000000000, 50000000000000) := by decide +kernel
    change IK.val q3D.mx = 1
    rw [h]
    norm_num [IK.val]
  have hmv : IK.val q3DecodedRows.data.mv = 5 / 4 := by
    have h : q3D.mv = (62500000000000, 50000000000000) := by decide +kernel
    change IK.val q3D.mv = 5 / 4
    rw [h]
    norm_num [IK.val]
  have hseries : V13DqSeries q3DecodedRows N :=
    DqSeries.v13_dq_series_core q3DecodedRows q3_field_row_facts hrows N hmx hmv
  have henergy := H6CertQ3.energy N hseries
  have htotal := v13_total_fact_of_ballBound q3DecodedRows q3_field_row_facts hrows N
    hAx hAv hAz hxb hvb hzb (planOf q3DecodedRows.data 3)
  have hlower := h6_energy_lower q3DecodedRows N (planOf q3DecodedRows.data 3) henergy htotal
    (by simpa [planOf_q3, q3DecodedRows_data] using q3EnergyPlan_tiles)
    (by simpa [planOf_q3] using q3EnergyClaims_gt_qlow)
    (by norm_num [qlowQ]) q3ReferenceMeasure_qlow_value
  let C := h6_numeric_certificates q3DecodedRows q3_field_row_facts hrows N
    (v13Ax 3) (v13Av 3) (v13Az 3) hAx hAv hAz hxb hvb hzb hsigma hlower
    (H6CertQ3.x_field N hxe) (H6CertQ3.v_field N hve)
    (H6CertQ3.z_field N) (by simpa using v13_alpha_le_q3) hxe hve
  have hc := H6CertQ3.cells N h6_vLogRE_sound
  exact v13ReferencePackageInput_of_pinned q3DecodedRows C vLogRE h6_vLogRE_sound
    q3ReferenceMeasure_qlow_value hc.x hc.vlo hc.vhi hc.zneg hc.zpos henergy htotal

end

end Li2Lean.B3

#print axioms Li2Lean.B3.v13_reference_package_input_q3_closed
