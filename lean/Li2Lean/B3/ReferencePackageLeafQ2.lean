/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
-- q = 2 construction-bound reference-package leaf.
import Li2Lean.B3.ReferencePackageLeafTemplates
import Li2Lean.B3.ReferencePackageGeneric
import Li2Lean.B3.Q2ReferencePackageTemplate
import Li2Lean.B3.ReferencePackagePinnedAdapter
import Li2Lean.B3.V13FieldCellGeneric
import Li2Lean.B3.H6CertBridges
import Li2Lean.B3.H6CertQ2
import Li2Lean.B3.H6BallSigmaPerQ
import Li2Lean.B3.V13DqSeries

namespace Li2Lean.B3

noncomputable section

open V
open V.EnergyCertI
open V.EnergyCertI.IK
/- The q2 row source and support bounds are concrete.  The constructor below
keeps the remaining numeric and analytic certificates explicit; in particular,
it cannot be used to manufacture the missing F/E/T ledger fields. -/
noncomputable def v13_reference_package_q2_of_numeric_certificates
    {hq : SignedVBaseRange 2}
    (C : V13NumericCertificates 2 hq q2ReferenceRows) :
    VReferencePackage 2 hq :=
  vReferencePackage_of_rows q2ReferenceRows C

/-- Closure target for the public q = 2 leaf.  Same assembly as the q4/q5/q7
leaves: the ball and sigma constants come from the exact maximum densities in
`v13RefMeasure_ball_and_sigma` (not from the integer ball bounds of
`Q2ReferenceXBall`), and every certificate is attached to the same
normalized measure `v13RefMeasure q2ReferenceRows N`. -/
noncomputable def v13_reference_package_input_q2_closed
    (hq : SignedVBaseRange 2) : V13ReferencePackageInput 2 hq := by
  let N := q2ReferenceNormalization_of_hq hq
  have hrows := q2_decoded_row_bounds_leaf
  obtain ⟨hAx, hAv, hAz, hxb, hvb, hzb, hsigma⟩ :=
    v13RefMeasure_ball_and_sigma q2ReferenceRows N
  have hxe := H6CertQ2.x_endpoint_disk hrows N
  have hve := H6CertQ2.v_endpoint_disk hrows N
  -- Exact decoded masses (checked offline: sum of x masses = 5*10^13 units,
  -- sum of v masses = 6.25*10^13 units, unit 5*10^13).
  have hmx : IK.val q2ReferenceRows.data.mx = 1 := by
    have h : q2D.mx = (50000000000000, 50000000000000) := by decide +kernel
    change IK.val q2D.mx = 1
    rw [h]
    norm_num [IK.val]
  have hmv : IK.val q2ReferenceRows.data.mv = 5 / 4 := by
    have h : q2D.mv = (62500000000000, 50000000000000) := by decide +kernel
    change IK.val q2D.mv = 5 / 4
    rw [h]
    norm_num [IK.val]
  have hseries : V13DqSeries q2ReferenceRows N :=
    DqSeries.v13_dq_series_core q2ReferenceRows q2_field_row_facts hrows N hmx hmv
  have henergy := H6CertQ2.energy N hseries
  have htotal := v13_total_fact_of_ballBound q2ReferenceRows q2_field_row_facts hrows N
    hAx hAv hAz hxb hvb hzb (planOf q2ReferenceRows.data 2)
  have hlower := h6_energy_lower q2ReferenceRows N (planOf q2ReferenceRows.data 2)
    henergy htotal
    (by simpa [planOf_q2, q2ReferenceRows_data] using q2EnergyPlan_tiles)
    (by simpa [planOf_q2] using q2EnergyClaims_gt_qlow)
    (by norm_num [qlowQ]) q2ReferenceQLowValue
  let C := h6_numeric_certificates q2ReferenceRows q2_field_row_facts hrows N
    (v13Ax 2) (v13Av 2) (v13Az 2) hAx hAv hAz hxb hvb hzb hsigma hlower
    (H6CertQ2.x_field N hxe) (H6CertQ2.v_field N hve)
    (H6CertQ2.z_field N) (by simpa using v13_alpha_le_q2) hxe hve
  have hc := H6CertQ2.cells N h6_vLogRE_sound
  exact v13ReferencePackageInput_of_pinned q2ReferenceRows C vLogRE h6_vLogRE_sound
    q2ReferenceQLowValue hc.x hc.vlo hc.vhi hc.zneg hc.zpos henergy htotal

end

end Li2Lean.B3

#print axioms Li2Lean.B3.v13_reference_package_input_q2_closed
