/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
/- q = 6 construction-bound reference-package leaf. -/

import Li2Lean.B3.ReferencePackageLeafTemplates
import Li2Lean.B3.ReferencePackageGeneric
import Li2Lean.B3.V13FieldCellGeneric
import Li2Lean.B3.H6CertBridges
import Li2Lean.B3.H6CertQ6
import Li2Lean.B3.H6BallSigmaPerQ
import Li2Lean.B3.V13DqSeries
import Li2Lean.B3.Q6ReferenceMeasureFacts
import Li2Lean.B3.Q6ReferenceNormalization
import Li2Lean.B3.Q6ReferenceSupportLow
import Li2Lean.V.EnergyCertI.Q6Assembly
import Li2Lean.V.EnergyCertI.ISoundGlue

namespace Li2Lean.B3

noncomputable section

open V
open V.EnergyCertI
open V.EnergyCertI.IK

/-- The q6 leaf is assembled from the common numeric constructor and the
finite q6 certificate ledgers. -/
noncomputable def v13_reference_package_input_q6_closed
    (hq : SignedVBaseRange 6) : V13ReferencePackageInput 6 hq := by
  let N := q6ReferenceNormalization_s5 hq
  have hrows := q6_decoded_row_bounds_template
  obtain ⟨hAx, hAv, hAz, hxb, hvb, hzb, hsigma⟩ :=
    v13RefMeasure_ball_and_sigma q6DecodedReferenceRows N
  have hxe := H6CertQ6.x_endpoint_disk hrows N
  have hve := H6CertQ6.v_endpoint_disk hrows N
  have hmx : IK.val q6DecodedReferenceRows.data.mx = 1 := by
    have h : q6D.mx = (50000000000000, 50000000000000) := by
      decide +kernel
    change IK.val q6D.mx = 1
    rw [h]
    norm_num [IK.val]
  have hmv : IK.val q6DecodedReferenceRows.data.mv = 5 / 4 := by
    have h : q6D.mv = (62500000000000, 50000000000000) := by
      decide +kernel
    change IK.val q6D.mv = 5 / 4
    rw [h]
    norm_num [IK.val]
  have hseries : V13DqSeries q6DecodedReferenceRows N :=
    DqSeries.v13_dq_series_core q6DecodedReferenceRows q6_field_row_facts hrows N hmx hmv
  have henergy := H6CertQ6.energy N hseries
  have htotal := v13_total_fact_of_ballBound q6DecodedReferenceRows q6_field_row_facts
    hrows N hAx hAv hAz hxb hvb hzb q6EnergyPlan
  have hlower := h6_energy_lower q6DecodedReferenceRows N q6EnergyPlan henergy htotal
    q6EnergyPlan_tiles q6EnergyClaims_gt_qlow (by norm_num [qlowQ])
    q6ReferenceMeasure_qlow_value
  let C := h6_numeric_certificates q6DecodedReferenceRows q6_field_row_facts hrows N
    (v13Ax 6) (v13Av 6) (v13Az 6) hAx hAv hAz hxb hvb hzb hsigma hlower
    (H6CertQ6.x_field N hxe) (H6CertQ6.v_field N hve)
    (H6CertQ6.z_field N) (by simpa using v13_alpha_le_q6) hxe hve
  have hc := H6CertQ6.cells N h6_vLogRE_sound
  exact v13ReferencePackageInput_of_rows q6DecodedReferenceRows C vLogRE
    h6_vLogRE_sound q6EnergyPlan (vEnergyTerm 6 q6DecodedReferenceRows.data)
    q6ReferenceMeasure_qlow_value hc.x hc.vlo hc.vhi hc.zneg hc.zpos henergy htotal

end

end Li2Lean.B3

#print axioms Li2Lean.B3.v13_reference_package_input_q6_closed
