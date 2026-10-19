/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
-- q = 4 construction-bound reference-package leaf.
import Li2Lean.B3.ReferencePackageLeafTemplates
import Li2Lean.B3.ReferencePackageGeneric
import Li2Lean.B3.ReferencePackagePinnedAdapter
import Li2Lean.B3.V13FieldCellGeneric
import Li2Lean.B3.H6CertBridges
import Li2Lean.B3.H6CertQ4
import Li2Lean.B3.H6BallSigmaPerQ
import Li2Lean.B3.V13DqSeries
import Li2Lean.B3.Q4ReferenceMeasureFacts
import Li2Lean.B3.Q4ReferenceNormalization
import Li2Lean.B3.Q4ReferenceSupportLow
import Li2Lean.B3.Q4ReferenceVSupport
import Li2Lean.B3.Q4ReferenceZSourceBounds
import Li2Lean.B3.Q4EndpointDisk
import Li2Lean.V.EnergyCertI.Q4Assembly
import Li2Lean.V.EnergyCertI.ISoundGlue

namespace Li2Lean.B3

noncomputable section

open V
open V.EnergyCertI
open V.EnergyCertI.IK
/-! The q4 row source is the exact decoded `q4D` table.  These bounds are
proved from the finite decoder checks and are independent of the missing
field, shard, and total ledgers. -/
theorem q4_decoded_row_bounds_leaf :
    V13DecodedRowBounds 4 q4DecodedRows := by
  refine {
    x_low := ?_
    x_full := ?_
    v_low := ?_
    v_full := ?_
    z_source := ?_ }
  · intro c hc
    have h := v13_q4_x_bounds c hc
    have hlow : (vXLow 4 : ℝ) =
        (3349364905389 : ℝ) / (5 * 10 ^ 13) := by
      norm_num [vXLow]
    constructor
    · rw [hlow]
      exact h.1
    · exact h.2
  · intro c hc
    have h := v13_q4_x_bounds c hc
    have hlow : (0 : ℝ) ≤ vXLow 4 := by
      norm_num [vXLow]
    have hlow' : (vXLow 4 : ℝ) ≤ c.left := by
      have hrepr : (vXLow 4 : ℝ) =
          (3349364905389 : ℝ) / (5 * 10 ^ 13) := by
        norm_num [vXLow]
      rw [hrepr]
      exact h.1
    exact ⟨hlow.trans hlow', h.2⟩
  · intro c hc
    have h := v13_q4_v_bounds c hc
    simpa [q4DecodedRows_data] using h
  · intro c hc
    have h := v13_q4_v_bounds c hc
    have hlow : (0 : ℝ) ≤ vVLow 4 := by
      norm_num [vVLow]
    exact ⟨hlow.trans (by simpa [q4DecodedRows_data] using h.1),
      by simpa [q4DecodedRows_data] using h.2⟩
  · intro c hc
    have h := v13_q4_z_source_bounds c hc
    simpa [q4DecodedRows_data] using h

/-! The finite q4 normalization facts are stated at the canonical base-range
proof in `Q4ReferenceNormalization`.  Proof irrelevance transports that
ledger to the arbitrary base-range proof used by a package leaf. -/
theorem q4ReferenceNormalization_of_hq (hq : SignedVBaseRange 4) :
    V13MeasureNormalization hq (v13RefRaw q4DecodedRows) := by
  exact q4ReferenceNormalization

/-! The generated q4 shard and tile certificates imply the q4 lower-energy
bound once the total identity is supplied for the same decoded measure. -/
theorem q4_energy_lower_of_shard_and_total
    (hq : SignedVBaseRange 4)
    (N : V13MeasureNormalization hq (v13RefRaw q4DecodedRows))
    (lr : IV)
    (henergy : EnergyShardSoundnessFact q4DecodedRows.data 4 lr
      q4EnergyPlan (vEnergyTerm 4 q4DecodedRows.data))
    (htotal : EnergyTotalSoundnessFact
      (v13RefMeasure q4DecodedRows N) q4DecodedRows.data q4EnergyPlan
      (vEnergyTerm 4 q4DecodedRows.data)) :
    ((vQlow 4 : ℚ) : ℝ) <
      V.signedVQuadratic (v13RefMeasure q4DecodedRows N) := by
  have hqlow : 0 < (qlowQ 4).2 := by
    norm_num [qlowQ]
  have hshard : ∀ e ∈ q4EnergyPlan,
      energyShardOK q4DecodedRows.data 4 lr e.1 e.2.1 e.2.2.1 e.2.2.2 = true := by
    intro e he
    exact (henergy e he).1
  have hEd : ∀ e ∈ q4EnergyPlan,
      IV.mem (energyShard q4DecodedRows.data 4 lr e.1 e.2.1 e.2.2.1)
        (∑ i ∈ Finset.Ico e.2.1 e.2.2.1,
          vEnergyTerm 4 q4DecodedRows.data e.1 i) := by
    intro e he
    exact (henergy e he).2
  have hbound : IK.val (qlowQ 4) <
      V.signedVQuadratic (v13RefMeasure q4DecodedRows N) := by
    exact energy_lower_of_plan q4DecodedRows.data 4 lr q4EnergyPlan
      (qlowQ 4) hqlow (vEnergyTerm 4 q4DecodedRows.data)
      (V.signedVQuadratic (v13RefMeasure q4DecodedRows N)) htotal
      q4EnergyPlan_tiles q4EnergyClaims_gt_qlow hshard hEd
  rw [q4ReferenceMeasure_qlow_value] at hbound
  exact hbound

/-! The generated q4 endpoint proof is stated at the canonical q4 base-range
normalization.  Since `V13MeasureNormalization` is proof-irrelevant in its
base-range proof, the same construction-bound estimate transports directly
to the arbitrary `hq` carried by a package leaf. -/
theorem q4_x_endpoint_disk_of_hq
    {hq : SignedVBaseRange 4}
    (N : V13MeasureNormalization hq (v13RefRaw q4DecodedRows))
    (w : ℂ)
    (hw0 : 0 < ‖w‖)
    (hw : ‖w‖ ≤ 1 / 250) :
    V.signedVFullFieldX (v13RefMeasure q4DecodedRows N) w ≤ (vEx 4 : ℝ) := by
  exact q4ReferenceMeasure_x_endpoint_disk N w hw0 hw

/-! Bind the q4 decoded source and generated plan to the common ledger
constructor.  The five restricted field witnesses, shard soundness, and
total identity remain explicit arguments. -/
noncomputable def v13_reference_package_input_q4_of_v13_certificates
    {hq : SignedVBaseRange 4}
    (C : V13NumericCertificates 4 hq q4DecodedRows)
    (lr : IV)
    (lr_sound : IV.mem lr (Real.log (3 / 5 : ℝ)))
    (qlow_value : IK.val (qlowQ 4) = (vQlow 4 : ℝ))
    (field_x : CellSoundnessOn (pieceDomain 4 .x).1 (pieceDomain 4 .x).2
      (fieldUB q4DecodedRows.data 4 lr .x)
      (fun t => V.signedVFullFieldX
        (v13RefMeasure q4DecodedRows C.normalization) (t : ℂ)))
    (field_vlo : CellSoundnessOn (pieceDomain 4 .vlo).1 (pieceDomain 4 .vlo).2
      (fieldUB q4DecodedRows.data 4 lr .vlo)
      (fun t => V.signedVFullFieldV
        (v13RefMeasure q4DecodedRows C.normalization) (t : ℂ)))
    (field_vhi : CellSoundnessOn (pieceDomain 4 .vhi).1 (pieceDomain 4 .vhi).2
      (fieldUB q4DecodedRows.data 4 lr .vhi)
      (fun t => V.signedVFullFieldV
        (v13RefMeasure q4DecodedRows C.normalization) (t : ℂ)))
    (field_zneg : CellSoundnessOn (pieceDomain 4 .zneg).1 (pieceDomain 4 .zneg).2
      (fieldUB q4DecodedRows.data 4 lr .zneg)
      (fun t => V.signedVFullFieldZ
        (v13RefMeasure q4DecodedRows C.normalization) (t : ℂ)))
    (field_zpos : CellSoundnessOn (pieceDomain 4 .zpos).1 (pieceDomain 4 .zpos).2
      (fieldUB q4DecodedRows.data 4 lr .zpos)
      (fun t => V.signedVFullFieldZ
        (v13RefMeasure q4DecodedRows C.normalization) (t : ℂ)))
    (energy : EnergyShardSoundnessFact q4DecodedRows.data 4 lr
      (planOf q4DecodedRows.data 4) (vEnergyTerm 4 q4DecodedRows.data))
    (total : EnergyTotalSoundnessFact
      (v13RefMeasure q4DecodedRows C.normalization) q4DecodedRows.data
      (planOf q4DecodedRows.data 4) (vEnergyTerm 4 q4DecodedRows.data)) :
    V13ReferencePackageInput 4 hq := by
  exact v13ReferencePackageInput_of_pinned q4DecodedRows C lr
    lr_sound qlow_value field_x field_vlo field_vhi field_zneg field_zpos
    energy total

/-- Closure target for the public q = 4 leaf. -/
noncomputable def v13_reference_package_input_q4_closed
    (hq : SignedVBaseRange 4) : V13ReferencePackageInput 4 hq := by
  let N := q4ReferenceNormalization_of_hq hq
  have hrows := q4_decoded_row_bounds_leaf
  obtain ⟨hAx, hAv, hAz, hxb, hvb, hzb, hsigma⟩ :=
    v13RefMeasure_ball_and_sigma q4DecodedRows N
  have hxe := q4_x_endpoint_disk_of_hq N
  have hve := H6CertQ4.v_endpoint_disk hrows N
  have hmx : IK.val q4DecodedRows.data.mx = 1 := by
    have h : q4D.mx = (50000000000000, 50000000000000) := by decide +kernel
    change IK.val q4D.mx = 1
    rw [h]
    norm_num [IK.val]
  have hmv : IK.val q4DecodedRows.data.mv = 5 / 4 := by
    have h : q4D.mv = (62500000000000, 50000000000000) := by decide +kernel
    change IK.val q4D.mv = 5 / 4
    rw [h]
    norm_num [IK.val]
  have hseries : V13DqSeries q4DecodedRows N :=
    DqSeries.v13_dq_series_core q4DecodedRows q4_field_row_facts hrows N hmx hmv
  have henergy := H6CertQ4.energy N hseries
  have htotal := v13_total_fact_of_ballBound q4DecodedRows q4_field_row_facts hrows N
    hAx hAv hAz hxb hvb hzb (planOf q4DecodedRows.data 4)
  have hlower := h6_energy_lower q4DecodedRows N (planOf q4DecodedRows.data 4) henergy htotal
    (by simpa [planOf_q4, q4DecodedRows_data] using q4EnergyPlan_tiles)
    (by simpa [planOf_q4] using q4EnergyClaims_gt_qlow)
    (by norm_num [qlowQ]) q4ReferenceMeasure_qlow_value
  let C := h6_numeric_certificates q4DecodedRows q4_field_row_facts hrows N
    (v13Ax 4) (v13Av 4) (v13Az 4) hAx hAv hAz hxb hvb hzb hsigma hlower
    (H6CertQ4.x_field N hxe) (H6CertQ4.v_field N hve)
    (H6CertQ4.z_field N) (by simpa using v13_alpha_le_q4) hxe hve
  have hc := H6CertQ4.cells N h6_vLogRE_sound
  exact v13ReferencePackageInput_of_pinned q4DecodedRows C vLogRE h6_vLogRE_sound
    q4ReferenceMeasure_qlow_value hc.x hc.vlo hc.vhi hc.zneg hc.zpos henergy htotal

end

end Li2Lean.B3

#print axioms Li2Lean.B3.v13_reference_package_input_q4_closed
