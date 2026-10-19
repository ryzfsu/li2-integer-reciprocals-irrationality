/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
/-
  q = 7 lower-energy bridge for the construction-bound reference leaf.

  The generated q7 plan checks provide only plan structure.  The shard
  enclosures and the total identity remain explicit same-source inputs.
-/

import Li2Lean.B3.ReferencePackageLeafTemplates
import Li2Lean.B3.ReferencePackageGeneric
import Li2Lean.B3.Q7ReferenceMeasureFacts
import Li2Lean.B3.V13ReferenceEnergyTerm
import Li2Lean.V.EnergyCertI.ISoundGlue
import Li2Lean.V.EnergyCertI.Q7Assembly

namespace Li2Lean

noncomputable section

namespace B3

open V
open V.EnergyCertI
open V.EnergyCertI.IK

/-! The normalization-level bridge is the form used by the q7 package
adapter.  It keeps the semantic measure explicit, so constructing the
numeric certificate does not have to refer to a certificate that is still
being assembled. -/
theorem q7_energy_lower_of_shard_and_total_of_normalization
    {hq : SignedVBaseRange 7}
    (N : V13MeasureNormalization hq (v13RefRaw q7ReferenceRows))
    (lr : IV)
    (henergy : EnergyShardSoundnessFact q7ReferenceRows.data 7 lr
      q7EnergyPlan (vEnergyTerm 7 q7ReferenceRows.data))
    (htotal : EnergyTotalSoundnessFact
      (v13RefMeasure q7ReferenceRows N)
      q7ReferenceRows.data q7EnergyPlan
      (vEnergyTerm 7 q7ReferenceRows.data)) :
    ((vQlow 7 : ℚ) : ℝ) <
      V.signedVQuadratic (v13RefMeasure q7ReferenceRows N) := by
  have hqpos : 0 < (qlowQ 7).2 := by
    norm_num [qlowQ]
  have hshard : ∀ e ∈ q7EnergyPlan,
      energyShardOK q7ReferenceRows.data 7 lr
        e.1 e.2.1 e.2.2.1 e.2.2.2 = true := by
    intro e he
    exact (henergy e he).1
  have hEd : ∀ e ∈ q7EnergyPlan,
      IV.mem (energyShard q7ReferenceRows.data 7 lr
        e.1 e.2.1 e.2.2.1)
        (∑ i ∈ Finset.Ico e.2.1 e.2.2.1,
          vEnergyTerm 7 q7ReferenceRows.data e.1 i) := by
    intro e he
    exact (henergy e he).2
  have hbound : IK.val (qlowQ 7) <
      V.signedVQuadratic (v13RefMeasure q7ReferenceRows N) :=
    energy_lower_of_plan q7ReferenceRows.data 7 lr q7EnergyPlan
      (qlowQ 7) hqpos (vEnergyTerm 7 q7ReferenceRows.data)
      (V.signedVQuadratic (v13RefMeasure q7ReferenceRows N))
      htotal q7EnergyPlan_tiles q7EnergyClaims_gt_qlow hshard hEd
  simpa only [q7ReferenceMeasure_qlow_value] using hbound
/-- The q7 shard and total facts imply the printed lower-energy bound for
the same normalized reference measure. -/
theorem q7_energy_lower_of_shard_and_total
    {hq : SignedVBaseRange 7}
    (C : V13NumericCertificates 7 hq q7ReferenceRows)
    (lr : IV)
    (henergy : EnergyShardSoundnessFact q7ReferenceRows.data 7 lr
      q7EnergyPlan (vEnergyTerm 7 q7ReferenceRows.data))
    (htotal : EnergyTotalSoundnessFact
      (v13RefMeasure q7ReferenceRows C.normalization)
      q7ReferenceRows.data q7EnergyPlan
      (vEnergyTerm 7 q7ReferenceRows.data)) :
    ((vQlow 7 : ℚ) : ℝ) <
      V.signedVQuadratic (v13RefMeasure q7ReferenceRows C.normalization) := by
  have hqpos : 0 < (qlowQ 7).2 := by
    norm_num [qlowQ]
  have hshard : ∀ e ∈ q7EnergyPlan,
      energyShardOK q7ReferenceRows.data 7 lr
        e.1 e.2.1 e.2.2.1 e.2.2.2 = true := by
    intro e he
    exact (henergy e he).1
  have hEd : ∀ e ∈ q7EnergyPlan,
      IV.mem (energyShard q7ReferenceRows.data 7 lr
        e.1 e.2.1 e.2.2.1)
        (∑ i ∈ Finset.Ico e.2.1 e.2.2.1,
          vEnergyTerm 7 q7ReferenceRows.data e.1 i) := by
    intro e he
    exact (henergy e he).2
  have hbound : IK.val (qlowQ 7) <
      V.signedVQuadratic (v13RefMeasure q7ReferenceRows C.normalization) :=
    energy_lower_of_plan q7ReferenceRows.data 7 lr q7EnergyPlan
      (qlowQ 7) hqpos (vEnergyTerm 7 q7ReferenceRows.data)
      (V.signedVQuadratic (v13RefMeasure q7ReferenceRows C.normalization))
      htotal q7EnergyPlan_tiles q7EnergyClaims_gt_qlow hshard hEd
  simpa only [q7ReferenceMeasure_qlow_value] using hbound

end B3

end

end Li2Lean
