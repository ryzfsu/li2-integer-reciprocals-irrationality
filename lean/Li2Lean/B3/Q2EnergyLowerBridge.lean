/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B3.EnergySoundnessInputs
import Li2Lean.B3.Q2ReferencePackageFacts
import Li2Lean.B3.V13ReferenceEnergyTerm
import Li2Lean.V.EnergyCertI.ISoundGlue
import Li2Lean.V.EnergyCertI.Q2Assembly

namespace Li2Lean.B3

noncomputable section

open V
open V.EnergyCertI
open V.EnergyCertI.IK

/-- The q2 energy certificate and total identity imply the printed v13 lower
bound.  This is the G-3 bridge from the integer plan to the concrete signed-V
quadratic form (v13 `v-analytic.tex:375-386`). -/
theorem q2_energy_lower_of_shard_and_total
    (hq : SignedVBaseRange 2)
    (N : V13MeasureNormalization hq (v13RefRaw q2ReferenceRows))
    (lr : IV)
    (henergy : EnergyShardSoundnessFact q2ReferenceRows.data 2 lr
      q2EnergyPlan (vEnergyTerm 2 q2ReferenceRows.data))
    (htotal : EnergyTotalSoundnessFact (v13RefMeasure q2ReferenceRows N)
      q2ReferenceRows.data q2EnergyPlan (vEnergyTerm 2 q2ReferenceRows.data)) :
    ((vQlow 2 : ℚ) : ℝ) <
      V.signedVQuadratic (v13RefMeasure q2ReferenceRows N) := by
  have hqlow : 0 < (qlowQ 2).2 := by
    norm_num [qlowQ]
  have hshard : ∀ e ∈ q2EnergyPlan,
      energyShardOK q2ReferenceRows.data 2 lr e.1 e.2.1 e.2.2.1 e.2.2.2 = true := by
    intro e he
    exact (henergy e he).1
  have hEd : ∀ e ∈ q2EnergyPlan,
      IV.mem (energyShard q2ReferenceRows.data 2 lr e.1 e.2.1 e.2.2.1)
        (∑ i ∈ Finset.Ico e.2.1 e.2.2.1,
          vEnergyTerm 2 q2ReferenceRows.data e.1 i) := by
    intro e he
    exact (henergy e he).2
  have hbound : IK.val (qlowQ 2) <
      V.signedVQuadratic (v13RefMeasure q2ReferenceRows N) := by
    exact energy_lower_of_plan q2ReferenceRows.data 2 lr q2EnergyPlan
      (qlowQ 2) hqlow (vEnergyTerm 2 q2ReferenceRows.data)
      (V.signedVQuadratic (v13RefMeasure q2ReferenceRows N)) htotal
      q2EnergyPlan_tiles q2EnergyClaims_gt_qlow hshard hEd
  rw [q2ReferenceQLowValue] at hbound
  exact hbound

end

end Li2Lean.B3

#print axioms Li2Lean.B3.q2_energy_lower_of_shard_and_total
