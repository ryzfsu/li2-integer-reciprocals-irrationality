/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
/-
  The q = 5 energy lower bridge for the H6 reference-package leaf.

  The finite shard checks and the total identity remain explicit inputs.  This
  module only applies the common v13 plan soundness theorem to those inputs.
-/

import Li2Lean.B3.H6ReferencePackageTemplates
import Li2Lean.B3.F6Alpha
import Li2Lean.V.EnergyCertI.ISoundGlue

namespace Li2Lean

noncomputable section

namespace B3

open V
open V.EnergyCertI
open V.EnergyCertI.IK

theorem q5_energy_lower_of_shard_and_total
    (hq : SignedVBaseRange 5)
    (N : V13MeasureNormalization hq (v13RefRaw q5DecodedReferenceRows))
    (lr : IV)
    (henergy : EnergyShardSoundnessFact q5DecodedReferenceRows.data 5 lr
      q5EnergyPlan (vEnergyTerm 5 q5DecodedReferenceRows.data))
    (htotal : EnergyTotalSoundnessFact
      (v13RefMeasure q5DecodedReferenceRows N)
      q5DecodedReferenceRows.data q5EnergyPlan
      (vEnergyTerm 5 q5DecodedReferenceRows.data)) :
    ((vQlow 5 : ℚ) : ℝ) <
      V.signedVQuadratic (v13RefMeasure q5DecodedReferenceRows N) := by
  have hqpos : 0 < (qlowQ 5).2 := by
    norm_num [qlowQ]
  have htiles : energyPlanTiles q5DecodedReferenceRows.data q5EnergyPlan = true := by
    simpa [q5DecodedReferenceRows_data] using q5EnergyPlan_tiles
  have hclaims : claimsGt q5EnergyPlan (qlowQ 5) = true :=
    q5EnergyClaims_gt_qlow
  have hshard : ∀ e ∈ q5EnergyPlan,
      energyShardOK q5DecodedReferenceRows.data 5 lr
        e.1 e.2.1 e.2.2.1 e.2.2.2 = true := by
    intro e he
    exact (henergy e he).1
  have hEd : ∀ e ∈ q5EnergyPlan,
      IV.mem (energyShard q5DecodedReferenceRows.data 5 lr
        e.1 e.2.1 e.2.2.1)
        (∑ i ∈ Finset.Ico e.2.1 e.2.2.1,
          vEnergyTerm 5 q5DecodedReferenceRows.data e.1 i) := by
    intro e he
    exact (henergy e he).2
  have hbound : IK.val (qlowQ 5) <
      V.signedVQuadratic (v13RefMeasure q5DecodedReferenceRows N) :=
    energy_lower_of_plan q5DecodedReferenceRows.data 5 lr q5EnergyPlan
      (qlowQ 5) hqpos (fun k i => vEnergyTerm 5 q5DecodedReferenceRows.data k i)
      (V.signedVQuadratic (v13RefMeasure q5DecodedReferenceRows N)) htotal htiles
      hclaims hshard hEd
  simpa only [q5ReferenceMeasure_qlow_value] using hbound

end B3

end

end Li2Lean

#print axioms Li2Lean.B3.q5_energy_lower_of_shard_and_total
