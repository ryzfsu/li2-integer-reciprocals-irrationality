/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
/-
  q = 3 lower-energy bridge for the construction-bound reference leaf.

  The generated q3 plan checks provide only plan structure.  The shard
  enclosures and the total identity remain explicit same-source inputs.
  This module does not construct `dual_admissible` or fill the reference
  package leaf.
-/

import Li2Lean.B3.ReferencePackageLeafTemplates
import Li2Lean.B3.ReferencePackageGeneric
import Li2Lean.B3.Q3ReferenceMeasureFacts
import Li2Lean.B3.V13ReferenceEnergyTerm
import Li2Lean.V.EnergyCertI.ISoundGlue
import Li2Lean.V.EnergyCertI.Q3Assembly

namespace Li2Lean

noncomputable section

namespace B3

open V
open V.EnergyCertI
open V.EnergyCertI.IK

/-- The q3 shard and total facts imply the printed lower-energy bound for
the same normalized reference measure (v13 `v-analytic.tex:375-386`). -/
theorem q3_energy_lower_of_shard_and_total
    {hq : SignedVBaseRange 3}
    (C : V13NumericCertificates 3 hq q3DecodedRows)
    (lr : IV)
    (henergy : EnergyShardSoundnessFact q3DecodedRows.data 3 lr
      q3EnergyPlan (vEnergyTerm 3 q3DecodedRows.data))
    (htotal : EnergyTotalSoundnessFact
      (v13RefMeasure q3DecodedRows C.normalization)
      q3DecodedRows.data q3EnergyPlan
      (vEnergyTerm 3 q3DecodedRows.data)) :
    ((vQlow 3 : ℚ) : ℝ) <
      V.signedVQuadratic (v13RefMeasure q3DecodedRows C.normalization) := by
  have hqpos : 0 < (qlowQ 3).2 := by
    norm_num [qlowQ]
  have hshard : ∀ e ∈ q3EnergyPlan,
      energyShardOK q3DecodedRows.data 3 lr
        e.1 e.2.1 e.2.2.1 e.2.2.2 = true := by
    intro e he
    exact (henergy e he).1
  have hEd : ∀ e ∈ q3EnergyPlan,
      IV.mem (energyShard q3DecodedRows.data 3 lr
        e.1 e.2.1 e.2.2.1)
        (∑ i ∈ Finset.Ico e.2.1 e.2.2.1,
          vEnergyTerm 3 q3DecodedRows.data e.1 i) := by
    intro e he
    exact (henergy e he).2
  have hbound : IK.val (qlowQ 3) <
      V.signedVQuadratic (v13RefMeasure q3DecodedRows C.normalization) :=
    energy_lower_of_plan q3DecodedRows.data 3 lr q3EnergyPlan
      (qlowQ 3) hqpos (vEnergyTerm 3 q3DecodedRows.data)
      (V.signedVQuadratic (v13RefMeasure q3DecodedRows C.normalization))
      htotal q3EnergyPlan_tiles q3EnergyClaims_gt_qlow hshard hEd
  simpa only [q3ReferenceMeasure_qlow_value] using hbound

end B3

end

end Li2Lean

#print axioms Li2Lean.B3.q3_energy_lower_of_shard_and_total
