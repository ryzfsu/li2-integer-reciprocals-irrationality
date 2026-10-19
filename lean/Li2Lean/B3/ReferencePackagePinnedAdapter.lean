/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Construction-bound adapter for the generated energy plan and evaluator.
The adapter keeps the existing `V13ReferencePackageInput` boundary, but does
not accept caller-selected `plan` or `term` values: both are fixed by the
decoded base and the construction's `vEnergyTerm`.

The q-indexed plans are generated in `EnergyCertI`; the empty alternative is
reserved for decoded bases outside the v13 range. The caller still has to
provide the corresponding shard and total proofs.
-/

import Li2Lean.B3.ReferencePackageGeneric
import Li2Lean.B3.V13ReferenceEnergyTerm
import Li2Lean.V.EnergyCertI.Q2Assembly
import Li2Lean.V.EnergyCertI.Q3Assembly
import Li2Lean.V.EnergyCertI.Q4Assembly
import Li2Lean.V.EnergyCertI.Q5Assembly
import Li2Lean.V.EnergyCertI.Q6Assembly
import Li2Lean.V.EnergyCertI.Q7Assembly

namespace Li2Lean

noncomputable section

namespace B3

open V
open V.EnergyCertI
open V.EnergyCertI.IK

/-! The argument order follows the source construction: decoded rows first,
then the q-indexed certificate plan. -/
def planOf (D : IData) (q : ℕ) : List (EKind × ℕ × ℕ × Int) :=
  if q = 2 then q2EnergyPlan else
    if q = 3 then q3EnergyPlan else
      if q = 4 then q4EnergyPlan else
        if q = 5 then q5EnergyPlan else
          if q = 6 then q6EnergyPlan else
            if q = 7 then q7EnergyPlan else []

@[simp] theorem planOf_q2 (D : IData) : planOf D 2 = q2EnergyPlan := by
  simp [planOf]

@[simp] theorem planOf_q5 (D : IData) : planOf D 5 = q5EnergyPlan := by
  simp [planOf]

@[simp] theorem planOf_q3 (D : IData) : planOf D 3 = q3EnergyPlan := by
  simp [planOf]

@[simp] theorem planOf_q4 (D : IData) : planOf D 4 = q4EnergyPlan := by
  simp [planOf]

@[simp] theorem planOf_q6 (D : IData) : planOf D 6 = q6EnergyPlan := by
  simp [planOf]

@[simp] theorem planOf_q7 (D : IData) : planOf D 7 = q7EnergyPlan := by
  simp [planOf]

/-! Bind all free ledger inputs to the same decoded source and measure. The
field arguments are already restricted by `CellSoundnessOn`; the energy and
total arguments use the fixed `planOf`/`vEnergyTerm` pair. -/
noncomputable def v13ReferencePackageInput_of_pinned
    {q : ℕ} {hq : SignedVBaseRange q}
    (D : V13DecodedRows q)
    (C : V13NumericCertificates q hq D)
    (lr : IV)
    (lr_sound : IK.IV.mem lr (Real.log (3 / 5 : ℝ)))
    (qlow_value : IK.val (V.EnergyCertI.qlowQ q) = (vQlow q : ℝ))
    (field_x : CellSoundnessOn (pieceDomain q .x).1 (pieceDomain q .x).2
      (V.EnergyCertI.fieldUB D.data q lr .x)
      (fun t => V.signedVFullFieldX
        (v13RefMeasure D C.normalization) (t : ℂ)))
    (field_vlo : CellSoundnessOn (pieceDomain q .vlo).1 (pieceDomain q .vlo).2
      (V.EnergyCertI.fieldUB D.data q lr .vlo)
      (fun t => V.signedVFullFieldV
        (v13RefMeasure D C.normalization) (t : ℂ)))
    (field_vhi : CellSoundnessOn (pieceDomain q .vhi).1 (pieceDomain q .vhi).2
      (V.EnergyCertI.fieldUB D.data q lr .vhi)
      (fun t => V.signedVFullFieldV
        (v13RefMeasure D C.normalization) (t : ℂ)))
    (field_zneg : CellSoundnessOn (pieceDomain q .zneg).1 (pieceDomain q .zneg).2
      (V.EnergyCertI.fieldUB D.data q lr .zneg)
      (fun t => V.signedVFullFieldZ
        (v13RefMeasure D C.normalization) (t : ℂ)))
    (field_zpos : CellSoundnessOn (pieceDomain q .zpos).1 (pieceDomain q .zpos).2
      (V.EnergyCertI.fieldUB D.data q lr .zpos)
      (fun t => V.signedVFullFieldZ
        (v13RefMeasure D C.normalization) (t : ℂ)))
    (energy : EnergyShardSoundnessFact D.data q lr
      (planOf D.data q) (vEnergyTerm q D.data))
    (total : EnergyTotalSoundnessFact (v13RefMeasure D C.normalization)
      D.data (planOf D.data q) (vEnergyTerm q D.data)) :
    V13ReferencePackageInput q hq := by
  let P : VReferencePackage q hq := vReferencePackage_of_rows D C
  have hP : P.measure = v13RefMeasure D C.normalization := by
    rfl
  refine ⟨{
    reference := P
    source := D
    lr := lr
    lr_sound := lr_sound
    plan := planOf D.data q
    term := vEnergyTerm q D.data
    qlow_value := qlow_value
    field_x := ?_
    field_vlo := ?_
    field_vhi := ?_
    field_zneg := ?_
    field_zpos := ?_
    energy := energy
    total := ?_ }⟩
  · simpa [hP] using field_x
  · simpa [hP] using field_vlo
  · simpa [hP] using field_vhi
  · simpa [hP] using field_zneg
  · simpa [hP] using field_zpos
  · simpa [hP] using total

end B3

end

end Li2Lean

#print axioms Li2Lean.B3.v13ReferencePackageInput_of_pinned
