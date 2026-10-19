/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Li2Lean.B3.V13ReferenceEnergyTerm

/-!
Concrete finite cross-row bookkeeping for the v13 evaluator.

`EnergyCertI.crossRow` emits one row for the head of `pts1.drop k`. The
theorem below sums those rows over the complete first chain and exposes the
same signed jump interaction as a single finite list expression. It is an
algebraic bridge only: interval enclosures and the identification with the
analytic measure remain separate E-a..E-d obligations.
-/

namespace Li2Lean

noncomputable section

namespace B3

open V
open V.EnergyCertI
open V.EnergyCertI.IK

/-- One concrete signed jump interaction row for a fixed first-chain point. -/
def vEnergyCrossPoint (p : CP) (pts2 : List CP) : ℝ :=
  (pts2.map fun l =>
    -IK.val p.J * IK.val l.J * vEnergyG (IK.val p.e - IK.val l.e)).sum

@[simp] theorem vEnergyCrossRow_zero (p : CP) (ps pts2 : List CP) :
    vEnergyCrossRow (p :: ps) pts2 0 = vEnergyCrossPoint p pts2 := by
  rfl

theorem vEnergyCrossRow_succ (p : CP) (ps pts2 : List CP) (k : ℕ) :
    vEnergyCrossRow (p :: ps) pts2 (k + 1) =
      vEnergyCrossRow ps pts2 k := by
  simp [vEnergyCrossRow, List.drop_succ_cons]

/-- Summing `crossRow` over all first-chain rows exposes the finite jump sum. -/
theorem vEnergyCrossRows_eq_jump_sum (pts1 pts2 : List CP) :
    (∑ k ∈ Finset.range pts1.length,
      vEnergyCrossRow pts1 pts2 k) =
      (pts1.map (fun p => vEnergyCrossPoint p pts2)).sum := by
  induction pts1 with
  | nil => simp
  | cons p ps ih =>
      rw [List.length_cons, Finset.sum_range_succ']
      have htail :
          (∑ k ∈ Finset.range ps.length,
            vEnergyCrossRow (p :: ps) pts2 (k + 1)) =
            ∑ k ∈ Finset.range ps.length,
              vEnergyCrossRow ps pts2 k := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [vEnergyCrossRow_succ]
      rw [htail, ih]
      simp [vEnergyCrossPoint]
      ring

/-! The expanded form is useful when matching the signed quadratic identity. -/
theorem vEnergyCrossRows_eq_expanded_jump_sum (pts1 pts2 : List CP) :
    (∑ k ∈ Finset.range pts1.length,
      vEnergyCrossRow pts1 pts2 k) =
      (pts1.map fun p =>
        (pts2.map fun l =>
          -IK.val p.J * IK.val l.J *
            vEnergyG (IK.val p.e - IK.val l.e)).sum).sum := by
  simpa [vEnergyCrossPoint] using vEnergyCrossRows_eq_jump_sum pts1 pts2

end B3

end

end Li2Lean

#print axioms Li2Lean.B3.vEnergyCrossRows_eq_jump_sum
#print axioms Li2Lean.B3.vEnergyCrossRows_eq_expanded_jump_sum
