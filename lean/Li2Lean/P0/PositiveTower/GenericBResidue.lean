/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Li2Lean.P0.PositiveTower.GenericTResidue

namespace Li2Lean.P0.PositiveTower

noncomputable section

open Li2Lean
open EntryGoodness

variable {p : ℕ} [Fact (Nat.Prime p)]

private theorem sum_Icc_two_eq_generic {M' : Type*} [AddCommMonoid M']
    (g : ℕ) (f : ℕ → M') (h1 : f 1 = 0) :
    ∑ s ∈ Finset.Icc 2 g, f s = ∑ s ∈ Finset.range g, f (s + 1) := by
  induction g with
  | zero => simp
  | succ g ih =>
      rw [Finset.sum_range_succ, ← ih]
      rcases Nat.eq_zero_or_pos g with hg | hg
      · subst hg
        simp [h1]
      · rw [Finset.sum_Icc_succ_top (by omega)]

/-- The outer numerator in the diagonal B entry, for an arbitrary base. -/
def genericB2 (a : ℤ) (g i s : ℕ) : ℚ :=
  (a : ℚ) ^ i * (-1 : ℚ) ^ (s + 1) *
    (Nat.choose (i + g) (g - (s + 1)) : ℚ)

/-- The inner scaled Q-sum in the diagonal B entry. -/
def genericBI (p : ℕ) (a : ℤ) (k s : ℕ) : ℚ :=
  ∑ r ∈ Finset.range s,
    p0Q (a : ℚ) (r + 1) *
      (qRatP p k / ((r + 1 : ℕ) : ℚ))

theorem generic_qqBB_decomp (a : ℤ) (k g i : ℕ) :
    (qRatP p k) ^ 2 * p0BQQ (a : ℚ) g i =
      (∑ r ∈ Finset.range i,
        p0UQ (a : ℚ) g (i - (r + 1)) *
          (qRatP p k / ((r + 1 : ℕ) : ℚ)) *
          (qRatP p k / ((r + 1 : ℕ) : ℚ))) -
      ∑ s ∈ Finset.range g,
        genericB2 a g i s *
          (qRatP p k / ((s + 1 : ℕ) : ℚ)) *
        genericBI p a k s := by
  unfold p0BQQ
  rw [mul_sub]
  congr 1
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    push_cast
    simp only [div_eq_mul_inv, ← inv_pow]
    ring
  · rw [sum_Icc_two_eq_generic g _ (by simp), ← mul_assoc,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    have hBI : genericBI p a k s = qRatP p k *
        ∑ r ∈ Finset.range s,
          p0Q (a : ℚ) (r + 1) / ((r : ℚ) + 1) := by
      unfold genericBI
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      push_cast
      ring
    rw [hBI]
    simp only [genericB2, Nat.add_sub_cancel]
    push_cast
    ring

end
end Li2Lean.P0.PositiveTower

#print axioms Li2Lean.P0.PositiveTower.generic_qqBB_decomp
