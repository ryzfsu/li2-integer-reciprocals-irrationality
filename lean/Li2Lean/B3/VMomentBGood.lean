/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B3.ActualFrobeniusBlockEntries

namespace Li2Lean.B3

noncomputable section

open scoped BigOperators
open Li2Lean.V.SignedVFrobenius
open Li2Lean.P0.ScaledLucas
open Li2Lean.P0.PositiveTower
open Li2Lean.P0.PositiveTower.EntryGoodness

variable {p : ℕ} [Fact (Nat.Prime p)]

/-- The squared prime-power scale makes every second-moment entry p-integral.
This is the diagonal B input for the v13 scaled pencil. -/
theorem q_sq_mul_vMomentB_good (a : ℤ) (k N : ℕ)
    (hN : N < p * p ^ k) :
    qRatP p k ^ 2 * V.vMomentB a N ∈ GoodP p := by
  unfold V.vMomentB
  rw [Finset.mul_sum]
  apply (GoodP p).sum_mem
  intro r hr
  have hrlt : r < N := Finset.mem_range.mp hr
  have hd : 0 < r + 1 := by omega
  have hbd : r + 1 < p * p ^ k := by omega
  rw [show qRatP p k ^ 2 *
      ((a : ℚ) ^ (N - (r + 1)) *
        ((((r + 1 : ℕ) : ℚ) ^ 2)⁻¹)) =
      (qRatP p k ^ 2 / (((r + 1 : ℕ) : ℚ) ^ 2)) *
        (a : ℚ) ^ (N - (r + 1)) by
    field_simp]
  exact (GoodP p).mul_mem
    (q_sq_div_sq_good k (r + 1) hd hbd)
    ((GoodP p).pow_mem (intRat_good a) _)

end
end Li2Lean.B3

#print axioms Li2Lean.B3.q_sq_mul_vMomentB_good
