/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.IntegerizationBottom

namespace Li2Lean.P0.Integerization

noncomputable section

open Li2Lean

/-!
## Parameterized arithmetic primitives for the positive-base integerizer

These lemmas isolate the two denominator facts used by the q-parametric
row-scale proof. They do not assert row integrality, determinant
integrality, a valuation profile, or an asymptotic rate.
-/

theorem p0UQ_natCast_of_nat (q g i : ℕ) :
    p0UQ (q : ℚ) g i =
      ((q ^ i * Nat.choose (i + g) g : ℕ) : ℚ) := by
  simp [p0UQ, Nat.cast_mul, Nat.cast_pow]

theorem p0Q_scaled_natCast_of_two_le {q s : ℕ} (hq : 2 ≤ q) :
    ∃ z : ℤ,
      (((q - 1 : ℕ) ^ s : ℚ) * p0Q (q : ℚ) s) = z := by
  have hq1 : 1 < q := by omega
  have hq1z : ((q : ℚ) - 1) ≠ 0 := by
    have hqcast : (1 : ℚ) < (q : ℚ) := by exact_mod_cast hq1
    linarith
  refine ⟨(q ^ s - (q - 1) ^ s : ℤ), ?_⟩
  rw [p0Q]
  have hcast : (((q - 1 : ℕ) ^ s : ℚ)) = ((q : ℚ) - 1) ^ s := by
    norm_num [Nat.cast_sub (by omega : 1 ≤ q)]
  rw [hcast]
  have hpow : ((q : ℚ) - 1)⁻¹ ^ s * ((q : ℚ) - 1) ^ s = 1 := by
    rw [← mul_pow]
    simp [hq1z]
  calc
    ((q : ℚ) - 1) ^ s * p0Q (q : ℚ) s =
        ((q : ℚ) - 1) ^ s *
          ((q : ℚ) ^ s * ((q : ℚ) - 1)⁻¹ ^ s - 1) := by
            simp [p0Q, div_eq_mul_inv, mul_pow]
    _ = (q : ℚ) ^ s *
          (((q : ℚ) - 1)⁻¹ ^ s * ((q : ℚ) - 1) ^ s) -
          ((q : ℚ) - 1) ^ s := by ring
    _ = (q : ℚ) ^ s - ((q : ℚ) - 1) ^ s := by rw [hpow]; ring
    _ = ((q ^ s - (q - 1) ^ s : ℤ) : ℚ) := by
      push_cast
      rfl

end

end Li2Lean.P0.Integerization
