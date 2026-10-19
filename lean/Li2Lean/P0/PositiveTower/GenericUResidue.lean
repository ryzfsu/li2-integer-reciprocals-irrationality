/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.Nonvanishing
import Li2Lean.P0.PositiveTower.GenericLucas

namespace Li2Lean.P0.PositiveTower

noncomputable section

open Li2Lean

variable {p : ℕ} [Fact (Nat.Prime p)]

theorem p0U_residue_lucas_M4 (a : ℤ) (A k v : ℕ) (hv : v < p ^ k) :
    ((p0UQ (a : ℚ) (2 * p ^ k) (A * p ^ k + v) : ℚ) : ZMod p) =
      (a : ZMod p) ^ v *
        ((p0UQ (a : ℚ) 2 A : ℚ) : ZMod p) := by
  have hU (h i : ℕ) :
      ((p0UQ (a : ℚ) h i : ℚ) : ZMod p) =
        (a : ZMod p) ^ i * (Nat.choose (i + h) h : ZMod p) := by
    have hU_int : p0UQ (a : ℚ) h i =
        ((a ^ i * (Nat.choose (i + h) h : ℤ) : ℤ) : ℚ) := by
      simp only [p0UQ, Int.cast_mul, Int.cast_pow, Int.cast_natCast]
    rw [hU_int, Rat.cast_intCast]
    simp only [Int.cast_mul, Int.cast_pow, Int.cast_natCast]
  have hchoose :
      (Nat.choose (A * p ^ k + v + 2 * p ^ k) (2 * p ^ k) : ZMod p) =
        (Nat.choose (A + 2) 2 : ZMod p) := by
    apply (ZMod.natCast_eq_natCast_iff _ _ p).2
    have hindex : A * p ^ k + v + 2 * p ^ k = (A + 2) * p ^ k + v := by
      ring
    rw [hindex]
    exact (choose_pow_add_two_mul_modEq (p := p) (u := A) (r := v) hv)
  have hpowq : (a : ZMod p) ^ p ^ k = (a : ZMod p) := by
    clear hchoose hv
    induction k with
    | zero => simp
    | succ k ih =>
        rw [pow_succ p k, pow_mul, ih]
        exact ZMod.pow_card (a : ZMod p)
  have hpow : (a : ZMod p) ^ (A * p ^ k) = (a : ZMod p) ^ A := by
    rw [Nat.mul_comm A (p ^ k), pow_mul, hpowq]
  rw [hU (2 * p ^ k) (A * p ^ k + v), hU 2 A,
    hchoose, pow_add, hpow]
  ac_rfl

end
end Li2Lean.P0.PositiveTower

#print axioms Li2Lean.P0.PositiveTower.p0U_residue_lucas_M4
