/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/

import Mathlib

namespace Li2Lean.P0.Q11Data

noncomputable section

/-!
Arithmetic of the q = 11 Frobenius index sequence.

The nonvanishing interface uses the seed index `M = 4` and auxiliary prime
`p = 197`; the actual endpoint sequence is `M * p ^ (k + 1)`. These lemmas
discharge only the elementary index obligations. They do not assert the
seed-transport or Frobenius congruences, which remain explicit fields of
`P0FrobeniusTowerCertificate`.
-/

def q11TowerIndex (k : ℕ) : ℕ := 4 * 197 ^ (k + 1)

theorem q11TowerIndex_pos (k : ℕ) : 0 < q11TowerIndex k := by
  unfold q11TowerIndex
  positivity

theorem q11TowerIndex_multiple_four (k : ℕ) :
    4 ∣ q11TowerIndex k := by
  refine ⟨197 ^ (k + 1), ?_⟩
  unfold q11TowerIndex
  ring

theorem q11TowerIndex_ge_eight (k : ℕ) :
    8 ≤ q11TowerIndex k := by
  unfold q11TowerIndex
  have hk : 1 ≤ k + 1 := by omega
  have hpow : 197 ≤ 197 ^ (k + 1) := by
    simpa using (Nat.pow_le_pow_right (n := 197) (by norm_num) hk)
  nlinarith

theorem q11TowerIndex_strictMono :
    StrictMono q11TowerIndex := by
  intro i j hij
  unfold q11TowerIndex
  have hprime : 1 < (197 : ℕ) := by norm_num
  have hpow : 197 ^ (i + 1) < 197 ^ (j + 1) := by
    exact Nat.pow_lt_pow_right hprime (by omega)
  exact (Nat.mul_lt_mul_left (by norm_num : 0 < (4 : ℕ))).2 hpow

theorem q11SeedTowerIndex_conditions :
    0 < (4 : ℕ) ∧ 4 ∣ (4 : ℕ) ∧ Nat.Prime 197 ∧
      2 * 4 + 4 / 2 < 197 := by
  norm_num

end

end Li2Lean.P0.Q11Data
