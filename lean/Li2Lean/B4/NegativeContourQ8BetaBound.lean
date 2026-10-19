/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B4.NegativeTailElementary

open Set

namespace Li2Lean.B4

noncomputable section

/-- Rational majorant for the q=8 negative beta saddle factor. -/
def hpNegativeQ8M : ℝ := 709 / 5000

theorem hpNegativeQ8M_cubic {s : ℝ} (hs : 0 ≤ s) :
    s ^ 2 * (1 - s) ≤ hpNegativeQ8M * (1 + s ^ 2 / 8) := by
  have hcert :
      4 * (1 + hpNegativeQ8M * (-(1 / 8 : ℝ))) ^ 3 ≤
        27 * hpNegativeQ8M := by
    norm_num [hpNegativeQ8M]
  have hMz : 0 < 1 + hpNegativeQ8M * (-(1 / 8 : ℝ)) := by
    norm_num [hpNegativeQ8M]
  have hmain := hp_negative_cubic_certificate
    (z := -(1 / 8 : ℝ)) hs hMz hcert
  calc
    s ^ 2 * (1 - s) ≤
        hpNegativeQ8M * (1 - (-(1 / 8 : ℝ)) * s ^ 2) := hmain
    _ = hpNegativeQ8M * (1 + s ^ 2 / 8) := by ring

theorem hpNegativeQ8M_sq_le_2013 :
    hpNegativeQ8M ^ 2 ≤ (2013 / 100000 : ℝ) := by
  norm_num [hpNegativeQ8M]

/-- Pointwise q=8 bound for the bracket in v13 `hp-tail.tex:202-215`.
The square-root substitution and AM--GM reduce the two variables to the
one-variable cubic certificate above. -/
theorem hp_negative_bracket_div_q8 {t u : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (0 : ℝ) 1) :
    t ^ 2 * u ^ 2 * ((1 - t) * (1 - u)) /
        (1 + t * u / 8) ^ 2 ≤ (2013 / 100000 : ℝ) := by
  have htu0 : 0 ≤ t * u := mul_nonneg ht.1 hu.1
  let s : ℝ := Real.sqrt (t * u)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs_sq : s ^ 2 = t * u := by
    dsimp [s]
    exact Real.sq_sqrt htu0
  have htu_le : t * u ≤ 1 := by
    have h := mul_le_mul ht.2 hu.2 hu.1 (by norm_num : (0 : ℝ) ≤ 1)
    simpa using h
  have hs1 : s ≤ 1 := by
    dsimp [s]
    exact (Real.sqrt_le_iff).2 ⟨by norm_num, by nlinarith [htu_le]⟩
  have hamgm := hp_sqrt_amgm ht hu
  have hnum :
      t ^ 2 * u ^ 2 * ((1 - t) * (1 - u)) ≤
        (s ^ 2 * (1 - s)) ^ 2 := by
    calc
      t ^ 2 * u ^ 2 * ((1 - t) * (1 - u)) =
          (t * u) ^ 2 * ((1 - t) * (1 - u)) := by ring
      _ = s ^ 4 * ((1 - t) * (1 - u)) := by rw [← hs_sq]; ring
      _ ≤ s ^ 4 * (1 - s) ^ 2 := by
        exact mul_le_mul_of_nonneg_left hamgm (by positivity)
      _ = (s ^ 2 * (1 - s)) ^ 2 := by ring
  have hcore := hpNegativeQ8M_cubic hs0
  have hcore0 : 0 ≤ s ^ 2 * (1 - s) := by
    exact mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hs1)
  have hmajor0 : 0 ≤ hpNegativeQ8M * (1 + s ^ 2 / 8) := by
    have hM : 0 ≤ hpNegativeQ8M := by norm_num [hpNegativeQ8M]
    have hden : 0 ≤ 1 + s ^ 2 / 8 := by positivity
    exact mul_nonneg hM hden
  have hnum' :
      (s ^ 2 * (1 - s)) ^ 2 ≤
        (hpNegativeQ8M * (1 + s ^ 2 / 8)) ^ 2 :=
    pow_le_pow_left₀ hcore0 hcore 2
  have hden : 0 < (1 + t * u / 8) ^ 2 := by positivity
  apply (div_le_iff₀ hden).2
  calc
    t ^ 2 * u ^ 2 * ((1 - t) * (1 - u)) ≤
        (s ^ 2 * (1 - s)) ^ 2 := hnum
    _ ≤ (hpNegativeQ8M * (1 + s ^ 2 / 8)) ^ 2 := hnum'
    _ = hpNegativeQ8M ^ 2 * (1 + t * u / 8) ^ 2 := by
      rw [hs_sq]
      ring
    _ ≤ (2013 / 100000 : ℝ) * (1 + t * u / 8) ^ 2 := by
      exact mul_le_mul_of_nonneg_right hpNegativeQ8M_sq_le_2013 (sq_nonneg _)

end

end Li2Lean.B4

#print axioms Li2Lean.B4.hp_negative_bracket_div_q8
