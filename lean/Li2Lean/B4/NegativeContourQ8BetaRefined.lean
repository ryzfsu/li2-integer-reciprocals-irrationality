/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B4.NegativeContourQ8BetaBound

open Set

namespace Li2Lean.B4

noncomputable section

/-- A sharpened rational majorant for the q=8 beta kernel.  The looser
`709/5000` certificate is retained in `NegativeContourQ8BetaBound`; this
constant is the one used in the strict rate check. -/
def hpNegativeQ8RefinedM : ℝ := 1407 / 10000

theorem hpNegativeQ8RefinedM_cubic {s : ℝ} (hs : 0 ≤ s) :
    s ^ 2 * (1 - s) ≤ hpNegativeQ8RefinedM * (1 + s ^ 2 / 8) := by
  have hcert :
      4 * (1 + hpNegativeQ8RefinedM * (-(1 / 8 : ℝ))) ^ 3 ≤
        27 * hpNegativeQ8RefinedM := by
    norm_num [hpNegativeQ8RefinedM]
  have hMz : 0 < 1 + hpNegativeQ8RefinedM * (-(1 / 8 : ℝ)) := by
    norm_num [hpNegativeQ8RefinedM]
  have hmain := hp_negative_cubic_certificate
    (z := -(1 / 8 : ℝ)) hs hMz hcert
  convert hmain using 1 <;> ring

theorem hpNegativeQ8RefinedM_sq :
    hpNegativeQ8RefinedM ^ 2 = (1979649 / 100000000 : ℝ) := by
  norm_num [hpNegativeQ8RefinedM]

/-- Refined q=8 pointwise bracket bound, still following the square-root
AM--GM reduction in v13 `hp-tail.tex:202-215`. -/
theorem hp_negative_bracket_div_q8_refined {t u : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (0 : ℝ) 1) :
    t ^ 2 * u ^ 2 * ((1 - t) * (1 - u)) /
        (1 + t * u / 8) ^ 2 ≤ hpNegativeQ8RefinedM ^ 2 := by
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
  have hcore := hpNegativeQ8RefinedM_cubic hs0
  have hcore0 : 0 ≤ s ^ 2 * (1 - s) := by
    exact mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hs1)
  have hnum' :
      (s ^ 2 * (1 - s)) ^ 2 ≤
        (hpNegativeQ8RefinedM * (1 + s ^ 2 / 8)) ^ 2 := by
    exact pow_le_pow_left₀ hcore0 hcore 2
  have hden : 0 < (1 + t * u / 8) ^ 2 := by positivity
  apply (div_le_iff₀ hden).2
  calc
    t ^ 2 * u ^ 2 * ((1 - t) * (1 - u)) ≤
        (s ^ 2 * (1 - s)) ^ 2 := hnum
    _ ≤ (hpNegativeQ8RefinedM * (1 + s ^ 2 / 8)) ^ 2 := hnum'
    _ = hpNegativeQ8RefinedM ^ 2 * (1 + t * u / 8) ^ 2 := by
      rw [hs_sq]
      ring

end

end Li2Lean.B4

#print axioms Li2Lean.B4.hp_negative_bracket_div_q8_refined
