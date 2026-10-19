/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B4.HPBetaIdentity
import Li2Lean.B4.NegativeContourQ8BetaRate

open Set

namespace Li2Lean.B4.TailAnalytic

noncomputable section

open Li2Lean.B4

/-- The concrete q = 8 beta remainder estimate for the v13 `hpRR` family.

This is the beta-integral input used by the exceptional contour decay bridge;
the pointwise kernel bound is the refined q = 8 certificate from
`NegativeContourQ8BetaRefined`.  The construction is fixed by `hpRR`, so the
statement does not quantify over an arbitrary remainder sequence.
-/
theorem hpRR_q8_beta_bound (n : ℕ) :
    |hpRR n (((-(8 : ℤ) : ℤ) : ℝ)⁻¹)| ≤
      (2 * n + 1 : ℝ) * 4 ^ n * (8 : ℝ)⁻¹ ^ (3 * n + 2) *
        hpNegativeQ8BetaM ^ n := by
  have hbr : ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
      t ^ 2 * u ^ 2 * ((1 - t) * (1 - u)) /
          (1 - (-(8 : ℝ)⁻¹) * t * u) ^ 2 ≤ hpNegativeQ8BetaM := by
    intro t ht u hu
    have h := hp_negative_bracket_div_q8_refined ht hu
    have hden : (1 - (-(8 : ℝ)⁻¹) * t * u) ^ 2 =
        (1 + t * u / 8) ^ 2 := by
      norm_num
      ring
    rw [hden]
    simpa [hpNegativeQ8BetaM] using h
  have h := hpRR_abs_le_of_bracket n
    (z := -(8 : ℝ)⁻¹) (Cz := 1) (M2 := hpNegativeQ8BetaM)
    (by norm_num) (by norm_num) hpNegativeQ8BetaM_nonneg
    (fun t ht u hu => by
      have htu : 0 ≤ t * u := mul_nonneg ht.1 hu.1
      have hbase : 1 ≤ 1 - (-(8 : ℝ)⁻¹) * t * u := by
        have hq0 : 0 ≤ (8 : ℝ)⁻¹ := by norm_num
        have hq : 0 ≤ (8 : ℝ)⁻¹ * t * u :=
          mul_nonneg (mul_nonneg hq0 ht.1) hu.1
        nlinarith
      have hden2 : 1 ≤ (1 - (-(8 : ℝ)⁻¹) * t * u) ^ 2 :=
        one_le_pow₀ hbase
      have htu_le : t * u ≤ 1 := mul_le_one₀ ht.2 hu.1 hu.2
      have hdenpos : 0 < (1 - (-(8 : ℝ)⁻¹) * t * u) ^ 2 := by
        positivity
      rw [abs_of_nonneg (by positivity), div_le_iff₀ hdenpos]
      simpa using htu_le.trans hden2)
    (fun t ht u hu => by
      have h1t : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
      have h1u : 0 ≤ 1 - u := sub_nonneg.mpr hu.2
      have hdenpos : 0 < (1 - (-(8 : ℝ)⁻¹) * t * u) ^ 2 := by
        have htu : 0 ≤ t * u := mul_nonneg ht.1 hu.1
        have hbase : 1 ≤ 1 - (-(8 : ℝ)⁻¹) * t * u := by
          have hq0 : 0 ≤ (8 : ℝ)⁻¹ := by norm_num
          have hq : 0 ≤ (8 : ℝ)⁻¹ * t * u :=
            mul_nonneg (mul_nonneg hq0 ht.1) hu.1
          nlinarith
        positivity
      have hnum : 0 ≤ t ^ 2 * u ^ 2 * (1 - t) * (1 - u) /
          (1 - (-(8 : ℝ)⁻¹) * t * u) ^ 2 := by
        positivity
      rw [abs_of_nonneg hnum]
      simpa [mul_assoc, mul_left_comm, mul_comm] using hbr t ht u hu)
  have hzcast : (((-(8 : ℤ) : ℤ) : ℝ)⁻¹) = -(8 : ℝ)⁻¹ := by
    norm_num
  rw [hzcast]
  have hzabs : |(-(8 : ℝ)⁻¹)| = (8 : ℝ)⁻¹ := by
    rw [abs_neg, abs_of_pos]
    norm_num
  simpa [hzabs] using h

end

end Li2Lean.B4.TailAnalytic

#print axioms Li2Lean.B4.TailAnalytic.hpRR_q8_beta_bound
