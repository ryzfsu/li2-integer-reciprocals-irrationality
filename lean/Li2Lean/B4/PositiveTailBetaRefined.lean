/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B4.PositiveTailBeta
import Li2Lean.B4.NegativeTailElementary

/-!
Generated (compiled in the release build).  Target path in the release:
`Li2Lean/B4/PositiveTailBetaRefined.lean`.  Mirrors
`NegativeContourQ8BetaRefined.lean` (3f9e06c3) line for line, with the
sign of the denominator parameter flipped: z = +1/12 instead of -1/8.

Refined positive beta bracket for every real q >= 12 (bases a >= 12),
v13 `hp-tail.tex:198-220`:

  t^2 u^2 (1-t)(1-u) / (1 - t u / q)^2 <= M^2,  M = 154/1000,
  hence  hpPositiveBetaKernel q n t u <= (12/11)^2 * (M^2)^n.

Certificate: AM--GM (`hp_sqrt_amgm`) reduces to s = sqrt(tu); the cubic
`s^2(1-s) <= M(1 - s^2/12)` is `hp_negative_cubic_certificate` at z = 1/12
with the rational check 4(1 + M/12)^3 <= 27 M, i.e. the integer inequality
4 * 6077^3 * 500 = 448846357066000 <= 449064000000000 = 27 * 77 * 6000^3.
The step 1 - s^2/12 <= 1 - s^2/q uses `hp_positive_qinv_le`.
True sup at q = 12: 0.0236921098 at t = u = 0.675218 (AM--GM tight on the diagonal); M^2 = 0.023716.
-/

open Set

namespace Li2Lean.B4

noncomputable section

/-- Refined rational majorant for the positive beta saddle factor (q >= 12).
Replaces the `(4/27)^2 (12/11)^2` constant of `hp_positive_beta_kernel_le`,
whose rate is 1.093 > 1. -/
def hpPositiveRefinedM : ℝ := 154 / 1000

theorem hpPositiveRefinedM_nonneg : 0 ≤ hpPositiveRefinedM := by
  norm_num [hpPositiveRefinedM]

theorem hpPositiveRefinedM_cubic {s : ℝ} (hs : 0 ≤ s) :
    s ^ 2 * (1 - s) ≤ hpPositiveRefinedM * (1 - s ^ 2 / 12) := by
  have hcert :
      4 * (1 + hpPositiveRefinedM * (1 / 12 : ℝ)) ^ 3 ≤
        27 * hpPositiveRefinedM := by
    norm_num [hpPositiveRefinedM]
  have hMz : 0 < 1 + hpPositiveRefinedM * (1 / 12 : ℝ) := by
    norm_num [hpPositiveRefinedM]
  have hmain := hp_negative_cubic_certificate
    (z := (1 / 12 : ℝ)) hs hMz hcert
  convert hmain using 1 <;> ring

/-- Uniform in `q >= 12`: the larger `q`, the larger the right-hand side. -/
theorem hpPositiveRefinedM_cubic_q {q s : ℝ} (hq : (12 : ℝ) ≤ q)
    (hs : 0 ≤ s) :
    s ^ 2 * (1 - s) ≤ hpPositiveRefinedM * (1 - q⁻¹ * s ^ 2) := by
  have h := hpPositiveRefinedM_cubic hs
  have hqi := hp_positive_qinv_le hq
  have hstep : 1 - s ^ 2 / 12 ≤ 1 - q⁻¹ * s ^ 2 := by
    have hmul : q⁻¹ * s ^ 2 ≤ (1 / 12 : ℝ) * s ^ 2 :=
      mul_le_mul_of_nonneg_right hqi (sq_nonneg s)
    linarith
  have hM := mul_le_mul_of_nonneg_left hstep hpPositiveRefinedM_nonneg
  linarith

theorem hpPositiveRefinedM_sq :
    hpPositiveRefinedM ^ 2 = (23716 / 1000000 : ℝ) := by
  norm_num [hpPositiveRefinedM]

/-- Refined positive pointwise bracket bound, v13 `hp-tail.tex:202-215`,
square-root AM--GM reduction exactly as in the q = 8 refined file. -/
theorem hp_positive_bracket_le_refined {q t u : ℝ} (hq : (12 : ℝ) ≤ q)
    (ht : t ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (0 : ℝ) 1) :
    hpPositiveBetaBracket q t u ≤ hpPositiveRefinedM ^ 2 := by
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
  have hcore := hpPositiveRefinedM_cubic_q hq hs0
  have hcore0 : 0 ≤ s ^ 2 * (1 - s) := by
    exact mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hs1)
  have hnum' :
      (s ^ 2 * (1 - s)) ^ 2 ≤
        (hpPositiveRefinedM * (1 - q⁻¹ * s ^ 2)) ^ 2 := by
    exact pow_le_pow_left₀ hcore0 hcore 2
  have hden := hp_positive_beta_denom_lower hq ht hu
  have hdenpos : 0 < (1 - q⁻¹ * t * u) ^ 2 := by
    have : 0 < 1 - q⁻¹ * t * u := by linarith
    exact sq_pos_of_pos this
  unfold hpPositiveBetaBracket
  apply (div_le_iff₀ hdenpos).2
  calc
    t ^ 2 * u ^ 2 * ((1 - t) * (1 - u)) ≤
        (s ^ 2 * (1 - s)) ^ 2 := hnum
    _ ≤ (hpPositiveRefinedM * (1 - q⁻¹ * s ^ 2)) ^ 2 := hnum'
    _ = hpPositiveRefinedM ^ 2 * (1 - q⁻¹ * t * u) ^ 2 := by
      rw [hs_sq]
      ring

/-- Refined full-kernel bound; drop-in replacement for
`hp_positive_beta_kernel_le` with `Cz = (12/11)^2`, `M2 = (154/1000)^2`. -/
theorem hp_positive_beta_kernel_le_refined {q : ℝ} (hq : (12 : ℝ) ≤ q)
    (n : ℕ) {t u : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hu : u ∈ Icc (0 : ℝ) 1) :
    hpPositiveBetaKernel q n t u ≤
      (12 / 11 : ℝ) ^ 2 * (hpPositiveRefinedM ^ 2) ^ n := by
  have hden := hp_positive_beta_denom_lower hq ht hu
  have hdenpos : 0 < (1 - q⁻¹ * t * u) ^ 2 := by
    have : 0 < 1 - q⁻¹ * t * u := by linarith
    exact sq_pos_of_pos this
  have htu : t * u ≤ 1 := by
    have h := mul_le_mul ht.2 hu.2 hu.1 (by norm_num : (0 : ℝ) ≤ 1)
    simpa using h
  have hpref : t * u / (1 - q⁻¹ * t * u) ^ 2 ≤ (12 / 11 : ℝ) ^ 2 := by
    apply (div_le_iff₀ hdenpos).2
    calc
      t * u ≤ 1 := htu
      _ = (12 / 11 : ℝ) ^ 2 * (11 / 12 : ℝ) ^ 2 := by norm_num
      _ ≤ (12 / 11 : ℝ) ^ 2 * (1 - q⁻¹ * t * u) ^ 2 := by
        gcongr
  have hbr := hp_positive_bracket_le_refined hq ht hu
  have hbr0 : 0 ≤ hpPositiveBetaBracket q t u := by
    unfold hpPositiveBetaBracket
    have ht0 : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
    have hu0 : 0 ≤ 1 - u := sub_nonneg.mpr hu.2
    apply div_nonneg
    · positivity
    · exact sq_nonneg _
  have hpow := pow_le_pow_left₀ hbr0 hbr n
  unfold hpPositiveBetaKernel
  calc
    t * u / (1 - q⁻¹ * t * u) ^ 2 *
          hpPositiveBetaBracket q t u ^ n ≤
        (12 / 11 : ℝ) ^ 2 * hpPositiveBetaBracket q t u ^ n :=
      mul_le_mul_of_nonneg_right hpref (pow_nonneg hbr0 n)
    _ ≤ (12 / 11 : ℝ) ^ 2 * (hpPositiveRefinedM ^ 2) ^ n :=
      mul_le_mul_of_nonneg_left hpow (by norm_num)

end

end Li2Lean.B4

#print axioms Li2Lean.B4.hp_positive_bracket_le_refined
#print axioms Li2Lean.B4.hp_positive_beta_kernel_le_refined
