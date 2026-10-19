/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B4.NegativeContourQ8BetaRefined
import Li2Lean.B4.NegativeTailContourDecay

open Set

namespace Li2Lean.B4.TailAnalytic

noncomputable section

open Li2Lean.B4

/-!
The q = 8 beta kernel and the contour envelope are combined here.  The
kernel is the concrete `B_n`/`R_n` input from v13 `hp-tail.tex:198-220`;
the rate factor is the fixed-base combination in `:411-430`.

This file deliberately stops at the beta-rate input.  The separate theorem
`hpLR_tendsto_zero_of_contour_beta_bounds` still requires the construction
specific beta integral bound for `hpRR`; this module supplies its exact
kernel constant and the strict numerical inequality needed by that bridge.
-/

/-- The exact sharpened rational beta constant certified for q = 8. -/
def hpNegativeQ8BetaM : ℝ := hpNegativeQ8RefinedM ^ 2

theorem hpNegativeQ8BetaM_nonneg : 0 ≤ hpNegativeQ8BetaM := by
  norm_num [hpNegativeQ8BetaM, hpNegativeQ8RefinedM]

/-! Convert the divided q=8 pointwise estimate into the numerator form used
by the beta integral.  This is the same denominator `(1 + tu/8)^2` as in
v13's equation `hp-beta`. -/
theorem hp_negative_q8_beta_kernel_bound {t u : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (0 : ℝ) 1) :
    t ^ 2 * u ^ 2 * ((1 - t) * (1 - u)) ≤
      hpNegativeQ8BetaM * (1 + t * u / 8) ^ 2 := by
  have h := hp_negative_bracket_div_q8_refined ht hu
  have htu : 0 ≤ t * u := mul_nonneg ht.1 hu.1
  have hden : 0 < (1 + t * u / 8) ^ 2 := by
    have hbase : 0 < 1 + t * u / 8 := by nlinarith
    positivity
  simpa [hpNegativeQ8BetaM] using (div_le_iff₀ hden).mp h

/-- The q=8 contour/beta exponential factor is strictly below one. -/
theorem hp_q8_contour_beta_rate_lt_one :
    hpContourGamma * 29 * (4 * hpNegativeQ8BetaM) * (8 : ℝ)⁻¹ < 1 := by
  have hgamma := hpContour_exp_4004_le
  unfold hpContourGamma at hgamma ⊢
  calc
    Real.exp (4 * (1 + 1 / 1000 : ℝ)) / 16 * 29 *
          (4 * hpNegativeQ8BetaM) * (8 : ℝ)⁻¹ ≤
        ((27182818286 / 10 ^ 10 : ℝ) ^ 4 * (1008 / 1000)) / 16 *
          29 * (4 * hpNegativeQ8BetaM) * (8 : ℝ)⁻¹ := by
      have hnonneg : 0 ≤ 29 * (4 * hpNegativeQ8BetaM) * (8 : ℝ)⁻¹ / 16 := by
        norm_num [hpNegativeQ8BetaM, hpNegativeQ8RefinedM]
      have hmul := mul_le_mul_of_nonneg_right hgamma hnonneg
      calc
        Real.exp (4 * (1 + 1 / 1000 : ℝ)) / 16 * 29 *
              (4 * hpNegativeQ8BetaM) * (8 : ℝ)⁻¹ =
            Real.exp (4 * (1 + 1 / 1000 : ℝ)) *
              (29 * (4 * hpNegativeQ8BetaM) * (8 : ℝ)⁻¹ / 16) := by ring
        _ ≤ (27182818286 / 10 ^ 10 : ℝ) ^ 4 * (1008 / 1000) *
              (29 * (4 * hpNegativeQ8BetaM) * (8 : ℝ)⁻¹ / 16) := hmul
        _ = ((27182818286 / 10 ^ 10 : ℝ) ^ 4 * (1008 / 1000)) / 16 *
              29 * (4 * hpNegativeQ8BetaM) * (8 : ℝ)⁻¹ := by ring
    _ < 1 := by
      norm_num [hpNegativeQ8BetaM, hpNegativeQ8RefinedM]

/-- The complete q=8 kernel/rate producer consumed by the contour-beta
decay bridge.  The first conjunct is the actual v13 beta kernel estimate;
the second is the strict `rho < 1` check with q = 8. -/
theorem hp_q8_contour_beta_rate_certificate :
    (∀ t u : ℝ, t ∈ Icc (0 : ℝ) 1 → u ∈ Icc (0 : ℝ) 1 →
      t ^ 2 * u ^ 2 * ((1 - t) * (1 - u)) ≤
        hpNegativeQ8BetaM * (1 + t * u / 8) ^ 2) ∧
      hpContourGamma * 29 * (4 * hpNegativeQ8BetaM) * (8 : ℝ)⁻¹ < 1 := by
  constructor
  · intro t u ht hu
    exact hp_negative_q8_beta_kernel_bound ht hu
  · exact hp_q8_contour_beta_rate_lt_one

/-! The fixed-base wrapper keeps the remaining analytic obligation visible:
the supplied `hR` is the beta integral estimate for the concrete `hpRR`
family.  Once that producer is available, all other hypotheses are the
existing v13 construction interfaces and the strict rate above closes the
decay theorem at `a = -8`. -/
theorem hpDecayNeg_q8_of_beta_producer
    (certificate : Nonempty
      (Li2Lean.B4.NegativeContour.NegContourRectangleCertificate
        Li2Lean.B4.NegativeContour.hpBSequence 8))
    (I : Li2Lean.B4.TailAnalytic.HPNoAdjacentV13Input (-8 : ℤ))
    (hR : ∀ n : ℕ,
      |Li2Lean.B4.TailAnalytic.hpRR n
          (((-(8 : ℤ) : ℤ) : ℝ)⁻¹)| ≤
        (2 * n + 1 : ℝ) * 4 ^ n * (8 : ℝ)⁻¹ ^ (3 * n + 2) *
          hpNegativeQ8BetaM ^ n) :
    Li2Lean.AllNAssembly.HPDecay (-(8 : ℤ)) := by
  have hR' : ∀ n : ℕ,
      |Li2Lean.B4.TailAnalytic.hpRR n
          ((-(8 : ℕ) : ℝ)⁻¹)| ≤
        (2 * n + 1 : ℝ) * 4 ^ n * (8 : ℝ)⁻¹ ^ (3 * n + 2) *
          hpNegativeQ8BetaM ^ n := by
    intro n
    convert hR n using 1 <;> norm_num
  exact hpDecayNeg_exceptional_of_contour_beta_bound
    (q := 8) (by norm_num) certificate I (M2 := hpNegativeQ8BetaM)
    hpNegativeQ8BetaM_nonneg hR' hp_q8_contour_beta_rate_lt_one

end

end Li2Lean.B4.TailAnalytic

#print axioms Li2Lean.B4.TailAnalytic.hp_negative_q8_beta_kernel_bound
#print axioms Li2Lean.B4.TailAnalytic.hp_q8_contour_beta_rate_lt_one
#print axioms Li2Lean.B4.TailAnalytic.hp_q8_contour_beta_rate_certificate
#print axioms Li2Lean.B4.TailAnalytic.hpDecayNeg_q8_of_beta_producer
