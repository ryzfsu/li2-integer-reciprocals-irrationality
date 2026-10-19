/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B4.PositiveTailBetaRefined
import Li2Lean.B4.NegativeTailContourDecay

/-!
Generated (compiled in the release build).  Target path in the release:
`Li2Lean/B4/PositiveTailBetaRate.lean`.  Mirrors
`NegativeContourQ8BetaRate.lean` (3f9e06c3 / 015ba459).

Positive rate, v13 `hp-tail.tex:205-220, 411-430`, for every real q >= 12:

  hpContourGamma * hpTailTiltK * (4 * (154/1000)^2) * q⁻¹ < 1.

With the repo bounds e <= 27182818286/10^10, exp(1/250) <= 1008/1000
(`hpContour_exp_4004_le`) and K = (286317/86317)^3 (t0 = 13683/100000) the
q = 12 value is 0.99240983 (margin 0.00759); with the true gamma 0.98847958.
Exact Fraction Verified: `positive_M_checks.py` (rate < 1, numerator/denominator
58/58 digits).
-/

open Set

namespace Li2Lean.B4.TailAnalytic

noncomputable section

open Li2Lean.B4

/-- The squared refined positive constant, `M2` of the tail-bound bridge. -/
def hpPositiveBetaM : ℝ := hpPositiveRefinedM ^ 2

theorem hpPositiveBetaM_nonneg : 0 ≤ hpPositiveBetaM := by
  norm_num [hpPositiveBetaM, hpPositiveRefinedM]

/-- Numerator form used by the beta integral, `q >= 12`. -/
theorem hp_positive_beta_numerator_bound {q t u : ℝ} (hq : (12 : ℝ) ≤ q)
    (ht : t ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (0 : ℝ) 1) :
    t ^ 2 * u ^ 2 * ((1 - t) * (1 - u)) ≤
      hpPositiveBetaM * (1 - q⁻¹ * t * u) ^ 2 := by
  have h := hp_positive_bracket_le_refined hq ht hu
  have hden := hp_positive_beta_denom_lower hq ht hu
  have hdenpos : 0 < (1 - q⁻¹ * t * u) ^ 2 := by
    have : 0 < 1 - q⁻¹ * t * u := by linarith
    exact sq_pos_of_pos this
  unfold hpPositiveBetaBracket at h
  simpa [hpPositiveBetaM] using (div_le_iff₀ hdenpos).mp h

theorem hpTailTiltK_nonneg : 0 ≤ hpTailTiltK := by
  norm_num [hpTailTiltK, hpTailTiltT0]

/-- The positive contour/beta exponential factor at q = 12. -/
theorem hp_positive_beta_rate_lt_one_12 :
    hpContourGamma * hpTailTiltK * (4 * hpPositiveBetaM) * (12 : ℝ)⁻¹ < 1 := by
  have hgamma := hpContour_exp_4004_le
  unfold hpContourGamma at hgamma ⊢
  calc
    Real.exp (4 * (1 + 1 / 1000 : ℝ)) / 16 * hpTailTiltK *
          (4 * hpPositiveBetaM) * (12 : ℝ)⁻¹ ≤
        ((27182818286 / 10 ^ 10 : ℝ) ^ 4 * (1008 / 1000)) / 16 *
          hpTailTiltK * (4 * hpPositiveBetaM) * (12 : ℝ)⁻¹ := by
      have hnonneg :
          0 ≤ hpTailTiltK * (4 * hpPositiveBetaM) * (12 : ℝ)⁻¹ / 16 := by
        norm_num [hpTailTiltK, hpTailTiltT0, hpPositiveBetaM,
          hpPositiveRefinedM]
      have hmul := mul_le_mul_of_nonneg_right hgamma hnonneg
      calc
        Real.exp (4 * (1 + 1 / 1000 : ℝ)) / 16 * hpTailTiltK *
              (4 * hpPositiveBetaM) * (12 : ℝ)⁻¹ =
            Real.exp (4 * (1 + 1 / 1000 : ℝ)) *
              (hpTailTiltK * (4 * hpPositiveBetaM) * (12 : ℝ)⁻¹ / 16) := by
          ring
        _ ≤ (27182818286 / 10 ^ 10 : ℝ) ^ 4 * (1008 / 1000) *
              (hpTailTiltK * (4 * hpPositiveBetaM) * (12 : ℝ)⁻¹ / 16) := hmul
        _ = ((27182818286 / 10 ^ 10 : ℝ) ^ 4 * (1008 / 1000)) / 16 *
              hpTailTiltK * (4 * hpPositiveBetaM) * (12 : ℝ)⁻¹ := by ring
    _ < 1 := by
      norm_num [hpTailTiltK, hpTailTiltT0, hpPositiveBetaM, hpPositiveRefinedM]

/-- Uniform in the base: every real `q >= 12`. -/
theorem hp_positive_beta_rate_lt_one {q : ℝ} (hq : (12 : ℝ) ≤ q) :
    hpContourGamma * hpTailTiltK * (4 * hpPositiveBetaM) * q⁻¹ < 1 := by
  have hc : 0 ≤ hpContourGamma * hpTailTiltK * (4 * hpPositiveBetaM) := by
    have h1 := hpContourGamma_nonneg
    have h2 := hpTailTiltK_nonneg
    have h3 := hpPositiveBetaM_nonneg
    positivity
  have hqi : q⁻¹ ≤ (12 : ℝ)⁻¹ := by
    simpa [one_div] using hp_positive_qinv_le hq   -- [Verified] 1/12 vs 12⁻¹
  calc
    hpContourGamma * hpTailTiltK * (4 * hpPositiveBetaM) * q⁻¹ ≤
        hpContourGamma * hpTailTiltK * (4 * hpPositiveBetaM) * (12 : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_left hqi hc
    _ < 1 := hp_positive_beta_rate_lt_one_12

/-- Kernel + rate certificate (positive analogue of
`hp_q8_contour_beta_rate_certificate`). -/
theorem hp_positive_beta_rate_certificate {q : ℝ} (hq : (12 : ℝ) ≤ q) :
    (∀ t u : ℝ, t ∈ Icc (0 : ℝ) 1 → u ∈ Icc (0 : ℝ) 1 →
      t ^ 2 * u ^ 2 * ((1 - t) * (1 - u)) ≤
        hpPositiveBetaM * (1 - q⁻¹ * t * u) ^ 2) ∧
      hpContourGamma * hpTailTiltK * (4 * hpPositiveBetaM) * q⁻¹ < 1 := by
  constructor
  · intro t u ht hu
    exact hp_positive_beta_numerator_bound hq ht hu
  · exact hp_positive_beta_rate_lt_one hq

/-! Positive decay wrapper (analogue of `hpDecayNeg_q8_of_beta_producer`).
The remaining typed inputs are genuine, not conclusion-shaped:
* `hB` -- coefficient bridge (plan C4): from `hpTail_B_bound` once
  `hpBRealAt a n = hpTailB n a` is proved, with `CB = 24`, `k = 3`
  ((n+1)(3n+1)(8n+1) <= 24 (n+1)^3);
* `hR` -- the beta remainder bound (plan C1+C2) with `Cz = (12/11)^2`;
* `I` -- only `tail_representation` is used (same coupling as q = 8; plan C5a
  decouples it). -/
theorem hpDecayPos_of_beta_producer {a : ℤ} (ha : (12 : ℤ) ≤ a)
    (I : HPNoAdjacentV13Input a) {CB : ℝ} {k : ℕ} (hCB : 0 ≤ CB)
    (hB : ∀ m : ℕ, |hpBRealAt a m| ≤
      CB * ((m + 1 : ℕ) : ℝ) ^ k * hpTailTiltK ^ m)
    (hR : ∀ n : ℕ, |hpRR n ((a : ℝ)⁻¹)| ≤
      (2 * n + 1 : ℝ) * 4 ^ n * (a : ℝ)⁻¹ ^ (3 * n + 2) *
        ((12 / 11 : ℝ) ^ 2 * hpPositiveBetaM ^ n)) :
    Li2Lean.AllNAssembly.HPDecay a := by
  apply HPDecay_of_hpLR_tendsto_zero
  have haR : (12 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hapos : (0 : ℝ) < (a : ℝ) := by linarith
  have hD : ∀ᶠ n : ℕ in Filter.atTop,
      0 ≤ hpDR n ∧ hpDR n ≤ Real.exp (2 * (1 + 1 / 1000 : ℝ)) *
        (2 * n + 1 : ℝ) ^ 2 * hpContourGamma ^ n := by
    filter_upwards [hpContourDR_upper] with n hn
    refine ⟨?_, hn⟩
    -- `hpDR_nonneg_local` is private in NegativeTailContourDecay; re-prove
    -- or make it public.  [Verified]
    unfold hpDR
    positivity
  have hL : ∀ n : ℕ, |hpLR a n| ≤
      (a : ℝ) ^ (2 * n + 1) * hpDR n *
        (|hpBRealAt a (n + 1)| * |hpRR n ((a : ℝ)⁻¹)| +
          |hpBRealAt a n| * |hpRR (n + 1) ((a : ℝ)⁻¹)|) := by
    intro n
    have h := hpLR_abs_le_of_v13_input I n
    rwa [abs_of_pos hapos] at h
  exact hpLR_tendsto_zero_of_tail_bounds (q := (a : ℝ)) (K := hpTailTiltK)
    (M2 := hpPositiveBetaM) (Cz := (12 / 11 : ℝ) ^ 2) (CB := CB)
    (e2 := Real.exp (2 * (1 + 1 / 1000 : ℝ))) (k := k)
    (Bf := fun m => hpBRealAt a m) (Rf := fun m => hpRR m ((a : ℝ)⁻¹))
    (D := hpDR) (L := hpLR a)
    hapos hpTailTiltK_nonneg hpPositiveBetaM_nonneg (by norm_num) hCB
    (Real.exp_pos _).le hB hR hD hL (hp_positive_beta_rate_lt_one haR)

end

end Li2Lean.B4.TailAnalytic

#print axioms Li2Lean.B4.TailAnalytic.hp_positive_beta_numerator_bound
#print axioms Li2Lean.B4.TailAnalytic.hp_positive_beta_rate_lt_one_12
#print axioms Li2Lean.B4.TailAnalytic.hp_positive_beta_rate_lt_one
#print axioms Li2Lean.B4.TailAnalytic.hp_positive_beta_rate_certificate
#print axioms Li2Lean.B4.TailAnalytic.hpDecayPos_of_beta_producer
