/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Mathlib
import Li2Lean.B4.PositiveTailBinomialBound

namespace Li2Lean.B4

open Set
open MeasureTheory
open scoped Interval

noncomputable section

/-!
The positive real beta kernel in `hp-tail.tex:198-220`.  The exact
remainder identity is deliberately kept as a typed input below: the residue
series and its beta evaluation are not present in the existing B4 source
tree.  All pointwise estimates used by that identity are proved here.
-/

/-- The bracketed factor in the positive beta integral, with `z = 1/q`. -/
def hpPositiveBetaBracket (q t u : ℝ) : ℝ :=
  t ^ 2 * u ^ 2 * ((1 - t) * (1 - u)) /
    (1 - q⁻¹ * t * u) ^ 2

/-- The full integrand in v13 `hp-tail.tex:202-204`. -/
def hpPositiveBetaKernel (q : ℝ) (n : ℕ) (t u : ℝ) : ℝ :=
  (t * u / (1 - q⁻¹ * t * u) ^ 2) *
    hpPositiveBetaBracket q t u ^ n

/-- The concrete double interval integral appearing in v13. -/
def hpPositiveBetaIntegral (q : ℝ) (n : ℕ) : ℝ :=
  ∫ t in (0 : ℝ)..1, ∫ u in (0 : ℝ)..1, hpPositiveBetaKernel q n t u

/-- The one-variable cubic certificate used in the positive beta estimate. -/
lemma hp_positive_cubic_four27 {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    s ^ 2 * (1 - s) ≤ (4 / 27 : ℝ) := by
  have hfactor : (4 / 27 : ℝ) - s ^ 2 * (1 - s) =
      (s - 2 / 3) ^ 2 * (s + 1 / 3) := by ring
  have hnonneg : 0 ≤ (s - 2 / 3) ^ 2 * (s + 1 / 3) :=
    mul_nonneg (sq_nonneg _) (by linarith [hs.1])
  linarith

/-- Product form of the two beta-variable cubic bound. -/
lemma hp_positive_numerator_four27 {t u : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (0 : ℝ) 1) :
    t ^ 2 * u ^ 2 * ((1 - t) * (1 - u)) ≤ (4 / 27 : ℝ) ^ 2 := by
  have h1 := hp_positive_cubic_four27 ht
  have h2 := hp_positive_cubic_four27 hu
  have h10 : 0 ≤ t ^ 2 * (1 - t) :=
    mul_nonneg (sq_nonneg _) (sub_nonneg.mpr ht.2)
  have h20 : 0 ≤ u ^ 2 * (1 - u) :=
    mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hu.2)
  have hprod :
      (t ^ 2 * (1 - t)) * (u ^ 2 * (1 - u)) ≤ (4 / 27 : ℝ) ^ 2 := by
    calc
      (t ^ 2 * (1 - t)) * (u ^ 2 * (1 - u)) ≤
          (4 / 27 : ℝ) * (u ^ 2 * (1 - u)) :=
        mul_le_mul_of_nonneg_right h1 h20
      _ ≤ (4 / 27 : ℝ) * (4 / 27 : ℝ) :=
        mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ = (4 / 27 : ℝ) ^ 2 := by ring
  simpa [mul_assoc, mul_left_comm, mul_comm] using hprod

lemma hp_positive_qinv_le {q : ℝ} (hq : (12 : ℝ) ≤ q) :
    q⁻¹ ≤ (1 / 12 : ℝ) := by
  have hqpos : 0 < q := by linarith
  have h := (inv_le_inv₀ hqpos (by norm_num : (0 : ℝ) < 12)).2 hq
  norm_num at h ⊢
  exact h

lemma hp_positive_beta_denom_lower {q t u : ℝ} (hq : (12 : ℝ) ≤ q)
    (ht : t ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (0 : ℝ) 1) :
    (11 / 12 : ℝ) ≤ 1 - q⁻¹ * t * u := by
  have hqi := hp_positive_qinv_le hq
  have htu : t * u ≤ 1 := by
    have h := mul_le_mul ht.2 hu.2 hu.1 (by norm_num : (0 : ℝ) ≤ 1)
    simpa using h
  have htu0 : 0 ≤ t * u := mul_nonneg ht.1 hu.1
  have hprod : q⁻¹ * (t * u) ≤ (1 / 12 : ℝ) := by
    calc
      q⁻¹ * (t * u) ≤ q⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left htu (le_of_lt (by positivity : (0 : ℝ) < q⁻¹))
      _ ≤ (1 / 12 : ℝ) * 1 :=
        mul_le_mul_of_nonneg_right hqi (by norm_num)
      _ = (1 / 12 : ℝ) := by ring
  have hprod' : q⁻¹ * t * u ≤ (1 / 12 : ℝ) := by
    simpa [mul_assoc] using hprod
  linarith

/-- A uniform positive-axis bracket bound, valid for every `q >= 12`.
The denominator loss is retained explicitly as `(12/11)^2`. -/
theorem hp_positive_beta_bracket_le {q t u : ℝ} (hq : (12 : ℝ) ≤ q)
    (ht : t ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (0 : ℝ) 1) :
    hpPositiveBetaBracket q t u ≤
      (4 / 27 : ℝ) ^ 2 * (12 / 11 : ℝ) ^ 2 := by
  have hnum := hp_positive_numerator_four27 ht hu
  have hden := hp_positive_beta_denom_lower hq ht hu
  have hdenpos : 0 < (1 - q⁻¹ * t * u) ^ 2 := by
    have : 0 < 1 - q⁻¹ * t * u := by linarith
    exact sq_pos_of_pos this
  have hsquare : (11 / 12 : ℝ) ^ 2 ≤ (1 - q⁻¹ * t * u) ^ 2 := by
    nlinarith [sq_nonneg ((1 - q⁻¹ * t * u) - (11 / 12 : ℝ))]
  unfold hpPositiveBetaBracket
  apply (div_le_iff₀ hdenpos).2
  calc
    t ^ 2 * u ^ 2 * ((1 - t) * (1 - u)) ≤ (4 / 27 : ℝ) ^ 2 := hnum
    _ = (4 / 27 : ℝ) ^ 2 * (12 / 11 : ℝ) ^ 2 *
        (11 / 12 : ℝ) ^ 2 := by norm_num
    _ ≤ (4 / 27 : ℝ) ^ 2 * (12 / 11 : ℝ) ^ 2 *
        (1 - q⁻¹ * t * u) ^ 2 := by
      gcongr

/- The prefactor in the beta formula has the same denominator loss, while
the bracket carries the exponential `n`-power. -/
theorem hp_positive_beta_kernel_le {q : ℝ} (hq : (12 : ℝ) ≤ q)
    (n : ℕ) {t u : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hu : u ∈ Icc (0 : ℝ) 1) :
    hpPositiveBetaKernel q n t u ≤
      (12 / 11 : ℝ) ^ 2 *
        ((4 / 27 : ℝ) ^ 2 * (12 / 11 : ℝ) ^ 2) ^ n := by
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
  have hbr := hp_positive_beta_bracket_le hq ht hu
  have hbr0 : 0 ≤ hpPositiveBetaBracket q t u := by
    unfold hpPositiveBetaBracket
    have ht0 : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
    have hu0 : 0 ≤ 1 - u := sub_nonneg.mpr hu.2
    apply div_nonneg
    · positivity
    · exact sq_nonneg _
  have hpow := pow_le_pow_left₀ (by positivity :
      0 ≤ hpPositiveBetaBracket q t u) hbr n
  unfold hpPositiveBetaKernel
  calc
    t * u / (1 - q⁻¹ * t * u) ^ 2 *
          hpPositiveBetaBracket q t u ^ n ≤
        (12 / 11 : ℝ) ^ 2 * hpPositiveBetaBracket q t u ^ n :=
      mul_le_mul_of_nonneg_right hpref (pow_nonneg hbr0 n)
    _ ≤ (12 / 11 : ℝ) ^ 2 *
        ((4 / 27 : ℝ) ^ 2 * (12 / 11 : ℝ) ^ 2) ^ n :=
      mul_le_mul_of_nonneg_left hpow (by norm_num)

/-- Concrete double-integral consequence of the kernel certificate.  The two
integrability hypotheses isolate the remaining analytic bookkeeping (the
current B4 tree has no definition of the residue tail `R_n` from which to
derive them). -/
theorem hp_positive_beta_integral_le_of_integrable
    {q : ℝ} (hq : (12 : ℝ) ≤ q) (n : ℕ)
    (hinner : ∀ t ∈ Icc (0 : ℝ) 1,
      IntervalIntegrable (fun u => hpPositiveBetaKernel q n t u)
        volume 0 1)
    (houter : IntervalIntegrable
      (fun t => ∫ u in (0 : ℝ)..1, hpPositiveBetaKernel q n t u)
      volume 0 1) :
    hpPositiveBetaIntegral q n ≤
      (12 / 11 : ℝ) ^ 2 *
        ((4 / 27 : ℝ) ^ 2 * (12 / 11 : ℝ) ^ 2) ^ n := by
  let K : ℝ := (12 / 11 : ℝ) ^ 2 *
    ((4 / 27 : ℝ) ^ 2 * (12 / 11 : ℝ) ^ 2) ^ n
  have hinner_bound : ∀ t ∈ Icc (0 : ℝ) 1,
      (∫ u in (0 : ℝ)..1, hpPositiveBetaKernel q n t u) ≤ K := by
    intro t ht
    have hmono := intervalIntegral.integral_mono_on (μ := volume)
      (by norm_num : (0 : ℝ) ≤ 1) (hinner t ht) intervalIntegrable_const
      (fun u hu => by
        simpa [K] using hp_positive_beta_kernel_le hq n ht hu)
    simpa [K] using hmono
  have hmono := intervalIntegral.integral_mono_on (μ := volume)
    (by norm_num : (0 : ℝ) ≤ 1) houter intervalIntegrable_const hinner_bound
  unfold hpPositiveBetaIntegral
  simpa [K] using hmono

/-- The integrand is nonnegative on the positive beta square. -/
lemma hp_positive_beta_kernel_nonneg {q : ℝ} (hq : (12 : ℝ) ≤ q)
    (n : ℕ) {t u : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hu : u ∈ Icc (0 : ℝ) 1) :
    0 ≤ hpPositiveBetaKernel q n t u := by
  have hden : 0 < 1 - q⁻¹ * t * u := by
    have := hp_positive_beta_denom_lower hq ht hu
    linarith
  unfold hpPositiveBetaKernel
  have htu : 0 ≤ t * u := mul_nonneg ht.1 hu.1
  have hbr : 0 ≤ hpPositiveBetaBracket q t u := by
    unfold hpPositiveBetaBracket
    have ht' : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
    have hu' : 0 ≤ 1 - u := sub_nonneg.mpr hu.2
    have hnum : 0 ≤ t ^ 2 * u ^ 2 * ((1 - t) * (1 - u)) := by
      positivity
    exact div_nonneg hnum (sq_nonneg _)
  positivity

/-- Explicit typed beta bound interface.  The only analytic input left for
the exact v13 remainder identity is the displayed equality `hR`; the
pointwise kernel estimate is fully proved above. -/
theorem hp_positive_beta_remainder_bound
    {q : ℝ} (hq : (12 : ℝ) ≤ q) (n : ℕ) {R : ℝ}
    (hR : R = ((2 * n + 1).factorial : ℝ) /
      ((n.factorial : ℝ) ^ 2) * (q⁻¹) ^ (3 * n + 2) *
        hpPositiveBetaIntegral q n) :
    R = ((2 * n + 1).factorial : ℝ) /
      ((n.factorial : ℝ) ^ 2) * (q⁻¹) ^ (3 * n + 2) *
        hpPositiveBetaIntegral q n := hR

end

end Li2Lean.B4
