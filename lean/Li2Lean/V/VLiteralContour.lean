/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

The signed contour and integral statement from Li2(1/n), paper v13.
This module defines the precise S0 target; the determinant-integral theorem
below remains the first open analytic obligation.
-/

import Li2Lean.Statement
import Li2Lean.V.VFamily
import Li2Lean.V.VPath

namespace Li2Lean
namespace V
namespace Literal

noncomputable section

open MeasureTheory Set

/-- The coefficient `c_q` of the two half-circles,
`v-analytic.tex:91-94`. -/
def vContourCoefficient (q : ℕ) : ℂ :=
  (Complex.ofReal (Real.log (q : ℝ)) + Complex.I * Real.pi) /
    (2 * Complex.ofReal Real.pi * Complex.I)

/-- Four unit-interval parameterizations of the oriented pieces of
`Gamma_q`, `v-analytic.tex:87-94`. The tags are the negative segment, positive
segment, upper semicircle, and lower semicircle in that order. -/
def vContourPoint (q : ℕ) (piece : Fin 4) (t : ℝ) : ℂ :=
  if piece.val = 0 then
    -(q : ℂ) + (Complex.ofReal (q : ℝ) - Complex.ofReal vContourRadius) * t
  else if piece.val = 1 then
    Complex.ofReal vContourRadius +
      (1 - Complex.ofReal vContourRadius) * t
  else if piece.val = 2 then
    Complex.ofReal vContourRadius *
      Complex.exp (Complex.I * (Complex.ofReal Real.pi * t))
  else
    Complex.ofReal vContourRadius *
      Complex.exp (Complex.I * (Complex.ofReal Real.pi +
        Complex.ofReal Real.pi * t))

/-- Derivatives of the four parameterized pieces,
`v-analytic.tex:87-94`. -/
def vContourDerivative (q : ℕ) (piece : Fin 4) (t : ℝ) : ℂ :=
  if piece.val = 0 then
    Complex.ofReal (q : ℝ) - Complex.ofReal vContourRadius
  else if piece.val = 1 then
    1 - Complex.ofReal vContourRadius
  else
    Complex.I * Complex.ofReal Real.pi * vContourPoint q piece t

/-- The complex path coefficient on each component of the v13 chain,
`v-analytic.tex:91-94`. -/
def vContourComponentWeight (q : ℕ) (piece : Fin 4) : ℂ :=
  if piece.val < 2 then 1
  else if piece.val = 2 then vContourCoefficient q - 1
  else vContourCoefficient q

/-- Positive parameter measure: counting measure on the four pieces times
Lebesgue measure restricted to `[0,1]`. Complex contour coefficients are
kept in the integrand, not encoded as a signed measure. -/
def vContourParameterMeasure : Measure (Fin 4 × ℝ) :=
  Measure.count.prod (volume.restrict (Set.Icc (0 : ℝ) 1))

/-- The weighted pullback of `dz` to one of the four parameterized pieces. -/
def vContourWeight (q : ℕ) (p : Fin 4 × ℝ) : ℂ :=
  vContourComponentWeight q p.1 * vContourDerivative q p.1 p.2

/-- The contour integral along the v13 signed chain, represented on a
positive parameter space with its complex path weights. -/
noncomputable def vContourIntegral (q : ℕ) (f : ℂ → ℂ) : ℂ :=
  ∫ p : Fin 4 × ℝ, vContourWeight q p * f (vContourPoint q p.1 p.2)
    ∂vContourParameterMeasure

/-- The Laurent moment appearing in the top block,
`v-analytic.tex:96-104,127`. -/
noncomputable def vContourLaurentMoment (q : ℕ) (d : ℤ) : ℂ :=
  vContourIntegral q (fun z => z ^ (d - 1))

/-- Vandermonde in the increasing `Fin` order. -/
def vContourVandermonde {d : ℕ} (z : Fin d → ℂ) : ℂ :=
  ∏ i : Fin d, ∏ j : Fin d, if i < j then z j - z i else 1

/-- The exact v13 integrand. The exponents are `3m/4=3n`, `m/4=n`,
and `-5m/4=-5n`, `v-analytic.tex:117-123`. -/
def vContourPhi (q n : ℕ) (x : Fin (4 * n) → ℝ)
    (v : Fin (5 * n) → ℝ) (z : Fin (4 * n) → ℂ) : ℂ :=
  let Δx := vContourVandermonde (fun i => (x i : ℂ))
  let Δv := vContourVandermonde (fun i => (v i : ℂ))
  let Δz := vContourVandermonde z
  Δx ^ 2 * Δv ^ 2 * Δz ^ 2 *
    (Finset.univ.prod fun i : Fin (4 * n) =>
      Finset.univ.prod fun b : Fin (5 * n) => z i - (v b : ℂ)) *
    (∏ i : Fin (4 * n), (x i : ℂ) ^ (3 * n)) *
    (∏ b : Fin (5 * n), (v b : ℂ) ^ n) *
    (∏ i : Fin (4 * n), z i ^ (-(5 * n : ℤ))) /
    (Finset.univ.prod fun i : Fin (4 * n) =>
      Finset.univ.prod fun b : Fin (5 * n) =>
        (q : ℂ) + (x i : ℂ) * (v b : ℂ))

def vContourUnitIntervalMeasure : Measure ℝ :=
  volume.restrict (Set.Icc (0 : ℝ) 1)

/-- The threefold parameter integral in v13 `v-analytic.tex:109-123`.
The innermost variables carry the four-piece contour parameterization. -/
noncomputable def vContourTripleIntegral (q n : ℕ) : ℂ :=
  ∫ x : Fin (4 * n) → ℝ,
    ∫ v : Fin (5 * n) → ℝ,
      ∫ p : Fin (4 * n) → (Fin 4 × ℝ),
        (∏ i : Fin (4 * n), vContourWeight q (p i)) *
          vContourPhi q n x v (fun i => vContourPoint q (p i).1 (p i).2)
        ∂Measure.pi (fun _ : Fin (4 * n) => vContourParameterMeasure)
      ∂Measure.pi (fun _ : Fin (5 * n) => vContourUnitIntervalMeasure)
    ∂Measure.pi (fun _ : Fin (4 * n) => vContourUnitIntervalMeasure)

/-- The exact factorial and q-power prefactor after substituting `m=4n`,
`L=5n`, v13 `v-analytic.tex:109-123`. -/
def vContourPrefactor (q n : ℕ) : ℂ :=
  (q : ℂ) ^ (24 * n ^ 2 - 4 * n) /
    (((Nat.factorial (4 * n) : ℕ) : ℂ) ^ 2 *
      ((Nat.factorial (5 * n) : ℕ) : ℂ))

/-- The same signed determinant value as `V.vPolynomial`, evaluated at the
v13 value `Li_2(-1/q)`, `v-arithmetic.tex:32-35` and
`v-analytic.tex:109-123`. -/
noncomputable def vContourGValue (q n : ℕ) : ℂ :=
  Polynomial.eval₂ (algebraMap ℚ ℂ)
    (li2InvValue (-(q : ℤ)) : ℂ) (vPolynomial n (-(q : ℤ)))

/-- Integrand on the positive parameter space for the four oriented pieces of Gamma_q, v-analytic.tex:87-104. -/
def vContourIntegrand (q : ℕ) (f : ℂ → ℂ) (p : Fin 4 × ℝ) : ℂ :=
  vContourWeight q p * f (vContourPoint q p.1 p.2)

/-- Split the positive parameter-space integral into the four oriented interval
integrals. The contour coefficients remain in `vContourWeight`, so this is
the v13 signed chain with counting measure only as an implementation device.
The sole analytic hypothesis is integrability on the product measure. -/
theorem vContourIntegral_eq_sum_setIntegral (q : ℕ) (f : ℂ → ℂ)
    (hF : Integrable (vContourIntegrand q f) vContourParameterMeasure) :
    vContourIntegral q f =
      ∑ piece : Fin 4, ∫ t in Set.Icc (0 : ℝ) 1,
        vContourWeight q (piece, t) * f (vContourPoint q piece t) := by
  rw [vContourIntegral]
  change (∫ p, vContourIntegrand q f p ∂(Measure.count.prod
    (volume.restrict (Set.Icc (0 : ℝ) 1)))) = _
  calc
    (∫ p, vContourIntegrand q f p ∂(Measure.count.prod
      (volume.restrict (Set.Icc (0 : ℝ) 1)))) =
        ∫ piece, ∫ t, vContourIntegrand q f (piece, t)
          ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) ∂Measure.count :=
      MeasureTheory.integral_prod _ hF
    _ = _ := by
      rw [MeasureTheory.integral_count]
      rfl

private lemma vContourPoint_ne_zero_on_parameter (q : ℕ) (hq : 2 ≤ q)
    (piece : Fin 4) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    vContourPoint q piece t ≠ 0 := by
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hrpos : 0 < vContourRadius := by norm_num [vContourRadius]
  have hrle : vContourRadius ≤ (1 : ℝ) := by norm_num [vContourRadius]
  have hqr : vContourRadius ≤ (q : ℝ) := by linarith
  have hqrmul : 0 ≤ ((q : ℝ) - vContourRadius) * (1 - t) := by
    exact mul_nonneg (sub_nonneg.mpr hqr) (sub_nonneg.mpr ht.2)
  fin_cases piece
  · have hneg : -(q : ℝ) + ((q : ℝ) - vContourRadius) * t < 0 := by
      nlinarith [hrpos, hqrmul]
    simp [vContourPoint]
    intro hz
    have hz' := congrArg Complex.re hz
    norm_num at hz'
    nlinarith [hneg]
  · have hpos : 0 < vContourRadius + (1 - vContourRadius) * t := by
      have hmul : 0 ≤ (1 - vContourRadius) * t :=
        mul_nonneg (sub_nonneg.mpr hrle) ht.1
      nlinarith
    simp [vContourPoint]
    intro hz
    have hz' := congrArg Complex.re hz
    norm_num at hz'
    nlinarith [hpos]
  · change Complex.ofReal vContourRadius *
      Complex.exp (Complex.I * (Complex.ofReal Real.pi * t)) ≠ 0
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hrpos))
      (Complex.exp_ne_zero _)
  · change Complex.ofReal vContourRadius *
      Complex.exp (Complex.I * (Complex.ofReal Real.pi +
        Complex.ofReal Real.pi * t)) ≠ 0
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hrpos))
      (Complex.exp_ne_zero _)

private lemma vContourLaurentZero_zpow (z : ℂ) :
    z ^ ((0 : ℤ) - 1) = z⁻¹ := by
  norm_num [zpow_neg]

private def vContourLaurentZeroPullback (q : ℕ) (p : Fin 4 × ℝ) : ℂ :=
  vContourWeight q p * (vContourPoint q p.1 p.2)⁻¹

private lemma vContourLaurentZero_continuous_piece (q : ℕ) (hq : 2 ≤ q)
    (piece : Fin 4) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ContinuousAt (fun s : ℝ => vContourLaurentZeroPullback q (piece, s)) t := by
  have hp : ContinuousAt (fun s : ℝ => vContourPoint q piece s) t := by
    fin_cases piece <;> simp [vContourPoint] <;> fun_prop
  have hpi : ContinuousAt (fun s : ℝ => (vContourPoint q piece s)⁻¹) t :=
    hp.inv₀ (vContourPoint_ne_zero_on_parameter q hq piece ht)
  have hw : ContinuousAt (fun s : ℝ => vContourWeight q (piece, s)) t := by
    fin_cases piece <;>
      simp [vContourWeight, vContourComponentWeight, vContourDerivative,
        vContourPoint] <;> fun_prop
  change ContinuousAt
    ((fun s : ℝ => vContourWeight q (piece, s)) *
      (fun s : ℝ => (vContourPoint q piece s)⁻¹)) t
  exact hw.mul hpi

private lemma vContourLaurentZero_continuous (q : ℕ) (hq : 2 ≤ q) :
    ContinuousOn (vContourLaurentZeroPullback q)
      ((Set.univ : Set (Fin 4)) ×ˢ Set.Icc (0 : ℝ) 1) := by
  apply continuousOn_of_forall_continuousAt
  rintro ⟨piece, t⟩ hp
  have ht : t ∈ Set.Icc (0 : ℝ) 1 := (Set.mem_prod.mp hp).2
  have hs : ({piece} ×ˢ (Set.univ : Set ℝ)) ∈ nhds (piece, t) := by
    apply (isOpen_discrete ({piece} : Set (Fin 4))).prod isOpen_univ |>.mem_nhds
    simp
  have hev : (fun p : Fin 4 × ℝ => vContourLaurentZeroPullback q p) =ᶠ[nhds (piece, t)]
      (fun p : Fin 4 × ℝ => vContourLaurentZeroPullback q (piece, p.2)) := by
    filter_upwards [hs] with p hp'
    rcases p with ⟨p1, p2⟩
    have hpiece : p1 = piece := by
      exact Set.mem_singleton_iff.mp (Set.mem_prod.mp hp').1
    subst p1
    rfl
  have hcomp : ContinuousAt
      (fun p : Fin 4 × ℝ => vContourLaurentZeroPullback q (piece, p.2))
      (piece, t) := by
    change ContinuousAt
      ((fun s : ℝ => vContourLaurentZeroPullback q (piece, s)) ∘ Prod.snd)
      (piece, t)
    exact (vContourLaurentZero_continuous_piece q hq piece ht).comp
      (f := Prod.snd) (g := fun s : ℝ => vContourLaurentZeroPullback q (piece, s))
      (x := (piece, t)) continuousAt_snd
  exact hcomp.congr_of_eventuallyEq hev

private lemma vContourLaurentZero_integrable (q : ℕ) (hq : 2 ≤ q) :
    Integrable (vContourLaurentZeroPullback q) vContourParameterMeasure := by
  have hcont := vContourLaurentZero_continuous q hq
  have hcompact : IsCompact ((Set.univ : Set (Fin 4)) ×ˢ Set.Icc (0 : ℝ) 1) :=
    isCompact_univ.prod isCompact_Icc
  have hIntOn : IntegrableOn (vContourLaurentZeroPullback q)
      ((Set.univ : Set (Fin 4)) ×ˢ Set.Icc (0 : ℝ) 1)
      (Measure.count.prod volume) :=
    ContinuousOn.integrableOn_compact hcompact hcont
  have hIntRestrict : Integrable (vContourLaurentZeroPullback q)
      ((Measure.count.prod volume).restrict
        ((Set.univ : Set (Fin 4)) ×ˢ Set.Icc (0 : ℝ) 1)) :=
    hIntOn.integrable
  have hmeasure :
      (Measure.count.prod volume).restrict
          ((Set.univ : Set (Fin 4)) ×ˢ Set.Icc (0 : ℝ) 1) =
        Measure.count.prod (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    rw [← Measure.prod_restrict]
    simp
  rw [hmeasure] at hIntRestrict
  exact hIntRestrict

private lemma vContourNegRadiusArg_deriv (q : ℕ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (q : ℝ) - ((q : ℝ) - vContourRadius) * s)
      (-((q : ℝ) - vContourRadius)) t := by
  convert (hasDerivAt_const t (q : ℝ)).sub
    ((hasDerivAt_const t ((q : ℝ) - vContourRadius)).mul (hasDerivAt_id t)) using 1
  · funext s
    dsimp [id]
  · ring

private lemma vContourPosRadiusArg_deriv (t : ℝ) :
    HasDerivAt (fun s : ℝ => vContourRadius + (1 - vContourRadius) * s)
      (1 - vContourRadius) t := by
  convert (hasDerivAt_const t vContourRadius).add
    ((hasDerivAt_const t (1 - vContourRadius)).mul (hasDerivAt_id t)) using 1
  · funext s
    dsimp [id]
  · ring

private lemma vContourNegRadiusArg_pos (q : ℕ) (hq : 2 ≤ q) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    0 < (q : ℝ) - ((q : ℝ) - vContourRadius) * t := by
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hrpos : 0 < vContourRadius := by norm_num [vContourRadius]
  have hrle : vContourRadius ≤ (1 : ℝ) := by norm_num [vContourRadius]
  have hqr : vContourRadius ≤ (q : ℝ) := by linarith
  have hqrmul : 0 ≤ ((q : ℝ) - vContourRadius) * (1 - t) := by
    exact mul_nonneg (sub_nonneg.mpr hqr) (sub_nonneg.mpr ht.2)
  nlinarith [hrpos, hqrmul]

private lemma vContourPosRadiusArg_pos {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    0 < vContourRadius + (1 - vContourRadius) * t := by
  have hrpos : 0 < vContourRadius := by norm_num [vContourRadius]
  have hrle : vContourRadius ≤ (1 : ℝ) := by norm_num [vContourRadius]
  have hmul : 0 ≤ (1 - vContourRadius) * t :=
    mul_nonneg (sub_nonneg.mpr hrle) ht.1
  nlinarith

private lemma vContourNegRadiusLog_deriv (q : ℕ) (hq : 2 ≤ q) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivAt
      (fun s : ℝ => Complex.ofReal
        (Real.log ((q : ℝ) - ((q : ℝ) - vContourRadius) * s)))
      (vContourLaurentZeroPullback q (0, t)) t := by
  have harg := vContourNegRadiusArg_pos q hq ht
  have hlog :=
    ((Real.hasDerivAt_log (ne_of_gt harg)).comp t
      (vContourNegRadiusArg_deriv q t)).ofReal_comp
  convert hlog using 1
  · rfl
  · simp [vContourLaurentZeroPullback, vContourWeight,
      vContourComponentWeight, vContourDerivative, vContourPoint]
    have hB :
        ((q : ℂ) - ((q : ℂ) - Complex.ofReal vContourRadius) *
          Complex.ofReal t) ≠ 0 := by
      have hB0 := Complex.ofReal_ne_zero.mpr (ne_of_gt harg)
      convert hB0 using 1 <;> push_cast <;> ring
    have hnegB :
        (-(q : ℂ) + ((q : ℂ) - Complex.ofReal vContourRadius) *
          Complex.ofReal t) ≠ 0 := by
      convert (neg_ne_zero.mpr hB) using 1 <;> ring
    field_simp [hB, hnegB]
    ring

private lemma vContourPosRadiusLog_deriv (q : ℕ) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivAt
      (fun s : ℝ => Complex.ofReal
        (Real.log (vContourRadius + (1 - vContourRadius) * s)))
      (vContourLaurentZeroPullback q (1, t)) t := by
  have harg := vContourPosRadiusArg_pos ht
  have hlog :=
    ((Real.hasDerivAt_log (ne_of_gt harg)).comp t
      (vContourPosRadiusArg_deriv t)).ofReal_comp
  convert hlog using 1
  · rfl
  · simp [vContourLaurentZeroPullback, vContourWeight,
      vContourComponentWeight, vContourDerivative, vContourPoint]
    ring

private lemma vContourNegRadiusLog_setIntegral (q : ℕ) (hq : 2 ≤ q) :
    (∫ t in Set.Icc (0 : ℝ) 1, vContourLaurentZeroPullback q (0, t)) =
      Complex.ofReal (Real.log vContourRadius - Real.log (q : ℝ)) := by
  have hcont : ContinuousOn (fun t : ℝ => vContourLaurentZeroPullback q (0, t))
      (uIcc (0 : ℝ) 1) := by
    apply continuousOn_of_forall_continuousAt
    intro t ht
    exact vContourLaurentZero_continuous_piece q hq 0
      (by simpa [uIcc_of_le] using ht)
  have hint : IntervalIntegrable (fun t : ℝ => vContourLaurentZeroPullback q (0, t))
      volume 0 1 := hcont.intervalIntegrable
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1,
      HasDerivAt
        (fun s : ℝ => Complex.ofReal
          (Real.log ((q : ℝ) - ((q : ℝ) - vContourRadius) * s)))
        (vContourLaurentZeroPullback q (0, t)) t := by
    intro t ht
    exact vContourNegRadiusLog_deriv q hq (by simpa [uIcc_of_le] using ht)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hset :
      (∫ t in Set.Icc (0 : ℝ) 1, vContourLaurentZeroPullback q (0, t)) =
        ∫ t in (0 : ℝ)..1, vContourLaurentZeroPullback q (0, t) := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
    rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [hset, hftc]
  norm_num [vContourRadius]

private lemma vContourPosRadiusLog_setIntegral (q : ℕ) (hq : 2 ≤ q) :
    (∫ t in Set.Icc (0 : ℝ) 1, vContourLaurentZeroPullback q (1, t)) =
      Complex.ofReal (Real.log (1 : ℝ) - Real.log vContourRadius) := by
  have hcont : ContinuousOn (fun t : ℝ => vContourLaurentZeroPullback q (1, t))
      (uIcc (0 : ℝ) 1) := by
    apply continuousOn_of_forall_continuousAt
    intro t ht
    exact vContourLaurentZero_continuous_piece q hq 1
      (by simpa [uIcc_of_le] using ht)
  have hint : IntervalIntegrable (fun t : ℝ => vContourLaurentZeroPullback q (1, t))
      volume 0 1 := hcont.intervalIntegrable
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1,
      HasDerivAt
        (fun s : ℝ => Complex.ofReal
          (Real.log (vContourRadius + (1 - vContourRadius) * s)))
        (vContourLaurentZeroPullback q (1, t)) t := by
    intro t ht
    exact vContourPosRadiusLog_deriv q (by simpa [uIcc_of_le] using ht)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hset :
      (∫ t in Set.Icc (0 : ℝ) 1, vContourLaurentZeroPullback q (1, t)) =
        ∫ t in (0 : ℝ)..1, vContourLaurentZeroPullback q (1, t) := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
    rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [hset, hftc]
  norm_num [vContourRadius]

private lemma vContourUpperArc_pointwise (q : ℕ) (hq : 2 ≤ q) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    vContourLaurentZeroPullback q (2, t) = (vContourCoefficient q - 1) *
      (Complex.I * Complex.ofReal Real.pi) := by
  have hz := vContourPoint_ne_zero_on_parameter q hq 2 ht
  simp only [vContourLaurentZeroPullback, vContourWeight,
    vContourComponentWeight, vContourDerivative, vContourPoint]
  norm_num
  field_simp [hz]
  have hrad : (Complex.ofReal vContourRadius) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (by norm_num [vContourRadius])
  field_simp [hrad]

private lemma vContourLowerArc_pointwise (q : ℕ) (hq : 2 ≤ q) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    vContourLaurentZeroPullback q (3, t) = vContourCoefficient q *
      (Complex.I * Complex.ofReal Real.pi) := by
  have hz := vContourPoint_ne_zero_on_parameter q hq 3 ht
  simp only [vContourLaurentZeroPullback, vContourWeight,
    vContourComponentWeight, vContourDerivative, vContourPoint]
  norm_num
  field_simp [hz]
  have hrad : (Complex.ofReal vContourRadius) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (by norm_num [vContourRadius])
  field_simp [hrad]

private lemma vContourUpperArc_setIntegral (q : ℕ) (hq : 2 ≤ q) :
    (∫ t in Set.Icc (0 : ℝ) 1, vContourLaurentZeroPullback q (2, t)) =
      (vContourCoefficient q - 1) * (Complex.I * Complex.ofReal Real.pi) := by
  calc
    (∫ t in Set.Icc (0 : ℝ) 1, vContourLaurentZeroPullback q (2, t)) =
        ∫ t in Set.Icc (0 : ℝ) 1,
          (vContourCoefficient q - 1) * (Complex.I * Complex.ofReal Real.pi) := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
      intro t ht
      exact vContourUpperArc_pointwise q hq ht
    _ = (vContourCoefficient q - 1) * (Complex.I * Complex.ofReal Real.pi) := by
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
      rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      simp

private lemma vContourLowerArc_setIntegral (q : ℕ) (hq : 2 ≤ q) :
    (∫ t in Set.Icc (0 : ℝ) 1, vContourLaurentZeroPullback q (3, t)) =
      vContourCoefficient q * (Complex.I * Complex.ofReal Real.pi) := by
  calc
    (∫ t in Set.Icc (0 : ℝ) 1, vContourLaurentZeroPullback q (3, t)) =
        ∫ t in Set.Icc (0 : ℝ) 1,
          vContourCoefficient q * (Complex.I * Complex.ofReal Real.pi) := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
      intro t ht
      exact vContourLowerArc_pointwise q hq ht
    _ = vContourCoefficient q * (Complex.I * Complex.ofReal Real.pi) := by
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
      rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      simp

private lemma vContourZeroCoefficient_identity (q : ℕ) :
    (vContourCoefficient q - 1) * (Complex.I * Complex.ofReal Real.pi) +
        vContourCoefficient q * (Complex.I * Complex.ofReal Real.pi) =
      Complex.ofReal (Real.log (q : ℝ)) := by
  unfold vContourCoefficient
  have hpi : Complex.ofReal Real.pi ≠ 0 :=
    Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp [Complex.I_ne_zero, hpi]
  ring

/-- v13's zero Laurent moment and branch convention,
`v-analytic.tex:87-104`. -/
theorem vContourLaurentMoment_zero (q : ℕ) (hq : 2 ≤ q) :
    vContourLaurentMoment q 0 = 0 := by
  let f : ℂ → ℂ := fun z => z ^ ((0 : ℤ) - 1)
  have hF : Integrable (vContourIntegrand q f) vContourParameterMeasure := by
    convert vContourLaurentZero_integrable q hq using 1
    funext p
    simp [vContourIntegrand, f, vContourLaurentZeroPullback,
      vContourLaurentZero_zpow]
  change vContourIntegral q f = 0
  calc
    vContourIntegral q f =
        ∑ piece : Fin 4, ∫ t in Set.Icc (0 : ℝ) 1,
          vContourLaurentZeroPullback q (piece, t) := by
      rw [vContourIntegral_eq_sum_setIntegral q f hF]
      apply Finset.sum_congr rfl
      intro piece hp
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
      intro t ht
      simp [vContourLaurentZeroPullback, f, vContourLaurentZero_zpow]
    _ = 0 := by
      rw [Fin.sum_univ_four]
      rw [vContourNegRadiusLog_setIntegral q hq,
        vContourPosRadiusLog_setIntegral q hq,
        vContourUpperArc_setIntegral q hq,
        vContourLowerArc_setIntegral q hq]
      have hcoef := vContourZeroCoefficient_identity q
      norm_num [vContourRadius] at *
      rw [← hcoef]
      push_cast
      ring

end
end Literal
end V
end Li2Lean

#print axioms Li2Lean.V.Literal.vContourIntegral_eq_sum_setIntegral
#print axioms Li2Lean.V.Literal.vContourLaurentMoment_zero
