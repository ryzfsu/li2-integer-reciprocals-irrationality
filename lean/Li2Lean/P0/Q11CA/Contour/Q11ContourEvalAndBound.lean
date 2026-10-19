/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.Q11ContourFourier
import Li2Lean.P0.Q11ContourSelfEnergyEnclosure
import Li2Lean.P0.Q11FrequencyTerms
import Li2Lean.P0.Q11CA.Contour.LocalTaylor
import Li2Lean.P0.CA.Contour.Eval
import Li2Lean.P0.CA.Contour.Bound
import Li2Lean.P0.CA.Contour.Taylor

/-!
# H7-contour (Part 1): Closed-Form Identity, Derivatives, Second-Derivative Bound, and Reflected Interval Evaluator for `q = 11`

This module adapts `Li2Lean.P0.CA.Contour.{ClosedForm,Deriv,Bound,Eval}` to the
`q = 11` reference configuration:
1. Closed-form representation `q11WformClosed θ` of
   `q11Weta (Li2Lean.p0EllipsePoint 1 θ) = q11Wform θ`, proved for all `θ : ℝ`
   (including the real endpoints `θ = 0, π`).
2. Explicit first and second derivatives `q11W1Closed θ` and `q11W2Closed θ`
   on `{θ | Real.sin θ ≠ 0}`, identified with `q11W1 θ` and `q11W2 θ` from
   `Li2Lean.P0.Q11CA.Contour.LocalTaylor`.
3. Global second-derivative bound `|q11W2Closed θ| ≤ 2200` (`q11W2_abs_le`) and
   second-order Taylor lower bound `q11_taylor_lower` on `Set.Ioo 0 Real.pi`.
4. Computable rational interval evaluators `q11WI c s`, `q11DI c s`, and
   `q11WDI c s` with soundness theorems `q11WI_mem` and `q11DI_mem`.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Li2Lean.P0.Q11Data

noncomputable section

open Li2Lean.LogSegment
open Li2Lean.P0.ConfigSegment
open Li2Lean.P0.ConfigContourReference
open Li2Lean.P0.ConfigContourKernel
open Li2Lean.P0.CA.Contour
open Li2Lean.P0.CA.Contour.QI

/-! ## 1. Complex Segment Potentials and Closed Form of `q11Weta` on the Ellipse -/

theorem q11IntervalComplexPotential_eq {X Y : ℝ} (hY : Y ≠ 0)
    (left right : ℕ → ℝ) (count : ℕ) (units : List ℕ) (width : ℝ)
    (hwidth : 0 < width)
    (hleft : ∀ j ∈ Finset.range count, left j ≤ right j) :
    (∫ y, Real.log ‖((X : ℂ) + (Y : ℂ) * Complex.I) - (y : ℂ)‖
        ∂q11IntervalReferenceMeasure left right count units width) =
      ∑ j ∈ Finset.range count, q11IntervalDensity units width j *
        (Gr (X - left j) Y - Gr (X - right j) Y) := by
  unfold q11IntervalReferenceMeasure
  have hint : ∀ j ∈ Finset.range count, Integrable
      (fun y : ℝ => Real.log ‖((X : ℂ) + (Y : ℂ) * Complex.I) - (y : ℂ)‖)
      (ENNReal.ofReal (q11IntervalDensity units width j) •
        volume.restrict (Set.Ico (left j) (right j))) := by
    intro j _
    exact (((continuous_log_norm_sub hY).integrableOn_Icc).mono_set
      Set.Ico_subset_Icc_self).smul_measure ENNReal.ofReal_ne_top
  rw [integral_finsetSum_measure hint]
  apply Finset.sum_congr rfl
  intro j hj
  rw [integral_smul_measure,
    ENNReal.toReal_ofReal (q11IntervalDensity_nonneg units hwidth j),
    MeasureTheory.integral_Ico_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (hleft j hj),
    integral_log_norm_sub hY]
  rfl

theorem q11IntervalComplexPotential_add_eq {X Y : ℝ} (hY : Y ≠ 0)
    (left right : ℕ → ℝ) (count : ℕ) (units : List ℕ) (width : ℝ)
    (hwidth : 0 < width)
    (hleft : ∀ j ∈ Finset.range count, left j ≤ right j) :
    (∫ y, Real.log ‖((X : ℂ) + (Y : ℂ) * Complex.I) + (y : ℂ)‖
        ∂q11IntervalReferenceMeasure left right count units width) =
      ∑ j ∈ Finset.range count, q11IntervalDensity units width j *
        (Gr (X + right j) Y - Gr (X + left j) Y) := by
  unfold q11IntervalReferenceMeasure
  have hint : ∀ j ∈ Finset.range count, Integrable
      (fun y : ℝ => Real.log ‖((X : ℂ) + (Y : ℂ) * Complex.I) + (y : ℂ)‖)
      (ENNReal.ofReal (q11IntervalDensity units width j) •
        volume.restrict (Set.Ico (left j) (right j))) := by
    intro j _
    exact (((continuous_log_norm_add hY).integrableOn_Icc).mono_set
      Set.Ico_subset_Icc_self).smul_measure ENNReal.ofReal_ne_top
  rw [integral_finsetSum_measure hint]
  apply Finset.sum_congr rfl
  intro j hj
  rw [integral_smul_measure,
    ENNReal.toReal_ofReal (q11IntervalDensity_nonneg units hwidth j),
    MeasureTheory.integral_Ico_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (hleft j hj),
    integral_log_norm_add hY]
  rfl

theorem q11PinnedComplexPotential_ofReal_eq_endpoints (x : ℝ) :
    q11PinnedComplexPotential (x : ℂ) =
      ∑ j ∈ Finset.range 8, q11IntervalDensity pinnedMassUnits (1 / 8 : ℝ) j *
        (primitive (x - q11PinnedEdgeReal j) -
          primitive (x - q11PinnedEdgeReal (j + 1))) := by
  unfold q11PinnedComplexPotential
  simp only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  exact q11PinnedPotential_eq_endpoints x

theorem q11ReflectedFrequencyPotential_ofReal_eq_endpoints (x : ℝ) :
    q11ReflectedFrequencyPotential (x : ℂ) =
      ∑ j ∈ Finset.range 4, q11IntervalDensity frequencyMassUnits 1 j *
        (primitive (x + q11FrequencyEdgeReal (j + 1)) -
          primitive (x + q11FrequencyEdgeReal j)) := by
  have heq : q11ReflectedFrequencyPotential (x : ℂ) = q11FrequencyPotential (-x) := by
    unfold q11ReflectedFrequencyPotential q11FrequencyPotential
    apply integral_congr_ae
    filter_upwards [] with t
    have hnorm : ‖(x : ℂ) + (t : ℂ)‖ = |-x - t| := by
      rw [show (x : ℂ) + (t : ℂ) = ((-(-x - t) : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_neg]
    rw [hnorm]
  rw [heq, q11FrequencyPotential_eq_endpoints]
  apply Finset.sum_congr rfl
  intro j _
  rw [show -x - q11FrequencyEdgeReal j = -(x + q11FrequencyEdgeReal j) by ring,
    show -x - q11FrequencyEdgeReal (j + 1) = -(x + q11FrequencyEdgeReal (j + 1)) by ring,
    Li2Lean.P0.ConfigPinnedTail.primitive_neg,
    Li2Lean.P0.ConfigPinnedTail.primitive_neg]
  ring

theorem q11Phi_ofReal_eq_endpoints (x : ℝ) :
    q11Phi (x : ℂ) =
      x * (Real.log 2 + q11Lambda) + (primitive (x + 1 / 2) - primitive x) +
        1 / 2 - (1 / 2 : ℝ) * Real.log (1 / 2 : ℝ) := by
  unfold q11Phi
  rw [phi_ofReal_eq_endpoints, Complex.ofReal_re]
  ring

/-- Linear combination of shifted segment primitives for `q = 11`
    (8 pinned cells of width `1/8` and 4 frequency cells of width `1`). -/
def q11SegComb (g : ℝ → ℝ) (lin c : ℝ) : ℝ :=
  (g (-(1 / 4)) - g (-(5 / 4)) + (g 0 - g (-2))) - (lin + (g (1 / 2) - g 0) + c) -
    2 * (∑ j ∈ Finset.range 8,
      q11IntervalDensity pinnedMassUnits (1 / 8 : ℝ) j *
        (g (-q11PinnedEdgeReal j) - g (-q11PinnedEdgeReal (j + 1)))) -
    (∑ j ∈ Finset.range 4,
      q11IntervalDensity frequencyMassUnits 1 j *
        (g (q11FrequencyEdgeReal (j + 1)) - g (q11FrequencyEdgeReal j)))

/-- Segment part of `q11Weta` at `X + i Y`. -/
def q11SegForm (X Y : ℝ) : ℝ :=
  q11SegComb (fun κ => Gr (X + κ) Y) (X * (Real.log 2 + q11Lambda))
    (1 / 2 - (1 / 2 : ℝ) * Real.log (1 / 2 : ℝ))

/-- Closed form of `q11Weta (Li2Lean.p0EllipsePoint 1 θ)`. -/
def q11WformClosed (θ : ℝ) : ℝ :=
  q11SegForm (ellX θ) (ellY θ) - 2 * q11ContourPotentialFourier θ

theorem q11SegForm_zero (X : ℝ) :
    q11SegForm X 0 =
      (primitive (X - 1 / 4) - primitive (X - 5 / 4) +
        (primitive X - primitive (X - 2))) -
      (X * (Real.log 2 + q11Lambda) + (primitive (X + 1 / 2) - primitive X) +
        1 / 2 - (1 / 2 : ℝ) * Real.log (1 / 2 : ℝ)) -
      2 * (∑ j ∈ Finset.range 8,
        q11IntervalDensity pinnedMassUnits (1 / 8 : ℝ) j *
          (primitive (X - q11PinnedEdgeReal j) -
            primitive (X - q11PinnedEdgeReal (j + 1)))) -
      (∑ j ∈ Finset.range 4,
        q11IntervalDensity frequencyMassUnits 1 j *
          (primitive (X + q11FrequencyEdgeReal (j + 1)) -
            primitive (X + q11FrequencyEdgeReal j))) := by
  simp only [q11SegForm, q11SegComb, Gr_zero, ← sub_eq_add_neg, add_zero, sub_zero]
  ring

theorem q11SegForm_eq {X Y : ℝ} (hY : Y ≠ 0) :
    Config.A0 ((X : ℂ) + (Y : ℂ) * Complex.I) -
        q11Phi ((X : ℂ) + (Y : ℂ) * Complex.I) -
        2 * q11PinnedComplexPotential ((X : ℂ) + (Y : ℂ) * Complex.I) -
        q11ReflectedFrequencyPotential ((X : ℂ) + (Y : ℂ) * Complex.I) =
      q11SegForm X Y := by
  have hA0 : Config.A0 ((X : ℂ) + (Y : ℂ) * Complex.I) =
      Gr (X - 1 / 4) Y - Gr (X - 5 / 4) Y + (Gr (X - 0) Y - Gr (X - 2) Y) := by
    simp only [Config.A0]
    rw [integral_log_norm_sub hY, integral_log_norm_sub hY]
  have hphi : q11Phi ((X : ℂ) + (Y : ℂ) * Complex.I) =
      X * (Real.log 2 + q11Lambda) + (Gr (X + 1 / 2) Y - Gr (X + 0) Y) +
        1 / 2 - (1 / 2 : ℝ) * Real.log (1 / 2 : ℝ) := by
    unfold q11Phi Config.phi
    rw [integral_log_norm_add hY]
    simp
    ring
  have hpin : q11PinnedComplexPotential ((X : ℂ) + (Y : ℂ) * Complex.I) =
      ∑ j ∈ Finset.range 8,
        q11IntervalDensity pinnedMassUnits (1 / 8 : ℝ) j *
          (Gr (X - q11PinnedEdgeReal j) Y -
            Gr (X - q11PinnedEdgeReal (j + 1)) Y) := by
    unfold q11PinnedComplexPotential q11PinnedReferenceMeasure
    apply q11IntervalComplexPotential_eq hY
    · norm_num
    · intro j hj
      have hw := q11PinnedEdgeReal_width (Finset.mem_range.mp hj)
      linarith
  have hfreq : q11ReflectedFrequencyPotential ((X : ℂ) + (Y : ℂ) * Complex.I) =
      ∑ j ∈ Finset.range 4,
        q11IntervalDensity frequencyMassUnits 1 j *
          (Gr (X + q11FrequencyEdgeReal (j + 1)) Y -
            Gr (X + q11FrequencyEdgeReal j) Y) := by
    unfold q11ReflectedFrequencyPotential q11FrequencyReferenceMeasure
    apply q11IntervalComplexPotential_add_eq hY
    · norm_num
    · intro j hj
      have hw := q11FrequencyEdgeReal_width (Finset.mem_range.mp hj)
      linarith
  rw [hA0, hphi, hpin, hfreq]
  simp only [q11SegForm, q11SegComb, ← sub_eq_add_neg, add_zero, sub_zero]
  ring

theorem q11Weta_ellipse_eq_q11WformClosed (θ : ℝ) :
    q11Weta (Li2Lean.p0EllipsePoint 1 θ) = q11WformClosed θ := by
  have hcont : q11ContourPotential (Li2Lean.p0EllipsePoint 1 θ) =
      q11ContourPotentialFourier θ :=
    q11ContourPotential_eq_fourier θ
  by_cases hY : ellY θ = 0
  · have hz : Li2Lean.p0EllipsePoint 1 θ = ((ellX θ : ℝ) : ℂ) := by
      rw [ellipse_eq, hY]; simp
    have hc := hcont
    rw [hz] at hc ⊢
    simp only [q11Weta, q11ActualReference, q11EtaReferencePotential]
    rw [A0_ofReal_eq_endpoints, q11Phi_ofReal_eq_endpoints,
      q11PinnedComplexPotential_ofReal_eq_endpoints,
      q11ReflectedFrequencyPotential_ofReal_eq_endpoints, hc]
    unfold q11WformClosed
    rw [hY, q11SegForm_zero]
    ring
  · simp only [q11Weta, q11ActualReference, q11EtaReferencePotential]
    rw [hcont]
    unfold q11WformClosed
    rw [← q11SegForm_eq hY, ← ellipse_eq]
    ring

theorem p0EllipsePoint_one_eq_gammaPoint (θ : ℝ) :
    Li2Lean.p0EllipsePoint 1 θ = gammaPoint θ := by
  simpa [Li2Lean.P0.ellipsePoint] using Li2Lean.P0.ellipsePoint_one_eq_gammaPoint θ

theorem q11Wform_eq_closed (θ : ℝ) :
    q11Wform θ = q11WformClosed θ := by
  unfold q11Wform
  rw [← p0EllipsePoint_one_eq_gammaPoint, q11Weta_ellipse_eq_q11WformClosed]

/-! ## 2. First and Second Derivatives of `q11WformClosed` -/

theorem hasDerivAt_q11SegComb {G G' : ℝ → ℝ → ℝ} {lin : ℝ → ℝ} {lin' c θ : ℝ}
    (hG : ∀ κ, HasDerivAt (fun t => G t κ) (G' θ κ) θ)
    (hl : HasDerivAt lin lin' θ) :
    HasDerivAt (fun t => q11SegComb (G t) (lin t) c) (q11SegComb (G' θ) lin' 0) θ := by
  have hs1 : HasDerivAt
      (fun t => ∑ j ∈ Finset.range 8,
        q11IntervalDensity pinnedMassUnits (1 / 8 : ℝ) j *
          (G t (-q11PinnedEdgeReal j) - G t (-q11PinnedEdgeReal (j + 1))))
      (∑ j ∈ Finset.range 8,
        q11IntervalDensity pinnedMassUnits (1 / 8 : ℝ) j *
          (G' θ (-q11PinnedEdgeReal j) - G' θ (-q11PinnedEdgeReal (j + 1)))) θ :=
    HasDerivAt.fun_sum (fun _ _ => ((hG _).sub (hG _)).const_mul _)
  have hs2 : HasDerivAt
      (fun t => ∑ j ∈ Finset.range 4,
        q11IntervalDensity frequencyMassUnits 1 j *
          (G t (q11FrequencyEdgeReal (j + 1)) - G t (q11FrequencyEdgeReal j)))
      (∑ j ∈ Finset.range 4,
        q11IntervalDensity frequencyMassUnits 1 j *
          (G' θ (q11FrequencyEdgeReal (j + 1)) - G' θ (q11FrequencyEdgeReal j))) θ :=
    HasDerivAt.fun_sum (fun _ _ => ((hG _).sub (hG _)).const_mul _)
  have h := ((((hG (-(1 / 4))).sub (hG (-(5 / 4)))).add ((hG 0).sub (hG (-2)))).sub
    ((hl.add ((hG (1 / 2)).sub (hG 0))).add_const c)).sub (hs1.const_mul 2) |>.sub hs2
  unfold q11SegComb
  convert h using 1
  ring

def q11BR (n : ℕ) : ℝ :=
  (1 + contourRatio ^ (n + 1)) * q11ContourFourierMoment (n + 1) / (n + 1 : ℝ)

def q11F1 (θ : ℝ) : ℝ :=
  ∑ n ∈ Finset.range 48, q11BR n * ((n + 1 : ℝ) * Real.sin ((n + 1 : ℝ) * θ))

def q11F2 (θ : ℝ) : ℝ :=
  ∑ n ∈ Finset.range 48, q11BR n * ((n + 1 : ℝ) ^ 2 * Real.cos ((n + 1 : ℝ) * θ))

theorem q11Fourier_eq (θ : ℝ) :
    q11ContourPotentialFourier θ =
      q11ContourMass * Real.log contourScale -
        ∑ n ∈ Finset.range 48, q11BR n * Real.cos ((n + 1 : ℝ) * θ) := rfl

theorem hasDerivAt_q11Fourier (θ : ℝ) :
    HasDerivAt q11ContourPotentialFourier (q11F1 θ) θ := by
  have hsum : HasDerivAt
      (fun x : ℝ => ∑ n ∈ Finset.range 48, q11BR n * Real.cos ((n + 1 : ℝ) * x))
      (∑ n ∈ Finset.range 48,
        q11BR n * (-(Real.sin ((n + 1 : ℝ) * θ)) * ((n + 1 : ℝ) * 1))) θ := by
    apply HasDerivAt.fun_sum
    intro n _
    exact ((Real.hasDerivAt_cos _).comp θ
      ((hasDerivAt_id θ).const_mul (n + 1 : ℝ))).const_mul (q11BR n)
  have h := (hasDerivAt_const θ (q11ContourMass * Real.log contourScale)).sub hsum
  rw [show q11ContourPotentialFourier = fun x => q11ContourMass * Real.log contourScale -
      ∑ n ∈ Finset.range 48, q11BR n * Real.cos ((n + 1 : ℝ) * x) from funext q11Fourier_eq]
  convert h using 1
  unfold q11F1
  rw [zero_sub, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro n _
  ring

theorem hasDerivAt_q11F1 (θ : ℝ) : HasDerivAt q11F1 (q11F2 θ) θ := by
  unfold q11F1 q11F2
  apply HasDerivAt.fun_sum
  intro n _
  have h := (((Real.hasDerivAt_sin _).comp θ
      ((hasDerivAt_id θ).const_mul (n + 1 : ℝ))).const_mul
      ((n + 1 : ℝ))).const_mul (q11BR n)
  refine h.congr_deriv ?_
  simp only [id]
  ring

def q11W1Closed (θ : ℝ) : ℝ :=
  q11SegComb (fun κ => dGr (ellX θ + κ) (ellY θ) (ellX1 θ) (ellY1 θ))
    (ellX1 θ * (Real.log 2 + q11Lambda)) 0 - 2 * q11F1 θ

def q11W2Closed (θ : ℝ) : ℝ :=
  q11SegComb (fun κ => d2Gr (ellX θ + κ) (ellY θ) (ellX1 θ) (ellY1 θ) (ellX2 θ) (ellY2 θ))
    (ellX2 θ * (Real.log 2 + q11Lambda)) 0 - 2 * q11F2 θ

theorem hasDerivAt_q11WformClosed {θ : ℝ} (hs : Real.sin θ ≠ 0) :
    HasDerivAt q11WformClosed (q11W1Closed θ) θ := by
  have hY : ellY θ ≠ 0 := by unfold ellY; exact mul_ne_zero (by norm_num) hs
  have hseg := hasDerivAt_q11SegComb (c := 1 / 2 - (1 / 2 : ℝ) * Real.log (1 / 2 : ℝ))
    (G := fun t κ => Gr (ellX t + κ) (ellY t))
    (G' := fun t κ => dGr (ellX t + κ) (ellY t) (ellX1 t) (ellY1 t))
    (lin := fun t => ellX t * (Real.log 2 + q11Lambda))
    (fun κ => hasDerivAt_Gr_comp ((hasDerivAt_ellX θ).add_const κ)
      (hasDerivAt_ellY θ) hY)
    ((hasDerivAt_ellX θ).mul_const (Real.log 2 + q11Lambda))
  exact hseg.sub ((hasDerivAt_q11Fourier θ).const_mul 2)

theorem hasDerivAt_q11W1Closed {θ : ℝ} (hs : Real.sin θ ≠ 0) :
    HasDerivAt q11W1Closed (q11W2Closed θ) θ := by
  have hY : ellY θ ≠ 0 := by unfold ellY; exact mul_ne_zero (by norm_num) hs
  have hseg := hasDerivAt_q11SegComb (c := 0)
    (G := fun t κ => dGr (ellX t + κ) (ellY t) (ellX1 t) (ellY1 t))
    (G' := fun t κ => d2Gr (ellX t + κ) (ellY t) (ellX1 t) (ellY1 t) (ellX2 t) (ellY2 t))
    (lin := fun t => ellX1 t * (Real.log 2 + q11Lambda))
    (fun κ => hasDerivAt_dGr_comp (u := fun t => ellX t + κ)
      ((hasDerivAt_ellX θ).add_const κ) (hasDerivAt_ellY θ)
      (hasDerivAt_ellX1 θ) (hasDerivAt_ellY1 θ) hY)
    ((hasDerivAt_ellX1 θ).mul_const (Real.log 2 + q11Lambda))
  exact hseg.sub ((hasDerivAt_q11F1 θ).const_mul 2)

theorem q11W1_eq_closed {θ : ℝ} (hs : Real.sin θ ≠ 0) :
    q11W1 θ = q11W1Closed θ := by
  unfold q11W1
  rw [show q11Wform = q11WformClosed from funext q11Wform_eq_closed]
  exact (hasDerivAt_q11WformClosed hs).deriv

theorem hasDerivAt_q11Wform_on_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 Real.pi) :
    HasDerivAt q11Wform (q11W1 θ) θ := by
  have hs := sin_ne_zero_of_mem hθ
  rw [show q11Wform = q11WformClosed from funext q11Wform_eq_closed, q11W1_eq_closed hs]
  exact hasDerivAt_q11WformClosed hs

theorem q11W2_eq_closed {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 Real.pi) :
    q11W2 θ = q11W2Closed θ := by
  have hs := sin_ne_zero_of_mem hθ
  have heq : q11W1 =ᶠ[nhds θ] q11W1Closed := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with x hx
    exact q11W1_eq_closed (sin_ne_zero_of_mem hx)
  unfold q11W2
  rw [heq.deriv_eq]
  exact (hasDerivAt_q11W1Closed hs).deriv

theorem hasDerivAt_q11W1_on_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 Real.pi) :
    HasDerivAt q11W1 (q11W2 θ) θ := by
  have hs := sin_ne_zero_of_mem hθ
  have heq : q11W1 =ᶠ[nhds θ] q11W1Closed := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with x hx
    exact q11W1_eq_closed (sin_ne_zero_of_mem hx)
  rw [q11W2_eq_closed hθ]
  exact (hasDerivAt_q11W1Closed hs).congr_of_eventuallyEq heq

/-! ## 3. Global Second-Derivative Bound `|q11W2Closed θ| ≤ 2200` and Taylor Lower Bound -/

theorem sum_q11RhoP :
    (∑ j ∈ Finset.range 8, q11IntervalDensity pinnedMassUnits (1 / 8 : ℝ) j) =
      8 * 1647154788848 / 3000000000000 := by
  have h : (∑ j ∈ Finset.range 8, q11IntervalDensity pinnedMassUnits (1 / 8 : ℝ) j) =
      (∑ j ∈ Finset.range 8, q11MassUnitReal pinnedMassUnits j) / (1 / 8 : ℝ) := by
    unfold q11IntervalDensity
    rw [Finset.sum_div]
  rw [h, q11PinnedMassUnitReal_sum, pinned_mass_sum]
  norm_num [denominator]

theorem sum_q11RhoF :
    (∑ j ∈ Finset.range 4, q11IntervalDensity frequencyMassUnits 1 j) = 1 := by
  have h : (∑ j ∈ Finset.range 4, q11IntervalDensity frequencyMassUnits 1 j) =
      ∑ j ∈ Finset.range 4, q11MassUnitReal frequencyMassUnits j := by
    unfold q11IntervalDensity
    simp
  rw [h]
  unfold q11MassUnitReal
  rw [← Finset.sum_div, ← frequency_masses_length, q11_sum_getD_cast, frequency_mass_sum]
  norm_num [denominator]

theorem shiftP_q11PinnedEdge {j : ℕ} (hj : j ≤ 8) :
    ShiftP (-q11PinnedEdgeReal j) := by
  interval_cases j <;>
    norm_num [ShiftP, q11PinnedEdgeReal, pinnedEdge, pinnedEdge32Units]

theorem shiftF_q11FrequencyEdge {j : ℕ} (hj : j ≤ 4) :
    ShiftF (q11FrequencyEdgeReal j) := by
  interval_cases j <;>
    norm_num [ShiftF, q11FrequencyEdgeReal, frequencyEdge, frequencyEdge2Units]

theorem q11SegComb_abs_le {g : ℝ → ℝ} {KA KP KF lin : ℝ}
    (hA : ∀ κ, ShiftA κ → |g κ| ≤ KA)
    (hP : ∀ κ, ShiftP κ → |g κ| ≤ KP)
    (hF : ∀ κ, ShiftF κ → |g κ| ≤ KF) :
    |q11SegComb g lin 0| ≤
      (2 + 4 * (8 * 1647154788848 / 3000000000000)) * KP +
        3 * KA + 3 * KF + |lin| := by
  have hs1 : |∑ j ∈ Finset.range 8,
        q11IntervalDensity pinnedMassUnits (1 / 8 : ℝ) j *
          (g (-q11PinnedEdgeReal j) - g (-q11PinnedEdgeReal (j + 1)))| ≤
      (8 * 1647154788848 / 3000000000000) * (2 * KP) := by
    calc _ ≤ ∑ j ∈ Finset.range 8,
          |q11IntervalDensity pinnedMassUnits (1 / 8 : ℝ) j *
            (g (-q11PinnedEdgeReal j) - g (-q11PinnedEdgeReal (j + 1)))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Finset.range 8,
          q11IntervalDensity pinnedMassUnits (1 / 8 : ℝ) j * (2 * KP) := by
        apply Finset.sum_le_sum
        intro j hj
        have hj8 : j < 8 := Finset.mem_range.mp hj
        have hpos := q11IntervalDensity_nonneg pinnedMassUnits (by norm_num : (0 : ℝ) < 1 / 8) j
        rw [abs_mul, abs_of_nonneg hpos]
        apply mul_le_mul_of_nonneg_left _ hpos
        have h1 := hP _ (shiftP_q11PinnedEdge (by omega : j ≤ 8))
        have h2 := hP _ (shiftP_q11PinnedEdge (by omega : j + 1 ≤ 8))
        calc |g (-q11PinnedEdgeReal j) - g (-q11PinnedEdgeReal (j + 1))|
            ≤ |g (-q11PinnedEdgeReal j)| + |g (-q11PinnedEdgeReal (j + 1))| := abs_sub _ _
          _ ≤ 2 * KP := by linarith
      _ = _ := by rw [← Finset.sum_mul, sum_q11RhoP]
  have hs2 : |∑ j ∈ Finset.range 4,
        q11IntervalDensity frequencyMassUnits 1 j *
          (g (q11FrequencyEdgeReal (j + 1)) - g (q11FrequencyEdgeReal j))| ≤
      1 * (2 * KF) := by
    calc _ ≤ ∑ j ∈ Finset.range 4,
          |q11IntervalDensity frequencyMassUnits 1 j *
            (g (q11FrequencyEdgeReal (j + 1)) - g (q11FrequencyEdgeReal j))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Finset.range 4,
          q11IntervalDensity frequencyMassUnits 1 j * (2 * KF) := by
        apply Finset.sum_le_sum
        intro j hj
        have hj4 : j < 4 := Finset.mem_range.mp hj
        have hpos := q11IntervalDensity_nonneg frequencyMassUnits (by norm_num : (0 : ℝ) < 1) j
        rw [abs_mul, abs_of_nonneg hpos]
        apply mul_le_mul_of_nonneg_left _ hpos
        have h1 := hF _ (shiftF_q11FrequencyEdge (by omega : j + 1 ≤ 4))
        have h2 := hF _ (shiftF_q11FrequencyEdge (by omega : j ≤ 4))
        calc |g (q11FrequencyEdgeReal (j + 1)) - g (q11FrequencyEdgeReal j)|
            ≤ |g (q11FrequencyEdgeReal (j + 1))| + |g (q11FrequencyEdgeReal j)| := abs_sub _ _
          _ ≤ 2 * KF := by linarith
      _ = _ := by rw [← Finset.sum_mul, sum_q11RhoF]
  have p1 := hP (-(1 / 4)) ⟨by norm_num, by norm_num⟩
  have p2 := hP (-(5 / 4)) ⟨by norm_num, by norm_num⟩
  have a0 := hA 0 ⟨by norm_num, by norm_num⟩
  have a2 := hA (-2) ⟨by norm_num, by norm_num⟩
  have f0 := hF (1 / 2) ⟨by norm_num, by norm_num⟩
  unfold q11SegComb
  set S1 := ∑ j ∈ Finset.range 8,
    q11IntervalDensity pinnedMassUnits (1 / 8 : ℝ) j *
      (g (-q11PinnedEdgeReal j) - g (-q11PinnedEdgeReal (j + 1)))
  set S2 := ∑ j ∈ Finset.range 4,
    q11IntervalDensity frequencyMassUnits 1 j *
      (g (q11FrequencyEdgeReal (j + 1)) - g (q11FrequencyEdgeReal j))
  have e : (g (-(1 / 4)) - g (-(5 / 4)) + (g 0 - g (-2))) - (lin + (g (1 / 2) - g 0) + 0) -
      2 * S1 - S2 = g (-(1 / 4)) - g (-(5 / 4)) + g 0 - g (-2) - g (1 / 2) + g 0 -
      lin - 2 * S1 - S2 := by ring
  rw [e]
  have t6 : |2 * S1| = 2 * |S1| := by rw [abs_mul]; norm_num
  have tri : ∀ a b : ℝ, |a - b| ≤ |a| + |b| := fun a b => abs_sub a b
  have tri2 : ∀ a b : ℝ, |a + b| ≤ |a| + |b| := fun a b => abs_add_le a b
  have := tri (g (-(1 / 4)) - g (-(5 / 4)) + g 0 - g (-2) - g (1 / 2) + g 0 - lin - 2 * S1) S2
  have := tri (g (-(1 / 4)) - g (-(5 / 4)) + g 0 - g (-2) - g (1 / 2) + g 0 - lin) (2 * S1)
  have := tri (g (-(1 / 4)) - g (-(5 / 4)) + g 0 - g (-2) - g (1 / 2) + g 0) lin
  have := tri2 (g (-(1 / 4)) - g (-(5 / 4)) + g 0 - g (-2) - g (1 / 2)) (g 0)
  have := tri (g (-(1 / 4)) - g (-(5 / 4)) + g 0 - g (-2)) (g (1 / 2))
  have := tri (g (-(1 / 4)) - g (-(5 / 4)) + g 0) (g (-2))
  have := tri2 (g (-(1 / 4)) - g (-(5 / 4))) (g 0)
  have := tri (g (-(1 / 4))) (g (-(5 / 4)))
  linarith

theorem q11ContourFourierMoment_mul_le (k : ℕ) (hk : k ≤ 48) :
    |q11ContourFourierMoment k| * (k : ℝ) ≤ (49 / 4 : ℝ) * q11ContourMass := by
  have hmass : 0 ≤ q11ContourMass := by
    rw [q11ContourMass_eq_sum]
    exact Finset.sum_nonneg (fun j _ => q11ContourWeight_nonneg j)
  unfold q11ContourFourierMoment
  rw [if_pos hk]
  have hk49 : (k : ℝ) ≤ 49 := by exact_mod_cast (Nat.le_succ_of_le hk)
  have hcoef0 : 0 ≤ 1 - (k : ℝ) / 49 := by linarith
  have hsum :
      |∑ j : Fin contourNodeCount,
        q11ContourWeight j * Real.cos ((k : ℝ) * contourAngle j)| ≤ q11ContourMass := by
    calc |∑ j : Fin contourNodeCount,
            q11ContourWeight j * Real.cos ((k : ℝ) * contourAngle j)|
        ≤ ∑ j : Fin contourNodeCount,
            |q11ContourWeight j * Real.cos ((k : ℝ) * contourAngle j)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j : Fin contourNodeCount, q11ContourWeight j := by
          apply Finset.sum_le_sum
          intro j _
          rw [abs_mul, abs_of_nonneg (q11ContourWeight_nonneg j)]
          exact mul_le_of_le_one_right (q11ContourWeight_nonneg j) (Real.abs_cos_le_one _)
      _ = q11ContourMass := q11ContourMass_eq_sum.symm
  rw [abs_mul, abs_of_nonneg hcoef0]
  have hquad : (1 - (k : ℝ) / 49) * (k : ℝ) ≤ 49 / 4 := by
    nlinarith [sq_nonneg (2 * (k : ℝ) - 49)]
  have hk0 : (0 : ℝ) ≤ k := by positivity
  calc (1 - (k : ℝ) / 49) *
        |∑ j : Fin contourNodeCount,
          q11ContourWeight j * Real.cos ((k : ℝ) * contourAngle j)| * (k : ℝ)
      = ((1 - (k : ℝ) / 49) * (k : ℝ)) *
          |∑ j : Fin contourNodeCount,
            q11ContourWeight j * Real.cos ((k : ℝ) * contourAngle j)| := by ring
    _ ≤ (49 / 4) * q11ContourMass :=
        mul_le_mul hquad hsum (abs_nonneg _) (by positivity)

theorem q11F2_abs_le (θ : ℝ) :
    |q11F2 θ| ≤ 1176 * q11ContourMass := by
  have hmass : 0 ≤ q11ContourMass := by
    rw [q11ContourMass_eq_sum]
    exact Finset.sum_nonneg (fun j _ => q11ContourWeight_nonneg j)
  unfold q11F2
  calc |∑ n ∈ Finset.range 48,
        q11BR n * ((n + 1 : ℝ) ^ 2 * Real.cos ((n + 1 : ℝ) * θ))|
      ≤ ∑ n ∈ Finset.range 48,
        |q11BR n * ((n + 1 : ℝ) ^ 2 * Real.cos ((n + 1 : ℝ) * θ))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ Finset.range 48, (49 / 2 : ℝ) * q11ContourMass := by
        apply Finset.sum_le_sum
        intro n hn
        have hn48 : n + 1 ≤ 48 := Finset.mem_range.mp hn
        have hnpos : (0 : ℝ) < (n + 1 : ℕ) := by positivity
        have hq0 : 0 ≤ contourRatio ^ (n + 1) := pow_nonneg contourRatio_nonneg _
        have hq1 : contourRatio ^ (n + 1) ≤ 1 :=
          pow_le_one₀ contourRatio_nonneg (by norm_num [contourRatio])
        have hm := q11ContourFourierMoment_mul_le (n + 1) hn48
        have hcos := Real.abs_cos_le_one ((n + 1 : ℝ) * θ)
        have hterm_eq :
            q11BR n * ((n + 1 : ℝ) ^ 2 * Real.cos ((n + 1 : ℝ) * θ)) =
              (1 + contourRatio ^ (n + 1)) *
                (q11ContourFourierMoment (n + 1) * ((n + 1 : ℕ) : ℝ)) *
                Real.cos ((n + 1 : ℝ) * θ) := by
          unfold q11BR
          push_cast
          field_simp [ (by positivity : (0 : ℝ) < (n : ℝ) + 1).ne' ]
        rw [hterm_eq, abs_mul, abs_mul, abs_mul,
          abs_of_nonneg (by positivity : 0 ≤ 1 + contourRatio ^ (n + 1)),
          abs_of_pos hnpos]
        have hprod1 :
            (1 + contourRatio ^ (n + 1)) *
              (|q11ContourFourierMoment (n + 1)| * ((n + 1 : ℕ) : ℝ)) ≤
              (49 / 2 : ℝ) * q11ContourMass := by
          nlinarith [hm, hmass, abs_nonneg (q11ContourFourierMoment (n + 1))]
        calc (1 + contourRatio ^ (n + 1)) *
              (|q11ContourFourierMoment (n + 1)| * ((n + 1 : ℕ) : ℝ)) *
              |Real.cos ((n + 1 : ℝ) * θ)|
            ≤ ((49 / 2 : ℝ) * q11ContourMass) * 1 :=
              mul_le_mul hprod1 hcos (abs_nonneg _) (by positivity)
          _ = (49 / 2 : ℝ) * q11ContourMass := by ring
    _ = 1176 * q11ContourMass := by norm_num; ring

theorem q11W2Closed_abs_le (θ : ℝ) : |q11W2Closed θ| ≤ 2200 := by
  have hS : ellX1 θ ^ 2 + ellY1 θ ^ 2 ≤ (12783 / 10000) ^ 2 := by
    unfold ellX1 ellY1
    nlinarith [Real.sin_sq_add_cos_sq θ, sq_nonneg (Real.cos θ)]
  have ha2 : |ellX2 θ| ≤ 12783 / 10000 := by
    unfold ellX2; rw [abs_mul]
    have := Real.abs_cos_le_one θ
    norm_num; nlinarith [abs_nonneg (Real.cos θ)]
  have hb2 : |ellY2 θ| ≤ 229 / 200 := by
    unfold ellY2; rw [abs_mul]
    have := Real.abs_sin_le_one θ
    norm_num; nlinarith [abs_nonneg (Real.sin θ)]
  have hA : ∀ κ, ShiftA κ →
      |d2Gr (ellX θ + κ) (ellY θ) (ellX1 θ) (ellY1 θ) (ellX2 θ) (ellY2 θ)| ≤ 2625 / 100 := by
    intro κ hκ
    have hs : Shift κ := Or.inl hκ
    have := d2Gr_bound (δ := 3 / 20) (by norm_num) (by have := dist_lower θ hs; nlinarith)
      (dist_lower θ hs) (dist_upper θ hs) hS ha2 hb2
    linarith
  have hP : ∀ κ, ShiftP κ →
      |d2Gr (ellX θ + κ) (ellY θ) (ellX1 θ) (ellY1 θ) (ellX2 θ) (ellY2 θ)| ≤ 1263 / 100 := by
    intro κ hκ
    have hs : Shift κ := Or.inl ⟨by linarith [hκ.1], by linarith [hκ.2]⟩
    have hd := dist_lower_P θ (x := -κ) hκ.1 hκ.2
    rw [sub_neg_eq_add] at hd
    have := d2Gr_bound (δ := 2 / 5) (by norm_num) (by nlinarith)
      (dist_lower θ hs) (dist_upper θ hs) hS ha2 hb2
    linarith
  have hF : ∀ κ, ShiftF κ →
      |d2Gr (ellX θ + κ) (ellY θ) (ellX1 θ) (ellY1 θ) (ellX2 θ) (ellY2 θ)| ≤ 138 / 10 := by
    intro κ hκ
    have hs : Shift κ := Or.inr hκ
    have hmem : Li2Lean.p0EllipsePoint 1 θ ∈ Config.baseEllipseSet := ⟨θ, rfl⟩
    have h := Config.mixedCellClearance_full.2 _ hmem κ hκ.1
    rw [norm_ellipse_add] at h
    have h2 := pow_le_pow_left₀ (by norm_num [Config.dMinus]) h 2
    rw [Real.sq_sqrt (by positivity)] at h2
    have := d2Gr_bound (δ := 1749 / 5000) (by norm_num)
      (by norm_num [Config.dMinus] at h2 ⊢; linarith)
      (dist_lower θ hs) (dist_upper θ hs) hS ha2 hb2
    linarith
  have hseg := q11SegComb_abs_le (lin := ellX2 θ * (Real.log 2 + q11Lambda)) hA hP hF
  have hlog2_pos : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog11_pos : 0 ≤ q11Lambda := Real.log_nonneg (by norm_num [q11Lambda])
  have hlog11_upper : q11Lambda ≤ 9 / 2 := by
    unfold q11Lambda
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 11 / 2)
    linarith
  have hlin : |ellX2 θ * (Real.log 2 + q11Lambda)| ≤ 7 := by
    rw [abs_mul, abs_of_nonneg (add_nonneg hlog2_pos hlog11_pos)]
    have hsum_le : Real.log 2 + q11Lambda ≤ 26 / 5 := by
      linarith [log_two_lt, hlog11_upper]
    nlinarith [abs_nonneg (ellX2 θ)]
  have hF2 := q11F2_abs_le θ
  have hmass_val : q11ContourMass = 2 * 676422605576 / 3000000000000 := by
    unfold q11ContourMass
    rw [contour_pair_mass_sum]
    norm_num [denominator]
  rw [hmass_val] at hF2
  unfold q11W2Closed
  calc |q11SegComb
        (fun κ => d2Gr (ellX θ + κ) (ellY θ) (ellX1 θ) (ellY1 θ) (ellX2 θ) (ellY2 θ))
        (ellX2 θ * (Real.log 2 + q11Lambda)) 0 - 2 * q11F2 θ|
      ≤ |q11SegComb
          (fun κ => d2Gr (ellX θ + κ) (ellY θ) (ellX1 θ) (ellY1 θ) (ellX2 θ) (ellY2 θ))
          (ellX2 θ * (Real.log 2 + q11Lambda)) 0| + |2 * q11F2 θ| := abs_sub _ _
    _ ≤ 2200 := by
        rw [abs_mul, abs_two]
        linarith

theorem q11W2_abs_le {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 Real.pi) :
    |q11W2 θ| ≤ 2200 := by
  rw [q11W2_eq_closed hθ]
  exact q11W2Closed_abs_le θ

/-- Second-order Taylor lower bound on `Set.Ioo 0 Real.pi` for `q11Wform` / `q11WformClosed`. -/
theorem q11_taylor_lower {θ θ0 : ℝ}
    (h : θ ∈ Set.Ioo 0 Real.pi) (h0 : θ0 ∈ Set.Ioo 0 Real.pi) :
    q11Wform θ0 + q11W1 θ0 * (θ - θ0) - 1100 * (θ - θ0) ^ 2 ≤ q11Wform θ := by
  have hab : Set.Icc (min θ θ0) (max θ θ0) ⊆ Set.Ioo 0 Real.pi := by
    intro x hx
    exact ⟨lt_of_lt_of_le (lt_min h.1 h0.1) hx.1,
      lt_of_le_of_lt hx.2 (max_lt h.2 h0.2)⟩
  have h := q11_local_taylor_lower
    (a := min θ θ0) (b := max θ θ0) (theta := θ) (theta0 := θ0) (M2 := 2200)
    hab ⟨min_le_left _ _, le_max_left _ _⟩ ⟨min_le_right _ _, le_max_right _ _⟩
    (by norm_num)
    (fun x hx => hasDerivAt_q11Wform_on_Ioo hx)
    (fun x hx => hasDerivAt_q11W1_on_Ioo hx)
    (fun x hx => q11W2_abs_le (hab hx))
  linarith

/-! ## 4. Reflected Interval Evaluator `q11WI` and `q11DI` -/

def q11RhoPQ (j : ℕ) : ℚ := q11DensityQ pinnedMassUnits (1 / 8) j
def q11RhoFQ (j : ℕ) : ℚ := q11DensityQ frequencyMassUnits 1 j

theorem q11RhoPQ_eq (j : ℕ) :
    ((q11RhoPQ j : ℚ) : ℝ) = q11IntervalDensity pinnedMassUnits (1 / 8 : ℝ) j := by
  simpa [q11RhoPQ] using q11DensityQ_cast pinnedMassUnits (1 / 8) j

theorem q11RhoFQ_eq (j : ℕ) :
    ((q11RhoFQ j : ℚ) : ℝ) = q11IntervalDensity frequencyMassUnits 1 j := by
  simpa [q11RhoFQ] using q11DensityQ_cast frequencyMassUnits 1 j

def q11SegCombI (p f : ℕ → QI) (z0 z2 lin cst : QI) : QI :=
  sub (sub (sub (add (sub (p 0) (p 8)) (sub z0 z2)) (add (add lin (sub (f 0) z0)) cst))
      (smul 2 (sumIdx 8 (fun j => smul (q11RhoPQ j) (sub (p j) (p (j + 1)))))))
    (sumIdx 4 (fun j => smul (q11RhoFQ j) (sub (f (j + 1)) (f j))))

theorem q11SegCombI_mem {p f : ℕ → QI} {z0 z2 lin cst : QI} {g : ℝ → ℝ} {L C : ℝ}
    (hp : ∀ j ≤ 8, (p j).mem (g (-q11PinnedEdgeReal j)))
    (hf : ∀ j ≤ 4, (f j).mem (g (q11FrequencyEdgeReal j)))
    (h0 : z0.mem (g 0)) (h2 : z2.mem (g (-2))) (hl : lin.mem L) (hc : cst.mem C) :
    (q11SegCombI p f z0 z2 lin cst).mem (q11SegComb g L C) := by
  have hp0 : (p 0).mem (g (-(1 / 4))) := by
    have h := hp 0 (by omega)
    have he0 : q11PinnedEdgeReal 0 = 1 / 4 := by
      norm_num [q11PinnedEdgeReal, pinnedEdge, pinnedEdge32Units]
    rwa [he0] at h
  have hp8 : (p 8).mem (g (-(5 / 4))) := by
    have h := hp 8 (by omega)
    have he8 : q11PinnedEdgeReal 8 = 5 / 4 := by
      norm_num [q11PinnedEdgeReal, pinnedEdge, pinnedEdge32Units]
    rwa [he8] at h
  have hf0 : (f 0).mem (g (1 / 2)) := by
    have h := hf 0 (by omega)
    have hfe0 : q11FrequencyEdgeReal 0 = 1 / 2 := by
      norm_num [q11FrequencyEdgeReal, frequencyEdge, frequencyEdge2Units]
    rwa [hfe0] at h
  have s1 : (sumIdx 8 (fun j => smul (q11RhoPQ j) (sub (p j) (p (j + 1))))).mem
      (∑ j ∈ Finset.range 8,
        q11IntervalDensity pinnedMassUnits (1 / 8 : ℝ) j *
          (g (-q11PinnedEdgeReal j) - g (-q11PinnedEdgeReal (j + 1)))) := by
    apply mem_sumIdx
    intro j hj
    have := mem_smul (q11RhoPQ j) (mem_sub (hp j (by omega)) (hp (j + 1) (by omega)))
    rw [q11RhoPQ_eq] at this
    exact this
  have s2 : (sumIdx 4 (fun j => smul (q11RhoFQ j) (sub (f (j + 1)) (f j)))).mem
      (∑ j ∈ Finset.range 4,
        q11IntervalDensity frequencyMassUnits 1 j *
          (g (q11FrequencyEdgeReal (j + 1)) - g (q11FrequencyEdgeReal j))) := by
    apply mem_sumIdx
    intro j hj
    have := mem_smul (q11RhoFQ j) (mem_sub (hf (j + 1) (by omega)) (hf j (by omega)))
    rw [q11RhoFQ_eq] at this
    exact this
  unfold q11SegCombI q11SegComb
  have := mem_sub (mem_sub (mem_sub (mem_add (mem_sub hp0 hp8) (mem_sub h0 h2))
    (mem_add (mem_add hl (mem_sub hf0 h0)) hc)) (by simpa using mem_smul 2 s1)) s2
  refine mem_of_eq this ?_
  norm_num

def q11PEdges (X Y : ℚ) : List EV :=
  (List.range 9).map (fun j => edge (X - pinnedEdge j) Y)

def q11FEdges (X Y : ℚ) : List EV :=
  (List.range 5).map (fun j => edge (X + frequencyEdge j) Y)

theorem q11PEdges_get (X Y : ℚ) {j : ℕ} (hj : j ≤ 8) :
    (q11PEdges X Y).getD j dflt = edge (X - pinnedEdge j) Y := by
  unfold q11PEdges
  exact getD_map_range _ _ (by omega : j < 9)

theorem q11FEdges_get (X Y : ℚ) {j : ℕ} (hj : j ≤ 4) :
    (q11FEdges X Y).getD j dflt = edge (X + frequencyEdge j) Y := by
  unfold q11FEdges
  exact getD_map_range _ _ (by omega : j < 5)

theorem q11PEdge_ok (X Y : ℚ) {j : ℕ} (hj : j ≤ 8) :
    ((q11PEdges X Y).getD j dflt).ok ((X : ℝ) + -q11PinnedEdgeReal j) Y := by
  rw [q11PEdges_get X Y hj]
  have := edge_ok (X - pinnedEdge j) Y
  unfold q11PinnedEdgeReal
  push_cast at this ⊢
  rwa [← sub_eq_add_neg]

theorem q11FEdge_ok (X Y : ℚ) {j : ℕ} (hj : j ≤ 4) :
    ((q11FEdges X Y).getD j dflt).ok ((X : ℝ) + q11FrequencyEdgeReal j) Y := by
  rw [q11FEdges_get X Y hj]
  have := edge_ok (X + frequencyEdge j) Y
  unfold q11FrequencyEdgeReal
  push_cast at this ⊢
  exact this

/-- Interval enclosure of `Real.log 2 + q11Lambda = Real.log 2 + Real.log (11 / 2)`. -/
def L11 : QI := add L2 (logI (11 / 2))

theorem L11_mem : L11.mem (Real.log 2 + q11Lambda) := by
  unfold L11 q11Lambda
  have h11 := logI_mem (q := 11 / 2) (by norm_num)
  push_cast at h11
  exact mem_add L2_mem h11

/-- Interval enclosure of `q11ContourMass * Real.log contourScale`. -/
def q11MLC : QI := smul q11ContourMassQ (logI (24233 / 20000))

theorem q11MLC_mem : q11MLC.mem (q11ContourMass * Real.log contourScale) := by
  have := mem_smul q11ContourMassQ (logI_mem (q := 24233 / 20000) (by norm_num))
  refine mem_of_eq this ?_
  rw [q11ContourMassQ_eq]
  simp [contourScale]

/-- Chebyshev recurrence for the `q = 11` Fourier sum and its derivative,
    parameterized by a coefficient enclosure `b : ℕ → QI`. -/
def q11FstateFrom (b : ℕ → QI) (c s : ℚ) : ℕ → FS
  | 0 => ⟨1, c, 0, s, pt 0, pt 0⟩
  | n + 1 =>
      let t := q11FstateFrom b c s n
      ⟨t.c1, 2 * c * t.c1 - t.c0, t.s1, 2 * c * t.s1 - t.s0,
        rnd (add t.v (smul t.c1 (b n))),
        rnd (add t.d (smul ((n + 1 : ℚ) * t.s1) (b n)))⟩

/-- Default `q = 11` Chebyshev evaluator using `q11BComp` from
    `Li2Lean.P0.Q11ContourSelfEnergyEnclosure`. -/
def q11Fstate (c s : ℚ) (n : ℕ) : FS := q11FstateFrom q11BComp c s n

theorem q11FstateFrom_spec {b : ℕ → QI}
    (hb_mem : ∀ k < 48, (b k).mem (q11BR k))
    {θ : ℝ} {c s : ℚ} (hc : Real.cos θ = c) (hs : Real.sin θ = s)
    (n : ℕ) (hn : n ≤ 48) :
    ((q11FstateFrom b c s n).c0 : ℝ) = Real.cos (n * θ) ∧
    ((q11FstateFrom b c s n).c1 : ℝ) = Real.cos ((n + 1 : ℕ) * θ) ∧
    ((q11FstateFrom b c s n).s0 : ℝ) = Real.sin (n * θ) ∧
    ((q11FstateFrom b c s n).s1 : ℝ) = Real.sin ((n + 1 : ℕ) * θ) ∧
    (q11FstateFrom b c s n).v.mem
      (∑ k ∈ Finset.range n, q11BR k * Real.cos ((k + 1 : ℝ) * θ)) ∧
    (q11FstateFrom b c s n).d.mem
      (∑ k ∈ Finset.range n, q11BR k * ((k + 1 : ℝ) * Real.sin ((k + 1 : ℝ) * θ))) := by
  induction n with
  | zero =>
      simp only [q11FstateFrom]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [hc, hs, QI.mem, pt]
  | succ n ih =>
      obtain ⟨a0, a1, b0, b1, hv, hd⟩ := ih (by omega)
      have hb := hb_mem n (by omega)
      simp only [q11FstateFrom]
      refine ⟨a1, ?_, b1, ?_, ?_, ?_⟩
      · rw [show n + 1 + 1 = n + 2 from rfl, cos_rec n θ, ← a1, ← a0, hc]; push_cast; ring
      · rw [show n + 1 + 1 = n + 2 from rfl, sin_rec n θ, ← b1, ← b0, hc]; push_cast; ring
      · apply mem_rnd
        rw [Finset.sum_range_succ]
        have := mem_add hv (mem_smul (q11FstateFrom b c s n).c1 hb)
        refine mem_of_eq this ?_
        rw [a1]; push_cast; ring
      · apply mem_rnd
        rw [Finset.sum_range_succ]
        have := mem_add hd (mem_smul ((n + 1 : ℚ) * (q11FstateFrom b c s n).s1) hb)
        refine mem_of_eq this ?_
        push_cast; rw [b1]; push_cast; ring

theorem q11Fstate_spec {θ : ℝ} {c s : ℚ} (hc : Real.cos θ = c) (hs : Real.sin θ = s)
    (n : ℕ) (hn : n ≤ 48) :
    ((q11Fstate c s n).c0 : ℝ) = Real.cos (n * θ) ∧
    ((q11Fstate c s n).c1 : ℝ) = Real.cos ((n + 1 : ℕ) * θ) ∧
    ((q11Fstate c s n).s0 : ℝ) = Real.sin (n * θ) ∧
    ((q11Fstate c s n).s1 : ℝ) = Real.sin ((n + 1 : ℕ) * θ) ∧
    (q11Fstate c s n).v.mem
      (∑ k ∈ Finset.range n, q11BR k * Real.cos ((k + 1 : ℝ) * θ)) ∧
    (q11Fstate c s n).d.mem
      (∑ k ∈ Finset.range n, q11BR k * ((k + 1 : ℝ) * Real.sin ((k + 1 : ℝ) * θ))) :=
  q11FstateFrom_spec (fun k hk => q11BComp_mem hk) hc hs n hn

def q11WIcore (X : ℚ) (pe fe : List EV) (e0 e2 : EV) (F : FS) : QI :=
  sub (q11SegCombI (fun j => (pe.getD j dflt).g) (fun j => (fe.getD j dflt).g) e0.g e2.g
      (smul X L11) (add (pt (1 / 2)) (smul (1 / 2) L2)))
    (smul 2 (sub q11MLC F.v))

def q11DIcore (Xp Yp : ℚ) (pe fe : List EV) (e0 e2 : EV) (F : FS) : QI :=
  let ds : EV → QI := fun e => add (smul Xp e.l) (smul Yp e.a)
  sub (q11SegCombI (fun j => ds (pe.getD j dflt)) (fun j => ds (fe.getD j dflt)) (ds e0) (ds e2)
      (smul Xp L11) (pt 0))
    (smul 2 F.d)

def q11WI (c s : ℚ) : QI :=
  q11WIcore (ellXq c) (q11PEdges (ellXq c) (ellYq s)) (q11FEdges (ellXq c) (ellYq s))
    (edge (ellXq c) (ellYq s)) (edge (ellXq c - 2) (ellYq s)) (q11Fstate c s 48)

def q11DI (c s : ℚ) : QI :=
  q11DIcore (-(12783 / 10000) * s) (229 / 200 * c) (q11PEdges (ellXq c) (ellYq s))
    (q11FEdges (ellXq c) (ellYq s)) (edge (ellXq c) (ellYq s)) (edge (ellXq c - 2) (ellYq s))
    (q11Fstate c s 48)

/-- Shared-edge evaluation of value and derivative at `(c, s)`. -/
def q11WDI (c s : ℚ) : QI × QI :=
  let X := ellXq c
  let Y := ellYq s
  let pe := q11PEdges X Y
  let fe := q11FEdges X Y
  let e0 := edge X Y
  let e2 := edge (X - 2) Y
  let F := q11Fstate c s 48
  (q11WIcore X pe fe e0 e2 F, q11DIcore (-(12783 / 10000) * s) (229 / 200 * c) pe fe e0 e2 F)

theorem q11WDI_eq (c s : ℚ) : q11WDI c s = (q11WI c s, q11DI c s) := rfl

theorem q11WI_mem_closed {θ : ℝ} {c s : ℚ} (hc : Real.cos θ = c) (hs : Real.sin θ = s) :
    (q11WI c s).mem (q11WformClosed θ) := by
  unfold q11WformClosed q11SegForm
  rw [q11Fourier_eq, ellX_eq hc, ellY_eq hs]
  obtain ⟨-, -, -, -, hv, -⟩ := q11Fstate_spec hc hs 48 le_rfl
  unfold q11WI q11WIcore
  set X := ellXq c
  set Y := ellYq s
  apply QI.mem_sub
  · apply q11SegCombI_mem
    · intro j hj; exact (q11PEdge_ok X Y hj).1
    · intro j hj; exact (q11FEdge_ok X Y hj).1
    · simpa using (edge_ok X Y).1
    · have h := (edge_ok (X - 2) Y).1
      rwa [show (((X - 2 : ℚ)) : ℝ) = (X : ℝ) + -2 by push_cast; ring] at h
    · exact mem_smul X L11_mem
    · have := mem_add (mem_pt (1 / 2)) (mem_smul (1 / 2) L2_mem)
      refine mem_of_eq this ?_
      rw [show Real.log (1 / 2) = -Real.log 2 by rw [one_div, Real.log_inv]]
      push_cast; ring
  · have := mem_smul 2 (mem_sub q11MLC_mem hv)
    refine mem_of_eq this ?_
    push_cast; ring

theorem q11WI_mem {θ : ℝ} {c s : ℚ} (hc : Real.cos θ = c) (hs : Real.sin θ = s) :
    (q11WI c s).mem (q11Wform θ) := by
  rw [q11Wform_eq_closed]
  exact q11WI_mem_closed hc hs

theorem q11DI_mem_closed {θ : ℝ} {c s : ℚ} (hc : Real.cos θ = c) (hs : Real.sin θ = s) :
    (q11DI c s).mem (q11W1Closed θ) := by
  obtain ⟨-, -, -, -, -, hd⟩ := q11Fstate_spec hc hs 48 le_rfl
  unfold q11W1Closed q11DI q11DIcore
  rw [ellX_eq hc, ellY_eq hs]
  have hX1 : ellX1 θ = ((-(12783 / 10000) * s : ℚ) : ℝ) := by simp [ellX1, hs]
  have hY1 : ellY1 θ = ((229 / 200 * c : ℚ) : ℝ) := by simp [ellY1, hc]
  rw [hX1, hY1]
  set X := ellXq c
  set Y := ellYq s
  have hds : ∀ (e : EV) (u : ℝ), e.ok u Y →
      (add (smul (-(12783 / 10000) * s) e.l) (smul (229 / 200 * c) e.a)).mem
        (dGr u Y ((-(12783 / 10000) * s : ℚ) : ℝ) ((229 / 200 * c : ℚ) : ℝ)) := by
    intro e u he
    have := mem_add (mem_smul (-(12783 / 10000) * s) he.2.1) (mem_smul (229 / 200 * c) he.2.2)
    refine mem_of_eq this ?_
    unfold dGr; ring
  apply QI.mem_sub
  · apply q11SegCombI_mem
    · intro j hj; exact hds _ _ (q11PEdge_ok X Y hj)
    · intro j hj; exact hds _ _ (q11FEdge_ok X Y hj)
    · have := hds _ _ (edge_ok X Y); simpa using this
    · exact hds _ _ (by
        have h := edge_ok (X - 2) Y
        rwa [show (((X - 2 : ℚ)) : ℝ) = (X : ℝ) + -2 by push_cast; ring] at h)
    · exact mem_smul _ L11_mem
    · exact mem_pt 0 |> fun h => by simpa using h
  · have := mem_smul 2 hd
    refine mem_of_eq this ?_
    unfold q11F1; push_cast; ring

theorem q11DI_mem {θ : ℝ} {c s : ℚ} (hθ : θ ∈ Set.Ioo 0 Real.pi)
    (hc : Real.cos θ = c) (hs : Real.sin θ = s) :
    (q11DI c s).mem (q11W1 θ) := by
  rw [q11W1_eq_closed (sin_ne_zero_of_mem hθ)]
  exact q11DI_mem_closed hc hs

end

end Li2Lean.P0.Q11Data
