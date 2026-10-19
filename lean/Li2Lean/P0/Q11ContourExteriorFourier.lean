/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.Q11ContourTail
import Li2Lean.P0.ConfigContourFormula
import Li2Lean.P0.ConfigFejerLog

open MeasureTheory
open scoped BigOperators

namespace Li2Lean.P0.Q11Data

noncomputable section

open ConfigContourFormula ConfigContourKernel ConfigContourReference
open ConfigFejerLog

/-!
The exterior contour formula used by the q = 11 frequency checker.  The
factorization and Fejer logarithm integral are the v13 exterior calculation
(`certificate-algorithm.tex:64-75`); the q11 weights are those of
`p0-reference-data.tex:29-40`.
-/

def q11ExteriorContourLogPolynomial (a : ℂ) : ℝ :=
  ∑ j : Fin contourNodeCount,
    q11ContourWeight j * (fejerLogPolynomial (a * phase (contourAngle j))).re

theorem q11_integral_exteriorContourDensity_log_norm {a : ℂ} (ha : ‖a‖ < 1) :
    (∫ u in (0 : ℝ)..(2 * Real.pi),
      q11ContourDensity u * Real.log ‖1 - a * phase u‖) =
      -(2 * Real.pi) * q11ExteriorContourLogPolynomial a := by
  unfold q11ContourDensity
  simp_rw [Finset.sum_mul]
  rw [intervalIntegral.integral_finsetSum]
  · simp_rw [mul_assoc, intervalIntegral.integral_const_mul,
      integral_fejer48_log_norm ha]
    unfold q11ExteriorContourLogPolynomial
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  · intro j hj
    exact ((continuous_const.mul
      (ConfigContourMeasure.continuous_fejer48.comp
        (continuous_id.sub continuous_const))).mul
        (continuous_log_norm ha)).intervalIntegrable _ _

theorem q11ExteriorContourPotential_neg_polynomial (t : ℝ) (ht : (1 / 2 : ℝ) ≤ t) :
    q11ContourPotential (-(t : ℂ)) =
      q11ContourMass * Real.log (outsideRadius t) -
        q11ExteriorContourLogPolynomial (outsideParameter t : ℂ) -
        q11ExteriorContourLogPolynomial ((contourRatio * outsideParameter t : ℝ) : ℂ) := by
  have h0 : IntervalIntegrable
      (fun u => q11ContourDensity u * Real.log (outsideRadius t)) volume 0 (2 * Real.pi) :=
    (continuous_q11ContourDensity.mul continuous_const).intervalIntegrable _ _
  have h1 : IntervalIntegrable
      (fun u => q11ContourDensity u *
        Real.log ‖1 - (outsideParameter t : ℂ) * phase u‖) volume 0 (2 * Real.pi) :=
    (continuous_q11ContourDensity.mul
      (continuous_log_norm (outsideParameter_norm_lt_one ht))).intervalIntegrable _ _
  have h2 : IntervalIntegrable
      (fun u => q11ContourDensity u *
        Real.log ‖1 - ((contourRatio * outsideParameter t : ℝ) : ℂ) * phase u‖)
      volume 0 (2 * Real.pi) := by
    apply Continuous.intervalIntegrable
    apply continuous_q11ContourDensity.mul
    apply continuous_log_norm
    simpa only [Complex.ofReal_mul] using outsideCorrection_norm_lt_one ht
  unfold q11ContourPotential q11ContourIntegral
  simp_rw [outside_log_distance ht, mul_add]
  rw [intervalIntegral.integral_add (h0.add h1) h2,
    intervalIntegral.integral_add h0 h1,
    intervalIntegral.integral_mul_const,
    q11IntegralContourDensity, q11ContourWeight_sum,
    q11_integral_exteriorContourDensity_log_norm (outsideParameter_norm_lt_one ht),
    q11_integral_exteriorContourDensity_log_norm (by
      simpa only [Complex.ofReal_mul] using outsideCorrection_norm_lt_one ht)]
  unfold q11ContourMass
  field_simp
  ring

def q11ExteriorContourMoment (n : ℕ) : ℝ :=
  (1 - (n : ℝ) / 49) *
    ∑ j : Fin contourNodeCount,
      q11ContourWeight j * Real.cos ((n : ℝ) * contourAngle j)

theorem q11ExteriorContourLogPolynomial_ofReal (x : ℝ) :
    q11ExteriorContourLogPolynomial (x : ℂ) =
      ∑ n ∈ Finset.range 49, q11ExteriorContourMoment n * (x ^ n / (n : ℝ)) := by
  unfold q11ExteriorContourLogPolynomial
  simp_rw [fejerLogPolynomial_ofReal_re, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  unfold q11ExteriorContourMoment
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The q11 exterior logarithmic potential in the finite v13 Fourier form. -/
theorem q11ExteriorContourPotential_neg (t : ℝ) (ht : (1 / 2 : ℝ) ≤ t) :
    q11ContourPotential (-(t : ℂ)) =
      q11ContourMass * Real.log (outsideRadius t) -
        ∑ n ∈ Finset.range 49,
          ((1 + contourRatio ^ n) * q11ExteriorContourMoment n / (n : ℝ)) *
            outsideParameter t ^ n := by
  rw [q11ExteriorContourPotential_neg_polynomial t ht,
    q11ExteriorContourLogPolynomial_ofReal, q11ExteriorContourLogPolynomial_ofReal,
    sub_sub, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  rw [mul_pow]
  ring

end

end Li2Lean.P0.Q11Data

#print axioms Li2Lean.P0.Q11Data.q11ExteriorContourPotential_neg
