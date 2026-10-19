/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.Q11ContourFourier
import Li2Lean.P0.Q11QLogEnvelope
import Li2Lean.P0.Q11ContourSelfIntegrability
import Li2Lean.P0.ActualReferenceQLogEnclosure

open MeasureTheory
open scoped BigOperators Interval

namespace Li2Lean.P0.Q11Data

noncomputable section

open Li2Lean.P0.ConfigContourSelfPotential
open Li2Lean.P0.ConfigContourKernel

/-- The exact 48-term Fourier expression for the q = 11 contour self-energy.
The coefficient and moment definitions are the literal q = 11 data from the
v13 contour construction. -/
def q11ContourSelfEnergyFourier : ℝ :=
  q11ContourMass ^ 2 * Real.log contourScale -
    ∑ n ∈ Finset.range 48,
      ((1 + contourRatio ^ (n + 1)) *
        (q11ContourFourierMoment (n + 1)) ^ 2 / (n + 1 : ℝ))

/-- The contour self-energy is exactly the finite Fourier expression from the
v13 contour construction. -/
theorem q11ContourSelfEnergy_eq_fourier :
    q11ContourIntegral q11ContourPotential = q11ContourSelfEnergyFourier := by
  have hterm (n : ℕ) : Continuous (fun u : ℝ => q11ContourDensity u *
      (((1 + contourRatio ^ (n + 1)) * q11ContourFourierMoment (n + 1) /
        (n + 1 : ℝ)) * Real.cos ((n + 1 : ℝ) * u))) := by
    exact q11ContourDensity_continuous.mul
      (continuous_const.mul (by fun_prop))
  have hconst : Continuous (fun u : ℝ =>
      q11ContourDensity u * (q11ContourMass * Real.log contourScale)) :=
    q11ContourDensity_continuous.mul continuous_const
  have hsum : Continuous (fun u : ℝ => ∑ n ∈ Finset.range 48,
      q11ContourDensity u *
        (((1 + contourRatio ^ (n + 1)) * q11ContourFourierMoment (n + 1) /
          (n + 1 : ℝ)) * Real.cos ((n + 1 : ℝ) * u))) := by
    apply continuous_finsetSum
    intro n hn
    exact hterm n
  unfold q11ContourIntegral
  change (2 * Real.pi)⁻¹ *
    (∫ u in (0 : ℝ)..(2 * Real.pi),
      q11ContourDensity u * q11ContourPotential
        (Li2Lean.p0EllipsePoint 1 u)) = _
  simp_rw [q11ContourPotential_eq_fourier, q11ContourPotentialFourier,
    mul_sub, Finset.mul_sum]
  rw [intervalIntegral.integral_sub (hconst.intervalIntegrable _ _)
      (hsum.intervalIntegrable _ _),
    intervalIntegral.integral_mul_const, q11IntegralContourDensity,
    q11ContourMass_eq_sum,
    intervalIntegral.integral_finsetSum
      (fun n hn => (hterm n).intervalIntegrable _ _)]
  have hmoment (n : ℕ) :
      (∫ u in (0 : ℝ)..(2 * Real.pi),
        q11ContourDensity u * Real.cos ((n + 1 : ℝ) * u)) =
        2 * Real.pi * q11ContourFourierMoment (n + 1) := by
    have h := q11ExternalFourierCoefficient_eq_actual_moment_succ n 0
    simpa [q11ExternalFourierCoefficient] using h
  have hcell (n : ℕ) :
      (∫ u in (0 : ℝ)..(2 * Real.pi),
        q11ContourDensity u *
          (((1 + contourRatio ^ (n + 1)) * q11ContourFourierMoment (n + 1) /
            (n + 1 : ℝ)) * Real.cos ((n + 1 : ℝ) * u))) =
      (2 * Real.pi) *
        ((1 + contourRatio ^ (n + 1)) *
          (q11ContourFourierMoment (n + 1)) ^ 2 / (n + 1 : ℝ)) := by
    rw [show (fun u : ℝ => q11ContourDensity u *
          (((1 + contourRatio ^ (n + 1)) * q11ContourFourierMoment (n + 1) /
            (n + 1 : ℝ)) * Real.cos ((n + 1 : ℝ) * u))) =
        fun u => ((1 + contourRatio ^ (n + 1)) *
          q11ContourFourierMoment (n + 1) / (n + 1 : ℝ)) *
            (q11ContourDensity u * Real.cos ((n + 1 : ℝ) * u)) by
          funext u; ring,
      intervalIntegral.integral_const_mul, hmoment]
    ring
  simp_rw [hcell]
  rw [← Finset.mul_sum]
  unfold q11ContourSelfEnergyFourier
  rw [q11ContourMass_eq_sum]
  have hp : (Real.pi : ℝ) ≠ 0 := by positivity
  field_simp [hp]

theorem q11Eνν_eq_fourier :
    q11Eνν = q11ContourSelfEnergyFourier := by
  unfold q11Eνν
  rw [← q11ContourIntegral_eq_integral
    q11ContourPotential_contour_integrable.aestronglyMeasurable]
  exact q11ContourSelfEnergy_eq_fourier

end

end Li2Lean.P0.Q11Data
