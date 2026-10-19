/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.Q11ContourFourier

open MeasureTheory Set
open scoped BigOperators Interval

namespace Li2Lean.P0.Q11ContourFourier

noncomputable section

open Li2Lean.P0.Q11Data
open Li2Lean.P0.ConfigContourKernel
open Li2Lean.P0.ConfigContourReference
open Li2Lean.P0.ConfigContourSelfPotential

/-- The finite Fourier expansion gives a uniform lower bound for the q = 11
contour potential.  This is the coarse Fejer estimate used in the v13
endpoint certificate (p0-analytic.tex:244-255 and
certificate-algorithm.tex:50-75). -/
theorem q11ContourPotential_lower_on_ellipse (u : ℝ) :
    -(q11ContourMass * |Real.log contourScale| + 96 * q11ContourMass) ≤
      q11ContourPotential (Li2Lean.p0EllipsePoint 1 u) := by
  have hmass : 0 ≤ q11ContourMass := by
    rw [q11ContourMass_eq_sum]
    apply Finset.sum_nonneg
    intro j hj
    exact q11ContourWeight_nonneg j
  have hmoment : ∀ n : ℕ,
      |q11ContourFourierMoment n| ≤ q11ContourMass := by
    intro n
    unfold q11ContourFourierMoment
    by_cases hn : n ≤ 48
    · simp only [if_pos hn]
      have hcoef0 : 0 ≤ 1 - (n : ℝ) / 49 := by
        have hn' : (n : ℝ) ≤ 49 := by
          exact_mod_cast (Nat.le_succ_of_le hn)
        linarith
      have hcoef1 : 1 - (n : ℝ) / 49 ≤ 1 := by
        have hn0 : 0 ≤ (n : ℝ) := by positivity
        linarith
      have hsum :
          |∑ j : Fin contourNodeCount,
              q11ContourWeight j * Real.cos ((n : ℝ) * contourAngle j)| ≤
            q11ContourMass := by
        calc
          |∑ j : Fin contourNodeCount,
              q11ContourWeight j * Real.cos ((n : ℝ) * contourAngle j)| ≤
              ∑ j : Fin contourNodeCount,
                |q11ContourWeight j * Real.cos ((n : ℝ) * contourAngle j)| :=
            Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ j : Fin contourNodeCount, q11ContourWeight j := by
            apply Finset.sum_le_sum
            intro j hj
            rw [abs_mul, abs_of_nonneg (q11ContourWeight_nonneg j)]
            exact mul_le_of_le_one_right (q11ContourWeight_nonneg j)
              (Real.abs_cos_le_one _)
          _ = q11ContourMass := by
            rw [q11ContourMass_eq_sum]
      rw [abs_mul]
      have hc : 0 ≤ 1 - (n : ℝ) / 49 := hcoef0
      rw [abs_of_nonneg hc]
      calc
        (1 - (n : ℝ) / 49) *
            |∑ j : Fin contourNodeCount,
              q11ContourWeight j * Real.cos ((n : ℝ) * contourAngle j)| ≤
            1 * q11ContourMass := by
          exact mul_le_mul hcoef1 hsum (by positivity) (by positivity)
        _ = q11ContourMass := by ring
    · simp only [if_neg hn, abs_zero]
      exact hmass
  have hscale :
      -(q11ContourMass * |Real.log contourScale|) ≤
        q11ContourMass * Real.log contourScale := by
    have h := neg_abs_le (Real.log contourScale)
    nlinarith
  have hterm : ∀ n ∈ Finset.range 48,
      |((1 + contourRatio ^ (n + 1)) *
          q11ContourFourierMoment (n + 1) / (n + 1 : ℝ)) *
            Real.cos ((n + 1 : ℝ) * u)| ≤ 2 * q11ContourMass := by
    intro n hn
    have hnpos : 0 < (n + 1 : ℝ) := by positivity
    have hq0 : 0 ≤ contourRatio ^ (n + 1) :=
      pow_nonneg contourRatio_nonneg _
    have hq1 : contourRatio ^ (n + 1) ≤ 1 := by
      exact pow_le_one₀ contourRatio_nonneg (by norm_num [contourRatio])
    have hm := hmoment (n + 1)
    have hcos : |Real.cos ((n + 1 : ℝ) * u)| ≤ 1 := Real.abs_cos_le_one _
    have hnum : (1 + contourRatio ^ (n + 1)) *
        |q11ContourFourierMoment (n + 1)| ≤ 2 * q11ContourMass := by
      exact le_trans (mul_le_mul_of_nonneg_left hm (by linarith))
        (by nlinarith [hmass])
    rw [abs_mul, abs_div, abs_mul,
      abs_of_nonneg (by positivity : 0 ≤ 1 + contourRatio ^ (n + 1)),
      abs_of_pos (by positivity : 0 < (n + 1 : ℝ))]
    calc
      ((1 + contourRatio ^ (n + 1)) *
          |q11ContourFourierMoment (n + 1)| / (n + 1 : ℝ)) *
          |Real.cos ((n + 1 : ℝ) * u)| ≤
        ((1 + contourRatio ^ (n + 1)) *
          |q11ContourFourierMoment (n + 1)| / (n + 1 : ℝ)) * 1 := by
            exact mul_le_mul_of_nonneg_left hcos (by positivity)
      _ ≤ 2 * q11ContourMass := by
        rw [mul_one]
        apply (div_le_iff₀ hnpos).2
        nlinarith [hnum]
  have hsum :
      ∑ n ∈ Finset.range 48,
          ((1 + contourRatio ^ (n + 1)) *
            q11ContourFourierMoment (n + 1) / (n + 1 : ℝ)) *
              Real.cos ((n + 1 : ℝ) * u) ≤
        96 * q11ContourMass := by
    have hle : ∀ n ∈ Finset.range 48,
        ((1 + contourRatio ^ (n + 1)) *
          q11ContourFourierMoment (n + 1) / (n + 1 : ℝ)) *
            Real.cos ((n + 1 : ℝ) * u) ≤ 2 * q11ContourMass := by
      intro n hn
      exact le_trans (le_abs_self _) (hterm n hn)
    calc
      _ ≤ ∑ n ∈ Finset.range 48, 2 * q11ContourMass := by
        apply Finset.sum_le_sum
        intro n hn
        exact hle n hn
      _ = 96 * q11ContourMass := by norm_num; ring
  rw [q11ContourPotential_eq_fourier]
  unfold q11ContourPotentialFourier
  nlinarith [hscale, hsum]

end

end Li2Lean.P0.Q11ContourFourier
