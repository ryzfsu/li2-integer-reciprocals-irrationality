/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.Q11Potential
import Li2Lean.P0.ConfigContourTail

open MeasureTheory Filter Set
open scoped Topology

namespace Li2Lean.P0.Q11Data

noncomputable section

open Li2Lean.P0.ConfigContourTail

def q11ContourTailDerivative (t : ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ * ∫ u in (0 : ℝ)..(2 * Real.pi),
    q11ContourDensity u * tailKernelDeriv t u

theorem q11_hasDerivAt_contourPotential_neg {t : ℝ}
    (ht : leftClearance < t) :
    HasDerivAt (fun s : ℝ => q11ContourPotential (-(s : ℂ)))
      (q11ContourTailDerivative t) t := by
  let mu : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi))
  let b : ℝ := (t + leftClearance) / 2
  have hb : leftClearance < b := by dsimp [b]; linarith
  have hbt : b < t := by dsimp [b]; linarith
  have hpi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  let F : ℝ → ℝ → ℝ := fun s u => q11ContourDensity u * tailKernel s u
  let F' : ℝ → ℝ → ℝ := fun s u => q11ContourDensity u * tailKernelDeriv s u
  let bound : ℝ → ℝ := fun u => q11ContourDensity u * (1 / (b - leftClearance))
  have hFi {s : ℝ} (hs : leftClearance < s) : Integrable (F s) mu := by
    dsimp [F, mu]
    exact ((continuous_q11ContourDensity.mul
      (continuous_tailKernel hs)).intervalIntegrable _ _).1
  have hDi {s : ℝ} (hs : leftClearance < s) : Continuous (F' s) := by
    dsimp [F']
    exact continuous_q11ContourDensity.mul (continuous_tailKernelDeriv hs)
  have hBi : Integrable bound mu := by
    dsimp [bound, mu]
    exact ((continuous_q11ContourDensity.mul continuous_const).intervalIntegrable _ _).1
  have hbound : ∀ᵐ u ∂mu, ∀ s ∈ Set.Ioi b, ‖F' s u‖ ≤ bound u := by
    filter_upwards [] with u
    intro s hs
    have hbs : b < s := hs
    have hds : leftClearance < s := lt_trans hb hbs
    have hrec : (1 : ℝ) / (s - leftClearance) ≤ 1 / (b - leftClearance) :=
      one_div_le_one_div_of_le (sub_pos.mpr hb) (by linarith)
    have hnon : 0 ≤ F' s u :=
      mul_nonneg (q11ContourDensity_nonneg u) (tailKernelDeriv_nonneg hds u)
    rw [Real.norm_eq_abs, abs_of_nonneg hnon]
    exact mul_le_mul_of_nonneg_left
      ((tailKernelDeriv_le hds u).trans hrec) (q11ContourDensity_nonneg u)
  have hdiff : ∀ᵐ u ∂mu, ∀ s ∈ Set.Ioi b,
      HasDerivAt (fun x => F x u) (F' s u) s := by
    filter_upwards [] with u
    intro s hs
    have hbs : b < s := hs
    exact (hasDerivAt_tailKernel (lt_trans hb hbs) u).const_mul
      (q11ContourDensity u)
  have hmeas : ∀ᶠ s in 𝓝 t, AEStronglyMeasurable (F s) mu := by
    filter_upwards [Ioi_mem_nhds hbt] with s hs
    exact (continuous_q11ContourDensity.mul
      (continuous_tailKernel (lt_trans hb hs))).aestronglyMeasurable
  have hderiv := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := mu) (F := F) (F' := F') (bound := bound)
    (Ioi_mem_nhds hbt) hmeas (hFi ht) (hDi ht).aestronglyMeasurable
    hbound hBi hdiff).2
  have heq (s : ℝ) : q11ContourPotential (-(s : ℂ)) =
      (2 * Real.pi)⁻¹ * ∫ u, F s u ∂mu := by
    unfold q11ContourPotential q11ContourIntegral
    simp only [← tailKernel_eq_log_norm]
    rw [intervalIntegral.integral_of_le hpi]
  have heqD : q11ContourTailDerivative t =
      (2 * Real.pi)⁻¹ * ∫ u, F' t u ∂mu := by
    unfold q11ContourTailDerivative
    dsimp [F', mu]
    rw [intervalIntegral.integral_of_le hpi]
  rw [heqD]
  simpa only [← heq] using hderiv.const_mul ((2 * Real.pi)⁻¹)

theorem q11_contourTailDerivative_le {t : ℝ} (ht : leftClearance < t) :
    q11ContourTailDerivative t ≤ q11ContourMass / (t - leftClearance) := by
  have hpi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hint₁ : IntervalIntegrable
      (fun u => q11ContourDensity u * tailKernelDeriv t u)
      volume 0 (2 * Real.pi) :=
    (continuous_q11ContourDensity.mul
      (continuous_tailKernelDeriv ht)).intervalIntegrable _ _
  have hint₂ : IntervalIntegrable
      (fun u => q11ContourDensity u * (1 / (t - leftClearance)))
      volume 0 (2 * Real.pi) :=
    (continuous_q11ContourDensity.mul continuous_const).intervalIntegrable _ _
  have hi := intervalIntegral.integral_mono_on hpi hint₁ hint₂ (fun u hu =>
    mul_le_mul_of_nonneg_left (tailKernelDeriv_le ht u)
      (q11ContourDensity_nonneg u))
  have hnorm : (2 * Real.pi)⁻¹ *
      (∫ u in (0 : ℝ)..(2 * Real.pi),
        q11ContourDensity u * (1 / (t - leftClearance))) =
      q11ContourMass / (t - leftClearance) := by
    rw [intervalIntegral.integral_mul_const, q11IntegralContourDensity,
      q11ContourWeight_sum]
    unfold q11ContourMass
    have hp : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    field_simp
  exact (mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ (2 * Real.pi)⁻¹)).trans_eq hnorm

theorem q11ContourPotential_neg_deriv_le {t : ℝ}
    (ht : leftClearance < t) :
    deriv (fun s : ℝ => q11ContourPotential (-(s : ℂ))) t ≤
      q11ContourMass / (t - leftClearance) := by
  rw [(q11_hasDerivAt_contourPotential_neg ht).deriv]
  exact q11_contourTailDerivative_le ht

end

end Li2Lean.P0.Q11Data
