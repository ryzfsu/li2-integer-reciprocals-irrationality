/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.Q11Reference
import Li2Lean.P0.ContourProductIntegrability

open MeasureTheory Set
open scoped ENNReal

namespace Li2Lean.P0.Q11Data

noncomputable section

open Li2Lean.P0.ConfigContourReference
open Li2Lean.P0.ConfigContourSelfPotential
open Li2Lean.P0.ConfigContourMeasure

private theorem q11ContourDensity_le_49_mass (u : ℝ) :
    q11ContourDensity u ≤
      49 * ∑ j : Fin contourNodeCount, q11ContourWeight j := by
  unfold q11ContourDensity
  calc
    (∑ j : Fin contourNodeCount, q11ContourWeight j *
        fejer48 (u - contourAngle j)) ≤
      ∑ j : Fin contourNodeCount, q11ContourWeight j * 49 := by
        apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul_of_nonneg_left
          (ConfigContourProductIntegrability.fejer48_le_49 _)
          (q11ContourWeight_nonneg j)
    _ = 49 * ∑ j : Fin contourNodeCount, q11ContourWeight j := by
      rw [← Finset.sum_mul]
      ring

private theorem q11_density_param_kernel_integrable :
    Integrable contourLogDistanceKernel
      (((volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))).withDensity
        (fun u => ENNReal.ofReal (q11ContourDensity u))).prod
        ((volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))).withDensity
          (fun u => ENNReal.ofReal (q11ContourDensity u)))) := by
  let m : Measure ℝ := volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))
  let f : ℝ → ℝ≥0∞ := fun u => ENNReal.ofReal (q11ContourDensity u)
  have hf : Measurable f :=
    ENNReal.measurable_ofReal.comp continuous_q11ContourDensity.measurable
  have hbase : Integrable contourLogDistanceKernel (m.prod m) := by
    dsimp [m]
    rw [Measure.prod_restrict]
    apply (ConfigContourProduct.contourLogDistanceKernel_integrable).mono_measure
    apply Measure.restrict_mono_set
    intro p hp
    exact ⟨⟨le_of_lt hp.1.1, hp.1.2⟩, ⟨le_of_lt hp.2.1, hp.2.2⟩⟩
  rw [show (m.withDensity f).prod (m.withDensity f) =
      (m.prod m).withDensity (fun p : ℝ × ℝ => f p.1 * f p.2) from
        prod_withDensity hf hf]
  have hfd : Measurable (fun p : ℝ × ℝ => f p.1 * f p.2) :=
    (hf.comp measurable_fst).mul (hf.comp measurable_snd)
  let B : ℝ := 49 * ∑ j : Fin contourNodeCount, q11ContourWeight j
  have hB : 0 ≤ B := by
    dsimp [B]
    have hsum : 0 ≤ ∑ j : Fin contourNodeCount, q11ContourWeight j := by
      exact Finset.sum_nonneg (fun j _ => q11ContourWeight_nonneg j)
    positivity
  have hbound : ∀ u : ℝ, f u ≤ ENNReal.ofReal B := by
    intro u
    dsimp [f, B]
    exact ENNReal.ofReal_le_ofReal (q11ContourDensity_le_49_mass u)
  have hflt : ∀ᵐ p ∂(m.prod m), f p.1 * f p.2 < ⊤ := by
    filter_upwards [] with p
    calc
      f p.1 * f p.2 ≤ ENNReal.ofReal B * ENNReal.ofReal B :=
        mul_le_mul (hbound p.1) (hbound p.2) (by positivity) (by positivity)
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  rw [integrable_withDensity_iff hfd hflt]
  let g : ℝ × ℝ → ℝ := fun p => (f p.1 * f p.2).toReal
  have hg : Measurable g := ENNReal.measurable_toReal.comp hfd
  have hg_bound : ∀ᵐ p ∂(m.prod m), ‖g p‖ ≤ B ^ 2 := by
    filter_upwards [] with p
    have h1 : 0 ≤ q11ContourDensity p.1 := q11ContourDensity_nonneg _
    have h2 : 0 ≤ q11ContourDensity p.2 := q11ContourDensity_nonneg _
    have hb1 := q11ContourDensity_le_49_mass p.1
    have hb2 := q11ContourDensity_le_49_mass p.2
    dsimp [g, f, B]
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal h1,
      ENNReal.toReal_ofReal h2]
    rw [abs_of_nonneg (mul_nonneg h1 h2)]
    nlinarith
  have hw := hbase.mul_bdd hg.aestronglyMeasurable hg_bound
  simpa [g, Pi.mul_apply, Function.comp_apply] using hw

private theorem q11ContourParamMeasure_le_density :
    q11ContourParamMeasure ≤
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))).withDensity
        (fun u => ENNReal.ofReal (q11ContourDensity u)) := by
  unfold q11ContourParamMeasure
  apply (Measure.le_iff').2
  intro s
  rw [Measure.smul_apply]
  change ENNReal.ofReal (2 * Real.pi)⁻¹ * _ ≤ _
  apply mul_le_of_le_one_left
  · exact bot_le
  simpa using ENNReal.ofReal_le_ofReal
    ((inv_le_one₀ (show 0 < (2 * Real.pi : ℝ) by positivity)).2
      (by nlinarith [Real.pi_gt_three]))

private theorem q11ContourParam_kernel_integrable :
    Integrable contourLogDistanceKernel
      (q11ContourParamMeasure.prod q11ContourParamMeasure) := by
  letI : IsFiniteMeasure q11ContourParamMeasure := ⟨by
    rw [q11ContourParamMeasure_univ]
    exact ENNReal.ofReal_lt_top⟩
  have hle := q11ContourParamMeasure_le_density
  exact q11_density_param_kernel_integrable.mono_measure
    (Measure.prod_mono hle hle)

private theorem q11ContourReferenceMeasure_prod_integrable :
    Integrable (fun p : ℂ × ℂ => Real.log ‖p.1 - p.2‖)
      (q11ContourReferenceMeasure.prod q11ContourReferenceMeasure) := by
  letI : IsFiniteMeasure q11ContourParamMeasure := ⟨by
    rw [q11ContourParamMeasure_univ]
    exact ENNReal.ofReal_lt_top⟩
  change Integrable (fun p : ℂ × ℂ => Real.log ‖p.1 - p.2‖)
      ((q11ContourParamMeasure.map (Li2Lean.p0EllipsePoint 1)).prod
        (q11ContourParamMeasure.map (Li2Lean.p0EllipsePoint 1)))
  rw [Measure.map_prod_map q11ContourParamMeasure q11ContourParamMeasure
    ConfigContourMeasure.continuous_ellipse.measurable
    ConfigContourMeasure.continuous_ellipse.measurable]
  have hmeas : Measurable (fun p : ℂ × ℂ => Real.log ‖p.1 - p.2‖) := by
    exact Real.measurable_log.comp
      (continuous_norm.comp (continuous_fst.sub continuous_snd)).measurable
  apply (integrable_map_measure hmeas.aestronglyMeasurable
    (ConfigContourMeasure.continuous_ellipse.measurable.prodMap
      ConfigContourMeasure.continuous_ellipse.measurable).aemeasurable).mpr
  convert q11ContourParam_kernel_integrable using 1 <;>
    rfl

/-- The q11 contour self-potential is integrable. The singular log kernel is
controlled by the q=2 parameter-square lemma; q11's finite Fejer density is
bounded explicitly before changing measures. -/
theorem q11ContourPotential_contour_integrable :
    Integrable q11ContourPotential q11ContourReferenceMeasure := by
  have h := q11ContourReferenceMeasure_prod_integrable.integral_prod_left
  apply h.congr
  filter_upwards [] with z
  rw [q11ContourPotential_eq_integral]

end

end Li2Lean.P0.Q11Data
