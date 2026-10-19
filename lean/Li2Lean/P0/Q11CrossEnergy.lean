/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.Q11EndpointBridge
import Li2Lean.P0.TubeSweptFiniteEnergy

open MeasureTheory Set
open scoped ENNReal

namespace Li2Lean.P0.Q11Data

noncomputable section

private def q11PinnedComplexMeasure : Measure ℂ :=
  q11PinnedReferenceMeasure.map Complex.ofReal

private instance q11PinnedComplexMeasure_isFinite :
    IsFiniteMeasure q11PinnedComplexMeasure := by
  refine ⟨?_⟩
  unfold q11PinnedComplexMeasure
  rw [Measure.map_apply Complex.continuous_ofReal.measurable MeasurableSet.univ]
  simp only [Set.preimage_univ, q11PinnedReferenceMeasure_mass]
  exact ENNReal.ofReal_lt_top

private theorem q11PinnedComplexMeasure_ae_segment :
    ∀ᵐ z ∂q11PinnedComplexMeasure,
      z.re ∈ Icc (0 : ℝ) 2 ∧ z.im = 0 := by
  have hset : MeasurableSet {z : ℂ |
      z.re ∈ Icc (0 : ℝ) 2 ∧ z.im = 0} := by
    exact (measurableSet_Icc.preimage Complex.continuous_re.measurable).inter
      ((measurableSet_singleton (0 : ℝ)).preimage Complex.continuous_im.measurable)
  unfold q11PinnedComplexMeasure
  rw [ae_map_iff Complex.continuous_ofReal.aemeasurable hset]
  filter_upwards [q11PinnedReferenceMeasure_ae_interval] with x hx
  constructor
  · simp only [Complex.ofReal_re]
    constructor <;> linarith [hx.1, hx.2]
  · simp

theorem q11_contour_pinned_cross_integrable :
    Integrable (fun p : ℂ × ℂ => li2LogKernel p.1 p.2)
      (q11ContourReferenceMeasure.prod q11PinnedComplexMeasure) := by
  exact TubeEnergy.integrable_li2LogKernel_gamma_pinned
    q11ContourReferenceMeasure q11PinnedComplexMeasure
    q11ContourReferenceMeasure_ae_Gamma q11PinnedComplexMeasure_ae_segment

theorem q11_pinned_contour_cross_integrable :
    Integrable (fun p : ℂ × ℂ => li2LogKernel p.1 p.2)
      (q11PinnedComplexMeasure.prod q11ContourReferenceMeasure) := by
  exact TubeEnergy.integrable_li2LogKernel_pinned_gamma
    q11PinnedComplexMeasure q11ContourReferenceMeasure
    q11PinnedComplexMeasure_ae_segment q11ContourReferenceMeasure_ae_Gamma

theorem q11ContourPotential_pinned_integrable :
    Integrable (fun x : ℝ => q11ContourPotential (x : ℂ))
      q11PinnedReferenceMeasure := by
  have hmap : Integrable (fun x : ℂ =>
      ∫ y, (-fun p : ℂ × ℂ => li2LogKernel p.1 p.2) (x, y)
        ∂q11ContourReferenceMeasure) q11PinnedComplexMeasure :=
    (q11_pinned_contour_cross_integrable.neg).integral_prod_left
  have h := (MeasureTheory.integrable_map_measure
    hmap.aestronglyMeasurable Complex.continuous_ofReal.aemeasurable).mp hmap
  apply h.congr
  filter_upwards [] with x
  rw [q11ContourPotential_eq_integral]
  apply integral_congr_ae
  filter_upwards [] with z
  simp [li2LogKernel, norm_sub_rev]

theorem q11PinnedComplexPotential_contour_integrable :
    Integrable q11PinnedComplexPotential q11ContourReferenceMeasure := by
  have hmap : Integrable (fun z : ℂ =>
      ∫ y, (-fun p : ℂ × ℂ => li2LogKernel p.1 p.2) (z, y)
        ∂q11PinnedComplexMeasure) q11ContourReferenceMeasure :=
    (q11_contour_pinned_cross_integrable.neg).integral_prod_left
  apply hmap.congr
  filter_upwards [] with z
  unfold q11PinnedComplexMeasure
  rw [integral_map Complex.continuous_ofReal.aemeasurable]
  · unfold q11PinnedComplexPotential
    apply integral_congr_ae
    filter_upwards [] with x
    simp [li2LogKernel, norm_sub_rev]
  · have hzmeas : Measurable (fun y : ℂ =>
        (-fun p : ℂ × ℂ => li2LogKernel p.1 p.2) (z, y)) := by
      unfold li2LogKernel
      fun_prop
    exact hzmeas.aestronglyMeasurable

/-! The pinned/frequency supports are separated from the origin.  Thus the
reflected frequency logarithm has a bounded product majorant; no numerical
energy estimate is used here. -/

theorem q11ReflectedFrequencyPotential_pinned_integrable_cross :
    Integrable (fun x : ℝ => q11ReflectedFrequencyPotential (x : ℂ))
      q11PinnedReferenceMeasure := by
  letI : IsFiniteMeasure q11PinnedReferenceMeasure := ⟨by
    rw [q11PinnedReferenceMeasure_mass]
    exact ENNReal.ofReal_lt_top⟩
  letI : IsFiniteMeasure q11FrequencyReferenceMeasure := ⟨by
    rw [q11FrequencyReferenceMeasure_univ]
    exact ENNReal.one_lt_top⟩
  have hprod :
      Integrable
        (fun p : ℝ × ℝ =>
          Real.log ‖(p.1 : ℂ) + (p.2 : ℂ)‖)
        (q11PinnedReferenceMeasure.prod q11FrequencyReferenceMeasure) := by
    have hmeas : Measurable (fun p : ℝ × ℝ =>
        ‖(p.1 : ℂ) + (p.2 : ℂ)‖) := by
      fun_prop
    apply (integrable_const
      (|Real.log (3 / 4 : ℝ)| + |Real.log (23 / 4 : ℝ)|)).mono'
      (Real.measurable_log.comp hmeas).aestronglyMeasurable
    have h1 := (Measure.quasiMeasurePreserving_fst
      (μ := q11PinnedReferenceMeasure)
      (ν := q11FrequencyReferenceMeasure)).ae
      q11PinnedReferenceMeasure_ae_interval
    have h2 := (Measure.quasiMeasurePreserving_snd
      (μ := q11PinnedReferenceMeasure)
      (ν := q11FrequencyReferenceMeasure)).ae
      q11FrequencyReferenceMeasure_ae_interval
    filter_upwards [h1, h2] with p hp ht
    have hsum_nonneg : 0 ≤ p.1 + p.2 := by
      linarith [hp.1, ht.1]
    have heq : (p.1 : ℂ) + (p.2 : ℂ) = Complex.ofReal (p.1 + p.2) := by
      norm_num
    have hlow : (3 / 4 : ℝ) ≤ ‖(p.1 : ℂ) + (p.2 : ℂ)‖ := by
      rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hsum_nonneg]
      linarith [hp.1, ht.1]
    have hhigh : ‖(p.1 : ℂ) + (p.2 : ℂ)‖ ≤ (23 / 4 : ℝ) := by
      rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hsum_nonneg]
      linarith [hp.2, ht.2]
    have hloglow : Real.log (3 / 4 : ℝ) ≤
        Real.log ‖(p.1 : ℂ) + (p.2 : ℂ)‖ :=
      Real.log_le_log (by norm_num) hlow
    have hloghigh : Real.log ‖(p.1 : ℂ) + (p.2 : ℂ)‖ ≤
        Real.log (23 / 4 : ℝ) :=
      Real.log_le_log (lt_of_lt_of_le (by norm_num) hlow) hhigh
    change ‖Real.log ‖(p.1 : ℂ) + (p.2 : ℂ)‖‖ ≤
      |Real.log (3 / 4 : ℝ)| + |Real.log (23 / 4 : ℝ)|
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [neg_abs_le (Real.log (3 / 4 : ℝ)),
      le_abs_self (Real.log (23 / 4 : ℝ)),
      abs_nonneg (Real.log (3 / 4 : ℝ)),
      abs_nonneg (Real.log (23 / 4 : ℝ))]
  simpa [q11ReflectedFrequencyPotential] using hprod.integral_prod_left

end

end Li2Lean.P0.Q11Data

#print axioms Li2Lean.P0.Q11Data.q11_contour_pinned_cross_integrable
#print axioms Li2Lean.P0.Q11Data.q11_pinned_contour_cross_integrable
