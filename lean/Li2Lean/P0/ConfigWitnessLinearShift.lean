/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.ConfigWitnessFiniteEnergy
import Li2Lean.P0.CellBound.RealPieces
import Li2Lean.P0.CellBound.CircleField

open MeasureTheory
open scoped BigOperators

namespace Li2Lean.P0.CoefficientAssembly

open Li2Lean.P0
open Li2Lean.P0.Config
open Li2Lean.P0.CellBound

noncomputable section

private lemma frequency_integral_of_continuous
    {f : ℝ → ℝ} (hf : Continuous f) (C : FiniteConfiguration) :
    (∫ t, f t ∂C.mu) =
      ∑ r ∈ C.frequency,
        (∫ t in ((r - 1 : ℕ) : ℝ) / (C.m : ℝ)..(r : ℝ) / (C.m : ℝ), f t) := by
  unfold FiniteConfiguration.mu frequencyMeasure
  rw [integral_finsetSum_measure]
  · apply Finset.sum_congr rfl
    intro r hr
    change (∫ a in Set.Ico (((r - 1 : ℕ) : ℝ) / (C.m : ℝ))
        ((r : ℝ) / (C.m : ℝ)), f a) = _
    rw [MeasureTheory.integral_Ico_eq_integral_Ioc]
    have hmnat : 0 < C.m := by have := C.m_ge_eight; omega
    have hm : (0 : ℝ) < (C.m : ℝ) := by exact_mod_cast hmnat
    have hnatcast : ((r - 1 : ℕ) : ℝ) ≤ (r : ℝ) := by
      exact_mod_cast (Nat.sub_le r 1)
    have hle : ((r - 1 : ℕ) : ℝ) / (C.m : ℝ) ≤ (r : ℝ) / (C.m : ℝ) :=
      div_le_div_of_nonneg_right hnatcast hm.le
    rw [← intervalIntegral.integral_of_le hle]
  · intro r hr
    exact hf.integrableOn_Icc.mono_set Set.Ico_subset_Icc_self

private lemma mu_first (C : FiniteConfiguration) :
    (∫ t : ℝ, t ∂frequencyMeasure C.m C.frequency) =
      ∑ r ∈ C.frequency, (((r : ℝ) - 1 / 2) / (C.m : ℝ) ^ 2) := by
  change (∫ t : ℝ, t ∂C.mu) = _
  rw [frequency_integral_of_continuous (f := fun t : ℝ => t) continuous_id C]
  apply Finset.sum_congr rfl
  intro r hr
  have hrpos : 0 < r := by
    have := C.frequency_lower r hr
    omega
  have hm : (0 : ℝ) < C.m := by
    exact_mod_cast (show 0 < C.m by have := C.m_ge_eight; omega)
  have hle : ((r - 1 : ℕ) : ℝ) / (C.m : ℝ) ≤ (r : ℝ) / (C.m : ℝ) := by
    apply div_le_div_of_nonneg_right _ hm.le
    exact_mod_cast (Nat.sub_le r 1)
  rw [integral_id]
  rw [Nat.cast_sub (by omega : 1 ≤ r)]
  push_cast
  field_simp
  ring

private lemma pinned_first (C : FiniteConfiguration) :
    (∫ x : ℝ, x ∂pinnedMeasure C.m C.pinned) =
      ∑ s ∈ C.pinned, (((s : ℝ) + 1 / 2) / (C.m : ℝ) ^ 2) := by
  unfold pinnedMeasure
  rw [integral_finsetSum_measure]
  · apply Finset.sum_congr rfl
    intro s hs
    change (∫ x in Set.Ico ((s : ℝ) / (C.m : ℝ))
      (((s + 1 : ℕ) : ℝ) / (C.m : ℝ)), x) = _
    rw [MeasureTheory.integral_Ico_eq_integral_Ioc]
    have hm : (0 : ℝ) < C.m := by
      exact_mod_cast (show 0 < C.m by have := C.m_ge_eight; omega)
    have hle : (s : ℝ) / (C.m : ℝ) ≤ ((s + 1 : ℕ) : ℝ) / (C.m : ℝ) := by
      apply div_le_div_of_nonneg_right _ hm.le
      exact_mod_cast (Nat.le_succ s)
    rw [← intervalIntegral.integral_of_le hle, integral_id]
    push_cast
    field_simp
    ring
  · intro s hs
    exact continuous_id.integrableOn_Icc.mono_set Set.Ico_subset_Icc_self

private lemma circle_re (z : ℂ) (r : ℝ) :
    (∫ w : ℂ, w.re ∂(circleProbability z r)) = z.re := by
  rw [Li2Lean.P0.CellBound.integral_circleProbability_eq
    Complex.measurable_re.stronglyMeasurable z r]
  rw [Li2Lean.P0.CellBound.circleAngle_integral_eq]
  simp_rw [Li2Lean.P0.CellBound.circlePoint_re]
  rw [intervalIntegral.integral_add
    (f := fun _ : ℝ => z.re) (g := fun t => r * Real.cos t)
    intervalIntegrable_const ((continuous_const.mul Real.continuous_cos).intervalIntegrable _ _),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_cos]
  simp
  field_simp [Real.pi_ne_zero]

private lemma contour_re (C : FiniteConfiguration) :
    (∫ z : ℂ, z.re ∂configContourMeasure C) =
      (C.m : ℝ)⁻¹ * ∑ a : Fin C.contourCount, (C.contour a).re := by
  have hInt : ∀ a : Fin C.contourCount,
      Integrable (fun z : ℂ => z.re)
        (circleProbability (C.contour a) (configTubeRadius C)) := by
    intro a
    apply Li2Lean.P0.CellBound.integrable_circleProbability_of
      Complex.measurable_re.stronglyMeasurable
    have hc : Continuous (fun t : ℝ => (circlePoint (C.contour a)
        (configTubeRadius C) t).re) := by
      exact Complex.continuous_re.comp
        (continuous_circlePoint (C.contour a) (configTubeRadius C))
    unfold circleAngleMeasure
    exact (hc.integrableOn_Icc (a := (0 : ℝ)) (b := 2 * Real.pi)).mono_set
      Set.Ioc_subset_Icc_self
  unfold configContourMeasure circleEmpiricalMeasure
  rw [integral_smul_measure,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (Nat.cast_nonneg _)),
    Measure.sum_fintype, integral_finsetSum_measure (fun a _ => hInt a), smul_eq_mul]
  apply congrArg (fun x : ℝ => (C.m : ℝ)⁻¹ * x)
  apply Finset.sum_congr rfl
  intro a ha
  exact circle_re (C.contour a) (configTubeRadius C)

private lemma map_pinned_re (C : FiniteConfiguration) :
    (∫ z : ℂ, z.re ∂Measure.map Complex.ofReal (pinnedMeasure C.m C.pinned)) =
      ∫ x : ℝ, x ∂pinnedMeasure C.m C.pinned := by
  rw [integral_map Complex.measurable_ofReal.aemeasurable
    Complex.measurable_re.aestronglyMeasurable]
  simp only [Function.comp_apply, Complex.ofReal_re]

private lemma contour_re_integrable (C : FiniteConfiguration) :
    Integrable (fun z : ℂ => z.re) (configContourMeasure C) := by
  have hInt : ∀ a : Fin C.contourCount,
      Integrable (fun z : ℂ => z.re)
        (circleProbability (C.contour a) (configTubeRadius C)) := by
    intro a
    apply Li2Lean.P0.CellBound.integrable_circleProbability_of
      Complex.measurable_re.stronglyMeasurable
    have hc : Continuous (fun t : ℝ => (circlePoint (C.contour a)
        (configTubeRadius C) t).re) := by
      exact Complex.continuous_re.comp
        (continuous_circlePoint (C.contour a) (configTubeRadius C))
    unfold circleAngleMeasure
    exact (hc.integrableOn_Icc (a := (0 : ℝ)) (b := 2 * Real.pi)).mono_set
      Set.Ioc_subset_Icc_self
  unfold configContourMeasure circleEmpiricalMeasure
  apply Integrable.smul_measure _ ENNReal.ofReal_ne_top
  rw [Measure.sum_fintype]
  exact integrable_finsetSum_measure.mpr (fun a _ => hInt a)

private lemma eta_re (C : FiniteConfiguration) :
    (∫ z : ℂ, z.re ∂(configTubeWitness C).eta) =
      (∫ x : ℝ, x ∂pinnedMeasure C.m C.pinned) +
        (C.m : ℝ)⁻¹ * ∑ a : Fin C.contourCount, (C.contour a).re := by
  have hp : Integrable (fun x : ℝ => x) (pinnedMeasure C.m C.pinned) := by
    have hbase : Integrable (fun x : ℝ => x)
        (volume.restrict (Set.Icc (1 / 4 : ℝ) (5 / 4 : ℝ))) := by
      exact continuous_id.integrableOn_Icc
    exact hbase.mono_measure (pinnedMeasure_le C)
  have hmap : Integrable (fun z : ℂ => z.re)
      (Measure.map Complex.ofReal (pinnedMeasure C.m C.pinned)) := by
    rw [integrable_map_measure Complex.measurable_re.aestronglyMeasurable
      Complex.measurable_ofReal.aemeasurable]
    simpa [Function.comp_def] using hp
  have hnu := contour_re_integrable C
  rw [witness_eta_eq, integral_add_measure hmap hnu,
    map_pinned_re C, contour_re C]

theorem witness_linear_shift_le (C : FiniteConfiguration)
    (hhead : ∀ r ∈ C.frequency, r ≤ 20 * C.m) :
    (∑ s ∈ C.pinned, (s : ℝ)) +
        (C.m : ℝ) * (∑ a : Fin C.contourCount, (C.contour a).re) -
        (∑ r ∈ C.frequency, (r : ℝ)) ≤
      -(C.m : ℝ) ^ 2 *
        ((∫ t : ℝ, t ∂(configTubeWitness C).mu) -
          ∫ z : ℂ, z.re ∂(configTubeWitness C).eta) := by
  have hmu := mu_first C
  have hpin := pinned_first C
  have heta := eta_re C
  change (∑ s ∈ C.pinned, (s : ℝ)) +
      (C.m : ℝ) * (∑ a : Fin C.contourCount, (C.contour a).re) -
      (∑ r ∈ C.frequency, (r : ℝ)) ≤
    -(C.m : ℝ) ^ 2 *
      ((∫ t : ℝ, t ∂frequencyMeasure C.m C.frequency) -
        ∫ z : ℂ, z.re ∂(configTubeWitness C).eta)
  rw [hmu, heta, hpin]
  have hcard : (C.frequency.card : ℝ) = (C.m : ℝ) := by
    exact_mod_cast C.frequency_card
  have hmc : (0 : ℝ) ≤ C.pinned.card := by positivity
  have hm : (0 : ℝ) < C.m := by exact_mod_cast (show 0 < C.m by
    have := C.m_ge_eight; omega)
  rw [← Finset.sum_div, Finset.sum_sub_distrib]
  rw [← Finset.sum_div]
  rw [← Finset.sum_div C.pinned (fun s : ℕ => (s : ℝ) + 1 / 2)
    ((C.m : ℝ) ^ 2)]
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.sum_add_distrib]
  rw [hcard]
  field_simp
  nlinarith

#print axioms witness_linear_shift_le

/-! Scaled contour form used by the q-dependent head estimate.  This is the
    same cell moment calculation with the literal `m * contour` points from
    v13 `paper-v13/p0-analytic.tex:700-747`. -/
theorem configTubeWitness_affine_shift_le (C : FiniteConfiguration)
    (hhead : ∀ r ∈ C.frequency, r ≤ 20 * C.m) :
    (∑ s ∈ C.pinned, (s : ℝ)) +
        (∑ a : Fin C.contourCount,
          (Complex.ofReal (C.m : ℝ) * C.contour a).re) -
        (∑ r ∈ C.frequency, (r : ℝ)) ≤
      -(C.m : ℝ) ^ 2 *
        ((∫ t : ℝ, t ∂(configTubeWitness C).mu) -
          ∫ z : ℂ, z.re ∂(configTubeWitness C).eta) := by
  simpa [Complex.mul_re, mul_comm, Finset.mul_sum] using
    (witness_linear_shift_le C hhead)

end
end Li2Lean.P0.CoefficientAssembly
