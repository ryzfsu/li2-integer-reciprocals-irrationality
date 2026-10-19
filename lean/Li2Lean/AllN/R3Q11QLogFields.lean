/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.Q11QLogEnvelope
import Li2Lean.P0.Q11CrossEnergy
import Li2Lean.P0.ContourProductIntegrability

/-!
# Unconditional analytic leaves for the q = 11 logarithmic-energy envelope

These proofs use the literal q = 11 table measures.  In particular they prove
all the integrability fields of `Q11QLogEnvelopeInputs` without assuming a
numerical enclosure or a finite-energy certificate.
-/

open MeasureTheory Set Filter
open scoped ENNReal

namespace Li2Lean.P0.Q11Data

noncomputable section

open Li2Lean.LogSegment
open ConfigContourReference ConfigContourMeasure
open ConfigContourSelfPotential ConfigContourProduct
open ConfigContourProductIntegrability

local instance : IsFiniteMeasure q11PinnedReferenceMeasure :=
  ⟨by rw [q11PinnedReferenceMeasure_mass]; exact ENNReal.ofReal_lt_top⟩

local instance : IsFiniteMeasure q11FrequencyReferenceMeasure :=
  ⟨by rw [q11FrequencyReferenceMeasure_univ]; exact ENNReal.one_lt_top⟩

local instance : IsFiniteMeasure q11ContourParamMeasure :=
  ⟨by rw [q11ContourParamMeasure_univ]; exact ENNReal.ofReal_lt_top⟩

theorem q11IntervalReferenceMeasure_integrable_of_continuous
    {f : ℝ → ℝ} (hf : Continuous f)
    (left right : ℕ → ℝ) (count : ℕ) (units : List ℕ) (width : ℝ) :
    Integrable f (q11IntervalReferenceMeasure left right count units width) := by
  unfold q11IntervalReferenceMeasure
  apply integrable_finsetSum_measure.mpr
  intro j hj
  exact (hf.integrableOn_Icc.mono_set Ico_subset_Icc_self).smul_measure
    ENNReal.ofReal_ne_top

theorem continuous_q11PinnedRealPotential : Continuous q11PinnedRealPotential := by
  have hform : q11PinnedRealPotential = fun x : ℝ =>
      ∑ j ∈ Finset.range 8, q11IntervalDensity pinnedMassUnits (1 / 8 : ℝ) j *
        (primitive (x - q11PinnedEdgeReal j) -
          primitive (x - q11PinnedEdgeReal (j + 1))) := by
    funext x
    exact q11PinnedPotential_eq_endpoints x
  rw [hform]
  apply continuous_finsetSum
  intro j hj
  exact continuous_const.mul
    ((continuous_primitive.comp (continuous_id.sub continuous_const)).sub
      (continuous_primitive.comp (continuous_id.sub continuous_const)))

theorem continuous_q11FrequencyPotential : Continuous q11FrequencyPotential := by
  have hform : q11FrequencyPotential = fun t : ℝ =>
      ∑ j ∈ Finset.range 4, q11IntervalDensity frequencyMassUnits 1 j *
        (primitive (t - q11FrequencyEdgeReal j) -
          primitive (t - q11FrequencyEdgeReal (j + 1))) := by
    funext t
    exact q11FrequencyPotential_eq_endpoints t
  rw [hform]
  apply continuous_finsetSum
  intro j hj
  exact continuous_const.mul
    ((continuous_primitive.comp (continuous_id.sub continuous_const)).sub
      (continuous_primitive.comp (continuous_id.sub continuous_const)))

theorem q11PinnedComplexPotential_real (x : ℝ) :
    q11PinnedComplexPotential (x : ℂ) = q11PinnedRealPotential x := by
  simp only [q11PinnedComplexPotential, q11PinnedRealPotential,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

theorem q11PinnedComplexPotential_pinned_integrable :
    Integrable (fun x : ℝ => q11PinnedComplexPotential (x : ℂ))
      q11PinnedReferenceMeasure := by
  simp_rw [q11PinnedComplexPotential_real]
  exact q11IntervalReferenceMeasure_integrable_of_continuous
    continuous_q11PinnedRealPotential _ _ _ _ _

theorem q11FrequencyPotential_frequency_integrable :
    Integrable q11FrequencyPotential q11FrequencyReferenceMeasure :=
  q11IntervalReferenceMeasure_integrable_of_continuous
    continuous_q11FrequencyPotential _ _ _ _ _

theorem q11ReflectedFrequencyPotential_real (x : ℝ) :
    q11ReflectedFrequencyPotential (x : ℂ) = q11FrequencyPotential (-x) := by
  unfold q11ReflectedFrequencyPotential q11FrequencyPotential
  apply integral_congr_ae
  filter_upwards [] with t
  rw [← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs]
  congr 1
  rw [show -x - t = -(x + t) by ring, abs_neg]

theorem q11ReflectedFrequencyPotential_pinned_integrable :
    Integrable (fun x : ℝ => q11ReflectedFrequencyPotential (x : ℂ))
      q11PinnedReferenceMeasure := by
  simp_rw [q11ReflectedFrequencyPotential_real]
  exact q11IntervalReferenceMeasure_integrable_of_continuous
    (continuous_q11FrequencyPotential.comp continuous_neg) _ _ _ _ _

private theorem q11_integrable_log_norm_of_bounds
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {f : α → ℂ} (hf : Measurable f) {lo hi : ℝ} (hlo : 0 < lo)
    (hbound : ∀ᵐ p ∂μ, lo ≤ ‖f p‖ ∧ ‖f p‖ ≤ hi) :
    Integrable (fun p => Real.log ‖f p‖) μ := by
  apply (integrable_const (|Real.log lo| + |Real.log hi|)).mono'
    (Real.measurable_log.comp (continuous_norm.measurable.comp hf)).aestronglyMeasurable
  filter_upwards [hbound] with p hp
  have h1 := Real.log_le_log hlo hp.1
  have h2 := Real.log_le_log (lt_of_lt_of_le hlo hp.1) hp.2
  change ‖Real.log ‖f p‖‖ ≤ _
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith [neg_abs_le (Real.log lo), le_abs_self (Real.log hi),
    abs_nonneg (Real.log lo), abs_nonneg (Real.log hi)]

theorem q11_contour_frequency_log_integrable :
    Integrable (fun p : ℂ × ℝ => Real.log ‖p.1 + (p.2 : ℂ)‖)
      (q11ContourReferenceMeasure.prod q11FrequencyReferenceMeasure) := by
  apply q11_integrable_log_norm_of_bounds (by fun_prop)
    (lo := 1749 / 5000) (hi := 9) (by norm_num)
  have h1 := (Measure.quasiMeasurePreserving_fst
    (μ := q11ContourReferenceMeasure) (ν := q11FrequencyReferenceMeasure)).ae
      q11ContourReferenceMeasure_ae_Gamma
  have h2 := (Measure.quasiMeasurePreserving_snd
    (μ := q11ContourReferenceMeasure) (ν := q11FrequencyReferenceMeasure)).ae
      q11FrequencyReferenceMeasure_ae_interval
  filter_upwards [h1, h2] with p hz ht
  constructor
  · have hsep := TubeEnergy.frequency_source_norm_sub_ge
      (x := -(p.2 : ℂ)) (by
        simp only [Complex.neg_re, Complex.ofReal_re]
        linarith [ht.1]) hz
    simpa only [sub_neg_eq_add] using hsep
  · have hzn := TubeVariance.norm_le_four_of_mem_Gamma hz
    have htn : ‖(p.2 : ℂ)‖ ≤ 9 / 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [ht.1])]
      exact ht.2
    exact (norm_add_le _ _).trans (by linarith)

theorem q11ReflectedFrequencyPotential_contour_integrable :
    Integrable q11ReflectedFrequencyPotential q11ContourReferenceMeasure :=
  q11_contour_frequency_log_integrable.integral_prod_left

theorem q11_contour_pinned_log_integrable :
    Integrable (fun p : ℂ × ℝ => Real.log ‖p.1 - (p.2 : ℂ)‖)
      (q11ContourReferenceMeasure.prod q11PinnedReferenceMeasure) := by
  apply q11_integrable_log_norm_of_bounds (by fun_prop)
    (lo := 751 / 5000) (hi := 6) (by norm_num)
  have h1 := (Measure.quasiMeasurePreserving_fst
    (μ := q11ContourReferenceMeasure) (ν := q11PinnedReferenceMeasure)).ae
      q11ContourReferenceMeasure_ae_Gamma
  have h2 := (Measure.quasiMeasurePreserving_snd
    (μ := q11ContourReferenceMeasure) (ν := q11PinnedReferenceMeasure)).ae
      q11PinnedReferenceMeasure_ae_interval
  filter_upwards [h1, h2] with p hz hx
  constructor
  · apply TubeEnergy.positive_source_norm_sub_ge
    · simp only [Complex.ofReal_re]
      constructor <;> linarith [hx.1, hx.2]
    · simp
    · exact hz
  · have hzn := TubeVariance.norm_le_four_of_mem_Gamma hz
    have hxn : ‖(p.2 : ℂ)‖ ≤ 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [hx.1])]
      linarith [hx.2]
    exact (norm_sub_le _ _).trans (by linarith)

theorem q11Eνκ_eq_Eκν : q11Eνκ = q11Eκν := by
  unfold q11Eνκ q11PinnedComplexPotential q11Eκν
  rw [integral_integral_swap q11_contour_pinned_log_integrable]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [q11ContourPotential_eq_integral]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [norm_sub_rev]

theorem q11ContourDensity_le_49 (u : ℝ) : q11ContourDensity u ≤ 49 := by
  have hmass : (∑ j : Fin contourNodeCount, q11ContourWeight j) ≤ 1 := by
    rw [q11ContourWeight_sum]
    apply (div_le_one (show 0 < (denominator : ℝ) by norm_num [denominator])).2
    have hnat : 2 * contourPairMassUnits.sum ≤ denominator := by
      have h := eta_mass_sum
      omega
    exact_mod_cast hnat
  calc
    q11ContourDensity u = ∑ j : Fin contourNodeCount,
        q11ContourWeight j * fejer48 (u - contourAngle j) := rfl
    _ ≤ ∑ j : Fin contourNodeCount, q11ContourWeight j * 49 := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left (fejer48_le_49 _) (q11ContourWeight_nonneg j)
    _ = (∑ j : Fin contourNodeCount, q11ContourWeight j) * 49 := by
      rw [Finset.sum_mul]
    _ ≤ 49 := by linarith

theorem q11_density_param_kernel_integrable : Integrable contourLogDistanceKernel
    ((volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))).withDensity
      (fun u => ENNReal.ofReal (q11ContourDensity u)) |>.prod
    ((volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))).withDensity
      (fun u => ENNReal.ofReal (q11ContourDensity u)))) := by
  let m : Measure ℝ := volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))
  let f : ℝ → ℝ≥0∞ := fun u => ENNReal.ofReal (q11ContourDensity u)
  have hf : Measurable f :=
    ENNReal.measurable_ofReal.comp continuous_q11ContourDensity.measurable
  have hbase : Integrable contourLogDistanceKernel (m.prod m) := by
    dsimp [m]
    rw [Measure.prod_restrict]
    apply contourLogDistanceKernel_integrable.mono_measure
    apply Measure.restrict_mono_set
    intro p hp
    exact ⟨⟨le_of_lt hp.1.1, hp.1.2⟩, ⟨le_of_lt hp.2.1, hp.2.2⟩⟩
  rw [show (m.withDensity f).prod (m.withDensity f) =
      (m.prod m).withDensity (fun p : ℝ × ℝ => f p.1 * f p.2)
    from prod_withDensity hf hf]
  have hfd : Measurable (fun p : ℝ × ℝ => f p.1 * f p.2) :=
    (hf.comp measurable_fst).mul (hf.comp measurable_snd)
  have hflt : ∀ᵐ p ∂(m.prod m), f p.1 * f p.2 < ⊤ := by
    filter_upwards [] with p
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  rw [integrable_withDensity_iff hfd hflt]
  let g : ℝ × ℝ → ℝ := fun p => (f p.1 * f p.2).toReal
  have hg : Measurable g := ENNReal.measurable_toReal.comp hfd
  have hg_bound : ∀ᵐ p ∂(m.prod m), ‖g p‖ ≤ (49 : ℝ) ^ 2 := by
    filter_upwards [] with p
    have h1 := q11ContourDensity_nonneg p.1
    have h2 := q11ContourDensity_nonneg p.2
    have hb1 := q11ContourDensity_le_49 p.1
    have hb2 := q11ContourDensity_le_49 p.2
    dsimp [g, f]
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal h1, ENNReal.toReal_ofReal h2]
    rw [abs_of_nonneg (mul_nonneg h1 h2)]
    nlinarith [mul_le_mul hb1 hb2 h2 (by norm_num : 0 ≤ (49 : ℝ))]
  have hw := hbase.mul_bdd hg.aestronglyMeasurable hg_bound
  simpa [g, Pi.mul_apply, Function.comp_apply] using hw

theorem q11ContourParam_kernel_integrable :
    Integrable contourLogDistanceKernel
      (q11ContourParamMeasure.prod q11ContourParamMeasure) := by
  apply q11_density_param_kernel_integrable.mono_measure
  apply Measure.prod_mono
  all_goals
    unfold q11ContourParamMeasure
    apply (Measure.le_iff').2
    intro s
    rw [Measure.smul_apply]
    change ENNReal.ofReal (2 * Real.pi)⁻¹ * _ ≤ _
    apply mul_le_of_le_one_left
    · exact bot_le
    simpa using (ENNReal.ofReal_le_ofReal
      ((inv_le_one₀ (show 0 < (2 * Real.pi : ℝ) by positivity)).2
        (by nlinarith [Real.pi_gt_three])))

theorem q11ContourReferenceMeasure_prod_log_integrable :
    Integrable (fun p : ℂ × ℂ => Real.log ‖p.1 - p.2‖)
      (q11ContourReferenceMeasure.prod q11ContourReferenceMeasure) := by
  change Integrable (fun p : ℂ × ℂ => Real.log ‖p.1 - p.2‖)
      ((q11ContourParamMeasure.map (Li2Lean.p0EllipsePoint 1)).prod
        (q11ContourParamMeasure.map (Li2Lean.p0EllipsePoint 1)))
  rw [Measure.map_prod_map q11ContourParamMeasure q11ContourParamMeasure
    continuous_ellipse.measurable continuous_ellipse.measurable]
  have hmeas : Measurable (fun p : ℂ × ℂ => Real.log ‖p.1 - p.2‖) :=
    Real.measurable_log.comp
      (continuous_norm.comp (continuous_fst.sub continuous_snd)).measurable
  exact (integrable_map_measure hmeas.aestronglyMeasurable
    (continuous_ellipse.measurable.prodMap continuous_ellipse.measurable).aemeasurable).2
      q11ContourParam_kernel_integrable

theorem q11ContourPotential_contour_integrable :
    Integrable q11ContourPotential q11ContourReferenceMeasure := by
  apply q11ContourReferenceMeasure_prod_log_integrable.integral_prod_left.congr
  filter_upwards [] with z
  exact (q11ContourPotential_eq_integral z).symm

/-- Every integrability field of the q = 11 seven-term energy split is proved. -/
theorem q11FiniteEnergyData_proved : Q11FiniteEnergyData where
  κκ := q11PinnedComplexPotential_pinned_integrable
  κν := q11ContourPotential_pinned_integrable
  νκ := q11PinnedComplexPotential_contour_integrable
  νν := q11ContourPotential_contour_integrable
  κμ := q11ReflectedFrequencyPotential_pinned_integrable
  νμ := q11ReflectedFrequencyPotential_contour_integrable

theorem q11ActualReference_qLog_eq_seven_terms_proved :
    q11ActualReference.qLog =
      q11Eκκ + q11Eκν + q11Eνκ + q11Eνν + q11Eμμ + q11Eκμ + q11Eνμ :=
  q11ActualReference_qLog_eq_seven_terms q11FiniteEnergyData_proved

theorem q11ActualReference_qLog_eq_six_terms_proved :
    q11ActualReference.qLog =
      q11Eκκ + 2 * q11Eκν + q11Eνν + q11Eμμ + q11Eκμ + q11Eνμ :=
  q11ActualReference_qLog_eq_six_terms q11FiniteEnergyData_proved q11Eνκ_eq_Eκν

end

end Li2Lean.P0.Q11Data

#print axioms Li2Lean.P0.Q11Data.q11PinnedComplexPotential_pinned_integrable
#print axioms Li2Lean.P0.Q11Data.q11ReflectedFrequencyPotential_pinned_integrable
#print axioms Li2Lean.P0.Q11Data.q11ReflectedFrequencyPotential_contour_integrable
#print axioms Li2Lean.P0.Q11Data.q11ContourPotential_contour_integrable
#print axioms Li2Lean.P0.Q11Data.q11FiniteEnergyData_proved
#print axioms Li2Lean.P0.Q11Data.q11ActualReference_qLog_eq_six_terms_proved
