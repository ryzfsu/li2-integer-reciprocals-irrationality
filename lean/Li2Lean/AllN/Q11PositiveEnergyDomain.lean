/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.AllN.Q11ShiftedDualAeAssembly
import Li2Lean.P0.Q11MeasureDomination
import Li2Lean.P0.Q11FrequencyFirstMoment
import Li2Lean.P0.ContourFieldFinite
import Li2Lean.P0.ContourProductIntegrability

open MeasureTheory Set Filter
open scoped ENNReal

namespace Li2Lean.AllNAssembly
noncomputable section
open Li2Lean.P0
open Li2Lean.P0.Q11Data
open Li2Lean.P0.TubeInterior
open Li2Lean.P0.ConfigContourReference


private lemma q11Dom0PinnedReferenceMeasure_singleton (x : ℝ) :
    q11PinnedReferenceMeasure {x} = 0 := by
  apply le_antisymm
  · calc
      q11PinnedReferenceMeasure {x} ≤
          (volume.restrict (Icc (1 / 4 : ℝ) (5 / 4 : ℝ))) {x} :=
        q11PinnedReferenceMeasure_le_restrict {x}
      _ ≤ volume {x} :=
        (Measure.restrict_le_self :
          volume.restrict (Icc (1 / 4 : ℝ) (5 / 4 : ℝ)) ≤ volume) _
      _ = 0 := Real.volume_singleton
  · exact bot_le

private lemma q11Dom0EtaReferenceMeasure_singleton (z : ℂ) :
    q11EtaReferenceMeasure {z} = 0 := by
  unfold q11EtaReferenceMeasure
  change (Measure.map Complex.ofReal q11PinnedReferenceMeasure) {z} +
      q11ContourReferenceMeasure {z} = 0
  have hmap : (Measure.map Complex.ofReal q11PinnedReferenceMeasure) {z} = 0 := by
    rw [Measure.map_apply Complex.continuous_ofReal.measurable
      (measurableSet_singleton z)]
    apply measure_mono_null
      (show Complex.ofReal ⁻¹' {z} ⊆ ({z.re} : Set ℝ) by
        intro x hx
        simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx
        simp [← hx])
    exact q11Dom0PinnedReferenceMeasure_singleton z.re
  rw [hmap, q11ContourReferenceMeasure_singleton, add_zero]

instance q11Dom0EtaFinite : IsFiniteMeasure q11EtaReferenceMeasure :=
  ⟨by rw [q11EtaReferenceMeasure_univ]; simp⟩

private lemma q11Dom0Eta_ae_norm :
    ∀ᵐ z ∂q11EtaReferenceMeasure, ‖z‖ ≤ 4 := by
  rw [q11EtaReferenceMeasure, ae_add_measure_iff]
  constructor
  · rw [ae_map_iff Complex.continuous_ofReal.aemeasurable
      (isClosed_le continuous_norm continuous_const).measurableSet]
    filter_upwards [q11PinnedReferenceMeasure_ae_interval] with x hx
    simp only [Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (by linarith [hx.1])]
    linarith [hx.2]
  · filter_upwards [q11ContourReferenceMeasure_ae_Gamma] with z hz
    exact TubeVariance.norm_le_four_of_mem_Gamma hz

private lemma q11Dom0Companion_integrable :
    Integrable (fun z : ℂ => p0CompanionField z) q11EtaReferenceMeasure := by
  apply EnergyLowerBound.integrable_companionField_of_ae_norm_le
  exact q11Dom0Eta_ae_norm

private lemma q11Dom0FrequencyField_integrable :
    Integrable (fun t : ℝ => p0RegularizedFrequencyField t)
      q11FrequencyReferenceMeasure := by
  letI : IsFiniteMeasure q11FrequencyReferenceMeasure :=
    ⟨by rw [q11FrequencyReferenceMeasure_univ]; simp⟩
  have hlog : ContinuousOn (fun t : ℝ => Real.log (1 + t))
      (Icc (1 / 2 : ℝ) (9 / 2 : ℝ)) := by
    apply ContinuousOn.log
    · fun_prop
    · intro t ht h0
      linarith [ht.1]
  have hfield : ContinuousOn (fun t : ℝ => p0RegularizedFrequencyField t)
      (Icc (1 / 2 : ℝ) (9 / 2 : ℝ)) := by
    unfold p0RegularizedFrequencyField
    exact ((ReferencePackaging.continuous_B0_literal.continuousOn.sub
      ReferencePackaging.continuous_psi_literal.continuousOn).sub
      (hlog.const_mul 3))
  have h : Integrable (fun t : ℝ => p0RegularizedFrequencyField t)
      (volume.restrict (Icc (1 / 2 : ℝ) (9 / 2 : ℝ))) := hfield.integrableOn_Icc
  exact h.mono_measure q11FrequencyReferenceMeasure_le_restrict

private lemma q11Dom0FrequencyReferenceMeasure_singleton (t : ℝ) :
    q11FrequencyReferenceMeasure {t} = 0 := by
  apply le_antisymm
  · calc
      q11FrequencyReferenceMeasure {t} ≤
          (volume.restrict (Icc (1 / 2 : ℝ) (9 / 2 : ℝ))) {t} :=
        q11FrequencyReferenceMeasure_le_restrict {t}
      _ ≤ volume {t} :=
        (Measure.restrict_le_self :
          volume.restrict (Icc (1 / 2 : ℝ) (9 / 2 : ℝ)) ≤ volume) _
      _ = 0 := Real.volume_singleton
  · exact bot_le

private lemma q11Dom0Frequency_log_abs_diff_integrable :
    Integrable (fun p : ℝ × ℝ => Real.log |p.1 - p.2|)
      (q11FrequencyReferenceMeasure.prod q11FrequencyReferenceMeasure) := by
  letI : IsFiniteMeasure q11FrequencyReferenceMeasure :=
    ⟨by rw [q11FrequencyReferenceMeasure_univ]; simp⟩
  let μ : Measure ℝ := volume.restrict (Ico (1 / 2 : ℝ) (9 / 2 : ℝ))
  have hμ : q11FrequencyReferenceMeasure ≤ μ := by
    calc
      q11FrequencyReferenceMeasure ≤
          volume.restrict (Icc (1 / 2 : ℝ) (9 / 2 : ℝ)) :=
        q11FrequencyReferenceMeasure_le_restrict
      _ = μ := by
        dsimp [μ]
        exact (Measure.restrict_congr_set Ico_ae_eq_Icc).symm
  have hbase : Integrable (fun p : ℝ × ℝ => Real.log |p.1 - p.2|)
      (μ.prod μ) := by
    dsimp [μ]
    exact Li2Lean.LogSegment.integrable_log_abs_sub_rectangle (by norm_num)
  exact hbase.mono_measure (Measure.prod_mono hμ hμ)

private lemma q11Dom0FrequencyKernel_integrable :
    Integrable (fun x : ℝ × ℝ => p0RegularizedFrequencyKernel x.1 x.2)
      (q11FrequencyReferenceMeasure.prod q11FrequencyReferenceMeasure) := by
  letI : IsFiniteMeasure q11FrequencyReferenceMeasure :=
    ⟨by rw [q11FrequencyReferenceMeasure_univ]; simp⟩
  have hlog1 : Integrable (fun t : ℝ => Real.log (1 + t))
      q11FrequencyReferenceMeasure := by
    have hlog : ContinuousOn (fun t : ℝ => Real.log (1 + t))
        (Icc (1 / 2 : ℝ) (9 / 2 : ℝ)) := by
      apply ContinuousOn.log
      · fun_prop
      · intro t ht h0
        linarith [ht.1]
    have h : Integrable (fun t : ℝ => Real.log (1 + t))
        (volume.restrict (Icc (1 / 2 : ℝ) (9 / 2 : ℝ))) := hlog.integrableOn_Icc
    exact h.mono_measure q11FrequencyReferenceMeasure_le_restrict
  have h1 : Integrable (fun p : ℝ × ℝ => Real.log (1 + p.1))
      (q11FrequencyReferenceMeasure.prod q11FrequencyReferenceMeasure) :=
    hlog1.comp_fst q11FrequencyReferenceMeasure
  have h2 : Integrable (fun p : ℝ × ℝ => Real.log (1 + p.2))
      (q11FrequencyReferenceMeasure.prod q11FrequencyReferenceMeasure) :=
    hlog1.comp_snd q11FrequencyReferenceMeasure
  have hlog := q11Dom0Frequency_log_abs_diff_integrable
  have hbase : Integrable (fun p : ℝ × ℝ =>
      Real.log (1 + p.1) + Real.log (1 + p.2) - Real.log |p.1 - p.2|)
      (q11FrequencyReferenceMeasure.prod q11FrequencyReferenceMeasure) :=
    h1.add h2 |>.sub hlog
  have hdiag : (q11FrequencyReferenceMeasure.prod q11FrequencyReferenceMeasure)
      (Set.diagonal ℝ) = 0 := by
    rw [Measure.measure_prod_null measurableSet_diagonal]
    filter_upwards with t
    have hset : Prod.mk t ⁻¹' Set.diagonal ℝ = {t} := by
      ext s
      simp [Set.diagonal, eq_comm]
    simp [hset, q11Dom0FrequencyReferenceMeasure_singleton]
  have hne : ∀ᵐ p : ℝ × ℝ ∂(q11FrequencyReferenceMeasure.prod
      q11FrequencyReferenceMeasure), p.1 ≠ p.2 := by
    rw [ae_iff]
    have hset : {p : ℝ × ℝ | ¬ p.1 ≠ p.2} = Set.diagonal ℝ := by
      ext p
      simp [Set.diagonal]
    rw [hset]
    exact hdiag
  have ha1 : ∀ᵐ p : ℝ × ℝ ∂(q11FrequencyReferenceMeasure.prod
      q11FrequencyReferenceMeasure), p.1 ∈ Icc (1 / 2 : ℝ) (9 / 2 : ℝ) :=
    (Measure.quasiMeasurePreserving_fst
      (μ := q11FrequencyReferenceMeasure)
      (ν := q11FrequencyReferenceMeasure)).ae
      q11FrequencyReferenceMeasure_ae_interval
  have ha2 : ∀ᵐ p : ℝ × ℝ ∂(q11FrequencyReferenceMeasure.prod
      q11FrequencyReferenceMeasure), p.2 ∈ Icc (1 / 2 : ℝ) (9 / 2 : ℝ) :=
    (Measure.quasiMeasurePreserving_snd
      (μ := q11FrequencyReferenceMeasure)
      (ν := q11FrequencyReferenceMeasure)).ae
      q11FrequencyReferenceMeasure_ae_interval
  refine hbase.congr ?_
  filter_upwards [hne, ha1, ha2] with p hne hp1 hp2
  have h1pos : (0 : ℝ) < 1 + p.1 := by linarith [hp1.1]
  have h2pos : (0 : ℝ) < 1 + p.2 := by linarith [hp2.1]
  have h1ne : (1 + p.1) ≠ 0 := ne_of_gt h1pos
  have h2ne : (1 + p.2) ≠ 0 := ne_of_gt h2pos
  have hdiff : |p.1 - p.2| ≠ 0 := abs_ne_zero.mpr (sub_ne_zero.mpr hne)
  simp only [p0RegularizedFrequencyKernel, if_neg hne]
  rw [Real.log_div (mul_ne_zero h1ne h2ne) hdiff, Real.log_mul h1ne h2ne]

private lemma q11Dom0ContourDensity_le_49_mass (u : ℝ) :
    q11ContourDensity u ≤
      49 * ((2 * contourPairMassUnits.sum : ℝ) / (denominator : ℝ)) := by
  unfold q11ContourDensity
  have hsum : (∑ j : Fin contourNodeCount,
      q11ContourWeight j * 49) =
      49 * ((2 * contourPairMassUnits.sum : ℝ) / (denominator : ℝ)) := by
    rw [← Finset.sum_mul, q11ContourWeight_sum]
    ring
  calc
    (∑ j : Fin contourNodeCount,
        q11ContourWeight j * fejer48 (u - contourAngle j)) ≤
      ∑ j : Fin contourNodeCount, q11ContourWeight j * 49 := by
        apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul_of_nonneg_left
          (Li2Lean.P0.ConfigContourProductIntegrability.fejer48_le_49 _)
          (q11ContourWeight_nonneg j)
    _ = 49 * ((2 * contourPairMassUnits.sum : ℝ) / (denominator : ℝ)) := hsum

private lemma q11Dom0ContourDensity_param_kernel_integrable :
    Integrable Li2Lean.P0.ConfigContourSelfPotential.contourLogDistanceKernel
      (((volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))).withDensity
        (fun u => ENNReal.ofReal (q11ContourDensity u))).prod
      ((volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))).withDensity
        (fun u => ENNReal.ofReal (q11ContourDensity u)))) := by
  let m : Measure ℝ := volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))
  let f : ℝ → ℝ≥0∞ := fun u => ENNReal.ofReal (q11ContourDensity u)
  have hf : Measurable f :=
    ENNReal.measurable_ofReal.comp continuous_q11ContourDensity.measurable
  have hbase : Integrable Li2Lean.P0.ConfigContourSelfPotential.contourLogDistanceKernel
      (m.prod m) := by
    dsimp [m]
    rw [Measure.prod_restrict]
    apply Li2Lean.P0.ConfigContourProduct.contourLogDistanceKernel_integrable.mono_measure
    apply Measure.restrict_mono_set
    intro p hp
    exact ⟨⟨le_of_lt hp.1.1, hp.1.2⟩, ⟨le_of_lt hp.2.1, hp.2.2⟩⟩
  rw [show (m.withDensity f).prod (m.withDensity f) =
      (m.prod m).withDensity (fun p : ℝ × ℝ => f p.1 * f p.2) from
        prod_withDensity hf hf]
  have hfd : Measurable (fun p : ℝ × ℝ => f p.1 * f p.2) :=
    (hf.comp measurable_fst).mul (hf.comp measurable_snd)
  have hmass : 0 ≤ ((2 * contourPairMassUnits.sum : ℝ) / (denominator : ℝ)) := by
    positivity
  have hbound : ∀ u : ℝ, f u ≤
      ENNReal.ofReal (49 * ((2 * contourPairMassUnits.sum : ℝ) /
        (denominator : ℝ))) := by
    intro u
    exact ENNReal.ofReal_le_ofReal (q11Dom0ContourDensity_le_49_mass u)
  have hflt : ∀ᵐ p ∂(m.prod m), f p.1 * f p.2 < ⊤ := by
    filter_upwards [] with p
    calc
      f p.1 * f p.2 ≤
          ENNReal.ofReal (49 * ((2 * contourPairMassUnits.sum : ℝ) /
            (denominator : ℝ))) *
            ENNReal.ofReal (49 * ((2 * contourPairMassUnits.sum : ℝ) /
            (denominator : ℝ))) :=
        mul_le_mul (hbound p.1) (hbound p.2) (by positivity) (by positivity)
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  rw [integrable_withDensity_iff hfd hflt]
  let g : ℝ × ℝ → ℝ := fun p => (f p.1 * f p.2).toReal
  have hg : Measurable g := ENNReal.measurable_toReal.comp hfd
  have hg_bound : ∀ᵐ p ∂(m.prod m), ‖g p‖ ≤
      (49 * ((2 * contourPairMassUnits.sum : ℝ) / (denominator : ℝ))) ^ 2 := by
    filter_upwards [] with p
    have h1 : 0 ≤ q11ContourDensity p.1 := q11ContourDensity_nonneg _
    have h2 : 0 ≤ q11ContourDensity p.2 := q11ContourDensity_nonneg _
    have hb1 := q11Dom0ContourDensity_le_49_mass p.1
    have hb2 := q11Dom0ContourDensity_le_49_mass p.2
    dsimp [g, f]
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal h1, ENNReal.toReal_ofReal h2]
    rw [abs_of_nonneg (mul_nonneg h1 h2)]
    nlinarith
  have hw := hbase.mul_bdd hg.aestronglyMeasurable hg_bound
  simpa [g, f, Pi.mul_apply, Function.comp_apply] using hw

private lemma q11Dom0ContourParam_kernel_integrable :
    Integrable Li2Lean.P0.ConfigContourSelfPotential.contourLogDistanceKernel
      (q11ContourParamMeasure.prod q11ContourParamMeasure) := by
  letI : IsFiniteMeasure q11ContourParamMeasure := ⟨by
    rw [q11ContourParamMeasure_univ]
    exact ENNReal.ofReal_lt_top⟩
  let m : Measure ℝ := volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))
  let f : ℝ → ℝ≥0∞ := fun u => ENNReal.ofReal (q11ContourDensity u)
  have hdensity : Integrable Li2Lean.P0.ConfigContourSelfPotential.contourLogDistanceKernel
      ((m.withDensity f).prod (m.withDensity f)) := by
    simpa [m, f] using q11Dom0ContourDensity_param_kernel_integrable
  apply hdensity.mono_measure
  apply Measure.prod_mono
  · unfold q11ContourParamMeasure
    change ENNReal.ofReal (2 * Real.pi)⁻¹ • (m.withDensity f) ≤ m.withDensity f
    apply (Measure.le_iff').2
    intro s
    rw [Measure.smul_apply]
    apply mul_le_of_le_one_left
    · exact bot_le
    · simpa using (ENNReal.ofReal_le_ofReal
        ((inv_le_one₀ (show 0 < (2 * Real.pi : ℝ) by positivity)).2
          (by nlinarith [Real.pi_gt_three])))
  · unfold q11ContourParamMeasure
    change ENNReal.ofReal (2 * Real.pi)⁻¹ • (m.withDensity f) ≤ m.withDensity f
    apply (Measure.le_iff').2
    intro s
    rw [Measure.smul_apply]
    apply mul_le_of_le_one_left
    · exact bot_le
    · simpa using (ENNReal.ofReal_le_ofReal
        ((inv_le_one₀ (show 0 < (2 * Real.pi : ℝ) by positivity)).2
          (by nlinarith [Real.pi_gt_three])))

private lemma q11Dom0ContourReferenceMeasure_prod_integrable :
    Integrable (fun p : ℂ × ℂ => li2LogKernel p.1 p.2)
      (q11ContourReferenceMeasure.prod q11ContourReferenceMeasure) := by
  letI : IsFiniteMeasure q11ContourParamMeasure := ⟨by
    rw [q11ContourParamMeasure_univ]
    exact ENNReal.ofReal_lt_top⟩
  change Integrable (fun p : ℂ × ℂ => li2LogKernel p.1 p.2)
      ((q11ContourParamMeasure.map (Li2Lean.p0EllipsePoint 1)).prod
        (q11ContourParamMeasure.map (Li2Lean.p0EllipsePoint 1)))
  rw [Measure.map_prod_map q11ContourParamMeasure q11ContourParamMeasure
    ConfigContourMeasure.continuous_ellipse.measurable
    ConfigContourMeasure.continuous_ellipse.measurable]
  have hmeas : Measurable (fun p : ℂ × ℂ => li2LogKernel p.1 p.2) := by
    unfold li2LogKernel
    exact (Real.measurable_log.comp
      (by fun_prop : Measurable (fun p : ℂ × ℂ => ‖p.1 - p.2‖))).neg
  apply (integrable_map_measure
    hmeas.aestronglyMeasurable
    (ConfigContourMeasure.continuous_ellipse.measurable.prodMap
      ConfigContourMeasure.continuous_ellipse.measurable).aemeasurable).2
  have hneg := q11Dom0ContourParam_kernel_integrable.neg
  refine hneg.congr (Filter.Eventually.of_forall (fun p => ?_))
  simp [li2LogKernel,
    Li2Lean.P0.ConfigContourSelfPotential.contourLogDistanceKernel]

private lemma q11Dom0PinnedReferenceMeasure_log_abs_diff_integrable :
    Integrable (fun p : ℝ × ℝ => Real.log |p.1 - p.2|)
      (q11PinnedReferenceMeasure.prod q11PinnedReferenceMeasure) := by
  letI : IsFiniteMeasure q11PinnedReferenceMeasure :=
    ⟨by rw [q11PinnedReferenceMeasure_mass]; exact ENNReal.ofReal_lt_top⟩
  let μ : Measure ℝ := volume.restrict (Ico (1 / 4 : ℝ) (5 / 4 : ℝ))
  have hμ : q11PinnedReferenceMeasure ≤ μ := by
    calc
      q11PinnedReferenceMeasure ≤
          volume.restrict (Icc (1 / 4 : ℝ) (5 / 4 : ℝ)) :=
        q11PinnedReferenceMeasure_le_restrict
      _ = μ := by
        dsimp [μ]
        exact (Measure.restrict_congr_set Ico_ae_eq_Icc).symm
  have hbase : Integrable (fun p : ℝ × ℝ => Real.log |p.1 - p.2|)
      (μ.prod μ) := by
    dsimp [μ]
    exact Li2Lean.LogSegment.integrable_log_abs_sub_rectangle (by norm_num)
  exact hbase.mono_measure (Measure.prod_mono hμ hμ)

private lemma q11Dom0PinnedComplexMeasure_prod_integrable :
    Integrable (fun p : ℂ × ℂ => li2LogKernel p.1 p.2)
      ((Measure.map Complex.ofReal q11PinnedReferenceMeasure).prod
        (Measure.map Complex.ofReal q11PinnedReferenceMeasure)) := by
  letI : IsFiniteMeasure q11PinnedReferenceMeasure :=
    ⟨by rw [q11PinnedReferenceMeasure_mass]; exact ENNReal.ofReal_lt_top⟩
  rw [Measure.map_prod_map q11PinnedReferenceMeasure q11PinnedReferenceMeasure
    Complex.continuous_ofReal.measurable Complex.continuous_ofReal.measurable]
  have hmeas : Measurable (fun p : ℂ × ℂ => li2LogKernel p.1 p.2) := by
    unfold li2LogKernel
    exact (Real.measurable_log.comp
      (by fun_prop : Measurable (fun p : ℂ × ℂ => ‖p.1 - p.2‖))).neg
  apply (integrable_map_measure
    hmeas.aestronglyMeasurable
    (Complex.continuous_ofReal.measurable.prodMap
      Complex.continuous_ofReal.measurable).aemeasurable).2
  have hneg := q11Dom0PinnedReferenceMeasure_log_abs_diff_integrable.neg
  refine hneg.congr (Filter.Eventually.of_forall (fun p => ?_))
  change -Real.log |p.1 - p.2| =
    -Real.log ‖(p.1 : ℂ) - (p.2 : ℂ)‖
  congr 1
  have heq : (p.1 : ℂ) - (p.2 : ℂ) = ((p.1 - p.2 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [heq, Complex.norm_real, Real.norm_eq_abs]

private lemma q11Dom0Eta_kernel_integrable :
    Integrable (fun p : ℂ × ℂ => li2LogKernel p.1 p.2)
      (q11EtaReferenceMeasure.prod q11EtaReferenceMeasure) := by
  letI : IsFiniteMeasure q11PinnedReferenceMeasure :=
    ⟨by rw [q11PinnedReferenceMeasure_mass]; exact ENNReal.ofReal_lt_top⟩
  letI : IsFiniteMeasure (Measure.map Complex.ofReal q11PinnedReferenceMeasure) := by
    refine ⟨?_⟩
    rw [Measure.map_apply Complex.continuous_ofReal.measurable MeasurableSet.univ]
    simp only [Set.preimage_univ, q11PinnedReferenceMeasure_mass]
    exact ENNReal.ofReal_lt_top
  letI : IsFiniteMeasure q11ContourReferenceMeasure :=
    q11ContourReferenceMeasure_isFinite
  letI : IsFiniteMeasure
      (Measure.map Complex.ofReal q11PinnedReferenceMeasure +
        q11ContourReferenceMeasure) := by
    refine ⟨?_⟩
    rw [Measure.add_apply _ _ Set.univ,
      Measure.map_apply Complex.continuous_ofReal.measurable MeasurableSet.univ]
    simp only [Set.preimage_univ]
    exact (ENNReal.add_lt_top).2 ⟨
      (show q11PinnedReferenceMeasure Set.univ < ⊤ from
        IsFiniteMeasure.measure_univ_lt_top),
      q11ContourReferenceMeasure_isFinite.measure_univ_lt_top⟩
  have hκκ := q11Dom0PinnedComplexMeasure_prod_integrable
  have hκν := q11_pinned_contour_cross_integrable
  have hνκ := q11_contour_pinned_cross_integrable
  have hνν := q11Dom0ContourReferenceMeasure_prod_integrable
  change Integrable (fun p : ℂ × ℂ => li2LogKernel p.1 p.2)
      ((Measure.map Complex.ofReal q11PinnedReferenceMeasure +
        q11ContourReferenceMeasure).prod
        (Measure.map Complex.ofReal q11PinnedReferenceMeasure +
        q11ContourReferenceMeasure))
  rw [Measure.add_prod, Measure.prod_add, Measure.prod_add]
  exact (hκκ.add_measure hκν).add_measure (hνκ.add_measure hνν)

private lemma q11Dom0Pinned_mixed_kernel_integrable :
    Integrable (fun p : ℂ × ℝ => p0RegularizedMixedKernel p.1 p.2)
      ((Measure.map Complex.ofReal q11PinnedReferenceMeasure).prod
        q11FrequencyReferenceMeasure) := by
  letI : IsFiniteMeasure q11PinnedReferenceMeasure :=
    ⟨by rw [q11PinnedReferenceMeasure_mass]; exact ENNReal.ofReal_lt_top⟩
  letI : IsFiniteMeasure (Measure.map Complex.ofReal q11PinnedReferenceMeasure) := by
    refine ⟨?_⟩
    rw [Measure.map_apply Complex.continuous_ofReal.measurable MeasurableSet.univ]
    simp only [Set.preimage_univ, q11PinnedReferenceMeasure_mass]
    exact ENNReal.ofReal_lt_top
  letI : IsFiniteMeasure q11FrequencyReferenceMeasure :=
    ⟨by rw [q11FrequencyReferenceMeasure_univ]; simp⟩
  have hmeas : Measurable (fun p : ℂ × ℝ => p0RegularizedMixedKernel p.1 p.2) := by
    unfold p0RegularizedMixedKernel
    fun_prop
  apply TubeEnergy.integrable_of_bound_ae hmeas.stronglyMeasurable.aestronglyMeasurable
    (C := Real.log 2)
  have hp : ∀ᵐ y : ℂ ∂(Measure.map Complex.ofReal q11PinnedReferenceMeasure),
      y.re ∈ Icc (1 / 4 : ℝ) (5 / 4 : ℝ) ∧ y.im = 0 := by
    have hmeasSet : MeasurableSet {y : ℂ |
        y.re ∈ Icc (1 / 4 : ℝ) (5 / 4 : ℝ) ∧ y.im = 0} := by
      exact measurableSet_Icc.preimage Complex.continuous_re.measurable |>.inter
        ((measurableSet_singleton (0 : ℝ)).preimage Complex.continuous_im.measurable)
    rw [ae_map_iff Complex.continuous_ofReal.aemeasurable hmeasSet]
    filter_upwards [q11PinnedReferenceMeasure_ae_interval] with x hx
    constructor
    · simpa using hx
    · simp
  have hf := q11FrequencyReferenceMeasure_ae_interval
  have h1 := (Measure.quasiMeasurePreserving_fst
    (μ := Measure.map Complex.ofReal q11PinnedReferenceMeasure)
    (ν := q11FrequencyReferenceMeasure)).ae hp
  have h2 := (Measure.quasiMeasurePreserving_snd
    (μ := Measure.map Complex.ofReal q11PinnedReferenceMeasure)
    (ν := q11FrequencyReferenceMeasure)).ae hf
  filter_upwards [h1, h2] with p hy ht
  have hyreal : p.1 = (p.1.re : ℂ) := by
    apply Complex.ext <;> simp [hy.2]
  have hdenpos : (0 : ℝ) < p.1.re + p.2 := by linarith [hy.1.1, ht.1]
  have hratio_lo : (1 / 2 : ℝ) ≤ (1 + p.2) / (p.1.re + p.2) := by
    apply (le_div_iff₀ hdenpos).2
    linarith [hy.1.2, ht.1]
  have hratio_hi : (1 + p.2) / (p.1.re + p.2) ≤ (2 : ℝ) := by
    apply (div_le_iff₀ hdenpos).2
    linarith [hy.1.1, ht.1]
  have hloglo : Real.log (1 / 2 : ℝ) ≤
      Real.log ((1 + p.2) / (p.1.re + p.2)) :=
    Real.log_le_log (by norm_num) hratio_lo
  have hloghi : Real.log ((1 + p.2) / (p.1.re + p.2)) ≤ Real.log 2 :=
    Real.log_le_log (by positivity) hratio_hi
  unfold p0RegularizedMixedKernel
  rw [hyreal]
  have heq : (p.1.re : ℂ) + (p.2 : ℂ) =
      ((p.1.re + p.2 : ℝ) : ℂ) := by
    push_cast
    ring
  have hsumpos : (0 : ℝ) ≤ p.1.re + p.2 := by linarith [hy.1.1, ht.1]
  rw [heq, Complex.norm_real, Real.norm_eq_abs]
  simp only [abs_of_nonneg hsumpos]
  apply abs_le.mpr
  have hhalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
  constructor <;> linarith [hloglo, hloghi, hhalf]

private lemma q11Dom0Contour_mixed_kernel_integrable :
    Integrable (fun p : ℂ × ℝ => p0RegularizedMixedKernel p.1 p.2)
      (q11ContourReferenceMeasure.prod q11FrequencyReferenceMeasure) := by
  letI : IsFiniteMeasure q11ContourReferenceMeasure :=
    q11ContourReferenceMeasure_isFinite
  letI : IsFiniteMeasure q11FrequencyReferenceMeasure :=
    ⟨by rw [q11FrequencyReferenceMeasure_univ]; simp⟩
  have hmeas : Measurable (fun p : ℂ × ℝ => p0RegularizedMixedKernel p.1 p.2) := by
    unfold p0RegularizedMixedKernel
    fun_prop
  apply TubeEnergy.integrable_of_bound_ae hmeas.stronglyMeasurable.aestronglyMeasurable
    (C := Real.log 18)
  have h1 := (Measure.quasiMeasurePreserving_fst
    (μ := q11ContourReferenceMeasure)
    (ν := q11FrequencyReferenceMeasure)).ae q11ContourReferenceMeasure_ae_Gamma
  have h2 := (Measure.quasiMeasurePreserving_snd
    (μ := q11ContourReferenceMeasure)
    (ν := q11FrequencyReferenceMeasure)).ae q11FrequencyReferenceMeasure_ae_interval
  filter_upwards [h1, h2] with p hz ht
  have hδmax : (0 : ℝ) ≤ tubeRadiusMax := by
    norm_num [tubeRadiusMax]
  exact TubeEnergy.p0RegularizedMixedKernel_bound_on_tube hδmax
    p.1 (TubeEnergy.Gamma_subset_tube (δ := 0) (by norm_num) hz)
    p.2 ht.1

private lemma q11Dom0Eta_mixed_kernel_integrable :
    Integrable (fun p : ℂ × ℝ => p0RegularizedMixedKernel p.1 p.2)
      (q11EtaReferenceMeasure.prod q11FrequencyReferenceMeasure) := by
  letI : IsFiniteMeasure q11PinnedReferenceMeasure :=
    ⟨by rw [q11PinnedReferenceMeasure_mass]; exact ENNReal.ofReal_lt_top⟩
  letI : IsFiniteMeasure (Measure.map Complex.ofReal q11PinnedReferenceMeasure) := by
    refine ⟨?_⟩
    rw [Measure.map_apply Complex.continuous_ofReal.measurable MeasurableSet.univ]
    simp only [Set.preimage_univ, q11PinnedReferenceMeasure_mass]
    exact ENNReal.ofReal_lt_top
  letI : IsFiniteMeasure q11ContourReferenceMeasure :=
    q11ContourReferenceMeasure_isFinite
  letI : IsFiniteMeasure q11FrequencyReferenceMeasure :=
    ⟨by rw [q11FrequencyReferenceMeasure_univ]; simp⟩
  change Integrable (fun p : ℂ × ℝ => p0RegularizedMixedKernel p.1 p.2)
      ((Measure.map Complex.ofReal q11PinnedReferenceMeasure +
        q11ContourReferenceMeasure).prod q11FrequencyReferenceMeasure)
  rw [Measure.add_prod]
  exact q11Dom0Pinned_mixed_kernel_integrable.add_measure
    q11Dom0Contour_mixed_kernel_integrable

theorem q11PositiveEnergyDomain :
    p0PositiveEnergyDomain q11AdmissibleMeasures := by
  have hfin : P0FiniteEnergyCondition q11AdmissibleMeasures := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact q11FrequencyReferenceMeasure_integrable_id
    · simpa only [q11AdmissibleMeasures_eta_eq] using
        q11Dom0Companion_integrable
    · exact q11Dom0FrequencyField_integrable
    · simpa only [q11AdmissibleMeasures_eta_eq] using
        q11Dom0Eta_kernel_integrable
    · intro z
      simpa only [q11AdmissibleMeasures_eta_eq] using
        q11Dom0EtaReferenceMeasure_singleton z
    · exact q11Dom0FrequencyKernel_integrable
    · rw [q11AdmissibleMeasures_eta_eq]
      change Integrable (fun p : ℂ × ℝ => p0RegularizedMixedKernel p.1 p.2)
        (q11EtaReferenceMeasure.prod q11FrequencyReferenceMeasure)
      exact q11Dom0Eta_mixed_kernel_integrable
  have hRe : Integrable (fun z : ℂ => z.re) q11AdmissibleMeasures.eta := by
    rw [q11AdmissibleMeasures_eta_eq]
    apply Integrable.mono' (integrable_const (4 : ℝ))
      Complex.continuous_re.aestronglyMeasurable
    filter_upwards [q11Dom0Eta_ae_norm] with z hz
    simpa [Real.norm_eq_abs] using (Complex.abs_re_le_norm z).trans hz
  exact ⟨hfin, hRe⟩

end
end Li2Lean.AllNAssembly
