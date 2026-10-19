/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.Q11WmuTail
import Li2Lean.P0.Q11EndpointCoarseV2
import Li2Lean.P0.Q11BridgeAlt
import Li2Lean.P0.TubeSweepSources
import Li2Lean.P0.TubeExteriorPair
import Li2Lean.P0.ContourEnergyLowerBound

open MeasureTheory Set Filter
open scoped ENNReal

namespace Li2Lean.P0.Q11Data

noncomputable section

open Li2Lean.P0.ConfigContourTail

/-! Endpoint bounds for the literal q = 11 measures.  The estimates are
proved against the actual interval and contour measures, rather than against
the finite table alone. -/

theorem q11FrequencyReferenceMeasure_ae_interval :
    ∀ᵐ t ∂q11FrequencyReferenceMeasure, t ∈ Icc (1 / 2 : ℝ) (9 / 2 : ℝ) := by
  unfold q11FrequencyReferenceMeasure q11IntervalReferenceMeasure
  rw [ae_finsetSum_measure_iff]
  intro j hj
  apply Measure.ae_smul_measure
  filter_upwards [ae_restrict_mem measurableSet_Ico] with t ht
  have hj4 : j < 4 := Finset.mem_range.mp hj
  have hleft : q11FrequencyEdgeReal j ≤ q11FrequencyEdgeReal (j + 1) := by
    linarith [q11FrequencyEdgeReal_width hj4]
  have hfirst : (1 / 2 : ℝ) ≤ q11FrequencyEdgeReal j := by
    interval_cases j <;>
      norm_num [q11FrequencyEdgeReal, frequencyEdge, frequencyEdge2Units]
  have hlast : q11FrequencyEdgeReal (j + 1) ≤ (9 / 2 : ℝ) := by
    have hj' : j + 1 ≤ 4 := by omega
    interval_cases j <;>
      norm_num [q11FrequencyEdgeReal, frequencyEdge, frequencyEdge2Units]
  exact ⟨le_trans hfirst ht.1, le_trans (le_of_lt ht.2) hlast⟩

theorem q11FrequencyPotential_le_log38 :
    q11FrequencyPotential (81 / 10 : ℝ) ≤ Real.log (38 / 5) := by
  letI : IsFiniteMeasure q11FrequencyReferenceMeasure := ⟨by
    rw [q11FrequencyReferenceMeasure_univ]
    exact ENNReal.one_lt_top⟩
  have hleft : ∀ j ∈ Finset.range 4,
      q11FrequencyEdgeReal j ≤ q11FrequencyEdgeReal (j + 1) := by
    intro j hj
    linarith [q11FrequencyEdgeReal_width (Finset.mem_range.mp hj)]
  have hInt : Integrable (fun x : ℝ => Real.log |(81 / 10 : ℝ) - x|)
      q11FrequencyReferenceMeasure := by
    exact integrable_log_q11IntervalReferenceMeasure
      q11FrequencyEdgeReal (fun j => q11FrequencyEdgeReal (j + 1)) 4
      frequencyMassUnits 1 hleft (81 / 10 : ℝ)
  have hbound : ∀ᵐ x : ℝ ∂q11FrequencyReferenceMeasure,
      Real.log |(81 / 10 : ℝ) - x| ≤ Real.log (38 / 5) := by
    filter_upwards [q11FrequencyReferenceMeasure_ae_interval] with x hx
    have hpos : 0 < (81 / 10 : ℝ) - x := by linarith [hx.2]
    rw [abs_of_pos hpos]
    apply Real.log_le_log
    · linarith
    · linarith [hx.1]
  have hmono := integral_mono_ae hInt
    (integrable_const (μ := q11FrequencyReferenceMeasure) (Real.log (38 / 5))) hbound
  change (∫ x, Real.log |(81 / 10 : ℝ) - x| ∂q11FrequencyReferenceMeasure) ≤ _ at hmono
  calc
    q11FrequencyPotential (81 / 10 : ℝ) =
        ∫ x, Real.log |(81 / 10 : ℝ) - x| ∂q11FrequencyReferenceMeasure := rfl
    _ ≤ ∫ _ : ℝ, Real.log (38 / 5) ∂q11FrequencyReferenceMeasure := hmono
    _ = Real.log (38 / 5) := by
      rw [integral_const, Measure.real, q11FrequencyReferenceMeasure_univ]
      simp

theorem q11PinnedReferenceMeasure_ae_interval :
    ∀ᵐ x ∂q11PinnedReferenceMeasure, x ∈ Icc (1 / 4 : ℝ) (5 / 4 : ℝ) := by
  unfold q11PinnedReferenceMeasure q11IntervalReferenceMeasure
  rw [ae_finsetSum_measure_iff]
  intro j hj
  apply Measure.ae_smul_measure
  filter_upwards [ae_restrict_mem measurableSet_Ico] with x hx
  have hj8 : j < 8 := Finset.mem_range.mp hj
  have hleft : q11PinnedEdgeReal j ≤ q11PinnedEdgeReal (j + 1) := by
    linarith [q11PinnedEdgeReal_width hj8]
  have hfirst : (1 / 4 : ℝ) ≤ q11PinnedEdgeReal j :=
    q11PinnedEdgeReal_ge_quarter hj8
  have hlast : q11PinnedEdgeReal (j + 1) ≤ (5 / 4 : ℝ) := by
    have hj' : j + 1 ≤ 8 := by omega
    interval_cases j <;>
      norm_num [q11PinnedEdgeReal, pinnedEdge, pinnedEdge32Units]
  exact ⟨le_trans hfirst hx.1, le_trans (le_of_lt hx.2) hlast⟩

theorem q11ContourReferenceMeasure_ae_Gamma :
    ∀ᵐ z ∂q11ContourReferenceMeasure, z ∈ Gamma := by
  rw [q11ContourReferenceMeasure]
  apply (ae_map_iff ConfigContourMeasure.continuous_ellipse.aemeasurable
    TubeInterior.measurable_Gamma).2
  filter_upwards [] with u
  have hg : Li2Lean.P0.gammaPoint u ∈ Gamma := ⟨u, rfl⟩
  have hb : Config.baseEllipse u ∈ Gamma := by
    rw [← TubeEnergy.gammaPoint_eq_baseEllipse]
    exact hg
  change Config.baseEllipse u ∈ Gamma
  exact hb

private theorem q11_log_norm_integrable_of_bounds
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

theorem q11PinnedComplexPotential_weighted_le_log111 :
    q11PinnedComplexPotential (Complex.ofReal (-(81 / 10 : ℝ))) ≤
      ((pinnedMassUnits.sum : ℝ) / (denominator : ℝ)) * Real.log (111 / 10) := by
  letI : IsFiniteMeasure q11PinnedReferenceMeasure := ⟨by
    rw [q11PinnedReferenceMeasure_mass]
    exact ENNReal.ofReal_lt_top⟩
  have hInt : Integrable
      (fun x : ℝ => Real.log ‖Complex.ofReal (-(81 / 10 : ℝ)) - (x : ℂ)‖)
      q11PinnedReferenceMeasure := by
    have h := integrable_log_q11IntervalReferenceMeasure
      q11PinnedEdgeReal (fun j => q11PinnedEdgeReal (j + 1)) 8
      pinnedMassUnits (1 / 8 : ℝ) (by
        intro j hj
        linarith [q11PinnedEdgeReal_width (Finset.mem_range.mp hj)])
      (-(81 / 10 : ℝ))
    unfold q11PinnedReferenceMeasure
    have hfun :
        (fun x : ℝ => Real.log ‖Complex.ofReal (-(81 / 10 : ℝ)) - (x : ℂ)‖) =
          (fun x : ℝ => Real.log |-(81 / 10 : ℝ) - x|) := by
      funext x
      have heq : Complex.ofReal (-(81 / 10 : ℝ)) - (x : ℂ) =
          Complex.ofReal (-(81 / 10 : ℝ) - x) := by
        push_cast
        congr 1 <;> ring
      rw [heq, Complex.norm_real, Real.norm_eq_abs]
    rw [hfun]
    exact h
  have hbound : ∀ᵐ x : ℝ ∂q11PinnedReferenceMeasure,
      Real.log ‖Complex.ofReal (-(81 / 10 : ℝ)) - (x : ℂ)‖ ≤
        Real.log (111 / 10) := by
    filter_upwards [q11PinnedReferenceMeasure_ae_interval] with x hx
    have heq : Complex.ofReal (-(81 / 10 : ℝ)) - (x : ℂ) =
        Complex.ofReal (-(81 / 10 + x)) := by
      push_cast
      congr 1 <;> ring
    have hpos : 0 < (81 / 10 : ℝ) + x := by
      nlinarith [hx.1]
    rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_neg,
      abs_of_pos hpos]
    apply Real.log_le_log
    · exact hpos
    · linarith [hx.2]
  have hmono := integral_mono_ae hInt
    (integrable_const (μ := q11PinnedReferenceMeasure) (Real.log (111 / 10))) hbound
  change (∫ x, Real.log ‖Complex.ofReal (-(81 / 10 : ℝ)) - (x : ℂ)‖
      ∂q11PinnedReferenceMeasure) ≤ _ at hmono
  calc
    q11PinnedComplexPotential (Complex.ofReal (-(81 / 10 : ℝ))) = _ := rfl
    _ ≤ ∫ _ : ℝ, Real.log (111 / 10) ∂q11PinnedReferenceMeasure := hmono
    _ ≤ ((pinnedMassUnits.sum : ℝ) / (denominator : ℝ)) * Real.log (111 / 10) := by
      rw [integral_const, Measure.real, q11PinnedReferenceMeasure_mass]
      have hp : (0 : ℝ) ≤ (pinnedMassUnits.sum : ℝ) / (denominator : ℝ) := by positivity
      simp only [ENNReal.toReal_ofReal hp, smul_eq_mul]
      exact le_rfl
  
theorem q11PinnedComplexPotential_le_log111 :
    q11PinnedComplexPotential (Complex.ofReal (-(81 / 10 : ℝ))) ≤
      Real.log (111 / 10) := by
  have hw := q11PinnedComplexPotential_weighted_le_log111
  have hm : (pinnedMassUnits.sum : ℝ) / (denominator : ℝ) ≤ 1 := by
    rw [pinned_mass_sum]
    norm_num [denominator]
  have hl : (0 : ℝ) ≤ Real.log (111 / 10) :=
    Real.log_nonneg (by norm_num)
  nlinarith

theorem q11ContourPotential_weighted_le_log111 :
    q11ContourPotential (Complex.ofReal (-(81 / 10 : ℝ))) ≤
      ((2 * contourPairMassUnits.sum : ℝ) / (denominator : ℝ)) *
        Real.log (111 / 10) := by
  let z : ℂ := Complex.ofReal (-(81 / 10 : ℝ))
  have hbound : ∀ᵐ w ∂q11ContourReferenceMeasure,
      (1749 / 5000 : ℝ) ≤ ‖z - w‖ ∧ ‖z - w‖ ≤ (111 / 10 : ℝ) := by
    filter_upwards [q11ContourReferenceMeasure_ae_Gamma] with w hw
    constructor
    · simpa [norm_sub_rev] using
        (TubeEnergy.frequency_source_norm_sub_ge (x := z)
          (by dsimp [z]; norm_num) hw)
    · calc
        ‖z - w‖ ≤ ‖z‖ + ‖w‖ := norm_sub_le _ _
        _ ≤ (111 / 10 : ℝ) := by
          have hw' := Li2Lean.P0.norm_le_three_of_mem_Gamma hw
          have hz : ‖z‖ = (81 / 10 : ℝ) := by
            dsimp [z]
            norm_num [Complex.norm_real, Real.norm_eq_abs]
          rw [hz]
          linarith
  have hInt : Integrable (fun w : ℂ => Real.log ‖z - w‖)
      q11ContourReferenceMeasure := by
    apply q11_log_norm_integrable_of_bounds
      (by fun_prop : Measurable (fun w : ℂ => z - w)) (by norm_num) hbound
  letI : IsFiniteMeasure q11ContourReferenceMeasure := q11ContourReferenceMeasure_isFinite
  have hmono := integral_mono_ae hInt
    (integrable_const (μ := q11ContourReferenceMeasure) (Real.log (111 / 10)))
    (hbound.mono fun w hw => by
      exact Real.log_le_log (lt_of_lt_of_le (by norm_num) hw.1) hw.2)
  have hpot : q11ContourPotential z =
      ∫ w, Real.log ‖z - w‖ ∂q11ContourReferenceMeasure :=
    q11ContourPotential_eq_integral z
  rw [hpot]
  calc
    _ ≤ ∫ _ : ℂ, Real.log (111 / 10) ∂q11ContourReferenceMeasure := hmono
    _ ≤ ((2 * contourPairMassUnits.sum : ℝ) / (denominator : ℝ)) *
        Real.log (111 / 10) := by
      rw [integral_const, Measure.real, q11ContourReferenceMeasure_univ]
      have hp : (0 : ℝ) ≤ (2 * contourPairMassUnits.sum : ℝ) /
          (denominator : ℝ) := by positivity
      simp only [ENNReal.toReal_ofReal hp, smul_eq_mul]
      exact le_rfl

theorem q11ContourPotential_le_log111 :
    q11ContourPotential (Complex.ofReal (-(81 / 10 : ℝ))) ≤
      Real.log (111 / 10) := by
  have hw := q11ContourPotential_weighted_le_log111
  have hm : (2 * contourPairMassUnits.sum : ℝ) /
      (denominator : ℝ) ≤ 1 := by
    rw [contour_pair_mass_sum]
    norm_num [denominator]
  have hl : (0 : ℝ) ≤ Real.log (111 / 10) :=
    Real.log_nonneg (by norm_num)
  nlinarith

theorem q11EtaReferencePotential_le_log111 :
    q11EtaReferencePotential (Complex.ofReal (-(81 / 10 : ℝ))) ≤
      Real.log (111 / 10) := by
  unfold q11EtaReferencePotential
  have hp := q11PinnedComplexPotential_weighted_le_log111
  have hc := q11ContourPotential_weighted_le_log111
  have hsum : (pinnedMassUnits.sum : ℝ) / (denominator : ℝ) +
      (2 * contourPairMassUnits.sum : ℝ) / (denominator : ℝ) = 1 := by
    norm_num [pinned_mass_sum, contour_pair_mass_sum, denominator]
  have hp0 : (0 : ℝ) ≤ (pinnedMassUnits.sum : ℝ) / (denominator : ℝ) := by positivity
  have hc0 : (0 : ℝ) ≤ (2 * contourPairMassUnits.sum : ℝ) /
      (denominator : ℝ) := by positivity
  have hlog : 0 ≤ Real.log (111 / 10) := Real.log_nonneg (by norm_num)
  nlinarith [hp, hc, hsum, hp0, hc0, hlog]

theorem q11Wmu_endpoint_coarse_bound :
    3 * Real.log (81 / 10) + (81 / 10) * Real.log (11 / 2)
      - 2 * Real.log (38 / 5) - Real.log (111 / 10)
      ≤ q11Wmu (81 / 10) := by
  rw [q11Wmu_eq_tail_parts]
  have hb : 3 * Real.log (81 / 10) + (81 / 10) * q11Lambda ≤
      q11BaseTail (81 / 10) := by
    have htpos : (0 : ℝ) < 81 / 10 := by norm_num
    have hhalf : (1 / 2 : ℝ) ≤ 81 / 10 := by norm_num
    exact q11BaseTail_ge_coarse (by norm_num)
  have hf := q11FrequencyPotential_le_log38
  have he := q11EtaReferencePotential_le_log111
  unfold q11EtaReferencePotential at he
  have hpn : q11PinnedNegativePotential (81 / 10) =
      q11PinnedComplexPotential (Complex.ofReal (-(81 / 10 : ℝ))) := by
    symm
    exact q11PinnedComplexPotential_negative _
  rw [hpn]
  have harg : (-(81 / 10 : ℂ)) = -((81 / 10 : ℝ) : ℂ) := by norm_num
  have he' : q11PinnedComplexPotential (Complex.ofReal (-(81 / 10 : ℝ))) +
      q11ContourPotential (-(81 / 10 : ℂ)) ≤ Real.log (111 / 10) := by
    rw [harg]
    simpa using he
  rw [harg] at he'
  simp [q11Lambda] at hb
  have hf' : 2 * q11FrequencyPotential (81 / 10) ≤
      2 * Real.log (38 / 5) := by
    nlinarith [hf]
  have hb' : 3 * Real.log (81 / 10) + (81 / 10) * Real.log (11 / 2) ≤
      q11BaseTail (81 / 10) := hb
  nlinarith [hb', hf', he']

/-! The scalar certificate and the actual-measure estimate meet at the
endpoint. Keeping these as separate declarations exposes the continuous
producer to downstream interpolation code. -/
theorem q11Wmu_endpoint_gt :
    (56 / 5 : ℝ) < q11Wmu (81 / 10) := by
  exact lt_of_lt_of_le q11_endpoint_coarse_log_lower_v2
    q11Wmu_endpoint_coarse_bound

theorem q11Wmu_tail_floor {t : ℝ} (ht : (81 / 10 : ℝ) ≤ t) :
    (56 / 5 : ℝ) < q11Wmu t := by
  exact lt_of_lt_of_le q11Wmu_endpoint_gt (q11Wmu_endpoint_le_tail ht)

end

end Li2Lean.P0.Q11Data
