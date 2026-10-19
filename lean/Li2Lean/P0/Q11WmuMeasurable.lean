/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.Q11Reference

open MeasureTheory

namespace Li2Lean.P0.Q11Data

noncomputable section

private instance q11PinnedReferenceMeasure_isFinite :
    IsFiniteMeasure q11PinnedReferenceMeasure := by
  refine ⟨?_⟩
  rw [q11PinnedReferenceMeasure_mass]
  exact ENNReal.ofReal_lt_top

private instance q11FrequencyReferenceMeasure_isFinite :
    IsFiniteMeasure q11FrequencyReferenceMeasure := by
  refine ⟨?_⟩
  rw [q11FrequencyReferenceMeasure_univ]
  exact ENNReal.one_lt_top

private theorem stronglyMeasurable_intervalIntegral_log_add
    {a b : ℝ} (hab : a ≤ b) :
    StronglyMeasurable
      (fun t : ℝ => ∫ x in a..b, Real.log (t + x)) := by
  have hfun :
      (fun t : ℝ => ∫ x in a..b, Real.log (t + x)) =
        (fun t : ℝ => ∫ x in Set.Ioc a b, Real.log (t + x)) := by
    funext t
    rw [intervalIntegral.integral_of_le hab]
  rw [hfun]
  apply StronglyMeasurable.integral_prod_right
  fun_prop

private theorem stronglyMeasurable_q11B0 :
    StronglyMeasurable Config.B0 := by
  unfold Config.B0
  exact (stronglyMeasurable_intervalIntegral_log_add (by norm_num)).add
    (stronglyMeasurable_intervalIntegral_log_add (by norm_num))

private theorem stronglyMeasurable_q11Psi :
    StronglyMeasurable q11Psi := by
  unfold q11Psi
  have hpsi : Measurable Config.psi := by
    unfold Config.psi
    fun_prop
  have hmul : StronglyMeasurable (fun t : ℝ => q11Lambda * t) :=
    stronglyMeasurable_const.mul continuous_id.stronglyMeasurable
  exact hpsi.stronglyMeasurable.sub hmul

private theorem stronglyMeasurable_q11PinnedComplexPotential :
    StronglyMeasurable q11PinnedComplexPotential := by
  unfold q11PinnedComplexPotential
  apply StronglyMeasurable.integral_prod_right
  fun_prop

private theorem stronglyMeasurable_q11FrequencyPotential :
    StronglyMeasurable q11FrequencyPotential := by
  unfold q11FrequencyPotential
  apply StronglyMeasurable.integral_prod_right
  fun_prop

private theorem stronglyMeasurable_q11ContourPotential :
    StronglyMeasurable q11ContourPotential := by
  have hrepr : q11ContourPotential = fun z : ℂ =>
      ∫ w, Real.log ‖z - w‖ ∂q11ContourReferenceMeasure := by
    funext z
    exact q11ContourPotential_eq_integral z
  rw [hrepr]
  apply StronglyMeasurable.integral_prod_right
  fun_prop

private theorem stronglyMeasurable_q11EtaReferencePotential :
    StronglyMeasurable q11EtaReferencePotential := by
  unfold q11EtaReferencePotential
  exact stronglyMeasurable_q11PinnedComplexPotential.add
    stronglyMeasurable_q11ContourPotential

private theorem stronglyMeasurable_q11EtaPotentialOnNegativeAxis :
    StronglyMeasurable (fun t : ℝ =>
      q11EtaReferencePotential (Complex.ofReal (-t))) := by
  exact stronglyMeasurable_q11EtaReferencePotential.comp_measurable (by fun_prop)

/-- The q=11 dual field is measurable, as needed for the row-to-integrability
reduction; see v13 `p0-analytic.tex`, pp. 199-205 and 748-830. -/
theorem measurable_q11Wmu : Measurable q11Wmu := by
  have hW : StronglyMeasurable q11Wmu := by
    change StronglyMeasurable (fun t : ℝ =>
      Config.B0 t - q11Psi t - 2 * q11FrequencyPotential t -
        q11EtaReferencePotential (Complex.ofReal (-t)))
    have hfreqMul : StronglyMeasurable
        (fun t : ℝ => 2 * q11FrequencyPotential t) :=
      stronglyMeasurable_const.mul stronglyMeasurable_q11FrequencyPotential
    exact (((stronglyMeasurable_q11B0.sub stronglyMeasurable_q11Psi).sub
      hfreqMul).sub stronglyMeasurable_q11EtaPotentialOnNegativeAxis)
  exact hW.measurable

end

end Li2Lean.P0.Q11Data
