/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.Q11EndpointBridge
import Li2Lean.P0.U2NegativeEtaL6Cap

/-!
The negative-axis local positive-kernel cap for the q = 11 reference measure.

This is the support-clearance step in the v13 p0 analytic argument
(`p0-analytic.tex:244-255`), specialized to the printed q = 11 reference
measure.
-/

open MeasureTheory Filter Set
open scoped ENNReal

namespace Li2Lean.P0.Q11Data

noncomputable section

open Li2Lean.P0.L6Variations
open Li2Lean.P0.U2GlobalFejer
open Li2Lean.P0.ConfigContourTail

/-- The q = 11 reference eta has a uniform positive-kernel cap on the
negative half-line, obtained from the v13 support-clearance argument. -/
theorem q11_eta_l6PosKernel_bound_on_negative_axis {x : ℝ}
    (hx : x ≤ -(1 / 2 : ℝ)) :
    (∫⁻ w, l6PosKernel (x : ℂ) w ∂q11EtaReferenceMeasure) ≤
      ENNReal.ofReal (Real.posLog
        U2NegativeEtaL6Cap.negativeEtaClearance⁻¹) := by
  have hclear : 0 < U2NegativeEtaL6Cap.negativeEtaClearance := by
    norm_num [U2NegativeEtaL6Cap.negativeEtaClearance]
  have hdist : ∀ᵐ w ∂q11EtaReferenceMeasure,
      U2NegativeEtaL6Cap.negativeEtaClearance ≤ ‖(x : ℂ) - w‖ := by
    have hset : MeasurableSet {w : ℂ |
        U2NegativeEtaL6Cap.negativeEtaClearance ≤ ‖(x : ℂ) - w‖} := by
      exact (isClosed_le continuous_const
        (continuous_norm.comp (continuous_const.sub continuous_id))).measurableSet
    change ∀ᵐ w ∂(Measure.map Complex.ofReal q11PinnedReferenceMeasure +
      q11ContourReferenceMeasure),
        U2NegativeEtaL6Cap.negativeEtaClearance ≤ ‖(x : ℂ) - w‖
    rw [ae_add_measure_iff]
    constructor
    · rw [ae_map_iff Complex.measurable_ofReal.aemeasurable hset]
      filter_upwards [q11PinnedReferenceMeasure_ae_interval] with t ht
      have hxt : x ≤ t := by linarith [hx, ht.1]
      rw [show ‖(x : ℂ) - (t : ℂ)‖ = |x - t| by
        rw [← Complex.ofReal_sub]
        simp only [Complex.norm_real, Real.norm_eq_abs]]
      rw [abs_of_nonpos (sub_nonpos.mpr hxt)]
      norm_num [U2NegativeEtaL6Cap.negativeEtaClearance]
      linarith [hx, ht.1]
    · filter_upwards [q11ContourReferenceMeasure_ae_Gamma] with w hw
      obtain ⟨u, rfl⟩ := hw
      have htx : (1 / 2 : ℝ) ≤ -x := by linarith
      have h := U2GlobalFejer.negativeAxis_distance_lower htx u
      have hd : U2NegativeEtaL6Cap.negativeEtaClearance ≤
          (-x : ℝ) - leftClearance := by
        norm_num [U2NegativeEtaL6Cap.negativeEtaClearance,
          ConfigContourTail.leftClearance]
        linarith
      have hrewrite : -(((-x : ℝ) : ℂ)) = (x : ℂ) := by
        push_cast
        ring
      rw [hrewrite] at h
      change -x - leftClearance ≤
        ‖(x : ℂ) - Config.baseEllipse u‖ at h
      rw [← TubeEnergy.gammaPoint_eq_baseEllipse u] at h
      exact hd.trans h
  have hpoint : ∀ᵐ w ∂q11EtaReferenceMeasure,
      l6PosKernel (x : ℂ) w ≤
        ENNReal.ofReal (Real.posLog
          U2NegativeEtaL6Cap.negativeEtaClearance⁻¹) := by
    filter_upwards [hdist] with w hw
    have hne : (x : ℂ) ≠ w := by
      intro hEq
      subst w
      norm_num [U2NegativeEtaL6Cap.negativeEtaClearance] at hw
    simp only [l6PosKernel, hne, ↓reduceIte]
    apply ENNReal.ofReal_le_ofReal
    apply Real.posLog_le_posLog
    · exact le_trans (by norm_num) (inv_nonneg.mpr (norm_nonneg _))
    · have hn : ‖(x : ℂ) - w‖ ≠ 0 :=
        norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne)
      simpa [one_div] using
        (one_div_le_one_div_of_le hclear hw)
  calc
    (∫⁻ w, l6PosKernel (x : ℂ) w ∂q11EtaReferenceMeasure) ≤
        ∫⁻ _w : ℂ,
          ENNReal.ofReal (Real.posLog
            U2NegativeEtaL6Cap.negativeEtaClearance⁻¹)
          ∂q11EtaReferenceMeasure := lintegral_mono_ae hpoint
    _ = ENNReal.ofReal (Real.posLog
          U2NegativeEtaL6Cap.negativeEtaClearance⁻¹) *
          q11EtaReferenceMeasure Set.univ := by rw [lintegral_const]
    _ = ENNReal.ofReal (Real.posLog
          U2NegativeEtaL6Cap.negativeEtaClearance⁻¹) := by
      rw [q11EtaReferenceMeasure_univ]
      simp

end

end Li2Lean.P0.Q11Data

#print axioms Li2Lean.P0.Q11Data.q11_eta_l6PosKernel_bound_on_negative_axis
