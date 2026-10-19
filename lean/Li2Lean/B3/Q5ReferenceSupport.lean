/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B3.Q5ReferencePackageAssembly
import Li2Lean.B3.ReferenceMeasureSupportCircle

namespace Li2Lean.B3

noncomputable section

open MeasureTheory Set
open V.EnergyCertI

/-- F1 support for the concrete q = 5 measure, obtained from the printed
v13 chain endpoints and the generic support theorem. -/
theorem q5ReferenceMeasure_x_support_low
    (N : q5ReferenceNormalizationGoal) :
    (q5ReferenceMeasure N).μx
      (Complex.ofReal '' Icc (vXLow 5) 1)ᶜ = 0 := by
  change v13DecodedChainMeasure q5D.xp
    (Complex.ofReal '' Icc (vXLow 5) 1)ᶜ = 0
  apply v13DecodedChainMeasure_outside_of_cells
  intro c hc
  have h := v13_q5_x_bounds c hc
  norm_num [vXLow] at h ⊢
  exact h

theorem q5ReferenceMeasure_v_support_low
    (N : q5ReferenceNormalizationGoal) :
    (q5ReferenceMeasure N).μv
      (Complex.ofReal '' Icc (vVLow 5) 1)ᶜ = 0 := by
  change v13DecodedChainMeasure q5D.vp
    (Complex.ofReal '' Icc (vVLow 5) 1)ᶜ = 0
  apply v13DecodedChainMeasure_outside_of_cells
  intro c hc
  have h := v13_q5_v_bounds c hc
  norm_num [vVLow] at h ⊢
  exact h

theorem q5ReferenceMeasure_x_support
    (N : q5ReferenceNormalizationGoal) :
    (q5ReferenceMeasure N).μx
      (Complex.ofReal '' Icc (0 : ℝ) 1)ᶜ = 0 := by
  change v13DecodedChainMeasure q5D.xp
    (Complex.ofReal '' Icc (0 : ℝ) 1)ᶜ = 0
  apply v13DecodedChainMeasure_outside_of_cells
  exact v13_q5_x_full_bounds

theorem q5ReferenceMeasure_v_support
    (N : q5ReferenceNormalizationGoal) :
    (q5ReferenceMeasure N).μv
      (Complex.ofReal '' Icc (0 : ℝ) 1)ᶜ = 0 := by
  change v13DecodedChainMeasure q5D.vp
    (Complex.ofReal '' Icc (0 : ℝ) 1)ᶜ = 0
  apply v13DecodedChainMeasure_outside_of_cells
  exact v13_q5_v_full_bounds

theorem q5ReferenceMeasure_z_support_source
    (N : q5ReferenceNormalizationGoal) :
    (q5ReferenceMeasure N).μz
      ((Complex.ofReal '' Icc (-(5 : ℝ)) (-3 / 5)) ∪
        Metric.sphere 0 (3 / 5))ᶜ = 0 := by
  change (v13DecodedChainMeasure q5D.zp + v13PoissonMeasure q5D.full)
    ((Complex.ofReal '' Icc (-(5 : ℝ)) (-3 / 5)) ∪
      Metric.sphere 0 (3 / 5))ᶜ = 0
  have hchain : v13DecodedChainMeasure q5D.zp
      ((Complex.ofReal '' Icc (-(5 : ℝ)) (-3 / 5)) ∪
        Metric.sphere 0 (3 / 5))ᶜ = 0 := by
    apply measure_mono_null
      (t := (Complex.ofReal '' Icc (-(5 : ℝ)) (-3 / 5))ᶜ)
    · intro z hz
      change z ∉ (Complex.ofReal '' Icc (-(5 : ℝ)) (-3 / 5))
      intro hzInterval
      exact hz (Or.inl hzInterval)
    · exact v13DecodedChainMeasure_outside_of_cells q5D.zp (-5) (-3 / 5)
        (by
          intro c hc
          have h := v13_q5_z_source_bounds c hc
          norm_num at h ⊢
          exact h)
  have hpoisson : v13PoissonMeasure q5D.full
      ((Complex.ofReal '' Icc (-(5 : ℝ)) (-3 / 5)) ∪
        Metric.sphere 0 (3 / 5))ᶜ = 0 := by
    apply measure_mono_null
      (t := (Metric.sphere 0 v13GlobalPoissonRadius)ᶜ)
    · intro z hz
      change z ∉ Metric.sphere 0 v13GlobalPoissonRadius
      intro hzSphere
      exact hz (Or.inr (by simpa [v13GlobalPoissonRadius] using hzSphere))
    · exact v13GlobalPoissonMeasure_outside_sphere q5D.full
  rw [Measure.add_apply, hchain, hpoisson, zero_add]

theorem q5ReferenceMeasure_z_support
    (N : q5ReferenceNormalizationGoal) :
    (q5ReferenceMeasure N).μz (V.vContourTrace 5)ᶜ = 0 := by
  apply measure_mono_null (t :=
    ((Complex.ofReal '' Icc (-(5 : ℝ)) (-3 / 5)) ∪
      Metric.sphere 0 (3 / 5))ᶜ)
  · intro z hzTrace
    change z ∉ V.vContourTrace 5 at hzTrace
    change z ∉ ((Complex.ofReal '' Icc (-(5 : ℝ)) (-3 / 5)) ∪
      Metric.sphere 0 (3 / 5))
    intro hzSource
    exact hzTrace (v13_source_subset_trace q5ReferenceBaseRange.1 hzSource)
  · exact q5ReferenceMeasure_z_support_source N

end

end Li2Lean.B3

#print axioms Li2Lean.B3.q5ReferenceMeasure_z_support
