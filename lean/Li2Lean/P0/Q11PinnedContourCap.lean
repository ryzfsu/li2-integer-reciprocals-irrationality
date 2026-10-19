/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.Q11Reference
import Li2Lean.P0.MixedCellClearanceFull
import Li2Lean.P0.ConfigWitnessFiniteEnergy

open MeasureTheory
open scoped ENNReal
open Li2Lean.P0.Q11Data

namespace Li2Lean.P0

noncomputable section

/-! This is the pinned-to-contour clearance estimate in v13
`p0-analytic.tex:244-255`, specialized to the q11 contour measure. -/
theorem q11_pinnedContour_l6PosKernel_bound {x : ℝ}
    (hx : x ∈ Set.Icc (1 / 4 : ℝ) (5 / 4)) :
    (∫⁻ w, L6Variations.l6PosKernel (x : ℂ) w ∂q11ContourReferenceMeasure) ≤
      ENNReal.ofReal (Real.posLog (751 / 5000 : ℝ)⁻¹) *
        q11ContourReferenceMeasure Set.univ := by
  have hx02 : x ∈ Set.Icc (0 : ℝ) 2 :=
    ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hsupport : Measure.support q11ContourReferenceMeasure ⊆ Gamma := by
    apply Measure.support_subset_of_isClosed TubeInterior.isCompact_Gamma.isClosed
    have hzero : q11ContourReferenceMeasure Gammaᶜ = 0 := by
      rw [Q11Data.q11ContourReferenceMeasure,
        Measure.map_apply ConfigContourMeasure.continuous_ellipse.measurable
          (TubeInterior.isCompact_Gamma.isClosed.measurableSet.compl)]
      have hpre : Li2Lean.p0EllipsePoint 1 ⁻¹' Gammaᶜ = (∅ : Set ℝ) := by
        ext u
        simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_range]
        constructor
        · intro h
          exact (h ⟨u, (ellipsePoint_one_eq_gammaPoint u).symm⟩).elim
        · intro h
          exact h.elim
      rw [hpre]
      simp
    exact hzero
  have hpoint : ∀ᵐ w ∂q11ContourReferenceMeasure,
      L6Variations.l6PosKernel (x : ℂ) w ≤
        ENNReal.ofReal (Real.posLog (751 / 5000 : ℝ)⁻¹) := by
    filter_upwards [Measure.support_mem_ae (μ := q11ContourReferenceMeasure)] with w hw
    rcases hsupport hw with ⟨u, rfl⟩
    have hbase : Config.baseEllipse u = Li2Lean.P0.gammaPoint u := by
      simpa [Config.baseEllipse, Li2Lean.P0.ellipsePoint] using
        (ellipsePoint_one_eq_gammaPoint u)
    rw [← hbase]
    have hclear := Config.s2_mixed_left_candidate
      (Config.baseEllipse u) ⟨u, rfl⟩ x hx02
    have hdist : (751 / 5000 : ℝ) ≤
        ‖(x : ℂ) - Config.baseEllipse u‖ := by
      rw [norm_sub_rev]
      simpa [Config.dPlus] using hclear
    have hne : (x : ℂ) ≠ Config.baseEllipse u := by
      intro heq
      have hzero : ‖(x : ℂ) - Config.baseEllipse u‖ = 0 := by rw [heq]; simp
      have : (751 / 5000 : ℝ) ≤ 0 := by simpa [hzero] using hdist
      norm_num at this
    simp only [L6Variations.l6PosKernel, ne_of_ne_of_eq hne rfl, ↓reduceIte]
    have hinv : ‖(x : ℂ) - Config.baseEllipse u‖⁻¹ ≤ (751 / 5000 : ℝ)⁻¹ := by
      simpa [one_div] using one_div_le_one_div_of_le (by norm_num) hdist
    have hpos : Real.posLog ‖(x : ℂ) - Config.baseEllipse u‖⁻¹ ≤
        Real.posLog (751 / 5000 : ℝ)⁻¹ :=
      Real.posLog_le_posLog
        (le_trans (by norm_num) (inv_nonneg.mpr (norm_nonneg _))) hinv
    exact ENNReal.ofReal_le_ofReal hpos
  calc
    (∫⁻ w, L6Variations.l6PosKernel (x : ℂ) w ∂q11ContourReferenceMeasure) ≤
        ∫⁻ _w : ℂ,
          ENNReal.ofReal (Real.posLog (751 / 5000 : ℝ)⁻¹) ∂q11ContourReferenceMeasure :=
      lintegral_mono_ae hpoint
    _ = ENNReal.ofReal (Real.posLog (751 / 5000 : ℝ)⁻¹) *
        q11ContourReferenceMeasure Set.univ := by rw [lintegral_const]

end
end Li2Lean.P0

#print axioms Li2Lean.P0.q11_pinnedContour_l6PosKernel_bound
