/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Mathlib
import Li2Lean.B3.SignedSmoothing
import Li2Lean.V.VPath

/-!
The negative one-body estimate from v13 `v-analytic.tex:572-590`.

This is kept as a small geometric lemma: points of the four contour pieces
have norm at least `3/5`, and the translated smoothing circle is within
`3 * smoothingEpsilon m` of its centre.  The logarithmic Lipschitz estimate
then gives the constant `7` used by the C7 budget.
-/

namespace Li2Lean.B3

noncomputable section

open Set

theorem c7_negative_z_one_body_bound
    {q m : ℕ} (hq : 2 ≤ q) (hm : 64 ≤ m)
    {z : ℂ} (hz : z ∈ V.vContourTrace q) (theta : ℝ) :
    -(5 / 4 : ℝ) * Real.log ‖z‖ ≤
      -(5 / 4 : ℝ) * Real.log ‖translatedAtom z m theta‖ +
        7 * smoothingEpsilon m := by
  have hmpos : 0 < m := by omega
  have heps : 0 ≤ smoothingEpsilon m := (smoothingEpsilon_pos hmpos).le
  have heps4096 : smoothingEpsilon m ≤ (1 / 4096 : ℝ) :=
    smoothingEpsilon_le_one_div_4096 hm
  have hz_norm : V.vContourRadius ≤ ‖z‖ := by
    simp only [V.vContourTrace, Set.mem_union, Set.mem_image] at hz
    rcases hz with hneg | hrest
    · rcases hneg with ⟨t, ht, hzt⟩
      rw [← hzt]
      unfold V.vNegativeSegment
      rw [Complex.norm_real, Real.norm_eq_abs]
      have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
      have hrad : 0 ≤ (q : ℝ) - V.vContourRadius := by
        norm_num [V.vContourRadius]
        linarith
      have hle :
          -(q : ℝ) + ((q : ℝ) - V.vContourRadius) * t ≤
            -V.vContourRadius := by
        have hmul : 0 ≤ ((q : ℝ) - V.vContourRadius) * (1 - t) :=
          mul_nonneg hrad (sub_nonneg.mpr ht.2)
        dsimp [V.vContourRadius] at *
        nlinarith
      have hle0 :
          -(q : ℝ) + ((q : ℝ) - V.vContourRadius) * t ≤ 0 := by
        have hr : 0 ≤ V.vContourRadius := by
          norm_num [V.vContourRadius]
        linarith
      rw [abs_of_nonpos hle0]
      linarith
    · rcases hrest with hpos | harcs
      · rcases hpos with ⟨t, ht, hzt⟩
        rw [← hzt]
        unfold V.vPositiveSegment
        rw [Complex.norm_real, Real.norm_eq_abs]
        have hle : 0 ≤ V.vContourRadius +
            (1 - V.vContourRadius) * t := by
          have hrad : 0 ≤ V.vContourRadius := by
            norm_num [V.vContourRadius]
          have hcoef : 0 ≤ 1 - V.vContourRadius := by
            norm_num [V.vContourRadius]
          exact add_nonneg hrad (mul_nonneg hcoef ht.1)
        rw [abs_of_nonneg hle]
        have hrad : (0 : ℝ) ≤ V.vContourRadius := by
          norm_num [V.vContourRadius]
        have hcoef : 0 ≤ 1 - V.vContourRadius := by
          norm_num [V.vContourRadius]
        nlinarith [ht.1]
      · rcases harcs with hu | hl
        · rcases hu with ⟨t, ht, hzt⟩
          rw [← hzt]
          unfold V.vUpperArc
          rw [ContourKit.p0CirclePoint_eq_circleMap]
          have hradius : 0 < V.vContourRadius := by
            norm_num [V.vContourRadius]
          have hmem :
              circleMap 0 V.vContourRadius (Real.pi * t) ∈
                Metric.sphere 0 V.vContourRadius :=
            circleMap_mem_sphere 0 hradius.le _
          have hrnonneg : (0 : ℝ) ≤ V.vContourRadius := by
            norm_num [V.vContourRadius]
          simpa [Metric.mem_sphere, dist_zero_right,
            abs_of_nonneg hrnonneg] using hmem
        · rcases hl with ⟨t, ht, hzt⟩
          rw [← hzt]
          unfold V.vLowerArc
          rw [ContourKit.p0CirclePoint_eq_circleMap]
          have hradius : 0 < V.vContourRadius := by
            norm_num [V.vContourRadius]
          have hmem :
              circleMap 0 V.vContourRadius (Real.pi + Real.pi * t) ∈
                Metric.sphere 0 V.vContourRadius :=
            circleMap_mem_sphere 0 hradius.le _
          have hrnonneg : (0 : ℝ) ≤ V.vContourRadius := by
            norm_num [V.vContourRadius]
          simpa [Metric.mem_sphere, dist_zero_right,
            abs_of_nonneg hrnonneg] using hmem
  let c : ℝ := V.vContourRadius - 3 * smoothingEpsilon m
  have hc : 0 < c := by
    dsimp [c]
    norm_num [V.vContourRadius]
    nlinarith
  have hcenter :
      c ≤ ‖translatedAtom z m theta‖ := by
    have hdist := translatedAtom_dist_le_threeEpsilon z m theta hmpos
    have htri : ‖z‖ ≤ ‖z - translatedAtom z m theta‖ +
        ‖translatedAtom z m theta‖ := by
      calc
        ‖z‖ = ‖(z - translatedAtom z m theta) +
            translatedAtom z m theta‖ := by congr 1 <;> ring
        _ ≤ ‖z - translatedAtom z m theta‖ +
            ‖translatedAtom z m theta‖ := norm_add_le _ _
    have hdist' : ‖z - translatedAtom z m theta‖ ≤
        3 * smoothingEpsilon m := by
      simpa [norm_sub_rev] using hdist
    dsimp [c]
    linarith
  have hz_c : c ≤ ‖z‖ := by
    dsimp [c]
    linarith [hz_norm]
  have hlog := abs_log_sub_log_le_common_lower hc hcenter hz_c
  have hnormdiff :
      |‖translatedAtom z m theta‖ - ‖z‖| ≤
        3 * smoothingEpsilon m := by
    exact (abs_norm_sub_norm_le _ _).trans
      (translatedAtom_dist_le_threeEpsilon z m theta hmpos)
  have hlog' :
      |Real.log ‖translatedAtom z m theta‖ - Real.log ‖z‖| ≤
        (3 * smoothingEpsilon m) / c := by
    exact hlog.trans (div_le_div_of_nonneg_right hnormdiff hc.le)
  have hratio : (5 / 4 : ℝ) * ((3 * smoothingEpsilon m) / c) ≤
      7 * smoothingEpsilon m := by
    rw [show (5 / 4 : ℝ) * (3 * smoothingEpsilon m / c) =
        ((5 / 4 : ℝ) * (3 * smoothingEpsilon m)) / c by ring]
    apply (div_le_iff₀ hc).2
    have hprod : 0 ≤ smoothingEpsilon m *
        ((1 / 4096 : ℝ) - smoothingEpsilon m) :=
      mul_nonneg heps (sub_nonneg.mpr heps4096)
    dsimp [c]
    norm_num [V.vContourRadius]
    nlinarith
  have hupper : Real.log ‖translatedAtom z m theta‖ -
      Real.log ‖z‖ ≤ (3 * smoothingEpsilon m) / c := by
    exact (le_abs_self _).trans hlog'
  nlinarith

end

end Li2Lean.B3

#print axioms Li2Lean.B3.c7_negative_z_one_body_bound
