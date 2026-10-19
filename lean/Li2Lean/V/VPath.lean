/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/

import Mathlib
import Li2Lean.P0.TubeCircleMeasure

/-!
The four geometric pieces of the v13 contour `Gamma_q`, parameterized on
`[0,1]`.  This is only the path geometry from `v-analytic.tex:85-104`;
the complex coefficients of the two arcs and the Laurent-moment identity
remain separate obligations.

The circle parameterization is reused from the frozen Li2(1/2) release via
`P0.circlePoint` and `ContourKit.p0CirclePoint_eq_circleMap`.
-/

namespace Li2Lean.V

noncomputable section

open Set

def vContourRadius : ℝ := 3 / 5

/-- The oriented segment `[-q,-3/5]`, rescaled to the unit parameter interval. -/
def vNegativeSegment (q : ℕ) (t : ℝ) : ℂ :=
  Complex.ofReal (-(q : ℝ) + ((q : ℝ) - vContourRadius) * t)

/-- The oriented segment `[3/5,1]`, rescaled to the unit parameter interval. -/
def vPositiveSegment (t : ℝ) : ℂ :=
  Complex.ofReal (vContourRadius + (1 - vContourRadius) * t)

/-- The upper half-circle `gamma_+`, with its v13 orientation. -/
def vUpperArc (t : ℝ) : ℂ :=
  P0.circlePoint 0 vContourRadius (Real.pi * t)

/-- The lower half-circle `gamma_-`, with its v13 orientation. -/
def vLowerArc (t : ℝ) : ℂ :=
  P0.circlePoint 0 vContourRadius (Real.pi + Real.pi * t)

theorem continuous_vNegativeSegment (q : ℕ) : Continuous (vNegativeSegment q) := by
  unfold vNegativeSegment
  fun_prop

theorem continuous_vPositiveSegment : Continuous vPositiveSegment := by
  unfold vPositiveSegment
  fun_prop

theorem continuous_vUpperArc : Continuous vUpperArc := by
  unfold vUpperArc
  exact (P0.continuous_circlePoint 0 vContourRadius).comp
    (continuous_const.mul continuous_id)

theorem continuous_vLowerArc : Continuous vLowerArc := by
  unfold vLowerArc
  exact (P0.continuous_circlePoint 0 vContourRadius).comp
    (continuous_const.add (continuous_const.mul continuous_id))

theorem vNegativeSegment_ne_zero {q : ℕ} (hq : 2 ≤ q)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : vNegativeSegment q t ≠ 0 := by
  unfold vNegativeSegment
  apply Complex.ofReal_ne_zero.mpr
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hrad : 0 ≤ (q : ℝ) - vContourRadius := by
    norm_num [vContourRadius]
    linarith
  have hmove : 0 ≤ ((q : ℝ) - vContourRadius) * (1 - t) :=
    mul_nonneg hrad (sub_nonneg.mpr ht.2)
  have hbound : -(q : ℝ) + ((q : ℝ) - vContourRadius) * t ≤ -vContourRadius := by
    dsimp [vContourRadius] at *
    nlinarith
  have hradius : 0 < vContourRadius := by norm_num [vContourRadius]
  linarith

theorem vPositiveSegment_ne_zero {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : vPositiveSegment t ≠ 0 := by
  unfold vPositiveSegment
  apply Complex.ofReal_ne_zero.mpr
  have hradius : 0 < vContourRadius := by norm_num [vContourRadius]
  have hmove : 0 ≤ (1 - vContourRadius) * t :=
    mul_nonneg (by norm_num [vContourRadius]) ht.1
  linarith

theorem vUpperArc_ne_zero {t : ℝ} : vUpperArc t ≠ 0 := by
  change P0.circlePoint 0 vContourRadius (Real.pi * t) ≠ 0
  rw [ContourKit.p0CirclePoint_eq_circleMap]
  have hradius : 0 < vContourRadius := by norm_num [vContourRadius]
  have hmem : circleMap 0 vContourRadius (Real.pi * t) ∈
      Metric.sphere 0 vContourRadius := circleMap_mem_sphere 0 hradius.le _
  have hnorm : ‖circleMap 0 vContourRadius (Real.pi * t)‖ = vContourRadius := by
    simpa [Metric.mem_sphere, dist_zero_right] using hmem
  intro hz
  rw [hz] at hnorm
  norm_num [vContourRadius] at hnorm

theorem vLowerArc_ne_zero {t : ℝ} : vLowerArc t ≠ 0 := by
  change P0.circlePoint 0 vContourRadius (Real.pi + Real.pi * t) ≠ 0
  rw [ContourKit.p0CirclePoint_eq_circleMap]
  have hradius : 0 < vContourRadius := by norm_num [vContourRadius]
  have hmem : circleMap 0 vContourRadius (Real.pi + Real.pi * t) ∈
      Metric.sphere 0 vContourRadius := circleMap_mem_sphere 0 hradius.le _
  have hnorm : ‖circleMap 0 vContourRadius (Real.pi + Real.pi * t)‖ = vContourRadius := by
    simpa [Metric.mem_sphere, dist_zero_right] using hmem
  intro hz
  rw [hz] at hnorm
  norm_num [vContourRadius] at hnorm

/-- The geometric trace of the four v13 contour pieces, without their
complex path-integral coefficients. -/
def vContourTrace (q : ℕ) : Set ℂ :=
  (vNegativeSegment q '' Set.Icc (0 : ℝ) 1) ∪
    ((vPositiveSegment '' Set.Icc (0 : ℝ) 1) ∪
      ((vUpperArc '' Set.Icc (0 : ℝ) 1) ∪
        (vLowerArc '' Set.Icc (0 : ℝ) 1)))

theorem vContourTrace_ne_zero {q : ℕ} (hq : 2 ≤ q) {z : ℂ}
    (hz : z ∈ vContourTrace q) : z ≠ 0 := by
  simp only [vContourTrace, Set.mem_union, Set.mem_image] at hz
  rcases hz with hn | hp
  · rcases hn with ⟨t, ht, hzt⟩
    rw [← hzt]
    exact vNegativeSegment_ne_zero hq ht
  · rcases hp with hv | hp
    · rcases hv with ⟨t, ht, hzt⟩
      rw [← hzt]
      exact vPositiveSegment_ne_zero ht
    · rcases hp with hu | hl
      · rcases hu with ⟨t, ht, hzt⟩
        rw [← hzt]
        exact vUpperArc_ne_zero
      · rcases hl with ⟨t, ht, hzt⟩
        rw [← hzt]
        exact vLowerArc_ne_zero

end

end Li2Lean.V

#print axioms Li2Lean.V.vContourTrace_ne_zero
