/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Mathlib
import Li2Lean.B3.ProducerInterfaces

namespace Li2Lean.B3

open MeasureTheory Set

/-- Closed-ball form of the v13 linear ball bound, obtained by radius
enlargement and an epsilon limit (`v-analytic.tex:425-434`). -/
theorem vBallBound_closedBall
    {μ : Measure ℂ} [IsFiniteMeasure μ] {A : ℝ}
    (hball : VBallBound μ A) (w : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    μ.real (Metric.closedBall w r) ≤ A * r := by
  have hle : ∀ ε : ℝ, 0 < ε →
      μ.real (Metric.closedBall w r) ≤ A * (r + ε) := by
    intro ε hε
    have hsub : Metric.closedBall w r ⊆ Metric.ball w (r + ε) :=
      Metric.closedBall_subset_ball (by linarith)
    exact (measureReal_mono hsub).trans (hball w (r + ε) (by linarith))
  have hA : 0 ≤ A := by
    have h1 := hball w 1 zero_lt_one
    have h0 : 0 ≤ (μ (Metric.ball w 1)).toReal := ENNReal.toReal_nonneg
    linarith
  by_contra! hlt
  rcases eq_or_lt_of_le hA with rfl | hApos
  · have h0 := hle 1 zero_lt_one
    linarith
  · have hε : 0 < (μ.real (Metric.closedBall w r) - A * r) / (2 * A) :=
      div_pos (by linarith) (by linarith)
    have h2 := hle _ hε
    have hcancel : A * ((μ.real (Metric.closedBall w r) - A * r) / (2 * A)) =
        (μ.real (Metric.closedBall w r) - A * r) / 2 := by
      field_simp [hApos.ne']
    linarith

end Li2Lean.B3

#print axioms Li2Lean.B3.vBallBound_closedBall
