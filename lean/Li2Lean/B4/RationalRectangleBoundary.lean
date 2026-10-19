/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B4.RationalHeightApprox

namespace Li2Lean.B4

/-- The bounded boundary of the v13 rectangle at a rational height. -/
def hpRationalRectangleBoundary (n : ℕ) (b : ℚ) (w : ℂ) : Prop :=
  ((-1 / 2 : ℝ) ≤ w.re ∧ w.re ≤ (n : ℝ) + 1 / 2) ∧
    (-((n : ℝ) * (b : ℝ)) ≤ w.im ∧
      w.im ≤ (n : ℝ) * (b : ℝ)) ∧
    hpSaddleRectSide n (b : ℝ) w

/-- Pole clearance transfers to the bounded rectangle boundary; the side-line
lemma in `CubicSaddle` proves the stronger statement on all supporting lines. -/
theorem hp_rational_rectangle_boundary_pole_clearance
    (q : ℝ) (hq : 1 < q) (n k : ℕ)
    (hkn : k ≤ n)
    (hheight : 1 / 2 ≤ (n : ℝ) *
      (hpSaddleRationalHeight q hq : ℝ))
    {w : ℂ} (hw : hpRationalRectangleBoundary n
      (hpSaddleRationalHeight q hq) w) :
    1 / 2 ≤ ‖(k : ℂ) - w‖ := by
  exact hp_saddle_pole_clearance_half n k
    (hpSaddleRationalHeight q hq : ℝ) hkn hheight hw.2.2

/-- Numerator-zero clearance transfers to the bounded rectangle boundary. -/
theorem hp_rational_rectangle_boundary_numerator_clearance
    (q : ℝ) (hq : 1 < q) (n j : ℕ)
    (hj₁ : n + 1 ≤ j) (hj₃ : j ≤ 3 * n + 1)
    {w : ℂ} (hw : hpRationalRectangleBoundary n
      (hpSaddleRationalHeight q hq) w) :
    1 / 2 ≤ ‖(j : ℂ) - w‖ := by
  exact hp_saddle_numerator_zero_clearance n j
    (hpSaddleRationalHeight q hq : ℝ) hj₁ hj₃ hw.1

end Li2Lean.B4
