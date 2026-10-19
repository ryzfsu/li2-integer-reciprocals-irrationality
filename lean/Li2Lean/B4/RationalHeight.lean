/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B4.CubicSaddle

namespace Li2Lean.B4

noncomputable section

/-- A rational height strictly below the positive cubic-saddle height.
This is the rational-height replacement for the exact contour height in
`hp-tail.tex:266-279`; the phase estimate remains a separate input. -/
def HpRationalHeight (q : ℝ) (hq : 1 < q) : Type :=
  {b : ℚ // 0 < (b : ℝ) ∧ (b : ℝ) < hpSaddleBeta q hq}

/-- A positive rational height exists by density of `ℚ` in `ℝ`. -/
theorem hp_rational_height_exists (q : ℝ) (hq : 1 < q) :
    Nonempty (HpRationalHeight q hq) := by
  have hβ : 0 < hpSaddleBeta q hq := hp_saddle_beta_pos q hq
  obtain ⟨b, hb0, hbβ⟩ := exists_rat_btwn hβ
  exact ⟨⟨b, hb0, hbβ⟩⟩

/-- The selected rational height used by the rectangle producer. -/
noncomputable def hpSaddleRationalHeight (q : ℝ) (hq : 1 < q) : ℚ :=
  (Classical.choice (hp_rational_height_exists q hq) : HpRationalHeight q hq).1

/-- Positivity and strict sub-saddle specification of the selected height. -/
theorem hp_saddle_rational_height_spec (q : ℝ) (hq : 1 < q) :
    0 < (hpSaddleRationalHeight q hq : ℝ) ∧
      (hpSaddleRationalHeight q hq : ℝ) < hpSaddleBeta q hq := by
  exact (Classical.choice (hp_rational_height_exists q hq) :
    HpRationalHeight q hq).property

/-- For every selected rational height, a sufficiently large rectangle has
height at least `1/2`. -/
theorem hp_saddle_rational_height_eventually (q : ℝ) (hq : 1 < q) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      (1 / 2 : ℝ) ≤ (n : ℝ) * (hpSaddleRationalHeight q hq : ℝ) := by
  have hb : 0 < (hpSaddleRationalHeight q hq : ℝ) :=
    (hp_saddle_rational_height_spec q hq).1
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt ((1 / 2 : ℝ) /
    (hpSaddleRationalHeight q hq : ℝ))
  refine ⟨N₀, ?_⟩
  intro n hn
  have hnR : (N₀ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hhalfN : (1 / 2 : ℝ) < (N₀ : ℝ) *
      (hpSaddleRationalHeight q hq : ℝ) := by
    exact (div_lt_iff₀ hb).mp hN₀
  have hmono : (N₀ : ℝ) * (hpSaddleRationalHeight q hq : ℝ) ≤
      (n : ℝ) * (hpSaddleRationalHeight q hq : ℝ) :=
    mul_le_mul_of_nonneg_right hnR hb.le
  linarith

/-- The rational-height rectangle encloses precisely the integer poles
`0, ..., n` once the height threshold is reached. -/
theorem hp_saddle_rational_rect_integer_poles (q : ℝ) (hq : 1 < q)
    (n k : ℕ) (hn : 1 / 2 ≤ (n : ℝ) *
      (hpSaddleRationalHeight q hq : ℝ)) :
    hpSaddleRectInterior n (hpSaddleRationalHeight q hq : ℝ) (k : ℂ) ↔ k ≤ n := by
  exact hp_saddle_rect_integer_poles n k
    (hpSaddleRationalHeight q hq : ℝ) hn

/-- Every enclosed pole is at least `1/2` from each side of the selected
rational-height rectangle. -/
theorem hp_saddle_rational_pole_clearance_half (q : ℝ) (hq : 1 < q)
    (n k : ℕ) (hkn : k ≤ n)
    (hn : 1 / 2 ≤ (n : ℝ) *
      (hpSaddleRationalHeight q hq : ℝ))
    {w : ℂ} (hw : hpSaddleRectSide n
      (hpSaddleRationalHeight q hq : ℝ) w) :
    1 / 2 ≤ ‖(k : ℂ) - w‖ := by
  exact hp_saddle_pole_clearance_half n k
    (hpSaddleRationalHeight q hq : ℝ) hkn hn hw

/-- Numerator zeros in the v13 range retain the half-unit clearance on the
same rational-height rectangle. -/
theorem hp_saddle_rational_numerator_zero_clearance (q : ℝ) (hq : 1 < q)
    (n j : ℕ) (hj₁ : n + 1 ≤ j) (hj₃ : j ≤ 3 * n + 1)
    {w : ℂ} (hw : -1 / 2 ≤ w.re ∧ w.re ≤ (n : ℝ) + 1 / 2) :
    1 / 2 ≤ ‖(j : ℂ) - w‖ := by
  exact hp_saddle_numerator_zero_clearance n j
    (hpSaddleRationalHeight q hq : ℝ) hj₁ hj₃ hw

end

end Li2Lean.B4
