/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B4.NegativeContourBoundary

open scoped BigOperators

namespace Li2Lean.B4.NegContour

noncomputable section

/-- The three denominator factors in the second derivative of the bottom
phase, with the fixed height `beta' = 1/5`; v13 `hp-tail.tex:343-355`. -/
def hpNegD (a x : ℝ) : ℝ := (x - a) ^ 2 + (1 / 5 : ℝ) ^ 2

/-- The numerator polynomial in the bottom-side concavity identity. -/
def hpNegP (x : ℝ) : ℝ :=
  x ^ 3 - 4 * x ^ 2 + (72 / 25 : ℝ) * x + 4 / 25

theorem hp_neg_concavity_numerator_identity (x : ℝ) :
    3 * (x - 1) * hpNegD 0 x * hpNegD 3 x -
        (x - 3) * hpNegD 0 x * hpNegD 1 x -
        2 * x * hpNegD 1 x * hpNegD 3 x = -6 * hpNegP x := by
  simp [hpNegD, hpNegP]
  ring

theorem hp_neg_p_at_right : hpNegP (61 / 60 : ℝ) = 949 / 216000 := by
  norm_num [hpNegP]

theorem hp_neg_p_at_left : hpNegP (-(1 / 60 : ℝ)) = 23951 / 216000 := by
  norm_num [hpNegP]

/-- The fixed-height polynomial is positive throughout the tangent window.
The proof uses the translated polynomial at `61/60`; the remainder bracket is
bounded below on `0 ≤ t ≤ 31/30` by exact rational arithmetic. -/
theorem hp_neg_p_pos_on_window {x : ℝ}
    (hxlo : -(1 / 60 : ℝ) ≤ x) (hxhi : x ≤ 61 / 60) :
    0 < hpNegP x := by
  let t : ℝ := 61 / 60 - x
  have ht0 : 0 ≤ t := by dsimp [t]; linarith
  have htmax : t ≤ 31 / 30 := by dsimp [t]; linarith
  have htsq : t ^ 2 ≤ (31 / 30 : ℝ) * t := by
    have hprod : 0 ≤ t * ((31 / 30 : ℝ) - t) :=
      mul_nonneg ht0 (sub_nonneg.mpr htmax)
    nlinarith
  have hbracket :
      0 ≤ -(t ^ 2) - (19 / 20 : ℝ) * t + 861 / 400 := by
    nlinarith [htsq]
  have hid : hpNegP x =
      949 / 216000 + t * (-(t ^ 2) - (19 / 20 : ℝ) * t + 861 / 400) := by
    dsimp [t, hpNegP]
    ring
  rw [hid]
  have hbase : (0 : ℝ) < 949 / 216000 := by norm_num
  have hprod : 0 ≤ t * (-(t ^ 2) - (19 / 20 : ℝ) * t + 861 / 400) :=
    mul_nonneg ht0 hbracket
  linarith

theorem hp_neg_D_pos (a x : ℝ) : 0 < hpNegD a x := by
  dsimp [hpNegD]
  positivity

end

end Li2Lean.B4.NegContour

#print axioms Li2Lean.B4.NegContour.hp_neg_p_pos_on_window
