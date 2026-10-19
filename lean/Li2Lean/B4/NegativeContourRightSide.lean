/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B4.NegativeContourBoundary

open Complex Real
open scoped BigOperators Interval

namespace Li2Lean.B4.NegContour

noncomputable section

/-!
Elementary geometry for the right edge of the fixed-height rectangle in
`hp-tail.tex:319-371`.  These lemmas only expose the coordinates of a point
on the edge and a coarse bound for one numerator factor; the logarithmic
right-edge estimate remains a separate analytic obligation.
-/

theorem hp_neg_right_re_eq (n : ℕ) {w : ℂ}
    (hw : w ∈ hpNegRightSide n) :
    w.re = (n : ℝ) + 1 / 2 := by
  have h := hw.1
  simpa [hpNegRightSide, hpRectUpper] using h

theorem hp_neg_right_im_abs_le (n : ℕ) {w : ℂ}
    (hw : w ∈ hpNegRightSide n) :
    |w.im| ≤ (n : ℝ) / 5 := by
  have h := hw.2
  have hlo : -((n : ℝ) / 5) ≤ w.im := by
    simpa [hpNegRightSide, hpRectLower, hpRectUpper, div_eq_mul_inv] using h.1
  have hhi : w.im ≤ (n : ℝ) / 5 := by
    simpa [hpNegRightSide, hpRectLower, hpRectUpper, div_eq_mul_inv] using h.2
  exact (abs_le).2 ⟨by linarith, hhi⟩

theorem hp_neg_right_factor_bound {n r : ℕ} {w : ℂ}
    (hr : r ∈ Finset.Icc (n + 1) (3 * n + 1))
    (hw : w ∈ hpNegRightSide n) :
    ‖w - (r : ℂ)‖ ≤ (11 / 5 : ℝ) * (n : ℝ) + 1 := by
  have hnr : n + 1 ≤ r := (Finset.mem_Icc.mp hr).1
  have hrmax : r ≤ 3 * n + 1 := (Finset.mem_Icc.mp hr).2
  have hre := hp_neg_right_re_eq n hw
  have him := hp_neg_right_im_abs_le n hw
  have hreal : |(w - (r : ℂ)).re| ≤ 2 * (n : ℝ) + 1 := by
    have hr_re : ((r : ℂ).re) = (r : ℝ) := by norm_num
    simp only [Complex.sub_re, hre, hr_re]
    have hnr' : (n : ℝ) + 1 ≤ (r : ℝ) := by exact_mod_cast hnr
    have hrmax' : (r : ℝ) ≤ 3 * (n : ℝ) + 1 := by
      exact_mod_cast hrmax
    have hnonpos : (n : ℝ) + 1 / 2 - (r : ℝ) ≤ 0 := by linarith
    rw [abs_of_nonpos hnonpos]
    linarith
  have himag : |(w - (r : ℂ)).im| ≤ (n : ℝ) / 5 := by
    simpa [Complex.sub_im] using him
  calc
    ‖w - (r : ℂ)‖ ≤ |(w - (r : ℂ)).re| + |(w - (r : ℂ)).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ ≤ (2 * (n : ℝ) + 1) + (n : ℝ) / 5 := add_le_add hreal himag
    _ ≤ (11 / 5 : ℝ) * (n : ℝ) + 1 := by ring_nf; linarith

theorem hp_neg_right_denominator_factor_lower {n j : ℕ} {w : ℂ}
    (hj : j ≤ n)
    (hw : w ∈ hpNegRightSide n) :
    (1 / 2 : ℝ) ≤ ‖(j : ℂ) - w‖ := by
  have hre := hp_neg_right_re_eq n hw
  have hjR : (j : ℝ) ≤ (n : ℝ) := by exact_mod_cast hj
  have hgap : (1 / 2 : ℝ) ≤ w.re - (j : ℝ) := by
    rw [hre]
    linarith
  have hnonpos : (j : ℝ) - w.re ≤ 0 := by linarith
  have hj_re : ((j : ℂ).re) = (j : ℝ) := by norm_num
  calc
    (1 / 2 : ℝ) ≤ w.re - (j : ℝ) := hgap
    _ = |((j : ℂ) - w).re| := by
      rw [Complex.sub_re, hj_re, abs_of_nonpos hnonpos]
      linarith
    _ ≤ ‖(j : ℂ) - w‖ := Complex.abs_re_le_norm _

end

end Li2Lean.B4.NegContour

#print axioms Li2Lean.B4.NegContour.hp_neg_right_re_eq
#print axioms Li2Lean.B4.NegContour.hp_neg_right_im_abs_le
#print axioms Li2Lean.B4.NegContour.hp_neg_right_factor_bound
#print axioms Li2Lean.B4.NegContour.hp_neg_right_denominator_factor_lower
