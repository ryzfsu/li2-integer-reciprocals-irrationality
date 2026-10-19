/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B4.NegativeContourRightSide

open Complex Real Set
open scoped BigOperators Interval

namespace Li2Lean.B4.NegContour

noncomputable section

/-!
Finite-product assembly for the right side of the fixed-height rectangle in
v13 `hp-tail.tex:319-337`.  The geometric factor estimate is supplied by
`NegativeContourRightSide`; this file only lifts it through a nonnegative
finite product.  The discrete logarithmic estimate and the factorial
denominator estimate remain explicit hypotheses of the contour producer.
-/

private theorem finset_prod_mono_nonneg {ι : Type} {s : Finset ι}
    {f g : ι → ℝ} (hf : ∀ i ∈ s, 0 ≤ f i)
    (hg : ∀ i ∈ s, 0 ≤ g i)
    (hfg : ∀ i ∈ s, f i ≤ g i) :
    s.prod f ≤ s.prod g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hga : 0 ≤ g a := hg a (Finset.mem_insert_self a s)
      have hfS : ∀ i ∈ s, 0 ≤ f i := by
        intro i hi
        exact hf i (Finset.mem_insert_of_mem hi)
      have hgS : ∀ i ∈ s, 0 ≤ g i := by
        intro i hi
        exact hg i (Finset.mem_insert_of_mem hi)
      have hfgS : ∀ i ∈ s, f i ≤ g i := by
        intro i hi
        exact hfg i (Finset.mem_insert_of_mem hi)
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      exact mul_le_mul (hfg a (Finset.mem_insert_self a s))
        (ih hfS hgS hfgS) (Finset.prod_nonneg hfS) hga

/-- The numerator factors on the right edge assemble into one product bound.

This is the norm-level product step corresponding to the discrete product in
v13 `hp-tail.tex:319-337`.  No estimate for the resulting logarithm is hidden
here, so the downstream producer can state that arithmetic separately.
-/
theorem hp_neg_right_numerator_product_le {n : ℕ} {w : ℂ}
    (hw : w ∈ hpNegRightSide n) :
    (∏ r ∈ Finset.Icc (n + 1) (3 * n + 1),
        ‖w - (r : ℂ)‖) ≤
      ∏ r ∈ Finset.Icc (n + 1) (3 * n + 1),
        ((11 / 5 : ℝ) * (n : ℝ) + 1) := by
  apply finset_prod_mono_nonneg
  · intro r hr
    exact norm_nonneg _
  · intro r hr
    positivity
  · intro r hr
    exact hp_neg_right_factor_bound hr hw

end

end Li2Lean.B4.NegContour

#print axioms Li2Lean.B4.NegContour.hp_neg_right_numerator_product_le
