/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B4.NegativeContourBoundary
import Li2Lean.B4.NegativeContourPhase
import Li2Lean.B4.NegativeContourRightSide

open Complex Real Set
open scoped BigOperators Interval

namespace Li2Lean.B4.NegContour

noncomputable section

private theorem prod_le_prod_nonneg {ι : Type} {s : Finset ι} {f g : ι → ℝ}
    (hf : ∀ i ∈ s, 0 ≤ f i) (hg : ∀ i ∈ s, 0 ≤ g i)
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
      exact mul_le_mul (hfg a (Finset.mem_insert_self a s)) (ih hfS hgS hfgS)
        (by exact Finset.prod_nonneg hfS) hga

/-!
Right-edge inputs for the fixed-height rectangle in v13 `hp-tail.tex:319-337`.

The right edge is the only side where the paper uses a direct discrete product
bound.  This file isolates the exact phase estimate and the norm-level product
assembly.  The two finite-product inequalities are explicit hypotheses of the
assembly theorem, so this module does not hide the remaining arithmetic
estimate behind an unproved contour claim.
-/

theorem hp_neg_right_re_im_bounds {n : ℕ} {w : ℂ}
    (hw : w ∈ hpNegRightSide n) :
    w.re = (n : ℝ) + 1 / 2 ∧
      -((n : ℝ) / 5) ≤ w.im ∧ w.im ≤ (n : ℝ) / 5 := by
  simpa [hpNegRightSide, hpRectLower, hpRectUpper, div_eq_mul_inv] using hw

theorem hp_neg_right_phase_exponent_le {q n : ℕ} {w : ℂ}
    (hq : 1 ≤ q) (hw : w ∈ hpNegRightSide n) :
    -Real.log (q : ℝ) * w.re - Real.pi * w.im ≤
      -Real.log (q : ℝ) * ((n : ℝ) + 1 / 2) + Real.pi * ((n : ℝ) / 5) := by
  rcases hp_neg_right_re_im_bounds hw with ⟨hre, him, _⟩
  rw [hre]
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hlog : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hqR
  have hpi : 0 ≤ Real.pi := Real.pi_pos.le
  nlinarith

theorem hp_neg_right_phase_norm_le {q n : ℕ} {w : ℂ}
    (hq : 1 ≤ q) (hw : w ∈ hpNegRightSide n) :
    ‖Complex.exp (hpNegLambda q * w)‖ ≤
      Real.exp (-Real.log (q : ℝ) * ((n : ℝ) + 1 / 2) +
        Real.pi * ((n : ℝ) / 5)) := by
  rw [hpNegPhaseNorm]
  exact Real.exp_le_exp.mpr (hp_neg_right_phase_exponent_le hq hw)

theorem hp_neg_right_norm_phi_le_of_factor_bounds {n : ℕ} {w : ℂ}
    {U D : ℝ} (hU : 0 ≤ U) (hD : 0 < D)
    (hnum : ∀ r ∈ Finset.Icc (n + 1) (3 * n + 1),
      ‖w - (r : ℂ)‖ ≤ U)
    (hden : D ≤ ∏ j ∈ Finset.range (n + 1), ‖w - (j : ℂ)‖ ^ 2) :
    ‖hpNegPhi n w‖ ≤
      (∏ r ∈ Finset.Icc (n + 1) (3 * n + 1), U) / D := by
  rw [hpNegPhi, Complex.norm_div, Complex.norm_prod, Complex.norm_prod]
  simp only [norm_pow]
  apply div_le_div₀
  · exact Finset.prod_nonneg (fun r hr => hU)
  · exact prod_le_prod_nonneg (fun r hr => norm_nonneg _)
      (fun r hr => hU) (fun r hr => hnum r hr)
  · exact hD
  · exact hden

def hpNegRightUpper (n : ℕ) : ℝ := (11 / 5 : ℝ) * (n : ℝ) + 1

theorem hp_neg_right_norm_phi_le_of_denominator {n : ℕ} {w : ℂ}
    (hw : w ∈ hpNegRightSide n) {D : ℝ} (hD : 0 < D)
    (hden : D ≤ ∏ j ∈ Finset.range (n + 1), ‖w - (j : ℂ)‖ ^ 2) :
    ‖hpNegPhi n w‖ ≤
      (∏ r ∈ Finset.Icc (n + 1) (3 * n + 1), hpNegRightUpper n) / D := by
  apply hp_neg_right_norm_phi_le_of_factor_bounds (U := hpNegRightUpper n)
  · dsimp [hpNegRightUpper]
    positivity
  · exact hD
  · intro r hr
    simpa [hpNegRightUpper] using hp_neg_right_factor_bound hr hw
  · exact hden

/-! The remaining right-edge arithmetic is named explicitly.  Its shape is
the v13 estimate after the norm product has been assembled: the first field is
the numerator factor bound, the second is the factorial denominator bound,
and the third is the logarithmic envelope. -/
structure HpNegRightFactorCertificate (q : ℕ) where
  q_spec : q = 8 ∨ q = 9 ∨ q = 10
  numerator : ∀ n : ℕ, 30 ≤ n → ∀ w ∈ hpNegRightSide n,
    ∀ r ∈ Finset.Icc (n + 1) (3 * n + 1),
      ‖w - (r : ℂ)‖ ≤ (11 / 5 : ℝ) * (n : ℝ) + 1
  denominator : ∀ n : ℕ, 30 ≤ n → ∀ w ∈ hpNegRightSide n,
    ((Nat.factorial n : ℝ) ^ 2) / 4 ≤
      ∏ j ∈ Finset.range (n + 1), ‖w - (j : ℂ)‖ ^ 2
  logarithmic : ∀ n : ℕ, 30 ≤ n → ∀ w ∈ hpNegRightSide n,
    hpNegBoundaryLog q n w ≤
      (n : ℝ) * (hpNegT q : ℝ) +
        (18 : ℝ) * (1 + Real.log ((n + 1 : ℕ) : ℝ))

end

end Li2Lean.B4.NegContour

#print axioms Li2Lean.B4.NegContour.hp_neg_right_phase_exponent_le
#print axioms Li2Lean.B4.NegContour.hp_neg_right_phase_norm_le
#print axioms Li2Lean.B4.NegContour.hp_neg_right_norm_phi_le_of_factor_bounds
