/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B4.NegativeContourBoundary
import Li2Lean.B4.NegativeContourPhase

open Complex Real Set
open scoped BigOperators

namespace Li2Lean.B4.NegContour

noncomputable section

/-!
Exact conjugation identities for the fixed-height rectangle in the negative
tail.  These are the reflection steps used in v13 `hp-tail.tex:319-371`:
the product has real coefficients, while the phase `lambda = -log q + pi I`
changes the sign of its imaginary-coordinate contribution.  The logarithmic
identity below is stated away from the pole set; the side membership lemmas
then identify the top/bottom and left/right reflected edges.
-/

theorem hp_neg_phi_conj (n : ℕ) (w : ℂ) :
    hpNegPhi n ((starRingEnd ℂ) w) =
      (starRingEnd ℂ) (hpNegPhi n w) := by
  unfold hpNegPhi
  rw [map_div₀]
  · congr 1
    · simp only [map_prod]
      apply Finset.prod_congr rfl
      intro r hr
      rw [map_sub]
      simp
    · simp only [map_prod]
      apply Finset.prod_congr rfl
      intro j hj
      rw [map_pow, map_sub]
      simp

theorem hp_neg_phi_norm_conj (n : ℕ) (w : ℂ) :
    ‖hpNegPhi n ((starRingEnd ℂ) w)‖ = ‖hpNegPhi n w‖ := by
  rw [hp_neg_phi_conj]
  exact Complex.norm_conj _

theorem hp_neg_phase_norm_conj (q : ℕ) (w : ℂ) :
    ‖Complex.exp (hpNegLambda q * ((starRingEnd ℂ) w))‖ =
      Real.exp (-Real.log (q : ℝ) * w.re + Real.pi * w.im) := by
  rw [hpNegPhaseNorm]
  congr 1
  simp

theorem hp_neg_boundary_log_conj (q n : ℕ) {w : ℂ}
    (hphi : hpNegPhi n w ≠ 0) :
    hpNegBoundaryLog q n ((starRingEnd ℂ) w) =
      hpNegBoundaryLog q n w + 2 * Real.pi * w.im := by
  have hnorm : ‖hpNegPhi n w‖ ≠ 0 := norm_ne_zero_iff.mpr hphi
  have hexp : ‖Complex.exp (hpNegLambda q * w)‖ ≠ 0 := by
    rw [hpNegPhaseNorm]
    exact ne_of_gt (Real.exp_pos _)
  have hconjexp :
      ‖Complex.exp (hpNegLambda q * ((starRingEnd ℂ) w))‖ ≠ 0 := by
    rw [hp_neg_phase_norm_conj]
    exact ne_of_gt (Real.exp_pos _)
  unfold hpNegBoundaryLog
  rw [norm_mul, norm_mul]
  rw [hp_neg_phi_norm_conj]
  rw [Real.log_mul hnorm hconjexp, Real.log_mul hnorm hexp]
  rw [hp_neg_phase_norm_conj, hpNegPhaseNorm]
  rw [Real.log_exp, Real.log_exp]
  simp
  ring

theorem hp_neg_top_mem_implies_bottom_mem {n : ℕ} {w : ℂ}
    (hw : w ∈ hpNegTopSide n) :
    (starRingEnd ℂ) w ∈ hpNegBottomSide n := by
  simp [hpNegTopSide, hpNegBottomSide, hpRectLower, hpRectUpper,
    Complex.conj_re, Complex.conj_im, div_eq_mul_inv] at hw ⊢
  rcases hw with ⟨hlo, hhi, him⟩
  refine ⟨hlo, hhi, ?_⟩
  linarith

theorem hp_neg_bottom_mem_implies_top_mem {n : ℕ} {w : ℂ}
    (hw : w ∈ hpNegBottomSide n) :
    (starRingEnd ℂ) w ∈ hpNegTopSide n := by
  simp [hpNegTopSide, hpNegBottomSide, hpRectLower, hpRectUpper,
    Complex.conj_re, Complex.conj_im, div_eq_mul_inv] at hw ⊢
  rcases hw with ⟨hlo, hhi, him⟩
  refine ⟨hlo, hhi, ?_⟩
  linarith

theorem hp_neg_left_mem_implies_left_mem {n : ℕ} {w : ℂ}
    (hw : w ∈ hpNegLeftSide n) :
    (starRingEnd ℂ) w ∈ hpNegLeftSide n := by
  simp [hpNegLeftSide, hpRectLower, hpRectUpper,
    Complex.conj_re, Complex.conj_im, div_eq_mul_inv] at hw ⊢
  rcases hw with ⟨hre, hlo, hhi⟩
  refine ⟨hre, ?_, ?_⟩ <;> linarith

theorem hp_neg_right_mem_implies_right_mem {n : ℕ} {w : ℂ}
    (hw : w ∈ hpNegRightSide n) :
    (starRingEnd ℂ) w ∈ hpNegRightSide n := by
  simp [hpNegRightSide, hpRectLower, hpRectUpper,
    Complex.conj_re, Complex.conj_im, div_eq_mul_inv] at hw ⊢
  rcases hw with ⟨hre, hlo, hhi⟩
  refine ⟨hre, ?_, ?_⟩ <;> linarith

theorem hp_neg_top_im (n : ℕ) {w : ℂ} (hw : w ∈ hpNegTopSide n) :
    w.im = (n : ℝ) / 5 := by
  simpa [hpNegTopSide, hpRectLower, hpRectUpper, div_eq_mul_inv] using hw.2.2

theorem hp_neg_bottom_im (n : ℕ) {w : ℂ} (hw : w ∈ hpNegBottomSide n) :
    w.im = -((n : ℝ) / 5) := by
  simpa [hpNegBottomSide, hpRectLower, hpRectUpper, div_eq_mul_inv] using hw.2.2

theorem hp_neg_boundary_log_top_reflection {q n : ℕ} {w : ℂ}
    (hw : w ∈ hpNegTopSide n) (hphi : hpNegPhi n w ≠ 0) :
    hpNegBoundaryLog q n ((starRingEnd ℂ) w) =
      hpNegBoundaryLog q n w + 2 * Real.pi * ((n : ℝ) / 5) := by
  rw [hp_neg_boundary_log_conj q n hphi, hp_neg_top_im n hw]

theorem hp_neg_boundary_log_bottom_reflection {q n : ℕ} {w : ℂ}
    (hw : w ∈ hpNegBottomSide n) (hphi : hpNegPhi n w ≠ 0) :
    hpNegBoundaryLog q n ((starRingEnd ℂ) w) =
      hpNegBoundaryLog q n w - 2 * Real.pi * ((n : ℝ) / 5) := by
  rw [hp_neg_boundary_log_conj q n hphi, hp_neg_bottom_im n hw]
  ring

end

end Li2Lean.B4.NegContour

#print axioms Li2Lean.B4.NegContour.hp_neg_phi_conj
#print axioms Li2Lean.B4.NegContour.hp_neg_phi_norm_conj
#print axioms Li2Lean.B4.NegContour.hp_neg_phase_norm_conj
#print axioms Li2Lean.B4.NegContour.hp_neg_boundary_log_conj
#print axioms Li2Lean.B4.NegContour.hp_neg_top_mem_implies_bottom_mem
#print axioms Li2Lean.B4.NegContour.hp_neg_bottom_mem_implies_top_mem
#print axioms Li2Lean.B4.NegContour.hp_neg_left_mem_implies_left_mem
#print axioms Li2Lean.B4.NegContour.hp_neg_right_mem_implies_right_mem
#print axioms Li2Lean.B4.NegContour.hp_neg_boundary_log_top_reflection
#print axioms Li2Lean.B4.NegContour.hp_neg_boundary_log_bottom_reflection
