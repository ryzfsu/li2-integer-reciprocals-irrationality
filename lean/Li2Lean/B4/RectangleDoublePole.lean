/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Mathlib

/-!
# Double-pole rectangle cancellation

This file isolates the elementary FTC part of the rectangle calculation used
in the v13 `hp-tail.tex:256-410` contour route.  The primitive is
`-c / (w - p)`; its four side integrals telescope, so a double pole has zero
oriented rectangle integral.  It is independent of the simple-pole residue
theorem and of the boundary estimate.

The definitions below match the vendored PrimeNumberTheoremAnd rectangle
API (`HIntegral`, `VIntegral`, and `RectangleIntegral`) so this lemma can be
used after the vendored files are imported.
-/

open Complex Set MeasureTheory intervalIntegral

namespace Li2Lean.B4.RectangleDoublePole

noncomputable section

def HIntegral (f : ℂ → ℂ) (x₁ x₂ y : ℝ) : ℂ :=
  ∫ x in x₁..x₂, f ((x : ℂ) + (y : ℂ) * I)

def VIntegral (f : ℂ → ℂ) (x y₁ y₂ : ℝ) : ℂ :=
  I • ∫ y in y₁..y₂, f ((x : ℂ) + (y : ℂ) * I)

def RectangleIntegral (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
  HIntegral f z.re w.re z.im - HIntegral f z.re w.re w.im +
    VIntegral f w.re z.im w.im - VIntegral f z.re z.im w.im

private lemma horizontal_den_ne_zero {y : ℝ} {p : ℂ} (hy : y ≠ p.im) (x : ℝ) :
    (x : ℂ) + (y : ℂ) * I - p ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  simp at hi
  apply hy
  linarith

private lemma vertical_den_ne_zero {x : ℝ} {p : ℂ} (hx : x ≠ p.re) (y : ℝ) :
    (x : ℂ) + (y : ℂ) * I - p ≠ 0 := by
  intro h
  have hr := congrArg Complex.re h
  simp at hr
  apply hx
  linarith

private lemma horizontal_primitive_deriv (c p : ℂ) (y x : ℝ)
    (hden : (x : ℂ) + (y : ℂ) * I - p ≠ 0) :
    HasDerivAt
      (fun t : ℝ => -(c / ((t : ℂ) + (y : ℂ) * I - p)))
      (c / ((x : ℂ) + (y : ℂ) * I - p) ^ 2) x := by
  have hs : HasDerivAt (fun t : ℝ => (t : ℂ) + (y : ℂ) * I - p) 1 x := by
    convert ((hasDerivAt_id x).ofReal_comp).add
      (hasDerivAt_const x ((y : ℂ) * I - p)) using 1
    · ext t
      simp
      ring
    · norm_num
  have hi := hs.inv hden
  have hc := hi.const_mul c
  have hn := hc.neg
  convert hn using 1
  · ext t
    simp [div_eq_mul_inv]
  · field_simp

private lemma vertical_primitive_deriv (c p : ℂ) (x y : ℝ)
    (hden : (x : ℂ) + (y : ℂ) * I - p ≠ 0) :
    HasDerivAt
      (fun t : ℝ => -(c / ((x : ℂ) + (t : ℂ) * I - p)))
      (I • (c / ((x : ℂ) + (y : ℂ) * I - p) ^ 2)) y := by
  have hs : HasDerivAt (fun t : ℝ => (x : ℂ) + (t : ℂ) * I - p) I y := by
    have ht : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 y := by
      simpa using (hasDerivAt_id y).ofReal_comp
    have hm := ht.const_mul I
    have ha := (hasDerivAt_const y ((x : ℂ) - p)).add hm
    convert ha using 1
    · ext t
      simp [mul_comm]
      ring
    · simp
  have hi := hs.inv hden
  have hc := hi.const_mul c
  have hn := hc.neg
  convert hn using 1
  · ext t
    simp [div_eq_mul_inv]
  · simp only [smul_eq_mul]
    simp [div_eq_mul_inv]
    ring

private lemma horizontal_ftc (c p : ℂ) (a b y : ℝ) (hy : y ≠ p.im) :
    HIntegral (fun s => c / (s - p) ^ 2) a b y =
      -(c / ((b : ℂ) + (y : ℂ) * I - p)) -
        -(c / ((a : ℂ) + (y : ℂ) * I - p)) := by
  unfold HIntegral
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    exact horizontal_primitive_deriv c p y x
      (horizontal_den_ne_zero hy x)
  · have hden : Continuous (fun t : ℝ => (t : ℂ) + (y : ℂ) * I - p) := by
      fun_prop
    have hpow : Continuous (fun t : ℝ => ((t : ℂ) + (y : ℂ) * I - p) ^ 2) :=
      hden.pow 2
    have hne : ∀ t : ℝ, ((t : ℂ) + (y : ℂ) * I - p) ^ 2 ≠ 0 := by
      intro t
      exact pow_ne_zero _ (horizontal_den_ne_zero hy t)
    exact (continuous_const.div hpow hne).intervalIntegrable (μ := volume) _ _

private lemma vertical_ftc (c p : ℂ) (x a b : ℝ) (hx : x ≠ p.re) :
    VIntegral (fun s => c / (s - p) ^ 2) x a b =
      -(c / ((x : ℂ) + (b : ℂ) * I - p)) -
        -(c / ((x : ℂ) + (a : ℂ) * I - p)) := by
  unfold VIntegral
  rw [← intervalIntegral.integral_smul]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro y hy
    exact vertical_primitive_deriv c p x y
      (vertical_den_ne_zero hx y)
  · have hden : Continuous (fun t : ℝ => (x : ℂ) + (t : ℂ) * I - p) := by
      fun_prop
    have hpow : Continuous (fun t : ℝ => ((x : ℂ) + (t : ℂ) * I - p) ^ 2) :=
      hden.pow 2
    have hne : ∀ t : ℝ, ((x : ℂ) + (t : ℂ) * I - p) ^ 2 ≠ 0 := by
      intro t
      exact pow_ne_zero _ (vertical_den_ne_zero hx t)
    have hbase : Continuous
        (fun t : ℝ => c / ((x : ℂ) + (t : ℂ) * I - p) ^ 2) :=
      continuous_const.div hpow hne
    have hconst : Continuous (fun _ : ℝ => I) := continuous_const
    exact (hconst.smul hbase).intervalIntegrable (μ := volume) _ _

/-- The oriented integral of a double principal part vanishes.  This is the
v13 double-pole contribution at `hp-tail.tex:256-410`; it is proved by the
explicit primitive rather than a general residue theorem. -/
theorem rectangleIntegral_doublePole_eq_zero
    (c p z w : ℂ)
    (hz_re : z.re ≠ p.re) (hw_re : w.re ≠ p.re)
    (hz_im : z.im ≠ p.im) (hw_im : w.im ≠ p.im) :
    RectangleIntegral (fun s => c / (s - p) ^ 2) z w = 0 := by
  unfold RectangleIntegral
  rw [horizontal_ftc c p z.re w.re z.im hz_im,
    horizontal_ftc c p z.re w.re w.im hw_im,
    vertical_ftc c p w.re z.im w.im hw_re,
    vertical_ftc c p z.re z.im w.im hz_re]
  ring

end

end Li2Lean.B4.RectangleDoublePole

#print axioms Li2Lean.B4.RectangleDoublePole.rectangleIntegral_doublePole_eq_zero
