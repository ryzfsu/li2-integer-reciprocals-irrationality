/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B4.P1GeometryLemmas

/-! Affine substitutions identifying the four oriented edge integrals with
the vendored rectangle integral. The height `1/5` specialization below is
the literal contour in v13 `hp-tail.tex:256-266`. -/

open Complex Set MeasureTheory intervalIntegral
open scoped BigOperators

namespace Li2Lean.B4.NegContourResidueProducer

noncomputable section

private theorem integral_affine_complex
    (f : ℝ → ℂ) (a b : ℝ) (hb : b ≠ 0) :
    (∫ t : ℝ in (0 : ℝ)..1, f (a + b * t) * (b : ℂ)) =
      ∫ x : ℝ in a..a + b, f x := by
  have hscale := intervalIntegral.integral_comp_mul_right
    (f := fun x : ℝ => f (a + x)) (a := (0 : ℝ)) (b := (1 : ℝ)) hb
  have hshift :
      (∫ x : ℝ in (0 : ℝ) * b..(1 : ℝ) * b, f (a + x)) =
        ∫ x : ℝ in a..a + b, f x := by
    calc
      (∫ x : ℝ in (0 : ℝ) * b..(1 : ℝ) * b, f (a + x)) =
          ∫ x : ℝ in (0 : ℝ) * b..(1 : ℝ) * b, f (x + a) := by
            apply intervalIntegral.integral_congr
            intro x hx
            congr 1
            ring
      _ = ∫ x : ℝ in (0 : ℝ) * b + a..(1 : ℝ) * b + a, f x := by
            exact intervalIntegral.integral_comp_add_right f a
      _ = ∫ x : ℝ in a..a + b, f x := by
            congr 1 <;> ring
  calc
    (∫ t : ℝ in (0 : ℝ)..1, f (a + b * t) * (b : ℂ)) =
        (∫ t : ℝ in (0 : ℝ)..1, f (a + t * b)) * (b : ℂ) := by
          rw [intervalIntegral.integral_mul_const]
          congr 1
          apply intervalIntegral.integral_congr
          intro t ht
          congr 1
          ring
    _ = ((b⁻¹) • (∫ x : ℝ in (0 : ℝ) * b..(1 : ℝ) * b, f (a + x))) *
          (b : ℂ) := by rw [hscale]
    _ = ∫ x : ℝ in (0 : ℝ) * b..(1 : ℝ) * b, f (a + x) := by
          rw [Complex.real_smul]
          have hbC : (b : ℂ) ≠ 0 := by exact_mod_cast hb
          push_cast
          field_simp
    _ = ∫ x : ℝ in a..a + b, f x := hshift

private theorem integral_affine_vertical
    (f : ℝ → ℂ) (a b : ℝ) (hb : b ≠ 0) :
    (∫ t : ℝ in (0 : ℝ)..1,
      f (a + b * t) * (Complex.I * (b : ℂ))) =
      Complex.I • (∫ y : ℝ in a..a + b, f y) := by
  have hpoint (t : ℝ) :
      f (a + b * t) * (Complex.I * (b : ℂ)) =
        (f (a + b * t) * (b : ℂ)) * Complex.I := by ring
  calc
    (∫ t : ℝ in (0 : ℝ)..1,
        f (a + b * t) * (Complex.I * (b : ℂ))) =
        ∫ t : ℝ in (0 : ℝ)..1,
          (f (a + b * t) * (b : ℂ)) * Complex.I := by
            apply intervalIntegral.integral_congr
            intro t ht
            exact hpoint t
    _ = (∫ t : ℝ in (0 : ℝ)..1,
          f (a + b * t) * (b : ℂ)) * Complex.I := by
            rw [intervalIntegral.integral_mul_const]
    _ = (∫ y : ℝ in a..a + b, f y) * Complex.I := by
          rw [integral_affine_complex f a b hb]
    _ = Complex.I • (∫ y : ℝ in a..a + b, f y) := by
          rw [smul_eq_mul]
          ring

private theorem hpTail_bottom_edge_integral
    (f : ℂ → ℂ) (left right bottom top : ℝ)
    (hwidth : right - left ≠ 0) :
    (∫ t : ℝ in (0 : ℝ)..1,
      f (hpTailRectEdgeMap left right bottom top .bottom t) *
        hpTailRectEdgeVelocity left right bottom top .bottom) =
      HIntegral f left right bottom := by
  have hvel : hpTailRectEdgeVelocity left right bottom top .bottom =
      ((right - left : ℝ) : ℂ) := by
    simp [hpTailRectEdgeVelocity, hpTailRectEdgeMap]
  rw [hvel]
  change (∫ t : ℝ in (0 : ℝ)..1,
      f (((left + (right - left) * t : ℝ) : ℂ) +
        (bottom : ℂ) * Complex.I) * ((right - left : ℝ) : ℂ)) = _
  calc
    _ = (∫ x : ℝ in left..left + (right - left),
          f ((x : ℂ) + (bottom : ℂ) * Complex.I)) :=
      integral_affine_complex
        (fun x : ℝ => f ((x : ℂ) + (bottom : ℂ) * Complex.I))
        left (right - left) hwidth
    _ = HIntegral f left right bottom := by
      unfold HIntegral
      rw [show left + (right - left) = right by ring]

private theorem hpTail_right_edge_integral
    (f : ℂ → ℂ) (left right bottom top : ℝ)
    (hheight : top - bottom ≠ 0) :
    (∫ t : ℝ in (0 : ℝ)..1,
      f (hpTailRectEdgeMap left right bottom top .right t) *
        hpTailRectEdgeVelocity left right bottom top .right) =
      VIntegral f right bottom top := by
  have hvel : hpTailRectEdgeVelocity left right bottom top .right =
      Complex.I * ((top - bottom : ℝ) : ℂ) := by
    simp [hpTailRectEdgeVelocity, hpTailRectEdgeMap]
    push_cast
    ring
  have hmap (t : ℝ) :
      hpTailRectEdgeMap left right bottom top .right t =
        (right : ℂ) + (((bottom + (top - bottom) * t : ℝ) : ℂ) * Complex.I) := by
    simp [hpTailRectEdgeMap]
    push_cast
    ring
  rw [hvel]
  calc
    _ = (∫ t : ℝ in (0 : ℝ)..1,
          f ((right : ℂ) +
            (((bottom + (top - bottom) * t : ℝ) : ℂ) * Complex.I)) *
              (Complex.I * ((top - bottom : ℝ) : ℂ))) := by
          apply intervalIntegral.integral_congr
          intro t ht
          change f (hpTailRectEdgeMap left right bottom top .right t) *
              (Complex.I * ((top - bottom : ℝ) : ℂ)) = _
          rw [hmap t]
    _ = Complex.I • (∫ y : ℝ in bottom..bottom + (top - bottom),
          f ((right : ℂ) + (y : ℂ) * Complex.I)) := by
          simpa only [Complex.ofReal_add, Complex.ofReal_mul] using
            integral_affine_vertical
              (fun y : ℝ => f ((right : ℂ) + (y : ℂ) * Complex.I))
              bottom (top - bottom) hheight
    _ = VIntegral f right bottom top := by
          unfold VIntegral
          rw [show bottom + (top - bottom) = top by ring]

private theorem hpTail_top_edge_integral
    (f : ℂ → ℂ) (left right bottom top : ℝ)
    (hwidth : right - left ≠ 0) :
    (∫ t : ℝ in (0 : ℝ)..1,
      f (hpTailRectEdgeMap left right bottom top .top t) *
        hpTailRectEdgeVelocity left right bottom top .top) =
      -HIntegral f left right top := by
  have hvel : hpTailRectEdgeVelocity left right bottom top .top =
      ((left - right : ℝ) : ℂ) := by
    simp [hpTailRectEdgeVelocity, hpTailRectEdgeMap]
  have hmap (t : ℝ) :
      hpTailRectEdgeMap left right bottom top .top t =
        ((right + (left - right) * t : ℝ) : ℂ) +
          (top : ℂ) * Complex.I := by
    simp [hpTailRectEdgeMap]
    push_cast
    ring
  have hreverse : left - right ≠ 0 := by
    intro h
    apply hwidth
    linarith
  rw [hvel]
  calc
    _ = (∫ t : ℝ in (0 : ℝ)..1,
          f (((right + (left - right) * t : ℝ) : ℂ) +
            (top : ℂ) * Complex.I) * ((left - right : ℝ) : ℂ)) := by
          apply intervalIntegral.integral_congr
          intro t ht
          change f (hpTailRectEdgeMap left right bottom top .top t) *
              ((left - right : ℝ) : ℂ) = _
          rw [hmap t]
    _ = (∫ x : ℝ in right..right + (left - right),
          f ((x : ℂ) + (top : ℂ) * Complex.I)) :=
      integral_affine_complex
        (fun x : ℝ => f ((x : ℂ) + (top : ℂ) * Complex.I))
        right (left - right) hreverse
    _ = -HIntegral f left right top := by
      unfold HIntegral
      rw [show right + (left - right) = left by ring,
        intervalIntegral.integral_symm]

private theorem hpTail_left_edge_integral
    (f : ℂ → ℂ) (left right bottom top : ℝ)
    (hheight : top - bottom ≠ 0) :
    (∫ t : ℝ in (0 : ℝ)..1,
      f (hpTailRectEdgeMap left right bottom top .left t) *
        hpTailRectEdgeVelocity left right bottom top .left) =
      -VIntegral f left bottom top := by
  have hvel : hpTailRectEdgeVelocity left right bottom top .left =
      Complex.I * ((bottom - top : ℝ) : ℂ) := by
    simp [hpTailRectEdgeVelocity, hpTailRectEdgeMap]
    push_cast
    ring
  have hmap (t : ℝ) :
      hpTailRectEdgeMap left right bottom top .left t =
        (left : ℂ) + (((top + (bottom - top) * t : ℝ) : ℂ) * Complex.I) := by
    simp [hpTailRectEdgeMap]
    push_cast
    ring
  have hreverse : bottom - top ≠ 0 := by
    intro h
    apply hheight
    linarith
  rw [hvel]
  calc
    _ = (∫ t : ℝ in (0 : ℝ)..1,
          f ((left : ℂ) +
            (((top + (bottom - top) * t : ℝ) : ℂ) * Complex.I)) *
              (Complex.I * ((bottom - top : ℝ) : ℂ))) := by
          apply intervalIntegral.integral_congr
          intro t ht
          change f (hpTailRectEdgeMap left right bottom top .left t) *
              (Complex.I * ((bottom - top : ℝ) : ℂ)) = _
          rw [hmap t]
    _ = Complex.I • (∫ y : ℝ in top..top + (bottom - top),
          f ((left : ℂ) + (y : ℂ) * Complex.I)) := by
          simpa only [Complex.ofReal_add, Complex.ofReal_mul] using
            integral_affine_vertical
              (fun y : ℝ => f ((left : ℂ) + (y : ℂ) * Complex.I))
              top (bottom - top) hreverse
    _ = -VIntegral f left bottom top := by
          unfold VIntegral
          rw [show top + (bottom - top) = bottom by ring,
            intervalIntegral.integral_symm, smul_neg]

theorem hpTail_rectIntegral_eq_RectangleIntegral
    (f : ℂ → ℂ) (left right bottom top : ℝ)
    (hwidth : right - left ≠ 0) (hheight : top - bottom ≠ 0) :
    hpTailRectIntegral left right bottom top f =
      RectangleIntegral f
        ((left : ℂ) + (bottom : ℂ) * Complex.I)
        ((right : ℂ) + (top : ℂ) * Complex.I) := by
  unfold hpTailRectIntegral
  rw [hpTail_bottom_edge_integral f left right bottom top hwidth,
    hpTail_right_edge_integral f left right bottom top hheight,
    hpTail_top_edge_integral f left right bottom top hwidth,
    hpTail_left_edge_integral f left right bottom top hheight]
  rw [RectangleIntegral]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, add_zero, zero_add, sub_self]
  abel

theorem hpTail_edge_parameterization (q n : ℕ) (hn : 0 < n) :
    hpTailRectIntegral (-1 / 2) ((n : ℝ) + 1 / 2)
        (-((n : ℝ) * (1 / 5 : ℝ))) ((n : ℝ) * (1 / 5 : ℝ))
        (hpTailKernelPlus q n) =
      RectangleIntegral (hpTailKernelPlus q n)
        (Complex.ofReal (-1 / 2) -
          Complex.ofReal ((n : ℝ) * (1 / 5 : ℝ)) * Complex.I)
        (Complex.ofReal ((n : ℝ) + 1 / 2) +
          Complex.ofReal ((n : ℝ) * (1 / 5 : ℝ)) * Complex.I) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hwidth : ((n : ℝ) + 1 / 2) - (-1 / 2 : ℝ) ≠ 0 := by
    have heq : ((n : ℝ) + 1 / 2) - (-1 / 2 : ℝ) = (n : ℝ) + 1 := by ring
    rw [heq]
    positivity
  have hheight : (n : ℝ) * (1 / 5 : ℝ) -
      (-((n : ℝ) * (1 / 5 : ℝ))) ≠ 0 := by
    have heq : (n : ℝ) * (1 / 5 : ℝ) -
        (-((n : ℝ) * (1 / 5 : ℝ))) = (n : ℝ) * (2 / 5 : ℝ) := by ring
    rw [heq]
    positivity
  convert hpTail_rectIntegral_eq_RectangleIntegral
      (hpTailKernelPlus q n) (-1 / 2) ((n : ℝ) + 1 / 2)
      (-((n : ℝ) * (1 / 5 : ℝ))) ((n : ℝ) * (1 / 5 : ℝ))
      hwidth hheight using 1 <;> push_cast <;> ring

theorem HpNegContourResidueProvider.of_q_spec (q : ℕ)
    (hq : q = 8 ∨ q = 9 ∨ q = 10) : HpNegContourResidueProvider q := by
  refine ⟨hq, ?_⟩
  intro n hn
  exact hpTailRectangleDecompositionAssumptions_of_edge_parameterization
    q n hn (hpTail_edge_parameterization q n hn)

theorem hpTailResidueRectangleCertificate_q8 (n : ℕ) (hn : 0 < n) :
    HpTailResidueRectangleCertificate 8 n (1 / 5 : ℝ) := by
  exact (HpNegContourResidueProvider.of_q_spec 8 (Or.inl rfl)).residue n hn

theorem hpTailResidueRectangleCertificate_q9 (n : ℕ) (hn : 0 < n) :
    HpTailResidueRectangleCertificate 9 n (1 / 5 : ℝ) := by
  exact (HpNegContourResidueProvider.of_q_spec 9 (Or.inr (Or.inl rfl))).residue n hn

theorem hpTailResidueRectangleCertificate_q10 (n : ℕ) (hn : 0 < n) :
    HpTailResidueRectangleCertificate 10 n (1 / 5 : ℝ) := by
  exact (HpNegContourResidueProvider.of_q_spec 10 (Or.inr (Or.inr rfl))).residue n hn

end

end Li2Lean.B4.NegContourResidueProducer

#print axioms Li2Lean.B4.NegContourResidueProducer.hpTail_rectIntegral_eq_RectangleIntegral
#print axioms Li2Lean.B4.NegContourResidueProducer.hpTail_edge_parameterization
#print axioms Li2Lean.B4.NegContourResidueProducer.HpNegContourResidueProvider.of_q_spec
#print axioms Li2Lean.B4.NegContourResidueProducer.hpTailResidueRectangleCertificate_q8
#print axioms Li2Lean.B4.NegContourResidueProducer.hpTailResidueRectangleCertificate_q9
#print axioms Li2Lean.B4.NegContourResidueProducer.hpTailResidueRectangleCertificate_q10
