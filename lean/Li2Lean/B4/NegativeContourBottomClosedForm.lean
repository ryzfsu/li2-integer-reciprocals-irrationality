/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B4.NegativeContourBottomLeft
import Li2Lean.P0.CA.Contour.ClosedForm

open Complex Real Set
open scoped BigOperators Interval

namespace Li2Lean.B4.NegContour

noncomputable section

open Li2Lean.P0.CA.Contour

/-!
Closed-form bookkeeping for the bottom side of the fixed-height rectangle.
This is the continuous term in v13 `hp-tail.tex:307-316`; the primitive
`Gr` is reused from the 1/2 contour implementation.  The tangent-window
polynomial is the one in `hp-tail.tex:343-355` and is supplied by
`NegativeContourTangent`.
-/

def hpBottomPoint (x : ℝ) : ℂ := (x : ℂ) - (1 / 5 : ℝ) * Complex.I

def hpBottomClosed (x : ℝ) : ℝ :=
  (Gr (x - 1) (-(1 / 5 : ℝ)) - Gr (x - 3) (-(1 / 5 : ℝ))) -
    2 * (Gr (x - 0) (-(1 / 5 : ℝ)) - Gr (x - 1) (-(1 / 5 : ℝ)))

theorem hp_bottom_point_re (x : ℝ) : (hpBottomPoint x).re = x := by
  simp [hpBottomPoint]

theorem hp_bottom_point_im (x : ℝ) : (hpBottomPoint x).im = -(1 / 5 : ℝ) := by
  simp [hpBottomPoint]

theorem hp_bottom_point_im_ne_zero (x : ℝ) : (hpBottomPoint x).im ≠ 0 := by
  rw [hp_bottom_point_im]
  norm_num

theorem hp_product_log_integral_bottom_closed (n : ℕ) (x : ℝ) :
    hpProductLogIntegral n (hpBottomPoint x) =
      (n : ℝ) * hpBottomClosed x := by
  have hpoint : hpBottomPoint x =
      (x : ℂ) + ((-(1 / 5 : ℝ)) : ℂ) * Complex.I := by
    simp [hpBottomPoint]
    ring
  rw [hpoint]
  unfold hpProductLogIntegral hpBottomClosed hpLog
  have h13 := integral_log_norm_sub (X := x) (Y := -(1 / 5 : ℝ))
    (by norm_num : (-(1 / 5 : ℝ)) ≠ 0) 1 3
  have h01 := integral_log_norm_sub (X := x) (Y := -(1 / 5 : ℝ))
    (by norm_num : (-(1 / 5 : ℝ)) ≠ 0) 0 1
  rw [show (∫ t in (1 : ℝ)..3,
      Real.log ‖(x : ℂ) + -((1 / 5 : ℝ) : ℂ) * Complex.I - (t : ℂ)‖) =
      Gr (x - 1) (-(1 / 5 : ℝ)) - Gr (x - 3) (-(1 / 5 : ℝ)) by
        simpa [Complex.ofReal_neg] using h13,
    show (∫ t in (0 : ℝ)..1,
      Real.log ‖(x : ℂ) + -((1 / 5 : ℝ) : ℂ) * Complex.I - (t : ℂ)‖) =
      Gr (x - 0) (-(1 / 5 : ℝ)) - Gr (x - 1) (-(1 / 5 : ℝ)) by
        simpa [Complex.ofReal_neg] using h01]

theorem hp_bottom_polynomial_pos_of_scaled (x : ℝ)
    (hxlo : -(1 / 60 : ℝ) ≤ x) (hxhi : x ≤ 61 / 60) :
    0 < hpNegP x :=
  hp_neg_p_pos_on_window hxlo hxhi

/-! The final tangent inequality is deliberately an explicit certificate input:
the preceding theorem discharges its rational concavity denominator, while
the three q-specific logarithm/arctangent evaluations are the certified finite
data for v13 `hp-tail.tex:343-371`.
-/
structure HpNegBottomTangentCertificate (q : ℕ) where
  q_spec : q = 8 ∨ q = 9 ∨ q = 10
  tangent : ∀ x : ℝ,
    (-(1 / 60 : ℝ)) ≤ x → x ≤ 61 / 60 →
    hpBottomClosed x - Real.log (q : ℝ) * x + Real.pi / 5 ≤
      (hpNegT q : ℝ)

theorem hp_neg_bottom_tangent_certificate_bound
    {q : ℕ} (cert : HpNegBottomTangentCertificate q)
    {x : ℝ} (hxlo : -(1 / 60 : ℝ) ≤ x) (hxhi : x ≤ 61 / 60) :
    hpBottomClosed x - Real.log (q : ℝ) * x + Real.pi / 5 ≤
      (hpNegT q : ℝ) :=
  cert.tangent x hxlo hxhi

end

end Li2Lean.B4.NegContour

#print axioms Li2Lean.B4.NegContour.hp_product_log_integral_bottom_closed
#print axioms Li2Lean.B4.NegContour.hp_bottom_polynomial_pos_of_scaled
#print axioms Li2Lean.B4.NegContour.hp_neg_bottom_tangent_certificate_bound
