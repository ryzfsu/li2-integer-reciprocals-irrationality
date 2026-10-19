/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B4.NegativeContourBoundary

open Complex Real

namespace Li2Lean.B4.NegContour

noncomputable section

/-!
The phase normalization used by the v13 exceptional rectangle is exposed as a
small reusable lemma.  This is the common input for all four side estimates:
`hp-tail.tex:258-266` uses `lambda = -log q + pi * I`, and the boundary
quantity in `hp-tail.tex:319-371` contains the full product with `exp (lambda*w)`.
-/

theorem hpNegLambda_re (q : ℕ) :
    (hpNegLambda q).re = -Real.log (q : ℝ) := by
  unfold hpNegLambda
  simp only [Complex.add_re, Complex.neg_re, Complex.ofReal_re,
    Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, sub_zero, zero_mul, add_zero]

theorem hpNegLambda_im (q : ℕ) :
    (hpNegLambda q).im = Real.pi := by
  unfold hpNegLambda
  simp only [Complex.add_im, Complex.neg_im, Complex.ofReal_im,
    Complex.mul_im, Complex.ofReal_re, Complex.I_re, Complex.I_im,
    mul_zero, zero_mul, sub_zero, zero_add, neg_zero, mul_one]
  ring

theorem hpNegPhaseNorm (q : ℕ) (w : ℂ) :
    ‖Complex.exp (hpNegLambda q * w)‖ =
      Real.exp (-Real.log (q : ℝ) * w.re - Real.pi * w.im) := by
  rw [Complex.norm_exp]
  congr 1
  rw [Complex.mul_re, hpNegLambda_re, hpNegLambda_im]

end

end Li2Lean.B4.NegContour

#print axioms Li2Lean.B4.NegContour.hpNegLambda_re
#print axioms Li2Lean.B4.NegContour.hpNegLambda_im
#print axioms Li2Lean.B4.NegContour.hpNegPhaseNorm
