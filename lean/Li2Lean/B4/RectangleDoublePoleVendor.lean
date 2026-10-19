/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B4.RectangleDoublePole
import Li2Lean.Vendor.PNT.ResidueCalcOnRectangles

open Complex Set MeasureTheory intervalIntegral

namespace Li2Lean.B4.RectangleDoublePole

noncomputable section

/-! The vendored PNT+ rectangle integral has the same four-side orientation
as the local FTC lemma.  This adapter exposes the result at the global PNT+
names used by the contour proof.  The mathematical content remains the
explicit primitive from v13 `hp-tail.tex:256-410`. -/
theorem vendor_rectangleIntegral_doublePole_eq_zero
    (c p z w : ℂ)
    (hz_re : z.re ≠ p.re) (hw_re : w.re ≠ p.re)
    (hz_im : z.im ≠ p.im) (hw_im : w.im ≠ p.im) :
    _root_.RectangleIntegral (fun s => c / (s - p) ^ 2) z w = 0 := by
  change RectangleIntegral (fun s => c / (s - p) ^ 2) z w = 0
  exact rectangleIntegral_doublePole_eq_zero c p z w hz_re hw_re hz_im hw_im

end

end Li2Lean.B4.RectangleDoublePole

#print axioms Li2Lean.B4.RectangleDoublePole.vendor_rectangleIntegral_doublePole_eq_zero
