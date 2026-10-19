/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.V.OuterMomentBridge
import Li2Lean.V.VLiteralContour

namespace Li2Lean.V

noncomputable section

/-- Evaluate the v13 rational coefficient matrix at the actual complex value
`Li_2(-1/q)` (`v-arithmetic.tex:24-35`). -/
def vOuterPolynomialEvalHom (q : ℕ) : Polynomial ℚ →+* ℂ :=
  Polynomial.eval₂RingHom (algebraMap ℚ ℂ)
    (Complex.ofReal (li2InvValue (-(q : ℤ))))

/-- The real source-matrix adapter is entrywise the complex evaluation of
the v13 polynomial matrix (`v-arithmetic.tex:24-35`). -/
theorem vOuterSourceMatrix_map_eq_polynomialEval (q n : ℕ) :
    (vOuterSourceMatrix q n).map Complex.ofRealHom =
      (vSourceMatrix n (-(q : ℤ))).map (vOuterPolynomialEvalHom q) := by
  classical
  ext r c
  change Complex.ofReal ((vOuterSourceMatrix q n) r c) =
    vOuterPolynomialEvalHom q ((vSourceMatrix n (-(q : ℤ))) r c)
  by_cases htop : r.val < vM n
  · have htop' : r.val < 4 * n := by simpa [vM] using htop
    simp [vOuterSourceMatrix, vSourceMatrix, vOuterPolynomialEvalHom,
      vM, vS, vMatrixSize, vIIndexNat, vJIndex, vCEntry, htop, htop']
  · by_cases hmid : r.val < 2 * vM n
    · have htop' : ¬ r.val < 4 * n := by simpa [vM] using htop
      have hmid' : r.val < 2 * (4 * n) := by simpa [vM] using hmid
      simp [vOuterSourceMatrix, vSourceMatrix, vOuterPolynomialEvalHom,
          vM, vS, vMatrixSize, vIIndexNat, vJIndex, vBEntry, vAEntry,
          htop, htop', hmid, hmid', vOuterBeta] <;> ring
    · have htop' : ¬ r.val < 4 * n := by simpa [vM] using htop
      have hmid' : ¬ r.val < 2 * (4 * n) := by simpa [vM] using hmid
      simp [vOuterSourceMatrix, vSourceMatrix, vOuterPolynomialEvalHom,
          vM, vS, vMatrixSize, vJIndex, vLambdaIndex, vVEntry, htop,
          htop', hmid, hmid']

/-- The literal moment matrix determinant is the v13 signed polynomial
value after the Mellin row addition (`v-arithmetic.tex:24-35`,
`v-analytic.tex:71-83`). -/
theorem vOuterMomentMatrix_det_eq_vContourGValue
    (q n : ℕ) (hq : 2 ≤ q) :
    Complex.ofReal ((vOuterMomentMatrix q n).det) =
      Literal.vContourGValue q n := by
  have hsource := vOuterSourceMatrix_map_eq_polynomialEval q n
  have hreal := RingHom.map_det Complex.ofRealHom (vOuterSourceMatrix q n)
  have hpoly := RingHom.map_det (vOuterPolynomialEvalHom q)
    (vSourceMatrix n (-(q : ℤ)))
  calc
    Complex.ofReal ((vOuterMomentMatrix q n).det) =
        Complex.ofReal ((vOuterSourceMatrix q n).det) := by
      exact congrArg Complex.ofReal
        (vOuterMomentMatrix_det_eq_sourceMatrix_det_of_signedMellin q n hq)
    _ = ((vOuterSourceMatrix q n).map Complex.ofRealHom).det := hreal
    _ = ((vSourceMatrix n (-(q : ℤ))).map (vOuterPolynomialEvalHom q)).det := by
      rw [hsource]
      rfl
    _ = vOuterPolynomialEvalHom q (Matrix.det (vSourceMatrix n (-(q : ℤ)))) := by
      have hmap :
          (vSourceMatrix n (-(q : ℤ))).map (vOuterPolynomialEvalHom q) =
            (vOuterPolynomialEvalHom q).mapMatrix
              (vSourceMatrix n (-(q : ℤ))) := rfl
      rw [hmap]
      exact hpoly.symm
    _ = Literal.vContourGValue q n := by
      rfl

/-- Frozen `q=2` regression of the literal-to-polynomial determinant
adapter (`v-arithmetic.tex:32-35`, `v-analytic.tex:71-83`). -/
theorem vOuterMomentMatrix_det_eq_vContourGValue_q2 (n : ℕ) :
    Complex.ofReal ((vOuterMomentMatrix 2 n).det) =
      Literal.vContourGValue 2 n := by
  exact vOuterMomentMatrix_det_eq_vContourGValue 2 n (by norm_num)

end

end Li2Lean.V

#print axioms Li2Lean.V.vOuterMomentMatrix_det_eq_vContourGValue
#print axioms Li2Lean.V.vOuterMomentMatrix_det_eq_vContourGValue_q2
