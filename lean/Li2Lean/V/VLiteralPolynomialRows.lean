/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.V.VLiteralContourRows

namespace Li2Lean.V

noncomputable section

open MeasureTheory

/- The columns of M0 use the `5n+4n` split, while M1 uses `4n+5n`;
   both encode the same increasing interval J. -/
/-- Column coordinate for the `Fin (5*n) ⊕ Fin (4*n)` split,
`v-arithmetic.tex:15-17` and `v-analytic.tex:127-153`. -/
def vLiteralOuterColumnIndex (n : ℕ)
    (c : Fin (5 * n) ⊕ Fin (4 * n)) : ℕ :=
  Sum.elim (fun l => n + l.val) (fun k => n + 5 * n + k.val) c

/- The outer Andreief column factor is the v13 polynomial row v^j. -/
/-- The v-variable column factor `v^j`, `v-analytic.tex:109-145,139-153`. -/
def vLiteralOuterB0 (n : ℕ) (x : ℝ)
    (c : Fin (5 * n) ⊕ Fin (4 * n)) : ℂ :=
  (x : ℂ) ^ vLiteralOuterColumnIndex n c

/- This is the actual 5n polynomial-row block of the middle matrix M1. -/
/-- The contour-stage matrix with v13 polynomial bottom rows,
`v-analytic.tex:109-145,139-153`. -/
def vLiteralContourM1PolynomialRows (q n : ℕ)
    (v : Fin (5 * n) → ℝ) :
    Matrix (Fin (4 * n) ⊕ Fin (5 * n))
      (Fin (4 * n) ⊕ Fin (5 * n)) ℂ :=
  vLiteralContourM1 q n
    (fun l c => (v l : ℂ) ^ vLiteralContourColumnIndex n c)

/- Reindexing maps preserve the ordinary increasing column number j in J. -/
/-- Select the M1 summand containing the column with flattened index j,
`v-arithmetic.tex:15-17`. -/
def vLiteralM1ColumnOfFin (n : ℕ) (j : Fin (9 * n)) :
    Fin (4 * n) ⊕ Fin (5 * n) :=
  if h : j.val < 4 * n then
    Sum.inl ⟨j.val, h⟩
  else
    Sum.inr ⟨j.val - 4 * n, by omega⟩

/-- Select the M0 summand containing the same flattened column j,
`v-arithmetic.tex:15-17`. -/
def vLiteralM0ColumnOfFin (n : ℕ) (j : Fin (9 * n)) :
    Fin (5 * n) ⊕ Fin (4 * n) :=
  if h : j.val < 5 * n then
    Sum.inl ⟨j.val, h⟩
  else
    Sum.inr ⟨j.val - 5 * n, by omega⟩

/-- M1's split summands flatten to the same J index,
`v-arithmetic.tex:15-17`. -/
theorem vLiteralM1ColumnIndexOfFin (n : ℕ) (j : Fin (9 * n)) :
    vLiteralContourColumnIndex n (vLiteralM1ColumnOfFin n j) = n + j.val := by
  unfold vLiteralContourColumnIndex vLiteralM1ColumnOfFin
  split_ifs with h
  · simp
  · simp
    omega

/-- M0's split summands flatten to the same J index,
`v-arithmetic.tex:15-17`. -/
theorem vLiteralOuterColumnIndexOfFin (n : ℕ) (j : Fin (9 * n)) :
    vLiteralOuterColumnIndex n (vLiteralM0ColumnOfFin n j) = n + j.val := by
  unfold vLiteralOuterColumnIndex vLiteralM0ColumnOfFin
  split_ifs with h
  · simp
  · simp
    omega

/- These entry lemmas give precisely the polynomial rows inserted by rowRepl
   and kept as the bottom rows of M1. -/
/-- The M1 bottom row entry is the v13 monomial `v_b^j`,
`v-analytic.tex:109-145,139-153`. -/
theorem vLiteralContourM1PolynomialRows_bottom_entry (q n : ℕ)
    (v : Fin (5 * n) → ℝ) (l : Fin (5 * n))
    (c : Fin (4 * n) ⊕ Fin (5 * n)) :
    vLiteralContourM1PolynomialRows q n v (Sum.inr l) c =
      (v l : ℂ) ^ vLiteralContourColumnIndex n c := by
  simp [vLiteralContourM1PolynomialRows, vLiteralContourM1]

/-- `rowRepl` inserts the same polynomial row into M0's top block,
`v-analytic.tex:109-145,139-153`. -/
theorem vLiteralRowRepl_outer_polynomial_entry (n : ℕ)
    (M0 : Matrix (Fin (5 * n) ⊕ Fin (4 * n))
      (Fin (5 * n) ⊕ Fin (4 * n)) ℂ)
    (v : Fin (5 * n) → ℝ) (l : Fin (5 * n))
    (c : Fin (5 * n) ⊕ Fin (4 * n)) :
    P0.Env.rowRepl M0 (fun b => vLiteralOuterB0 n (v b))
        (Sum.inl l) c = vLiteralOuterB0 n (v l) c := by
  simp [P0.Env.rowRepl]

/-- The M0 and M1 polynomial-row entries agree at every common column j,
`v-arithmetic.tex:15-17` and `v-analytic.tex:109-145,139-153`. -/
theorem vLiteralOuterB0_eq_contourM1_bottom (n : ℕ)
    (x : ℝ) (j : Fin (9 * n)) :
    vLiteralOuterB0 n x (vLiteralM0ColumnOfFin n j) =
      (x : ℂ) ^ vLiteralContourColumnIndex n (vLiteralM1ColumnOfFin n j) := by
  rw [vLiteralOuterB0, vLiteralOuterColumnIndexOfFin,
    vLiteralM1ColumnIndexOfFin]

/-- The top `rowRepl` entries and M1 bottom entries coincide under the
v13 column coordinate, `v-analytic.tex:109-145,139-153`. -/
theorem vLiteralRowRepl_eq_contourM1_bottom (q n : ℕ)
    (M0 : Matrix (Fin (5 * n) ⊕ Fin (4 * n))
      (Fin (5 * n) ⊕ Fin (4 * n)) ℂ)
    (v : Fin (5 * n) → ℝ) (l : Fin (5 * n)) (j : Fin (9 * n)) :
    P0.Env.rowRepl M0 (fun b => vLiteralOuterB0 n (v b))
        (Sum.inl l) (vLiteralM0ColumnOfFin n j) =
      vLiteralContourM1PolynomialRows q n v (Sum.inr l)
        (vLiteralM1ColumnOfFin n j) := by
  rw [vLiteralRowRepl_outer_polynomial_entry,
    vLiteralContourM1PolynomialRows_bottom_entry]
  exact vLiteralOuterB0_eq_contourM1_bottom n (v l) j

/- The contour integrability and moment theorems now specialize to the
   concrete polynomial-row matrix. -/
/-- The concrete polynomial-row matrix satisfies the contour integrability
field, `v-analytic.tex:87-104,109-145`. -/
theorem vLiteralContourM1PolynomialRows_hint1 (q n : ℕ) (hq : 2 ≤ q)
    (v : Fin (5 * n) → ℝ) (k : Fin (4 * n))
    (c : Fin (4 * n) ⊕ Fin (5 * n)) :
    Integrable
      (fun p => vLiteralContourA1 q n v k p * vLiteralContourB1 q n v p c)
      Literal.vContourParameterMeasure :=
  vLiteralContourA1B1_integrable q n hq v k c

/-- The concrete M1 C rows satisfy hmom1 for every q>=2,
`v-arithmetic.tex:24-27` and `v-analytic.tex:96-104,127-153`. -/
theorem vLiteralContourM1PolynomialRows_hmom1 (q n : ℕ) (hq : 2 ≤ q)
    (v : Fin (5 * n) → ℝ) (k : Fin (4 * n))
    (c : Fin (4 * n) ⊕ Fin (5 * n)) :
    vLiteralContourM1PolynomialRows q n v (Sum.inl k) c =
      ∫ p, vLiteralContourA1 q n v k p * vLiteralContourB1 q n v p c
        ∂Literal.vContourParameterMeasure := by
  simpa [vLiteralContourM1PolynomialRows] using
    vLiteralContourM1_hmom1 q n hq
      (fun l c => (v l : ℂ) ^ vLiteralContourColumnIndex n c) v k c

/- q=2 remains the same signed C block in the frozen Li2(1/2) instance. -/
/-- Frozen q=2 regression for the concrete polynomial-row M1,
`v-arithmetic.tex:24-27` and `v-analytic.tex:96-104`. -/
theorem vLiteralContourM1PolynomialRows_hmom1_q2 (n : ℕ)
    (v : Fin (5 * n) → ℝ) (k : Fin (4 * n))
    (c : Fin (4 * n) ⊕ Fin (5 * n)) :
    vLiteralContourM1PolynomialRows 2 n v (Sum.inl k) c =
      ∫ p, vLiteralContourA1 2 n v k p * vLiteralContourB1 2 n v p c
        ∂Literal.vContourParameterMeasure :=
  vLiteralContourM1PolynomialRows_hmom1 2 n (by norm_num) v k c

end

end Li2Lean.V

#print axioms Li2Lean.V.vLiteralContourM1PolynomialRows_bottom_entry
#print axioms Li2Lean.V.vLiteralRowRepl_outer_polynomial_entry
#print axioms Li2Lean.V.vLiteralRowRepl_eq_contourM1_bottom
#print axioms Li2Lean.V.vLiteralContourM1PolynomialRows_hint1
#print axioms Li2Lean.V.vLiteralContourM1PolynomialRows_hmom1
#print axioms Li2Lean.V.vLiteralContourM1PolynomialRows_hmom1_q2
