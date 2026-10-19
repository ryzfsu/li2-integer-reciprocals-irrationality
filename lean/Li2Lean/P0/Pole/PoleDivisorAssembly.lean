/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.Pole.EntryOrders
import Li2Lean.P0.Pole.ForwardDifferenceTransform
import Li2Lean.P0.Pole.SeparableOrder
import Li2Lean.P0.Pole.MatrixCore

namespace Li2Lean.P0.Pole

open Polynomial Matrix Li2Lean.P0.Integerization
open Li2Lean.P0.PoleMatrixCore

noncomputable section

/--
Algebraic assembly of the P0 pole divisor.  `N` is the matrix obtained after
the row/column forward-difference transform and the top-row `X^h` scaling.
The concrete entry-order proof and the top-row determinant calculation are
kept as hypotheses so this theorem can be reused by the matrix construction.
The transform and pole-matrix identities are then applied here, and the
extra `X^(4*h^2)` from the scaled top rows is cancelled in the domain.
-/
theorem shifted_pole_det_dvd_of_entry_orders
    (h : ℕ)
    (N : Matrix (Fin (8 * h)) (Fin (8 * h)) BivPoly)
    (e f : Fin (8 * h) → ℕ)
    (hN : ∀ r c, (Polynomial.X : BivPoly) ^ (e r + f c) ∣ N r c)
    (hsum : (∑ r, e r) + ∑ c, f c = 11 * h ^ 2 + 3 * h)
    (hdet : Matrix.det N =
      (Polynomial.X : BivPoly) ^ (4 * h ^ 2) *
        shiftB (Matrix.det
          ((algebraMap ℚ BivPoly).mapMatrix (poleRowDiffMatrix (4 * h)) *
            poleMatrix (4 * h) *
            (algebraMap ℚ BivPoly).mapMatrix
              (forwardDiffMatrix (2 * (4 * h))).transpose))) :
    (Polynomial.X : BivPoly) ^ (7 * h ^ 2 + 3 * h) ∣
      shiftB (Matrix.det (poleMatrix (4 * h))) := by
  have hdiv := separable_order_dvd_det N e f hN
  rw [hsum, hdet, det_poleForwardDifferenceTransform,
    det_poleMatrix_eq] at hdiv
  rcases hdiv with ⟨q, hq⟩
  have hhalf : 4 * h / 2 = 2 * h := by omega
  let A : BivPoly := (Polynomial.X : BivPoly) ^ (4 * h ^ 2)
  let B : BivPoly := (Polynomial.X : BivPoly) ^ (7 * h ^ 2 + 3 * h)
  have hpow : (Polynomial.X : BivPoly) ^ (11 * h ^ 2 + 3 * h) = A * B := by
    dsimp [A, B]
    rw [← pow_add]
    congr 1
    ring
  have heq : A * shiftB (tScale (2 * h) (formalCanonicalPolynomial (4 * h))) =
      A * (B * q) := by
    calc
      A * shiftB (tScale (2 * h) (formalCanonicalPolynomial (4 * h))) =
          (Polynomial.X : BivPoly) ^ (11 * h ^ 2 + 3 * h) * q := by
            simpa [A, hhalf] using hq
      _ = (A * B) * q := by rw [hpow]
      _ = A * (B * q) := by ring
  have hcancel :
      shiftB (tScale (2 * h) (formalCanonicalPolynomial (4 * h))) = B * q :=
    mul_left_cancel₀ (pow_ne_zero _ (by simp [A])) heq
  refine ⟨q, ?_⟩
  simpa [B, det_poleMatrix_eq, hhalf] using hcancel

end

end Li2Lean.P0.Pole
