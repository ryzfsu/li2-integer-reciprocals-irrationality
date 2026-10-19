/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.PencilAlgebra

/-!
# Evaluation of the parameterized P0 scaled pencil

Reuse `PencilAlgebra.p0_scaled_pencil_det` and the evaluation step of
`NonvanishingTowerProducer.p0A2ScaledMatrix_det_eq_source_eval` for arbitrary
base, seed index, and scaling factor. Source: v13
`chapters/nonvanishing.tex:200-258` (the rational pencil identity).
-/
namespace Li2Lean.P0.PositiveTower

/-- Evaluating the literal scaled pencil at `Q²r` recovers the same source
at `r`, including the exact determinant normalization `Q^(3m)`. -/
theorem scaledPencil_det_eval (a : ℤ) (m Q : ℕ)
    (hm : 4 ∣ m) (hQ : Q ≠ 0) (r : ℚ) :
    Matrix.det ((p0ScaledPencilMatrixQ (a : ℚ) m Q).map
      (fun f => f.eval ((Q : ℚ) ^ 2 * r))) =
      (Q : ℚ) ^ (3 * m) * (p0CanonicalPolynomial a m).eval r := by
  have hQrat : (Q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hQ
  have hcomp :
      (Polynomial.evalRingHom ((Q : ℚ) ^ 2 * r)).comp
        (Polynomial.eval₂RingHom Polynomial.C (p0PencilSubstitution Q)) =
      Polynomial.evalRingHom r := by
    apply Polynomial.ringHom_ext
    · intro c
      simp [RingHom.comp_apply]
    · simp only [RingHom.comp_apply, Polynomial.evalRingHom,
        Polynomial.eval₂RingHom]
      simp [p0PencilSubstitution]
      field_simp [hQrat]
  have hsubEval :
      (Polynomial.eval₂RingHom Polynomial.C (p0PencilSubstitution Q)
        (p0CanonicalPolynomial a m)).eval ((Q : ℚ)^2 * r) =
      (p0CanonicalPolynomial a m).eval r := by
    change ((Polynomial.evalRingHom ((Q : ℚ)^2 * r)).comp
      (Polynomial.eval₂RingHom Polynomial.C (p0PencilSubstitution Q)))
      (p0CanonicalPolynomial a m) = _
    rw [hcomp]
    rfl
  have hmat := (RingHom.map_det
    (Polynomial.evalRingHom ((Q : ℚ)^2 * r))
    (p0ScaledPencilMatrixQ (a : ℚ) m Q)).symm
  change Matrix.det ((p0ScaledPencilMatrixQ (a : ℚ) m Q).map
      (fun f => f.eval ((Q : ℚ)^2 * r))) =
    (Matrix.det (p0ScaledPencilMatrixQ (a : ℚ) m Q)).eval
      ((Q : ℚ)^2 * r) at hmat
  rw [hmat, p0_scaled_pencil_det a m Q hm hQ,
    Polynomial.eval_mul, Polynomial.eval_C, hsubEval]

/-- The same identity with the construction pinned by its P0 family. -/
theorem scaledPencil_det_source_eval (F : P0Family) (m Q : ℕ)
    (hm : 4 ∣ m) (hQ : Q ≠ 0) (r : ℚ) :
    Matrix.det ((p0ScaledPencilMatrixQ (F.a : ℚ) m Q).map
      (fun f => f.eval ((Q : ℚ)^2 * r))) =
      (Q : ℚ)^(3 * m) * p0SourceEvalQ F m r :=
  scaledPencil_det_eval F.a m Q hm hQ r

end Li2Lean.P0.PositiveTower
