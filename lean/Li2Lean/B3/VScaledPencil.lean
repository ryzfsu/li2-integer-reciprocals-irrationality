/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B3.ActualFrobeniusBlockEntries

/-!
# Row-scaled signed-V Frobenius pencil and its determinant identity

This module defines the row-scaled pencil and its determinant identity
(v13 `chapters/nonvanishing.tex:214-219). Scaling the `C` and `V` rows by `Q`
and the `B - T A` rows by `Q^2` after substituting `T = X / Q^2` yields
`vScaledPencilMatrix`, whose determinant is `V.vFrobeniusScaledPolynomial`.
-/

namespace Li2Lean.B3

noncomputable section

open scoped BigOperators
open Matrix

/-- v13 `nonvanishing.tex:214-216`: `Q` on `C` and `V` rows, `Q^2` on `B - T A` rows. -/
def vPencilRowScale (Q : ℕ) (r : Fin (V.vMatrixSize Q)) : ℚ :=
  if r.val < V.vM Q then (Q : ℚ)
  else if r.val < 2 * V.vM Q then (Q : ℚ) ^ 2 else (Q : ℚ)

/-- The scaled signed-V pencil `[Q C; Q^2 B - X A; Q V]`. -/
def vScaledPencilMatrix (q Q : ℕ) :
    Matrix (Fin (V.vMatrixSize Q)) (Fin (V.vMatrixSize Q)) (Polynomial ℚ) := fun r c =>
  let a : ℤ := -(q : ℤ)
  let j := V.vJIndex Q c
  if r.val < V.vM Q then
    Polynomial.C ((Q : ℚ) * V.vCEntry a (V.vIIndexNat Q r.val) j)
  else if r.val < 2 * V.vM Q then
    let i := 2 * Q + (r.val - V.vM Q)
    Polynomial.C ((Q : ℚ) ^ 2 * V.vBEntry a i j) -
      Polynomial.X * Polynomial.C (V.vAEntry a i j)
  else
    Polynomial.C ((Q : ℚ) * V.vVEntry j (1 + (r.val - 2 * V.vM Q)))

theorem vPencilRowScale_prod (Q : ℕ) :
    (∏ r : Fin (V.vMatrixSize Q), vPencilRowScale Q r) = (Q : ℚ) ^ (13 * Q) := by
  let f : ℕ → ℚ := fun i =>
    if i < V.vM Q then (Q : ℚ)
    else if i < 2 * V.vM Q then (Q : ℚ) ^ 2 else (Q : ℚ)
  have hFin : (∏ r : Fin (V.vMatrixSize Q), vPencilRowScale Q r) =
      ∏ i ∈ Finset.range (V.vMatrixSize Q), f i := by
    simpa [vPencilRowScale, f] using
      (Fin.prod_univ_eq_prod_range f (V.vMatrixSize Q))
  rw [hFin]
  have hsize : V.vMatrixSize Q = (4 * Q + 4 * Q) + Q := by
    simp [V.vMatrixSize, V.vM, V.vS]
    ring
  rw [hsize, Finset.prod_range_add, Finset.prod_range_add]
  have hfirst : (∏ i ∈ Finset.range (4 * Q), f i) = (Q : ℚ) ^ (4 * Q) := by
    calc
      (∏ i ∈ Finset.range (4 * Q), f i) = ∏ _i ∈ Finset.range (4 * Q), (Q : ℚ) := by
        apply Finset.prod_congr rfl
        intro i hi
        have hi' : i < V.vM Q := by simpa [V.vM] using Finset.mem_range.mp hi
        simp [f, hi']
      _ = (Q : ℚ) ^ (4 * Q) := by simp [Finset.prod_const]
  have hsecond : (∏ i ∈ Finset.range (4 * Q), f (4 * Q + i)) = ((Q : ℚ) ^ 2) ^ (4 * Q) := by
    calc
      (∏ i ∈ Finset.range (4 * Q), f (4 * Q + i)) =
          ∏ _i ∈ Finset.range (4 * Q), (Q : ℚ) ^ 2 := by
        apply Finset.prod_congr rfl
        intro i hi
        have hi' : i < 4 * Q := Finset.mem_range.mp hi
        have hnot1 : ¬ 4 * Q + i < V.vM Q := by simp [V.vM]
        have hlt2 : 4 * Q + i < 2 * V.vM Q := by
          simp [V.vM]
          omega
        simp [f, hnot1, hlt2]
      _ = ((Q : ℚ) ^ 2) ^ (4 * Q) := by simp [Finset.prod_const]
  have hthird : (∏ i ∈ Finset.range Q, f ((4 * Q + 4 * Q) + i)) = (Q : ℚ) ^ Q := by
    calc
      (∏ i ∈ Finset.range Q, f ((4 * Q + 4 * Q) + i)) =
          ∏ _i ∈ Finset.range Q, (Q : ℚ) := by
        apply Finset.prod_congr rfl
        intro i hi
        have hnot1 : ¬ (4 * Q + 4 * Q) + i < V.vM Q := by
          simp [V.vM]
          omega
        have hnot2 : ¬ (4 * Q + 4 * Q) + i < 2 * V.vM Q := by
          simp [V.vM]
          omega
        simp [f, hnot1, hnot2]
      _ = (Q : ℚ) ^ Q := by simp [Finset.prod_const]
  rw [hfirst, hsecond, hthird, ← pow_mul, ← pow_add, ← pow_add]
  congr 1
  ring

/-
  let f : ℕ → ℚ := fun i =>
    if i < V.vM Q then (Q : ℚ)
    else if i < 2 * V.vM Q then (Q : ℚ) ^ 2 else (Q : ℚ)
  have hFin : (∏ r : Fin (V.vMatrixSize Q), vPencilRowScale Q r) =
      ∏ i ∈ Finset.range (V.vMatrixSize Q), f i := by
    simpa [vPencilRowScale, f] using
      (Fin.prod_univ_eq_prod_range f (V.vMatrixSize Q))
  rw [hFin]
  have hsize : V.vMatrixSize Q = V.vM Q + V.vM Q + Q := by
    simp [V.vMatrixSize, V.vM, V.vS]
    ring
  rw [hsize, Finset.prod_range_add]
  have hsplit : V.vM Q + V.vM Q = 2 * V.vM Q := by omega
  rw [Finset.prod_range_add]
  have hfirst : (∏ i ∈ Finset.range (V.vM Q), f i) =
      (Q : ℚ) ^ V.vM Q := by
    calc
      (∏ i ∈ Finset.range (V.vM Q), f i) =
          ∏ _i ∈ Finset.range (V.vM Q), (Q : ℚ) := by
        apply Finset.prod_congr rfl
        intro i hi
        have hi' : i < V.vM Q := Finset.mem_range.mp hi
        simp [f, hi']
      _ = (Q : ℚ) ^ V.vM Q := by simp [Finset.prod_const]
  have hsecond : (∏ i ∈ Finset.range (V.vM Q), f (V.vM Q + i)) =
      ((Q : ℚ) ^ 2) ^ V.vM Q := by
    calc
      (∏ i ∈ Finset.range (V.vM Q), f (V.vM Q + i)) =
          ∏ _i ∈ Finset.range (V.vM Q), (Q : ℚ) ^ 2 := by
        apply Finset.prod_congr rfl
        intro i hi
        have hmi : V.vM Q ≤ V.vM Q + i := Nat.le_add_right _ _
        simp [f, not_lt_of_ge hmi]
      _ = ((Q : ℚ) ^ 2) ^ V.vM Q := by simp [Finset.prod_const]
  have hthird : (∏ i ∈ Finset.range Q, f (2 * V.vM Q + i)) =
      (Q : ℚ) ^ Q := by
    calc
      (∏ i ∈ Finset.range Q, f (2 * V.vM Q + i)) =
          ∏ _i ∈ Finset.range Q, (Q : ℚ) := by
        apply Finset.prod_congr rfl
        intro i hi
        have hmi : 2 * V.vM Q ≤ 2 * V.vM Q + i := Nat.le_add_right _ _
        simp [f, not_lt_of_ge hmi]
      _ = (Q : ℚ) ^ Q := by simp [Finset.prod_const]
  rw [hfirst, hsecond, hthird]
  simp [V.vM]
  ring
-/

theorem vScaledPencilMatrix_eq_diagonal_mul (q Q : ℕ) (hQ : 0 < Q) :
    vScaledPencilMatrix q Q =
      Matrix.diagonal (fun r => Polynomial.C (vPencilRowScale Q r)) *
        (Polynomial.compRingHom
          (Polynomial.C (((Q : ℚ) ^ 2)⁻¹) * Polynomial.X)).mapMatrix
          (V.vSourceMatrix Q (-(q : ℤ))) := by
  ext r c : 1
  rw [Matrix.diagonal_mul]
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Polynomial.coe_compRingHom_apply]
  unfold vScaledPencilMatrix vPencilRowScale V.vSourceMatrix
  by_cases h1 : r.val < V.vM Q
  · simp [h1, Polynomial.C_comp, Polynomial.C_mul]
  · by_cases h2 : r.val < 2 * V.vM Q
    · simp only [h1, h2, ↓reduceIte, Polynomial.sub_comp, Polynomial.C_comp,
        Polynomial.mul_comp, Polynomial.X_comp]
      have hQ2 : ((Q : ℚ) ^ 2) ≠ 0 := by positivity
      rw [mul_sub, Polynomial.C_mul]
      congr 1
      rw [← mul_assoc, ← mul_assoc, ← Polynomial.C_mul, mul_inv_cancel₀ hQ2,
        Polynomial.C_1, one_mul]
    · simp [h1, h2, Polynomial.C_comp, Polynomial.C_mul]

theorem vScaledPencilMatrix_det (q p k : ℕ) (hp : 0 < p) :
    (vScaledPencilMatrix q (p ^ k)).det =
      V.vFrobeniusScaledPolynomial q p k := by
  have hQ : 0 < p ^ k := pow_pos hp k
  rw [vScaledPencilMatrix_eq_diagonal_mul q (p ^ k) hQ,
    Matrix.det_mul, Matrix.det_diagonal, ← RingHom.map_det,
    ← map_prod Polynomial.C, vPencilRowScale_prod]
  rfl

end
end Li2Lean.B3
