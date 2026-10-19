/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B3.VScaledPencil
import Li2Lean.P0.PositiveTower.BlockDeterminant

/-!
# Index equivalences and 9×9 residue block matrix for the signed-V Frobenius pencil

This module defines the index equivalences and residue block matrix
(v13 `chapters/nonvanishing.tex:221-257`). It defines the column and row
index equivalences `Fin 9 × Fin Q ≃ Fin (V.vMatrixSize Q)` (where the V-block
row index `A = 8` uses `Fin.rev u = Q - 1 - u`) and evaluates the determinant
of the resulting `9 × 9`-block diagonal matrix.
-/

namespace Li2Lean.B3

noncomputable section

open scoped BigOperators
open Matrix
open Li2Lean.P0.PositiveTower

variable {p : ℕ} [Fact (Nat.Prime p)]

/-- Column reindexing `Fin 9 × Fin Q ≃ Fin (V.vMatrixSize Q)` sending
`(B, v) ↦ B * Q + v`. -/
def vColEquiv (Q : ℕ) : Fin 9 × Fin Q ≃ Fin (V.vMatrixSize Q) :=
  finProdFinEquiv.trans (finCongr (by simp [V.vMatrixSize, V.vM, V.vS]; ring))

/-- Involutional row permutation reversing the residue index on the V block
(`A = 8`) so that `u + ℓ = Q` aligns on the diagonal `u = v`. -/
def vResidueRowPerm (Q : ℕ) : Equiv.Perm (Fin 9 × Fin Q) where
  toFun x := (x.1, if x.1 = 8 then Fin.rev x.2 else x.2)
  invFun x := (x.1, if x.1 = 8 then Fin.rev x.2 else x.2)
  left_inv := by
    rintro ⟨A, u⟩
    dsimp only
    split_ifs <;> simp
  right_inv := by
    rintro ⟨A, u⟩
    dsimp only
    split_ifs <;> simp

/-- Row reindexing `Fin 9 × Fin Q ≃ Fin (V.vMatrixSize Q)` obtained by
composing `vResidueRowPerm Q` with `vColEquiv Q`. -/
def vRowEquiv (Q : ℕ) : Fin 9 × Fin Q ≃ Fin (V.vMatrixSize Q) :=
  (vResidueRowPerm Q).trans (vColEquiv Q)

theorem vColEquiv_val (Q : ℕ) (B : Fin 9) (v : Fin Q) :
    (vColEquiv Q (B, v)).val = B.val * Q + v.val := by
  calc
    (vColEquiv Q (B, v)).val = v.val + Q * B.val := rfl
    _ = B.val * Q + v.val := by ring

theorem vRowEquiv_val (Q : ℕ) (A : Fin 9) (u : Fin Q) :
    (vRowEquiv Q (A, u)).val =
      if A.val < 8 then A.val * Q + u.val else 8 * Q + (Q - 1 - u.val) := by
  by_cases hA : A = 8
  · simp [vRowEquiv, vResidueRowPerm, vColEquiv, finProdFinEquiv,
      hA, Fin.rev]
    have hu := u.isLt
    omega
  · have hlt : A.val < 8 := by
      have h9 := A.isLt
      have hne : A.val ≠ 8 := fun h => hA (Fin.ext h)
      omega
    simp [vRowEquiv, vResidueRowPerm, vColEquiv, finProdFinEquiv,
      hA, hlt]
    ring

/-- Per-row Frobenius block scale: `d ^ u` on the 8 C and B rows (`A < 8`)
and `1` on the V row (`A = 8`). -/
def vBlockRowScale {R : Type*} [CommRing R] (d : R) (u : ℕ) (A : Fin 9) : R :=
  if A.val < 8 then d ^ u else 1

/-- The `9 × 9` block-diagonal residue matrix indexed by `Fin 9 × Fin Q`. -/
def vResidueBlockMatrix {R : Type*} [CommRing R]
    (S : Matrix (Fin 9) (Fin 9) R) (d : R) (Q : ℕ) :
    Matrix (Fin 9 × Fin Q) (Fin 9 × Fin Q) R :=
  Matrix.blockDiagonal (fun u : Fin Q => Matrix.diagonal (vBlockRowScale d u.val) * S)

theorem vResidueBlockMatrix_apply {R : Type*} [CommRing R]
    (S : Matrix (Fin 9) (Fin 9) R) (d : R) (Q : ℕ)
    (A B : Fin 9) (u v : Fin Q) :
    vResidueBlockMatrix S d Q (A, u) (B, v) =
      if u = v then vBlockRowScale d u.val A * S A B else 0 := by
  simp only [vResidueBlockMatrix, Matrix.blockDiagonal_apply, Matrix.diagonal_mul]

private theorem prod_vBlockRowScale {R : Type*} [CommRing R] (d : R) (u : ℕ) :
    (∏ A : Fin 9, vBlockRowScale d u A) = d ^ (8 * u) := by
  have hfin : (∏ A : Fin 9, vBlockRowScale d u A) =
      ∏ i ∈ Finset.range 9, (if i < 8 then d ^ u else 1) := by
    simpa [vBlockRowScale] using
      (Fin.prod_univ_eq_prod_range (fun i : ℕ => if i < 8 then d ^ u else 1) 9)
  rw [hfin, Finset.prod_range_succ]
  have h8 : ¬ (8 < 8) := by decide
  simp only [h8, ↓reduceIte, mul_one]
  have hfirst : (∏ i ∈ Finset.range 8, (if i < 8 then d ^ u else 1)) =
      ∏ _i ∈ Finset.range 8, d ^ u := by
    apply Finset.prod_congr rfl
    intro i hi
    have hi8 : i < 8 := Finset.mem_range.mp hi
    simp [hi8]
  rw [hfirst, Finset.prod_const, Finset.card_range, ← pow_mul, Nat.mul_comm]

theorem det_vResidueBlockMatrix {R : Type*} [CommRing R]
    (S : Matrix (Fin 9) (Fin 9) R) (d : R) (Q : ℕ) :
    (vResidueBlockMatrix S d Q).det = d ^ (4 * Q * (Q - 1)) * S.det ^ Q := by
  unfold vResidueBlockMatrix
  rw [Matrix.det_blockDiagonal]
  simp only [Matrix.det_mul, Matrix.det_diagonal, prod_vBlockRowScale]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  rw [Finset.prod_pow_eq_pow_sum]
  have hsum : (∑ u : Fin Q, 8 * u.val) = 8 * (∑ u : Fin Q, u.val) := by
    rw [Finset.mul_sum]
  rw [hsum, Li2Lean.P0.sum_fin_val_mul]
  congr 1
  have hEven : Even (Q * (Q - 1)) := by
    by_cases hQ : Q = 0
    · simp [hQ]
    · have h := Nat.even_mul_succ_self (Q - 1)
      have hsucc : (Q - 1) + 1 = Q := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hQ)
      rw [hsucc, Nat.mul_comm] at h
      exact h
  have hhalf : Q * (Q - 1) / 2 * 2 = Q * (Q - 1) :=
    Nat.div_mul_cancel hEven.two_dvd
  calc
    8 * (Q * (Q - 1) / 2) = 4 * (Q * (Q - 1) / 2 * 2) := by ring
    _ = 4 * (Q * (Q - 1)) := by rw [hhalf]
    _ = 4 * Q * (Q - 1) := by ring

theorem det_vResidueBlockMatrix_tower
    (S : Matrix (Fin 9) (Fin 9) (ZMod p))
    (d : ZMod p) (hd : d ≠ 0) (k : ℕ) :
    (vResidueBlockMatrix S d (p ^ k)).det = S.det ^ (p ^ k) := by
  rw [det_vResidueBlockMatrix, tower_scalar_unit d hd 4 k, one_mul]

theorem det_submatrix_vRow_vCol {R : Type*} [CommRing R] (Q : ℕ)
    (M : Matrix (Fin (V.vMatrixSize Q)) (Fin (V.vMatrixSize Q)) R) :
    (M.submatrix (vRowEquiv Q) (vColEquiv Q)).det =
      (Equiv.Perm.sign (vResidueRowPerm Q) : R) * M.det := by
  have hsub : M.submatrix (vRowEquiv Q) (vColEquiv Q) =
      (M.submatrix (vColEquiv Q) (vColEquiv Q)).submatrix (vResidueRowPerm Q) id := by
    ext r c
    rfl
  rw [hsub, Matrix.det_permute, Matrix.det_submatrix_equiv_self]

end
end Li2Lean.B3
