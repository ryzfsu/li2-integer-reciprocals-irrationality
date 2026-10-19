/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/

import Li2Lean.V.CauchyVandermonde
import Mathlib.LinearAlgebra.Vandermonde

namespace Li2Lean.V

noncomputable section

open Matrix
open scoped BigOperators

/-!
Finite determinant evaluations for the two Laurent/power blocks in
`source/chapters/v-analytic.tex:150-156`.

The definitions keep the row and column order of the manuscript.  The
determinant identities are stated first in the factored matrix form used by
the later Andreief assembly; no contour or moment assumptions are bundled
into these finite algebraic lemmas.
-/

/-! ### The `D_z` block -/

/- The unscaled negative-power block used below. -/
def dzNegativeMatrix (n : ℕ) (z : Fin (4 * n) → ℂ) :
    Matrix (Fin (4 * n)) (Fin (4 * n)) ℂ :=
  Matrix.of (fun r d => z d ^ (-((2 * n + r.val + 1 : ℕ) : ℤ)))

/-- The Laurent row block `I = [2n,6n)` with the signed row factor `(-q)^i`.
The exponent is represented by `zpow` so that the definition also records the
negative powers at the matrix-entry level. -/
def dzMatrix (n : ℕ) (q : ℂ) (z : Fin (4 * n) → ℂ) :
    Matrix (Fin (4 * n)) (Fin (4 * n)) ℂ :=
  Matrix.diagonal (fun r : Fin (4 * n) => (-q) ^ (2 * n + r.val)) *
    dzNegativeMatrix n z

theorem dzMatrix_apply (n : ℕ) (q : ℂ) (z : Fin (4 * n) → ℂ)
    (r d : Fin (4 * n)) :
    dzMatrix n q z r d =
      (-q) ^ (2 * n + r.val) *
        z d ^ (-((2 * n + r.val + 1 : ℕ) : ℤ)) := by
  classical
  simp only [dzMatrix, dzNegativeMatrix, Matrix.mul_apply, Matrix.diagonal,
    Matrix.of_apply]
  rw [Finset.sum_eq_single r]
  · change (if r = r then (-q) ^ (2 * n + r.val) else 0) *
      z d ^ (-((2 * n + r.val + 1 : ℕ) : ℤ)) = _
    simp only [if_true, one_mul]
  · intro k hk hkr
    have hrk : r ≠ k := Ne.symm hkr
    simp [hrk]
  · intro hr
    exact (hr (Finset.mem_univ r)).elim

theorem dzNegativeMatrix_eq_inverseVandermonde (n : ℕ)
    (z : Fin (4 * n) → ℂ) (hz : ∀ d, z d ≠ 0) :
    dzNegativeMatrix n z =
      (Matrix.vandermonde (fun d => (z d)⁻¹))ᵀ *
        Matrix.diagonal (fun d => (z d)⁻¹ ^ (2 * n + 1)) := by
  ext r d
  simp only [dzNegativeMatrix, Matrix.mul_apply]
  change z d ^ (-((2 * n + r.val + 1 : ℕ) : ℤ)) = _
  simp only [Matrix.transpose_apply, Matrix.vandermonde, Matrix.diagonal,
    Matrix.of_apply]
  rw [Finset.sum_eq_single d]
  · simp only [if_pos rfl, mul_one]
    calc
      z d ^ (-((2 * n + r.val + 1 : ℕ) : ℤ)) =
          (z d ^ (2 * n + r.val + 1 : ℕ))⁻¹ := by
            rw [_root_.zpow_neg, zpow_natCast]
      _ = (z d)⁻¹ ^ (2 * n + r.val + 1) := by rw [← inv_pow]
      _ = (z d)⁻¹ ^ r.val * (z d)⁻¹ ^ (2 * n + 1) := by
        simp [pow_add, mul_comm, mul_left_comm, mul_assoc]
  · intro k hk hkd
    simp [hkd]
  · intro hd
    exact (hd (Finset.mem_univ _)).elim

theorem det_dzNegativeMatrix (n : ℕ) (z : Fin (4 * n) → ℂ)
    (hz : ∀ d, z d ≠ 0) :
    (dzNegativeMatrix n z).det =
      (∏ d : Fin (4 * n), (z d)⁻¹ ^ (2 * n + 1)) *
        (Matrix.vandermonde (fun d => (z d)⁻¹)).det := by
  rw [dzNegativeMatrix_eq_inverseVandermonde n z hz]
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal]
  rw [mul_comm]

/- The direct determinant form is useful to downstream assembly because it
keeps the row factor separate from the Laurent Vandermonde factor. -/
theorem det_dzMatrix_inverse (n : ℕ) (q : ℂ) (z : Fin (4 * n) → ℂ)
    (hz : ∀ d, z d ≠ 0) :
    (dzMatrix n q z).det =
      (∏ r : Fin (4 * n), (-q) ^ (2 * n + r.val)) *
        (∏ d : Fin (4 * n), (z d)⁻¹ ^ (2 * n + 1)) *
          (Matrix.vandermonde (fun d => (z d)⁻¹)).det := by
  rw [dzMatrix, Matrix.det_mul, Matrix.det_diagonal]
  rw [det_dzNegativeMatrix n z hz]
  ring

/-! ### The `D_{zv}` block -/

/-- The concatenated point vector `w=(z_1,...,z_m,v_1,...,v_L)` in v13. -/
def dzvPoints (n : ℕ) (z : Fin (4 * n) → ℂ) (v : Fin (5 * n) → ℂ) :
    Fin (4 * n + 5 * n) → ℂ := Fin.append z v

/-- The shifted power matrix with exponents `J=[n,10n)`. -/
def dzvMatrix (n : ℕ) (z : Fin (4 * n) → ℂ) (v : Fin (5 * n) → ℂ) :
    Matrix (Fin (4 * n + 5 * n)) (Fin (4 * n + 5 * n)) ℂ :=
  Matrix.of (fun b j => dzvPoints n z v b ^ (n + j.val))

theorem dzvMatrix_apply (n : ℕ) (z : Fin (4 * n) → ℂ) (v : Fin (5 * n) → ℂ)
    (b j : Fin (4 * n + 5 * n)) :
    dzvMatrix n z v b j = dzvPoints n z v b ^ (n + j.val) := by
  rfl

theorem dzvMatrix_eq_diagonal_mul_vandermonde (n : ℕ)
    (z : Fin (4 * n) → ℂ) (v : Fin (5 * n) → ℂ) :
    dzvMatrix n z v =
      Matrix.diagonal (fun b => dzvPoints n z v b ^ n) *
        Matrix.vandermonde (dzvPoints n z v) := by
  ext b j
  simp only [dzvMatrix, Matrix.mul_apply, Matrix.diagonal,
    Matrix.vandermonde, Matrix.of_apply]
  rw [Finset.sum_eq_single b]
  · simp [pow_add]
  · intro k hk hkb
    have hbk : b ≠ k := Ne.symm hkb
    simp [hbk]
  · intro hb
    exact (hb (Finset.mem_univ _)).elim

theorem det_dzvMatrix (n : ℕ) (z : Fin (4 * n) → ℂ) (v : Fin (5 * n) → ℂ) :
    (dzvMatrix n z v).det =
      (∏ b : Fin (4 * n + 5 * n), dzvPoints n z v b ^ n) *
        (Matrix.vandermonde (dzvPoints n z v)).det := by
  rw [dzvMatrix_eq_diagonal_mul_vandermonde, Matrix.det_mul,
    Matrix.det_diagonal]

theorem det_dzvMatrix_expanded (n : ℕ) (z : Fin (4 * n) → ℂ)
    (v : Fin (5 * n) → ℂ) :
    (dzvMatrix n z v).det =
      (∏ d : Fin (4 * n), z d ^ n) *
        (∏ b : Fin (5 * n), v b ^ n) *
        (Matrix.vandermonde z).det *
        (Matrix.vandermonde v).det *
        (∏ d : Fin (4 * n), ∏ b : Fin (5 * n), (v b - z d)) := by
  rw [det_dzvMatrix]
  have hpow :
      (∏ b : Fin (4 * n + 5 * n), dzvPoints n z v b ^ n) =
        (∏ d : Fin (4 * n), z d ^ n) *
          (∏ b : Fin (5 * n), v b ^ n) := by
    simp only [dzvPoints, Fin.prod_univ_add, Fin.append_left, Fin.append_right]
  rw [hpow, Matrix.det_vandermonde]
  change _ *
      (∏ i : Fin (4 * n + 5 * n),
        ∏ j ∈ Finset.Ioi i,
          (Fin.append z v j - Fin.append z v i)) = _
  rw [Li2Lean.P0.CauchyDeterminant.vandermonde_append_product]
  rw [← Matrix.det_vandermonde z, ← Matrix.det_vandermonde v]
  ring

/- The cross factor can be presented in the orientation used in the paper. -/
theorem det_dzvMatrix_source_form (n : ℕ) (z : Fin (4 * n) → ℂ)
    (v : Fin (5 * n) → ℂ) :
    (dzvMatrix n z v).det =
      (-1 : ℂ) ^ ((4 * n) * (5 * n)) *
        (∏ d : Fin (4 * n), z d ^ n) *
        (∏ b : Fin (5 * n), v b ^ n) *
        (Matrix.vandermonde z).det *
        (Matrix.vandermonde v).det *
        (∏ d : Fin (4 * n), ∏ b : Fin (5 * n), (z d - v b)) := by
  rw [det_dzvMatrix_expanded]
  have hcross :
      (∏ d : Fin (4 * n), ∏ b : Fin (5 * n), (v b - z d)) =
        (-1 : ℂ) ^ ((4 * n) * (5 * n)) *
          (∏ d : Fin (4 * n), ∏ b : Fin (5 * n), (z d - v b)) := by
    calc
      (∏ d : Fin (4 * n), ∏ b : Fin (5 * n), (v b - z d)) =
          ∏ d : Fin (4 * n), ∏ b : Fin (5 * n), (-(z d - v b)) := by
            apply Finset.prod_congr rfl
            intro d hd
            apply Finset.prod_congr rfl
            intro b hb
            ring
      _ = (∏ d : Fin (4 * n), ∏ b : Fin (5 * n), (-1 : ℂ)) *
          (∏ d : Fin (4 * n), ∏ b : Fin (5 * n), (z d - v b)) := by
            have hneg :
                (∏ d : Fin (4 * n), ∏ b : Fin (5 * n), (-(z d - v b))) =
                  ∏ d : Fin (4 * n), ∏ b : Fin (5 * n),
                    ((-1 : ℂ) * (z d - v b)) := by
              apply Finset.prod_congr rfl
              intro d hd
              apply Finset.prod_congr rfl
              intro b hb
              exact neg_eq_neg_one_mul (z d - v b)
            rw [hneg]
            simp_rw [Finset.prod_mul_distrib]
      _ = (-1 : ℂ) ^ ((4 * n) * (5 * n)) *
          (∏ d : Fin (4 * n), ∏ b : Fin (5 * n), (z d - v b)) := by
            simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
            rw [← pow_mul]
            congr 1
            ring
  rw [hcross]
  ring

/-! Compatibility names for the v13 assembly layer.  They are aliases only;
the determinant proofs above remain the source-facing API. -/
abbrev v13D_zMatrix := dzMatrix
abbrev v13D_zvMatrix := dzvMatrix

theorem det_v13D_zMatrix (n : ℕ) (q : ℂ) (z : Fin (4 * n) → ℂ)
    (hz : ∀ d, z d ≠ 0) :
    (v13D_zMatrix n q z).det =
      (∏ r : Fin (4 * n), (-q) ^ (2 * n + r.val)) *
        (∏ d : Fin (4 * n), (z d)⁻¹ ^ (2 * n + 1)) *
          (Matrix.vandermonde (fun d => (z d)⁻¹)).det := by
  exact det_dzMatrix_inverse n q z hz

theorem det_v13D_zvMatrix (n : ℕ) (z : Fin (4 * n) → ℂ)
    (v : Fin (5 * n) → ℂ) :
    (v13D_zvMatrix n z v).det =
      (-1 : ℂ) ^ ((4 * n) * (5 * n)) *
        (∏ d : Fin (4 * n), z d ^ n) *
        (∏ b : Fin (5 * n), v b ^ n) *
        (Matrix.vandermonde z).det *
        (Matrix.vandermonde v).det *
        (∏ d : Fin (4 * n), ∏ b : Fin (5 * n), (z d - v b)) := by
  exact det_dzvMatrix_source_form n z v

end
end Li2Lean.V

#print axioms Li2Lean.V.det_dzMatrix_inverse
#print axioms Li2Lean.V.det_dzvMatrix_expanded
