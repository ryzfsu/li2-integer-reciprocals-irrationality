/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B3.S0TAssembly
import Li2Lean.B3.H5DzDeterminant
import Li2Lean.V.VLiteralXStage
import Li2Lean.V.VLiteralAndreiefActual

open scoped BigOperators Matrix
open MeasureTheory

namespace Li2Lean.B3

open Li2Lean V

private theorem v13_stage1_cross_sign (n : ℕ)
    (z : Fin (4 * n) → ℂ) (v : Fin (5 * n) → ℂ) :
    (∏ d : Fin (4 * n), ∏ b : Fin (5 * n), (v b - z d)) =
      ∏ d : Fin (4 * n), ∏ b : Fin (5 * n), (z d - v b) := by
  have hev : Even ((4 * n) * (5 * n)) := by
    refine ⟨(2 * n) * (5 * n), ?_⟩
    ring
  calc
    (∏ d : Fin (4 * n), ∏ b : Fin (5 * n), (v b - z d)) =
        ∏ d : Fin (4 * n), ∏ b : Fin (5 * n), -(z d - v b) := by
      apply Finset.prod_congr rfl
      intro d hd
      apply Finset.prod_congr rfl
      intro b hb
      ring
    _ = (-1 : ℂ) ^ ((4 * n) * (5 * n)) *
        (∏ d : Fin (4 * n), ∏ b : Fin (5 * n), (z d - v b)) := by
      simp_rw [Finset.prod_neg]
      simp only [Finset.card_univ, Fintype.card_fin]
      calc
        (∏ d : Fin (4 * n), (-1 : ℂ) ^ (5 * n) *
            ∏ b : Fin (5 * n), (z d - v b)) =
            (∏ d : Fin (4 * n), (-1 : ℂ) ^ (5 * n)) *
              (∏ d : Fin (4 * n), ∏ b : Fin (5 * n), (z d - v b)) := by
                rw [Finset.prod_mul_distrib]
        _ = (-1 : ℂ) ^ ((4 * n) * (5 * n)) *
              (∏ d : Fin (4 * n), ∏ b : Fin (5 * n), (z d - v b)) := by
                rw [Finset.prod_const]
                simp only [Finset.card_univ, Fintype.card_fin]
                rw [← pow_mul]
                congr 1
                ring
    _ = ∏ d : Fin (4 * n), ∏ b : Fin (5 * n), (z d - v b) := by
      rw [hev.neg_one_pow]
      ring

private theorem v13_stage1_zpow_combine (n : ℕ) (z : Fin (4 * n) → ℂ)
    (hz : ∀ d, z d ≠ 0) :
    (∏ d : Fin (4 * n), z d ^ (-(6 * n : ℤ))) *
        (∏ d : Fin (4 * n), z d ^ (n : ℕ)) =
      ∏ d : Fin (4 * n), z d ^ (-(5 * n : ℤ)) := by
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro d hd
  rw [← zpow_natCast, ← zpow_add₀ (hz d)]
  congr 1
  push_cast
  ring

/-- NEW (`B3a`): Stage-1 contour determinant evaluation for the literal v13 rows. -/
theorem v13Literal_stage1_andreiefProduct_eq (q n : ℕ)
    (v : Fin (5 * n) → ℝ) (p : Fin (4 * n) → Fin 4 × ℝ) :
    let z : Fin (4 * n) → ℂ := fun d => V.Literal.vContourPoint q (p d).1 (p d).2
    let vC : Fin (5 * n) → ℂ := fun b => (v b : ℂ)
    V.andreiefProduct (V.vLiteralContourM1PolynomialRows q n v)
        (V.vLiteralContourA1 q n v) (V.vLiteralContourB1 q n v) p =
      (∏ d : Fin (4 * n), V.Literal.vContourWeight q (p d)) *
        (-1 : ℂ) ^ (Nat.choose (4 * n) 2) *
        (-(q : ℂ)) ^ (∑ k : Fin (4 * n), (2 * n + (k : ℕ))) *
        (V.Literal.vContourVandermonde z) ^ 2 *
        V.Literal.vContourVandermonde vC *
        (∏ d : Fin (4 * n), z d ^ (-(5 * n : ℤ))) *
        (∏ b : Fin (5 * n), vC b ^ n) *
        (∏ d : Fin (4 * n), ∏ b : Fin (5 * n), (z d - vC b)) := by
  classical
  dsimp
  let z : Fin (4 * n) → ℂ := fun d =>
    V.Literal.vContourPoint q (p d).1 (p d).2
  let vC : Fin (5 * n) → ℂ := fun b => (v b : ℂ)
  let A : Matrix (Fin (4 * n)) (Fin (4 * n)) ℂ :=
    Matrix.of fun k d =>
      (-(q : ℂ)) ^ (2 * n + (k : ℕ)) *
        z d ^ (-(2 * n + (k : ℕ) : ℤ) - 1)
  let W : Matrix (Fin (4 * n)) (Fin (4 * n)) ℂ :=
    Matrix.diagonal (fun d => V.Literal.vContourWeight q (p d))
  let C : Matrix (Fin (4 * n) ⊕ Fin (5 * n))
      (Fin (4 * n) ⊕ Fin (5 * n)) ℂ :=
    Matrix.of fun r c =>
      (Sum.elim z vC r) ^
        (Sum.elim (fun k => n + k.val)
          (fun l => n + 4 * n + l.val) c)
  have hAeq :
      Matrix.of (fun k d =>
        V.vLiteralContourA1 q n v k (p d)) = A * W := by
    ext k d
    simp only [A, W, Matrix.mul_apply, Matrix.diagonal_apply,
      Matrix.of_apply]
    rw [Finset.sum_eq_single d]
    · simp only [if_pos rfl, one_mul, if_true]
      change (-(q : ℂ)) ^ (vIIndexNat n k.val) *
          (V.Literal.vContourWeight q (p d) *
            z d ^ (-(vIIndexNat n k.val : ℤ) - 1)) = _
      change (-(q : ℂ)) ^ (2 * n + k.val) *
          (V.Literal.vContourWeight q (p d) *
            z d ^ (-(2 * n + k.val : ℤ) - 1)) = _
      ring
    · intro d' hd' hne
      simp [hne]
    · simp
  have hCeq :
      P0.Env.rowRepl (V.vLiteralContourM1PolynomialRows q n v)
          (fun l => V.vLiteralContourB1 q n v (p l)) = C := by
    ext r c
    cases r with
    | inl k =>
        cases c <;>
          simp [P0.Env.rowRepl, C, z, vC, V.vLiteralContourB1,
            V.vLiteralContourM1PolynomialRows, V.vLiteralContourM1,
            V.vLiteralContourColumnIndex]
    | inr l =>
        cases c <;>
          simp [P0.Env.rowRepl, C, z, vC,
            V.vLiteralContourM1PolynomialRows, V.vLiteralContourM1,
            V.vLiteralContourColumnIndex]
  have hCdet :
      (P0.Env.rowRepl (V.vLiteralContourM1PolynomialRows q n v)
          (fun l => V.vLiteralContourB1 q n v (p l))).det =
        (∏ d : Fin (4 * n), z d ^ n) *
          (∏ b : Fin (5 * n), vC b ^ n) *
          V.Literal.vContourVandermonde z *
          V.Literal.vContourVandermonde vC *
          (∏ d : Fin (4 * n), ∏ b : Fin (5 * n), (vC b - z d)) := by
    rw [hCeq, v13_D_zv_eval]
  by_cases hz : ∀ d, z d ≠ 0
  · have hAdet :
        (Matrix.of (fun k d =>
          V.vLiteralContourA1 q n v k (p d))).det =
          (∏ d : Fin (4 * n), V.Literal.vContourWeight q (p d)) *
            (-1 : ℂ) ^ (Nat.choose (4 * n) 2) *
            (-(q : ℂ)) ^ (∑ k : Fin (4 * n), (2 * n + (k : ℕ))) *
            V.Literal.vContourVandermonde z *
            (∏ d : Fin (4 * n), z d ^ (-(6 * n : ℤ))) := by
      rw [hAeq, Matrix.det_mul, Matrix.det_diagonal]
      rw [v13_D_z_eval q n z hz]
      simp [A]
      ring
    rw [V.andreiefProduct, hAdet, hCdet]
    calc
      _ = (∏ d : Fin (4 * n), V.Literal.vContourWeight q (p d)) *
          (-1 : ℂ) ^ (Nat.choose (4 * n) 2) *
          (-(q : ℂ)) ^ (∑ k : Fin (4 * n), (2 * n + (k : ℕ))) *
          (V.Literal.vContourVandermonde z) ^ 2 *
          V.Literal.vContourVandermonde vC *
          ((∏ d : Fin (4 * n), z d ^ (-(6 * n : ℤ))) *
            (∏ d : Fin (4 * n), z d ^ n)) *
          (∏ b : Fin (5 * n), vC b ^ n) *
          (∏ d : Fin (4 * n), ∏ b : Fin (5 * n), (vC b - z d)) := by ring
      _ = (∏ d : Fin (4 * n), V.Literal.vContourWeight q (p d)) *
          (-1 : ℂ) ^ (Nat.choose (4 * n) 2) *
          (-(q : ℂ)) ^ (∑ k : Fin (4 * n), (2 * n + (k : ℕ))) *
          (V.Literal.vContourVandermonde z) ^ 2 *
          V.Literal.vContourVandermonde vC *
          (∏ d : Fin (4 * n), z d ^ (-(5 * n : ℤ))) *
          (∏ b : Fin (5 * n), vC b ^ n) *
          (∏ d : Fin (4 * n), ∏ b : Fin (5 * n), (vC b - z d)) := by
            rw [v13_stage1_zpow_combine n z hz]
      _ = (∏ d : Fin (4 * n), V.Literal.vContourWeight q (p d)) *
          (-1 : ℂ) ^ (Nat.choose (4 * n) 2) *
          (-(q : ℂ)) ^ (∑ k : Fin (4 * n), (2 * n + (k : ℕ))) *
          (V.Literal.vContourVandermonde z) ^ 2 *
          V.Literal.vContourVandermonde vC *
          (∏ d : Fin (4 * n), z d ^ (-(5 * n : ℤ))) *
          (∏ b : Fin (5 * n), vC b ^ n) *
          (∏ d : Fin (4 * n), ∏ b : Fin (5 * n), (z d - vC b)) := by
            rw [v13_stage1_cross_sign n z vC]
      _ = _ := by
        dsimp [z, vC]
  · obtain ⟨d, hd⟩ := not_forall.mp hz
    have hzeroA :
        (Matrix.of (fun k d =>
          V.vLiteralContourA1 q n v k (p d))).det = 0 := by
      apply Matrix.det_eq_zero_of_column_eq_zero d
      intro k
      have hzd : z d = 0 := by
        by_contra h
        exact hd h
      have hn : 0 < n := by
        by_contra hn0
        have hn0' : n = 0 := Nat.eq_zero_of_not_pos hn0
        subst n
        exact d.elim0
      have hne : (-(2 * n + (k : ℕ) : ℤ) - 1) ≠ 0 := by omega
      change (-(q : ℂ)) ^ (2 * n + (k : ℕ)) *
        (V.Literal.vContourWeight q (p d) *
          V.Literal.vContourPoint q (p d).1 (p d).2 ^
            (-(2 * n + (k : ℕ) : ℤ) - 1)) = 0
      have hzd' : V.Literal.vContourPoint q (p d).1 (p d).2 = 0 := by
        simpa [z] using hzd
      rw [hzd', zero_zpow _ hne]
      ring
    have hzeroR :
        (∏ d : Fin (4 * n), z d ^ (-(5 * n : ℤ))) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ d)
      have hn : 0 < n := by
        by_contra hn0
        have hn0' : n = 0 := Nat.eq_zero_of_not_pos hn0
        subst n
        exact d.elim0
      have hne : (-(5 * n : ℤ)) ≠ 0 := by omega
      have hzd : z d = 0 := by
        by_contra h
        exact hd h
      rw [hzd, zero_zpow _ hne]
    unfold V.andreiefProduct
    rw [hzeroA]
    have hzeroR' :
        (∏ d : Fin (4 * n),
          (V.Literal.vContourPoint q (p d).1 (p d).2) ^ (-(5 * n : ℤ))) = 0 := by
      simpa [z] using hzeroR
    rw [hzeroR']
    simp

/-! ## Stage-2 support branches

The Cauchy--Vandermonde determinant evaluation requires injective nodes,
but the support conditions alone do not imply injectivity.  These helpers
close the complementary repeated-node and zero-node branches by the
alternating determinant itself. -/

theorem duplicate_monomial_det_zero {n : ℕ} (x : Fin (4 * n) → ℝ)
    (i j : Fin (4 * n)) (hij : i ≠ j) (hval : x i = x j) :
    (Matrix.of (fun k l => V.literalXMonomial n k (x l))).det = 0 := by
  apply Matrix.det_zero_of_column_eq hij
  intro k
  change (x i : ℂ) ^ (2 * n + k.val) = (x j : ℂ) ^ (2 * n + k.val)
  rw [hval]

theorem duplicate_vandermonde_zero {n : ℕ} (x : Fin (4 * n) → ℝ)
    (i j : Fin (4 * n)) (hij : i ≠ j) (hval : x i = x j) :
    V.Literal.vContourVandermonde (fun l => (x l : ℂ)) = 0 := by
  rw [V.vContourVandermonde_eq_det]
  apply Matrix.det_zero_of_row_eq hij
  funext k
  simp [Matrix.vandermonde, hval]

theorem zero_monomial_det_zero {n : ℕ} (x : Fin (4 * n) → ℝ)
    (i : Fin (4 * n)) (hval : x i = 0) :
    (Matrix.of (fun k l => V.literalXMonomial n k (x l))).det = 0 := by
  rw [V.literalXMonomialMatrix_det]
  apply mul_eq_zero.mpr
  right
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  have hi := i.isLt
  have hn : 0 < n := by omega
  have hpow : 2 * n ≠ 0 := by omega
  rw [show (x i : ℂ) = 0 by simp [hval], zero_pow hpow]

theorem duplicate_literal_andreiefProduct_zero {n : ℕ}
    (M : Matrix (Fin (4 * n) ⊕ Fin n) (Fin (4 * n) ⊕ Fin n) ℂ)
    (b : ℝ → (Fin (4 * n) ⊕ Fin n) → ℂ)
    (x : Fin (4 * n) → ℝ) (i j : Fin (4 * n))
    (hij : i ≠ j) (hval : x i = x j) :
    V.andreiefProduct M
      (fun k y => V.literalXMonomial n k y)
      b x = 0 := by
  unfold V.andreiefProduct
  rw [duplicate_monomial_det_zero x i j hij hval]
  simp

theorem zero_literal_andreiefProduct_zero {n : ℕ}
    (M : Matrix (Fin (4 * n) ⊕ Fin n) (Fin (4 * n) ⊕ Fin n) ℂ)
    (b : ℝ → (Fin (4 * n) ⊕ Fin n) → ℂ)
    (x : Fin (4 * n) → ℝ) (i : Fin (4 * n)) (hval : x i = 0) :
    V.andreiefProduct M
      (fun k y => V.literalXMonomial n k y)
      b x = 0 := by
  unfold V.andreiefProduct
  rw [zero_monomial_det_zero x i hval]
  simp

end Li2Lean.B3

#print axioms Li2Lean.B3.v13Literal_stage1_andreiefProduct_eq
