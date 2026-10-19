/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Li2Lean.V.CauchyVandermonde

/-!
# The `D_x` and `D_{xv}` determinant evaluations

This module records the two finite determinant identities used in the
`v-analytic.tex:157-163` block.  The Cauchy--Vandermonde calculation is
delegated to `Li2Lean.V.CauchyVandermonde`; the only extra bookkeeping is the
row scaling for `t_i = q / x_i` and the common monomial shift in `D_x`.
-/

namespace Li2Lean.V

noncomputable section

open Matrix

/-! ## The `D_x` Vandermonde block -/

/-- Matrix with row exponents `r₀, r₀+1, ..., r₀+m-1`.

For the v13 choice `r₀ = 2*n` and `m = 4*n`, this is exactly the matrix
`(x_{i'}^i)_{i in I,i'}` from `v-analytic.tex:157`. -/
def vDxMatrix {m : ℕ} (r₀ : ℕ) (x : Fin m → ℂ) :
    Matrix (Fin m) (Fin m) ℂ :=
  Matrix.of fun i j => (x j) ^ (r₀ + i.val)

/-- The common column factor in the shifted Vandermonde matrix. -/
def vDxColumnScale {m : ℕ} (r₀ : ℕ) (x : Fin m → ℂ) :
    Fin m → ℂ := fun j => (x j) ^ r₀

/-- The shifted monomial matrix is a transposed Vandermonde times a diagonal
column scaling. -/
theorem vDxMatrix_eq_vandermonde_transpose_mul_diagonal
    {m : ℕ} (r₀ : ℕ) (x : Fin m → ℂ) :
    vDxMatrix r₀ x =
      (Matrix.vandermonde x).transpose * Matrix.diagonal (vDxColumnScale r₀ x) := by
  classical
  ext i j
  simp only [vDxMatrix, vDxColumnScale, Matrix.mul_apply,
    Matrix.diagonal_apply, Matrix.transpose_apply, Matrix.of_apply]
  rw [Finset.sum_eq_single j]
  · simp [Matrix.vandermonde, pow_add, mul_comm]
  · intro k hk hne
    simp [hne]
  · simp

/-- The `D_x` determinant evaluation from `v-analytic.tex:157`. -/
theorem det_vDxMatrix {m : ℕ} (r₀ : ℕ) (x : Fin m → ℂ) :
    (vDxMatrix r₀ x).det =
      (Matrix.vandermonde x).det * ∏ j : Fin m, (x j) ^ r₀ := by
  rw [vDxMatrix_eq_vandermonde_transpose_mul_diagonal,
    Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal]
  simp [vDxColumnScale]

/-! ## The `D_{xv}` Cauchy--Vandermonde block -/

/-- Row scaling used for `t_i = q/x_i`: the first `m` rows are multiplied by
`x_i⁻¹`, while the polynomial rows are unchanged. -/
def vDxvRowScale {m h : ℕ}
    (x : Fin m → ℂ) : Fin (m + h) → ℂ :=
  fun s => match (finSumFinEquiv (m := m) (n := h)).symm s with
    | Sum.inl i => (x i)⁻¹
    | Sum.inr _ => 1

/-- The literal Cauchy--Vandermonde matrix from `v-analytic.tex:158-163`. -/
def vDxvMatrix {m h : ℕ}
    (q : ℂ) (x : Fin m → ℂ) (v : Fin (m + h) → ℂ) :
    Matrix (Fin (m + h)) (Fin (m + h)) ℂ :=
  fun s b => match (finSumFinEquiv (m := m) (n := h)).symm s with
    | Sum.inl i => (q + x i * v b)⁻¹
    | Sum.inr k => v b ^ (k : ℕ)

/-- The row-scale product has one factor for each rational row. -/
theorem vDxvRowScale_prod {m h : ℕ} (x : Fin m → ℂ) :
    (∏ s : Fin (m + h), vDxvRowScale x s) =
      ∏ i : Fin m, (x i)⁻¹ := by
  classical
  calc
    (∏ s : Fin (m + h), vDxvRowScale x s) =
        ∏ s : Fin m ⊕ Fin h, (match s with
          | Sum.inl i => (x i)⁻¹
          | Sum.inr _ => 1) := by
      apply Fintype.prod_equiv (finSumFinEquiv (m := m) (n := h)).symm
      intro s
      rfl
    _ = ∏ i : Fin m, (x i)⁻¹ := by simp

/-- The literal rows are a diagonal row scaling of the generic Cauchy--
Vandermonde matrix. -/
theorem vDxvMatrix_eq_diagonal_mul_cvMatrix
    {m h : ℕ}
    (q : ℂ) (x : Fin m → ℂ) (v : Fin (m + h) → ℂ)
    (hx : ∀ i, x i ≠ 0) :
    vDxvMatrix q x v =
      Matrix.diagonal (vDxvRowScale x) *
        CauchyVandermonde.cvMatrix (fun i => q / x i) v := by
  classical
  ext s b
  simp only [vDxvMatrix, Matrix.mul_apply, Matrix.diagonal,
    vDxvRowScale, CauchyVandermonde.cvMatrix, Matrix.of_apply]
  rw [Finset.sum_eq_single s]
  · simp only [if_true, one_mul]
    cases hs : (finSumFinEquiv (m := m) (n := h)).symm s with
    | inl i =>
        change (q + x i * v b)⁻¹ =
          (x i)⁻¹ * (q / x i + v b)⁻¹
        field_simp [hx i]
    | inr k =>
        simp [CauchyVandermonde.cvEntry]
  · intro s' hs' hne
    have hne' : ¬ s = s' := Ne.symm hne
    simp [hne']
  · intro hs
    exact (hs (Finset.mem_univ s)).elim

/-- Generic Cauchy--Vandermonde evaluation in the `q/x` coordinates. -/
theorem det_vDxvMatrix_q_over_x
    {m h : ℕ}
    (q : ℂ) (x : Fin m → ℂ) (v : Fin (m + h) → ℂ)
    (hx : ∀ i, x i ≠ 0)
    (ht : Function.Injective (fun i => q / x i))
    (hxy : ∀ i b, q / x i + v b ≠ 0) :
    (vDxvMatrix q x v).det =
      (∏ s : Fin (m + h), vDxvRowScale x s) *
        (Matrix.vandermonde v).det *
          (Matrix.vandermonde (fun i => q / x i)).det *
            (∏ i : Fin m, ∏ b : Fin (m + h),
              (q / x i + v b))⁻¹ := by
  rw [vDxvMatrix_eq_diagonal_mul_cvMatrix q x v hx,
    Matrix.det_mul, Matrix.det_diagonal]
  change (∏ s : Fin (m + h), vDxvRowScale x s) *
      (CauchyVandermonde.cvQXMatrix q x v).det = _
  rw [CauchyVandermonde.cvQX_det_eq_vandermonde_mul_inv_denominator
    q x v ht hxy]
  ring

/-!
The next lemma is the inversion of the Vandermonde under `x ↦ q/x`.
Clearing the coordinate powers avoids any negative natural exponents and is
the form used to pass from the generic Cauchy--Vandermonde quotient to the
paper's `D_{xv}` formula.
-/

/-- Cleared-denominator `D_{xv}` evaluation in paper coordinates. -/
theorem det_vDxvMatrix_mul_denominator
    {m h : ℕ}
    (q : ℂ) (x : Fin m → ℂ) (v : Fin (m + h) → ℂ)
    (hq : q ≠ 0) (hx : ∀ i, x i ≠ 0)
    (hinj : Function.Injective x)
    (hden : ∀ i b, q + x i * v b ≠ 0) :
    (vDxvMatrix q x v).det *
        (∏ i : Fin m, ∏ b : Fin (m + h), (q + x i * v b)) =
      (∏ s : Fin (m + h), vDxvRowScale x s) *
        (∏ i : Fin m, (x i) ^ (m + h)) *
          (Matrix.vandermonde v).det *
            (Matrix.vandermonde (fun i => q / x i)).det := by
  classical
  let t : Fin m → ℂ := fun i => q / x i
  let p : ℂ := ∏ i : Fin m, ∏ b : Fin (m + h), (q + x i * v b)
  let d : ℂ := ∏ i : Fin m, ∏ b : Fin (m + h), (t i + v b)
  let xp : ℂ := ∏ i : Fin m, (x i) ^ (m + h)
  have htinj : Function.Injective t := by
    intro i j hij
    apply hinj
    have hmul : q * x j = q * x i := by
      dsimp [t] at hij
      field_simp [hx i, hx j] at hij
      exact congrArg (fun z => q * z) hij
    exact mul_left_cancel₀ hq hmul.symm
  have hentry (i : Fin m) (b : Fin (m + h)) :
      t i + v b = (q + x i * v b) * (x i)⁻¹ := by
    dsimp [t]
    field_simp [hx i]
  have hxy : ∀ i b, t i + v b ≠ 0 := by
    intro i b
    rw [hentry i b]
    exact mul_ne_zero (hden i b) (inv_ne_zero (hx i))
  have hprod : d = p * ∏ i : Fin m, (x i)⁻¹ ^ (m + h) := by
    dsimp [d, p]
    calc
      (∏ i : Fin m, ∏ b : Fin (m + h), (t i + v b)) =
          ∏ i : Fin m, ∏ b : Fin (m + h),
            ((q + x i * v b) * (x i)⁻¹) := by
              simp_rw [hentry]
      _ = (∏ i : Fin m, ∏ b : Fin (m + h), (q + x i * v b)) *
            ∏ i : Fin m, ∏ b : Fin (m + h), (x i)⁻¹ := by
              simp_rw [Finset.prod_mul_distrib]
      _ = (∏ i : Fin m, ∏ b : Fin (m + h), (q + x i * v b)) *
            ∏ i : Fin m, (x i)⁻¹ ^ (m + h) := by
              congr 1
              apply Finset.prod_congr rfl
              intro i hi
              simp
  have hcv :
      (CauchyVandermonde.cvQXMatrix q x v).det * d =
        (Matrix.vandermonde v).det * (Matrix.vandermonde t).det := by
    dsimp [CauchyVandermonde.cvQXMatrix, d, t]
    exact CauchyVandermonde.cv_det_mul_denominator_eq_vandermonde
      (fun i => q / x i) v htinj hxy
  have hscale :
      (vDxvMatrix q x v).det =
        (∏ s : Fin (m + h), vDxvRowScale x s) *
          (CauchyVandermonde.cvQXMatrix q x v).det := by
    rw [vDxvMatrix_eq_diagonal_mul_cvMatrix q x v hx,
      Matrix.det_mul, Matrix.det_diagonal]
    simp [CauchyVandermonde.cvQXMatrix]
  have hcancel :
      (∏ i : Fin m, (x i)⁻¹ ^ (m + h)) *
          (∏ i : Fin m, (x i) ^ (m + h)) = 1 := by
    rw [← Finset.prod_mul_distrib]
    simp [← mul_pow, hx]
  have hdenprod : d * xp = p := by
    rw [hprod]
    dsimp [xp]
    calc
      p * (∏ i : Fin m, (x i)⁻¹ ^ (m + h)) *
          ∏ i : Fin m, (x i) ^ (m + h) =
        p * ((∏ i : Fin m, (x i)⁻¹ ^ (m + h)) *
          ∏ i : Fin m, (x i) ^ (m + h)) := by ring
      _ = p := by rw [hcancel]; simp
  calc
    (vDxvMatrix q x v).det * p =
        ((∏ s : Fin (m + h), vDxvRowScale x s) *
          (CauchyVandermonde.cvQXMatrix q x v).det) * p := by
            rw [hscale]
    _ = (∏ s : Fin (m + h), vDxvRowScale x s) * xp *
          ((CauchyVandermonde.cvQXMatrix q x v).det * d) := by
          rw [← hdenprod]
          ring
    _ = (∏ s : Fin (m + h), vDxvRowScale x s) * xp *
          ((Matrix.vandermonde v).det *
            (Matrix.vandermonde t).det) := by
          rw [hcv]
    _ = (∏ s : Fin (m + h), vDxvRowScale x s) *
          (∏ i : Fin m, (x i) ^ (m + h)) *
            (Matrix.vandermonde v).det *
              (Matrix.vandermonde (fun i => q / x i)).det := by
          simp [t, xp, mul_assoc]

/-! The old names remain available to consumers that used the Phase-B receipt. -/
abbrev dxMatrix {m : ℕ} (r₀ : ℕ) (x : Fin m → ℂ) := vDxMatrix r₀ x
abbrev dxColumnScale {m : ℕ} (r₀ : ℕ) (x : Fin m → ℂ) := vDxColumnScale r₀ x
abbrev dxvMatrix {m h : ℕ} (q : ℂ) (x : Fin m → ℂ)
    (v : Fin (m + h) → ℂ) := vDxvMatrix q x v

theorem det_dxMatrix {m : ℕ} (r₀ : ℕ) (x : Fin m → ℂ) :
    (dxMatrix r₀ x).det =
      (Matrix.vandermonde x).det * ∏ j : Fin m, (x j) ^ r₀ :=
  det_vDxMatrix r₀ x

theorem det_dxvMatrix_q_over_x {m h : ℕ}
    (q : ℂ) (x : Fin m → ℂ) (v : Fin (m + h) → ℂ)
    (hx : ∀ i, x i ≠ 0)
    (ht : Function.Injective (fun i => q / x i))
    (hxy : ∀ i b, q / x i + v b ≠ 0) :
    (dxvMatrix q x v).det =
      (∏ s : Fin (m + h), vDxvRowScale x s) *
        (Matrix.vandermonde v).det *
          (Matrix.vandermonde (fun i => q / x i)).det *
            (∏ i : Fin m, ∏ b : Fin (m + h),
              (q / x i + v b))⁻¹ :=
  det_vDxvMatrix_q_over_x q x v hx ht hxy

theorem det_dxvMatrix_mul_denominator {m h : ℕ}
    (q : ℂ) (x : Fin m → ℂ) (v : Fin (m + h) → ℂ)
    (hq : q ≠ 0) (hx : ∀ i, x i ≠ 0)
    (hinj : Function.Injective x)
    (hden : ∀ i b, q + x i * v b ≠ 0) :
    (dxvMatrix q x v).det *
        (∏ i : Fin m, ∏ b : Fin (m + h), (q + x i * v b)) =
      (∏ s : Fin (m + h), vDxvRowScale x s) *
        (∏ i : Fin m, (x i) ^ (m + h)) *
          (Matrix.vandermonde v).det *
            (Matrix.vandermonde (fun i => q / x i)).det :=
  det_vDxvMatrix_mul_denominator q x v hq hx hinj hden

end

end Li2Lean.V

#print axioms Li2Lean.V.det_vDxMatrix
#print axioms Li2Lean.V.det_vDxvMatrix_q_over_x
