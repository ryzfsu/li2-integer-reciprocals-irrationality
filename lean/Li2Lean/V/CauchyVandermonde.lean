/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Mathlib
import Li2Lean.P0.CauchyDeterminant

/-!
  The Cauchy--Vandermonde block used by the signed V construction.

  Source ledger: `paper-v13/chapters/v-analytic.tex:153-194`.  The
  polynomial clearing step below is the finite-dimensional form of the
  proof in `:166-194`; the `q/x` specialization is recorded at `:166-173`.

  The determinant helpers are imported from the frozen Li2(1/2) release
  (`Li2Lean/P0/CauchyDeterminant.lean`).  In particular, no second Cauchy
  determinant proof is introduced here.
-/

namespace Li2Lean.V.CauchyVandermonde

open Polynomial

noncomputable section

def allLinearProduct {m : ℕ} (t : Fin m → ℂ) : Polynomial ℂ :=
  ∏ i : Fin m, (Polynomial.X + Polynomial.C (t i))

def cvPolynomialSum {m h : ℕ} (t : Fin m → ℂ) :
    Fin m ⊕ Fin h → Polynomial ℂ :=
  Sum.elim (Li2Lean.P0.CauchyDeterminant.omittedLinearProduct t)
    (fun k => Polynomial.X ^ (k : ℕ) * allLinearProduct t)

def cvPolynomial {m h : ℕ} (t : Fin m → ℂ) : Fin (m + h) → Polynomial ℂ :=
  fun j => cvPolynomialSum t (finSumFinEquiv.symm j)

lemma allLinearProduct_natDegree_le {m : ℕ} (t : Fin m → ℂ) :
    (allLinearProduct t).natDegree ≤ m := by
  calc
    (allLinearProduct t).natDegree ≤
        ∑ i : Fin m, (Polynomial.X + Polynomial.C (t i)).natDegree := by
          exact Polynomial.natDegree_prod_le _ _
    _ = m := by simp

lemma allLinearProduct_monic {m : ℕ} (t : Fin m → ℂ) :
    (allLinearProduct t).Monic := by
  exact Polynomial.monic_prod_of_monic Finset.univ
    (fun i : Fin m => Polynomial.X + Polynomial.C (t i))
    (by intro i hi; exact Polynomial.monic_X_add_C _)

lemma allLinearProduct_natDegree_eq {m : ℕ} (t : Fin m → ℂ) :
    (allLinearProduct t).natDegree = m := by
  change (∏ i : Fin m, (Polynomial.X + Polynomial.C (t i))).natDegree = m
  rw [Polynomial.natDegree_prod]
  · simp
  · intro i hi
    exact (Polynomial.monic_X_add_C (t i)).ne_zero

lemma cvPolynomial_natDegree_lt {m h : ℕ} (t : Fin m → ℂ) (j : Fin (m + h)) :
    (cvPolynomial t j).natDegree < m + h := by
  classical
  rw [cvPolynomial]
  cases hs : finSumFinEquiv.symm j with
  | inl i =>
      have hi :=
        Li2Lean.P0.CauchyDeterminant.omittedLinearProduct_natDegree_lt t i
      simpa [cvPolynomialSum, hs] using lt_of_lt_of_le hi (Nat.le_add_right m h)
  | inr k =>
      have hk : (k : ℕ) < h := k.isLt
      have hprod := allLinearProduct_natDegree_le t
      have hmul := (Polynomial.natDegree_mul_le
        (p := Polynomial.X ^ (k : ℕ)) (q := allLinearProduct t))
      have hpow : ((Polynomial.X : Polynomial ℂ) ^ (k : ℕ)).natDegree ≤ (k : ℕ) := by
        rw [Polynomial.natDegree_X_pow]
      have hsum : (k : ℕ) + m < m + h := by omega
      calc
        (cvPolynomialSum t (Sum.inr k)).natDegree =
            (Polynomial.X ^ (k : ℕ) * allLinearProduct t).natDegree := by rfl
        _ ≤ (Polynomial.X ^ (k : ℕ)).natDegree +
              (allLinearProduct t).natDegree := hmul
        _ ≤ (k : ℕ) + m := Nat.add_le_add hpow hprod
        _ < m + h := hsum

def cvEntry {m h : ℕ} (t : Fin m → ℂ) (v : Fin (m + h) → ℂ)
    (s : Fin m ⊕ Fin h) (b : Fin (m + h)) : ℂ :=
  match s with
  | Sum.inl i => (t i + v b)⁻¹
  | Sum.inr k => (v b) ^ (k : ℕ)

def cvMatrix {m h : ℕ} (t : Fin m → ℂ) (v : Fin (m + h) → ℂ) :
    Matrix (Fin (m + h)) (Fin (m + h)) ℂ :=
  Matrix.of (fun r b => cvEntry t v (finSumFinEquiv.symm r) b)

def cvDenominator {m h : ℕ} (t : Fin m → ℂ) (v : Fin (m + h) → ℂ) :
    Fin (m + h) → ℂ :=
  fun b => ∏ i : Fin m, (t i + v b)

def cvEvaluationMatrix {m h : ℕ} (t : Fin m → ℂ) (v : Fin (m + h) → ℂ) :
    Matrix (Fin (m + h)) (Fin (m + h)) ℂ :=
  Matrix.of (fun b j => (cvPolynomial t j).eval (v b))

lemma cvDenominator_ne_zero {m h : ℕ} {t : Fin m → ℂ} {v : Fin (m + h) → ℂ}
    (hxy : ∀ i b, t i + v b ≠ 0) :
    ∀ b, cvDenominator t v b ≠ 0 := by
  intro b
  exact Finset.prod_ne_zero_iff.mpr (fun i hi => hxy i b)

lemma cvEvaluationMatrix_eq_diagonal_mul_transpose {m h : ℕ}
    (t : Fin m → ℂ) (v : Fin (m + h) → ℂ)
    (hxy : ∀ i b, t i + v b ≠ 0) :
    cvEvaluationMatrix t v =
      Matrix.diagonal (cvDenominator t v) * (cvMatrix t v).transpose := by
  classical
  ext b j
  simp only [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.transpose_apply,
    Matrix.of_apply]
  rw [Finset.sum_eq_single b]
  · simp only [if_pos rfl, one_mul]
    change (cvEvaluationMatrix t v) b j =
      cvDenominator t v b * cvMatrix t v j b
    change (cvPolynomial t j).eval (v b) =
      (∏ i : Fin m, (t i + v b)) *
        cvEntry t v (finSumFinEquiv.symm j) b
    cases hs : finSumFinEquiv.symm j with
    | inl i =>
        have hj : j = finSumFinEquiv (Sum.inl i) := by
          simpa using congrArg finSumFinEquiv hs
        rw [hj]
        simp only [cvPolynomial, cvPolynomialSum, cvEntry,
          Equiv.symm_apply_apply, Sum.elim_inl]
        change (Li2Lean.P0.CauchyDeterminant.omittedLinearProduct t i).eval
            (v b) = (∏ i' : Fin m, (t i' + v b)) * (t i + v b)⁻¹
        rw [Li2Lean.P0.CauchyDeterminant.omittedLinearProduct_eval]
        rw [← Finset.prod_erase_mul (Finset.univ : Finset (Fin m))
          (fun i' => t i' + v b) (Finset.mem_univ i)]
        field_simp [hxy i b]
        apply Finset.prod_congr rfl
        intro k hk
        ring
    | inr k =>
        have hj : j = finSumFinEquiv (Sum.inr k) := by
          simpa using congrArg finSumFinEquiv hs
        rw [hj]
        simp only [cvPolynomial, cvPolynomialSum, cvEntry,
          Equiv.symm_apply_apply, Sum.elim_inr]
        change ((Polynomial.X : Polynomial ℂ) ^ (k : ℕ) * allLinearProduct t).eval
            (v b) = (∏ i : Fin m, (t i + v b)) * (v b) ^ (k : ℕ)
        rw [Polynomial.eval_mul, Polynomial.eval_pow]
        simp only [allLinearProduct, Polynomial.eval_prod, Polynomial.eval_add,
          Polynomial.eval_X, Polynomial.eval_C, RingHom.id_apply]
        have hp : (∏ x : Fin m, (v b + t x)) =
            ∏ x : Fin m, (t x + v b) := by
          apply Finset.prod_congr rfl
          intro i hi
          ring
        rw [hp]
        ring
  · intro b' hb' hne
    have hne' : ¬ b = b' := Ne.symm hne
    simp [hne']
  · simp

def cvCoefficientMatrix {m h : ℕ} (t : Fin m → ℂ) :
    Matrix (Fin (m + h)) (Fin (m + h)) ℂ :=
  Matrix.of (fun d j => (cvPolynomial t j).coeff d)

def cvCoefficientSum {m h : ℕ} (t : Fin m → ℂ) :
    Matrix (Fin m ⊕ Fin h) (Fin m ⊕ Fin h) ℂ :=
  Matrix.fromBlocks
    (Matrix.of (fun i j =>
      (Li2Lean.P0.CauchyDeterminant.omittedLinearProduct t j).coeff i))
    (Matrix.of (fun i k =>
      (Polynomial.X ^ (k : ℕ) * allLinearProduct t).coeff i))
    0
    (Matrix.of (fun r k =>
      (Polynomial.X ^ (k : ℕ) * allLinearProduct t).coeff (m + (r : ℕ))))

lemma cvCoefficient_reindex_eq {m h : ℕ} (t : Fin m → ℂ) :
    Matrix.reindex (finSumFinEquiv (m := m) (n := h)).symm
      (finSumFinEquiv (m := m) (n := h)).symm (cvCoefficientMatrix t) =
      cvCoefficientSum (m := m) (h := h) t := by
  classical
  ext s j
  cases s with
  | inl i =>
      cases j with
      | inl j =>
          simp [cvCoefficientMatrix, cvCoefficientSum, Matrix.reindex_apply,
            cvPolynomial, cvPolynomialSum]

      | inr k =>
          simp [cvCoefficientMatrix, cvCoefficientSum, Matrix.reindex_apply,
            cvPolynomial, cvPolynomialSum]
  | inr r =>
      cases j with
      | inl j =>
          simp [cvCoefficientMatrix, cvCoefficientSum, Matrix.reindex_apply,
            cvPolynomial, cvPolynomialSum]
          exact Polynomial.coeff_eq_zero_of_natDegree_lt
            (lt_of_lt_of_le
              (Li2Lean.P0.CauchyDeterminant.omittedLinearProduct_natDegree_lt t j)
              (Nat.le_add_right m r))
      | inr k =>
          simp [cvCoefficientMatrix, cvCoefficientSum, Matrix.reindex_apply,
            cvPolynomial, cvPolynomialSum]

def cvUpperBlock {m h : ℕ} (t : Fin m → ℂ) :
    Matrix (Fin h) (Fin h) ℂ :=
  Matrix.of (fun r k =>
    (Polynomial.X ^ (k : ℕ) * allLinearProduct t).coeff (m + (r : ℕ)))

lemma cvUpperBlock_isUpperTriangular {m h : ℕ} (t : Fin m → ℂ) :
    (cvUpperBlock (m := m) (h := h) t).IsUpperTriangular := by
  intro r k hrk
  dsimp [cvUpperBlock]
  rw [Polynomial.coeff_X_pow_mul']
  change (k : ℕ) < (r : ℕ) at hrk
  by_cases hle : (k : ℕ) ≤ m + (r : ℕ)
  · rw [if_pos hle]
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    exact lt_of_le_of_lt (allLinearProduct_natDegree_le t) (by omega)
  · simp [hle]

lemma cvUpperBlock_diag {m h : ℕ} (t : Fin m → ℂ) (r : Fin h) :
    cvUpperBlock (m := m) (h := h) t r r = 1 := by
  dsimp [cvUpperBlock]
  rw [Polynomial.coeff_X_pow_mul]
  have hdeg := allLinearProduct_natDegree_eq t
  simpa [hdeg] using Polynomial.Monic.coeff_natDegree (allLinearProduct_monic t)

lemma cvCoefficientSum_det {m h : ℕ} (t : Fin m → ℂ)
    (ht : Function.Injective t) :
    (cvCoefficientSum (m := m) (h := h) t).det =
      (Matrix.vandermonde t).det := by
  classical
  unfold cvCoefficientSum
  rw [Matrix.det_fromBlocks_zero₂₁]
  have hA :
      (Matrix.of (fun (i j : Fin m) =>
        (Li2Lean.P0.CauchyDeterminant.omittedLinearProduct t j).coeff i)).det =
        (Matrix.vandermonde t).det :=
    Li2Lean.P0.CauchyDeterminant.omittedLinearProduct_coeff_det t ht
  have hD :
      (Matrix.of (fun (r k : Fin h) =>
        (Polynomial.X ^ (k : ℕ) * allLinearProduct t).coeff (m + (r : ℕ)))).det = 1 := by
    change (cvUpperBlock (m := m) (h := h) t).det = 1
    rw [Matrix.det_of_isUpperTriangular (cvUpperBlock_isUpperTriangular t)]
    simp_rw [cvUpperBlock_diag]
    simp
  rw [hA, hD, mul_one]

lemma cvCoefficientMatrix_det {m h : ℕ} (t : Fin m → ℂ)
    (ht : Function.Injective t) :
    (cvCoefficientMatrix (m := m) (h := h) t).det =
      (Matrix.vandermonde t).det := by
  have hdet := Matrix.det_reindex_self
    (finSumFinEquiv (m := m) (n := h)).symm (cvCoefficientMatrix t)
  rw [cvCoefficient_reindex_eq t] at hdet
  exact hdet.symm.trans (cvCoefficientSum_det t ht)

lemma cvEvaluationMatrix_det {m h : ℕ} (t : Fin m → ℂ)
    (v : Fin (m + h) → ℂ) (ht : Function.Injective t) :
    (cvEvaluationMatrix t v).det =
      (Matrix.vandermonde v).det * (Matrix.vandermonde t).det := by
  have hfactor :=
    Li2Lean.P0.CauchyDeterminant.eval_matrix_eq_vandermonde_mul_coeff v
      (cvPolynomial t) (cvPolynomial_natDegree_lt t)
  change (Matrix.of (fun i j => (cvPolynomial t j).eval (v i))).det = _
  rw [hfactor, Matrix.det_mul]
  change (Matrix.vandermonde v).det *
      (cvCoefficientMatrix (m := m) (h := h) t).det = _
  rw [cvCoefficientMatrix_det (m := m) (h := h) t ht]

lemma cv_det_mul_column_denominator_eq_vandermonde {m h : ℕ}
    (t : Fin m → ℂ) (v : Fin (m + h) → ℂ)
    (ht : Function.Injective t) (hxy : ∀ i b, t i + v b ≠ 0) :
    (cvMatrix t v).det * (∏ b : Fin (m + h), cvDenominator t v b) =
      (Matrix.vandermonde v).det * (Matrix.vandermonde t).det := by
  have hEval := cvEvaluationMatrix_det t v ht
  rw [cvEvaluationMatrix_eq_diagonal_mul_transpose t v hxy,
    Matrix.det_mul, Matrix.det_diagonal, Matrix.det_transpose] at hEval
  calc
    (cvMatrix t v).det * (∏ b : Fin (m + h), cvDenominator t v b) =
        (∏ b : Fin (m + h), cvDenominator t v b) * (cvMatrix t v).det := by
          ring
    _ = (Matrix.vandermonde v).det * (Matrix.vandermonde t).det := hEval

lemma cv_det_mul_denominator_eq_vandermonde {m h : ℕ}
    (t : Fin m → ℂ) (v : Fin (m + h) → ℂ)
    (ht : Function.Injective t) (hxy : ∀ i b, t i + v b ≠ 0) :
    (cvMatrix t v).det *
        (∏ i : Fin m, ∏ b : Fin (m + h), (t i + v b)) =
      (Matrix.vandermonde v).det * (Matrix.vandermonde t).det := by
  have hprod :
      (∏ b : Fin (m + h), cvDenominator t v b) =
        ∏ i : Fin m, ∏ b : Fin (m + h), (t i + v b) := by
    simp only [cvDenominator]
    rw [Finset.prod_comm]
  rw [← hprod]
  exact cv_det_mul_column_denominator_eq_vandermonde t v ht hxy

lemma cv_det_eq_vandermonde_mul_inv_denominator {m h : ℕ}
    (t : Fin m → ℂ) (v : Fin (m + h) → ℂ)
    (ht : Function.Injective t) (hxy : ∀ i b, t i + v b ≠ 0) :
    (cvMatrix t v).det =
      (Matrix.vandermonde v).det * (Matrix.vandermonde t).det *
        (∏ i : Fin m, ∏ b : Fin (m + h), (t i + v b))⁻¹ := by
  let d : ℂ := ∏ i : Fin m, ∏ b : Fin (m + h), (t i + v b)
  have hd : d ≠ 0 := by
    dsimp [d]
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    apply Finset.prod_ne_zero_iff.mpr
    intro b hb
    exact hxy i b
  have hm := cv_det_mul_denominator_eq_vandermonde t v ht hxy
  dsimp [d] at hd ⊢
  calc
    (cvMatrix t v).det = (cvMatrix t v).det *
        (∏ i : Fin m, ∏ b : Fin (m + h), (t i + v b)) *
          (∏ i : Fin m, ∏ b : Fin (m + h), (t i + v b))⁻¹ := by
            field_simp [hd]
    _ = (Matrix.vandermonde v).det * (Matrix.vandermonde t).det *
          (∏ i : Fin m, ∏ b : Fin (m + h), (t i + v b))⁻¹ := by
            rw [hm]

/- The parameter specialization here is exactly v13's `t_i = q/x_i`
   reduction at `v-analytic.tex:166-171`. -/
def cvQXMatrix {m h : ℕ} (q : ℂ) (x : Fin m → ℂ)
    (v : Fin (m + h) → ℂ) : Matrix (Fin (m + h)) (Fin (m + h)) ℂ :=
  cvMatrix (fun i => q / x i) v

lemma cvQX_det_eq_vandermonde_mul_inv_denominator {m h : ℕ}
    (q : ℂ) (x : Fin m → ℂ) (v : Fin (m + h) → ℂ)
    (ht : Function.Injective (fun i => q / x i))
    (hxy : ∀ i b, q / x i + v b ≠ 0) :
    (cvQXMatrix q x v).det =
      (Matrix.vandermonde v).det *
        (Matrix.vandermonde (fun i => q / x i)).det *
          (∏ i : Fin m, ∏ b : Fin (m + h), (q / x i + v b))⁻¹ := by
  simpa [cvQXMatrix] using
    (cv_det_eq_vandermonde_mul_inv_denominator
      (fun i => q / x i) v ht hxy)

end

end Li2Lean.V.CauchyVandermonde

#print axioms Li2Lean.V.CauchyVandermonde.cv_det_eq_vandermonde_mul_inv_denominator
#print axioms Li2Lean.V.CauchyVandermonde.cvQX_det_eq_vandermonde_mul_inv_denominator
