/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Mathlib

namespace Li2Lean.V

/-!
Encoding of the signed determinant in v13
`chapters/v-arithmetic.tex:13-35`.  This is the v13 construction; it is not
obtained from another irrationality formalization.  The parameter is kept
integral and all rational entries are represented in `Polynomial ℚ`.
-/

/-- v13 `v-arithmetic.tex:13`: `m=4n`. -/
def vM (n : ℕ) : ℕ := 4 * n

/-- v13 `v-arithmetic.tex:13`: the auxiliary sizes `s=k=h=n`. -/
def vS (n : ℕ) : ℕ := n

/-- v13 `v-arithmetic.tex:16`: the largest column index `N=10n-1`. -/
def vN (n : ℕ) : ℕ := 10 * n - 1

/-- v13 `v-arithmetic.tex:16`: the largest Cauchy-sum index `U=11n-1`. -/
def vU (n : ℕ) : ℕ := 11 * n - 1

/-- v13 `v-arithmetic.tex:13-17`: the column and row count `2m+n`. -/
def vMatrixSize (n : ℕ) : ℕ := 2 * vM n + vS n

/-- v13 `v-arithmetic.tex:15-16`: the `I=[2n,6n)` row index map. -/
def vIIndex (n : ℕ) (r : Fin (vM n)) : ℕ := 2 * n + r.val

/-- v13 `v-arithmetic.tex:15-16`: natural-index form of `I=[2n,6n)`. -/
def vIIndexNat (n i : ℕ) : ℕ := 2 * n + i

/-- v13 `v-arithmetic.tex:15-16`: the `J=[n,10n)` column index map. -/
def vJIndex (n : ℕ) (c : Fin (vMatrixSize n)) : ℕ := n + c.val

/-- v13 `v-arithmetic.tex:16`: the `Lambda={1,...,n}` row index map. -/
def vLambdaIndex (n : ℕ) (r : Fin n) : ℕ := 1 + r.val

/- The following interface equalities and range facts unpack the index
   conventions in v13 `v-arithmetic.tex:13-17`. -/
theorem vM_eq (n : ℕ) : vM n = 4 * n := rfl

/- v13 `v-arithmetic.tex:13`: `s=k=h=n`. -/
theorem vS_eq (n : ℕ) : vS n = n := rfl

/- v13 `v-arithmetic.tex:13-17`: `2m+n=9n` for the chosen `m=4n`. -/
theorem vMatrixSize_eq (n : ℕ) : vMatrixSize n = 9 * n := by
  simp [vMatrixSize, vM, vS]
  ring

/- v13 `v-arithmetic.tex:15`: the image of `I` is `[2n,6n)`. -/
theorem vIIndex_mem (n : ℕ) (r : Fin (vM n)) :
    2 * n ≤ vIIndex n r ∧ vIIndex n r < 6 * n := by
  simp [vIIndex, vM]
  omega

/- v13 `v-arithmetic.tex:15`: the image of `J` is `[n,10n)`. -/
theorem vJIndex_mem (n : ℕ) (c : Fin (vMatrixSize n)) :
    n ≤ vJIndex n c ∧ vJIndex n c < 10 * n := by
  simp [vJIndex, vMatrixSize, vM, vS]
  omega

/- v13 `v-arithmetic.tex:16`: the image of `Lambda` is `{1,...,n}`. -/
theorem vLambdaIndex_mem (n : ℕ) (r : Fin n) :
    1 ≤ vLambdaIndex n r ∧ vLambdaIndex n r ≤ n := by
  simp [vLambdaIndex]
  omega

/-- v13 `v-arithmetic.tex:20-23`: the first moment `t_j`, including `t_0=0`. -/
def vMomentT (a : ℤ) (j : ℕ) : ℚ :=
  ∑ r ∈ Finset.range j,
    (a : ℚ) ^ (j - (r + 1)) * (((r + 1 : ℕ) : ℚ)⁻¹)

/-- v13 `v-arithmetic.tex:20-23`: the second moment `b_j`, including `b_0=0`. -/
def vMomentB (a : ℤ) (j : ℕ) : ℚ :=
  ∑ r ∈ Finset.range j,
    (a : ℚ) ^ (j - (r + 1)) * ((((r + 1 : ℕ) : ℚ) ^ 2)⁻¹)

/-- v13 `v-arithmetic.tex:26`: the signed `C` block entry. -/
def vCEntry (a : ℤ) (i j : ℕ) : ℚ :=
  if i = j then 0
  else ((a : ℚ) ^ i - (a : ℚ) ^ j) / ((j : ℚ) - (i : ℚ))

/-- v13 `v-arithmetic.tex:28`: the divided-difference/diagonal `B` entry. -/
def vBEntry (a : ℤ) (i j : ℕ) : ℚ :=
  if i = j then vMomentB a i
  else (vMomentT a i - vMomentT a j) / ((j : ℚ) - (i : ℚ))

/-- v13 `v-arithmetic.tex:31`: the diagonal `A` block entry. -/
def vAEntry (a : ℤ) (i j : ℕ) : ℚ :=
  if i = j then (a : ℚ) ^ i else 0

/-- v13 `v-arithmetic.tex:31`: the Cauchy block entry `1/(j+ell)`. -/
def vVEntry (j ell : ℕ) : ℚ := (((j + ell : ℕ) : ℚ)⁻¹)

/-- v13 `v-arithmetic.tex:24-26`: the rectangular `C` block. -/
noncomputable def vCBlock (n : ℕ) (a : ℤ) :
    Matrix (Fin (vM n)) (Fin (vMatrixSize n)) (Polynomial ℚ) :=
  fun r c => Polynomial.C (vCEntry a (vIIndex n r) (vJIndex n c))

/-- v13 `v-arithmetic.tex:24,28`: the rectangular `B` block. -/
noncomputable def vBBlock (n : ℕ) (a : ℤ) :
    Matrix (Fin (vM n)) (Fin (vMatrixSize n)) (Polynomial ℚ) :=
  fun r c => Polynomial.C (vBEntry a (vIIndex n r) (vJIndex n c))

/-- v13 `v-arithmetic.tex:24,31`: the rectangular diagonal `A` block. -/
noncomputable def vABlock (n : ℕ) (a : ℤ) :
    Matrix (Fin (vM n)) (Fin (vMatrixSize n)) (Polynomial ℚ) :=
  fun r c => Polynomial.C (vAEntry a (vIIndex n r) (vJIndex n c))

/-- v13 `v-arithmetic.tex:24,31`: the bottom Cauchy block. -/
noncomputable def vVBlock (n : ℕ) :
    Matrix (Fin (vS n)) (Fin (vMatrixSize n)) (Polynomial ℚ) :=
  fun r c => Polynomial.C (vVEntry (vJIndex n c) (vLambdaIndex n r))

/--
The complete v13 source matrix ` [C; B-XA; V] `, with rows indexed in block
order and columns indexed by `J`.  Its entries are polynomials in the
indeterminate `X`, which represents the paper's `T`.
Source: v13 `v-arithmetic.tex:24-32`.
-/
noncomputable def vSourceMatrix (n : ℕ) (a : ℤ) :
    Matrix (Fin (vMatrixSize n)) (Fin (vMatrixSize n)) (Polynomial ℚ) :=
  fun r c =>
    let j := vJIndex n c
    if r.val < vM n then
      Polynomial.C (vCEntry a (vIIndexNat n r.val) j)
    else if r.val < 2 * vM n then
      let i := 2 * n + (r.val - vM n)
      Polynomial.C (vBEntry a i j) -
        Polynomial.X * Polynomial.C (vAEntry a i j)
    else
      Polynomial.C (vVEntry j (1 + (r.val - 2 * vM n)))

/-- v13 `v-arithmetic.tex:32`: `G_{4n}(X;a)` as the determinant polynomial. -/
noncomputable def vPolynomial (n : ℕ) (a : ℤ) : Polynomial ℚ :=
  Matrix.det (vSourceMatrix n a)

/-! The next decomposition isolates the only `X`-dependent rows of the v13
source matrix.  It follows its block form `[C; B-XA; V]` in
`v-arithmetic.tex:24-32`, with the middle block having `vM n = 4n` rows as
fixed in `v-arithmetic.tex:13-17`. -/

private def vPolynomialXMatrix (n : ℕ) (a : ℤ) :
    Matrix (Fin (vMatrixSize n)) (Fin (vMatrixSize n)) ℚ :=
  fun r c =>
    if r.val < vM n then 0
    else if r.val < 2 * vM n then
      -(vAEntry a (2 * n + (r.val - vM n)) (vJIndex n c))
    else 0

private def vPolynomialConstantMatrix (n : ℕ) (a : ℤ) :
    Matrix (Fin (vMatrixSize n)) (Fin (vMatrixSize n)) ℚ :=
  fun r c =>
    let j := vJIndex n c
    if r.val < vM n then
      vCEntry a (vIIndexNat n r.val) j
    else if r.val < 2 * vM n then
      vBEntry a (2 * n + (r.val - vM n)) j
    else
      vVEntry j (1 + (r.val - 2 * vM n))

private def vPolynomialVariableRowBudget (n : ℕ)
    (r : Fin (vMatrixSize n)) : ℕ :=
  if vM n ≤ r.val ∧ r.val < 2 * vM n then 1 else 0

private def vPolynomialMiddleRows (n : ℕ) :=
  {r : Fin (vMatrixSize n) // vM n ≤ r.val ∧ r.val < 2 * vM n}

private def vPolynomialMiddleRowsEquiv (n : ℕ) :
    vPolynomialMiddleRows n ≃ Fin (vM n) where
  toFun r := by
    have hr := r.property
    exact ⟨r.val.val - vM n, by omega⟩
  invFun i := by
    have hs : 2 * vM n ≤ vMatrixSize n := by
      simp [vMatrixSize, vM, vS]
    have hi : i.val < vM n := i.isLt
    have hle : vM n + i.val < vMatrixSize n := by
      calc
        vM n + i.val < 2 * vM n := by omega
        _ ≤ vMatrixSize n := hs
    refine ⟨⟨vM n + i.val, hle⟩, ?_⟩
    change vM n ≤ vM n + i.val ∧ vM n + i.val < 2 * vM n
    constructor
    · exact Nat.le_add_right _ _
    · calc
        vM n + i.val < vM n + vM n := Nat.add_lt_add_left hi _
        _ = 2 * vM n := by omega
  left_inv r := by
    have hr := r.property
    apply Subtype.ext
    apply Fin.ext
    simp
    omega
  right_inv i := by
    apply Fin.ext
    simp

private theorem vPolynomialVariableRowBudget_sum (n : ℕ) :
    (∑ r : Fin (vMatrixSize n), vPolynomialVariableRowBudget n r) = vM n := by
  classical
  let s : Finset (Fin (vMatrixSize n)) := Finset.univ.filter
    (fun r => vM n ≤ r.val ∧ r.val < 2 * vM n)
  have hs : ∀ r : Fin (vMatrixSize n),
      r ∈ s ↔ vM n ≤ r.val ∧ r.val < 2 * vM n := by
    intro r
    simp [s]
  letI : Fintype (vPolynomialMiddleRows n) := Fintype.subtype s hs
  calc
    (∑ r : Fin (vMatrixSize n), vPolynomialVariableRowBudget n r) =
        (Finset.univ.filter
          (fun r : Fin (vMatrixSize n) => vM n ≤ r.val ∧ r.val < 2 * vM n)).card := by
      simp [vPolynomialVariableRowBudget, Finset.sum_boole]
    _ = Fintype.card (vPolynomialMiddleRows n) := by
      symm
      change Fintype.card
        {r : Fin (vMatrixSize n) // vM n ≤ r.val ∧ r.val < 2 * vM n} = s.card
      exact Fintype.card_of_subtype s hs
    _ = vM n := by
      rw [Fintype.card_congr (vPolynomialMiddleRowsEquiv n)]
      simp

/-- The coefficient of `X` and the constant part of the exact v13 block
matrix, `v-arithmetic.tex:24-32`. -/
theorem vSourceMatrix_eq_X_smul_add_constant (n : ℕ) (a : ℤ) :
    vSourceMatrix n a =
      (Polynomial.X : Polynomial ℚ) • (vPolynomialXMatrix n a).map Polynomial.C +
        (vPolynomialConstantMatrix n a).map Polynomial.C := by
  funext r c
  by_cases h₁ : r.val < vM n
  · simp [vSourceMatrix, vPolynomialXMatrix, vPolynomialConstantMatrix, h₁]
  · by_cases h₂ : r.val < 2 * vM n
    · simp [vSourceMatrix, vPolynomialXMatrix, vPolynomialConstantMatrix, h₁, h₂]
      ring
    · simp [vSourceMatrix, vPolynomialXMatrix, vPolynomialConstantMatrix, h₁, h₂]

/-- The exact v13 determinant polynomial has degree at most `m=4n`: only
the `B-XA` block in `v-arithmetic.tex:24-32` depends on `X`, and it has
`vM n` rows by `v-arithmetic.tex:13-17`. -/
theorem vPolynomial_natDegree_le (n : ℕ) (a : ℤ) :
    (vPolynomial n a).natDegree ≤ vM n := by
  rw [vPolynomial, vSourceMatrix_eq_X_smul_add_constant]
  rw [Matrix.det_apply]
  refine (Polynomial.natDegree_sum_le _ _).trans ?_
  refine Multiset.max_le_of_forall_le _ _ ?_
  simp only [forall_apply_eq_imp_iff, true_and, Function.comp_apply,
    Multiset.mem_map, exists_imp, Finset.mem_univ_val]
  intro g
  let entry : Fin (vMatrixSize n) → Fin (vMatrixSize n) → Polynomial ℚ :=
    fun r c =>
      (Polynomial.X : Polynomial ℚ) • (vPolynomialXMatrix n a).map Polynomial.C r c +
        (vPolynomialConstantMatrix n a).map Polynomial.C r c
  have hentry : ∀ r c, (entry r c).natDegree ≤ vPolynomialVariableRowBudget n r := by
    intro r c
    by_cases h₁ : r.val < vM n
    · simp [entry, vPolynomialXMatrix, vPolynomialConstantMatrix,
        vPolynomialVariableRowBudget, h₁]
    · by_cases h₂ : r.val < 2 * vM n
      · simp only [entry, vPolynomialXMatrix, vPolynomialConstantMatrix, h₁, h₂,
          ↓reduceIte, Matrix.map_apply, smul_eq_mul, map_neg]
        have hbudget : vPolynomialVariableRowBudget n r = 1 := by
          simp [vPolynomialVariableRowBudget]
          omega
        rw [hbudget]
        calc
          (Polynomial.X * -Polynomial.C (vAEntry a (2 * n + (r.val - vM n))
              (vJIndex n c)) +
              Polynomial.C (vBEntry a (2 * n + (r.val - vM n))
                (vJIndex n c))).natDegree
              ≤ max (Polynomial.X * -Polynomial.C (vAEntry a
                    (2 * n + (r.val - vM n)) (vJIndex n c))).natDegree
                  (Polynomial.C (vBEntry a (2 * n + (r.val - vM n))
                    (vJIndex n c))).natDegree :=
            Polynomial.natDegree_add_le _ _
          _ ≤ 1 := by
            apply max_le
            · calc
                (Polynomial.X * -Polynomial.C
                    (vAEntry a (2 * n + (r.val - vM n)) (vJIndex n c))).natDegree
                    ≤ Polynomial.X.natDegree + (-Polynomial.C
                        (vAEntry a (2 * n + (r.val - vM n)) (vJIndex n c))).natDegree :=
                      @Polynomial.natDegree_mul_le ℚ _ Polynomial.X
                        (-Polynomial.C
                          (vAEntry a (2 * n + (r.val - vM n)) (vJIndex n c)))
                _ = 1 := by
                  rw [Polynomial.natDegree_X (R := ℚ)]
                  simp
            · simp
      · simp [entry, vPolynomialXMatrix, vPolynomialConstantMatrix,
          vPolynomialVariableRowBudget, h₁, h₂]
  calc
    (Equiv.Perm.sign g • ∏ i : Fin (vMatrixSize n), entry (g i) i).natDegree
        ≤ (∏ i : Fin (vMatrixSize n), entry (g i) i).natDegree :=
          Polynomial.natDegree_smul_le _ _
    _ ≤ ∑ i : Fin (vMatrixSize n), (entry (g i) i).natDegree :=
      Polynomial.natDegree_prod_le Finset.univ _
    _ ≤ ∑ i : Fin (vMatrixSize n), vPolynomialVariableRowBudget n (g i) :=
      Finset.sum_le_sum fun i _ => hentry (g i) i
    _ = vM n := by
      rw [Equiv.sum_comp g (vPolynomialVariableRowBudget n)]
      exact vPolynomialVariableRowBudget_sum n

/-- The generic v13 degree bound specializes unchanged to the existing
positive-base `a=2` construction, `v-arithmetic.tex:18-32`. -/
theorem vPolynomial_two_natDegree_le (n : ℕ) :
    (vPolynomial n (2 : ℤ)).natDegree ≤ vM n :=
  vPolynomial_natDegree_le n 2

/--
Regression at the positive parameter `a=2`: this is the same generic V
construction specialized at `2`, with the determinant unchanged.  Source:
v13 `v-arithmetic.tex:18-32`.
-/
theorem vSourceMatrix_two (n : ℕ) :
    vSourceMatrix n (2 : ℤ) = vSourceMatrix n 2 := rfl

theorem vPolynomial_two (n : ℕ) :
    vPolynomial n (2 : ℤ) = Matrix.det (vSourceMatrix n (2 : ℤ)) := rfl

end Li2Lean.V
