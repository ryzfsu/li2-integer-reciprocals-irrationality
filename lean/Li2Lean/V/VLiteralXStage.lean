/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Li2Lean.V.VLiteralNestedBridge
import Li2Lean.V.CauchyVandermonde

/-!
# Literal x-row Andreief stage for v13

The rows and kernels below are the x-variable part of the v13 three-form
construction (`v-analytic.tex:109-153`).  The last n rows are the polynomial
rows in the Cauchy--Vandermonde block (`v-analytic.tex:139-173`).
-/

namespace Li2Lean.V

noncomputable section

open MeasureTheory Set

/-- v13's x-column indexing, identifying the 4n rational rows and n
polynomial rows with the 5n v-nodes (`v-analytic.tex:139-153`). -/
def literalXColumnEquiv (n : ℕ) :
    (Fin (4 * n) ⊕ Fin n) ≃ Fin (5 * n) := by
  let h : 4 * n + n = 5 * n := by omega
  exact (finSumFinEquiv (m := 4 * n) (n := n)).trans
    (Equiv.cast (congrArg Fin h))

/-- The x-row monomial uses the actual interval `I=[2n,6n)` from v13,
`v-analytic.tex:139-153`. -/
def literalXMonomial (n : ℕ) (i : Fin (4 * n)) (x : ℝ) : ℂ :=
  (x : ℂ) ^ (2 * n + i.val)

/-- The kernel is extended by zero away from the integration interval.  On
`[0,1]` it is exactly `1/(q+xv)` from `v-analytic.tex:109-123`; the extension
makes the moment-integrability field total in the outer parameter. -/
def literalXKernel (q : ℕ) (v x : ℝ) : ℂ :=
  if v ∈ Set.Icc (0 : ℝ) 1 then
    ((q : ℂ) + (x : ℂ) * (v : ℂ))⁻¹
  else 0

/-- The actual x moment `f_i(v)`, with the row index shifted to
`I=[2n,6n)` (`v-analytic.tex:139-153`). -/
def literalXMoment (q n : ℕ) (i : Fin (4 * n)) (v : ℝ) : ℂ :=
  ∫ x, literalXMonomial n i x * literalXKernel q v x
    ∂Literal.vContourUnitIntervalMeasure

/-- The first 4n rows are x moments; the final n rows are `1,v,...,v^(n-1)`
(`v-analytic.tex:139-153`). -/
def literalXStageA0 (q n : ℕ) (r : Fin (5 * n)) (v : ℝ) : ℂ :=
  match (literalXColumnEquiv n).symm r with
  | Sum.inl i => literalXMoment q n i v
  | Sum.inr k => (v : ℂ) ^ k.val

/-- The `a2` functions in the final nested Andreief application are the
monomials `x^i` for `i in [2n,6n)` (`v-analytic.tex:139-153`). -/
def literalXStageA2 (n : ℕ) (i : Fin (4 * n)) (x : ℝ) : ℂ :=
  literalXMonomial n i x

/-- The `b2` functions are the rational kernel evaluated at each v-node
(`v-analytic.tex:109-123,139-153`). -/
def literalXStageB2 (q n : ℕ) (v : Fin (5 * n) → ℝ) (x : ℝ)
    (c : Fin (4 * n) ⊕ Fin n) : ℂ :=
  literalXKernel q (v (literalXColumnEquiv n c)) x

/-- The concrete x-moment matrix `M2`; it is the v13 x-moment/polynomial-row
matrix, reindexed from its natural `Fin (5n)` columns
(`v-analytic.tex:139-153`). -/
def literalXStageM2 (q n : ℕ) (v : Fin (5 * n) → ℝ) :
    Matrix (Fin (4 * n) ⊕ Fin n) (Fin (4 * n) ⊕ Fin n) ℂ :=
  Matrix.reindex (literalXColumnEquiv n).symm (literalXColumnEquiv n).symm
    (Matrix.of fun r c => literalXStageA0 q n r (v c))

/-- Every x moment in `M2` is the corresponding Andreief product moment
(`v-analytic.tex:139-153`). -/
theorem literalXStage_hmom2 (q n : ℕ) (v : Fin (5 * n) → ℝ)
    (i : Fin (4 * n)) (c : Fin (4 * n) ⊕ Fin n) :
    literalXStageM2 q n v (Sum.inl i) c =
      ∫ x, literalXStageA2 n i x * literalXStageB2 q n v x c
        ∂Literal.vContourUnitIntervalMeasure := by
  simp [literalXStageM2, literalXStageA0, literalXStageA2,
    literalXStageB2, literalXMoment, Matrix.reindex_apply,
    Equiv.apply_symm_apply]

/-- The integrability required by the x-row Andreief identity.  The zero
extension outside the v interval leaves the v13 kernel unchanged on the
support of the v measure (`v-analytic.tex:109-123`). -/
theorem literalXStage_hint2 (q n : ℕ) (hq : 2 ≤ q)
    (v : Fin (5 * n) → ℝ) (i : Fin (4 * n))
    (c : Fin (4 * n) ⊕ Fin n) :
    Integrable
      (fun x => literalXStageA2 n i x * literalXStageB2 q n v x c)
      Literal.vContourUnitIntervalMeasure := by
  classical
  let t := v (literalXColumnEquiv n c)
  by_cases ht : t ∈ Set.Icc (0 : ℝ) 1
  · have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    have hden : ∀ x ∈ Set.Icc (0 : ℝ) 1,
        (q : ℂ) + (x : ℂ) * (t : ℂ) ≠ 0 := by
      intro x hx
      have hpos : (0 : ℝ) < (q : ℝ) + x * t := by
        have hmul : 0 ≤ x * t := mul_nonneg hx.1 ht.1
        linarith
      have heq : (q : ℂ) + (x : ℂ) * (t : ℂ) =
          ((q : ℝ) + x * t : ℝ) := by
        push_cast
        ring
      rw [heq, Complex.ofReal_ne_zero]
      exact ne_of_gt hpos
    have hpow : Continuous
        (fun x : ℝ => literalXStageA2 n i x) := by
      fun_prop [literalXStageA2, literalXMonomial]
    have hdencont : Continuous
        (fun x : ℝ => (q : ℂ) + (x : ℂ) * (t : ℂ)) := by
      fun_prop
    have hcont : ContinuousOn
        (fun x : ℝ => literalXStageA2 n i x *
          ((q : ℂ) + (x : ℂ) * (t : ℂ))⁻¹)
        (Set.Icc (0 : ℝ) 1) :=
      hpow.continuousOn.mul (hdencont.continuousOn.inv₀ hden)
    have hOn : IntegrableOn
        (fun x : ℝ => literalXStageA2 n i x *
          ((q : ℂ) + (x : ℂ) * (t : ℂ))⁻¹)
        (Set.Icc (0 : ℝ) 1) volume :=
      hcont.integrableOn_compact isCompact_Icc
    have hInt : Integrable
        (fun x : ℝ => literalXStageA2 n i x *
          ((q : ℂ) + (x : ℂ) * (t : ℂ))⁻¹)
        Literal.vContourUnitIntervalMeasure := by
      simpa [Literal.vContourUnitIntervalMeasure] using hOn.integrable
    simpa [literalXStageB2, literalXKernel, t, ht] using hInt
  · simp [literalXStageB2, literalXKernel, t, ht]

/-- The x-stage determinant is exactly the evaluation determinant of the
moment and polynomial rows (`v-analytic.tex:139-153`). -/
theorem literalXStage_halign2 (q n : ℕ) (v : Fin (5 * n) → ℝ) :
    (literalXStageM2 q n v).det =
      (Matrix.of fun k l => literalXStageA0 q n k (v l)).det := by
  exact Matrix.det_reindex_self (literalXColumnEquiv n).symm _

/-- The x-monomial matrix factors as the transposed Vandermonde times the
column diagonal carrying the common `x^(2n)` factor
(`v-analytic.tex:151-153`). -/
theorem literalXMonomialMatrix_factor (n : ℕ) (x : Fin (4 * n) → ℝ) :
    Matrix.of (fun i j => literalXMonomial n i (x j)) =
      (Matrix.vandermonde (fun j => (x j : ℂ))).transpose *
        Matrix.diagonal (fun j => (x j : ℂ) ^ (2 * n)) := by
  classical
  ext i j
  simp only [Matrix.mul_apply, Matrix.diagonal_apply,
    Matrix.transpose_apply, Matrix.of_apply]
  rw [Finset.sum_eq_single j]
  · simp [literalXMonomial, Matrix.vandermonde, pow_add, Nat.add_comm]
  · intro k hk hne
    simp [hne]
  · simp

/-- The product convention for `vContourVandermonde` is the standard
Vandermonde determinant convention (`v-analytic.tex:151-153`). -/
private theorem literalXVandermonde_eq_matrix_det {d : ℕ}
    (z : Fin d → ℂ) :
    (Matrix.vandermonde z).det = Literal.vContourVandermonde z := by
  rw [Matrix.det_vandermonde]
  unfold Literal.vContourVandermonde
  apply Finset.prod_congr rfl
  intro i hi
  have hIoi : Finset.Ioi i =
      (Finset.univ : Finset (Fin d)).filter (fun j => i < j) := by
    ext j
    simp
  rw [hIoi, Finset.prod_filter]

/-- The determinant of the x-monomial rows is the v13 Vandermonde times
`prod x_i^(m/2)` with `m=4n` (`v-analytic.tex:151-153`). -/
theorem literalXMonomialMatrix_det (n : ℕ) (x : Fin (4 * n) → ℝ) :
    (Matrix.of (fun i j => literalXMonomial n i (x j))).det =
      Literal.vContourVandermonde (fun j => (x j : ℂ)) *
        ∏ j : Fin (4 * n), (x j : ℂ) ^ (2 * n) := by
  rw [literalXMonomialMatrix_factor, Matrix.det_mul, Matrix.det_transpose,
    Matrix.det_diagonal, literalXVandermonde_eq_matrix_det]

/-- Frozen-base regression for the x-stage moment identity at `q=2`, the
Li2(1/2) instance of the present signed construction
(`v-analytic.tex:109-153`). -/
theorem literalXStage_hmom2_q2 (n : ℕ) (v : Fin (5 * n) → ℝ)
    (i : Fin (4 * n)) (c : Fin (4 * n) ⊕ Fin n) :
    literalXStageM2 2 n v (Sum.inl i) c =
      ∫ x, literalXStageA2 n i x * literalXStageB2 2 n v x c
        ∂Literal.vContourUnitIntervalMeasure :=
  literalXStage_hmom2 2 n v i c

/-- Frozen-base regression for the x-stage determinant alignment at `q=2`
(`v-analytic.tex:139-153`). -/
theorem literalXStage_halign2_q2 (n : ℕ) (v : Fin (5 * n) → ℝ) :
    (literalXStageM2 2 n v).det =
      (Matrix.of fun k l => literalXStageA0 2 n k (v l)).det :=
  literalXStage_halign2 2 n v

/-- The direct x-kernel/polynomial matrix in the Cauchy--Vandermonde block,
written in v13's row order (`v-analytic.tex:139-153`). -/
def literalXKernelMatrix {m h : ℕ} (q : ℂ) (x : Fin m → ℂ)
    (v : Fin (m + h) → ℂ) : Matrix (Fin (m + h)) (Fin (m + h)) ℂ :=
  Matrix.of fun r c =>
    match (finSumFinEquiv (m := m) (n := h)).symm r with
    | Sum.inl i => (q + x i * v c)⁻¹
    | Sum.inr k => (v c) ^ k.val

/-- Row multipliers for the v13 substitution `t_i=q/x_i`
(`v-analytic.tex:166-173`). -/
def literalXKernelRowScale {m h : ℕ} (x : Fin m → ℂ) :
    Fin (m + h) → ℂ := fun r =>
  match (finSumFinEquiv (m := m) (n := h)).symm r with
  | Sum.inl i => (x i)⁻¹
  | Sum.inr _ => 1

/-- The rational rows in the x-kernel matrix are the row-scaled q/x rows of
the existing v13 Cauchy--Vandermonde matrix. -/
theorem literalXKernelMatrix_eq_diagonal_cvQX {m h : ℕ}
    (q : ℂ) (x : Fin m → ℂ) (v : Fin (m + h) → ℂ)
    (hx : ∀ i, x i ≠ 0) :
    literalXKernelMatrix q x v =
      Matrix.diagonal (literalXKernelRowScale x) *
        CauchyVandermonde.cvQXMatrix q x v := by
  classical
  ext r c
  simp only [literalXKernelMatrix, Matrix.mul_apply, Matrix.diagonal_apply,
    Matrix.of_apply, CauchyVandermonde.cvQXMatrix,
    CauchyVandermonde.cvMatrix]
  rw [Finset.sum_eq_single r]
  · simp only [if_pos rfl, one_mul]
    cases hs : (finSumFinEquiv (m := m) (n := h)).symm r with
    | inl i =>
        simp only [literalXKernelRowScale, hs,
          CauchyVandermonde.cvEntry, Equiv.symm_apply_apply]
        field_simp [hx i]
        simp [hx i, mul_assoc, mul_comm, mul_left_comm]
    | inr k =>
        simp [literalXKernelRowScale, hs,
          CauchyVandermonde.cvEntry, Equiv.symm_apply_apply]
  · intro r' hr' hne
    have hne' : ¬ r = r' := Ne.symm hne
    simp [hne']
  · simp

/-!
The determinant clearing step below is the `t_i=q/x_i` calculation in
`v-analytic.tex:166-194`.  Product factors are left explicit so later
stages can specialize them to the paper's `m=4n`, `h=n` indices.
-/

/-- The cleared determinant formula for v13's literal kernel rows, obtained
from the existing Cauchy--Vandermonde block after `t_i=q/x_i`
(`v-analytic.tex:166-194`). -/
theorem literalXKernelMatrix_det_mul_denominator_eq_vandermonde
    {m h : ℕ} (q : ℂ) (x : Fin m → ℂ) (v : Fin (m + h) → ℂ)
    (hq : q ≠ 0) (hx : ∀ i, x i ≠ 0)
    (hinj : Function.Injective x)
    (hden : ∀ i b, q + x i * v b ≠ 0) :
    (literalXKernelMatrix q x v).det *
        (∏ i : Fin m, ∏ b : Fin (m + h), (q + x i * v b)) =
      (∏ r : Fin (m + h), literalXKernelRowScale x r) *
        (∏ i : Fin m, (x i) ^ (m + h)) *
          (Matrix.vandermonde v).det *
            (Matrix.vandermonde (fun i => q / x i)).det := by
  classical
  let t : Fin m → ℂ := fun i => q / x i
  let scale : ℂ := ∏ r : Fin (m + h), literalXKernelRowScale x r
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
  have hcancel :
      (∏ i : Fin m, (x i)⁻¹ ^ (m + h)) * xp = 1 := by
    dsimp [xp]
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
  have hscale :
      (literalXKernelMatrix q x v).det =
        scale * (CauchyVandermonde.cvQXMatrix q x v).det := by
    rw [literalXKernelMatrix_eq_diagonal_cvQX q x v hx,
      Matrix.det_mul, Matrix.det_diagonal]
  have hcv :
      (CauchyVandermonde.cvQXMatrix q x v).det * d =
        (Matrix.vandermonde v).det * (Matrix.vandermonde t).det := by
    dsimp [CauchyVandermonde.cvQXMatrix, d, t]
    exact CauchyVandermonde.cv_det_mul_denominator_eq_vandermonde
      (fun i => q / x i) v htinj hxy
  calc
    (literalXKernelMatrix q x v).det * p =
        (scale * (CauchyVandermonde.cvQXMatrix q x v).det) * p := by
          rw [hscale]
    _ = scale * xp *
          ((CauchyVandermonde.cvQXMatrix q x v).det * d) := by
          rw [← hdenprod]
          ring
    _ = scale * xp *
          ((Matrix.vandermonde v).det * (Matrix.vandermonde t).det) := by
          rw [hcv]
    _ = scale * xp * (Matrix.vandermonde v).det *
          (Matrix.vandermonde (fun i => q / x i)).det := by
          simp [t, mul_assoc]

end

end Li2Lean.V

#print axioms Li2Lean.V.literalXStage_hmom2
#print axioms Li2Lean.V.literalXStage_hint2
#print axioms Li2Lean.V.literalXStage_halign2
#print axioms Li2Lean.V.literalXMonomialMatrix_factor
#print axioms Li2Lean.V.literalXMonomialMatrix_det
#print axioms Li2Lean.V.literalXStage_hmom2_q2
#print axioms Li2Lean.V.literalXStage_halign2_q2
#print axioms Li2Lean.V.literalXKernelMatrix_eq_diagonal_cvQX
