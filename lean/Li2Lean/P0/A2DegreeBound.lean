/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.Main

namespace Li2Lean

open Polynomial

noncomputable section

/-! The determinant pencil has only `m` affine rows.  We expose this
    row-count degree bound for every base; it is needed by the
    endpoint integerizer producer and does not assert any coefficient data. -/

private def p0BaseDegreeSlope (a : ℚ) (m : ℕ) :
    Matrix (Fin (2 * m)) (Fin (2 * m)) ℚ := fun r c =>
  if r.val < m then 0 else
    -p0AQ a (m / 2) (m / 4 + (r.val - m)) c.val

private def p0BaseDegreeConstant (a : ℚ) (m : ℕ) :
    Matrix (Fin (2 * m)) (Fin (2 * m)) ℚ := fun r c =>
  if r.val < m then
    p0CQ a (m / 2) (m / 4 + r.val) c.val
  else
    p0BQ a (m / 2) (m / 4 + (r.val - m)) c.val

private theorem p0Base_matrix_eq_degree_pencil (a : ℚ) (m : ℕ) :
    p0MatrixQ a m =
      (Polynomial.X : Polynomial ℚ) • (p0BaseDegreeSlope a m).map Polynomial.C +
        (p0BaseDegreeConstant a m).map Polynomial.C := by
  ext r c
  by_cases hr : r.val < m
  · simp [p0MatrixQ, p0BaseDegreeSlope, p0BaseDegreeConstant, hr]
  · simp [p0MatrixQ, p0BaseDegreeSlope, p0BaseDegreeConstant, hr,
      Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    ring

private theorem p0Base_degree_entry_bound (a : ℚ) (m : ℕ)
    (r c : Fin (2 * m)) :
    (p0MatrixQ a m r c).natDegree ≤
      if r.val < m then 0 else 1 := by
  by_cases hr : r.val < m
  · simp [p0MatrixQ, hr]
  · simp [p0MatrixQ, hr]
    let slope : ℚ := p0AQ a (m / 2) (m / 4 + (r.val - m)) c.val
    let b : ℚ := p0BQ a (m / 2) (m / 4 + (r.val - m)) c.val
    have hcalc : (Polynomial.C b - Polynomial.C slope * Polynomial.X).natDegree ≤ 1 := by
      calc
        (Polynomial.C b - Polynomial.C slope * Polynomial.X).natDegree ≤
            max (Polynomial.C b).natDegree
              (Polynomial.C slope * Polynomial.X).natDegree :=
          Polynomial.natDegree_sub_le _ _
        _ ≤ 1 := by
          apply max_le
          · simp
          · calc
              (Polynomial.C slope * Polynomial.X).natDegree ≤
                  (Polynomial.C slope).natDegree + Polynomial.X.natDegree :=
                Polynomial.natDegree_mul_le
              _ ≤ 1 := by norm_num
    simpa [slope, b] using hcalc

private theorem p0A2_affine_row_sum (m : ℕ) :
    (∑ r : Fin (2 * m), if r.val < m then 0 else 1) = m := by
  rw [Fin.sum_univ_eq_sum_range
    (fun i : ℕ => if i < m then 0 else 1) (2 * m)]
  rw [show 2 * m = m + m by omega, Finset.sum_range_add]
  have hleft : (∑ i ∈ Finset.range m, if i < m then 0 else 1) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp [Finset.mem_range.mp hi]
  have hright : (∑ i ∈ Finset.range m, if m + i < m then 0 else 1) = m := by
    have hpoint : ∀ i ∈ Finset.range m, (if m + i < m then 0 else 1) = 1 := by
      intro i hi
      simp [Nat.not_lt_of_ge (Nat.le_add_right m i)]
    rw [Finset.sum_congr rfl hpoint]
    simp
  rw [hleft, hright]
  simp

theorem p0CanonicalPolynomial_degree_bound (q : ℤ) (m : ℕ) (hm4 : 4 ∣ m) :
    ((p0CanonicalPolynomial q m).map (algebraMap ℚ ℝ)).natDegree ≤ m := by
  let a : ℚ := (q : ℚ)
  rw [Polynomial.natDegree_map_eq_of_injective Rat.cast_injective]
  simp [p0CanonicalPolynomial, hm4]
  change (p0MatrixQ a m).det.natDegree ≤ m
  rw [p0Base_matrix_eq_degree_pencil]
  rw [Matrix.det_apply]
  refine (Polynomial.natDegree_sum_le _ _).trans ?_
  refine Multiset.max_le_of_forall_le _ _ ?_
  simp only [forall_apply_eq_imp_iff, true_and, Function.comp_apply,
    Multiset.mem_map, exists_imp, Finset.mem_univ_val]
  intro g
  calc
    Polynomial.natDegree (Equiv.Perm.sign g •
        ∏ i : Fin (2 * m),
          ((Polynomial.X : Polynomial ℚ) •
            (p0BaseDegreeSlope a m).map Polynomial.C +
            (p0BaseDegreeConstant a m).map Polynomial.C) (g i) i) ≤
        Polynomial.natDegree (∏ i : Fin (2 * m),
          ((Polynomial.X : Polynomial ℚ) •
            (p0BaseDegreeSlope a m).map Polynomial.C +
            (p0BaseDegreeConstant a m).map Polynomial.C) (g i) i) := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign g) with hsg | hsg
      · rw [hsg, one_smul]
      · rw [hsg, Units.neg_smul, one_smul, Polynomial.natDegree_neg]
    _ ≤ ∑ i : Fin (2 * m),
        Polynomial.natDegree (((Polynomial.X : Polynomial ℚ) •
          (p0BaseDegreeSlope a m).map Polynomial.C +
          (p0BaseDegreeConstant a m).map Polynomial.C) (g i) i) :=
      Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ i : Fin (2 * m), (if (g i).val < m then 0 else 1) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [← p0Base_matrix_eq_degree_pencil]
      exact p0Base_degree_entry_bound a m (g i) i
    _ = m := by
      calc
        (∑ i : Fin (2 * m), if (g i).val < m then 0 else 1) =
            ∑ i : Fin (2 * m), if i.val < m then 0 else 1 := by
          simpa using
            (Equiv.sum_comp g (fun i : Fin (2 * m) => if i.val < m then 0 else 1))
        _ = m := p0A2_affine_row_sum m


theorem p0A2CanonicalFamily_degree_bound (m : ℕ) (_hm : 0 < m) (hm4 : 4 ∣ m) :
    (p0A2CanonicalFamily.G m).natDegree ≤ m := by
  exact p0CanonicalPolynomial_degree_bound 2 m hm4

end

end Li2Lean

#print axioms Li2Lean.p0A2CanonicalFamily_degree_bound

#print axioms Li2Lean.p0CanonicalPolynomial_degree_bound
