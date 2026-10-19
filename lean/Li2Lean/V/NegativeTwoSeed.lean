/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Mathlib
import Li2Lean.Kit.EndpointCriterion
import Li2Lean.Statement

namespace Li2Lean

/-!
The `q = 2` seed certificate for the signed V-family.  The definitions below
are the source matrix in v13 `chapters/nonvanishing.tex`, Negative V seeds,
specialized to `a = -2`, `m = 4`, `I = {2,3,4,5}`, `J = {1,...,9}` and
`Lambda = {1}`; this file verifies its reduction modulo the listed seed prime.
This finite seed is only the nonvanishing input.  It does not establish the
all-index signed energy or integerizer bounds needed by the endpoint criterion.
-/

abbrev VTwoSeedRing := ZMod 11

private def vTwoSeedBase : VTwoSeedRing := ((-2 : ℤ) : VTwoSeedRing)

private def vTwoSeedT (j : ℕ) : VTwoSeedRing :=
  ∑ s ∈ Finset.range j,
    vTwoSeedBase ^ (j - (s + 1)) * (((s + 1 : ℕ) : VTwoSeedRing)⁻¹)

private def vTwoSeedB (j : ℕ) : VTwoSeedRing :=
  ∑ s ∈ Finset.range j,
    vTwoSeedBase ^ (j - (s + 1)) *
      (((s + 1 : ℕ) : VTwoSeedRing) ^ 2)⁻¹

private def vTwoSeedCEntry (i j : ℕ) : VTwoSeedRing :=
  if i = j then 0 else
    (vTwoSeedBase ^ i - vTwoSeedBase ^ j) *
      (((j : VTwoSeedRing) - (i : VTwoSeedRing))⁻¹)

private def vTwoSeedBEntry (i j : ℕ) : VTwoSeedRing :=
  if i = j then vTwoSeedB i else
    (vTwoSeedT i - vTwoSeedT j) *
      (((j : VTwoSeedRing) - (i : VTwoSeedRing))⁻¹)

private def vTwoSeedAEntry (i j : ℕ) : VTwoSeedRing :=
  if i = j then vTwoSeedBase ^ i else 0

/-- The q=2, n=1 signed V source matrix, reduced modulo 11. -/
private def vTwoSeedMatrix (T : VTwoSeedRing) :
    Matrix (Fin 9) (Fin 9) VTwoSeedRing := fun r c =>
  let j := c.val + 1
  if r.val < 4 then
    vTwoSeedCEntry (r.val + 2) j
  else if r.val < 8 then
    let i := r.val - 2
    vTwoSeedBEntry i j - T * vTwoSeedAEntry i j
  else
    (((j + 1 : ℕ) : VTwoSeedRing)⁻¹)

theorem vTwoSeedPrime : Nat.Prime 11 := by norm_num

theorem vTwoSeedPrime_gt_seven : 7 < 11 := by norm_num

/-- The paper's seed denominator support is `{2,3,5,7}`; 11 is a unit on it. -/
theorem vTwoSeedPrime_coprime_denominator : Nat.Coprime 11 2520 := by
  norm_num

theorem vTwoSeedPrime_coprime_denominator_sq : Nat.Coprime 11 (2520 ^ 2) := by
  norm_num

theorem vTwoSeedPrime_coprime_base_and_shift : Nat.Coprime 11 (2 * 3) := by
  norm_num

private theorem vTwoSeed_inv_two : (2 : VTwoSeedRing)⁻¹ = 6 := by
  apply ZMod.inv_eq_of_mul_eq_one
  decide

private theorem vTwoSeed_inv_three : (3 : VTwoSeedRing)⁻¹ = 4 := by
  apply ZMod.inv_eq_of_mul_eq_one
  decide

private theorem vTwoSeed_inv_four : (4 : VTwoSeedRing)⁻¹ = 3 := by
  apply ZMod.inv_eq_of_mul_eq_one
  decide

private theorem vTwoSeed_inv_five : (5 : VTwoSeedRing)⁻¹ = 9 := by
  apply ZMod.inv_eq_of_mul_eq_one
  decide

private theorem vTwoSeed_inv_six : (6 : VTwoSeedRing)⁻¹ = 2 := by
  apply ZMod.inv_eq_of_mul_eq_one
  decide

private theorem vTwoSeed_inv_seven : (7 : VTwoSeedRing)⁻¹ = 8 := by
  apply ZMod.inv_eq_of_mul_eq_one
  decide

private theorem vTwoSeed_inv_eight : (8 : VTwoSeedRing)⁻¹ = 7 := by
  apply ZMod.inv_eq_of_mul_eq_one
  decide

private theorem vTwoSeed_inv_nine : (9 : VTwoSeedRing)⁻¹ = 5 := by
  apply ZMod.inv_eq_of_mul_eq_one
  decide

private theorem vTwoSeed_inv_ten : (10 : VTwoSeedRing)⁻¹ = 10 := by
  apply ZMod.inv_eq_of_mul_eq_one
  decide

private theorem vTwoSeed_inv_sixteen : (16 : VTwoSeedRing)⁻¹ = 9 := by
  apply ZMod.inv_eq_of_mul_eq_one
  decide

private theorem vTwoSeed_inv_twentyfive : (25 : VTwoSeedRing)⁻¹ = 4 := by
  apply ZMod.inv_eq_of_mul_eq_one
  decide

private theorem vTwoSeed_inv_neg_one : (-1 : VTwoSeedRing)⁻¹ = 10 := by
  apply ZMod.inv_eq_of_mul_eq_one
  decide

private theorem vTwoSeed_inv_neg_two : (-2 : VTwoSeedRing)⁻¹ = 5 := by
  apply ZMod.inv_eq_of_mul_eq_one
  decide

private theorem vTwoSeed_inv_neg_three : (-3 : VTwoSeedRing)⁻¹ = 7 := by
  apply ZMod.inv_eq_of_mul_eq_one
  decide

private theorem vTwoSeed_inv_neg_four : (-4 : VTwoSeedRing)⁻¹ = 8 := by
  apply ZMod.inv_eq_of_mul_eq_one
  decide

private theorem vTwoSeed_inv_two_sq : ((2 : VTwoSeedRing) ^ 2)⁻¹ = 3 := by
  apply ZMod.inv_eq_of_mul_eq_one
  decide

private theorem vTwoSeed_inv_three_sq : ((3 : VTwoSeedRing) ^ 2)⁻¹ = 5 := by
  apply ZMod.inv_eq_of_mul_eq_one
  decide

private theorem vTwoSeed_inv_four_sq : ((4 : VTwoSeedRing) ^ 2)⁻¹ = 9 := by
  apply ZMod.inv_eq_of_mul_eq_one
  decide

private theorem vTwoSeed_inv_five_sq : ((5 : VTwoSeedRing) ^ 2)⁻¹ = 4 := by
  apply ZMod.inv_eq_of_mul_eq_one
  decide

/- The explicit matrix is a cheap kernel-checkable certificate for all source
entries.  It is intentionally separate from the 9-by-9 determinant reduction:
the latter is a larger arithmetic certificate and remains a pending input. -/
theorem vTwoSeed_matrix_explicit :
    vTwoSeedMatrix 0 = !![
      5, 0, 1, 5, 1, 7, 0, 2, 3;
      3, 1, 0, 9, 1, 9, 8, 0, 7;
      5, 5, 9, 0, 4, 9, 4, 6, 0;
      2, 1, 1, 4, 0, 3, 4, 3, 10;
      8, 1, 8, 2, 2, 5, 6, 0, 1;
      8, 8, 3, 7, 10, 4, 0, 5, 9;
      4, 2, 7, 3, 2, 8, 5, 10, 5;
      9, 2, 10, 2, 9, 3, 1, 9, 3;
      6, 4, 3, 9, 2, 8, 7, 5, 10
    ] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [vTwoSeedMatrix, vTwoSeedCEntry, vTwoSeedBEntry,
      vTwoSeedAEntry, vTwoSeedT, vTwoSeedB, vTwoSeedBase,
      vTwoSeed_inv_two, vTwoSeed_inv_three, vTwoSeed_inv_four,
      vTwoSeed_inv_five, vTwoSeed_inv_six, vTwoSeed_inv_seven,
      vTwoSeed_inv_eight, vTwoSeed_inv_nine, vTwoSeed_inv_ten,
      vTwoSeed_inv_sixteen, vTwoSeed_inv_twentyfive,
      vTwoSeed_inv_neg_one, vTwoSeed_inv_neg_two, vTwoSeed_inv_neg_three,
      vTwoSeed_inv_neg_four, vTwoSeed_inv_two_sq, vTwoSeed_inv_three_sq,
      vTwoSeed_inv_four_sq, vTwoSeed_inv_five_sq,
      Finset.sum_range_succ] <;>
    decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
private structure VTwoSeedRowAdd where
  target : Fin 9
  source : Fin 9
  coefficient : VTwoSeedRing

private def vTwoSeedApplyRowAdds : Matrix (Fin 9) (Fin 9) VTwoSeedRing →
    List VTwoSeedRowAdd → Matrix (Fin 9) (Fin 9) VTwoSeedRing
  | M, [] => M
  | M, op :: ops =>
      vTwoSeedApplyRowAdds
        (M.updateRow op.target (M op.target + op.coefficient • M op.source)) ops

private def vTwoSeedPreOps₁ : List VTwoSeedRowAdd := [
  ⟨1, 0, 6⟩, ⟨2, 0, 10⟩, ⟨3, 0, 4⟩, ⟨4, 0, 5⟩,
  ⟨5, 0, 5⟩, ⟨6, 0, 8⟩, ⟨7, 0, 7⟩, ⟨8, 0, 1⟩
]

private def vTwoSeedPreOps₂ : List VTwoSeedRowAdd := [
  ⟨2, 1, 6⟩, ⟨3, 1, 10⟩, ⟨4, 1, 10⟩, ⟨5, 1, 3⟩,
  ⟨6, 1, 9⟩, ⟨7, 1, 9⟩, ⟨8, 1, 7⟩
]

private def vTwoSeedPostOps : List VTwoSeedRowAdd := [
  ⟨4, 2, 7⟩, ⟨5, 2, 4⟩, ⟨6, 2, 3⟩, ⟨7, 2, 5⟩, ⟨8, 2, 2⟩,
  ⟨4, 3, 2⟩, ⟨5, 3, 6⟩, ⟨6, 3, 4⟩, ⟨7, 3, 8⟩, ⟨8, 3, 2⟩,
  ⟨5, 4, 1⟩, ⟨6, 4, 3⟩, ⟨7, 4, 9⟩, ⟨8, 4, 6⟩,
  ⟨6, 5, 9⟩, ⟨7, 5, 7⟩, ⟨8, 5, 7⟩,
  ⟨7, 6, 3⟩, ⟨8, 6, 4⟩, ⟨8, 7, 7⟩
]

private def vTwoSeedRowSwap : Equiv.Perm (Fin 9) := Equiv.swap 2 3

private def vTwoSeedL : Matrix (Fin 9) (Fin 9) VTwoSeedRing := !![
  1, 0, 0, 0, 0, 0, 0, 0, 0;
  5, 1, 0, 0, 0, 0, 0, 0, 0;
  7, 1, 1, 0, 0, 0, 0, 0, 0;
  1, 5, 0, 1, 0, 0, 0, 0, 0;
  6, 1, 4, 9, 1, 0, 0, 0, 0;
  6, 8, 7, 5, 10, 1, 0, 0, 0;
  3, 2, 8, 7, 8, 2, 1, 0, 0;
  4, 2, 6, 3, 2, 4, 8, 1, 0;
  10, 4, 9, 9, 5, 4, 7, 4, 1
]

private def vTwoSeedU : Matrix (Fin 9) (Fin 9) VTwoSeedRing := !![
  5, 0, 1, 5, 1, 7, 0, 2, 3;
  0, 1, 6, 6, 7, 7, 8, 1, 3;
  0, 0, 10, 7, 8, 2, 7, 10, 8;
  0, 0, 0, 9, 1, 0, 8, 10, 4;
  0, 0, 0, 0, 3, 3, 8, 0, 0;
  0, 0, 0, 0, 0, 5, 9, 8, 1;
  0, 0, 0, 0, 0, 0, 4, 1, 6;
  0, 0, 0, 0, 0, 0, 0, 1, 5;
  0, 0, 0, 0, 0, 0, 0, 0, 3
]

private theorem vTwoSeed_lu :
    (vTwoSeedMatrix 0).submatrix vTwoSeedRowSwap id = vTwoSeedL * vTwoSeedU := by
  rw [vTwoSeed_matrix_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;> decide +kernel

/- The former recursive row-operation certificate is retained in the source
   history but excluded from elaboration; the explicit LU certificate above
   is the only proof path used by vTwoSeed_det_zero.
private def vTwoSeedUpperMatrix : Matrix (Fin 9) (Fin 9) VTwoSeedRing := !![
  5, 0, 1, 5, 1, 7, 0, 2, 3;
  0, 1, 6, 6, 7, 7, 8, 1, 3;
  0, 0, 10, 7, 8, 2, 7, 10, 8;
  0, 0, 0, 9, 1, 0, 8, 10, 4;
  0, 0, 0, 0, 3, 3, 8, 0, 0;
  0, 0, 0, 0, 0, 5, 9, 8, 1;
  0, 0, 0, 0, 0, 0, 4, 1, 6;
  0, 0, 0, 0, 0, 0, 0, 1, 5;
  0, 0, 0, 0, 0, 0, 0, 0, 3
]

private theorem vTwoSeed_pre_stage₁ :
    vTwoSeedApplyRowAdds (vTwoSeedMatrix 0) vTwoSeedPreOps₁ = !![
      5, 0, 1, 5, 1, 7, 0, 2, 3;
      0, 1, 6, 6, 7, 7, 8, 1, 3;
      0, 5, 8, 6, 3, 2, 4, 4, 8;
      0, 1, 5, 2, 4, 9, 4, 0, 0;
      0, 1, 2, 5, 7, 7, 6, 10, 5;
      0, 8, 8, 10, 4, 6, 0, 4, 2;
      0, 2, 4, 10, 10, 9, 5, 4, 7;
      0, 2, 6, 4, 5, 8, 1, 1, 2;
      0, 4, 4, 3, 3, 4, 7, 7, 2
    ] := by
  rw [vTwoSeed_matrix_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [vTwoSeedApplyRowAdds, vTwoSeedPreOps₁] <;> decide

private theorem vTwoSeed_pre_stage₂ :
    vTwoSeedApplyRowAdds (!![
      5, 0, 1, 5, 1, 7, 0, 2, 3;
      0, 1, 6, 6, 7, 7, 8, 1, 3;
      0, 5, 8, 6, 3, 2, 4, 4, 8;
      0, 1, 5, 2, 4, 9, 4, 0, 0;
      0, 1, 2, 5, 7, 7, 6, 10, 5;
      0, 8, 8, 10, 4, 6, 0, 4, 2;
      0, 2, 4, 10, 10, 9, 5, 4, 7;
      0, 2, 6, 4, 5, 8, 1, 1, 2;
      0, 4, 4, 3, 3, 4, 7, 7, 2
    ]) vTwoSeedPreOps₂ = !![
      5, 0, 1, 5, 1, 7, 0, 2, 3;
      0, 1, 6, 6, 7, 7, 8, 1, 3;
      0, 0, 0, 9, 1, 0, 8, 10, 4;
      0, 0, 10, 7, 8, 2, 7, 10, 8;
      0, 0, 7, 10, 0, 0, 9, 9, 2;
      0, 0, 4, 6, 3, 5, 2, 7, 0;
      0, 0, 3, 9, 7, 6, 0, 2, 1;
      0, 0, 5, 3, 2, 5, 7, 10, 7;
      0, 0, 2, 1, 8, 9, 8, 3, 1
    ] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [vTwoSeedApplyRowAdds, vTwoSeedPreOps₂] <;> decide

private theorem vTwoSeed_det_applyRowAdds
    (M : Matrix (Fin 9) (Fin 9) VTwoSeedRing)
    (ops : List VTwoSeedRowAdd)
    (hops : ∀ op ∈ ops, op.target ≠ op.source) :
    (vTwoSeedApplyRowAdds M ops).det = M.det := by
  induction ops generalizing M with
  | nil => rfl
  | cons op ops ih =>
      simp only [vTwoSeedApplyRowAdds]
      rw [ih]
      · exact Matrix.det_updateRow_add_smul_self
          (R := VTwoSeedRing) _ (hops op (by simp)) op.coefficient
      · intro q hq
        exact hops q (by simp [hq])

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
private theorem vTwoSeed_elimination_result :
    vTwoSeedApplyRowAdds
      ((vTwoSeedApplyRowAdds
        (vTwoSeedApplyRowAdds (vTwoSeedMatrix 0) vTwoSeedPreOps₁)
        vTwoSeedPreOps₂).submatrix vTwoSeedRowSwap id)
      vTwoSeedPostOps = vTwoSeedUpperMatrix := by
  rw [vTwoSeed_pre_stage₁, vTwoSeed_pre_stage₂]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [vTwoSeedApplyRowAdds, vTwoSeedPostOps,
      vTwoSeedUpperMatrix, vTwoSeedRowSwap, Equiv.swap] <;> decide
 -/


private theorem vTwoSeed_L_lower : vTwoSeedL.IsLowerTriangular := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide +kernel

private theorem vTwoSeed_U_upper : vTwoSeedU.IsUpperTriangular := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide +kernel

private theorem vTwoSeed_L_det : vTwoSeedL.det = 1 := by
  rw [Matrix.det_of_isLowerTriangular vTwoSeedL vTwoSeed_L_lower]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  decide +kernel

private theorem vTwoSeed_U_det : vTwoSeedU.det = 7 := by
  rw [Matrix.det_of_isUpperTriangular vTwoSeed_U_upper]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  decide +kernel

private theorem vTwoSeed_swap_det :
    ((vTwoSeedMatrix 0).submatrix vTwoSeedRowSwap id).det =
      -(vTwoSeedMatrix 0).det := by
  rw [Matrix.det_permute vTwoSeedRowSwap, vTwoSeedRowSwap,
    Equiv.Perm.sign_swap (show (2 : Fin 9) ≠ 3 by decide)]
  simp

theorem vTwoSeed_det_zero : (vTwoSeedMatrix 0).det = 4 := by
  have h := vTwoSeed_swap_det
  rw [vTwoSeed_lu, Matrix.det_mul, vTwoSeed_L_det, vTwoSeed_U_det] at h
  have h3 : (-((1 : VTwoSeedRing) * 7) : VTwoSeedRing) = 4 := by decide +kernel
  exact (neg_eq_iff_eq_neg.mpr h).symm.trans h3

/--
The fixed-base endpoint criterion already used by the positive construction
also applies to the signed q=2 determinant once its complete certificate is
provided.  The seed theorem above supplies only the certificate's
nonvanishing component.
-/
theorem li2_neg_two_irrational_of_v_endpoint_certificate
    (certificate : EndpointCertificate (li2InvValue (-2 : ℤ))) :
    Irrational (li2InvValue (-2 : ℤ)) :=
  ContourKit.endpoint_criterion certificate

end Li2Lean
