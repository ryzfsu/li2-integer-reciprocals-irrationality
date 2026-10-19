/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.V.VLiteralOuterMomentDet

/-!
# Outer Moment Matrix Determinant Alignment (`H5-hM0`)

This module proves `vLiteralOuterM0_det_eq_vOuterMomentMatrix_det` and
`v13LiteralAndreiefData_actual_hM0`:
```lean
(V.v13LiteralAndreiefData_actual q n hq).M0.det =
  Complex.ofReal ((V.vOuterMomentMatrix q n).det)
```
closing the `hM0` obligation of `V13LiteralS0AssemblyData` (`Li2Lean/B3/S0TAssembly.lean:59-60`).

## Proof Structure
1. Prove forward value lemmas `literalXColumnEquiv_inl_val` and `literalXColumnEquiv_inr_val`
   so every `k : Fin (5 * n)` can be rewritten as `V.literalXColumnEquiv n (Sum.inl ⟨k.val, hk⟩)`
   (when `k.val < 4 * n`) or `V.literalXColumnEquiv n (Sum.inr ⟨k.val - 4 * n, _⟩)` (when `¬ k.val < 4 * n`)
   via `Fin.ext`, avoiding any `finSumFinEquiv.symm` or `cast` unfolding.
2. Apply `V.vLiteralOuterM0_inl_inl_eq` and `V.vLiteralOuterM0_inl_inr_eq` directly to get
   `vLiteralOuterM0_inl_of_lt` and `vLiteralOuterM0_inl_of_not_lt`.
3. Reindex `V.vLiteralOuterM0 q n` to `Fin (9 * n)` via `h5M0ColumnEquiv` and permute rows by
   `h5RowBlockSwapPerm n` (which is definitionally equal to `V.vLiteralRowBlockSwapPerm n`, so its
   sign is `1` by `V.vLiteralRowBlockSwapPerm_sign_eq_one`), canceling `h5M0ColumnEquiv` against
   `(h5M0ColumnEquiv).symm` before comparing entrywise with `(V.vOuterMomentMatrix q n).map Complex.ofRealHom`.
-/

open scoped BigOperators Matrix

namespace Li2Lean.B3

noncomputable section

open Li2Lean V

/-! ## 1. Forward value lemmas for `literalXColumnEquiv` and `vLiteralOuterM0` -/

theorem literalXColumnEquiv_inl_val (n : ℕ) (i : Fin (4 * n)) :
    (V.literalXColumnEquiv n (Sum.inl i)).val = i.val := by
  have h : 4 * n + n = 5 * n := by omega
  simp only [V.literalXColumnEquiv, Equiv.trans_apply, Equiv.cast_apply]
  rw [← Fin.cast_eq_cast h]
  rw [Fin.val_cast]
  simp [finSumFinEquiv]

theorem literalXColumnEquiv_inr_val (n : ℕ) (l : Fin n) :
    (V.literalXColumnEquiv n (Sum.inr l)).val = 4 * n + l.val := by
  have h : 4 * n + n = 5 * n := by omega
  simp only [V.literalXColumnEquiv, Equiv.trans_apply, Equiv.cast_apply]
  rw [← Fin.cast_eq_cast h]
  rw [Fin.val_cast]
  simp [finSumFinEquiv]

theorem vLiteralOuterM0_inl_of_lt (q n : ℕ) (hq : 2 ≤ q)
    (k : Fin (5 * n)) (hk : k.val < 4 * n)
    (c : Fin (5 * n) ⊕ Fin (4 * n)) :
    V.vLiteralOuterM0 q n (Sum.inl k) c =
      Complex.ofReal (V.vOuterMoment q (2 * n + k.val)
        (V.vLiteralOuterColumnIndex n c)) := by
  have hk_eq : k = V.literalXColumnEquiv n (Sum.inl ⟨k.val, hk⟩) := by
    apply Fin.ext
    rw [literalXColumnEquiv_inl_val]
  rw [hk_eq, V.vLiteralOuterM0_inl_inl_eq q n hq ⟨k.val, hk⟩ c]
  simp [literalXColumnEquiv_inl_val]

theorem vLiteralOuterM0_inl_of_not_lt (q n : ℕ)
    (k : Fin (5 * n)) (hk : ¬ k.val < 4 * n)
    (c : Fin (5 * n) ⊕ Fin (4 * n)) :
    V.vLiteralOuterM0 q n (Sum.inl k) c =
      Complex.ofReal (vVEntry (V.vLiteralOuterColumnIndex n c)
        (1 + (k.val - 4 * n))) := by
  have hklt := k.isLt
  have hk_eq : k = V.literalXColumnEquiv n (Sum.inr ⟨k.val - 4 * n, by omega⟩) := by
    apply Fin.ext
    rw [literalXColumnEquiv_inr_val]
    dsimp
    omega
  rw [hk_eq, V.vLiteralOuterM0_inl_inr_eq q n ⟨k.val - 4 * n, by omega⟩ c]
  simp [literalXColumnEquiv_inr_val]

/-! ## 2. Column equivalences and row block swap on `Fin (9 * n)` -/

private def h5M1ColumnEquiv (n : ℕ) :
    Fin (9 * n) ≃ Fin (4 * n) ⊕ Fin (5 * n) := by
  let h : 9 * n = 4 * n + 5 * n := by omega
  exact (Equiv.cast (congrArg Fin h)).trans
    (finSumFinEquiv (m := 4 * n) (n := 5 * n)).symm

private def h5M0ColumnEquiv (n : ℕ) :
    Fin (9 * n) ≃ Fin (5 * n) ⊕ Fin (4 * n) := by
  let h : 9 * n = 5 * n + 4 * n := by omega
  exact (Equiv.cast (congrArg Fin h)).trans
    (finSumFinEquiv (m := 5 * n) (n := 4 * n)).symm

private theorem h5M1ColumnEquiv_apply (n : ℕ) (j : Fin (9 * n)) :
    h5M1ColumnEquiv n j = V.vLiteralM1ColumnOfFin n j := by
  simp only [h5M1ColumnEquiv, V.vLiteralM1ColumnOfFin,
    Equiv.trans_apply, Equiv.cast_apply]
  split_ifs with h
  · have hc : cast (congrArg Fin (by omega : 9 * n = 4 * n + 5 * n)) j =
        Fin.castAdd (5 * n) ⟨j.val, h⟩ := by
      rw [← Fin.cast_eq_cast (by omega : 9 * n = 4 * n + 5 * n)]
      apply Fin.ext
      rfl
    rw [hc]
    simpa [finSumFinEquiv] using
      (Fin.addCases_left
        (motive := fun _ => Fin (4 * n) ⊕ Fin (5 * n))
        (left := fun i => Sum.inl i) (right := fun i => Sum.inr i)
        (⟨j.val, h⟩ : Fin (4 * n)))
  · have hc : cast (congrArg Fin (by omega : 9 * n = 4 * n + 5 * n)) j =
        Fin.natAdd (4 * n) ⟨j.val - 4 * n, by omega⟩ := by
      rw [← Fin.cast_eq_cast (by omega : 9 * n = 4 * n + 5 * n)]
      apply Fin.ext
      simp
      omega
    rw [hc]
    simp only [finSumFinEquiv, Equiv.symm]
    change (finSumFinEquiv (m := 4 * n) (n := 5 * n)).invFun
      (Fin.natAdd (4 * n) ⟨j.val - 4 * n, by omega⟩) = _
    simp only [finSumFinEquiv]
    have he := Fin.addCases_right
      (motive := fun _ => Fin (4 * n) ⊕ Fin (5 * n))
      (left := fun i => Sum.inl i) (right := fun i => Sum.inr i)
      (⟨j.val - 4 * n, by omega⟩ : Fin (5 * n))
    rw [he]

private theorem h5M0ColumnEquiv_apply (n : ℕ) (j : Fin (9 * n)) :
    h5M0ColumnEquiv n j = V.vLiteralM0ColumnOfFin n j := by
  simp only [h5M0ColumnEquiv, V.vLiteralM0ColumnOfFin,
    Equiv.trans_apply, Equiv.cast_apply]
  split_ifs with h
  · have hc : cast (congrArg Fin (by omega : 9 * n = 5 * n + 4 * n)) j =
        Fin.castAdd (4 * n) ⟨j.val, h⟩ := by
      rw [← Fin.cast_eq_cast (by omega : 9 * n = 5 * n + 4 * n)]
      apply Fin.ext
      rfl
    rw [hc]
    simpa [finSumFinEquiv] using
      (Fin.addCases_left
        (motive := fun _ => Fin (5 * n) ⊕ Fin (4 * n))
        (left := fun i => Sum.inl i) (right := fun i => Sum.inr i)
        (⟨j.val, h⟩ : Fin (5 * n)))
  · have hc : cast (congrArg Fin (by omega : 9 * n = 5 * n + 4 * n)) j =
        Fin.natAdd (5 * n) ⟨j.val - 5 * n, by omega⟩ := by
      rw [← Fin.cast_eq_cast (by omega : 9 * n = 5 * n + 4 * n)]
      apply Fin.ext
      simp
      omega
    rw [hc]
    simp only [finSumFinEquiv, Equiv.symm]
    change (finSumFinEquiv (m := 5 * n) (n := 4 * n)).invFun
      (Fin.natAdd (5 * n) ⟨j.val - 5 * n, by omega⟩) = _
    simp only [finSumFinEquiv]
    have he := Fin.addCases_right
      (motive := fun _ => Fin (5 * n) ⊕ Fin (4 * n))
      (left := fun i => Sum.inl i) (right := fun i => Sum.inr i)
      (⟨j.val - 5 * n, by omega⟩ : Fin (4 * n))
    rw [he]

private def h5RowBlockSwapPerm (n : ℕ) : Equiv.Perm (Fin (9 * n)) :=
  (h5M1ColumnEquiv n).trans
    ((Equiv.sumComm (Fin (4 * n)) (Fin (5 * n))).trans
      (h5M0ColumnEquiv n).symm)

private theorem h5RowBlockSwapPerm_eq (n : ℕ) :
    h5RowBlockSwapPerm n = V.vLiteralRowBlockSwapPerm n := rfl

private def h5SizeEquiv (n : ℕ) : Fin (2 * vM n + vS n) ≃ Fin (9 * n) := by
  have h : 2 * vM n + vS n = 9 * n := by
    rw [vM_eq, vS_eq]
    omega
  exact Equiv.cast (congrArg Fin h)

private theorem fin_cast_symm_val {a b : ℕ} (h : a = b) (r : Fin b) :
    ((Equiv.cast (congrArg Fin h)).symm r).val = r.val := by
  subst b
  rfl

private theorem h5SizeEquiv_symm_val (n : ℕ) (r : Fin (9 * n)) :
    ((h5SizeEquiv n).symm r).val = r.val := by
  have h : 2 * vM n + vS n = 9 * n := by
    rw [vM_eq, vS_eq]
    omega
  change ((Equiv.cast (congrArg Fin h)).symm r).val = r.val
  exact fin_cast_symm_val h r

/-! ## 3. Entrywise and determinant alignment of `vLiteralOuterM0` with `vOuterMomentMatrix` -/

theorem vLiteralOuterM0_det_eq_vOuterMomentMatrix_det
    (q n : ℕ) (hq : 2 ≤ q) :
    (V.vLiteralOuterM0 q n).det =
      Complex.ofReal ((V.vOuterMomentMatrix q n).det) := by
  classical
  let B : Matrix (Fin (9 * n)) (Fin (9 * n)) ℂ :=
    Matrix.reindex (h5M0ColumnEquiv n).symm (h5M0ColumnEquiv n).symm
      (V.vLiteralOuterM0 q n)
  let A : Matrix (Fin (9 * n)) (Fin (9 * n)) ℂ :=
    Matrix.reindex (h5SizeEquiv n) (h5SizeEquiv n)
      ((V.vOuterMomentMatrix q n).map Complex.ofRealHom)
  have hB : (V.vLiteralOuterM0 q n).det = B.det :=
    (Matrix.det_reindex_self (h5M0ColumnEquiv n).symm _).symm
  have hA : ((V.vOuterMomentMatrix q n).map Complex.ofRealHom).det = A.det :=
    (Matrix.det_reindex_self (h5SizeEquiv n) _).symm
  have hmap : ((V.vOuterMomentMatrix q n).map Complex.ofRealHom).det =
      Complex.ofReal ((V.vOuterMomentMatrix q n).det) :=
    (RingHom.map_det Complex.ofRealHom (V.vOuterMomentMatrix q n)).symm
  have hAB : A = B.submatrix (h5RowBlockSwapPerm n) id := by
    ext r c
    simp only [A, B, Matrix.reindex_apply, Matrix.submatrix_apply, id_eq,
      h5RowBlockSwapPerm, Equiv.trans_apply, Equiv.symm_symm]
    rw [h5M1ColumnEquiv_apply n r, h5M0ColumnEquiv_apply n c]
    simp only [Equiv.apply_symm_apply]
    have hcol : V.vLiteralOuterColumnIndex n (V.vLiteralM0ColumnOfFin n c) = n + c.val :=
      V.vLiteralOuterColumnIndexOfFin n c
    have hr_val : ((h5SizeEquiv n).symm r).val = r.val := h5SizeEquiv_symm_val n r
    have hc_val : ((h5SizeEquiv n).symm c).val = c.val := h5SizeEquiv_symm_val n c
    have hm_eq : vM n = 4 * n := vM_eq n
    by_cases htop : r.val < 4 * n
    · have htop_m : ((h5SizeEquiv n).symm r).val < vM n := by omega
      simp only [V.vLiteralM1ColumnOfFin, dif_pos htop, Equiv.sumComm_apply, Sum.swap_inl]
      rw [Matrix.map_apply]
      change Complex.ofReal ((V.vOuterMomentMatrix q n) ((h5SizeEquiv n).symm r) ((h5SizeEquiv n).symm c)) =
        (vCEntry (-(q : ℤ)) (vIIndexNat n r.val) (V.vLiteralOuterColumnIndex n (V.vLiteralM0ColumnOfFin n c)) : ℂ)
      rw [V.vOuterMomentMatrix, if_pos htop_m, hr_val, hc_val, hcol]
      simp [V.vIIndexNat]
    · have htop_m : ¬ ((h5SizeEquiv n).symm r).val < vM n := by omega
      simp only [V.vLiteralM1ColumnOfFin, dif_neg htop, Equiv.sumComm_apply, Sum.swap_inr]
      let k : Fin (5 * n) := ⟨r.val - 4 * n, by omega⟩
      by_cases hmid : r.val < 8 * n
      · have hmid_m : ((h5SizeEquiv n).symm r).val < 2 * vM n := by omega
        have hk_lt : k.val < 4 * n := by dsimp [k]; omega
        rw [vLiteralOuterM0_inl_of_lt q n hq k hk_lt, hcol]
        rw [Matrix.map_apply]
        change Complex.ofReal ((V.vOuterMomentMatrix q n) ((h5SizeEquiv n).symm r) ((h5SizeEquiv n).symm c)) = _
        rw [V.vOuterMomentMatrix, if_neg htop_m, if_pos hmid_m, hr_val, hc_val, hm_eq]
      · have hmid_m : ¬ ((h5SizeEquiv n).symm r).val < 2 * vM n := by omega
        have hk_not_lt : ¬ k.val < 4 * n := by dsimp [k]; omega
        rw [vLiteralOuterM0_inl_of_not_lt q n k hk_not_lt, hcol]
        rw [Matrix.map_apply]
        change Complex.ofReal ((V.vOuterMomentMatrix q n) ((h5SizeEquiv n).symm r) ((h5SizeEquiv n).symm c)) = _
        rw [V.vOuterMomentMatrix, if_neg htop_m, if_neg hmid_m, hr_val, hc_val, hm_eq]
        have hsub : r.val - 2 * (4 * n) = k.val - 4 * n := by dsimp [k]; omega
        rw [hsub]
  rw [hB, ← hmap, hA, hAB, Matrix.det_permute, h5RowBlockSwapPerm_eq,
    V.vLiteralRowBlockSwapPerm_sign_eq_one]
  simp

/-- The exact `hM0` field for `V.v13LiteralAndreiefData_actual q n hq`. -/
theorem v13LiteralAndreiefData_actual_hM0
    (q n : ℕ) (hq : 2 ≤ q) :
    (V.v13LiteralAndreiefData_actual q n hq).M0.det =
      Complex.ofReal ((V.vOuterMomentMatrix q n).det) :=
  vLiteralOuterM0_det_eq_vOuterMomentMatrix_det q n hq

end

end Li2Lean.B3

#print axioms Li2Lean.B3.vLiteralOuterM0_det_eq_vOuterMomentMatrix_det
#print axioms Li2Lean.B3.v13LiteralAndreiefData_actual_hM0
