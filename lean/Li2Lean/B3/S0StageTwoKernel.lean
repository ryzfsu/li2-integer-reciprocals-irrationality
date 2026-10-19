/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B3.S0RestrictedKernel

/-!
# Stage-2 Determinant Identity and Restricted S0 Kernel Factorization (`H5-hKernel`)

This module proves the Stage-2 determinant evaluation on the unit cubes and combines
it with `v13Literal_stage1_andreiefProduct_eq` (`Li2Lean/B3/S0RestrictedKernel.lean:63`)
to close the restricted `hKernel` identity for `V.v13LiteralAndreiefData_actual`:

1. **`vandermonde_q_div_mul_pow_eq`**:
   Proves the Vandermonde inversion identity
   `(∏ i : Fin m, x i ^ (m - 1)) * (Matrix.vandermonde (fun i => q / x i)).det = (-q) ^ (Nat.choose m 2) * V.Literal.vContourVandermonde x`
   via the matrix factorization
   `Matrix.diagonal (fun i => x i ^ (m - 1)) * Matrix.vandermonde (fun i => q / x i) = Matrix.projVandermonde (fun _ => 1) x * Matrix.diagonal (fun k => q ^ k.val)`.
2. **`v13Literal_stage2_andreiefProduct_mul_den_eq` & `v13Literal_stage2_andreiefProduct_eq`**:
   Proves the Stage-2 Andreief determinant identity on `(∀ i, x i ∈ Set.Icc 0 1)` and
   `(∀ b, v b ∈ Set.Icc 0 1)`, handling the non-degenerate branch via
   `V.literalXKernelMatrix_det_mul_denominator_eq_vandermonde` and the degenerate
   branches (`∃ i, x i = 0` or `¬ Function.Injective x`) via
   `zero_literal_andreiefProduct_zero`, `duplicate_literal_andreiefProduct_zero`, and
   `duplicate_vandermonde_zero`.
3. **`v13Literal_restricted_hKernel`**:
   Combines `v13Literal_stage1_andreiefProduct_eq` and `v13Literal_stage2_andreiefProduct_eq`
   with the exponent identity `Nat.choose (4 * n) 2 + ∑ k : Fin (4 * n), (2 * n + k.val) = 24 * n ^ 2 - 4 * n`
   to prove the exact `hKernel` premise of `vContourTripleIntegral_eq_const_mul_canonicalS1Andreief_restrict`.
-/

open scoped BigOperators Matrix
open MeasureTheory

namespace Li2Lean.B3

noncomputable section

open Li2Lean V

/-! ## 1. Finite index sums and `Nat.choose (4 * n) 2` identities -/

private theorem sum_fin_val_eq_choose_two (m : ℕ) :
    (∑ k : Fin m, (k : ℕ)) = Nat.choose m 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, Fin.val_succ, zero_add]
      rw [Finset.sum_add_distrib, ih]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
      simpa [Nat.choose_one_right, add_comm] using (Nat.choose_succ_succ m 1).symm

private theorem sum_fin_card_Ioi_eq_choose_two (m : ℕ) :
    (∑ i : Fin m, (Finset.Ioi i).card) = Nat.choose m 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Fin.sum_univ_succ]
      have htail :
          (∑ i : Fin m, (Finset.Ioi i.succ).card) =
            ∑ i : Fin m, (Finset.Ioi i).card := by
        apply Finset.sum_congr rfl
        intro i _
        simp only [Fin.card_Ioi, Fin.val_succ]
        omega
      rw [htail, ih]
      simpa [Fin.card_Ioi] using (Nat.choose_succ_succ m 1).symm

theorem choose_four_mul_two_even (n : ℕ) :
    Even (Nat.choose (4 * n) 2) := by
  rw [Nat.choose_two_right]
  have hmul : 4 * n * (4 * n - 1) = 2 * (2 * n * (4 * n - 1)) := by ring
  rw [hmul, Nat.mul_div_right _ (by decide)]
  refine ⟨n * (4 * n - 1), ?_⟩
  ring

theorem v13_qscale_exponent_eq (n : ℕ) :
    Nat.choose (4 * n) 2 + (∑ k : Fin (4 * n), (2 * n + (k : ℕ))) =
      24 * n ^ 2 - 4 * n := by
  rw [Finset.sum_add_distrib, sum_fin_val_eq_choose_two]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rcases n with _ | m
  · simp
  · have hsub1 : 4 * (m + 1) - 1 = 4 * m + 3 := by omega
    have hchoose : Nat.choose (4 * (m + 1)) 2 = 2 * (m + 1) * (4 * m + 3) := by
      rw [Nat.choose_two_right, hsub1]
      have hmul : 4 * (m + 1) * (4 * m + 3) = 2 * (2 * (m + 1) * (4 * m + 3)) := by ring
      rw [hmul, Nat.mul_div_right _ (by decide)]
    rw [hchoose]
    symm
    apply Nat.sub_eq_of_eq_add
    ring

theorem v13_qscale_exponent_even (n : ℕ) :
    Even (24 * n ^ 2 - 4 * n) := by
  rcases n with _ | m
  · simp
  · refine ⟨12 * (m + 1) ^ 2 - 2 * (m + 1), ?_⟩
    have h1 : 24 * (m + 1) ^ 2 - 4 * (m + 1) = 24 * m ^ 2 + 44 * m + 20 := by
      apply Nat.sub_eq_of_eq_add
      ring
    have h2 : 12 * (m + 1) ^ 2 - 2 * (m + 1) = 12 * m ^ 2 + 22 * m + 10 := by
      apply Nat.sub_eq_of_eq_add
      ring
    rw [h1, h2]
    ring

theorem v13_stage_q_powers_combine (q n : ℕ) :
    (-(q : ℂ)) ^ (Nat.choose (4 * n) 2) *
        (-1 : ℂ) ^ (Nat.choose (4 * n) 2) *
        (-(q : ℂ)) ^ (∑ k : Fin (4 * n), (2 * n + (k : ℕ))) =
      vContourQScale q n := by
  rw [(choose_four_mul_two_even n).neg_one_pow, mul_one, ← pow_add,
    v13_qscale_exponent_eq n, (v13_qscale_exponent_even n).neg_pow]
  rfl

/-! ## 2. Vandermonde inversion under `x ↦ q / x` -/

theorem det_projVandermonde_one {m : ℕ} (x : Fin m → ℂ) :
    (Matrix.projVandermonde (fun _ : Fin m => (1 : ℂ)) x).det =
      (-1 : ℂ) ^ (Nat.choose m 2) * V.Literal.vContourVandermonde x := by
  rw [Matrix.det_projVandermonde, V.vContourVandermonde_eq_det, Matrix.det_vandermonde]
  simp only [one_mul]
  calc
    (∏ i : Fin m, ∏ j ∈ Finset.Ioi i, (x i - x j)) =
        ∏ i : Fin m, ((-1 : ℂ) ^ (Finset.Ioi i).card *
          (∏ j ∈ Finset.Ioi i, (x j - x i))) := by
      apply Finset.prod_congr rfl
      intro i _
      simpa only [neg_sub] using
        (Finset.prod_neg (s := Finset.Ioi i) (fun j : Fin m => x j - x i))
    _ = (-1 : ℂ) ^ (Nat.choose m 2) *
        (∏ i : Fin m, ∏ j ∈ Finset.Ioi i, (x j - x i)) := by
      rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, sum_fin_card_Ioi_eq_choose_two]

theorem vandermonde_q_div_mul_pow_eq (q : ℂ) {m : ℕ} (x : Fin m → ℂ)
    (hx : ∀ i, x i ≠ 0) :
    (∏ i : Fin m, x i ^ (m - 1)) *
        (Matrix.vandermonde (fun i : Fin m => q / x i)).det =
      (-q) ^ (Nat.choose m 2) * V.Literal.vContourVandermonde x := by
  classical
  let D1 : Matrix (Fin m) (Fin m) ℂ := Matrix.diagonal (fun i : Fin m => x i ^ (m - 1))
  let V1 : Matrix (Fin m) (Fin m) ℂ := Matrix.vandermonde (fun i : Fin m => q / x i)
  let P1 : Matrix (Fin m) (Fin m) ℂ := Matrix.projVandermonde (fun _ : Fin m => (1 : ℂ)) x
  let D2 : Matrix (Fin m) (Fin m) ℂ := Matrix.diagonal (fun k : Fin m => q ^ (k : ℕ))
  have hmat : D1 * V1 = P1 * D2 := by
    ext i k
    simp only [D1, V1, P1, D2, Matrix.mul_apply, Matrix.diagonal_apply,
      Matrix.vandermonde_apply, Matrix.projVandermonde_apply, one_pow, one_mul]
    rw [Finset.sum_eq_single i, Finset.sum_eq_single k]
    · simp only [if_true]
      have hk := k.isLt
      have hrev : m - 1 = (k : ℕ) + k.rev.val := by
        dsimp only [Fin.rev]
        omega
      rw [hrev, pow_add, div_pow]
      have hxk : x i ^ (k : ℕ) ≠ 0 := pow_ne_zero (k : ℕ) (hx i)
      field_simp [hxk]
    · intro k' _ hne
      simp [hne]
    · simp
    · intro i' _ hne
      have hne' : ¬ i = i' := Ne.symm hne
      simp [hne']
    · simp
  have hdet := congrArg Matrix.det hmat
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal,
    det_projVandermonde_one, Finset.prod_pow_eq_pow_sum, sum_fin_val_eq_choose_two] at hdet
  calc
    (∏ i : Fin m, x i ^ (m - 1)) * (Matrix.vandermonde (fun i : Fin m => q / x i)).det =
        ((-1 : ℂ) ^ (Nat.choose m 2) * V.Literal.vContourVandermonde x) *
          q ^ (Nat.choose m 2) := hdet
    _ = ((-1 : ℂ) ^ (Nat.choose m 2) * q ^ (Nat.choose m 2)) *
          V.Literal.vContourVandermonde x := by ring
    _ = (-q) ^ (Nat.choose m 2) * V.Literal.vContourVandermonde x := by
      rw [← mul_pow, neg_one_mul]

/-! ## 3. Reindexing and exponent helpers for `literalXStageM2` -/

private theorem prod_cast_fin {a b : ℕ} (h : a = b) (f : Fin b → ℂ) :
    (∏ i : Fin a, f (Equiv.cast (congrArg Fin h) i)) = ∏ i : Fin b, f i := by
  subst h
  rfl

private theorem vandermonde_det_cast {a b : ℕ} (h : a = b) (v : Fin b → ℂ) :
    (Matrix.vandermonde (fun i : Fin a => v (Equiv.cast (congrArg Fin h) i))).det =
      (Matrix.vandermonde v).det := by
  subst h
  rfl

private theorem literalXKernelRowScale_prod {m h : ℕ} (x : Fin m → ℂ) :
    (∏ r : Fin (m + h), V.literalXKernelRowScale x r) =
      ∏ i : Fin m, (x i)⁻¹ := by
  classical
  calc
    (∏ r : Fin (m + h), V.literalXKernelRowScale x r) =
        ∏ s : Fin m ⊕ Fin h, (match s with
          | Sum.inl i => (x i)⁻¹
          | Sum.inr _ => 1) := by
      apply Fintype.prod_equiv (finSumFinEquiv (m := m) (n := h)).symm
      intro r
      rfl
    _ = ∏ i : Fin m, (x i)⁻¹ := by simp

private theorem inv_prod_mul_pow_five_n (n : ℕ) (xC : Fin (4 * n) → ℂ)
    (hx : ∀ i, xC i ≠ 0) :
    (∏ i : Fin (4 * n), (xC i)⁻¹) * (∏ i : Fin (4 * n), xC i ^ (4 * n + n)) =
      (∏ i : Fin (4 * n), xC i ^ (4 * n - 1)) * (∏ i : Fin (4 * n), xC i ^ n) := by
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  have hi := i.isLt
  have hexp : 4 * n + n = 1 + ((4 * n - 1) + n) := by omega
  rw [hexp, pow_add, pow_one, pow_add]
  have hxi : xC i ≠ 0 := hx i
  field_simp [hxi]

private theorem pow_two_n_mul_pow_n (n : ℕ) (xC : Fin (4 * n) → ℂ) :
    (∏ i : Fin (4 * n), xC i ^ (2 * n)) * (∏ i : Fin (4 * n), xC i ^ n) =
      ∏ i : Fin (4 * n), xC i ^ (3 * n) := by
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [← pow_add, show 2 * n + n = 3 * n by omega]

theorem rowRepl_literalXStageM2_det_eq_literalXKernelMatrix_det
    (q n : ℕ) (x : Fin (4 * n) → ℝ) (v : Fin (5 * n) → ℝ)
    (hv : ∀ b, v b ∈ Set.Icc (0 : ℝ) 1) :
    let h5 : 4 * n + n = 5 * n := by omega
    let eCast : Fin (4 * n + n) ≃ Fin (5 * n) := Equiv.cast (congrArg Fin h5)
    (P0.Env.rowRepl (V.literalXStageM2 q n v)
        (fun i => V.literalXStageB2 q n v (x i))).det =
      (V.literalXKernelMatrix (q : ℂ) (fun i => (x i : ℂ))
        (fun b => (v (eCast b) : ℂ))).det := by
  classical
  intro h5 eCast
  let e0 : Fin (4 * n) ⊕ Fin n ≃ Fin (4 * n + n) := finSumFinEquiv (m := 4 * n) (n := n)
  have hcol : ∀ c : Fin (4 * n) ⊕ Fin n,
      V.literalXColumnEquiv n c = eCast (e0 c) := fun _ => rfl
  have hreindex :
      Matrix.reindex e0 e0
        (P0.Env.rowRepl (V.literalXStageM2 q n v)
          (fun i => V.literalXStageB2 q n v (x i))) =
        V.literalXKernelMatrix (q : ℂ) (fun i => (x i : ℂ))
          (fun b => (v (eCast b) : ℂ)) := by
    ext r c
    simp only [Matrix.reindex_apply, V.literalXKernelMatrix, Matrix.of_apply]
    rcases hs : e0.symm r with i | k
    · have hvb : v (V.literalXColumnEquiv n (e0.symm c)) ∈ Set.Icc (0 : ℝ) 1 :=
        hv (V.literalXColumnEquiv n (e0.symm c))
      have hvc : V.literalXColumnEquiv n (e0.symm c) = eCast c := by
        rw [hcol, e0.apply_symm_apply]
      have hvb' : v (eCast c) ∈ Set.Icc (0 : ℝ) 1 := by
        simpa [hvc] using hvb
      simp [hs, P0.Env.rowRepl, V.literalXStageB2, V.literalXKernel, hvc,
        hvb'.1, hvb'.2]
    · have hvc : V.literalXColumnEquiv n (e0.symm c) = eCast c := by
        rw [hcol, e0.apply_symm_apply]
      simp [hs, P0.Env.rowRepl, V.literalXStageM2, V.literalXStageA0,
        Matrix.reindex_apply, Equiv.symm_apply_apply, hvc]
  rw [← Matrix.det_reindex_self e0
    (P0.Env.rowRepl (V.literalXStageM2 q n v) (fun i => V.literalXStageB2 q n v (x i))),
    hreindex]

/-! ## 4. Stage-2 Andreief product evaluation on the unit cubes -/

theorem v13Literal_stage2_denominator_ne_zero (q n : ℕ) (hq : 2 ≤ q)
    (x : Fin (4 * n) → ℝ) (v : Fin (5 * n) → ℝ)
    (hx : ∀ i, x i ∈ Set.Icc (0 : ℝ) 1)
    (hv : ∀ b, v b ∈ Set.Icc (0 : ℝ) 1) :
    (∏ i : Fin (4 * n), ∏ b : Fin (5 * n),
      ((q : ℂ) + (x i : ℂ) * (v b : ℂ))) ≠ 0 := by
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  refine Finset.prod_ne_zero_iff.mpr (fun i _ => Finset.prod_ne_zero_iff.mpr (fun b _ => ?_))
  have hpos : (0 : ℝ) < (q : ℝ) + x i * v b := by
    have hmul : 0 ≤ x i * v b := mul_nonneg (hx i).1 (hv b).1
    linarith
  have heq : (q : ℂ) + (x i : ℂ) * (v b : ℂ) = (((q : ℝ) + x i * v b : ℝ) : ℂ) := by
    push_cast
    ring
  rw [heq, Complex.ofReal_ne_zero]
  exact ne_of_gt hpos

/-- Cleared-denominator Stage-2 Andreief determinant evaluation on the unit cubes. -/
theorem v13Literal_stage2_andreiefProduct_mul_den_eq (q n : ℕ) (hq : 2 ≤ q)
    (x : Fin (4 * n) → ℝ) (v : Fin (5 * n) → ℝ)
    (hx : ∀ i, x i ∈ Set.Icc (0 : ℝ) 1)
    (hv : ∀ b, v b ∈ Set.Icc (0 : ℝ) 1) :
    let xC : Fin (4 * n) → ℂ := fun i => (x i : ℂ)
    let vC : Fin (5 * n) → ℂ := fun b => (v b : ℂ)
    V.andreiefProduct (V.literalXStageM2 q n v)
        (V.literalXStageA2 n) (V.literalXStageB2 q n v) x *
      (∏ i : Fin (4 * n), ∏ b : Fin (5 * n), ((q : ℂ) + xC i * vC b)) =
      (-(q : ℂ)) ^ (Nat.choose (4 * n) 2) *
        (V.Literal.vContourVandermonde xC) ^ 2 *
        V.Literal.vContourVandermonde vC *
        (∏ i : Fin (4 * n), xC i ^ (3 * n)) := by
  classical
  intro xC vC
  by_cases hzero : ∃ i : Fin (4 * n), x i = 0
  · rcases hzero with ⟨i, hi0⟩
    have hL : V.andreiefProduct (V.literalXStageM2 q n v)
        (V.literalXStageA2 n) (V.literalXStageB2 q n v) x = 0 :=
      zero_literal_andreiefProduct_zero (V.literalXStageM2 q n v)
        (V.literalXStageB2 q n v) x i hi0
    have hR : (∏ j : Fin (4 * n), xC j ^ (3 * n)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      have hj := i.isLt
      have hpow : 3 * n ≠ 0 := by omega
      dsimp [xC]
      rw [hi0, Complex.ofReal_zero, zero_pow hpow]
    rw [hL, zero_mul, hR, mul_zero]
  · push_neg at hzero
    by_cases hinj : Function.Injective x
    · have h5 : 4 * n + n = 5 * n := by omega
      let eCast : Fin (4 * n + n) ≃ Fin (5 * n) := Equiv.cast (congrArg Fin h5)
      let v' : Fin (4 * n + n) → ℂ := fun b => vC (eCast b)
      have hq_ne : (q : ℂ) ≠ 0 := by
        exact_mod_cast (show q ≠ 0 by omega)
      have hxC_ne : ∀ i : Fin (4 * n), xC i ≠ 0 := fun i =>
        Complex.ofReal_ne_zero.mpr (hzero i)
      have hxC_inj : Function.Injective xC := fun i j hij =>
        hinj (Complex.ofReal_inj.mp hij)
      have hden' : ∀ (i : Fin (4 * n)) (b : Fin (4 * n + n)),
          (q : ℂ) + xC i * v' b ≠ 0 := by
        intro i b
        have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
        have hpos : (0 : ℝ) < (q : ℝ) + x i * v (eCast b) := by
          have hmul : 0 ≤ x i * v (eCast b) := mul_nonneg (hx i).1 (hv (eCast b)).1
          linarith
        have heq : (q : ℂ) + xC i * v' b = (((q : ℝ) + x i * v (eCast b) : ℝ) : ℂ) := by
          dsimp [xC, v', vC]
          push_cast
          ring
        rw [heq, Complex.ofReal_ne_zero]
        exact ne_of_gt hpos
      have hden_cast :
          (∏ i : Fin (4 * n), ∏ b : Fin (4 * n + n), ((q : ℂ) + xC i * v' b)) =
            ∏ i : Fin (4 * n), ∏ b : Fin (5 * n), ((q : ℂ) + xC i * vC b) := by
        apply Finset.prod_congr rfl
        intro i _
        exact prod_cast_fin h5 (fun b => (q : ℂ) + xC i * vC b)
      have hvand_v : (Matrix.vandermonde v').det = V.Literal.vContourVandermonde vC := by
        rw [vandermonde_det_cast h5 vC, V.vContourVandermonde_eq_det]
      have hM2 := rowRepl_literalXStageM2_det_eq_literalXKernelMatrix_det q n x v hv
      have hcv := V.literalXKernelMatrix_det_mul_denominator_eq_vandermonde
        (q : ℂ) xC v' hq_ne hxC_ne hxC_inj hden'
      rw [hden_cast, hvand_v, literalXKernelRowScale_prod] at hcv
      have hA2 : (Matrix.of (fun k l => V.literalXStageA2 n k (x l))).det =
          V.Literal.vContourVandermonde xC * ∏ i : Fin (4 * n), xC i ^ (2 * n) :=
        V.literalXMonomialMatrix_det n x
      have hinv := vandermonde_q_div_mul_pow_eq (q : ℂ) xC hxC_ne
      have hxpow := inv_prod_mul_pow_five_n n xC hxC_ne
      have hx23 := pow_two_n_mul_pow_n n xC
      unfold V.andreiefProduct
      calc
        (Matrix.of fun k l => V.literalXStageA2 n k (x l)).det *
            (P0.Env.rowRepl (V.literalXStageM2 q n v)
              (fun l => V.literalXStageB2 q n v (x l))).det *
            (∏ i : Fin (4 * n), ∏ b : Fin (5 * n), ((q : ℂ) + xC i * vC b)) =
          (V.Literal.vContourVandermonde xC * ∏ i : Fin (4 * n), xC i ^ (2 * n)) *
            ((V.literalXKernelMatrix (q : ℂ) xC v').det *
              (∏ i : Fin (4 * n), ∏ b : Fin (5 * n), ((q : ℂ) + xC i * vC b))) := by
          rw [hA2, hM2]
          ring
        _ = (V.Literal.vContourVandermonde xC * ∏ i : Fin (4 * n), xC i ^ (2 * n)) *
            (((∏ i : Fin (4 * n), (xC i)⁻¹) * (∏ i : Fin (4 * n), xC i ^ (4 * n + n))) *
              V.Literal.vContourVandermonde vC *
              (Matrix.vandermonde (fun i : Fin (4 * n) => (q : ℂ) / xC i)).det) := by
          rw [hcv]
        _ = V.Literal.vContourVandermonde xC *
            V.Literal.vContourVandermonde vC *
            ((∏ i : Fin (4 * n), xC i ^ (4 * n - 1)) *
              (Matrix.vandermonde (fun i : Fin (4 * n) => (q : ℂ) / xC i)).det) *
            ((∏ i : Fin (4 * n), xC i ^ (2 * n)) *
              (∏ i : Fin (4 * n), xC i ^ n)) := by
          rw [hxpow]
          ring
        _ = (-(q : ℂ)) ^ (Nat.choose (4 * n) 2) *
            (V.Literal.vContourVandermonde xC) ^ 2 *
            V.Literal.vContourVandermonde vC *
            (∏ i : Fin (4 * n), xC i ^ (3 * n)) := by
          rw [hinv, hx23]
          ring
    · unfold Function.Injective at hinj
      push_neg at hinj
      rcases hinj with ⟨i, j, hval, hij⟩
      have hL : V.andreiefProduct (V.literalXStageM2 q n v)
          (V.literalXStageA2 n) (V.literalXStageB2 q n v) x = 0 :=
        duplicate_literal_andreiefProduct_zero (V.literalXStageM2 q n v)
          (V.literalXStageB2 q n v) x i j hij hval
      have hR : V.Literal.vContourVandermonde xC = 0 :=
        duplicate_vandermonde_zero x i j hij hval
      rw [hL, zero_mul, hR]
      ring

/-- Divided Stage-2 Andreief determinant evaluation on the unit cubes. -/
theorem v13Literal_stage2_andreiefProduct_eq (q n : ℕ) (hq : 2 ≤ q)
    (x : Fin (4 * n) → ℝ) (v : Fin (5 * n) → ℝ)
    (hx : ∀ i, x i ∈ Set.Icc (0 : ℝ) 1)
    (hv : ∀ b, v b ∈ Set.Icc (0 : ℝ) 1) :
    let xC : Fin (4 * n) → ℂ := fun i => (x i : ℂ)
    let vC : Fin (5 * n) → ℂ := fun b => (v b : ℂ)
    V.andreiefProduct (V.literalXStageM2 q n v)
        (V.literalXStageA2 n) (V.literalXStageB2 q n v) x =
      (-(q : ℂ)) ^ (Nat.choose (4 * n) 2) *
        (V.Literal.vContourVandermonde xC) ^ 2 *
        V.Literal.vContourVandermonde vC *
        (∏ i : Fin (4 * n), xC i ^ (3 * n)) /
        (∏ i : Fin (4 * n), ∏ b : Fin (5 * n), ((q : ℂ) + xC i * vC b)) := by
  intro xC vC
  have hden := v13Literal_stage2_denominator_ne_zero q n hq x v hx hv
  have hmul := v13Literal_stage2_andreiefProduct_mul_den_eq q n hq x v hx hv
  exact (eq_div_iff hden).mpr hmul

/-! ## 5. Combined restricted `hKernel` identity for `v13LiteralAndreiefData_actual` -/

/-- Restricted `hKernel` identity on the unit cubes `x ∈ [0, 1]^(4n)`, `v ∈ [0, 1]^(5n)`
    for `D := V.v13LiteralAndreiefData_actual q n hq`. -/
theorem v13Literal_restricted_hKernel (q n : ℕ) (hq : 2 ≤ q)
    (x : Fin (4 * n) → ℝ) (v : Fin (5 * n) → ℝ)
    (p : Fin (4 * n) → Fin 4 × ℝ)
    (hx : ∀ i, x i ∈ Set.Icc (0 : ℝ) 1)
    (hv : ∀ i, v i ∈ Set.Icc (0 : ℝ) 1) :
    let D := V.v13LiteralAndreiefData_actual q n hq
    (∏ i : Fin (4 * n), V.Literal.vContourWeight q (p i)) *
        V.Literal.vContourPhi q n x v
          (fun i => V.Literal.vContourPoint q (p i).1 (p i).2) =
      (vContourQScale q n)⁻¹ *
        (V.andreiefProduct (D.M2 v) (D.a2 v) (D.b2 v) x *
          V.andreiefProduct (D.M1 v) (D.a1 v) (D.b1 v) p) := by
  intro D
  have h1 := v13Literal_stage1_andreiefProduct_eq q n v p
  have h2 := v13Literal_stage2_andreiefProduct_eq q n hq x v hx hv
  have hqpow : vContourQScale q n ≠ 0 := by
    unfold vContourQScale
    exact pow_ne_zero _ (by exact_mod_cast (show q ≠ 0 by omega))
  have hqcombine := v13_stage_q_powers_combine q n
  change (∏ i : Fin (4 * n), V.Literal.vContourWeight q (p i)) *
      V.Literal.vContourPhi q n x v
        (fun i => V.Literal.vContourPoint q (p i).1 (p i).2) =
    (vContourQScale q n)⁻¹ *
      (V.andreiefProduct (V.literalXStageM2 q n v)
          (V.literalXStageA2 n) (V.literalXStageB2 q n v) x *
        V.andreiefProduct (V.vLiteralContourM1PolynomialRows q n v)
          (V.vLiteralContourA1 q n v) (V.vLiteralContourB1 q n v) p)
  rw [h2, h1]
  unfold V.Literal.vContourPhi
  dsimp only
  calc
    (∏ i : Fin (4 * n), V.Literal.vContourWeight q (p i)) *
        (V.Literal.vContourVandermonde (fun i => (x i : ℂ)) ^ 2 *
          V.Literal.vContourVandermonde (fun i => (v i : ℂ)) ^ 2 *
          V.Literal.vContourVandermonde (fun i => V.Literal.vContourPoint q (p i).1 (p i).2) ^ 2 *
          (∏ i : Fin (4 * n), ∏ b : Fin (5 * n),
            (V.Literal.vContourPoint q (p i).1 (p i).2 - (v b : ℂ))) *
          (∏ i : Fin (4 * n), (x i : ℂ) ^ (3 * n)) *
          (∏ b : Fin (5 * n), (v b : ℂ) ^ n) *
          (∏ i : Fin (4 * n), V.Literal.vContourPoint q (p i).1 (p i).2 ^ (-(5 * n : ℤ))) /
          (∏ i : Fin (4 * n), ∏ b : Fin (5 * n), ((q : ℂ) + (x i : ℂ) * (v b : ℂ)))) =
      (vContourQScale q n)⁻¹ *
        (((-(q : ℂ)) ^ (Nat.choose (4 * n) 2) *
            (-1 : ℂ) ^ (Nat.choose (4 * n) 2) *
            (-(q : ℂ)) ^ (∑ k : Fin (4 * n), (2 * n + (k : ℕ)))) *
          ((∏ i : Fin (4 * n), V.Literal.vContourWeight q (p i)) *
            (V.Literal.vContourVandermonde (fun i => (x i : ℂ)) ^ 2 *
              V.Literal.vContourVandermonde (fun i => (v i : ℂ)) ^ 2 *
              V.Literal.vContourVandermonde (fun i => V.Literal.vContourPoint q (p i).1 (p i).2) ^ 2 *
              (∏ i : Fin (4 * n), ∏ b : Fin (5 * n),
                (V.Literal.vContourPoint q (p i).1 (p i).2 - (v b : ℂ))) *
              (∏ i : Fin (4 * n), (x i : ℂ) ^ (3 * n)) *
              (∏ b : Fin (5 * n), (v b : ℂ) ^ n) *
              (∏ i : Fin (4 * n), V.Literal.vContourPoint q (p i).1 (p i).2 ^ (-(5 * n : ℤ))) /
              (∏ i : Fin (4 * n), ∏ b : Fin (5 * n), ((q : ℂ) + (x i : ℂ) * (v b : ℂ)))))) := by
      rw [hqcombine, inv_mul_cancel_left₀ hqpow]
    _ = _ := by
      ring

/-- Restricted triple-integral-to-S1-Andreief identity for `v13LiteralAndreiefData_actual`
    given only `hSwap`. -/
theorem v13Literal_vContourTripleIntegral_eq_qscale_inv_mul_s1
    (q n : ℕ) (hq : 2 ≤ q)
    (hSwap : Integrable
      (fun y : (Fin (4 * n) → ℝ) × (Fin (5 * n) → ℝ) =>
        V.andreiefProduct ((V.v13LiteralAndreiefData_actual q n hq).M2 y.2)
            ((V.v13LiteralAndreiefData_actual q n hq).a2 y.2)
            ((V.v13LiteralAndreiefData_actual q n hq).b2 y.2) y.1 *
          ∫ p : Fin (4 * n) → Fin 4 × ℝ,
            V.andreiefProduct ((V.v13LiteralAndreiefData_actual q n hq).M1 y.2)
              ((V.v13LiteralAndreiefData_actual q n hq).a1 y.2)
              ((V.v13LiteralAndreiefData_actual q n hq).b1 y.2) p
              ∂(Measure.pi fun _ : Fin (4 * n) => V.Literal.vContourParameterMeasure))
      ((Measure.pi fun _ : Fin (4 * n) => V.Literal.vContourUnitIntervalMeasure).prod
        (Measure.pi fun _ : Fin (5 * n) => V.Literal.vContourUnitIntervalMeasure))) :
    V.Literal.vContourTripleIntegral q n =
      (vContourQScale q n)⁻¹ *
        V.v13S1AndreiefIntegral (V.v13LiteralAndreiefData_actual q n hq) :=
  vContourTripleIntegral_eq_const_mul_canonicalS1Andreief_restrict
    (V.v13LiteralAndreiefData_actual q n hq)
    (vContourQScale q n)⁻¹
    (v13Literal_restricted_hKernel q n hq)
    hSwap

end

end Li2Lean.B3

#print axioms Li2Lean.B3.vandermonde_q_div_mul_pow_eq
#print axioms Li2Lean.B3.v13Literal_stage2_andreiefProduct_mul_den_eq
#print axioms Li2Lean.B3.v13Literal_stage2_andreiefProduct_eq
#print axioms Li2Lean.B3.v13Literal_restricted_hKernel
#print axioms Li2Lean.B3.v13Literal_vContourTripleIntegral_eq_qscale_inv_mul_s1
