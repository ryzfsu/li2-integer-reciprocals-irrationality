/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.V.VLiteralPolynomialRows
import Li2Lean.V.VLiteralXStage

namespace Li2Lean
namespace V

noncomputable section

open MeasureTheory Set
open scoped BigOperators

/-- The outer moment matrix in the first v13 Andreief stage
(`v-analytic.tex:50-105,125-145`). -/
noncomputable def vLiteralOuterM0 (q n : ℕ) :
    Matrix (Fin (5 * n) ⊕ Fin (4 * n)) (Fin (5 * n) ⊕ Fin (4 * n)) ℂ :=
  fun r c =>
    match r with
    | Sum.inl k =>
        ∫ t : ℝ, literalXStageA0 q n k t * vLiteralOuterB0 n t c
          ∂Literal.vContourUnitIntervalMeasure
    | Sum.inr k =>
        (vCEntry (-(q : ℤ)) (vIIndexNat n k.val)
          (vLiteralOuterColumnIndex n c) : ℂ)

private def clamp01 (x : ℝ) : ℝ := min 1 (max 0 x)

private def outerMomentIntegrand (q n : ℕ) (i : Fin (4 * n)) : ℝ → ℝ → ℂ :=
  fun v x =>
    literalXMonomial n i x *
      ((q : ℂ) + (clamp01 x : ℂ) * (clamp01 v : ℂ))⁻¹

private theorem clamp01_mem (x : ℝ) : clamp01 x ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact le_min (by positivity) (le_max_left _ _)
  · exact min_le_left _ _

private theorem outerMomentIntegrand_continuous (q n : ℕ) (hq : 2 ≤ q)
    (i : Fin (4 * n)) :
    Continuous (Function.uncurry (outerMomentIntegrand q n i)) := by
  have hc : Continuous clamp01 := by
    unfold clamp01
    exact continuous_const.min (continuous_const.max continuous_id)
  have hden : Continuous (fun p : ℝ × ℝ =>
      (q : ℂ) + (clamp01 p.2 : ℂ) * (clamp01 p.1 : ℂ)) := by
    fun_prop
  have hden_ne : ∀ p : ℝ × ℝ,
      (q : ℂ) + (clamp01 p.2 : ℂ) * (clamp01 p.1 : ℂ) ≠ 0 := by
    intro p
    have hqR : (0 : ℝ) < (q : ℝ) := by
      have hq' : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
      linarith
    have hcx : 0 ≤ clamp01 p.2 := (clamp01_mem p.2).1
    have hcv : 0 ≤ clamp01 p.1 := (clamp01_mem p.1).1
    have hpos : (0 : ℝ) < (q : ℝ) + clamp01 p.2 * clamp01 p.1 := by
      nlinarith [mul_nonneg hcx hcv]
    have heq : (q : ℂ) + (clamp01 p.2 : ℂ) * (clamp01 p.1 : ℂ) =
        ((q : ℝ) + clamp01 p.2 * clamp01 p.1 : ℝ) := by
      push_cast
      ring
    rw [heq, Complex.ofReal_ne_zero]
    exact ne_of_gt hpos
  have hmon : Continuous (fun p : ℝ × ℝ => literalXMonomial n i p.2) := by
    fun_prop [literalXMonomial]
  exact hmon.mul (hden.inv₀ hden_ne)

theorem literalXMoment_continuousOn (q n : ℕ) (hq : 2 ≤ q) (i : Fin (4 * n)) :
    ContinuousOn (literalXMoment q n i) (Set.Icc (0 : ℝ) 1) := by
  let hparam : Continuous (fun v : ℝ =>
      ∫ x in (0 : ℝ)..1, outerMomentIntegrand q n i v x) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (outerMomentIntegrand_continuous q n hq i) 0 1
  have heq : Set.EqOn (literalXMoment q n i) (fun v : ℝ =>
      ∫ x in (0 : ℝ)..1, outerMomentIntegrand q n i v x)
      (Set.Icc (0 : ℝ) 1) := by
    intro v hv
    rw [literalXMoment]
    change (∫ x in Set.Icc (0 : ℝ) 1,
      literalXMonomial n i x * literalXKernel q v x) = _
    rw [integral_Icc_eq_integral_Ioc]
    calc
      (∫ x in Set.Ioc (0 : ℝ) 1,
          literalXMonomial n i x * literalXKernel q v x) =
          ∫ x in (0 : ℝ)..1,
            literalXMonomial n i x * literalXKernel q v x :=
        (intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)).symm
      _ = ∫ x in (0 : ℝ)..1, outerMomentIntegrand q n i v x := by
        rw [intervalIntegral.integral_of_le (f := fun x : ℝ =>
          literalXMonomial n i x * literalXKernel q v x)
          (by norm_num : (0 : ℝ) ≤ 1),
          intervalIntegral.integral_of_le (f := fun x : ℝ =>
            outerMomentIntegrand q n i v x)
          (by norm_num : (0 : ℝ) ≤ 1)]
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
        have hx' : x ∈ Set.Icc (0 : ℝ) 1 := ⟨hx.1.le, hx.2⟩
        have hcx : clamp01 x = x := by
          unfold clamp01
          rw [max_eq_right hx'.1, min_eq_right hx'.2]
        have hcv : clamp01 v = v := by
          unfold clamp01
          rw [max_eq_right hv.1, min_eq_right hv.2]
        simp [outerMomentIntegrand, literalXKernel, hx', hv, hcx, hcv]
      _ = (fun v => ∫ x in (0 : ℝ)..1,
          outerMomentIntegrand q n i v x) v := rfl
  exact hparam.continuousOn.congr heq

theorem literalXStageA0_continuousOn (q n : ℕ) (hq : 2 ≤ q) (r : Fin (5 * n)) :
    ContinuousOn (literalXStageA0 q n r) (Set.Icc (0 : ℝ) 1) := by
  unfold literalXStageA0
  rcases h : (literalXColumnEquiv n).symm r with i | k
  · simp only [h]
    exact literalXMoment_continuousOn q n hq i
  · simp only [h]
    exact (Complex.continuous_ofReal.comp_continuousOn continuousOn_id).pow k.val

theorem vLiteralOuter_hint0 (q n : ℕ) (hq : 2 ≤ q)
    (r : Fin (5 * n)) (c : Fin (5 * n) ⊕ Fin (4 * n)) :
    Integrable (fun t : ℝ => literalXStageA0 q n r t * vLiteralOuterB0 n t c)
      Literal.vContourUnitIntervalMeasure := by
  have h_cont : ContinuousOn
      (fun t : ℝ => literalXStageA0 q n r t * vLiteralOuterB0 n t c)
      (Set.Icc (0 : ℝ) 1) := by
    refine (literalXStageA0_continuousOn q n hq r).mul ?_
    unfold vLiteralOuterB0
    exact (Complex.continuous_ofReal.comp_continuousOn continuousOn_id).pow _
  exact (h_cont.integrableOn_Icc).integrable

theorem vLiteralOuter_hmom0 (q n : ℕ)
    (r : Fin (5 * n)) (c : Fin (5 * n) ⊕ Fin (4 * n)) :
    vLiteralOuterM0 q n (Sum.inl r) c =
      ∫ t : ℝ, literalXStageA0 q n r t * vLiteralOuterB0 n t c
        ∂Literal.vContourUnitIntervalMeasure := rfl

end
end V
end Li2Lean

#print axioms Li2Lean.V.literalXMoment_continuousOn
#print axioms Li2Lean.V.literalXStageA0_continuousOn
#print axioms Li2Lean.V.vLiteralOuter_hint0
#print axioms Li2Lean.V.vLiteralOuter_hmom0

namespace Li2Lean
namespace V

/-! Stage 1 of the literal Andreief alignment.  The row exchange is the
even block swap from the `4n` contour rows followed by the `5n` polynomial
rows to the `5n` outer rows followed by the `4n` C rows.  This is the row
ordering in v13 `v-analytic.tex:50-105,125-145`. -/

private def vLiteralM1ColumnEquiv (n : ℕ) :
    Fin (9 * n) ≃ Fin (4 * n) ⊕ Fin (5 * n) := by
  let h : 9 * n = 4 * n + 5 * n := by omega
  exact (Equiv.cast (congrArg Fin h)).trans
    (finSumFinEquiv (m := 4 * n) (n := 5 * n)).symm

private def vLiteralM0ColumnEquiv (n : ℕ) :
    Fin (9 * n) ≃ Fin (5 * n) ⊕ Fin (4 * n) := by
  let h : 9 * n = 5 * n + 4 * n := by omega
  exact (Equiv.cast (congrArg Fin h)).trans
    (finSumFinEquiv (m := 5 * n) (n := 4 * n)).symm

private theorem vLiteralM1ColumnEquiv_apply (n : ℕ) (j : Fin (9 * n)) :
    vLiteralM1ColumnEquiv n j = vLiteralM1ColumnOfFin n j := by
  simp only [vLiteralM1ColumnEquiv, vLiteralM1ColumnOfFin,
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

private theorem vLiteralM0ColumnEquiv_apply (n : ℕ) (j : Fin (9 * n)) :
    vLiteralM0ColumnEquiv n j = vLiteralM0ColumnOfFin n j := by
  simp only [vLiteralM0ColumnEquiv, vLiteralM0ColumnOfFin,
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

def vLiteralRowBlockSwapPerm (n : ℕ) : Equiv.Perm (Fin (9 * n)) :=
  (vLiteralM1ColumnEquiv n).trans
    ((Equiv.sumComm (Fin (4 * n)) (Fin (5 * n))).trans
      (vLiteralM0ColumnEquiv n).symm)

theorem vLiteralRowBlockSwapPerm_sign_eq_one (n : ℕ) :
    Equiv.Perm.sign (vLiteralRowBlockSwapPerm n) = 1 := by
  classical
  by_cases hn0 : n = 0
  · subst n
    have hs : Equiv.sumComm (Fin 0) (Fin 0) = Equiv.refl _ := by
      apply Equiv.ext
      intro x
      exact Sum.elim Fin.elim0 Fin.elim0 x
    simp [vLiteralRowBlockSwapPerm, vLiteralM1ColumnEquiv,
      vLiteralM0ColumnEquiv, hs]
  have hn : 0 < n := Nat.pos_of_ne_zero hn0
  let k : Fin (9 * n) := ⟨5 * n, by omega⟩
  have hperm : vLiteralRowBlockSwapPerm n = finCycle k := by
    apply Equiv.ext
    intro j
    simp only [vLiteralRowBlockSwapPerm, Equiv.trans_apply]
    rw [vLiteralM1ColumnEquiv_apply]
    by_cases hj : j.val < 4 * n
    · simp only [vLiteralM1ColumnOfFin, dif_pos hj]
      have hswap : Equiv.sumComm (Fin (4 * n)) (Fin (5 * n))
          (Sum.inl (⟨j.val, hj⟩ : Fin (4 * n))) =
          Sum.inr (⟨j.val, hj⟩ : Fin (4 * n)) := rfl
      rw [hswap]
      change (vLiteralM0ColumnEquiv n).symm
          (Sum.inr (⟨j.val, by omega⟩ : Fin (4 * n))) = _
      let j' : Fin (9 * n) :=
        ⟨j.val + 5 * n, by omega⟩
      have he0 := vLiteralM0ColumnEquiv_apply n j'
      have he0' : vLiteralM0ColumnEquiv n j' =
          Sum.inr (⟨j.val, by omega⟩ : Fin (4 * n)) := by
        simpa [j', vLiteralM0ColumnOfFin, dif_neg] using he0
      rw [← he0']
      rw [(vLiteralM0ColumnEquiv n).symm_apply_apply]
      apply Fin.ext
      change j'.val = (finCycle k j).val
      change j.val + 5 * n =
        (j + (⟨5 * n, by omega⟩ : Fin (9 * n))).val
      simp only [Fin.add_def]
      rw [Nat.mod_eq_of_lt]
      omega
    · simp only [vLiteralM1ColumnOfFin, dif_neg hj]
      have hswap : Equiv.sumComm (Fin (4 * n)) (Fin (5 * n))
          (Sum.inr (⟨j.val - 4 * n, by omega⟩ : Fin (5 * n))) =
          Sum.inl (⟨j.val - 4 * n, by omega⟩ : Fin (5 * n)) := rfl
      rw [hswap]
      change (vLiteralM0ColumnEquiv n).symm
          (Sum.inl (⟨j.val - 4 * n, by omega⟩ : Fin (5 * n))) = _
      let j' : Fin (9 * n) :=
        ⟨j.val - 4 * n, by omega⟩
      have he0 := vLiteralM0ColumnEquiv_apply n j'
      have hj5 : j.val - 4 * n < 5 * n := by omega
      have he0' : vLiteralM0ColumnEquiv n j' =
          Sum.inl (⟨j.val - 4 * n, by omega⟩ : Fin (5 * n)) := by
        simpa [j', vLiteralM0ColumnOfFin, hj5] using he0
      rw [← he0']
      rw [(vLiteralM0ColumnEquiv n).symm_apply_apply]
      apply Fin.ext
      change j'.val = (finCycle k j).val
      change j.val - 4 * n =
        (j + (⟨5 * n, by omega⟩ : Fin (9 * n))).val
      simp only [Fin.add_def]
      have hjlt := j.isLt
      have hjge : 9 * n ≤ j.val + 5 * n := by omega
      have hsub : j.val + 5 * n - 9 * n = j.val - 4 * n := by
        apply (Nat.sub_eq_iff_eq_add' hjge).2
        have h4 : 4 * n ≤ j.val := by omega
        have hdecomp : j.val - 4 * n + 4 * n = j.val :=
          Nat.sub_add_cancel h4
        omega
      rw [Nat.mod_eq_sub_mod hjge, hsub]
      rw [Nat.mod_eq_of_lt]
      have hn' : 0 < n := hn
      omega
  have hcycle : finCycle k = finRotate (9 * n) ^ k.val := by
    apply Equiv.ext
    intro j
    rw [← Equiv.Perm.iterate_eq_pow]
    exact congrFun (finCycle_eq_finRotate_iterate (k := k)) j
  rw [hperm, hcycle, map_pow, sign_finRotate]
  rw [← pow_mul]
  have h_even : Even ((9 * n - 1) * (5 * n)) := by
    rcases Nat.even_or_odd n with hn_even | hn_odd
    · have h5 : Even (5 * n) := by
        simpa [Nat.mul_comm] using hn_even.mul_left 5
      exact h5.mul_left (9 * n - 1)
    · rcases hn_odd with ⟨m, hm⟩
      have h9 : Even (9 * n - 1) := by
        refine ⟨9 * m + 4, ?_⟩
        omega
      exact h9.mul_right (5 * n)
  exact h_even.neg_one_pow

theorem vLiteralOuter_halign1 (q n : ℕ) (v : Fin (5 * n) → ℝ) :
    (vLiteralContourM1PolynomialRows q n v).det =
      (P0.Env.rowRepl (vLiteralOuterM0 q n)
        (fun l => vLiteralOuterB0 n (v l))).det := by
  let A := Matrix.reindex (vLiteralM1ColumnEquiv n).symm
      (vLiteralM1ColumnEquiv n).symm
      (vLiteralContourM1PolynomialRows q n v)
  let B := Matrix.reindex (vLiteralM0ColumnEquiv n).symm
      (vLiteralM0ColumnEquiv n).symm
      (P0.Env.rowRepl (vLiteralOuterM0 q n)
        (fun l => vLiteralOuterB0 n (v l)))
  have hA : (vLiteralContourM1PolynomialRows q n v).det = A.det :=
    (Matrix.det_reindex_self (vLiteralM1ColumnEquiv n).symm _).symm
  have hB : (P0.Env.rowRepl (vLiteralOuterM0 q n)
      (fun l => vLiteralOuterB0 n (v l))).det = B.det :=
    (Matrix.det_reindex_self (vLiteralM0ColumnEquiv n).symm _).symm
  rw [hA, hB]
  have hAB : A = B.submatrix (vLiteralRowBlockSwapPerm n) id := by
    ext r c
    simp only [A, B, Matrix.reindex_apply, Matrix.submatrix_apply, id_eq,
      vLiteralRowBlockSwapPerm, Equiv.trans_apply, Equiv.symm_symm]
    have hcol : vLiteralContourColumnIndex n
          (vLiteralM1ColumnOfFin n c) =
        vLiteralOuterColumnIndex n (vLiteralM0ColumnOfFin n c) := by
      rw [vLiteralM1ColumnIndexOfFin, vLiteralOuterColumnIndexOfFin]
    rw [vLiteralM1ColumnEquiv_apply n r,
      vLiteralM1ColumnEquiv_apply n c,
      vLiteralM0ColumnEquiv_apply n c]
    rcases h : vLiteralM1ColumnOfFin n r with k | l
    · simp [vLiteralContourM1PolynomialRows, vLiteralContourM1,
        P0.Env.rowRepl, vLiteralOuterM0, vLiteralOuterB0, h, hcol]
    · simp [vLiteralContourM1PolynomialRows, vLiteralContourM1,
        P0.Env.rowRepl, vLiteralOuterM0, vLiteralOuterB0, h, hcol]
  rw [hAB, Matrix.det_permute,
    vLiteralRowBlockSwapPerm_sign_eq_one]
  simp

noncomputable def v13LiteralAndreiefData_actual (q n : ℕ) (hq : 2 ≤ q) :
    V13LiteralAndreiefData q n where
  sigma_v := by
    unfold Literal.vContourUnitIntervalMeasure
    infer_instance
  sigma_z := by
    unfold Literal.vContourParameterMeasure
    infer_instance
  M0 := vLiteralOuterM0 q n
  a0 := literalXStageA0 q n
  b0 := vLiteralOuterB0 n
  M1 := vLiteralContourM1PolynomialRows q n
  a1 := fun v => vLiteralContourA1 q n v
  b1 := vLiteralContourB1 q n
  M2 := literalXStageM2 q n
  a2 := fun _ => literalXStageA2 n
  b2 := literalXStageB2 q n
  hint0 := fun r c => vLiteralOuter_hint0 q n hq r c
  hmom0 := fun r c => vLiteralOuter_hmom0 q n r c
  hint1 := fun v k c => vLiteralContourM1PolynomialRows_hint1 q n hq v k c
  hmom1 := fun v k c => vLiteralContourM1PolynomialRows_hmom1 q n hq v k c
  hint2 := fun v k c => literalXStage_hint2 q n hq v k c
  hmom2 := fun v k c => literalXStage_hmom2 q n v k c
  halign1 := fun v => vLiteralOuter_halign1 q n v
  halign2 := fun v => literalXStage_halign2 q n v

end V
end Li2Lean

#print axioms Li2Lean.V.vLiteralRowBlockSwapPerm_sign_eq_one
#print axioms Li2Lean.V.vLiteralOuter_halign1
#print axioms Li2Lean.V.v13LiteralAndreiefData_actual
