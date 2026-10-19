/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.EnvMatrixQ
import Li2Lean.P0.EnvFreq

open Finset Filter Topology

namespace Li2Lean.P0.Env

noncomputable section

/-! The frequency-side objects with the base `q` made explicit.  The old
    `EnvFreq` definitions remain the q = 2 API; this file is the small
    parametric layer used by the positive-base envelope. -/

/-- q-dependent frequency coefficient `(-1)^(g+1) w_{t,q} K(i_k,t)`. -/
def freqCoefQ (q : ℕ) (m : ℕ) (k : Fin m) (t : ℕ) : ℂ :=
  ((((-1 : ℝ) ^ (m / 2 + 1)) *
      qFrequencyWeightRealQ q (m / 2) t : ℝ) : ℂ) *
    cauchyKernel (m / 4 + k.val) t

/-- q-dependent frequency row vector.  The Cauchy kernel itself is q-free. -/
def freqVecQ (q : ℕ) (m : ℕ) (t : ℕ) (c : Fin m ⊕ Fin m) : ℂ :=
  cauchyKernel t (colLab m c)

/-- q-dependent upper source row. -/
def topRowQ (q : ℕ) (m : ℕ) (i : Fin m) (c : Fin m ⊕ Fin m) : ℂ :=
  ((p0CQ (q : ℚ) (m / 2) (m / 4 + i.val) (colLab m c) : ℚ) : ℂ)

/-- The q-dependent matrix `[K_{R,J}; C_q]`. -/
def YmatQ (q : ℕ) (m : ℕ) (R : Fin m → ℕ) :
    Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℂ :=
  Matrix.of fun r c =>
    Sum.elim (fun l => freqVecQ q m (R l) c) (fun i => topRowQ q m i c) r

/-- The q-dependent coefficient matrix `(a_k(R l))`. -/
def freqAQ (q : ℕ) (m : ℕ) (R : Fin m → ℕ) : Matrix (Fin m) (Fin m) ℂ :=
  Matrix.of fun k l => freqCoefQ q m k (R l)

theorem freqCoefQ_two (m : ℕ) (k : Fin m) (t : ℕ) :
    freqCoefQ 2 m k t = freqCoef m k t := by
  simp [freqCoefQ, freqCoef, qFrequencyWeightRealQ_two]

theorem freqVecQ_two (m : ℕ) (t : ℕ) (c : Fin m ⊕ Fin m) :
    freqVecQ 2 m t c = freqVec m t c := by
  rfl

theorem topRowQ_two (m : ℕ) (i : Fin m) (c : Fin m ⊕ Fin m) :
    topRowQ 2 m i c = topRow m i c := by
  rfl

theorem YmatQ_two (m : ℕ) (R : Fin m → ℕ) :
    YmatQ 2 m R = Ymat m R := by
  ext r c
  rcases r with l | i <;> rfl

theorem freqAQ_two (m : ℕ) (R : Fin m → ℕ) :
    freqAQ 2 m R = freqA m R := by
  ext k l
  exact freqCoefQ_two m k (R l)

/-- The q-parametric analogue of the frequency determinant factorization. -/
theorem norm_det_freqAQ (q : ℕ) (m : ℕ) (R : Fin m → ℕ) :
    ‖(freqAQ q m R).det‖ =
      (∏ l, qFrequencyWeightRealQ q (m / 2) (R l)) *
        ‖cauchyDet (fun i : Fin m => ((rowIndex m i : ℕ) : ℂ))
          (fun j : Fin m => ((R j : ℕ) : ℂ))‖ := by
  have h : freqAQ q m R = Matrix.of fun k l =>
      ((((-1 : ℝ) ^ (m / 2 + 1)) *
          qFrequencyWeightRealQ q (m / 2) (R l) : ℝ) : ℂ) *
        (Matrix.of fun i j => (((rowIndex m i : ℕ) : ℂ) +
            ((R j : ℕ) : ℂ))⁻¹ : Matrix (Fin m) (Fin m) ℂ) k l := by
    ext k l
    simp [freqAQ, freqCoefQ, cauchyKernel, rowIndex]
  rw [h, Matrix.det_mul_row, norm_mul]
  congr 1
  rw [norm_prod]
  apply Finset.prod_congr rfl
  intro l _
  rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_pow, abs_neg,
    abs_one, one_pow, one_mul, abs_of_nonneg]
  unfold qFrequencyWeightRealQ
  positivity

theorem norm_det_freqAQ_two (m : ℕ) (R : Fin m → ℕ) :
    ‖(freqAQ 2 m R).det‖ =
      (∏ l, frequencyWeightReal (m / 2) (R l)) *
        ‖cauchyDet (fun i : Fin m => ((rowIndex m i : ℕ) : ℂ))
          (fun j : Fin m => ((R j : ℕ) : ℂ))‖ := by
  simpa [freqAQ_two] using norm_det_freqA m R

end

end Li2Lean.P0.Env
namespace Li2Lean.P0.Env
noncomputable section

/-- Reindexing the lower rows of the q frequency truncation. -/
theorem truncQ_reindex_inl (q m H : ℕ) (k : Fin m) (c : Fin m ⊕ Fin m) :
    (truncMatrixQ q m H).submatrix (eρ m) (eρ m) (Sum.inl k) c =
      ∑ t ∈ Ioc (m / 2) H, freqCoefQ q m k t * freqVecQ q m t c := by
  have hk : ¬ (eρ m (Sum.inl k)).val < m := by rw [eρ_inl]; omega
  have hlab : lab m (eρ m (Sum.inl k)) = m / 4 + k.val := by
    rw [lab, eρ_inl, if_neg (by omega)]; omega
  simp only [Matrix.submatrix_apply, truncMatrixQ, if_neg hk, hlab]
  have hfilter : (range (H + 1)).filter (fun t => m / 2 < t) = Ioc (m / 2) H := by
    ext t; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc]; omega
  rw [← Finset.sum_filter, hfilter]
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  simp only [freqCoefQ, freqVecQ, cauchyKernel, colLab]
  push_cast
  have h1 : ((m / 4 : ℕ) : ℂ) + (k.val : ℂ) + (t : ℂ) ≠ 0 := by
    have : (0 : ℝ) < ((m / 4 : ℕ) : ℝ) + (k.val : ℝ) + (t : ℝ) := by
      have : 0 < t := by simp at ht; omega
      positivity
    exact_mod_cast this.ne'
  have h2 : (t : ℂ) + (((eρ m c).val : ℕ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < (t : ℝ) + (((eρ m c).val : ℕ) : ℝ) := by
      have : 0 < t := by simp at ht; omega
      positivity
    exact_mod_cast this.ne'
  have h1' : ((m / 4 : ℕ) : ℂ) + (k.val : ℂ) + (t : ℂ) = (((m / 4 + k.val : ℕ) : ℂ) + (t : ℂ)) := by
    push_cast; ring
  rw [show (((eρ m c).val : ℕ) : ℂ) + (t : ℂ) = (t : ℂ) + (((eρ m c).val : ℕ) : ℂ) by ring]
  field_simp [h1, h2]

theorem truncQ_reindex_inr (q m H : ℕ) (i : Fin m) (c : Fin m ⊕ Fin m) :
    (truncMatrixQ q m H).submatrix (eρ m) (eρ m) (Sum.inr i) c = topRowQ q m i c := by
  have hi : (eρ m (Sum.inr i)).val < m := by rw [eρ_inr]; exact i.isLt
  have hlab : lab m (eρ m (Sum.inr i)) = m / 4 + i.val := by
    rw [lab, eρ_inr, if_pos i.isLt]
  simp only [Matrix.submatrix_apply, truncMatrixQ, if_pos hi, hlab, topRowQ, colLab]

theorem rowRepl_truncQ (q m H : ℕ) (R : Fin m → ℕ) :
    rowRepl ((truncMatrixQ q m H).submatrix (eρ m) (eρ m)) (fun l => freqVecQ q m (R l)) =
      YmatQ q m R := by
  ext r c
  rcases r with l | i
  · simp [rowRepl, YmatQ]
  · simp only [rowRepl, YmatQ, Matrix.of_apply, Sum.elim_inr]
    exact truncQ_reindex_inr q m H i c

theorem norm_det_freqAQ_comp (q m : ℕ) (R : Fin m → ℕ) (π : Equiv.Perm (Fin m)) :
    ‖(freqAQ q m (R ∘ π)).det‖ = ‖(freqAQ q m R).det‖ := by
  have h : freqAQ q m (R ∘ π) = (freqAQ q m R).submatrix id π := by
    ext k l; simp [freqAQ]
  rw [h, Matrix.det_permute', norm_mul]
  rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;> simp [h]

theorem norm_det_YmatQ_comp (q m : ℕ) (R : Fin m → ℕ) (π : Equiv.Perm (Fin m)) :
    ‖(YmatQ q m (R ∘ π)).det‖ = ‖(YmatQ q m R).det‖ := by
  have h : YmatQ q m (R ∘ π) =
      (YmatQ q m R).submatrix (Equiv.sumCongr π (Equiv.refl (Fin m))) id := by
    ext r c; rcases r with l | i <;> simp [YmatQ]
  rw [h, Matrix.det_permute, norm_mul]
  rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.sumCongr π (Equiv.refl (Fin m)))) with h | h <;> simp [h]

theorem det_freqAQ_eq_zero_of_not_injective (q m : ℕ) (R : Fin m → ℕ)
    (h : ¬ Function.Injective R) : (freqAQ q m R).det = 0 := by
  obtain ⟨l, l', hR, hne⟩ : ∃ l l', R l = R l' ∧ l ≠ l' := by
    by_contra hc
    apply h
    intro l l' e
    by_contra hne
    exact hc ⟨l, l', e, hne⟩
  exact Matrix.det_zero_of_column_eq hne (fun k => by simp [freqAQ, hR])

/-- q-parametric frequency Cauchy--Binet bound for a truncated determinant. -/
theorem norm_det_truncQ_le (q m H : ℕ) :
    ‖(truncMatrixQ q m H).det‖ ≤
      ∑ r ∈ FrequencyCutoff.cutoffTuples (m / 2) m H,
        (∏ l, qFrequencyWeightRealQ q (m / 2) (r.val l)) *
          ‖cauchyDet (fun i : Fin m => ((rowIndex m i : ℕ) : ℂ))
              (fun j : Fin m => ((r.val j : ℕ) : ℂ))‖ *
          ‖(YmatQ q m r.val).det‖ := by
  classical
  have hdet : ((truncMatrixQ q m H).submatrix (eρ m) (eρ m)).det =
      (truncMatrixQ q m H).det := Matrix.det_submatrix_equiv_self _ _
  have hDA := discrete_andreief (Ioc (m / 2) H)
    ((truncMatrixQ q m H).submatrix (eρ m) (eρ m))
    (freqCoefQ q m) (fun t c => freqVecQ q m t c)
    (truncQ_reindex_inl q m H)
  simp only [rowRepl_truncQ] at hDA
  set X' := (truncMatrixQ q m H).submatrix (eρ m) (eρ m)
  set G : (Fin m → ℕ) → ℝ := fun f => ‖(freqAQ q m f).det‖ * ‖(YmatQ q m f).det‖
  have hcount := sum_piFinset_le_factorial_mul_cutoff (m / 2) H m G
    (fun f => by positivity)
    (fun f π => by simp only [G, norm_det_freqAQ_comp, norm_det_YmatQ_comp])
    (fun f hf => by simp only [G, det_freqAQ_eq_zero_of_not_injective q m f hf, norm_zero, zero_mul])
  have hfac : (0 : ℝ) < (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos m
  have hmain : (m.factorial : ℝ) * ‖X'.det‖ ≤
      (m.factorial : ℝ) * ∑ r ∈ FrequencyCutoff.cutoffTuples (m / 2) m H, G r.val := by
    have h1 : (m.factorial : ℝ) * ‖X'.det‖ = ‖(m.factorial : ℂ) * X'.det‖ := by
      rw [norm_mul, Complex.norm_natCast]
    rw [h1, ← hDA]
    refine (norm_sum_le _ _).trans ?_
    refine le_trans ?_ hcount
    apply Finset.sum_le_sum
    intro f _
    rw [norm_mul]
    rfl
  have hle := le_of_mul_le_mul_left hmain hfac
  rw [hdet] at hle
  refine hle.trans (le_of_eq ?_)
  apply Finset.sum_congr rfl
  intro r _
  show ‖(freqAQ q m r.val).det‖ * ‖(YmatQ q m r.val).det‖ = _
  rw [norm_det_freqAQ]

end
end Li2Lean.P0.Env
