/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.EnvPinned
import Li2Lean.P0.EnvContourQ
import Li2Lean.P0.EnvFreqQ
namespace Li2Lean.P0.Env
noncomputable section
open Finset MeasureTheory
open Li2Lean.P0.PositiveBase
/-- q-dependent diagonal source rows. -/
def PpQ (q m : ℕ) (i : Fin m) (c : Fin m ⊕ Fin m) : ℂ :=
  qPinPart (q : ℤ) (m / 2) (rowIndex m i) (colLab m c)

/-- q-dependent contour source rows. -/
def QpQ (q m : ℕ) (i : Fin m) (c : Fin m ⊕ Fin m) : ℂ :=
  qContPart (q : ℤ) (m / 2) (rowIndex m i) (colLab m c)

theorem YmatQ_inr_split (q m : ℕ) (hq : InRange (q : ℤ)) (h4 : 4 ∣ m)
    (R : Fin m → ℕ) (i : Fin m) (c : Fin m ⊕ Fin m) :
    YmatQ q m R (Sum.inr i) c = PpQ q m i c + QpQ q m i c := by
  simp only [YmatQ, Matrix.of_apply, Sum.elim_inr, topRowQ, PpQ, QpQ]
  have hcast : ((p0CQ (q : ℚ) (m / 2) (rowIndex m i) (colLab m c) : ℚ) : ℂ) =
      p0CComplex (q : ℤ) (m / 2) (rowIndex m i) (colLab m c) := by
    unfold p0CQ p0CComplex p0UQ p0UComplex
    split_ifs <;> push_cast <;> ring
  have hsplit := p0C_split_q (q : ℤ) hq (m / 2) (rowIndex m i) (colLab m c)
    (by rw [rowIndex_val]; omega) (by rw [show 4 * (m / 2) = 2 * m by omega]; exact colLab_lt m c)
  have hcast' : ((p0CQ (q : ℚ) (m / 2) (m / 4 + i.val) (colLab m c) : ℚ) : ℂ) =
      p0CComplex (q : ℤ) (m / 2) (rowIndex m i) (colLab m c) := by
    simpa [rowIndex] using hcast
  rw [hcast']
  simpa [qPinPart, qContPart, show 2 * (m / 2) = m by omega, add_comm] using hsplit

def pinnedDQ (q m : ℕ) (S : Finset ℕ) (h4 : 4 ∣ m) (hSI : S ⊆ Iset m)
    (R : Fin m → ℕ) :
    Matrix (Fin (m - S.card) ⊕ Fin m) (Fin (m - S.card) ⊕ Fin m) ℂ :=
  Matrix.of fun a a' => Sum.elim
    (fun l => qContPart (q : ℤ) (m / 2) (aLab m S hSI l) (jLab m S h4 hSI a'))
    (fun k => cauchyKernel (R k) (jLab m S h4 hSI a')) a

theorem norm_det_splitQ_eq (q m : ℕ) (hq : 2 ≤ q) (hm : 0 < m) (h4 : 4 ∣ m)
    (S : Finset ℕ) (hSI : S ⊆ Iset m) (R : Fin m → ℕ) :
    ‖(splitMat (YmatQ q m R) (PpQ q m) (QpQ q m) (tOf m S)).det‖ =
      ‖(pinnedDQ q m S h4 hSI R).det‖ *
        ∏ a ∈ S, (Real.log (q : ℝ) * qUReal q (m / 2) a) := by
  have hrow : ∀ x, pinRowEquiv m hm S hSI x = pinRowFun m hm S hSI x := fun _ => rfl
  have hcol : ∀ x, pinColEquiv m hm S h4 hSI x = pinColFun m hm S h4 hSI x := fun _ => rfl
  have hmemS : ∀ i : Fin m, i ∈ tOf m S ↔ rowIndex m i ∈ S := fun i => by simp [tOf]
  have hjS : ∀ x, jLab m S h4 hSI x ∉ S := fun x => (Finset.mem_sdiff.mp (jLab_mem m S h4 hSI x)).2
  have hcolLab : ∀ x, colLab m (colOf m hm (jLab m S h4 hSI x)) = jLab m S h4 hSI x :=
    fun x => colLab_colOf m hm _ (jLab_lt m S h4 hSI x)
  have hblock := norm_det_of_block (splitMat (YmatQ q m R) (PpQ q m) (QpQ q m) (tOf m S))
    (pinRowEquiv m hm S hSI) (pinColEquiv m hm S h4 hSI)
    (fun b => qPinPart (q : ℤ) (m / 2) (rowIndex m b.val) (rowIndex m b.val))
    (by
      intro b a; rw [hrow, hcol]
      simp only [pinRowFun, pinColFun, splitMat, Matrix.of_apply, Sum.elim_inr, if_pos b.property,
        PpQ, qPinPart, hcolLab]
      rw [if_neg]; intro h; exact hjS a (h ▸ (hmemS b.val).mp b.property))
    (by
      intro b b'; rw [hrow, hcol]
      simp only [pinRowFun, pinColFun, splitMat, Matrix.of_apply, Sum.elim_inr, if_pos b.property,
        PpQ, qPinPart, colLab_colOf m hm _ (rowIndex_lt m h4 b'.val)]
      by_cases hb : b = b'
      · subst hb; simp
      · rw [if_neg, if_neg hb]; intro h; exact hb (Subtype.ext (rowIndex_injective m h)))
  rw [hblock]
  congr 1
  · congr 2; ext a a'; simp only [Matrix.of_apply]; rw [hrow, hcol]
    rcases a with l | k
    · have hnot : posI m hm (aLab m S hSI l) ∉ tOf m S := by
        rw [hmemS, rowIndex_posI m hm _ (Finset.mem_sdiff.mp (aLab_mem m S hSI l)).1]
        exact (Finset.mem_sdiff.mp (aLab_mem m S hSI l)).2
      simp only [pinRowFun, pinColFun, splitMat, Matrix.of_apply, Sum.elim_inr, if_neg hnot,
        QpQ, hcolLab, pinnedDQ, Sum.elim_inl,
        rowIndex_posI m hm _ (Finset.mem_sdiff.mp (aLab_mem m S hSI l)).1]
    · simp only [pinRowFun, pinColFun, splitMat, Matrix.of_apply, Sum.elim_inl, YmatQ,
        freqVecQ, hcolLab, pinnedDQ, Sum.elim_inr]
  · rw [Finset.prod_coe_sort (tOf m S) (fun i => ‖qPinPart (q : ℤ) (m / 2) (rowIndex m i) (rowIndex m i)‖)]
    conv_rhs => rw [← tOf_image m S hSI]
    rw [Finset.prod_image (fun i _ j _ h => rowIndex_injective m h)]
    apply Finset.prod_congr rfl; intro i _
    rw [qPinPart, if_pos rfl, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg (by exact_mod_cast (show 1 ≤ q by omega)))]
    simp [qUReal, qPinPart, p0UComplex, Complex.norm_mul, Complex.norm_natCast]

end
end Li2Lean.P0.Env
