/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.EnvMatrix
import Li2Lean.P0.EnvContourQ
import Li2Lean.P0.EnvBankQ

open Finset Filter Topology

namespace Li2Lean.P0.Env

noncomputable section

/-- Base-q frequency weight for the finite truncation layer.  It is kept
below the positive-base envelope module to avoid an import cycle. -/
noncomputable def qFrequencyWeightRealQ (q g r : ℕ) : ℝ :=
  (Nat.choose (r - 1) g : ℝ) / (q : ℝ) ^ r

theorem qFrequencyWeightRealQ_two (g r : ℕ) :
    qFrequencyWeightRealQ 2 g r = frequencyWeightReal g r := by
  simp [qFrequencyWeightRealQ, frequencyWeightReal]

/-- The complex P0 pencil matrix at the base-q value of `Li₂(1/q)`. -/
def XbetaQ (q : ℤ) (m : ℕ) : Matrix (Fin (2 * m)) (Fin (2 * m)) ℂ := fun r c =>
  if r.val < m then
    ((p0CQ (q : ℚ) (m / 2) (lab m r) c.val : ℚ) : ℂ)
  else
    ((p0BQ (q : ℚ) (m / 2) (lab m r) c.val : ℚ) : ℂ) -
      ((li2InvValue q : ℝ) : ℂ) *
        ((p0AQ (q : ℚ) (m / 2) (lab m r) c.val : ℚ) : ℂ)

/-- The lower block after the base-q unipotent source-row operation. -/
def XinfQ (q : ℤ) (m : ℕ) : Matrix (Fin (2 * m)) (Fin (2 * m)) ℂ := fun r c =>
  if r.val < m then
    ((p0CQ (q : ℚ) (m / 2) (lab m r) c.val : ℚ) : ℂ)
  else
    ((((p0BQ (q : ℚ) (m / 2) (lab m r) c.val : ℚ) : ℝ) -
      li2InvValue q *
        ((p0AQ (q : ℚ) (m / 2) (lab m r) c.val : ℚ) : ℝ) -
      qSourceRowOperationCoefficient q *
        ((p0CQ (q : ℚ) (m / 2) (lab m r) c.val : ℚ) : ℝ) : ℝ) : ℂ)

/-- The q-parametric unipotent operation `row_{m+k} += log(q/(q-1)) row_k`.
The coefficient is the row operation constant; the diagonal pin remains `log q`
inside `p0C_split_q`. -/
def rowOpQ (q : ℤ) (m : ℕ) : Matrix (Fin (2 * m)) (Fin (2 * m)) ℂ := fun r s =>
  (if r = s then 1 else 0) +
    (if m ≤ r.val ∧ s.val = r.val - m then
      ((qSourceRowOperationCoefficient q : ℝ) : ℂ) else 0)

theorem rowOpQ_det (q : ℤ) (m : ℕ) (hm : 0 < m) : (rowOpQ q m).det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · apply Finset.prod_eq_one
    intro r _
    simp only [rowOpQ, if_true]
    rw [if_neg (by omega)]
    ring_nf
  · intro r s hrs
    simp only [OrderDual.toDual_lt_toDual] at hrs
    simp only [rowOpQ]
    rw [if_neg (ne_of_lt hrs), if_neg]
    · ring
    · intro h
      have : s.val < r.val := by omega
      exact absurd hrs (not_lt.mpr (le_of_lt (Fin.lt_def.mpr this)))

theorem XbetaQ_eq_rowOpQ_mul (q : ℤ) (m : ℕ) :
    XbetaQ q m = rowOpQ q m * XinfQ q m := by
  ext r c
  simp only [Matrix.mul_apply, rowOpQ, add_mul, Finset.sum_add_distrib, ite_mul,
    one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  by_cases hr : r.val < m
  · have hz : (∑ x : Fin (2 * m),
        (if m ≤ r.val ∧ x.val = r.val - m then
          ((qSourceRowOperationCoefficient q : ℝ) : ℂ) * XinfQ q m x c else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro x _
      rw [if_neg (by omega)]
    rw [hz, add_zero]
    simp [XbetaQ, XinfQ, hr]
  · let r0 : Fin (2 * m) := ⟨r.val - m, by omega⟩
    have hsum : (∑ x : Fin (2 * m),
        (if m ≤ r.val ∧ x.val = r.val - m then
          ((qSourceRowOperationCoefficient q : ℝ) : ℂ) * XinfQ q m x c else 0)) =
        ((qSourceRowOperationCoefficient q : ℝ) : ℂ) * XinfQ q m r0 c := by
      rw [Finset.sum_eq_single r0]
      · rw [if_pos ⟨by omega, rfl⟩]
      · intro x _ hx
        rw [if_neg]
        intro h
        exact hx (Fin.ext (by simp [r0]; omega))
      · intro h
        exact absurd (Finset.mem_univ r0) h
    rw [hsum]
    have hr0 : r0.val < m := by simp [r0]; omega
    have hlab : lab m r0 = lab m r := by
      simp only [lab, r0, if_pos hr0, if_neg hr]
    simp only [XbetaQ, XinfQ, if_neg hr, if_pos hr0, hlab]
    push_cast
    ring_nf

theorem det_XbetaQ_eq_det_XinfQ (q : ℤ) (m : ℕ) (hm : 0 < m) :
    (XbetaQ q m).det = (XinfQ q m).det := by
  rw [XbetaQ_eq_rowOpQ_mul, Matrix.det_mul, rowOpQ_det q m hm, one_mul]

theorem XbetaQ_two (m : ℕ) : XbetaQ 2 m = Xbeta m := by
  ext r c
  simp [XbetaQ, Xbeta]

theorem XinfQ_two (m : ℕ) : XinfQ 2 m = Xinf m := by
  ext r c
  by_cases hr : r.val < m
  · simp [XinfQ, Xinf, hr]
  · simp [XinfQ, Xinf, hr, qSourceRowOperationCoefficient_two]

theorem rowOpQ_two (m : ℕ) : rowOpQ 2 m = rowOp m := by
  ext r s
  simp [rowOpQ, rowOp, qSourceRowOperationCoefficient_two]

theorem det_XbetaQ_eq_det_XinfQ_two (m : ℕ) (hm : 0 < m) :
    (XbetaQ 2 m).det = (XinfQ 2 m).det := by
  simpa [XbetaQ_two, XinfQ_two] using det_Xbeta_eq_det_Xinf m hm

/-- Frequency-truncated q version of `XinfQ`.  Its entrywise limit is
`XinfQ`; the q source-bank identity is supplied by the bank module. -/
def truncMatrixQ (q : ℕ) (m H : ℕ) :
    Matrix (Fin (2 * m)) (Fin (2 * m)) ℂ := fun r c =>
  if r.val < m then
    ((p0CQ (q : ℚ) (m / 2) (lab m r) c.val : ℚ) : ℂ)
  else
    ((((-1 : ℝ) ^ (m / 2 + 1)) * ∑ t ∈ Finset.range (H + 1),
      (if m / 2 < t then qFrequencyWeightRealQ q (m / 2) t /
        (((lab m r : ℝ) + t) * ((c.val : ℝ) + t)) else 0) : ℝ) : ℂ)

theorem truncMatrixQ_two (m H : ℕ) :
    truncMatrixQ 2 m H = truncMatrix m H := by
  ext r c
  by_cases hr : r.val < m
  · simp [truncMatrixQ, truncMatrix, hr]
  · simp [truncMatrixQ, truncMatrix, hr, qFrequencyWeightRealQ_two]

/-- The q-source-bank identity supplies the entrywise limit of the frequency
truncations, including the unipotent row-operation coefficient. -/
theorem tendsto_truncMatrixQ (q m : ℕ) (hq : 2 ≤ q) :
    Tendsto (fun H => truncMatrixQ q m H) atTop
      (𝓝 (XinfQ (q : ℤ) m)) := by
  refine tendsto_pi_nhds.mpr fun r => tendsto_pi_nhds.mpr fun c => ?_
  by_cases hr : r.val < m
  · simp only [truncMatrixQ, XinfQ, if_pos hr]
    exact tendsto_const_nhds
  · simp only [truncMatrixQ, XinfQ, if_neg hr]
    apply (Complex.continuous_ofReal.tendsto _).comp
    have hb := (bank_hasSum_q q (m / 2) (lab m r) c.val hq).tendsto_sum_nat
    have hb' := (hb.comp (tendsto_add_atTop_nat 1)).const_mul
      ((-1 : ℝ) ^ (m / 2 + 1))
    have hs : ((-1 : ℝ) ^ (m / 2 + 1)) *
        ((-1 : ℝ) ^ (m / 2 + 1)) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]
      norm_num
    rw [← mul_assoc, hs, one_mul] at hb'
    exact hb'

/-! The following generic lift remains useful for alternative entrywise
sources; `tendsto_truncMatrixQ` above discharges it from the actual q bank. -/
theorem tendsto_truncMatrixQ_of_entrywise
    (q : ℕ) (m : ℕ)
    (hentry : ∀ r c,
      Tendsto (fun H => truncMatrixQ q m H r c) atTop
        (𝓝 (XinfQ (q : ℤ) m r c))) :
    Tendsto (fun H => truncMatrixQ q m H) atTop
      (𝓝 (XinfQ (q : ℤ) m)) := by
  refine tendsto_pi_nhds.mpr (fun r => tendsto_pi_nhds.mpr (fun c => ?_))
  exact hentry r c

theorem tendsto_det_truncMatrixQ_of_entrywise
    (q : ℕ) (m : ℕ)
    (hentry : ∀ r c,
      Tendsto (fun H => truncMatrixQ q m H r c) atTop
        (𝓝 (XinfQ (q : ℤ) m r c))) :
    Tendsto (fun H => (truncMatrixQ q m H).det) atTop
      (𝓝 (XinfQ (q : ℤ) m).det) :=
  (continuous_id.matrix_det.tendsto (XinfQ (q : ℤ) m)).comp
    (tendsto_truncMatrixQ_of_entrywise q m hentry)

theorem tendsto_det_truncMatrixQ (q m : ℕ) (hq : 2 ≤ q) :
    Tendsto (fun H => (truncMatrixQ q m H).det) atTop
      (𝓝 (XinfQ (q : ℤ) m).det) :=
  (continuous_id.matrix_det.tendsto (XinfQ (q : ℤ) m)).comp
    (tendsto_truncMatrixQ q m hq)

theorem tendsto_truncMatrixQ_two (m : ℕ) :
    Tendsto (fun H => truncMatrixQ 2 m H) atTop (𝓝 (XinfQ 2 m)) := by
  simpa [truncMatrixQ_two, XinfQ_two] using tendsto_truncMatrix m

end

end Li2Lean.P0.Env
