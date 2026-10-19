/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.PositiveBaseCellShift
import Li2Lean.P0.FrequencyLimit

namespace Li2Lean.P0.PositiveBase

noncomputable section

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal
open Li2Lean.P0.FrequencyCutoff Li2Lean.P0.FrequencyRegularity

/-- Changing the base from `2` to `q` scales a frequency weight by `q^{-r}`.
For two sites, the exact ratio differs from the q=2 ratio by `(2/q)^(r-s)`. -/
theorem qFrequencyWeightReal_ratio_eq_two_mul (q g s r : ℕ)
    (hq : 2 ≤ q) (hgs : g < s) (hsr : s ≤ r) :
    qFrequencyWeightReal q g r / qFrequencyWeightReal q g s =
      ((2 : ℝ) / (q : ℝ)) ^ (r - s) *
        (frequencyWeightReal g r / frequencyWeightReal g s) := by
  have hqpos : (q : ℝ) ≠ 0 := by
    exact_mod_cast (show q ≠ 0 by omega)
  have hqpow : (q : ℝ) ^ r = (q : ℝ) ^ s * (q : ℝ) ^ (r - s) := by
    rw [← pow_add]
    congr 1
    omega
  have h2pow : (2 : ℝ) ^ r = (2 : ℝ) ^ s * (2 : ℝ) ^ (r - s) := by
    rw [← pow_add]
    congr 1
    omega
  unfold qFrequencyWeightReal frequencyWeightReal
  rw [hqpow, h2pow]
  field_simp [hqpos]
  have hqpow_cancel :
      (q : ℝ) ^ (r - s) * ((2 : ℝ) / (q : ℝ)) ^ (r - s) =
        (2 : ℝ) ^ (r - s) := by
    rw [← mul_pow]
    field_simp [hqpos]
  rw [← hqpow_cancel]
  ring

/-- For `q ≥ 2`, the ratio of q-frequency weights is no larger than its
q=2 ratio whenever the replacement moves from `s` to a larger site `r`. -/
theorem qFrequencyWeightReal_ratio_le_two (q g s r : ℕ)
    (hq : 2 ≤ q) (hgs : g < s) (hsr : s ≤ r) :
    qFrequencyWeightReal q g r / qFrequencyWeightReal q g s ≤
      frequencyWeightReal g r / frequencyWeightReal g s := by
  rw [qFrequencyWeightReal_ratio_eq_two_mul q g s r hq hgs hsr]
  have hbase : (0 : ℝ) ≤ (2 : ℝ) / (q : ℝ) := by positivity
  have hbase_le : (2 : ℝ) / (q : ℝ) ≤ 1 := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < q)]
    have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    nlinarith
  have hpow : ((2 : ℝ) / (q : ℝ)) ^ (r - s) ≤ 1 :=
    pow_le_one₀ hbase hbase_le
  have hratio_nonneg :
      0 ≤ frequencyWeightReal g r / frequencyWeightReal g s := by
    unfold frequencyWeightReal
    positivity
  calc
    ((2 : ℝ) / (q : ℝ)) ^ (r - s) *
        (frequencyWeightReal g r / frequencyWeightReal g s) ≤
      1 * (frequencyWeightReal g r / frequencyWeightReal g s) :=
        mul_le_mul_of_nonneg_right hpow hratio_nonneg
    _ = frequencyWeightReal g r / frequencyWeightReal g s := by ring

/-! ## The q-pinned finite contour envelope -/

/-- The finite q-specific sum before integration over the contour parameters. -/
def qFiniteQSum (q m H : ℕ) (h4 : 4 ∣ m) (S : Finset ℕ)
    (hSI : S ⊆ Iset m) (Z : Fin (m - S.card) → ℂ) : ℝ :=
  ∑ r ∈ cutoffTuples (m / 2) m H,
    qContourQValue q S h4 hSI r.val r.property.1 Z

/-- The actual q-dependent finite-cutoff contour envelope. -/
def qE (q m H : ℕ) (h4 : 4 ∣ m) : ℝ := by
  classical
  exact ∑ S ∈ (Iset m).powerset,
    if hSI : S ⊆ Iset m then
      (Nat.factorial (m - S.card) : ℝ)⁻¹ *
        ∫ u : Fin (m - S.card) → ℝ,
          ∑ r ∈ cutoffTuples (m / 2) m H, qEnvelopeTerm q m h4 S hSI r u
          ∂(ContourKit.productMeasure contourParameterMeasure)
    else 0

def qFiniteEnvelopeIntegrand (q m H : ℕ) (h4 : 4 ∣ m)
    (S : Finset ℕ) (hSI : S ⊆ Iset m)
    (u : Fin (m - S.card) → ℝ) : ℝ≥0∞ :=
  ∑ r ∈ cutoffTuples (m / 2) m H,
    ENNReal.ofReal (qEnvelopeTerm q m h4 S hSI r u)

def qFiniteContribution (q m H : ℕ) (h4 : 4 ∣ m)
    (S : Finset ℕ) (hSI : S ⊆ Iset m) : ℝ≥0∞ :=
  ENNReal.ofReal ((Nat.factorial (m - S.card) : ℝ)⁻¹) *
    ∫⁻ u : Fin (m - S.card) → ℝ, qFiniteEnvelopeIntegrand q m H h4 S hSI u
      ∂(ContourKit.productMeasure contourParameterMeasure)

def qFiniteEnvelope (q m H : ℕ) (h4 : 4 ∣ m) : ℝ≥0∞ := by
  classical
  exact ∑ S ∈ (Iset m).powerset,
    if hSI : S ⊆ Iset m then qFiniteContribution q m H h4 S hSI else 0

theorem qContourQValue_nonneg (q : ℕ) (hq : 2 ≤ q)
    {m : ℕ} (S : Finset ℕ) (h4 : 4 ∣ m) (hSI : S ⊆ Iset m)
    (R : Fin m → ℕ) (hR : StrictMono R)
    (Z : Fin (m - S.card) → ℂ) :
    0 ≤ qContourQValue q S h4 hSI R hR Z := by
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (by omega : 1 ≤ q)
  have hlog : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hq1
  unfold qContourQValue qUReal qFrequencyWeightReal
  positivity

theorem qEnvelopeTerm_nonneg (q m : ℕ) (hq : 2 ≤ q) (h4 : 4 ∣ m)
    (S : Finset ℕ) (hSI : S ⊆ Iset m)
    (r : IncreasingFrequencyTuple (m / 2) m)
    (u : Fin (m - S.card) → ℝ) :
    0 ≤ qEnvelopeTerm q m h4 S hSI r u := by
  unfold qEnvelopeTerm
  apply mul_nonneg
  · exact qContourQValue_nonneg q hq S h4 hSI r.val r.property.1 _
  · unfold contourArcDensity
    positivity

theorem continuous_p0EntireQ (q : ℤ) (g : ℕ) :
    Continuous (p0EntireQ q g) := by
  unfold p0EntireQ
  fun_prop

private theorem orderedElem_mem_q (R : Finset ℕ) (i : Fin R.card) :
    orderedElem R i ∈ R := (Finset.orderIsoOfFin R rfl i).property

theorem continuous_qEnvelopeTerm (q m : ℕ) (hm : 0 < m) (h4 : 4 ∣ m)
    (S : Finset ℕ) (hSI : S ⊆ Iset m)
    (r : IncreasingFrequencyTuple (m / 2) m) :
    Continuous (qEnvelopeTerm q m h4 S hSI r) := by
  classical
  let d := m - S.card
  let Ic := Iset m \ S
  let Jc := Jset m \ S
  have hScard : S.card ≤ m := by
    rw [← Iset_card m]
    exact Finset.card_le_card hSI
  have hIc : Ic.card = d := by
    rw [Finset.card_sdiff_of_subset hSI, Iset_card]
  have hSJ : S ⊆ Jset m := hSI.trans (Iset_subset_Jset m h4)
  have hJc : Jc.card = d + m := by
    rw [Finset.card_sdiff_of_subset hSJ]
    simp [d, Jset, Finset.card_range]
    omega
  have hpoint (i : Fin d) :
      Continuous (fun u : Fin d → ℝ => p0EllipsePoint m (u i)) :=
    (continuous_ellipsePoint m).comp (continuous_apply i)
  have hleftpole (i : Fin d) :
      orderedElem Ic (Fin.cast hIc.symm i) < 2 * m := by
    have hi := (Finset.mem_sdiff.mp
      (orderedElem_mem_q Ic (Fin.cast hIc.symm i))).1
    exact Finset.mem_range.mp (Iset_subset_Jset m h4 hi)
  have hrightpole (i : Fin (d + m)) :
      orderedElem Jc (Fin.cast hJc.symm i) < 2 * m := by
    exact Finset.mem_range.mp
      (Finset.mem_sdiff.mp
        (orderedElem_mem_q Jc (Fin.cast hJc.symm i))).1
  have hpole (a : ℕ) (ha : a < 2 * m) (u : ℝ) :
      (a : ℂ) - p0EllipsePoint m u ≠ 0 := by
    apply sub_ne_zero.mpr
    apply Ne.symm
    exact ellipsePoint_ne_real m hm u a (by positivity)
      (by exact_mod_cast Nat.le_of_lt ha)
  have hleft : Continuous (fun u : Fin d → ℝ => cauchyDet
      (fun i : Fin d => ((orderedElem Ic (Fin.cast hIc.symm i) : ℕ) : ℂ))
      (fun i => -p0EllipsePoint m (u i))) := by
    apply Continuous.matrix_det
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    apply Continuous.inv₀ (continuous_const.add (hpoint j).neg)
    intro u
    simpa [sub_eq_add_neg] using hpole _ (hleftpole i) (u j)
  have hright : Continuous (fun u : Fin d → ℝ => Matrix.det
      (fun i : Fin (d + m) => fun j : Fin (d + m) =>
        ((if hi : i.val < d then -p0EllipsePoint m (u ⟨i.val, hi⟩) else
            (r.val ⟨i.val - d, by omega⟩ : ℂ)) +
          ((orderedElem Jc (Fin.cast hJc.symm j) : ℕ) : ℂ))⁻¹)) := by
    apply Continuous.matrix_det
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    by_cases hi : i.val < d
    · simp only [dite_eq_left hi]
      apply Continuous.inv₀ ((hpoint ⟨i.val, hi⟩).neg.add continuous_const)
      intro u
      simpa [sub_eq_add_neg, add_comm] using
        hpole _ (hrightpole j) (u ⟨i.val, hi⟩)
    · simp only [dite_eq_right hi]
      exact continuous_const
  have hminors : Continuous (fun u : Fin d → ℝ =>
      contourQMinors S h4 hSI r.val r.property.1
        (fun i => p0EllipsePoint m (u i))) := by
    exact hleft.prodMk (continuous_const.prodMk hright)
  have hFG : Continuous (fun u : Fin d → ℝ =>
      ∏ i : Fin d, ‖p0EntireQ (q : ℤ) (m / 2)
          (p0EllipsePoint m (u i))‖) :=
    continuous_finsetProd _ (fun i _ =>
      ((continuous_p0EntireQ (q : ℤ) (m / 2)).comp (hpoint i)).norm)
  have hdensity : Continuous (fun u : Fin d → ℝ =>
      ∏ i : Fin d, contourArcDensity m (u i)) := by
    apply continuous_finsetProd
    intro i _
    exact ((continuous_ellipseTangent m).comp (continuous_apply i)).norm.div_const _
  unfold qEnvelopeTerm qContourQValue
  dsimp only
  exact (((continuous_const.mul continuous_const).mul hFG).mul
    ((hminors.fst.mul hminors.snd.fst).mul hminors.snd.snd).norm).mul hdensity

theorem qIntegrableFiniteEnvelope (q m H : ℕ) (hm : 0 < m)
    (h4 : 4 ∣ m) (S : Finset ℕ) (hSI : S ⊆ Iset m) :
    Integrable
      (fun u : Fin (m - S.card) → ℝ =>
        ∑ r ∈ cutoffTuples (m / 2) m H, qEnvelopeTerm q m h4 S hSI r u)
      (ContourKit.productMeasure contourParameterMeasure) := by
  apply integrable_parameter
  exact continuous_finsetSum _ (fun r _ => continuous_qEnvelopeTerm q m hm h4 S hSI r)

theorem qFiniteContribution_eq_ofReal (q m H : ℕ) (hm : 0 < m)
    (hq : 2 ≤ q) (h4 : 4 ∣ m) (S : Finset ℕ) (hSI : S ⊆ Iset m) :
    qFiniteContribution q m H h4 S hSI =
      ENNReal.ofReal ((Nat.factorial (m - S.card) : ℝ)⁻¹ *
        ∫ u : Fin (m - S.card) → ℝ,
          ∑ r ∈ cutoffTuples (m / 2) m H, qEnvelopeTerm q m h4 S hSI r u
          ∂(ContourKit.productMeasure contourParameterMeasure)) := by
  classical
  rw [ENNReal.ofReal_mul (by positivity)]
  unfold qFiniteContribution qFiniteEnvelopeIntegrand
  congr 1
  rw [ofReal_integral_eq_lintegral_ofReal
    (qIntegrableFiniteEnvelope q m H hm h4 S hSI)
    (Filter.Eventually.of_forall (fun u =>
      Finset.sum_nonneg (fun r _ => qEnvelopeTerm_nonneg q m hq h4 S hSI r u)))]
  apply lintegral_congr
  intro u
  exact (ENNReal.ofReal_sum_of_nonneg
    (fun r _ => qEnvelopeTerm_nonneg q m hq h4 S hSI r u)).symm

theorem qFiniteEnvelope_eq_ofReal (q m H : ℕ) (hm : 0 < m)
    (hq : 2 ≤ q) (h4 : 4 ∣ m) :
    qFiniteEnvelope q m H h4 = ENNReal.ofReal (qE q m H h4) := by
  classical
  unfold qFiniteEnvelope qE
  rw [ENNReal.ofReal_sum_of_nonneg]
  · apply Finset.sum_congr rfl
    intro S hS
    have hSI : S ⊆ Iset m := Finset.mem_powerset.mp hS
    simp only [dite_eq_left hSI]
    exact qFiniteContribution_eq_ofReal q m H hm hq h4 S hSI
  · intro S hS
    have hSI : S ⊆ Iset m := Finset.mem_powerset.mp hS
    simp only [dite_eq_left hSI]
    apply mul_nonneg (by positivity)
    apply integral_nonneg
    intro u
    exact Finset.sum_nonneg (fun r _ => qEnvelopeTerm_nonneg q m hq h4 S hSI r u)

theorem qFullContribution_eq_iSup_qFiniteContribution (q m : ℕ)
    (hm : 0 < m) (h4 : 4 ∣ m) (S : Finset ℕ) (hSI : S ⊆ Iset m) :
    qFullContribution q m h4 S hSI =
      ⨆ H, qFiniteContribution q m H h4 S hSI := by
  unfold qFullContribution qFiniteContribution qFiniteEnvelopeIntegrand
  erw [lintegral_tsum_eq_iSup_cutoff _ (m / 2) m
    (fun r u => ENNReal.ofReal (qEnvelopeTerm q m h4 S hSI r u))
    (fun r => (continuous_qEnvelopeTerm q m hm h4 S hSI r).measurable.ennreal_ofReal)]
  exact ENNReal.mul_iSup _ _

theorem qFiniteContribution_mono (q m : ℕ) (h4 : 4 ∣ m)
    (S : Finset ℕ) (hSI : S ⊆ Iset m) :
    Monotone (fun H => qFiniteContribution q m H h4 S hSI) := by
  intro H K hHK
  unfold qFiniteContribution qFiniteEnvelopeIntegrand
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply lintegral_mono
  intro u
  exact Finset.sum_le_sum_of_subset (cutoffTuples_mono (m / 2) m hHK)

theorem qFiniteEnvelope_mono (q m : ℕ) (h4 : 4 ∣ m) :
    Monotone (fun H => qFiniteEnvelope q m H h4) := by
  classical
  intro H K hHK
  unfold qFiniteEnvelope
  apply Finset.sum_le_sum
  intro S hS
  have hSI : S ⊆ Iset m := Finset.mem_powerset.mp hS
  simp only [dite_eq_left hSI]
  exact qFiniteContribution_mono q m h4 S hSI hHK

theorem qFullEnvelope_eq_iSup_qFiniteEnvelope (q m : ℕ)
    (hm : 0 < m) (h4 : 4 ∣ m) :
    qFullEnvelope q m h4 = ⨆ H, qFiniteEnvelope q m H h4 := by
  classical
  unfold qFullEnvelope qFiniteEnvelope
  rw [← sum_iSup_of_monotone (Iset m).powerset
    (fun S H => if hSI : S ⊆ Iset m then qFiniteContribution q m H h4 S hSI else 0)]
  · apply Finset.sum_congr rfl
    intro S hS
    have hSI : S ⊆ Iset m := Finset.mem_powerset.mp hS
    simp only [dite_eq_left hSI]
    exact qFullContribution_eq_iSup_qFiniteContribution q m hm h4 S hSI
  · intro S hS
    have hSI : S ⊆ Iset m := Finset.mem_powerset.mp hS
    simpa only [dite_eq_left hSI] using
      qFiniteContribution_mono q m h4 S hSI

theorem qFullEnvelope_eq_iSup_ofReal_qE (q m : ℕ)
    (hm : 0 < m) (hq : 2 ≤ q) (h4 : 4 ∣ m) :
    qFullEnvelope q m h4 = ⨆ H, ENNReal.ofReal (qE q m H h4) := by
  rw [qFullEnvelope_eq_iSup_qFiniteEnvelope q m hm h4]
  apply iSup_congr
  intro H
  exact qFiniteEnvelope_eq_ofReal q m H hm hq h4

theorem qFullEnvelope_le_of_finiteCutoff (q m : ℕ)
    (hm : 0 < m) (hq : 2 ≤ q) (h4 : 4 ∣ m) (C : ℝ)
    (hfinite : ∀ H : ℕ, 20 * m ≤ H →
      qE q m H h4 ≤ C * qE q m (20 * m) h4) :
    qFullEnvelope q m h4 ≤ ENNReal.ofReal (C * qE q m (20 * m) h4) := by
  rw [qFullEnvelope_eq_iSup_qFiniteEnvelope q m hm h4]
  apply iSup_le
  intro H
  calc
    qFiniteEnvelope q m H h4 ≤ qFiniteEnvelope q m (max H (20 * m)) h4 :=
      qFiniteEnvelope_mono q m h4 (le_max_left _ _)
    _ = ENNReal.ofReal (qE q m (max H (20 * m)) h4) :=
      qFiniteEnvelope_eq_ofReal q m (max H (20 * m)) hm hq h4
    _ ≤ ENNReal.ofReal (C * qE q m (20 * m) h4) :=
      ENNReal.ofReal_le_ofReal (hfinite _ (le_max_right _ _))

theorem qE_nonneg (q m H : ℕ) (hq : 2 ≤ q) (h4 : 4 ∣ m) :
    0 ≤ qE q m H h4 := by
  classical
  unfold qE
  apply Finset.sum_nonneg
  intro S hS
  have hSI : S ⊆ Iset m := Finset.mem_powerset.mp hS
  simp only [dite_eq_left hSI]
  apply mul_nonneg (by positivity)
  apply integral_nonneg
  intro u
  exact Finset.sum_nonneg (fun r _ => qEnvelopeTerm_nonneg q m hq h4 S hSI r u)

/-- A pointwise finite-sum comparison passes through the actual q-contour
integrals and pinned-set sum. -/
theorem qE_le_of_finiteQSum_le (q m H K : ℕ) (hm : 0 < m)
    (hq : 2 ≤ q) (h4 : 4 ∣ m) (C : ℝ)
    (hpoint : ∀ (S : Finset ℕ) (hSI : S ⊆ Iset m)
      (u : Fin (m - S.card) → ℝ),
        qFiniteQSum q m H h4 S hSI (fun i => p0EllipsePoint m (u i)) ≤
          C * qFiniteQSum q m K h4 S hSI (fun i => p0EllipsePoint m (u i))) :
    qE q m H h4 ≤ C * qE q m K h4 := by
  classical
  unfold qE
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro S hS
  have hSI : S ⊆ Iset m := Finset.mem_powerset.mp hS
  simp only [dite_eq_left hSI]
  let fH := fun u : Fin (m - S.card) → ℝ =>
    ∑ r ∈ cutoffTuples (m / 2) m H, qEnvelopeTerm q m h4 S hSI r u
  let fK := fun u : Fin (m - S.card) → ℝ =>
    ∑ r ∈ cutoffTuples (m / 2) m K, qEnvelopeTerm q m h4 S hSI r u
  have hpoint' : ∀ u, fH u ≤ C * fK u := by
    intro u
    have hden : 0 ≤ ∏ i : Fin (m - S.card), contourArcDensity m (u i) := by
      unfold contourArcDensity
      positivity
    have hsumH : fH u =
        qFiniteQSum q m H h4 S hSI (fun i => p0EllipsePoint m (u i)) *
          ∏ i : Fin (m - S.card), contourArcDensity m (u i) := by
      simp [fH, qFiniteQSum, qEnvelopeTerm, ← Finset.sum_mul]
    have hsumK : fK u =
        qFiniteQSum q m K h4 S hSI (fun i => p0EllipsePoint m (u i)) *
          ∏ i : Fin (m - S.card), contourArcDensity m (u i) := by
      simp [fK, qFiniteQSum, qEnvelopeTerm, ← Finset.sum_mul]
    rw [hsumH, hsumK]
    exact (mul_le_mul_of_nonneg_right (hpoint S hSI u) hden).trans_eq (by ring)
  have hI :
      (∫ u, fH u ∂(ContourKit.productMeasure contourParameterMeasure)) ≤
      C * ∫ u, fK u ∂(ContourKit.productMeasure contourParameterMeasure) := by
    rw [← integral_const_mul]
    exact integral_mono
      (qIntegrableFiniteEnvelope q m H hm h4 S hSI)
      ((qIntegrableFiniteEnvelope q m K hm h4 S hSI).const_mul C) hpoint'
  calc
    _ ≤ (Nat.factorial (m - S.card) : ℝ)⁻¹ *
        (C * ∫ u, fK u ∂(ContourKit.productMeasure contourParameterMeasure)) :=
      mul_le_mul_of_nonneg_left hI (by positivity)
    _ = _ := by ring

/-- The nonnegativity dependency for the finite q-sum.  The eventual proof
must expose the q-dependent contour/pinned factor and the finite frequency
sum before applying monotonicity; this named proposition prevents that step
from being hidden in the tail interface. -/
def qFiniteQSum_factorization_nonneg
    (q m H : ℕ) (h4 : 4 ∣ m) (S : Finset ℕ)
    (hSI : S ⊆ Iset m) (u : Fin (m - S.card) → ℝ) : Prop :=
  ∀ r ∈ cutoffTuples (m / 2) m H,
    0 ≤ qContourQValue q S h4 hSI r.val r.property.1
      (fun i => p0EllipsePoint m (u i))

/-- The exact pointwise premise for the finite-to-infinite tail transfer.  It
is kept separate from the integral passage so the smoothing producer has a
single concrete obligation to discharge for the actual q-envelope. -/
def qEInfinity_le_tail_hpoint (q m : ℕ) (h4 : 4 ∣ m) : Prop :=
  ∀ H : ℕ, 20 * m ≤ H →
    ∀ (S : Finset ℕ) (hSI : S ⊆ Iset m)
      (u : Fin (m - S.card) → ℝ),
      qFiniteQSum_factorization_nonneg q m H h4 S hSI u ∧
        qFiniteQSum q m H h4 S hSI (fun i => p0EllipsePoint m (u i)) ≤
          (1 + (3 / 160 : ℝ) * (1 / 2 : ℝ) ^ m) *
            qFiniteQSum q m (20 * m) h4 S hSI
              (fun i => p0EllipsePoint m (u i))

/-! A uniform finite q-frequency replacement estimate controls the literal
infinite q-envelope, with its finiteness obtained from the same estimate. -/
theorem qEInfinity_le_of_finiteQSum_cutoff
    (q m : ℕ) (hm : 0 < m) (hq : 2 ≤ q) (h4 : 4 ∣ m)
    (hpoint : ∀ H : ℕ, 20 * m ≤ H →
      ∀ (S : Finset ℕ) (hSI : S ⊆ Iset m)
        (u : Fin (m - S.card) → ℝ),
        qFiniteQSum q m H h4 S hSI (fun i => p0EllipsePoint m (u i)) ≤
          (1 + (3 / 160 : ℝ) * (1 / 2 : ℝ) ^ m) *
            qFiniteQSum q m (20 * m) h4 S hSI
              (fun i => p0EllipsePoint m (u i))) :
    qEInfinity q m h4 ≤
      (1 + (3 / 160 : ℝ) * (1 / 2 : ℝ) ^ m) * qE q m (20 * m) h4 := by
  have hfinite : ∀ H : ℕ, 20 * m ≤ H →
      qE q m H h4 ≤
        (1 + (3 / 160 : ℝ) * (1 / 2 : ℝ) ^ m) * qE q m (20 * m) h4 := by
    intro H hH
    exact qE_le_of_finiteQSum_le q m H (20 * m) hm hq h4
      (1 + (3 / 160 : ℝ) * (1 / 2 : ℝ) ^ m)
      (fun S hSI u => hpoint H hH S hSI u)
  have hfull := qFullEnvelope_le_of_finiteCutoff q m hm hq h4
    (1 + (3 / 160 : ℝ) * (1 / 2 : ℝ) ^ m) hfinite
  have htarget : 0 ≤
      (1 + (3 / 160 : ℝ) * (1 / 2 : ℝ) ^ m) * qE q m (20 * m) h4 := by
    apply mul_nonneg
    · positivity
    · exact qE_nonneg q m (20 * m) hq h4
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hfull
  simpa only [qEInfinity, ENNReal.toReal_ofReal htarget] using hreal

theorem qEInfinity_le_tail
    (q m : ℕ) (hm : 0 < m) (hq : 2 ≤ q) (h4 : 4 ∣ m)
    (hpoint : qEInfinity_le_tail_hpoint q m h4) :
    qEInfinity q m h4 ≤
      (1 + (3 / 160 : ℝ) * (1 / 2 : ℝ) ^ m) * qE q m (20 * m) h4 := by
  exact qEInfinity_le_of_finiteQSum_cutoff q m hm hq h4
    (fun H hH S hSI u => (hpoint H hH S hSI u).2)

end

end Li2Lean.P0.PositiveBase

#print axioms Li2Lean.P0.PositiveBase.qFrequencyWeightReal_ratio_eq_two_mul
#print axioms Li2Lean.P0.PositiveBase.qFrequencyWeightReal_ratio_le_two
#print axioms Li2Lean.P0.PositiveBase.qEInfinity_le_of_finiteQSum_cutoff
#print axioms Li2Lean.P0.PositiveBase.qEInfinity_le_tail
