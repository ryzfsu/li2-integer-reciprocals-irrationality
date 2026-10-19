/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.PositiveBaseFrequencyTail
import Li2Lean.P0.PositiveBaseFrequencyReplacement
import Li2Lean.P0.FrequencyFiniteCutoff
import Li2Lean.P0.ActualFrequencyTailFactor

open MeasureTheory

namespace Li2Lean.AllNAssembly

noncomputable section

open Li2Lean.P0
open Li2Lean.P0.PositiveBase
open Li2Lean.P0.FrequencyFinite
open Li2Lean.P0.FrequencyLeaf
open Li2Lean.P0.FrequencyCutoff

noncomputable def qContourQFixedFactor {m : ℕ} (q : ℕ) (S : Finset ℕ)
    (hSI : S ⊆ Iset m) (Z : Fin (m - S.card) → ℂ) : ℝ :=
  (∏ a ∈ S, Real.log (q : ℝ) * qUReal q (m / 2) a) *
    (∏ i : Fin (m - S.card), ‖p0EntireQ (q : ℤ) (m / 2) (Z i)‖) *
    ‖contourQLeftMinor S hSI Z‖

noncomputable def qContourQMinorFrequencyProduct {m : ℕ} (q : ℕ)
    (S : Finset ℕ) (h4 : 4 ∣ m) (hSI : S ⊆ Iset m)
    (R : Fin m → ℕ) (hR : StrictMono R)
    (Z : Fin (m - S.card) → ℂ) : ℝ :=
  (∏ i : Fin m, qFrequencyWeightReal q (m / 2) (R i)) *
    ‖(contourQMinors S h4 hSI R hR Z).2.1‖ *
    ‖(contourQMinors S h4 hSI R hR Z).2.2‖

theorem qContourQValue_eq_fixed_mul_minor {m : ℕ} (q : ℕ)
    (S : Finset ℕ) (h4 : 4 ∣ m) (hSI : S ⊆ Iset m)
    (R : Fin m → ℕ) (hR : StrictMono R) (Z : Fin (m - S.card) → ℂ) :
    qContourQValue q S h4 hSI R hR Z =
      qContourQFixedFactor q S hSI Z * qContourQMinorFrequencyProduct q S h4 hSI R hR Z := by
  simp only [qContourQValue, qContourQFixedFactor, qContourQMinorFrequencyProduct,
    contourQMinors, contourQLeftMinor, norm_mul]
  ring

theorem qContourQMinorFrequencyProduct_eq_scale_mul {m : ℕ} (q : ℕ)
    (hq : 0 < q) (S : Finset ℕ) (h4 : 4 ∣ m) (hSI : S ⊆ Iset m)
    (R : Fin m → ℕ) (hR : StrictMono R) (Z : Fin (m - S.card) → ℂ) :
    qContourQMinorFrequencyProduct q S h4 hSI R hR Z =
      qFrequencyScale q ((Finset.univ : Finset (Fin m)).image R) *
        contourQMinorFrequencyProduct S h4 hSI R hR Z := by
  unfold qContourQMinorFrequencyProduct contourQMinorFrequencyProduct
  have hweights :
      (∏ i : Fin m, FrequencyLeaf.weight (m / 2) (R i)) =
        ∏ i : Fin m, frequencyWeightReal (m / 2) (R i) := by
    calc
      _ = ∏ r ∈ (Finset.univ : Finset (Fin m)).image R,
          FrequencyLeaf.weight (m / 2) r :=
        prod_fin_image R hR.injective _
      _ = _ := (frequencyWeights_eq_image R hR).symm
  rw [qFrequencyWeights_eq_scale_mul q (m / 2) R hR hq]
  rw [hweights]
  ring

noncomputable def qContourQFrequencyIndependentFactor {m : ℕ} (q : ℕ)
    (S : Finset ℕ) (h4 : 4 ∣ m) (hSI : S ⊆ Iset m)
    (Z : Fin (m - S.card) → ℂ) : ℝ :=
  qContourQFixedFactor q S hSI Z * contourQMinorFrequencyIndependentFactor S h4 hSI Z

theorem qContourQFixedFactor_nonneg {m : ℕ} (q : ℕ) (hq : 2 ≤ q)
    (S : Finset ℕ) (hSI : S ⊆ Iset m) (Z : Fin (m - S.card) → ℂ) :
    0 ≤ qContourQFixedFactor q S hSI Z := by
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (show 1 ≤ q by omega)
  have hlog : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hqR
  have hpinned : 0 ≤ ∏ a ∈ S, Real.log (q : ℝ) * qUReal q (m / 2) a := by
    apply Finset.prod_nonneg
    intro a ha
    apply mul_nonneg hlog
    unfold qUReal
    positivity
  have hentire : 0 ≤ ∏ i : Fin (m - S.card), ‖p0EntireQ (q : ℤ) (m / 2) (Z i)‖ := by
    apply Finset.prod_nonneg
    intro i hi
    exact norm_nonneg _
  unfold qContourQFixedFactor
  exact mul_nonneg (mul_nonneg hpinned hentire) (norm_nonneg _)

theorem qContourQFrequencyIndependentFactor_nonneg {m : ℕ} (q : ℕ)
    (hq : 2 ≤ q) (S : Finset ℕ) (h4 : 4 ∣ m) (hSI : S ⊆ Iset m)
    (Z : Fin (m - S.card) → ℂ)
    (hZ : ∀ z j, Z z ≠ contourQRightColumns S h4 hSI j) :
    0 ≤ qContourQFrequencyIndependentFactor q S h4 hSI Z := by
  unfold qContourQFrequencyIndependentFactor
  exact mul_nonneg (qContourQFixedFactor_nonneg q hq S hSI Z)
    (contourQMinorFrequencyIndependentFactor_nonneg S h4 hSI Z hZ)

theorem qContourQValue_eq_frequencyFactor {m : ℕ} (q : ℕ)
    (hq : 0 < q) (hm : 0 < m) (h4 : 4 ∣ m) (S : Finset ℕ)
    (hSI : S ⊆ Iset m) (R : Fin m → ℕ) (hR : StrictMono R)
    (hRpos : ∀ i, 0 < R i) (Z : Fin (m - S.card) → ℂ)
    (hZ : ∀ z j, Z z ≠ contourQRightColumns S h4 hSI j) :
    qContourQValue q S h4 hSI R hR Z =
      qContourQFrequencyIndependentFactor q S h4 hSI Z *
        qFrequencyFactor q m (m / 2) S
          ((Finset.univ : Finset (Fin m)).image R) (m - S.card) Z := by
  rw [qContourQValue_eq_fixed_mul_minor,
    qContourQMinorFrequencyProduct_eq_scale_mul q hq S h4 hSI R hR Z,
    contourQMinorFrequencyProduct_eq_fixedFactor_mul_frequencyFactor
      hm h4 S hSI R hR hRpos Z hZ]
  simp [qContourQFrequencyIndependentFactor, qFrequencyFactor]
  ring

noncomputable def qFrequencyZ (q m M : ℕ) (S : Finset ℕ)
    (d : ℕ) (Z : Fin d → ℂ) : ℝ :=
  finiteZ m M (fun R => qFrequencyFactor q m (m / 2) S R d Z)

theorem qFrequencyFactor_nonneg {q m : ℕ} (hq : 2 ≤ q)
    (S R : Finset ℕ) (d : ℕ) (Z : Fin d → ℂ) :
    0 ≤ qFrequencyFactor q m (m / 2) S R d Z := by
  unfold qFrequencyFactor qFrequencyScale
  apply mul_nonneg
  · apply Finset.prod_nonneg
    intro r hr
    apply pow_nonneg
    positivity
  · exact FrequencyFinite.frequencyFactor_nonneg m (m / 2) S R d Z

theorem finiteFrequencyTail_of_family_ratio {m M : ℕ}
    (hm : 0 < m) (hM : 20 * m ≤ M) (f : Finset ℕ → ℝ)
    (hf : ∀ R ∈ finiteFamily (m / 2) m M, 0 ≤ f R)
    (hratio : ∀ R ∈ tailFamily m M,
      f R ≤ ((12500 : ℝ) ^ m * (m : ℝ) ^ 2 /
        (4 * (largest R : ℝ) ^ 2) * weight (m / 2) (largest R)) *
          f (replacement m R)) :
    finiteZ m M f - finiteZ m (20 * m) f ≤
      finiteTailCoefficient m M * finiteZ m M f := by
  have hreplace : ∀ R ∈ tailFamily m M,
      f R ≤ ((12500 : ℝ) ^ m / 1600) * weight (m / 2) (largest R) *
        f (replacement m R) := by
    intro R hR
    exact (hratio R hR).trans
      (mul_le_mul_of_nonneg_right
        (largeFrequency_coefficient_le m (largest R) (tail_largest_gt hR))
        (hf (replacement m R) (replacement_mem hm hM hR)))
  have h := finiteReplacement_bound hm hM f
    (fun r => ((12500 : ℝ) ^ m / 1600) * weight (m / 2) r)
    hf (by intro r hr; unfold weight; positivity) hreplace
  have hcoeff : finiteTailCoefficient m M =
      (m : ℝ) * ∑ r ∈ Finset.Ioc (20 * m) M,
        ((12500 : ℝ) ^ m / 1600) * weight (m / 2) r := by
    unfold finiteTailCoefficient
    rw [Finset.mul_sum]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    ring
  rw [hcoeff]
  exact h

theorem finiteCutoff_of_family_ratio {m M : ℕ}
    (hm : 0 < m) (hM : 20 * m ≤ M) (f : Finset ℕ → ℝ)
    (hf : ∀ R ∈ finiteFamily (m / 2) m M, 0 ≤ f R)
    (hratio : ∀ R ∈ tailFamily m M,
      f R ≤ ((12500 : ℝ) ^ m * (m : ℝ) ^ 2 /
        (4 * (largest R : ℝ) ^ 2) * weight (m / 2) (largest R)) *
          f (replacement m R)) :
    finiteZ m M f ≤
      (1 + (3 / 160 : ℝ) * (1 / 2 : ℝ) ^ m) * finiteZ m (20 * m) f := by
  have htail : 0 ≤ finiteZ m M f - finiteZ m (20 * m) f := by
    rw [finiteZ_sub_eq_tail hM]
    apply Finset.sum_nonneg
    intro R hR
    exact hf R (Finset.mem_sdiff.mp hR).1
  have heq : finiteZ m (20 * m) f +
      (finiteZ m M f - finiteZ m (20 * m) f) = finiteZ m M f := by ring
  have hfull : 0 ≤ finiteZ m M f := by
    unfold finiteZ
    apply Finset.sum_nonneg
    intro R hR
    exact hf R hR
  have hbound : finiteZ m M f - finiteZ m (20 * m) f ≤
      FrequencyTail.replacementTailRatio m *
        (finiteZ m (20 * m) f +
          (finiteZ m M f - finiteZ m (20 * m) f)) := by
    rw [heq]
    exact (finiteFrequencyTail_of_family_ratio hm hM f hf hratio).trans
      (mul_le_mul_of_nonneg_right
        (Li2Lean.P0.FrequencyFinite.finiteTailCoefficient_le_replacementTailRatio
          m M) hfull)
  simpa only [heq] using FrequencyTail.finiteCutoff_absorption htail hbound
theorem qFiniteQSum_eq_factor_mul_qFrequencyZ {q m H : ℕ}
    (hm : 0 < m) (hq : 2 ≤ q) (h4 : 4 ∣ m) (S : Finset ℕ)
    (hSI : S ⊆ Iset m) (u : Fin (m - S.card) → ℝ) :
    qFiniteQSum q m H h4 S hSI (fun i => p0EllipsePoint m (u i)) =
      qContourQFrequencyIndependentFactor q S h4 hSI
          (fun i => p0EllipsePoint m (u i)) *
        qFrequencyZ q m H S (m - S.card)
          (fun i => p0EllipsePoint m (u i)) := by
  classical
  have hZ := p0EllipsePoint_avoids_contourQRightColumns hm h4 S hSI u
  unfold qFiniteQSum
  rw [FrequencyCutoff.sum_cutoffTuples]
  calc
    (∑ r : TruncatedTuple (m / 2) m H,
        qContourQValue q S h4 hSI (forgetCutoff r).val
          (forgetCutoff r).property.1 (fun i => p0EllipsePoint m (u i))) =
        qContourQFrequencyIndependentFactor q S h4 hSI
            (fun i => p0EllipsePoint m (u i)) *
          ∑ r : TruncatedTuple (m / 2) m H,
            qFrequencyFactor q m (m / 2) S
              (FrequencyCutoff.tupleSet (forgetCutoff r)) (m - S.card)
              (fun i => p0EllipsePoint m (u i)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      have hRpos : ∀ i, 0 < (forgetCutoff r).val i := by
        intro i
        exact Nat.zero_lt_of_lt ((forgetCutoff r).property.2 i)
      have hterm := qContourQValue_eq_frequencyFactor q (by omega) hm h4 S hSI
        (forgetCutoff r).val (forgetCutoff r).property.1 hRpos
        (fun i => p0EllipsePoint m (u i)) hZ
      simpa [FrequencyCutoff.tupleSet] using hterm
    _ = qContourQFrequencyIndependentFactor q S h4 hSI
          (fun i => p0EllipsePoint m (u i)) *
        qFrequencyZ q m H S (m - S.card) (fun i => p0EllipsePoint m (u i)) := by
      congr 1
      unfold qFrequencyZ finiteZ finiteFamily
      exact (FrequencyCutoff.sum_powersetCard_eq_sum_truncated
        (m / 2) m H
        (fun R => qFrequencyFactor q m (m / 2) S R
          (m - S.card) (fun i => p0EllipsePoint m (u i)))).symm

/-! The q-tail route has one analytic bridge left: turn the q-frequency
replacement estimate into the pointwise finite-cutoff inequality consumed by
`qEInfinity_le_of_finiteQSum_cutoff`.  The outer theorem below is already
closed and has no free envelope or arbitrary coefficient function. -/

/-- The actual largest-site replacement certificate on a tail configuration.

This is the concrete specialization of
`qFrequencyFactor_replacement_le`; all site, cutoff, admissibility, and
ellipse hypotheses come from the paper's `tailFamily` and the canonical
scaled ellipse. -/
theorem qFrequencyFactor_replacement_for_tail
    {q m H : ℕ} (hq : 2 ≤ q) (hm : 0 < m) (h4 : 4 ∣ m)
    {R : Finset ℕ} (hR : R ∈ tailFamily m H)
    (S : Finset ℕ) (hSI : S ⊆ FrequencyLeaf.I_m m)
    (u : Fin (m - S.card) → ℝ) :
    qFrequencyFactor q m (m / 2) S R (m - S.card)
        (fun z => p0EllipsePoint m (u z)) ≤
      ((12500 : ℝ) ^ m * (m : ℝ) ^ 2 /
        (4 * (largest R : ℝ) ^ 2) * FrequencyLeaf.weight (m / 2) (largest R)) *
        qFrequencyFactor q m (m / 2) S
          (FrequencyLeaf.replace (m / 2) m R (site m R) (largest R))
          (m - S.card) (fun z => p0EllipsePoint m (u z)) := by
  have hfull := (mem_finiteFamily_iff (m / 2) m H R).mp
    (Finset.mem_sdiff.mp hR).1
  have hadm : admissible (m / 2) m R := hfull.1
  have hnonempty : R.Nonempty := tail_nonempty hm hR
  have hrmem : largest R ∈ R := largest_mem R hnonempty
  have hlarge : 20 * m < largest R := tail_largest_gt hR
  have hsite_mem : site m R ∈ window (m / 2) m \ R := site_mem hm hR
  have hs : site m R ∉ R := (Finset.mem_sdiff.mp hsite_mem).2
  have hsite_window : site m R ∈ window (m / 2) m :=
    (Finset.mem_sdiff.mp hsite_mem).1
  have hsite_bounds := (mem_window_iff (m / 2) m (site m R)).mp hsite_window
  have hsite_le : site m R ≤ (m / 2) + m := by
    exact (site_le_three_halves hm hR).trans (by omega)
  have hmax : ∀ v ∈ R, v ≤ largest R :=
    fun v hv => le_largest R v hv
  have hgm : 2 * (m / 2) = m := by omega
  have hZre : ∀ z, -(m : ℝ) / 6 < (p0EllipsePoint m (u z)).re :=
    fun z => p0EllipsePoint_re_lower hm (u z)
  have hZnorm : ∀ z, ‖p0EllipsePoint m (u z)‖ < 5 * (m : ℝ) / 2 :=
    fun z => p0EllipsePoint_norm_upper hm (u z)
  exact qFrequencyFactor_replacement_le q hq hm h4 hgm S R hSI hadm
    hrmem hs hsite_bounds.1 hsite_le hlarge hmax
    (fun z => p0EllipsePoint m (u z)) hZre hZnorm

/-- Pointwise q-frequency cutoff bound at the actual paper factor.

The eventual proof factors each `qContourQValue` into a q-independent contour
factor and `qFrequencyFactor`, then applies
`qFrequencyFactor_replacement_le` followed by the finite-frequency tail
aggregation.  Keeping this as one named bridge makes the remaining analytic
stub explicit and prevents an arbitrary envelope from entering the producer. -/
theorem qFiniteQSum_cutoff_of_frequency_replacement
    (q m H : ℕ) (hm : 0 < m) (hq : 2 ≤ q) (h4 : 4 ∣ m)
    (hH : 20 * m ≤ H) (S : Finset ℕ) (hSI : S ⊆ Iset m)
    (u : Fin (m - S.card) → ℝ) :
    qFiniteQSum q m H h4 S hSI (fun i => p0EllipsePoint m (u i)) ≤
      (1 + (3 / 160 : ℝ) * (1 / 2 : ℝ) ^ m) *
        qFiniteQSum q m (20 * m) h4 S hSI
          (fun i => p0EllipsePoint m (u i)) := by
  have hSI' : S ⊆ FrequencyLeaf.I_m m := by
    rw [← Li2Lean.P0.Iset_eq_frequency_I_m hm h4]
    exact hSI
  have hZavoid := p0EllipsePoint_avoids_contourQRightColumns hm h4 S hSI u
  have hratio : ∀ R ∈ tailFamily m H,
      qFrequencyFactor q m (m / 2) S R (m - S.card)
          (fun z => p0EllipsePoint m (u z)) ≤
        ((12500 : ℝ) ^ m * (m : ℝ) ^ 2 /
          (4 * (largest R : ℝ) ^ 2) * FrequencyLeaf.weight (m / 2) (largest R)) *
          qFrequencyFactor q m (m / 2) S
            (FrequencyLeaf.replace (m / 2) m R (site m R) (largest R))
            (m - S.card) (fun z => p0EllipsePoint m (u z)) := by
    intro R hR
    exact qFrequencyFactor_replacement_for_tail hq hm h4 hR S hSI' u
  have hcut : qFrequencyZ q m H S (m - S.card)
      (fun z => p0EllipsePoint m (u z)) ≤
      (1 + (3 / 160 : ℝ) * (1 / 2 : ℝ) ^ m) *
        qFrequencyZ q m (20 * m) S (m - S.card)
          (fun z => p0EllipsePoint m (u z)) := by
    unfold qFrequencyZ
    exact finiteCutoff_of_family_ratio hm hH
      (fun R => qFrequencyFactor q m (m / 2) S R (m - S.card)
        (fun z => p0EllipsePoint m (u z)))
      (by
        intro R hR
        exact qFrequencyFactor_nonneg hq S R (m - S.card)
          (fun z => p0EllipsePoint m (u z)))
      hratio
  have hfactor_nonneg := qContourQFrequencyIndependentFactor_nonneg
    q hq S h4 hSI (fun i => p0EllipsePoint m (u i)) hZavoid
  calc
    qFiniteQSum q m H h4 S hSI (fun i => p0EllipsePoint m (u i)) =
        qContourQFrequencyIndependentFactor q S h4 hSI
            (fun i => p0EllipsePoint m (u i)) *
          qFrequencyZ q m H S (m - S.card) (fun i => p0EllipsePoint m (u i)) :=
      qFiniteQSum_eq_factor_mul_qFrequencyZ hm hq h4 S hSI u
    _ ≤ qContourQFrequencyIndependentFactor q S h4 hSI
          (fun i => p0EllipsePoint m (u i)) *
        ((1 + (3 / 160 : ℝ) * (1 / 2 : ℝ) ^ m) *
          qFrequencyZ q m (20 * m) S (m - S.card)
            (fun i => p0EllipsePoint m (u i))) :=
      mul_le_mul_of_nonneg_left hcut hfactor_nonneg
    _ = (1 + (3 / 160 : ℝ) * (1 / 2 : ℝ) ^ m) *
        qFiniteQSum q m (20 * m) h4 S hSI
          (fun i => p0EllipsePoint m (u i)) := by
      rw [qFiniteQSum_eq_factor_mul_qFrequencyZ hm hq h4 S hSI u]
      ring

/-- The actual q-envelope tail factor, with no free envelope parameter. -/
theorem qEInfinity_le_tail
    (q : ℕ) (hq2 : 2 ≤ q) (m : ℕ) (hm : 0 < m) (h4 : 4 ∣ m) :
    qEInfinity q m h4 ≤
      FrequencyLimit.actualFrequencyTailFactor m * qE q m (20 * m) h4 := by
  have hcore :=
    Li2Lean.P0.PositiveBase.qEInfinity_le_of_finiteQSum_cutoff
      q m hm hq2 h4
      (fun H hH S hSI u =>
        qFiniteQSum_cutoff_of_frequency_replacement
          q m H hm hq2 h4 hH S hSI u)
  simpa [FrequencyLimit.actualFrequencyTailFactor] using hcore

end

end Li2Lean.AllNAssembly

#print axioms Li2Lean.AllNAssembly.qFiniteQSum_cutoff_of_frequency_replacement
#print axioms Li2Lean.AllNAssembly.qEInfinity_le_tail
