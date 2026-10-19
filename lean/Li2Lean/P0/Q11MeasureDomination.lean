/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/

import Li2Lean.P0.Q11Reference

open MeasureTheory Set
open scoped ENNReal

namespace Li2Lean.P0.Q11Data

noncomputable section

private lemma smul_interval_le_restrict
    {c : ℝ} {a b : ℝ} {S : Set ℝ}
    (hc1 : c ≤ 1) (hab : Ico a b ⊆ S) :
    ENNReal.ofReal c • (volume.restrict (Ico a b)) ≤
      volume.restrict S := by
  apply Measure.le_iff.2
  intro t ht
  rw [Measure.smul_apply, Measure.restrict_apply ht,
    Measure.restrict_apply ht]
  have hcoef : ENNReal.ofReal c ≤ 1 := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hc1
  calc
    ENNReal.ofReal c • volume (t ∩ Ico a b) ≤
        (1 : ENNReal) • volume (t ∩ Ico a b) := by
      exact smul_le_smul hcoef
        (show volume (t ∩ Ico a b) ≤ volume (t ∩ Ico a b) by rfl)
        (show (0 : ENNReal) ≤ ENNReal.ofReal c by positivity)
        (show (0 : ENNReal) ≤ volume (t ∩ Ico a b) by positivity)
    _ ≤ volume (t ∩ S) := by
      simp only [one_smul]
      exact measure_mono (inter_subset_inter Subset.rfl hab)

private lemma interval_sum_inter_le_restrict
    {left right : ℕ → ℝ} {count : ℕ} {S : Set ℝ}
    (hsep : ∀ i ∈ Finset.range count, ∀ j ∈ Finset.range count,
      i < j → right i ≤ left j)
    (hsubset : ∀ j ∈ Finset.range count, Ico (left j) (right j) ⊆ S)
    (t : Set ℝ) (ht : MeasurableSet t) :
    (∑ j ∈ Finset.range count, volume (t ∩ Ico (left j) (right j))) ≤
      volume (t ∩ S) := by
  let μ : Measure ℝ := volume.restrict (t ∩ S)
  have hnull : ∀ i ∈ Finset.range count,
      NullMeasurableSet (Ico (left i) (right i)) μ := by
    intro i hi
    exact measurableSet_Ico.nullMeasurableSet
  have hdisj : (↑(Finset.range count) : Set ℕ).Pairwise
      (Function.onFun (AEDisjoint μ) (fun i => Ico (left i) (right i))) := by
    intro i hi j hj hij
    apply (Set.disjoint_left.2 ?_).aedisjoint
    intro x hxi hxj
    rcases lt_or_gt_of_ne hij with hij' | hji
    · have hri : right i ≤ x :=
        le_trans (hsep i (Finset.mem_coe.mp hi) j (Finset.mem_coe.mp hj) hij') hxj.1
      exact (not_lt_of_ge hri) hxi.2
    · have hrj : right j ≤ x :=
        le_trans (hsep j (Finset.mem_coe.mp hj) i (Finset.mem_coe.mp hi) hji) hxi.1
      exact (not_lt_of_ge hrj) hxj.2
  have hsum := sum_measure_le_measure_univ hnull hdisj
  have hterm : ∀ j ∈ Finset.range count,
      μ (Ico (left j) (right j)) = volume (t ∩ Ico (left j) (right j)) := by
    intro j hj
    rw [show μ = volume.restrict (t ∩ S) by rfl,
      Measure.restrict_apply measurableSet_Ico]
    congr 1
    ext x
    constructor
    · intro hx
      exact ⟨hx.2.1, hx.1⟩
    · intro hx
      exact ⟨hx.2, hx.1, hsubset j hj hx.2⟩
  calc
    (∑ j ∈ Finset.range count, volume (t ∩ Ico (left j) (right j))) =
        ∑ j ∈ Finset.range count, μ (Ico (left j) (right j)) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact (hterm j hj).symm
    _ ≤ μ Set.univ := hsum
    _ = volume (t ∩ S) := by simp [μ]

theorem q11IntervalReferenceMeasure_le_restrict
    {left right : ℕ → ℝ} {count : ℕ} {units : List ℕ} {width : ℝ}
    {S : Set ℝ}
    (hwidth : 0 < width)
    (hdensity : ∀ j ∈ Finset.range count,
      q11IntervalDensity units width j ≤ 1)
    (hsep : ∀ i ∈ Finset.range count, ∀ j ∈ Finset.range count,
      i < j → right i ≤ left j)
    (hsubset : ∀ j ∈ Finset.range count,
      Ico (left j) (right j) ⊆ S) :
    q11IntervalReferenceMeasure left right count units width ≤
      volume.restrict S := by
  apply Measure.le_iff.2
  intro t ht
  unfold q11IntervalReferenceMeasure
  rw [Measure.finsetSum_apply]
  simp_rw [Measure.smul_apply, Measure.restrict_apply ht]
  have hterm : ∀ j ∈ Finset.range count,
      ENNReal.ofReal (q11IntervalDensity units width j) •
          volume (t ∩ Ico (left j) (right j)) ≤
        volume (t ∩ Ico (left j) (right j)) := by
    intro j hj
    simpa using (smul_le_smul (ENNReal.ofReal_le_ofReal (hdensity j hj)) le_rfl
      (show (0 : ENNReal) ≤ ENNReal.ofReal (q11IntervalDensity units width j) by positivity)
      (show (0 : ENNReal) ≤ volume (t ∩ Ico (left j) (right j)) by positivity))
  calc
    (∑ x ∈ Finset.range count,
        ENNReal.ofReal (q11IntervalDensity units width x) •
          volume (t ∩ Ico (left x) (right x))) ≤
        ∑ x ∈ Finset.range count,
          volume (t ∩ Ico (left x) (right x)) := by
      apply Finset.sum_le_sum
      intro j hj
      exact hterm j hj
    _ ≤ volume (t ∩ S) := interval_sum_inter_le_restrict hsep hsubset t ht

theorem q11PinnedReferenceMeasure_le_restrict :
    q11PinnedReferenceMeasure ≤ volume.restrict (Icc (1 / 4 : ℝ) (5 / 4 : ℝ)) := by
  unfold q11PinnedReferenceMeasure
  apply q11IntervalReferenceMeasure_le_restrict (by norm_num)
  · intro j hj
    have hj' : j < 8 := Finset.mem_range.mp hj
    interval_cases j <;>
      norm_num [q11IntervalDensity, q11MassUnitReal, pinnedMassUnits, denominator]
  · intro i hi j hj hij
    have hi' : i < 8 := Finset.mem_range.mp hi
    have hj' : j < 8 := Finset.mem_range.mp hj
    interval_cases i <;> interval_cases j <;>
      norm_num [q11PinnedEdgeReal, pinnedEdge, pinnedEdge32Units] at *
  · intro j hj x hx
    have hj' : j < 8 := Finset.mem_range.mp hj
    constructor
    · have hfirst : (1 / 4 : ℝ) ≤ q11PinnedEdgeReal j := by
        interval_cases j <;>
          norm_num [q11PinnedEdgeReal, pinnedEdge, pinnedEdge32Units]
      exact le_trans hfirst hx.1
    · have hlast : q11PinnedEdgeReal (j + 1) ≤ (5 / 4 : ℝ) := by
        have hj'' : j + 1 ≤ 8 := by omega
        interval_cases j <;>
          norm_num [q11PinnedEdgeReal, pinnedEdge, pinnedEdge32Units]
      exact le_trans (le_of_lt hx.2) hlast

theorem q11FrequencyReferenceMeasure_le_restrict :
    q11FrequencyReferenceMeasure ≤ volume.restrict (Icc (1 / 2 : ℝ) (9 / 2 : ℝ)) := by
  unfold q11FrequencyReferenceMeasure
  apply q11IntervalReferenceMeasure_le_restrict (by norm_num)
  · intro j hj
    have hj' : j < 4 := Finset.mem_range.mp hj
    interval_cases j <;>
      norm_num [q11IntervalDensity, q11MassUnitReal, frequencyMassUnits, denominator]
  · intro i hi j hj hij
    have hi' : i < 4 := Finset.mem_range.mp hi
    have hj' : j < 4 := Finset.mem_range.mp hj
    interval_cases i <;> interval_cases j <;>
      norm_num [q11FrequencyEdgeReal, frequencyEdge, frequencyEdge2Units] at *
  · intro j hj x hx
    have hj' : j < 4 := Finset.mem_range.mp hj
    constructor
    · have hfirst : (1 / 2 : ℝ) ≤ q11FrequencyEdgeReal j := by
        interval_cases j <;>
          norm_num [q11FrequencyEdgeReal, frequencyEdge, frequencyEdge2Units]
      exact le_trans hfirst hx.1
    · have hlast : q11FrequencyEdgeReal (j + 1) ≤ (9 / 2 : ℝ) := by
        have hj' : j + 1 ≤ 4 := by omega
        interval_cases j <;>
          norm_num [q11FrequencyEdgeReal, frequencyEdge, frequencyEdge2Units]
      exact le_trans (le_of_lt hx.2) hlast

end
end Li2Lean.P0.Q11Data
