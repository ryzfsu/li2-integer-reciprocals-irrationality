/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.Q11Reference
import Li2Lean.P0.ConfigPinnedTail

open MeasureTheory Set
open scoped ENNReal

namespace Li2Lean.P0.Q11Data

noncomputable section

open Li2Lean.LogSegment

theorem q11IntervalDensity_nonneg (units : List ℕ) {width : ℝ}
    (hwidth : 0 < width) (j : ℕ) :
    0 ≤ q11IntervalDensity units width j := by
  unfold q11IntervalDensity q11MassUnitReal
  have hden : 0 < (denominator : ℝ) := by exact_mod_cast denominator_pos
  positivity

theorem q11MassUnitReal_nonneg (units : List ℕ) (j : ℕ) :
    0 ≤ q11MassUnitReal units j := by
  unfold q11MassUnitReal
  have hden : 0 < (denominator : ℝ) := by exact_mod_cast denominator_pos
  positivity

theorem integrable_log_q11IntervalReferenceMeasure
    (left right : ℕ → ℝ) (count : ℕ) (units : List ℕ) (width : ℝ)
    (hleft : ∀ j ∈ Finset.range count, left j ≤ right j) (x : ℝ) :
    Integrable (fun y => Real.log |x - y|)
      (q11IntervalReferenceMeasure left right count units width) := by
  unfold q11IntervalReferenceMeasure
  apply integrable_finsetSum_measure.mpr
  intro j hj
  exact (integrableOn_Ico_log_abs_sub x (hleft j hj)).smul_measure
    ENNReal.ofReal_ne_top

theorem q11IntervalReferenceMeasure_potential_eq_endpoints
    (left right : ℕ → ℝ) (count : ℕ) (units : List ℕ) (width : ℝ)
    (hwidth : 0 < width)
    (hleft : ∀ j ∈ Finset.range count, left j ≤ right j)
    (x : ℝ) :
    (∫ y, Real.log |x - y|
      ∂q11IntervalReferenceMeasure left right count units width) =
      ∑ j ∈ Finset.range count, q11IntervalDensity units width j *
        (primitive (x - left j) - primitive (x - right j)) := by
  unfold q11IntervalReferenceMeasure
  rw [integral_finsetSum_measure]
  · apply Finset.sum_congr rfl
    intro j hj
    rw [integral_smul_measure,
      ENNReal.toReal_ofReal (q11IntervalDensity_nonneg units hwidth j),
      integral_Ico_log_abs_sub x (hleft j hj)]
    rfl
  · intro j hj
    exact (integrableOn_Ico_log_abs_sub x (hleft j hj)).smul_measure
      ENNReal.ofReal_ne_top

theorem q11PinnedPotential_eq_endpoints (x : ℝ) :
    (∫ y, Real.log |x - y| ∂q11PinnedReferenceMeasure) =
      ∑ j ∈ Finset.range 8, q11IntervalDensity pinnedMassUnits (1 / 8 : ℝ) j *
        (primitive (x - q11PinnedEdgeReal j) -
          primitive (x - q11PinnedEdgeReal (j + 1))) := by
  unfold q11PinnedReferenceMeasure
  apply q11IntervalReferenceMeasure_potential_eq_endpoints
  · norm_num
  · intro j hj
    have hw := q11PinnedEdgeReal_width (Finset.mem_range.mp hj)
    linarith

def q11PinnedRealPotential (x : ℝ) : ℝ :=
  ∫ y, Real.log |x - y| ∂q11PinnedReferenceMeasure

def q11PinnedNegativePotential (t : ℝ) : ℝ :=
  q11PinnedRealPotential (-t)

theorem q11PinnedNegativePotential_eq_endpoints (t : ℝ) :
    q11PinnedNegativePotential t =
      ∑ j ∈ Finset.range 8,
        q11IntervalDensity pinnedMassUnits (1 / 8 : ℝ) j *
          (primitive (t + q11PinnedEdgeReal (j + 1)) -
            primitive (t + q11PinnedEdgeReal j)) := by
  unfold q11PinnedNegativePotential q11PinnedRealPotential
  rw [q11PinnedPotential_eq_endpoints]
  apply Finset.sum_congr rfl
  intro j hj
  have hleft : -t - q11PinnedEdgeReal j = -(t + q11PinnedEdgeReal j) := by ring
  have hright : -t - q11PinnedEdgeReal (j + 1) =
      -(t + q11PinnedEdgeReal (j + 1)) := by ring
  rw [hleft, hright, Li2Lean.P0.ConfigPinnedTail.primitive_neg,
    Li2Lean.P0.ConfigPinnedTail.primitive_neg]
  ring

theorem q11PinnedComplexPotential_negative (t : ℝ) :
    q11PinnedComplexPotential (Complex.ofReal (-t)) =
      q11PinnedNegativePotential t := by
  simp only [q11PinnedComplexPotential, q11PinnedNegativePotential,
    q11PinnedRealPotential, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs]

theorem q11PinnedEdgeReal_ge_quarter {j : ℕ} (hj : j < 8) :
    1 / 4 ≤ q11PinnedEdgeReal j := by
  interval_cases j <;>
    norm_num [q11PinnedEdgeReal, pinnedEdge, pinnedEdge32Units]

theorem q11PinnedNegativePotential_hasDerivAt {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt q11PinnedNegativePotential
      (∑ j ∈ Finset.range 8,
        q11IntervalDensity pinnedMassUnits (1 / 8 : ℝ) j *
          (Real.log (t + q11PinnedEdgeReal (j + 1)) -
            Real.log (t + q11PinnedEdgeReal j))) t := by
  have hform : q11PinnedNegativePotential = fun s =>
      ∑ j ∈ Finset.range 8,
        q11IntervalDensity pinnedMassUnits (1 / 8 : ℝ) j *
          (primitive (s + q11PinnedEdgeReal (j + 1)) -
            primitive (s + q11PinnedEdgeReal j)) := by
    funext s
    exact q11PinnedNegativePotential_eq_endpoints s
  rw [hform]
  apply HasDerivAt.fun_sum
  intro j hj
  have hj8 : j < 8 := Finset.mem_range.mp hj
  have hj9 : j + 1 < 9 := by omega
  have hleft_pos : 0 < t + q11PinnedEdgeReal j := by
    have hleft := q11PinnedEdgeReal_ge_quarter hj8
    linarith
  have hright_pos : 0 < t + q11PinnedEdgeReal (j + 1) := by
    have hright : 1 / 4 ≤ q11PinnedEdgeReal (j + 1) := by
      interval_cases j <;>
        norm_num [q11PinnedEdgeReal, pinnedEdge, pinnedEdge32Units]
    linarith
  simpa only [integral_log_add] using!
    (hasDerivAt_integral_log_add
      (t := t) (a := q11PinnedEdgeReal j)
      (b := q11PinnedEdgeReal (j + 1)) hleft_pos.ne' hright_pos.ne').const_mul
        (q11IntervalDensity pinnedMassUnits (1 / 8 : ℝ) j)

theorem q11PinnedMassUnitReal_sum :
    (∑ j ∈ Finset.range 8, q11MassUnitReal pinnedMassUnits j) =
      (pinnedMassUnits.sum : ℝ) / (denominator : ℝ) := by
  unfold q11MassUnitReal
  rw [← Finset.sum_div, ← pinned_masses_length, q11_sum_getD_cast]

theorem q11PinnedNegativePotential_deriv_le {t : ℝ} (ht : 0 ≤ t) :
    deriv q11PinnedNegativePotential t ≤
      ((pinnedMassUnits.sum : ℝ) / (denominator : ℝ)) / (t + 1 / 4) := by
  have hder := q11PinnedNegativePotential_hasDerivAt ht
  have hcell : ∀ j ∈ Finset.range 8,
      q11IntervalDensity pinnedMassUnits (1 / 8 : ℝ) j *
          (Real.log (t + q11PinnedEdgeReal (j + 1)) -
            Real.log (t + q11PinnedEdgeReal j)) ≤
        q11MassUnitReal pinnedMassUnits j / (t + 1 / 4) := by
    intro j hj
    have hj8 : j < 8 := Finset.mem_range.mp hj
    have hleft_ge := q11PinnedEdgeReal_ge_quarter hj8
    have hwidth := q11PinnedEdgeReal_width hj8
    have hleft_pos : 0 < t + q11PinnedEdgeReal j := by linarith
    have hright_pos : 0 < t + q11PinnedEdgeReal (j + 1) := by linarith
    have hlog := Li2Lean.P0.ConfigPinnedTail.log_add_difference_le
      (t := t + q11PinnedEdgeReal j)
      (a := 0) (b := (1 / 8 : ℝ)) (by linarith) (by linarith)
    have hlog' : Real.log (t + q11PinnedEdgeReal (j + 1)) -
        Real.log (t + q11PinnedEdgeReal j) ≤
        (1 / 8 : ℝ) / (t + q11PinnedEdgeReal j) := by
      have hstep : t + q11PinnedEdgeReal (j + 1) =
          (t + q11PinnedEdgeReal j) + 1 / 8 := by linarith
      rw [hstep]
      simpa using hlog
    have hbase_pos : 0 < t + 1 / 4 := by linarith
    have hden_le : t + 1 / 4 ≤ t + q11PinnedEdgeReal j := by linarith
    have hmass_nonneg := q11MassUnitReal_nonneg pinnedMassUnits j
    have hdens_width :
        q11IntervalDensity pinnedMassUnits (1 / 8 : ℝ) j * (1 / 8 : ℝ) =
          q11MassUnitReal pinnedMassUnits j := by
      unfold q11IntervalDensity q11MassUnitReal
      field_simp
    calc
      _ ≤ q11IntervalDensity pinnedMassUnits (1 / 8 : ℝ) j *
          ((1 / 8 : ℝ) / (t + q11PinnedEdgeReal j)) :=
        mul_le_mul_of_nonneg_left hlog'
          (q11IntervalDensity_nonneg pinnedMassUnits (by norm_num) j)
      _ = (q11IntervalDensity pinnedMassUnits (1 / 8 : ℝ) j * (1 / 8 : ℝ)) /
          (t + q11PinnedEdgeReal j) := by ring
      _ ≤ q11MassUnitReal pinnedMassUnits j / (t + 1 / 4) := by
        rw [hdens_width]
        exact div_le_div_of_nonneg_left hmass_nonneg hbase_pos hden_le
  calc
    deriv q11PinnedNegativePotential t =
        ∑ j ∈ Finset.range 8,
          q11IntervalDensity pinnedMassUnits (1 / 8 : ℝ) j *
            (Real.log (t + q11PinnedEdgeReal (j + 1)) -
              Real.log (t + q11PinnedEdgeReal j)) := by
      rw [hder.deriv]
    _ ≤ ∑ j ∈ Finset.range 8,
        q11MassUnitReal pinnedMassUnits j / (t + 1 / 4) := by
      apply Finset.sum_le_sum
      intro j hj
      exact hcell j hj
    _ = (∑ j ∈ Finset.range 8,
        q11MassUnitReal pinnedMassUnits j) / (t + 1 / 4) := by
      rw [Finset.sum_div]
    _ = ((pinnedMassUnits.sum : ℝ) / (denominator : ℝ)) /
        (t + 1 / 4) := by rw [q11PinnedMassUnitReal_sum]


theorem q11FrequencyPotential_eq_endpoints (t : ℝ) :
    q11FrequencyPotential t =
      ∑ j ∈ Finset.range 4, q11IntervalDensity frequencyMassUnits 1 j *
        (primitive (t - q11FrequencyEdgeReal j) -
          primitive (t - q11FrequencyEdgeReal (j + 1))) := by
  unfold q11FrequencyPotential q11FrequencyReferenceMeasure
  apply q11IntervalReferenceMeasure_potential_eq_endpoints
  · norm_num
  · intro j hj
    have hw := q11FrequencyEdgeReal_width (Finset.mem_range.mp hj)
    linarith

theorem q11FrequencyPotential_hasDerivAt {t : ℝ}
    (hleft : ∀ j ∈ Finset.range 4, t ≠ q11FrequencyEdgeReal j)
    (hright : ∀ j ∈ Finset.range 4,
      t ≠ q11FrequencyEdgeReal (j + 1)) :
    HasDerivAt q11FrequencyPotential
      (∑ j ∈ Finset.range 4,
        q11IntervalDensity frequencyMassUnits 1 j *
          (Real.log |t - q11FrequencyEdgeReal j| -
            Real.log |t - q11FrequencyEdgeReal (j + 1)|)) t := by
  have hform : q11FrequencyPotential = fun s =>
      ∑ j ∈ Finset.range 4,
        q11IntervalDensity frequencyMassUnits 1 j *
          (primitive (s - q11FrequencyEdgeReal j) -
            primitive (s - q11FrequencyEdgeReal (j + 1))) := by
    funext s
    exact q11FrequencyPotential_eq_endpoints s
  rw [hform]
  apply HasDerivAt.fun_sum
  intro j hj
  simpa only [integral_log_abs_sub] using!
    (hasDerivAt_integral_log_abs_sub (hleft j hj) (hright j hj)).const_mul
      (q11IntervalDensity frequencyMassUnits 1 j)

theorem q11FrequencyEdgeReal_le_four {j : ℕ} (hj : j ≤ 4) :
    q11FrequencyEdgeReal j ≤ q11FrequencyEdgeReal 4 := by
  interval_cases j <;>
    norm_num [q11FrequencyEdgeReal, frequencyEdge, frequencyEdge2Units]

theorem q11FrequencyPotential_deriv_le {t : ℝ} (ht : 9 / 2 < t) :
    deriv q11FrequencyPotential t ≤ 1 / (t - 9 / 2) := by
  have hleft : ∀ j ∈ Finset.range 4, t ≠ q11FrequencyEdgeReal j := by
    intro j hj
    have hj4 : j < 4 := Finset.mem_range.mp hj
    have hj' : j ≤ 4 := by omega
    have hed := q11FrequencyEdgeReal_le_four hj'
    have hfour : q11FrequencyEdgeReal 4 = 9 / 2 := by
      norm_num [q11FrequencyEdgeReal, frequencyEdge, frequencyEdge2Units]
    linarith
  have hright : ∀ j ∈ Finset.range 4,
      t ≠ q11FrequencyEdgeReal (j + 1) := by
    intro j hj
    have hj4 : j < 4 := Finset.mem_range.mp hj
    have hj' : j + 1 ≤ 4 := by omega
    have hed := q11FrequencyEdgeReal_le_four hj'
    have hfour : q11FrequencyEdgeReal 4 = 9 / 2 := by
      norm_num [q11FrequencyEdgeReal, frequencyEdge, frequencyEdge2Units]
    linarith
  have hder := q11FrequencyPotential_hasDerivAt hleft hright
  have hcell : ∀ j ∈ Finset.range 4,
      q11IntervalDensity frequencyMassUnits 1 j *
          (Real.log |t - q11FrequencyEdgeReal j| -
            Real.log |t - q11FrequencyEdgeReal (j + 1)|) ≤
        q11MassUnitReal frequencyMassUnits j / (t - 9 / 2) := by
    intro j hj
    have hj4 : j < 4 := Finset.mem_range.mp hj
    have hj' : j + 1 ≤ 4 := by omega
    have hed := q11FrequencyEdgeReal_le_four hj'
    have hfour : q11FrequencyEdgeReal 4 = 9 / 2 := by
      norm_num [q11FrequencyEdgeReal, frequencyEdge, frequencyEdge2Units]
    have hwidth := q11FrequencyEdgeReal_width (Finset.mem_range.mp hj)
    have hright_le : q11FrequencyEdgeReal (j + 1) ≤ 9 / 2 := by linarith
    have hden : 0 < t - q11FrequencyEdgeReal (j + 1) := by linarith
    have hden0 : 0 < t - 9 / 2 := by linarith
    have hlog := Li2Lean.P0.ConfigPinnedTail.log_add_difference_le
      (t := t - q11FrequencyEdgeReal (j + 1))
      (a := 0) (b := 1) (by linarith) (by linarith)
    have hratio :
        Real.log |t - q11FrequencyEdgeReal j| -
            Real.log |t - q11FrequencyEdgeReal (j + 1)| ≤
          1 / (t - q11FrequencyEdgeReal (j + 1)) := by
      have hleft_pos : 0 < t - q11FrequencyEdgeReal j := by
        have hmono := q11FrequencyEdgeReal_width (Finset.mem_range.mp hj)
        linarith
      rw [abs_of_pos hleft_pos, abs_of_pos hden]
      have hsub : t - q11FrequencyEdgeReal j =
          (t - q11FrequencyEdgeReal (j + 1)) + 1 := by
        linarith
      rw [hsub]
      simpa using hlog
    have hratio' :
        Real.log |t - q11FrequencyEdgeReal j| -
            Real.log |t - q11FrequencyEdgeReal (j + 1)| ≤
          (t - q11FrequencyEdgeReal (j + 1))⁻¹ := by
      simpa [one_div] using hratio
    have hden_le : t - 9 / 2 ≤ t - q11FrequencyEdgeReal (j + 1) := by
      linarith
    have hdens_width : q11IntervalDensity frequencyMassUnits 1 j =
        q11MassUnitReal frequencyMassUnits j := by
      unfold q11IntervalDensity
      norm_num
    rw [hdens_width]
    calc
      _ ≤ q11MassUnitReal frequencyMassUnits j /
          (t - q11FrequencyEdgeReal (j + 1)) := by
        exact mul_le_mul_of_nonneg_left hratio' (q11MassUnitReal_nonneg _ _)
      _ ≤ q11MassUnitReal frequencyMassUnits j / (t - 9 / 2) := by
        exact div_le_div_of_nonneg_left
          (q11MassUnitReal_nonneg _ _) hden0 hden_le
  calc
    deriv q11FrequencyPotential t =
        ∑ j ∈ Finset.range 4,
          q11IntervalDensity frequencyMassUnits 1 j *
            (Real.log |t - q11FrequencyEdgeReal j| -
              Real.log |t - q11FrequencyEdgeReal (j + 1)|) := by
      rw [hder.deriv]
    _ ≤ ∑ j ∈ Finset.range 4,
        q11MassUnitReal frequencyMassUnits j / (t - 9 / 2) := by
      apply Finset.sum_le_sum
      intro j hj
      exact hcell j hj
    _ = (∑ j ∈ Finset.range 4, q11MassUnitReal frequencyMassUnits j) /
        (t - 9 / 2) := by rw [Finset.sum_div]
    _ = 1 / (t - 9 / 2) := by
      have hsum : ∑ j ∈ Finset.range 4,
          q11MassUnitReal frequencyMassUnits j = 1 := by
        unfold q11MassUnitReal
        rw [← Finset.sum_div, ← frequency_masses_length, q11_sum_getD_cast,
          frequency_mass_sum]
        norm_num [denominator]
      rw [hsum]

end

end Li2Lean.P0.Q11Data
