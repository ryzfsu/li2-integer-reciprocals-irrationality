/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.Q11Potential
import Li2Lean.P0.CA.Frequency.Terms

open MeasureTheory

namespace Li2Lean.P0.Q11Data

noncomputable section

open Li2Lean.P0.CA.Frequency
open Li2Lean.P0.ConfigSegment
open Li2Lean.LogSegment

/-!
Finite primitive expansion of the q = 11 frequency field, following the
endpoint-integral construction in v13 `certificate-algorithm.tex:29-39` and
the q11 rows in `p0-reference-data.tex:29-40`.  The contour potential remains
the actual q11 potential; its Fourier reduction is a separate input.
-/

def q11DensityQ (units : List ℕ) (width : ℚ) (j : ℕ) : ℚ :=
  ((units.getD j 0 : ℚ) / denominator) / width

theorem q11DensityQ_cast (units : List ℕ) (width : ℚ) (j : ℕ) :
    (q11DensityQ units width j : ℝ) =
      q11IntervalDensity units (width : ℝ) j := by
  simp [q11DensityQ, q11IntervalDensity, q11MassUnitReal, denominator]

def q11FrequencyPair (j : ℕ) : List (ℚ × ℚ) :=
  [(-2 * q11DensityQ frequencyMassUnits 1 j, -frequencyEdge j),
   (2 * q11DensityQ frequencyMassUnits 1 j, -frequencyEdge (j + 1))]

def q11PinnedPair (j : ℕ) : List (ℚ × ℚ) :=
  [(q11DensityQ pinnedMassUnits (1 / 8) j, pinnedEdge j),
   (-q11DensityQ pinnedMassUnits (1 / 8) j, pinnedEdge (j + 1))]

def q11FrequencyTerms : List (ℚ × ℚ) :=
  [(1, 5 / 4), (-1, 1 / 4), (1, 2), (-1, 0), (-1, 0), (1, -(1 / 2))] ++
    (List.range 4).flatMap q11FrequencyPair ++
    (List.range 8).flatMap q11PinnedPair

theorem termsVal_q11FrequencyPair (j : ℕ) (t : ℝ) :
    termsVal (q11FrequencyPair j) t =
      -2 * q11IntervalDensity frequencyMassUnits 1 j *
        (primitive (t - q11FrequencyEdgeReal j) -
          primitive (t - q11FrequencyEdgeReal (j + 1))) := by
  have hd := q11DensityQ_cast frequencyMassUnits 1 j
  have he1 : -((frequencyEdge j : ℚ) : ℝ) = -q11FrequencyEdgeReal j := by
    simp [q11FrequencyEdgeReal]
  have he2 : -((frequencyEdge (j + 1) : ℚ) : ℝ) =
      -q11FrequencyEdgeReal (j + 1) := by
    simp [q11FrequencyEdgeReal]
  simp only [q11FrequencyPair, termsVal, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_neg]
  rw [hd, he1, he2]
  simp only [← sub_eq_add_neg, Rat.cast_one]
  ring

theorem termsVal_q11PinnedPair (j : ℕ) (t : ℝ) :
    termsVal (q11PinnedPair j) t =
      -q11IntervalDensity pinnedMassUnits (1 / 8 : ℝ) j *
        (primitive (t + q11PinnedEdgeReal (j + 1)) -
          primitive (t + q11PinnedEdgeReal j)) := by
  have hd := q11DensityQ_cast pinnedMassUnits (1 / 8) j
  have he1 : ((pinnedEdge j : ℚ) : ℝ) = q11PinnedEdgeReal j := by
    simp [q11PinnedEdgeReal]
  have he2 : ((pinnedEdge (j + 1) : ℚ) : ℝ) =
      q11PinnedEdgeReal (j + 1) := by
    simp [q11PinnedEdgeReal]
  simp only [q11PinnedPair, termsVal, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Rat.cast_neg]
  rw [hd, he1, he2]
  ring

theorem q11FrequencyTerms_eq_integral_parts (t : ℝ) :
    termsVal q11FrequencyTerms t =
      (primitive (t + 5 / 4) - primitive (t + 1 / 4) +
        (primitive (t + 2) - primitive t)) - primitive t +
        primitive (t - 1 / 2) - 2 * q11FrequencyPotential t -
        q11PinnedNegativePotential t := by
  unfold q11FrequencyTerms
  rw [termsVal_append, termsVal_append, termsVal_flatMap_range,
    termsVal_flatMap_range]
  have hfreq :
      (∑ j ∈ Finset.range 4, termsVal (q11FrequencyPair j) t) =
        -2 * q11FrequencyPotential t := by
    rw [q11FrequencyPotential_eq_endpoints]
    simp_rw [termsVal_q11FrequencyPair]
    calc
      (∑ j ∈ Finset.range 4,
          -2 * q11IntervalDensity frequencyMassUnits 1 j *
            (primitive (t - q11FrequencyEdgeReal j) -
              primitive (t - q11FrequencyEdgeReal (j + 1)))) =
          ∑ j ∈ Finset.range 4,
            -2 * (q11IntervalDensity frequencyMassUnits 1 j *
              (primitive (t - q11FrequencyEdgeReal j) -
                primitive (t - q11FrequencyEdgeReal (j + 1)))) := by
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = -2 * ∑ j ∈ Finset.range 4,
          q11IntervalDensity frequencyMassUnits 1 j *
            (primitive (t - q11FrequencyEdgeReal j) -
              primitive (t - q11FrequencyEdgeReal (j + 1))) := by
        rw [← Finset.mul_sum]
  have hpin :
      (∑ j ∈ Finset.range 8, termsVal (q11PinnedPair j) t) =
        -q11PinnedNegativePotential t := by
    rw [q11PinnedNegativePotential_eq_endpoints]
    simp_rw [termsVal_q11PinnedPair]
    calc
      (∑ j ∈ Finset.range 8,
          -q11IntervalDensity pinnedMassUnits (1 / 8 : ℝ) j *
            (primitive (t + q11PinnedEdgeReal (j + 1)) -
              primitive (t + q11PinnedEdgeReal j))) =
          ∑ j ∈ Finset.range 8,
            -(q11IntervalDensity pinnedMassUnits (1 / 8 : ℝ) j *
              (primitive (t + q11PinnedEdgeReal (j + 1)) -
                primitive (t + q11PinnedEdgeReal j))) := by
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = -(∑ j ∈ Finset.range 8,
          q11IntervalDensity pinnedMassUnits (1 / 8 : ℝ) j *
            (primitive (t + q11PinnedEdgeReal (j + 1)) -
              primitive (t + q11PinnedEdgeReal j))) := by
        rw [← Finset.sum_neg_distrib]
  have hbase : termsVal
      [(1, 5 / 4), (-1, 1 / 4), (1, 2), (-1, 0), (-1, 0),
        (1, -(1 / 2))] t =
      primitive (t + 5 / 4) - primitive (t + 1 / 4) +
        (primitive (t + 2) - primitive t) - primitive t +
          primitive (t - 1 / 2) := by
    simp [termsVal]
    ring
  rw [hbase, hfreq, hpin]
  ring

theorem q11Wmu_eq_frequencyTerms (t : ℝ) :
    q11Wmu t =
      -1 / 2 - Real.log 2 / 2 + t * (Real.log 2 + q11Lambda) +
        termsVal q11FrequencyTerms t -
        q11ContourPotential (Complex.ofReal (-t)) := by
  have hparts := q11FrequencyTerms_eq_integral_parts t
  simp only [q11Wmu, q11Psi, q11ActualReference, q11EtaReferencePotential]
  rw [B0_eq_endpoints, q11PinnedComplexPotential_negative]
  rw [Li2Lean.P0.CA.Frequency.psi_eq_primitive]
  calc
    _ = (-1 / 2 - Real.log 2 / 2 + t * (Real.log 2 + q11Lambda)) +
        ((primitive (t + 5 / 4) - primitive (t + 1 / 4) +
          (primitive (t + 2) - primitive t)) - primitive t +
          primitive (t - 1 / 2) - 2 * q11FrequencyPotential t -
          q11PinnedNegativePotential t) -
        q11ContourPotential (Complex.ofReal (-t)) := by ring
    _ = -1 / 2 - Real.log 2 / 2 + t * (Real.log 2 + q11Lambda) +
        termsVal q11FrequencyTerms t -
        q11ContourPotential (Complex.ofReal (-t)) := by
      rw [← hparts]

end

end Li2Lean.P0.Q11Data

#print axioms Li2Lean.P0.Q11Data.q11Wmu_eq_frequencyTerms
