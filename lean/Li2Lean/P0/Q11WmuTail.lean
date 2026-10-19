/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.Q11ContourTail
import Li2Lean.P0.ConfigRealTail

open MeasureTheory

namespace Li2Lean.P0.Q11Data

noncomputable section

open Li2Lean.P0.ConfigContourTail

def q11BaseTail (t : ℝ) : ℝ := Config.B0 t - q11Psi t

theorem q11BaseTail_hasDerivAt {t : ℝ} (ht : (1 / 2 : ℝ) < t) :
    HasDerivAt q11BaseTail
      (deriv Config.B0 t -
        (Real.log t - Real.log (t - 1 / 2) - Real.log 2 - q11Lambda)) t := by
  have ht0 : 0 < t := by linarith
  have hB0 := Li2Lean.P0.ConfigRealTail.B0_hasDerivAt ht0
  have hpsi := Li2Lean.P0.ConfigRealTail.psi_hasDerivAt ht
  have hlambda : HasDerivAt (fun s : ℝ => q11Lambda * s) q11Lambda t :=
    by simpa only [id_eq, mul_one] using (hasDerivAt_id t).const_mul q11Lambda
  have hqpsi : HasDerivAt q11Psi
      (Real.log t - Real.log (t - 1 / 2) - Real.log 2 - q11Lambda) t := by
    change HasDerivAt (fun s : ℝ => Config.psi s - q11Lambda * s)
      (Real.log t - Real.log (t - 1 / 2) - Real.log 2 - q11Lambda) t
    exact hpsi.sub hlambda
  have hB0' : HasDerivAt Config.B0 (deriv Config.B0 t) t := by
    simpa only [hB0.deriv] using hB0
  change HasDerivAt (Config.B0 - q11Psi)
    (deriv Config.B0 t -
      (Real.log t - Real.log (t - 1 / 2) - Real.log 2 - q11Lambda)) t
  exact hB0'.sub hqpsi

theorem q11BaseTail_deriv_ge {t : ℝ} (ht : (1 / 2 : ℝ) < t) :
    3 / (t + 2) + Real.log 2 + q11Lambda +
        Real.log (t - 1 / 2) - Real.log t ≤ deriv q11BaseTail t := by
  have ht0 : 0 < t := by linarith
  rw [(q11BaseTail_hasDerivAt ht).deriv]
  have hB := Li2Lean.P0.ConfigRealTail.B0_deriv_ge ht0
  linarith

theorem q11FrequencyPotential_hasDerivAt_tail {t : ℝ}
    (ht : (9 / 2 : ℝ) < t) :
    HasDerivAt q11FrequencyPotential
      (∑ j ∈ Finset.range 4,
        q11IntervalDensity frequencyMassUnits 1 j *
          (Real.log |t - q11FrequencyEdgeReal j| -
            Real.log |t - q11FrequencyEdgeReal (j + 1)|)) t := by
  have hleft : ∀ j ∈ Finset.range 4, t ≠ q11FrequencyEdgeReal j := by
    intro j hj
    have hj4 : j < 4 := Finset.mem_range.mp hj
    have hed := q11FrequencyEdgeReal_le_four (j := j) (by omega)
    have hfour : q11FrequencyEdgeReal 4 = 9 / 2 := by
      norm_num [q11FrequencyEdgeReal, frequencyEdge, frequencyEdge2Units]
    linarith
  have hright : ∀ j ∈ Finset.range 4,
      t ≠ q11FrequencyEdgeReal (j + 1) := by
    intro j hj
    have hj4 : j < 4 := Finset.mem_range.mp hj
    have hed := q11FrequencyEdgeReal_le_four (j := j + 1) (by omega)
    have hfour : q11FrequencyEdgeReal 4 = 9 / 2 := by
      norm_num [q11FrequencyEdgeReal, frequencyEdge, frequencyEdge2Units]
    linarith
  exact q11FrequencyPotential_hasDerivAt hleft hright

theorem q11EtaPotential_negative_eq_parts (t : ℝ) :
    q11EtaReferencePotential (Complex.ofReal (-t)) =
      q11PinnedNegativePotential t + q11ContourPotential (-(t : ℂ)) := by
  unfold q11EtaReferencePotential
  rw [q11PinnedComplexPotential_negative]
  congr 1
  rw [Complex.ofReal_neg]

theorem q11Wmu_eq_tail_parts (t : ℝ) :
    q11Wmu t = q11BaseTail t - 2 * q11FrequencyPotential t -
      q11PinnedNegativePotential t - q11ContourPotential (-(t : ℂ)) := by
  dsimp [q11Wmu, q11ActualReference, q11BaseTail]
  rw [← Complex.ofReal_neg, q11EtaPotential_negative_eq_parts]
  rw [Complex.ofReal_neg]
  ring

theorem q11Wmu_hasDerivAt_tail {t : ℝ} (ht : (9 / 2 : ℝ) < t)
    (ht0 : 0 ≤ t) (hcont : leftClearance < t) :
    HasDerivAt q11Wmu
      (deriv q11BaseTail t - 2 * deriv q11FrequencyPotential t -
        deriv q11PinnedNegativePotential t -
        deriv (fun s : ℝ => q11ContourPotential (-(s : ℂ))) t) t := by
  have hbase := q11BaseTail_hasDerivAt
    (t := t) (by linarith : (1 / 2 : ℝ) < t)
  have hfreq := q11FrequencyPotential_hasDerivAt_tail ht
  have hpin := q11PinnedNegativePotential_hasDerivAt ht0
  have hcont' := q11_hasDerivAt_contourPotential_neg hcont
  have hparts : HasDerivAt
      (fun s : ℝ => q11BaseTail s - 2 * q11FrequencyPotential s -
        q11PinnedNegativePotential s - q11ContourPotential (-(s : ℂ)))
      (deriv q11BaseTail t - 2 * deriv q11FrequencyPotential t -
        deriv q11PinnedNegativePotential t -
        deriv (fun s : ℝ => q11ContourPotential (-(s : ℂ))) t) t := by
    have hfreq' : HasDerivAt (fun s : ℝ => 2 * q11FrequencyPotential s)
        (2 * deriv q11FrequencyPotential t) t := by
      simpa only [hfreq.deriv] using hfreq.const_mul 2
    have hpin' : HasDerivAt q11PinnedNegativePotential
        (deriv q11PinnedNegativePotential t) t := by
      simpa only [hpin.deriv] using hpin
    have hbase' : HasDerivAt q11BaseTail (deriv q11BaseTail t) t := by
      simpa only [hbase.deriv] using hbase
    have hcont'' : HasDerivAt
        (fun s : ℝ => q11ContourPotential (-(s : ℂ)))
        (deriv (fun s : ℝ => q11ContourPotential (-(s : ℂ))) t) t := by
      simpa only [hcont'.deriv] using hcont'
    exact (((hbase'.sub hfreq').sub hpin').sub hcont'')
  have hEq : q11Wmu = fun s : ℝ =>
      q11BaseTail s - 2 * q11FrequencyPotential s -
        q11PinnedNegativePotential s - q11ContourPotential (-(s : ℂ)) := by
    funext s
    exact q11Wmu_eq_tail_parts s
  rw [hEq]
  exact hparts

theorem q11Wmu_deriv_ge_tail {t : ℝ} (ht : (81 / 10 : ℝ) ≤ t) :
    3 / (t + 2) + Real.log 2 + q11Lambda +
        Real.log (t - 1 / 2) - Real.log t -
        2 / (t - 9 / 2) -
        ((pinnedMassUnits.sum : ℝ) / (denominator : ℝ)) / (t + 1 / 4) -
        q11ContourMass / (t - leftClearance) ≤ deriv q11Wmu t := by
  have ht0 : 0 ≤ t := by linarith
  have hhalf : (1 / 2 : ℝ) < t := by linarith
  have hfreq : (9 / 2 : ℝ) < t := by linarith
  have hclear : leftClearance < t := by
    unfold leftClearance
    linarith
  have hder := q11Wmu_hasDerivAt_tail hfreq ht0 hclear
  rw [hder.deriv]
  have hbase := q11BaseTail_deriv_ge hhalf
  have hfreqBound := q11FrequencyPotential_deriv_le hfreq
  have hpinBound := q11PinnedNegativePotential_deriv_le ht0
  have hcontBound := q11ContourPotential_neg_deriv_le hclear
  have hfreqBound2 :
      2 * deriv q11FrequencyPotential t ≤ 2 / (t - 9 / 2) := by
    have hscaled := mul_le_mul_of_nonneg_left hfreqBound (by norm_num : (0 : ℝ) ≤ 2)
    simpa [div_eq_mul_inv] using hscaled
  linarith

theorem q11Wmu_deriv_gt_one_tail {t : ℝ} (ht : (81 / 10 : ℝ) ≤ t) :
    1 < deriv q11Wmu t := by
  have htpos : 0 < t := by linarith
  have htHalf : 0 < t - 1 / 2 := by linarith
  have hratio : t / (t - 1 / 2) ≤ 81 / 76 := by
    apply (div_le_iff₀ htHalf).2
    nlinarith [ht]
  have hlogRatio : Real.log (t / (t - 1 / 2)) ≤ 1 / 10 := by
    calc
      Real.log (t / (t - 1 / 2)) ≤ Real.log (81 / 76) :=
        Real.log_le_log (div_pos htpos htHalf) hratio
      _ ≤ (81 / 76 : ℝ) - 1 :=
        Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 81 / 76)
      _ ≤ 1 / 10 := by norm_num
  have hlogDiv : Real.log (t / (t - 1 / 2)) =
      Real.log t - Real.log (t - 1 / 2) :=
    Real.log_div (ne_of_gt htpos) (ne_of_gt htHalf)
  have hlogDiff : -(1 / 10 : ℝ) ≤ Real.log (t - 1 / 2) - Real.log t := by
    linarith
  have hlogFour : Real.log (4 : ℝ) = Real.log 2 + Real.log 2 := by
    calc
      Real.log (4 : ℝ) = Real.log (2 * 2) := by norm_num
      _ = Real.log 2 + Real.log 2 := Real.log_mul (by norm_num) (by norm_num)
  have hlogFourLt : Real.log (4 : ℝ) < Real.log (11 / 2 : ℝ) :=
    Real.log_lt_log (by norm_num) (by norm_num)
  have hlogTwo : (2 : ℝ) / 3 < Real.log 2 := by
    have h := Real.log_two_gt_d9
    linarith
  have hlogs : (2 : ℝ) < Real.log 2 + q11Lambda := by
    unfold q11Lambda
    linarith
  have hfreqDen : 0 < t - 9 / 2 := by linarith
  have hfreqPenalty : 2 / (t - 9 / 2) ≤ 5 / 9 := by
    apply (div_le_iff₀ hfreqDen).2
    nlinarith [ht]
  have hpinMass : (pinnedMassUnits.sum : ℝ) / (denominator : ℝ) ≤ 1 := by
    rw [pinned_mass_sum]
    norm_num [denominator]
  have hpinDen : 0 < t + 1 / 4 := by linarith
  have hpinPenalty :
      ((pinnedMassUnits.sum : ℝ) / (denominator : ℝ)) / (t + 1 / 4) ≤ 1 / 8 := by
    apply (div_le_iff₀ hpinDen).2
    calc
      (pinnedMassUnits.sum : ℝ) / (denominator : ℝ) ≤ 1 := hpinMass
      _ ≤ (1 / 8 : ℝ) * (t + 1 / 4) := by nlinarith [ht]
  have hcontMass : q11ContourMass ≤ 1 := by
    unfold q11ContourMass
    rw [contour_pair_mass_sum]
    norm_num [denominator]
  have hclear : leftClearance < t := by
    unfold leftClearance
    linarith [ht]
  have hcontDen : 0 < t - leftClearance := by linarith
  have hcontPenalty : q11ContourMass / (t - leftClearance) ≤ 1 / 7 := by
    apply (div_le_iff₀ hcontDen).2
    calc
      q11ContourMass ≤ 1 := hcontMass
      _ ≤ (1 / 7 : ℝ) * (t - leftClearance) := by
        unfold leftClearance
        nlinarith [ht]
  have hthree : 0 ≤ 3 / (t + 2) := by positivity
  have hlower : (1 : ℝ) <
      3 / (t + 2) + Real.log 2 + q11Lambda +
        Real.log (t - 1 / 2) - Real.log t -
        2 / (t - 9 / 2) -
        ((pinnedMassUnits.sum : ℝ) / (denominator : ℝ)) / (t + 1 / 4) -
        q11ContourMass / (t - leftClearance) := by
    linarith
  exact lt_of_lt_of_le hlower (q11Wmu_deriv_ge_tail ht)

theorem q11Wmu_strictMonoOn_tail :
    StrictMonoOn q11Wmu (Set.Ici (81 / 10 : ℝ)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici _)
  · intro t ht
    have ht' : (81 / 10 : ℝ) ≤ t := Set.mem_Ici.mp ht
    have ht0 : 0 ≤ t := by linarith
    have hfreq : (9 / 2 : ℝ) < t := by linarith
    have hclear : leftClearance < t := by
      unfold leftClearance
      linarith
    exact (q11Wmu_hasDerivAt_tail hfreq ht0 hclear).continuousAt.continuousWithinAt
  · intro t ht
    rw [interior_Ici] at ht
    have ht' : (81 / 10 : ℝ) < t := Set.mem_Ioi.mp ht
    exact lt_trans (by norm_num : (0 : ℝ) < 1)
      (q11Wmu_deriv_gt_one_tail (le_of_lt ht'))

theorem q11Wmu_endpoint_le_tail {t : ℝ} (ht : (81 / 10 : ℝ) ≤ t) :
    q11Wmu (81 / 10) ≤ q11Wmu t := by
  by_cases hEq : t = (81 / 10 : ℝ)
  · simp [hEq]
  · have hlt : (81 / 10 : ℝ) < t := lt_of_le_of_ne ht (Ne.symm hEq)
    exact (q11Wmu_strictMonoOn_tail (by norm_num) ht hlt).le

end

end Li2Lean.P0.Q11Data
