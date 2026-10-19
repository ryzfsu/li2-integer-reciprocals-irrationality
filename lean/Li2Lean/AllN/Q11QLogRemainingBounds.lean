/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/

import Li2Lean.AllN.Q11QLogConcreteBounds
import Li2Lean.P0.Q11ContourSelfEnergyEnclosure
import Li2Lean.P0.Q11ContourTail
import Li2Lean.P0.ConfigContourFormula
import Li2Lean.P0.ConfigFejerLog
import Li2Lean.P0.ActualReferenceQLogEnclosure
import Li2Lean.P0.ActualReferenceQLogOutsideBridge
import Li2Lean.P0.ActualReferencePinnedSemantics

set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

/-!
# Remaining `q = 11` logarithmic-energy component bounds and full `Q11QLogEnvelopeInputs` (`H7-bounds` r2)

Closes the remaining open component bounds of `Q11QLogEnvelopeInputs`:
1. `lowerContourFrequency` (`q11Eνμ ≥ 564360308 / 1000000000`),
2. `lowerPinnedContour` (`q11Eκν ≥ 85664740 / 1000000000`),
3. `lowerContourPinned` (`q11Eνκ ≥ 85664740 / 1000000000`, via `q11Eνκ_eq_Eκν`),
4. `lowerContourContour` (reusing master `Q11Data.lowerContourContour` and `q11Eνν_lower`
   from `Li2Lean/P0/Q11ContourSelfEnergyEnclosure.lean:140-156`, together with the certified
   lower bound `-193059871 / 1000000000 ≤ ratioToReal lowerContourContour`),

and assembles `q11_qlog_envelope_inputs_actual : Q11QLogEnvelopeInputs` and
`q11ActualReference_qLog_lower_proved : q11QLogLower` with total lower bound
`q11TotalLower = ⟨-635535679, 1000000000⟩ > -635537 / 1000000 = qLogLower`
(margin `1321 / 10^9 = 1.321 × 10⁻⁶`).

Source: v13 `chapters/p0-analytic.tex:749-826`, `chapters/certificate-algorithm.tex:50-75`.
-/

open MeasureTheory Set Filter
open scoped BigOperators Interval ENNReal

namespace Li2Lean.P0.Q11Data

noncomputable section

open Li2Lean.P0.ConfigContourReference
open Li2Lean.P0.ConfigContourKernel
open Li2Lean.P0.CA.Contour
open Li2Lean.P0.CA.Contour.QI
open Li2Lean.P0.ConfigContourFormula
open Li2Lean.P0.ConfigFejerLog
open Li2Lean.P0.ConfigInteriorContourPotential
open Li2Lean.P0.PinnedRow1ClosedForm
open Li2Lean.P0.ActualReferenceQLogOutside
open Li2Lean.P0.ActualReferenceQLogOutsideBridge
open Li2Lean.P0.ActualReferenceQLogEnclosure
open Li2Lean.P0.ActualReferenceQLogFormula
open Li2Lean.P0.ActualReferencePinnedData
open Li2Lean.P0.ActualReferencePinnedSemantics
open Li2Lean.P0.Q11QLogEnvelopeProducer

local instance : IsFiniteMeasure q11PinnedReferenceMeasure :=
  ⟨by rw [q11PinnedReferenceMeasure_mass]; exact ENNReal.ofReal_lt_top⟩

local instance : IsFiniteMeasure q11FrequencyReferenceMeasure :=
  ⟨by rw [q11FrequencyReferenceMeasure_univ]; exact ENNReal.one_lt_top⟩

local instance : IsFiniteMeasure q11ContourParamMeasure :=
  ⟨by rw [q11ContourParamMeasure_univ]; exact ENNReal.ofReal_lt_top⟩

/-! ## 1. Exterior Fourier bridges using `q11ContourLogPolynomial` from `Q11ContourFourier` -/

theorem q11_integral_contourDensity_log_norm {a : ℂ} (ha : ‖a‖ < 1) :
    (∫ u in (0 : ℝ)..(2 * Real.pi),
      q11ContourDensity u * Real.log ‖1 - a * phase u‖) =
      -(2 * Real.pi) * q11ContourLogPolynomial a :=
  q11ContourLogNorm_fejer a ha

theorem q11ContourPotential_neg_polynomial (t : ℝ) (ht : (1 / 2 : ℝ) ≤ t) :
    q11ContourPotential (-(t : ℂ)) =
      q11ContourMass * Real.log (outsideRadius t) -
        q11ContourLogPolynomial (outsideParameter t : ℂ) -
        q11ContourLogPolynomial ((contourRatio * outsideParameter t : ℝ) : ℂ) := by
  have h0 : IntervalIntegrable
      (fun u => q11ContourDensity u * Real.log (outsideRadius t)) volume 0 (2 * Real.pi) :=
    (continuous_q11ContourDensity.mul continuous_const).intervalIntegrable _ _
  have h1 : IntervalIntegrable
      (fun u => q11ContourDensity u *
        Real.log ‖1 - (outsideParameter t : ℂ) * phase u‖) volume 0 (2 * Real.pi) :=
    (continuous_q11ContourDensity.mul
      (continuous_log_norm (outsideParameter_norm_lt_one ht))).intervalIntegrable _ _
  have h2 : IntervalIntegrable
      (fun u => q11ContourDensity u *
        Real.log ‖1 - ((contourRatio * outsideParameter t : ℝ) : ℂ) * phase u‖)
      volume 0 (2 * Real.pi) := by
    apply Continuous.intervalIntegrable
    apply continuous_q11ContourDensity.mul
    apply continuous_log_norm
    simpa only [Complex.ofReal_mul] using outsideCorrection_norm_lt_one ht
  unfold q11ContourPotential q11ContourIntegral
  simp_rw [outside_log_distance ht, mul_add]
  rw [intervalIntegral.integral_add (h0.add h1) h2,
    intervalIntegral.integral_add h0 h1,
    intervalIntegral.integral_mul_const,
    q11IntegralContourDensity, q11ContourWeight_sum,
    q11_integral_contourDensity_log_norm (outsideParameter_norm_lt_one ht),
    q11_integral_contourDensity_log_norm (by
      simpa only [Complex.ofReal_mul] using outsideCorrection_norm_lt_one ht)]
  unfold q11ContourMass
  field_simp
  ring

def q11ContourMoment (n : ℕ) : ℝ :=
  (1 - (n : ℝ) / 49) *
    ∑ j : Fin contourNodeCount,
      q11ContourWeight j * Real.cos ((n : ℝ) * contourAngle j)

theorem q11ContourLogPolynomial_ofReal (x : ℝ) :
    q11ContourLogPolynomial (x : ℂ) =
      ∑ n ∈ Finset.range 49, q11ContourMoment n * (x ^ n / (n : ℝ)) := by
  unfold q11ContourLogPolynomial
  simp_rw [fejerLogPolynomial_ofReal_re, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _
  unfold q11ContourMoment
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem q11ContourPotential_neg (t : ℝ) (ht : (1 / 2 : ℝ) ≤ t) :
    q11ContourPotential (-(t : ℂ)) =
      q11ContourMass * Real.log (outsideRadius t) -
        ∑ n ∈ Finset.range 49,
          ((1 + contourRatio ^ n) * q11ContourMoment n / (n : ℝ)) *
            outsideParameter t ^ n := by
  rw [q11ContourPotential_neg_polynomial t ht,
    q11ContourLogPolynomial_ofReal, q11ContourLogPolynomial_ofReal,
    sub_sub, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  rw [mul_pow]
  ring

theorem q11ContourMoment_zero : q11ContourMoment 0 = q11ContourMass := by
  unfold q11ContourMoment q11ContourMass
  simp [q11ContourWeight_sum]

theorem q11ContourMoment_eq_fourierMoment {n : ℕ} (hn : n ≤ 48) :
    q11ContourMoment n = q11ContourFourierMoment n := by
  unfold q11ContourMoment q11ContourFourierMoment
  split_ifs
  rfl

/-! ## 2. `lowerContourContour` from master `Q11ContourSelfEnergyEnclosure` -/

private theorem q11SelfEnergyI_lo_check :
    decide ((-193059871 / 1000000000 : ℚ) ≤ q11SelfEnergyI.lo) = true := by
  decide +kernel

theorem lowerContourContour_ge_decimal :
    (-193059871 / 1000000000 : ℝ) ≤ ratioToReal lowerContourContour := by
  have hle_q : (-193059871 / 1000000000 : ℚ) ≤ q11SelfEnergyI.lo :=
    of_decide_eq_true q11SelfEnergyI_lo_check
  have hle_r : ((-193059871 / 1000000000 : ℚ) : ℝ) ≤ (q11SelfEnergyI.lo : ℝ) := by
    exact_mod_cast hle_q
  have hratio : ratioToReal lowerContourContour = (q11SelfEnergyI.lo : ℝ) := by
    change (q11SelfEnergyI.lo.num : ℝ) / (q11SelfEnergyI.lo.den : ℝ) = (q11SelfEnergyI.lo : ℝ)
    exact_mod_cast (Rat.num_div_den q11SelfEnergyI.lo)
  rw [hratio]
  refine le_trans ?_ hle_r
  norm_num

/-! ## 3. `lowerContourFrequency` (`q11Eνμ`) via the exterior Fourier primitive -/

theorem q11Eνμ_eq_frequency_integral :
    q11Eνμ = ∫ t, q11ContourPotential (-(t : ℂ)) ∂q11FrequencyReferenceMeasure := by
  unfold q11Eνμ q11ReflectedFrequencyPotential
  rw [integral_integral_swap q11_contour_frequency_log_integrable]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [q11ContourPotential_eq_integral]
  apply integral_congr_ae
  filter_upwards [] with z
  have hnorm : ‖z + (t : ℂ)‖ = ‖-(t : ℂ) - z‖ := by
    calc
      ‖z + (t : ℂ)‖ = ‖-(z + (t : ℂ))‖ := by rw [norm_neg]
      _ = ‖-(t : ℂ) - z‖ := by congr 1 <;> ring
  rw [hnorm]

def q11OutsideCoefficient (n : ℕ) : ℝ :=
  (1 + contourRatio ^ n) * q11ContourMoment n / (n : ℝ)

theorem q11OutsideCoefficient_zero : q11OutsideCoefficient 0 = 0 := by
  simp [q11OutsideCoefficient]

def q11OutsideContourPrimitive (t : ℝ) : ℝ :=
  q11ContourMass * outsideLogPrimitive (outsideRadius t) -
    ∑ n ∈ Finset.range 49, q11OutsideCoefficient n *
      outsidePowerPrimitive n (outsideRadius t)

theorem q11OutsideContourPrimitive_eq_sum48 (t : ℝ) :
    q11OutsideContourPrimitive t =
      q11ContourMass * outsideLogPrimitive (outsideRadius t) -
        ∑ n ∈ Finset.range 48, q11OutsideCoefficient (n + 1) *
          outsidePowerPrimitive (n + 1) (outsideRadius t) := by
  unfold q11OutsideContourPrimitive
  have h := Finset.sum_range_succ'
    (fun n => q11OutsideCoefficient n * outsidePowerPrimitive n (outsideRadius t)) 48
  rw [q11OutsideCoefficient_zero, zero_mul, add_zero] at h
  rw [h]

theorem hasDerivAt_q11OutsideContourPrimitive {t : ℝ} (ht : 1 / 2 ≤ t) :
    HasDerivAt q11OutsideContourPrimitive (q11ContourPotential (-(t : ℂ))) t := by
  have hR := hasDerivAt_outsideRadius ht
  have hR0 : outsideRadius t ≠ 0 := (outsideRadius_pos ht).ne'
  have hJ := outsideRadius_jacobian ht
  have hlog : HasDerivAt (fun s => outsideLogPrimitive (outsideRadius s))
      (Real.log (outsideRadius t)) t := by
    have h := (hasDerivAt_outsideLogPrimitive hR0).comp t hR
    refine h.congr_deriv ?_
    rw [mul_assoc, hJ, mul_one]
  have hpow : ∀ n, HasDerivAt (fun s => outsidePowerPrimitive n (outsideRadius s))
      (outsideParameter t ^ n) t := by
    intro n
    have h := (hasDerivAt_outsidePowerPrimitive n hR0).comp t hR
    refine h.congr_deriv ?_
    rw [mul_assoc, hJ, mul_one]
    simp [outsideParameter]
  have hsum := HasDerivAt.fun_sum (u := Finset.range 49)
    (fun n _ => (hpow n).const_mul (q11OutsideCoefficient n))
  have h := (hlog.const_mul q11ContourMass).sub hsum
  refine h.congr_deriv ?_
  rw [q11ContourPotential_neg t ht]
  rfl

theorem continuousAt_q11OutsideFormula {t : ℝ} (ht : 1 / 2 ≤ t) :
    ContinuousAt (fun s =>
      q11ContourMass * Real.log (outsideRadius s) -
        ∑ n ∈ Finset.range 49, q11OutsideCoefficient n * outsideParameter s ^ n) t := by
  have hR := (hasDerivAt_outsideRadius ht).continuousAt
  have hR0 : outsideRadius t ≠ 0 := (outsideRadius_pos ht).ne'
  have hparam : DifferentiableAt ℝ outsideParameter t :=
    ((hasDerivAt_const t (-contourScale)).div (hasDerivAt_outsideRadius ht) hR0).differentiableAt
  have hsum : ContinuousAt (fun s =>
      ∑ n ∈ Finset.range 49, q11OutsideCoefficient n * outsideParameter s ^ n) t :=
    (HasDerivAt.fun_sum (fun n _ => (hparam.hasDerivAt.pow n).const_mul
      (q11OutsideCoefficient n))).continuousAt
  exact (continuousAt_const.mul (hR.log hR0)).sub hsum

theorem continuousOn_q11ContourPotential_neg :
    ContinuousOn (fun t : ℝ => q11ContourPotential (-(t : ℂ))) (Set.Ici (1 / 2)) := by
  have hform : ContinuousOn (fun s =>
      q11ContourMass * Real.log (outsideRadius s) -
        ∑ n ∈ Finset.range 49, q11OutsideCoefficient n * outsideParameter s ^ n)
      (Set.Ici (1 / 2)) := fun t ht =>
    (continuousAt_q11OutsideFormula ht).continuousWithinAt
  apply hform.congr
  intro t ht
  exact q11ContourPotential_neg t ht

theorem integrableOn_q11ContourPotential_neg_Icc {a b : ℝ} (ha : 1 / 2 ≤ a) :
    IntegrableOn (fun t : ℝ => q11ContourPotential (-(t : ℂ))) (Set.Icc a b) volume := by
  have hcont := continuousOn_q11ContourPotential_neg.mono
    (show Set.Icc a b ⊆ Set.Ici (1 / 2) from fun _ ht => ha.trans ht.1)
  exact hcont.integrableOn_Icc

theorem integrableOn_q11ContourPotential_neg_Ico {a b : ℝ} (ha : 1 / 2 ≤ a) :
    IntegrableOn (fun t : ℝ => q11ContourPotential (-(t : ℂ))) (Set.Ico a b) volume :=
  (integrableOn_q11ContourPotential_neg_Icc ha).mono_set Set.Ico_subset_Icc_self

theorem integral_q11ContourPotential_neg {a b : ℝ}
    (ha : 1 / 2 ≤ a) (hab : a ≤ b) :
    (∫ t in a..b, q11ContourPotential (-(t : ℂ))) =
      q11OutsideContourPrimitive b - q11OutsideContourPrimitive a := by
  have ht : ∀ t ∈ Set.uIcc a b, 1 / 2 ≤ t := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    exact ha.trans ht.1
  have hcont : ContinuousOn (fun t : ℝ => q11ContourPotential (-(t : ℂ)))
      (Set.uIcc a b) := by
    have hform : ContinuousOn (fun s =>
        q11ContourMass * Real.log (outsideRadius s) -
          ∑ n ∈ Finset.range 49, q11OutsideCoefficient n * outsideParameter s ^ n)
        (Set.uIcc a b) := fun t ht' =>
      (continuousAt_q11OutsideFormula (ht t ht')).continuousWithinAt
    apply hform.congr
    intro t ht'
    exact q11ContourPotential_neg t (ht t ht')
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht' => hasDerivAt_q11OutsideContourPrimitive (ht t ht')) hcont.intervalIntegrable

theorem q11FrequencyEdge_ge_half {j : ℕ} (hj : j ≤ 4) :
    (1 / 2 : ℚ) ≤ frequencyEdge j := by
  interval_cases j <;> norm_num [frequencyEdge, frequencyEdge2Units]

theorem q11FrequencyEdgeReal_ge_half {j : ℕ} (hj : j ≤ 4) :
    (1 / 2 : ℝ) ≤ q11FrequencyEdgeReal j := by
  unfold q11FrequencyEdgeReal
  exact CA.Frequency.half_le_cast (q11FrequencyEdge_ge_half hj)

theorem q11FrequencyEdgeReal_le_succ {j : ℕ} (hj : j < 4) :
    q11FrequencyEdgeReal j ≤ q11FrequencyEdgeReal (j + 1) := by
  linarith [q11FrequencyEdgeReal_width hj]

theorem integral_q11ContourPotential_neg_frequency :
    (∫ t, q11ContourPotential (-(t : ℂ)) ∂q11FrequencyReferenceMeasure) =
      ∑ j ∈ Finset.range 4, q11IntervalDensity frequencyMassUnits 1 j *
        (q11OutsideContourPrimitive (q11FrequencyEdgeReal (j + 1)) -
          q11OutsideContourPrimitive (q11FrequencyEdgeReal j)) := by
  unfold q11FrequencyReferenceMeasure q11IntervalReferenceMeasure
  rw [integral_finsetSum_measure]
  · apply Finset.sum_congr rfl
    intro j hj
    have hj4 : j < 4 := Finset.mem_range.mp hj
    have ha : (1 / 2 : ℝ) ≤ q11FrequencyEdgeReal j :=
      q11FrequencyEdgeReal_ge_half (by omega)
    have hab : q11FrequencyEdgeReal j ≤ q11FrequencyEdgeReal (j + 1) :=
      q11FrequencyEdgeReal_le_succ hj4
    rw [integral_smul_measure,
      ENNReal.toReal_ofReal (q11IntervalDensity_nonneg frequencyMassUnits (by norm_num) j),
      integral_Ico_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hab,
      integral_q11ContourPotential_neg ha hab]
    rfl
  · intro j hj
    have hj4 : j < 4 := Finset.mem_range.mp hj
    exact (integrableOn_q11ContourPotential_neg_Ico
      (q11FrequencyEdgeReal_ge_half (by omega))).smul_measure ENNReal.ofReal_ne_top

theorem q11OutsideCoefficient_eq_fourier {n : ℕ} (hn : n < 48) :
    q11OutsideCoefficient (n + 1) =
      (1 + contourRatio ^ (n + 1)) * q11ContourFourierMoment (n + 1) / (n + 1 : ℝ) := by
  unfold q11OutsideCoefficient
  rw [q11ContourMoment_eq_fourierMoment (by omega)]
  simp [Nat.cast_add, Nat.cast_one]

def q11OutsidePrimitiveI (t : ℚ) : CA.Contour.QI :=
  CA.Contour.QI.rnd
    (CA.Contour.QI.sub
      (CA.Contour.QI.smul q11ContourMassQ
        (ActualReferenceQLogOutsideCheck.logPrimitiveI t))
      (CA.Contour.QI.sumIdx 48 (fun n =>
        CA.Contour.QI.rnd
          (CA.Contour.QI.mul (q11BComp n)
            (ActualReferenceQLogOutsideCheck.powerPrimitiveI n t)))))

theorem q11OutsidePrimitiveI_mem {t : ℚ} (ht : 1 / 2 ≤ t) :
    (q11OutsidePrimitiveI t).mem (q11OutsideContourPrimitive (t : ℝ)) := by
  have htR : (1 / 2 : ℝ) ≤ (t : ℝ) := CA.Frequency.half_le_cast ht
  rw [q11OutsideContourPrimitive_eq_sum48, ← q11ContourMassQ_eq,
    outsideLogPrimitive_eq_checker htR]
  have hsum :
      (∑ n ∈ Finset.range 48,
        q11OutsideCoefficient (n + 1) *
          outsidePowerPrimitive (n + 1) (outsideRadius (t : ℝ))) =
      ∑ n ∈ Finset.range 48,
        ((1 + contourRatio ^ (n + 1)) * q11ContourFourierMoment (n + 1) / (n + 1 : ℝ)) *
          ActualReferenceQLogOutsideCheck.powerPrimitive n (t : ℝ) := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [q11OutsideCoefficient_eq_fourier (Finset.mem_range.mp hn),
      outsidePowerPrimitive_eq_checker]
  rw [hsum]
  exact CA.Contour.QI.mem_rnd
    (CA.Contour.QI.mem_sub
      (CA.Contour.QI.mem_smul q11ContourMassQ
        (ActualReferenceQLogOutsideCheck.logPrimitiveI_mem ht))
      (CA.Contour.QI.mem_sumIdx fun n hn =>
        CA.Contour.QI.mem_rnd
          (CA.Contour.QI.mem_mul (q11BComp_mem hn)
            (ActualReferenceQLogOutsideCheck.powerPrimitiveI_mem ht n))))

def q11FrequencyContourI : CA.Contour.QI :=
  CA.Contour.QI.sumIdx 4 (fun j =>
    CA.Contour.QI.rnd
      (CA.Contour.QI.smul (q11DensityQ frequencyMassUnits 1 j)
        (CA.Contour.QI.sub
          (q11OutsidePrimitiveI (frequencyEdge (j + 1)))
          (q11OutsidePrimitiveI (frequencyEdge j)))))

theorem q11FrequencyContourI_mem : q11FrequencyContourI.mem q11Eνμ := by
  rw [q11Eνμ_eq_frequency_integral, integral_q11ContourPotential_neg_frequency]
  unfold q11FrequencyContourI
  apply CA.Contour.QI.mem_sumIdx
  intro j hj
  have hj4 : j < 4 := hj
  have h0 : (1 / 2 : ℚ) ≤ frequencyEdge j := q11FrequencyEdge_ge_half (by omega)
  have h1 : (1 / 2 : ℚ) ≤ frequencyEdge (j + 1) := q11FrequencyEdge_ge_half (by omega)
  have hsub := CA.Contour.QI.mem_sub
    (q11OutsidePrimitiveI_mem h1) (q11OutsidePrimitiveI_mem h0)
  have hsmul := CA.Contour.QI.mem_rnd
    (CA.Contour.QI.mem_smul (q11DensityQ frequencyMassUnits 1 j) hsub)
  simpa only [q11DensityQ_cast, Rat.cast_one, q11FrequencyEdgeReal] using hsmul

def q11LowerContourFrequency : IntRatio :=
  ⟨564360308, 1000000000⟩

theorem q11LowerContourFrequency_den_pos : 0 < q11LowerContourFrequency.den := by
  decide +kernel

private theorem q11FrequencyContourI_lo_check :
    decide ((564360308 / 1000000000 : ℚ) ≤ q11FrequencyContourI.lo) = true := by
  decide +kernel

theorem q11LowerContourFrequency_le :
    ratioToReal q11LowerContourFrequency ≤ q11Eνμ := by
  have hle_q : (564360308 / 1000000000 : ℚ) ≤ q11FrequencyContourI.lo :=
    of_decide_eq_true q11FrequencyContourI_lo_check
  have hle_r : ((564360308 / 1000000000 : ℚ) : ℝ) ≤ (q11FrequencyContourI.lo : ℝ) := by
    exact_mod_cast hle_q
  have hmem := q11FrequencyContourI_mem.1
  refine le_trans ?_ (le_trans hle_r hmem)
  norm_num [q11LowerContourFrequency, ratioToReal]

/-! ## 4. `lowerPinnedContour` (`q11Eκν`) and `lowerContourPinned` (`q11Eνκ`) -/

theorem q11ContourLogPolynomial_pair (a b : ℂ) (p : ℕ → ℝ)
    (hp : ∀ n, a ^ n + b ^ n = (p n : ℂ)) :
    q11ContourLogPolynomial ((starRingEnd ℂ) a) +
        q11ContourLogPolynomial ((starRingEnd ℂ) b) =
      ∑ n ∈ Finset.range 49, q11ContourMoment n * (p n / (n : ℝ)) := by
  unfold q11ContourLogPolynomial
  rw [← Finset.sum_add_distrib]
  simp_rw [← mul_add, CA.Pinned.fejerLogPolynomial_pair_re a b p hp, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _
  unfold q11ContourMoment
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem q11ContourPotential_inside (x : ℝ)
    (hx0 : 0 ≤ x) (hx2 : x ≤ 2) :
    q11ContourPotential (x : ℂ) =
      q11ContourMass * Real.log contourScale -
        q11ContourLogPolynomial ((starRingEnd ℂ) (pinnedRootPlus x)) -
        q11ContourLogPolynomial ((starRingEnd ℂ) (pinnedRootMinus x)) := by
  have hr1 := pinnedRootPlus_norm_lt_one hx0 hx2
  have hr2 := pinnedRootMinus_norm_lt_one hx0 hx2
  have h1 : ‖(starRingEnd ℂ) (pinnedRootPlus x)‖ < 1 := by
    simpa only [Complex.norm_conj] using hr1
  have h2 : ‖(starRingEnd ℂ) (pinnedRootMinus x)‖ < 1 := by
    simpa only [Complex.norm_conj] using hr2
  have hconst : IntervalIntegrable
      (fun v : ℝ => q11ContourDensity v * Real.log contourScale)
      volume 0 (2 * Real.pi) :=
    (continuous_q11ContourDensity.mul continuous_const).intervalIntegrable _ _
  have hterm1 : IntervalIntegrable
      (fun v : ℝ => q11ContourDensity v *
        Real.log ‖1 - (starRingEnd ℂ) (pinnedRootPlus x) * phase v‖)
      volume 0 (2 * Real.pi) :=
    (continuous_q11ContourDensity.mul (continuous_log_norm h1)).intervalIntegrable _ _
  have hterm2 : IntervalIntegrable
      (fun v : ℝ => q11ContourDensity v *
        Real.log ‖1 - (starRingEnd ℂ) (pinnedRootMinus x) * phase v‖)
      volume 0 (2 * Real.pi) :=
    (continuous_q11ContourDensity.mul (continuous_log_norm h2)).intervalIntegrable _ _
  have hdist (v : ℝ) :
      Real.log ‖(x : ℂ) - Li2Lean.p0EllipsePoint 1 v‖ =
        Real.log contourScale +
          Real.log ‖1 - (starRingEnd ℂ) (pinnedRootPlus x) * phase v‖ +
          Real.log ‖1 - (starRingEnd ℂ) (pinnedRootMinus x) * phase v‖ := by
    have hfact := ellipse_difference_pinned_roots x v
    have hnorm :
        ‖(x : ℂ) - Li2Lean.p0EllipsePoint 1 v‖ =
          contourScale *
            ‖1 - pinnedRootPlus x / phase v‖ *
            ‖1 - pinnedRootMinus x / phase v‖ := by
      rw [show (x : ℂ) - Li2Lean.p0EllipsePoint 1 v =
        -(Li2Lean.p0EllipsePoint 1 v - (x : ℂ)) by ring,
        norm_neg, hfact, norm_mul, norm_mul, norm_mul,
        pinned_alpha_eq_contourScale,
        Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by norm_num [contourScale]),
        norm_phase]
      ring
    have hn1 : ‖1 - pinnedRootPlus x / phase v‖ ≠ 0 := by
      apply norm_ne_zero_iff.mpr
      intro hzero
      have h' : phase v = pinnedRootPlus x := by
        have hdiv : pinnedRootPlus x / phase v = 1 :=
          (sub_eq_zero.mp hzero).symm
        have := (div_eq_iff (phase_ne_zero v)).mp hdiv
        simpa using this.symm
      have := congrArg norm h'
      rw [norm_phase] at this
      linarith [hr1]
    have hn2 : ‖1 - pinnedRootMinus x / phase v‖ ≠ 0 := by
      apply norm_ne_zero_iff.mpr
      intro hzero
      have h' : phase v = pinnedRootMinus x := by
        have hdiv : pinnedRootMinus x / phase v = 1 :=
          (sub_eq_zero.mp hzero).symm
        have := (div_eq_iff (phase_ne_zero v)).mp hdiv
        simpa using this.symm
      have := congrArg norm h'
      rw [norm_phase] at this
      linarith [hr2]
    rw [hnorm, Real.log_mul
      (mul_ne_zero (ne_of_gt (by norm_num [contourScale])) hn1) hn2,
      Real.log_mul (ne_of_gt (by norm_num [contourScale])) hn1,
      log_norm_inverse_phase_complex, log_norm_inverse_phase_complex]
  unfold q11ContourPotential q11ContourIntegral
  simp_rw [hdist, mul_add]
  rw [intervalIntegral.integral_add (hconst.add hterm1) hterm2,
    intervalIntegral.integral_add hconst hterm1,
    intervalIntegral.integral_mul_const,
    q11IntegralContourDensity,
    ← q11ContourMass_eq_sum,
    q11_integral_contourDensity_log_norm h1,
    q11_integral_contourDensity_log_norm h2]
  have hp : 2 * Real.pi ≠ 0 := by positivity
  field_simp
  ring

theorem q11ContourPotential_eq_poly (x : ℝ)
    (hxlo : 1 / 4 ≤ x) (hxhi : x ≤ 5 / 4) :
    q11ContourPotential (x : ℂ) =
      q11ContourMass * Real.log contourScale -
        ∑ n ∈ Finset.range 49, q11ContourMoment n *
          (Polynomial.aeval x (pairPolyQ n) / (n : ℝ)) := by
  rw [q11ContourPotential_inside x (by linarith) (by linarith), sub_sub,
    q11ContourLogPolynomial_pair _ _ _ (row1PairPowerSum_root_identity x)]
  simp_rw [aeval_pairPolyQ]

def q11PinnedMassQ : ℚ :=
  (1647154788848 : ℚ) / (3000000000000 : ℚ)

theorem integral_q11Pinned_const (r : ℝ) :
    (∫ _ : ℝ, r ∂q11PinnedReferenceMeasure) = (q11PinnedMassQ : ℝ) * r := by
  rw [integral_const, Measure.real, q11PinnedReferenceMeasure_mass,
    ENNReal.toReal_ofReal (by positivity), pinned_mass_sum]
  unfold q11PinnedMassQ
  norm_num [denominator, smul_eq_mul]

def q11MonomialMomentQ (k : ℕ) : ℚ :=
  ∑ j ∈ Finset.range 8,
    q11DensityQ pinnedMassUnits (1 / 8) j *
      ((pinnedEdge (j + 1)) ^ (k + 1) - (pinnedEdge j) ^ (k + 1)) / (k + 1 : ℚ)

theorem integral_q11Pinned_monomial (k : ℕ) :
    (∫ x : ℝ, x ^ k ∂q11PinnedReferenceMeasure) = (q11MonomialMomentQ k : ℝ) := by
  have hcont : Continuous (fun x : ℝ => x ^ k) := continuous_id.pow k
  rw [q11PinnedReferenceMeasure,
    q11IntervalReferenceMeasure_integral_of_continuous hcont
      q11PinnedEdgeReal (fun j => q11PinnedEdgeReal (j + 1)) 8 pinnedMassUnits
      (show 0 < (1 / 8 : ℝ) by norm_num)]
  unfold q11MonomialMomentQ
  push_cast
  apply Finset.sum_congr rfl
  intro j hj
  have hj8 : j < 8 := Finset.mem_range.mp hj
  have hle : q11PinnedEdgeReal j ≤ q11PinnedEdgeReal (j + 1) := by
    linarith [q11PinnedEdgeReal_width hj8]
  have hdens : (q11DensityQ pinnedMassUnits (1 / 8) j : ℝ) =
      q11IntervalDensity pinnedMassUnits (1 / 8 : ℝ) j := by
    simpa [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
      q11DensityQ_cast pinnedMassUnits (1 / 8) j
  rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle,
    integral_pow, hdens]
  simp only [q11PinnedEdgeReal]
  ring

theorem integral_q11Pinned_evalL (p : List ℚ) :
    (∫ x : ℝ, PinnedListBasic.evalL x p ∂q11PinnedReferenceMeasure) =
      ∑ k ∈ Finset.range p.length,
        (p.getD k 0 : ℝ) * (q11MonomialMomentQ k : ℝ) := by
  simp_rw [PinnedListBasic.evalL_sum]
  rw [integral_finsetSum]
  · simp_rw [integral_const_mul, integral_q11Pinned_monomial]
  · intro k _
    exact q11IntervalReferenceMeasure_integrable_of_continuous
      (continuous_const.mul (continuous_id.pow k))
      q11PinnedEdgeReal (fun j => q11PinnedEdgeReal (j + 1)) 8 pinnedMassUnits (1 / 8 : ℝ)

def q11PinnedPowerIntegralQ (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (pTable.getD n []).length,
    (pTable.getD n []).getD k 0 * q11MonomialMomentQ k

theorem integral_q11Pinned_pairPolyQ {n : ℕ} (hn : n < 49) :
    (∫ x : ℝ, Polynomial.aeval x (pairPolyQ n) ∂q11PinnedReferenceMeasure) =
      (q11PinnedPowerIntegralQ n : ℝ) := by
  simp_rw [← evalL_pTable n hn]
  rw [integral_q11Pinned_evalL]
  unfold q11PinnedPowerIntegralQ
  push_cast
  rfl

def q11PinnedContourFinite : ℝ :=
  (q11PinnedMassQ : ℝ) * q11ContourMass * Real.log contourScale -
    ∑ n ∈ Finset.range 49, q11ContourMoment n *
      ((q11PinnedPowerIntegralQ n : ℝ) / (n : ℝ))

theorem q11PinnedContourFinite_eq_sum48 :
    q11PinnedContourFinite =
      ((q11PinnedMassQ * q11ContourMassQ : ℚ) : ℝ) * Real.log contourScale -
        ∑ n ∈ Finset.range 48,
          ((q11PinnedPowerIntegralQ (n + 1) / (n + 1 : ℚ) : ℚ) : ℝ) *
            q11ContourFourierMoment (n + 1) := by
  unfold q11PinnedContourFinite
  have h := Finset.sum_range_succ'
    (fun n => q11ContourMoment n * ((q11PinnedPowerIntegralQ n : ℝ) / (n : ℝ))) 48
  simp only [Nat.cast_zero, div_zero, mul_zero, add_zero] at h
  rw [h, ← q11ContourMassQ_eq]
  push_cast
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  have hm := q11ContourMoment_eq_fourierMoment
    (n := n + 1) (by have := Finset.mem_range.mp hn; omega)
  rw [hm]
  ring

theorem q11Eκν_eq_finite :
    q11Eκν = q11PinnedContourFinite := by
  unfold q11Eκν
  let E : ℝ → ℝ := fun x => q11ContourMass * Real.log contourScale -
    ∑ n ∈ Finset.range 49, q11ContourMoment n *
      (Polynomial.aeval x (pairPolyQ n) / (n : ℝ))
  have hsum : Continuous (fun x : ℝ =>
      ∑ n ∈ Finset.range 49, q11ContourMoment n *
        (Polynomial.aeval x (pairPolyQ n) / (n : ℝ))) := by
    apply continuous_finsetSum
    intro n _
    exact ((pairPolyQ n).continuous_aeval.div_const (n : ℝ)).const_mul _
  have hE : (fun x : ℝ => q11ContourPotential (x : ℂ)) =ᵐ[q11PinnedReferenceMeasure] E := by
    filter_upwards [q11PinnedReferenceMeasure_ae_interval] with x hx
    exact q11ContourPotential_eq_poly x hx.1 hx.2
  rw [integral_congr_ae hE]
  dsimp [E]
  have hconstI : Integrable (fun _ : ℝ => q11ContourMass * Real.log contourScale)
      q11PinnedReferenceMeasure :=
    q11IntervalReferenceMeasure_integrable_of_continuous continuous_const
      q11PinnedEdgeReal (fun j => q11PinnedEdgeReal (j + 1)) 8 pinnedMassUnits (1 / 8 : ℝ)
  have hsumI : Integrable (fun x : ℝ =>
      ∑ n ∈ Finset.range 49, q11ContourMoment n *
        (Polynomial.aeval x (pairPolyQ n) / (n : ℝ))) q11PinnedReferenceMeasure :=
    q11IntervalReferenceMeasure_integrable_of_continuous hsum
      q11PinnedEdgeReal (fun j => q11PinnedEdgeReal (j + 1)) 8 pinnedMassUnits (1 / 8 : ℝ)
  rw [integral_sub hconstI hsumI,
    integral_q11Pinned_const,
    integral_finsetSum]
  · have hterms :
        (∑ n ∈ Finset.range 49,
          ∫ x : ℝ, q11ContourMoment n *
            (Polynomial.aeval x (pairPolyQ n) / (n : ℝ)) ∂q11PinnedReferenceMeasure) =
        ∑ n ∈ Finset.range 49,
          q11ContourMoment n * ((q11PinnedPowerIntegralQ n : ℝ) / (n : ℝ)) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [integral_const_mul, integral_div,
        integral_q11Pinned_pairPolyQ (Finset.mem_range.mp hn)]
    rw [hterms]
    unfold q11PinnedContourFinite
    ring
  · intro n _
    exact q11IntervalReferenceMeasure_integrable_of_continuous
      (((pairPolyQ n).continuous_aeval.div_const (n : ℝ)).const_mul _)
      q11PinnedEdgeReal (fun j => q11PinnedEdgeReal (j + 1)) 8 pinnedMassUnits (1 / 8 : ℝ)

def q11PinnedContourI : CA.Contour.QI :=
  CA.Contour.QI.sub
    (CA.Contour.QI.smul (q11PinnedMassQ * q11ContourMassQ) logScaleI)
    (CA.Contour.QI.sumIdx 48 (fun n =>
      CA.Contour.QI.rnd
        (CA.Contour.QI.smul
          (q11PinnedPowerIntegralQ (n + 1) / (n + 1 : ℚ))
          (q11MomI (n + 1)))))

theorem q11PinnedContourI_mem : q11PinnedContourI.mem q11Eκν := by
  rw [q11Eκν_eq_finite, q11PinnedContourFinite_eq_sum48]
  unfold q11PinnedContourI
  refine CA.Contour.QI.mem_sub
    (CA.Contour.QI.mem_smul (q11PinnedMassQ * q11ContourMassQ) logScaleI_mem)
    (CA.Contour.QI.mem_sumIdx fun n hn => ?_)
  exact CA.Contour.QI.mem_rnd
    (CA.Contour.QI.mem_smul
      (q11PinnedPowerIntegralQ (n + 1) / (n + 1 : ℚ))
      (q11MomI_mem (k := n + 1) (by omega)))

def q11LowerPinnedContour : IntRatio :=
  ⟨85664740, 1000000000⟩

def q11LowerContourPinned : IntRatio :=
  ⟨85664740, 1000000000⟩

theorem q11LowerPinnedContour_den_pos : 0 < q11LowerPinnedContour.den := by
  decide +kernel

theorem q11LowerContourPinned_den_pos : 0 < q11LowerContourPinned.den := by
  decide +kernel

private theorem q11PinnedContourI_lo_check :
    decide ((85664740 / 1000000000 : ℚ) ≤ q11PinnedContourI.lo) = true := by
  decide +kernel

theorem q11LowerPinnedContour_le :
    ratioToReal q11LowerPinnedContour ≤ q11Eκν := by
  have hle_q : (85664740 / 1000000000 : ℚ) ≤ q11PinnedContourI.lo :=
    of_decide_eq_true q11PinnedContourI_lo_check
  have hle_r : ((85664740 / 1000000000 : ℚ) : ℝ) ≤ (q11PinnedContourI.lo : ℝ) := by
    exact_mod_cast hle_q
  have hmem := q11PinnedContourI_mem.1
  refine le_trans ?_ (le_trans hle_r hmem)
  norm_num [q11LowerPinnedContour, ratioToReal]

theorem q11LowerContourPinned_le :
    ratioToReal q11LowerContourPinned ≤ q11Eνκ := by
  rw [q11Eνκ_eq_Eκν]
  exact q11LowerPinnedContour_le

/-! ## 5. Full `Q11QLogEnvelopeInputs` assembly and `q11QLogLower` -/

def q11TotalLower : IntRatio :=
  ⟨-635535679, 1000000000⟩

theorem q11TotalLower_den_pos : 0 < q11TotalLower.den := by
  decide +kernel

theorem q11TotalLower_le_terms :
    ratioToReal q11TotalLower ≤
      ratioToReal q11LowerPinnedPinned + ratioToReal q11LowerPinnedContour +
        ratioToReal q11LowerContourPinned + ratioToReal lowerContourContour +
        ratioToReal q11LowerFrequencyFrequency + ratioToReal q11LowerPinnedFrequency +
        ratioToReal q11LowerContourFrequency := by
  have hcc := lowerContourContour_ge_decimal
  have hsum : ratioToReal q11TotalLower ≤
      ratioToReal q11LowerPinnedPinned + ratioToReal q11LowerPinnedContour +
        ratioToReal q11LowerContourPinned + (-193059871 / 1000000000 : ℝ) +
        ratioToReal q11LowerFrequencyFrequency + ratioToReal q11LowerPinnedFrequency +
        ratioToReal q11LowerContourFrequency := by
    norm_num [ratioToReal, q11TotalLower, q11LowerPinnedPinned,
      q11LowerPinnedContour, q11LowerContourPinned,
      q11LowerFrequencyFrequency, q11LowerPinnedFrequency, q11LowerContourFrequency]
  linarith

theorem q11TotalLower_margin_check :
    ratioLtBool qLogLower q11TotalLower = true := by
  decide +kernel

/-- Complete, sorry-free `Q11QLogEnvelopeInputs` witness for `q = 11`. -/
def q11_qlog_envelope_inputs_actual : Q11QLogEnvelopeInputs where
  pinnedSelfIntegrable := q11PinnedComplexPotential_pinned_integrable
  pinnedFrequencyIntegrable :=
    Li2Lean.P0.Q11Data.q11ReflectedFrequencyPotential_pinned_integrable
  contourFrequencyIntegrable := q11ReflectedFrequencyPotential_contour_integrable
  lowerPinnedPinned := q11LowerPinnedPinned
  lowerPinnedContour := q11LowerPinnedContour
  lowerContourPinned := q11LowerContourPinned
  lowerContourContour := lowerContourContour
  lowerPinnedFrequency := q11LowerPinnedFrequency
  lowerContourFrequency := q11LowerContourFrequency
  lowerFrequencyFrequency := q11LowerFrequencyFrequency
  totalLower := q11TotalLower
  pinnedPinned_den_pos := q11LowerPinnedPinned_den_pos
  pinnedContour_den_pos := q11LowerPinnedContour_den_pos
  contourPinned_den_pos := q11LowerContourPinned_den_pos
  contourContour_den_pos := lowerContourContour_den_pos
  pinnedFrequency_den_pos := q11LowerPinnedFrequency_den_pos
  contourFrequency_den_pos := q11LowerContourFrequency_den_pos
  frequencyFrequency_den_pos := q11LowerFrequencyFrequency_den_pos
  total_den_pos := q11TotalLower_den_pos
  pinnedPinned_le := q11LowerPinnedPinned_le
  pinnedContour_le := q11LowerPinnedContour_le
  contourPinned_le := q11LowerContourPinned_le
  contourContour_le := q11Eνν_lower
  pinnedFrequency_le := q11LowerPinnedFrequency_le
  contourFrequency_le := q11LowerContourFrequency_le
  frequencyFrequency_le := q11LowerFrequencyFrequency_le
  total_le_terms := q11TotalLower_le_terms
  margin_check := q11TotalLower_margin_check

/-- Unconditional proof of `q11QLogLower` (`-635537 / 1000000 < q11ActualReference.qLog`). -/
theorem q11ActualReference_qLog_lower_proved : q11QLogLower :=
  q11ActualReference_qLog_lower_of_envelope q11_qlog_envelope_inputs_actual

end
end Li2Lean.P0.Q11Data

#print axioms Li2Lean.P0.Q11Data.q11LowerContourFrequency_le
#print axioms Li2Lean.P0.Q11Data.q11LowerPinnedContour_le
#print axioms Li2Lean.P0.Q11Data.q11LowerContourPinned_le
#print axioms Li2Lean.P0.Q11Data.q11ActualReference_qLog_lower_proved
