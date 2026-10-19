/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.Q11Certificate
import Li2Lean.P0.ConfigContourMeasure
import Li2Lean.P0.ConfigSegment

/-!
The literal q = 11 endpoint reference objects from paper v13.

Source locks:
* `p0-analytic.tex:17-27` fixes the ellipse, interval supports and fields.
* `p0-reference-data.tex:29-40` gives the q = 11 edge and mass lists.
* `certificate-algorithm.tex:29-42, 50-75` specifies uniform interval rows
  and the 64-node, degree-48 Fejer contour mixture.
* `p0-analytic.tex:227-255` defines the reference fields, qLog and dual
  first-variation field.

This file defines the actual q = 11 measures, potentials and fields. Their
mass, admissibility, continuum bounds and energy enclosures are separate
theorems; no such analytic claim is encoded as a field here.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Li2Lean.P0.Q11Data

noncomputable section

open ConfigContourReference

def q11MassUnitReal (units : List ℕ) (j : ℕ) : ℝ :=
  (units.getD j 0 : ℝ) / (denominator : ℝ)

def q11IntervalDensity (units : List ℕ) (width : ℝ) (j : ℕ) : ℝ :=
  q11MassUnitReal units j / width

def q11IntervalReferenceMeasure (left right : ℕ → ℝ) (count : ℕ)
    (units : List ℕ) (width : ℝ) : Measure ℝ :=
  ∑ j ∈ Finset.range count,
    ENNReal.ofReal (q11IntervalDensity units width j) •
      volume.restrict (Ico (left j) (right j))

def q11PinnedEdgeReal (j : ℕ) : ℝ :=
  (pinnedEdge j : ℝ)

def q11FrequencyEdgeReal (j : ℕ) : ℝ :=
  (frequencyEdge j : ℝ)

def q11PinnedReferenceMeasure : Measure ℝ :=
  q11IntervalReferenceMeasure q11PinnedEdgeReal
    (fun j => q11PinnedEdgeReal (j + 1)) 8
    pinnedMassUnits (1 / 8 : ℝ)

def q11FrequencyReferenceMeasure : Measure ℝ :=
  q11IntervalReferenceMeasure q11FrequencyEdgeReal
    (fun j => q11FrequencyEdgeReal (j + 1)) 4
    frequencyMassUnits 1

theorem q11PinnedEdgeReal_width {j : ℕ} (hj : j < 8) :
    q11PinnedEdgeReal (j + 1) - q11PinnedEdgeReal j = (1 / 8 : ℝ) := by
  interval_cases j <;>
    norm_num [q11PinnedEdgeReal, pinnedEdge, pinnedEdge32Units]

theorem q11FrequencyEdgeReal_width {j : ℕ} (hj : j < 4) :
    q11FrequencyEdgeReal (j + 1) - q11FrequencyEdgeReal j = (1 : ℝ) := by
  interval_cases j <;>
    norm_num [q11FrequencyEdgeReal, frequencyEdge, frequencyEdge2Units]

theorem q11_sum_getD_cast (l : List ℕ) :
    ∑ j ∈ Finset.range l.length, ((l.getD j 0 : ℕ) : ℝ) = (l.sum : ℝ) := by
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [List.length_cons, Finset.sum_range_succ', List.sum_cons]
      simp only [List.getD_cons_succ, List.getD_cons_zero]
      rw [ih]
      push_cast
      ring

/-- The mass of an equal-width interval reference measure is exactly the sum
of its printed rational masses. -/
theorem q11IntervalReferenceMeasure_univ
    {left right : ℕ → ℝ} {count : ℕ} {units : List ℕ} {width : ℝ}
    (hleft : ∀ j ∈ Finset.range count, left j ≤ right j)
    (hwidth : ∀ j ∈ Finset.range count, right j - left j = width)
    (hwidth_pos : 0 < width) (hcount : count = units.length) :
    q11IntervalReferenceMeasure left right count units width Set.univ =
      ENNReal.ofReal ((units.sum : ℝ) / (denominator : ℝ)) := by
  unfold q11IntervalReferenceMeasure
  rw [Measure.finsetSum_apply]
  simp only [Measure.smul_apply, Measure.restrict_apply_univ,
    Real.volume_Ico, smul_eq_mul]
  have hterms : ∀ j ∈ Finset.range count,
      q11IntervalDensity units width j * (right j - left j) =
        q11MassUnitReal units j := by
    intro j hj
    rw [hwidth j hj]
    unfold q11IntervalDensity
    field_simp [ne_of_gt hwidth_pos,
      show (denominator : ℝ) ≠ 0 by norm_num [denominator]]
  have hsum :
      (∑ j ∈ Finset.range count,
        q11IntervalDensity units width j * (right j - left j)) =
        (units.sum : ℝ) / (denominator : ℝ) := by
    calc
      _ = ∑ j ∈ Finset.range count, q11MassUnitReal units j := by
        apply Finset.sum_congr rfl
        intro j hj
        exact hterms j hj
      _ = ∑ j ∈ Finset.range units.length, q11MassUnitReal units j := by
        rw [hcount]
      _ = (∑ j ∈ Finset.range units.length,
          ((units.getD j 0 : ℕ) : ℝ)) / (denominator : ℝ) := by
        simp only [q11MassUnitReal, ← Finset.sum_div]
      _ = (units.sum : ℝ) / (denominator : ℝ) := by
        rw [q11_sum_getD_cast]
  have hrewrite :
      (∑ j ∈ Finset.range count,
        ENNReal.ofReal (q11IntervalDensity units width j) *
          ENNReal.ofReal (right j - left j)) =
      ∑ j ∈ Finset.range count,
        ENNReal.ofReal (q11IntervalDensity units width j *
          (right j - left j)) := by
    apply Finset.sum_congr rfl
    intro j hj
    change ENNReal.ofReal
        (((units.getD j 0 : ℕ) : ℝ) / (denominator : ℝ) / width) *
          ENNReal.ofReal (right j - left j) =
      ENNReal.ofReal
        ((((units.getD j 0 : ℕ) : ℝ) / (denominator : ℝ) / width) *
          (right j - left j))
    rw [← ENNReal.ofReal_mul
      (div_nonneg (div_nonneg (by positivity) (by positivity)) hwidth_pos.le)]
  rw [hrewrite, ← ENNReal.ofReal_sum_of_nonneg]
  · exact congrArg ENNReal.ofReal hsum
  · intro j hj
    apply mul_nonneg
    · exact div_nonneg (div_nonneg (by positivity) (by positivity)) hwidth_pos.le
    · exact sub_nonneg.mpr (hleft j hj)

theorem q11PinnedReferenceMeasure_mass :
    q11PinnedReferenceMeasure Set.univ =
      ENNReal.ofReal ((pinnedMassUnits.sum : ℝ) / (denominator : ℝ)) := by
  unfold q11PinnedReferenceMeasure
  apply q11IntervalReferenceMeasure_univ
  · intro j hj
    have hw := q11PinnedEdgeReal_width (Finset.mem_range.mp hj)
    linarith
  · intro j hj
    exact q11PinnedEdgeReal_width (Finset.mem_range.mp hj)
  · norm_num
  · simpa using pinned_masses_length.symm

theorem q11FrequencyReferenceMeasure_mass :
    q11FrequencyReferenceMeasure Set.univ =
      ENNReal.ofReal ((frequencyMassUnits.sum : ℝ) / (denominator : ℝ)) := by
  unfold q11FrequencyReferenceMeasure
  apply q11IntervalReferenceMeasure_univ
  · intro j hj
    have hw := q11FrequencyEdgeReal_width (Finset.mem_range.mp hj)
    linarith
  · intro j hj
    exact q11FrequencyEdgeReal_width (Finset.mem_range.mp hj)
  · norm_num
  · simpa using frequency_masses_length.symm

theorem q11FrequencyReferenceMeasure_univ :
    q11FrequencyReferenceMeasure Set.univ = 1 := by
  rw [q11FrequencyReferenceMeasure_mass, frequency_mass_sum]
  norm_num [denominator]

def q11ContourWeight (j : Fin contourNodeCount) : ℝ :=
  (contourMassUnit j.val : ℝ) / (denominator : ℝ)

def q11ContourDensity (u : ℝ) : ℝ :=
  ∑ j : Fin contourNodeCount,
    q11ContourWeight j * fejer48 (u - contourAngle j)

def q11ContourIntegral (f : ℂ → ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ * ∫ u in (0 : ℝ)..(2 * Real.pi),
    q11ContourDensity u * f (Li2Lean.p0EllipsePoint 1 u)

def q11ContourParamMeasure : Measure ℝ :=
  ENNReal.ofReal (2 * Real.pi)⁻¹ •
    (volume.restrict (Ioc 0 (2 * Real.pi))).withDensity
      (fun u => ENNReal.ofReal (q11ContourDensity u))

def q11ContourReferenceMeasure : Measure ℂ :=
  q11ContourParamMeasure.map (Li2Lean.p0EllipsePoint 1)

def q11EtaReferenceMeasure : Measure ℂ :=
  q11PinnedReferenceMeasure.map Complex.ofReal + q11ContourReferenceMeasure

theorem q11ContourWeight_nonneg (j : Fin contourNodeCount) :
    0 ≤ q11ContourWeight j := by
  unfold q11ContourWeight
  positivity

theorem q11ContourDensity_nonneg (u : ℝ) : 0 ≤ q11ContourDensity u := by
  unfold q11ContourDensity
  apply Finset.sum_nonneg
  intro j hj
  exact mul_nonneg (q11ContourWeight_nonneg j) (fejer48_nonneg _)

theorem q11ContourWeight_reverse (j : Fin contourNodeCount) :
    q11ContourWeight (reverseIndex j) = q11ContourWeight j := by
  have hmass : contourMassUnit (reverseIndex j).val = contourMassUnit j.val := by
    simpa [reverseIndex, contourNodeCount] using
      (contour_massUnit_reflection j.val j.isLt).symm
  unfold q11ContourWeight
  rw [hmass]

theorem q11ContourDensity_reflect (u : ℝ) :
    q11ContourDensity (2 * Real.pi - u) = q11ContourDensity u := by
  change (∑ j : Fin 64,
      ((contourMassUnit j.val : ℝ) / (denominator : ℝ)) *
        fejer48 (2 * Real.pi - u - contourAngle j)) =
    ∑ j : Fin 64, ((contourMassUnit j.val : ℝ) / (denominator : ℝ)) *
      fejer48 (u - contourAngle j)
  rw [← Equiv.sum_comp reverseIndex
    (fun j => ((contourMassUnit j.val : ℝ) / (denominator : ℝ)) * fejer48
      (2 * Real.pi - u - contourAngle j))]
  apply Finset.sum_congr rfl
  intro j hj
  have hmass : contourMassUnit (reverseIndex j).val = contourMassUnit j.val := by
    exact (contour_massUnit_reflection j.val j.isLt).symm
  rw [hmass, contourAngle_reverse]
  congr 1
  rw [show 2 * Real.pi - u - (2 * Real.pi - contourAngle j) =
      -(u - contourAngle j) by ring, fejer48_neg]

theorem continuous_q11ContourDensity : Continuous q11ContourDensity := by
  unfold q11ContourDensity
  exact continuous_finsetSum _ fun j _ =>
    continuous_const.mul
      (ConfigContourMeasure.continuous_fejer48.comp
        (continuous_id.sub continuous_const))

theorem q11ContourWeight_sum :
    (∑ j : Fin contourNodeCount, q11ContourWeight j) =
      (2 * contourPairMassUnits.sum : ℝ) / (denominator : ℝ) := by
  have hsum :
      (∑ j : Fin contourNodeCount, (contourMassUnit j.val : ℝ)) =
        (2 * contourPairMassUnits.sum : ℝ) := by
    have hn :
        (∑ j : Fin contourNodeCount, contourMassUnit j.val) =
          2 * contourPairMassUnits.sum := by
      decide +kernel
    exact_mod_cast hn
  unfold q11ContourWeight
  rw [← Finset.sum_div, hsum]

def q11ContourMass : ℝ :=
  (2 * contourPairMassUnits.sum : ℝ) / (denominator : ℝ)

theorem q11ContourMass_eq_sum :
    q11ContourMass = ∑ j : Fin contourNodeCount, q11ContourWeight j := by
  unfold q11ContourMass
  rw [q11ContourWeight_sum]

theorem q11IntegralContourDensity :
    (∫ u in (0 : ℝ)..(2 * Real.pi), q11ContourDensity u) =
      (2 * Real.pi) * ∑ j : Fin contourNodeCount, q11ContourWeight j := by
  unfold q11ContourDensity
  rw [intervalIntegral.integral_finsetSum]
  · simp_rw [intervalIntegral.integral_const_mul,
      ConfigFejerMass.integral_fejer48]
    rw [← Finset.sum_mul]
    ring
  · intro j hj
    apply Continuous.intervalIntegrable
    exact continuous_const.mul
      (ConfigContourMeasure.continuous_fejer48.comp
        (continuous_id.sub continuous_const))

theorem q11ContourIntegral_one :
    q11ContourIntegral (fun _ => 1) =
      (2 * contourPairMassUnits.sum : ℝ) / (denominator : ℝ) := by
  unfold q11ContourIntegral
  simp only [mul_one]
  rw [q11IntegralContourDensity, q11ContourWeight_sum]
  have hp : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  field_simp [hp]

theorem measurable_q11ContourDensityENN :
    Measurable (fun u => ENNReal.ofReal (q11ContourDensity u)) :=
  ENNReal.measurable_ofReal.comp continuous_q11ContourDensity.measurable

theorem q11Integral_contourParamMeasure (g : ℝ → ℝ) :
    ∫ u, g u ∂q11ContourParamMeasure =
      (2 * Real.pi)⁻¹ * ∫ u in (0 : ℝ)..(2 * Real.pi),
        q11ContourDensity u * g u := by
  have h2pi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  rw [q11ContourParamMeasure, integral_smul_measure,
    integral_withDensity_eq_integral_toReal_smul measurable_q11ContourDensityENN
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top),
    intervalIntegral.integral_of_le h2pi,
    ENNReal.toReal_ofReal (inv_nonneg.mpr h2pi)]
  simp only [smul_eq_mul, ENNReal.toReal_ofReal (q11ContourDensity_nonneg _)]

theorem q11ContourParamMeasure_univ :
    q11ContourParamMeasure Set.univ =
      ENNReal.ofReal (q11ContourIntegral (fun _ => 1)) := by
  have h2pi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hInt : IntegrableOn q11ContourDensity (Ioc 0 (2 * Real.pi)) :=
    continuous_q11ContourDensity.integrableOn_Ioc
  have hlin := ofReal_integral_eq_lintegral_ofReal hInt
    (Filter.Eventually.of_forall fun u => q11ContourDensity_nonneg u)
  rw [q11ContourParamMeasure, Measure.smul_apply,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← hlin, smul_eq_mul, ← ENNReal.ofReal_mul (inv_nonneg.mpr h2pi)]
  congr 1
  unfold q11ContourIntegral
  rw [intervalIntegral.integral_of_le h2pi]
  simp only [mul_one]

theorem q11ContourReferenceMeasure_univ :
    q11ContourReferenceMeasure Set.univ =
      ENNReal.ofReal ((2 * contourPairMassUnits.sum : ℝ) /
        (denominator : ℝ)) := by
  rw [q11ContourReferenceMeasure,
    Measure.map_apply ConfigContourMeasure.continuous_ellipse.measurable
      MeasurableSet.univ, preimage_univ, q11ContourParamMeasure_univ,
    q11ContourIntegral_one]

instance q11ContourReferenceMeasure_isFinite :
    IsFiniteMeasure q11ContourReferenceMeasure :=
  ⟨by rw [q11ContourReferenceMeasure_univ]; exact ENNReal.ofReal_lt_top⟩

theorem q11ContourReferenceMeasure_singleton (z : ℂ) :
    q11ContourReferenceMeasure {z} = 0 := by
  have hmeas : MeasurableSet (Li2Lean.p0EllipsePoint 1 ⁻¹' {z}) :=
    ConfigContourMeasure.continuous_ellipse.measurable (measurableSet_singleton z)
  rw [q11ContourReferenceMeasure,
    Measure.map_apply ConfigContourMeasure.continuous_ellipse.measurable
      (measurableSet_singleton z), q11ContourParamMeasure,
    Measure.smul_apply, withDensity_apply _ hmeas,
    Measure.restrict_restrict hmeas]
  have hsub : (Li2Lean.p0EllipsePoint 1 ⁻¹' {z} ∩ Ioc 0 (2 * Real.pi)).Subsingleton := by
    intro u hu v hv
    exact ConfigContourMeasure.ellipse_injOn hu.2 hv.2 (by rw [hu.1, hv.1])
  rw [setLIntegral_measure_zero _ _ (hsub.measure_zero volume), smul_zero]

theorem q11EtaReferenceMeasure_univ : q11EtaReferenceMeasure Set.univ = 1 := by
  unfold q11EtaReferenceMeasure
  rw [Measure.add_apply _ _ Set.univ,
    Measure.map_apply Complex.continuous_ofReal.measurable MeasurableSet.univ]
  simp only [Set.preimage_univ]
  rw [q11PinnedReferenceMeasure_mass, q11ContourReferenceMeasure_univ]
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  have hsum : (pinnedMassUnits.sum : ℝ) +
      2 * (contourPairMassUnits.sum : ℝ) = (denominator : ℝ) := by
    exact_mod_cast eta_mass_sum
  rw [← add_div, hsum]
  norm_num [denominator]

def q11PinnedComplexPotential (z : ℂ) : ℝ :=
  ∫ x, Real.log ‖z - (x : ℂ)‖ ∂q11PinnedReferenceMeasure

def q11FrequencyPotential (t : ℝ) : ℝ :=
  ∫ x, Real.log |t - x| ∂q11FrequencyReferenceMeasure

def q11FrequencyComplexPotential (z : ℂ) : ℝ :=
  ∫ x, Real.log ‖z - (x : ℂ)‖ ∂q11FrequencyReferenceMeasure

def q11ContourPotential (z : ℂ) : ℝ :=
  q11ContourIntegral (fun w => Real.log ‖z - w‖)

def q11EtaReferenceIntegral (f : ℂ → ℝ) : ℝ :=
  (∫ x, f (x : ℂ) ∂q11PinnedReferenceMeasure) + q11ContourIntegral f

def q11EtaReferencePotential (z : ℂ) : ℝ :=
  q11PinnedComplexPotential z + q11ContourPotential z

def q11ReflectedFrequencyPotential (z : ℂ) : ℝ :=
  ∫ t, Real.log ‖z + (t : ℂ)‖ ∂q11FrequencyReferenceMeasure

def q11QetaEta : ℝ := q11EtaReferenceIntegral q11EtaReferencePotential

def q11QmuMu : ℝ :=
  ∫ t, q11FrequencyPotential t ∂q11FrequencyReferenceMeasure

def q11QetaMu : ℝ := q11EtaReferenceIntegral q11ReflectedFrequencyPotential

def q11ActualReference : Config.DualReferencePotentials where
  Leta := q11EtaReferencePotential
  Lmu := q11FrequencyPotential
  LmuNegative := q11ReflectedFrequencyPotential
  QetaEta := q11QetaEta
  QmuMu := q11QmuMu
  QetaMu := q11QetaMu
  qLog := q11QetaEta + q11QmuMu + q11QetaMu
  qLog_eq := rfl

def q11Lambda : ℝ := Real.log (11 / 2 : ℝ)

def q11Phi (z : ℂ) : ℝ := Config.phi z + q11Lambda * z.re

def q11Psi (t : ℝ) : ℝ := Config.psi t - q11Lambda * t

def q11Weta (z : ℂ) : ℝ :=
  Config.A0 z - q11Phi z - 2 * q11ActualReference.Leta z -
    q11ActualReference.LmuNegative z

def q11Wmu (t : ℝ) : ℝ :=
  Config.B0 t - q11Psi t - 2 * q11ActualReference.Lmu t -
    q11ActualReference.Leta (Complex.ofReal (-t))

theorem q11ContourIntegral_eq_integral {f : ℂ → ℝ}
    (hf : AEStronglyMeasurable f q11ContourReferenceMeasure) :
    q11ContourIntegral f = ∫ z, f z ∂q11ContourReferenceMeasure := by
  rw [q11ContourReferenceMeasure,
    integral_map ConfigContourMeasure.continuous_ellipse.aemeasurable hf,
    q11Integral_contourParamMeasure]
  rfl

theorem q11ContourPotential_eq_integral (z : ℂ) :
    q11ContourPotential z =
      ∫ w, Real.log ‖z - w‖ ∂q11ContourReferenceMeasure := by
  unfold q11ContourPotential
  apply q11ContourIntegral_eq_integral
  exact (Real.measurable_log.comp
    (continuous_norm.comp (continuous_const.sub continuous_id)).measurable).aestronglyMeasurable

theorem q11EtaReferenceMeasure_integral (f : ℂ → ℝ)
    (hf : Measurable f)
    (hpin : Integrable (fun x : ℝ => f (x : ℂ)) q11PinnedReferenceMeasure)
    (hcontour : Integrable (fun z : ℂ => f z) q11ContourReferenceMeasure) :
    ∫ z : ℂ, f z ∂q11EtaReferenceMeasure =
      (∫ x : ℝ, f (x : ℂ) ∂q11PinnedReferenceMeasure) +
        ∫ z : ℂ, f z ∂q11ContourReferenceMeasure := by
  have hmapint : Integrable f
      (Measure.map Complex.ofReal q11PinnedReferenceMeasure) :=
    (integrable_map_measure hf.aestronglyMeasurable
      Complex.measurable_ofReal.aemeasurable).mpr hpin
  rw [q11EtaReferenceMeasure, integral_add_measure hmapint hcontour]
  rw [integral_map_of_stronglyMeasurable Complex.measurable_ofReal
    hf.stronglyMeasurable]

theorem q11EtaReferenceIntegral_eq_measure_integral (f : ℂ → ℝ)
    (hf : Measurable f)
    (hpin : Integrable (fun x : ℝ => f (x : ℂ)) q11PinnedReferenceMeasure)
    (hcontour : Integrable (fun z : ℂ => f z) q11ContourReferenceMeasure) :
    q11EtaReferenceIntegral f = ∫ z : ℂ, f z ∂q11EtaReferenceMeasure := by
  unfold q11EtaReferenceIntegral
  rw [q11ContourIntegral_eq_integral hcontour.aestronglyMeasurable]
  exact (q11EtaReferenceMeasure_integral f hf hpin hcontour).symm

end

end Li2Lean.P0.Q11Data
