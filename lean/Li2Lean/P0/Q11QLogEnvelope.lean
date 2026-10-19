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

/-! A q = 11 negative-frequency measure, kept separate from the q = 2
`P0AdmissibleMeasures` record.  The q = 11 analytic producer still has to
prove its finite-energy and Fubini obligations. -/

def q11FrequencyNegativeMeasure : Measure ℂ :=
  q11FrequencyReferenceMeasure.map (fun t : ℝ => (-(t : ℂ)))

theorem q11FrequencyNegativeMeasure_univ :
    q11FrequencyNegativeMeasure Set.univ = 1 := by
  unfold q11FrequencyNegativeMeasure
  rw [Measure.map_apply]
  · simp only [Set.preimage_univ]
    exact q11FrequencyReferenceMeasure_univ
  · exact measurable_neg.comp Complex.measurable_ofReal
  · exact MeasurableSet.univ

instance q11FrequencyNegativeMeasure_isFinite :
    IsFiniteMeasure q11FrequencyNegativeMeasure :=
  ⟨by rw [q11FrequencyNegativeMeasure_univ]; simp⟩

/-! The six product-energy pieces.  The contour pieces are written using the
mapped contour measure, so every later split has an explicit measure and does
not rely on Lean's default value for a non-integrable integral. -/

def q11Eκκ : ℝ :=
  ∫ x, q11PinnedComplexPotential (x : ℂ) ∂q11PinnedReferenceMeasure

def q11Eκν : ℝ :=
  ∫ x, q11ContourPotential (x : ℂ) ∂q11PinnedReferenceMeasure

def q11Eνκ : ℝ :=
  ∫ z, q11PinnedComplexPotential z ∂q11ContourReferenceMeasure

def q11Eνν : ℝ :=
  ∫ z, q11ContourPotential z ∂q11ContourReferenceMeasure

def q11Eκμ : ℝ :=
  ∫ x, q11ReflectedFrequencyPotential (x : ℂ) ∂q11PinnedReferenceMeasure

def q11Eνμ : ℝ :=
  ∫ z, q11ReflectedFrequencyPotential z ∂q11ContourReferenceMeasure

def q11Eμμ : ℝ := q11QmuMu

/-! These are exactly the integrability inputs needed for the two measure
splits.  They are intentionally hypotheses: endpoint bounds and finite table
checks do not imply them. -/

structure Q11FiniteEnergyData : Prop where
  κκ : Integrable (fun x : ℝ => q11PinnedComplexPotential (x : ℂ))
    q11PinnedReferenceMeasure
  κν : Integrable (fun x : ℝ => q11ContourPotential (x : ℂ))
    q11PinnedReferenceMeasure
  νκ : Integrable q11PinnedComplexPotential q11ContourReferenceMeasure
  νν : Integrable q11ContourPotential q11ContourReferenceMeasure
  κμ : Integrable (fun x : ℝ => q11ReflectedFrequencyPotential (x : ℂ))
    q11PinnedReferenceMeasure
  νμ : Integrable q11ReflectedFrequencyPotential q11ContourReferenceMeasure

private theorem q11_contour_integral_eq_measure_integral_of_integrable
    {f : ℂ → ℝ} (hf : Integrable f q11ContourReferenceMeasure) :
    q11ContourIntegral f = ∫ z, f z ∂q11ContourReferenceMeasure := by
  exact q11ContourIntegral_eq_integral hf.aestronglyMeasurable

theorem q11QetaEta_split (h : Q11FiniteEnergyData) :
    q11QetaEta = q11Eκκ + q11Eκν + q11Eνκ + q11Eνν := by
  unfold q11QetaEta q11EtaReferenceIntegral q11EtaReferencePotential
  have hκ : Integrable (fun x : ℝ =>
      q11PinnedComplexPotential (x : ℂ) + q11ContourPotential (x : ℂ))
      q11PinnedReferenceMeasure := h.κκ.add h.κν
  have hν : Integrable (fun z : ℂ =>
      q11PinnedComplexPotential z + q11ContourPotential z)
      q11ContourReferenceMeasure := h.νκ.add h.νν
  rw [integral_add h.κκ h.κν]
  rw [q11_contour_integral_eq_measure_integral_of_integrable hν]
  rw [integral_add h.νκ h.νν]
  simp only [q11Eκκ, q11Eκν, q11Eνκ, q11Eνν]
  ring

theorem q11QetaMu_split (h : Q11FiniteEnergyData) :
    q11QetaMu = q11Eκμ + q11Eνμ := by
  unfold q11QetaMu q11EtaReferenceIntegral
  have hκ : Integrable (fun x : ℝ => q11ReflectedFrequencyPotential (x : ℂ))
      q11PinnedReferenceMeasure := h.κμ
  have hν : Integrable q11ReflectedFrequencyPotential
      q11ContourReferenceMeasure := h.νμ
  rw [q11_contour_integral_eq_measure_integral_of_integrable hν]
  simp only [q11Eκμ, q11Eνμ]

theorem q11QmuMu_eq_Eμμ : q11QmuMu = q11Eμμ := rfl

theorem q11ActualReference_qLog_eq_seven_terms
    (h : Q11FiniteEnergyData) :
    q11ActualReference.qLog =
      q11Eκκ + q11Eκν + q11Eνκ + q11Eνν + q11Eμμ + q11Eκμ + q11Eνμ := by
  rw [show q11ActualReference.qLog = q11QetaEta + q11QmuMu + q11QetaMu by rfl,
    q11QetaEta_split h, q11QmuMu_eq_Eμμ, q11QetaMu_split h]
  ring

theorem q11ActualReference_qLog_eq_six_terms
    (h : Q11FiniteEnergyData) (hsym : q11Eνκ = q11Eκν) :
    q11ActualReference.qLog =
      q11Eκκ + 2 * q11Eκν + q11Eνν + q11Eμμ + q11Eκμ + q11Eνμ := by
  rw [q11ActualReference_qLog_eq_seven_terms h, hsym]
  ring

/-! Arithmetic consumers must provide a lower bound for every one of the seven
pieces.  The printed q = 11 ratio is only a target constant; this theorem
does not manufacture any of those analytic lower bounds. -/

theorem q11_qLog_lower_of_seven
    (h : Q11FiniteEnergyData)
    {Lκκ Lκν Lνκ Lνν Lκμ Lνμ Lμμ : ℝ}
    (hκκ : Lκκ ≤ q11Eκκ) (hκν : Lκν ≤ q11Eκν)
    (hνκ : Lνκ ≤ q11Eνκ) (hνν : Lνν ≤ q11Eνν)
    (hκμ : Lκμ ≤ q11Eκμ) (hνμ : Lνμ ≤ q11Eνμ)
    (hμμ : Lμμ ≤ q11Eμμ)
    (hbudget : ratioToReal qLogLower <
      Lκκ + Lκν + Lνκ + Lνν + Lμμ + Lκμ + Lνμ) :
    ratioToReal qLogLower < q11ActualReference.qLog := by
  rw [q11ActualReference_qLog_eq_seven_terms h]
  linarith

theorem q11_qLog_lower_of_six
    (h : Q11FiniteEnergyData) (hsym : q11Eνκ = q11Eκν)
    {Lκκ Lκν Lνν Lκμ Lνμ Lμμ : ℝ}
    (hκκ : Lκκ ≤ q11Eκκ) (hκν : Lκν ≤ q11Eκν)
    (hνν : Lνν ≤ q11Eνν) (hκμ : Lκμ ≤ q11Eκμ)
    (hνμ : Lνμ ≤ q11Eνμ) (hμμ : Lμμ ≤ q11Eμμ)
    (hbudget : ratioToReal qLogLower <
      Lκκ + 2 * Lκν + Lνν + Lμμ + Lκμ + Lνμ) :
    ratioToReal qLogLower < q11ActualReference.qLog := by
  rw [q11ActualReference_qLog_eq_six_terms h hsym]
  linarith

end

end Li2Lean.P0.Q11Data
