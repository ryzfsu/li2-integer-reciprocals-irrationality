/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/

import Li2Lean.AllN.B2ShiftedDualEndpoint11SA4
import Li2Lean.AllN.Q11ShiftedDualAeAssembly
import Li2Lean.P0.Q11QLogEnvelopeProducer

open MeasureTheory Set Filter

namespace Li2Lean.AllNAssembly

noncomputable section

open Li2Lean.P0
open Li2Lean.P0.L6Admissible
open Li2Lean.P0.L6Variations
open Li2Lean.P0.Q11Data
open Li2Lean.P0.Q11QLogEnvelopeProducer

/-! Identify the concrete q = 11 L6 qLog with the reference-energy value used
by the integer-ratio envelope. The finite-energy hypothesis is explicit. -/
theorem q11Admissible_l6QLog_eq_actualReference
    (hfin : P0FiniteEnergyCondition q11AdmissibleMeasures) :
    L6Variations.l6QLog q11AdmissibleMeasures.eta
      (p0FrequencyMeasure q11AdmissibleMeasures) = q11ActualReference.qLog := by
  have hEE := eta_kernel_integrable q11AdmissibleMeasures hfin
  have hFF := freq_kernel_integrable q11AdmissibleMeasures hfin
  have hEF := eta_freq_kernel_integrable q11AdmissibleMeasures hfin
  have hemb := Complex.isometry_ofReal.isClosedEmbedding.measurableEmbedding
  have hpotE : L6Variations.l6LogPotential q11AdmissibleMeasures.eta =ᵐ[
      q11AdmissibleMeasures.eta] q11EtaReferencePotential := by
    filter_upwards [kernel_integrable_of_prod_right hEE] with z hz
    exact q11_eta_potential_eq hz
  have hintE : Integrable q11EtaReferencePotential q11AdmissibleMeasures.eta :=
    (L6Variations.integrable_potential hEE).congr hpotE
  have hsplit : ∀ f : ℂ → ℝ, Integrable f q11AdmissibleMeasures.eta →
      ∫ z, f z ∂q11AdmissibleMeasures.eta = q11EtaReferenceIntegral f := by
    intro f hf
    rw [q11AdmissibleMeasures_eta_eq] at hf ⊢
    have hmap : Integrable f (Measure.map Complex.ofReal
        q11PinnedReferenceMeasure) :=
      hf.mono_measure (Measure.le_add_right le_rfl)
    have hnu : Integrable f q11ContourReferenceMeasure :=
      hf.mono_measure (Measure.le_add_left le_rfl)
    rw [q11EtaReferenceMeasure, integral_add_measure hmap hnu,
      hemb.integral_map,
      q11EtaReferenceIntegral,
      q11ContourIntegral_eq_integral hnu.aestronglyMeasurable]
  have hI1 : li2LogInteraction q11AdmissibleMeasures.eta
      q11AdmissibleMeasures.eta = -q11QetaEta := by
    rw [L6Variations.li2LogInteraction_eq_neg_integral_potential hEE,
      integral_congr_ae hpotE, hsplit _ hintE]
    rfl
  have hintF : Integrable q11ReflectedFrequencyPotential
      q11AdmissibleMeasures.eta := by
    have h := L6Variations.integrable_potential hEF
    exact h.congr (Filter.Eventually.of_forall
      (fun z => q11_frequency_potential_eq z))
  have hI3 : li2LogInteraction q11AdmissibleMeasures.eta
      (p0FrequencyMeasure q11AdmissibleMeasures) = -q11QetaMu := by
    rw [L6Variations.li2LogInteraction_eq_neg_integral_potential hEF]
    rw [show (fun z => L6Variations.l6LogPotential
        (p0FrequencyMeasure q11AdmissibleMeasures) z) =
          q11ReflectedFrequencyPotential
      from funext q11_frequency_potential_eq, hsplit _ hintF]
    rfl
  have hI2 : li2LogInteraction (p0FrequencyMeasure q11AdmissibleMeasures)
      (p0FrequencyMeasure q11AdmissibleMeasures) = -q11QmuMu := by
    have hpot := L6Variations.integrable_potential hFF
    rw [L6Variations.li2LogInteraction_eq_neg_integral_potential hFF]
    rw [q11AdmissibleMeasures_frequency_eq] at hpot ⊢
    rw [q11FrequencyNegativeMeasure] at hpot ⊢
    rw [integral_map measurable_reflect.aemeasurable hpot.aestronglyMeasurable]
    have hfreq (t : ℝ) :
        L6Variations.l6LogPotential
            (Measure.map (fun s : ℝ => (-(s : ℂ))) q11FrequencyReferenceMeasure)
            (-(t : ℂ)) = q11FrequencyPotential t := by
      unfold L6Variations.l6LogPotential
      have hmeas : Measurable (fun w : ℂ => Real.log ‖-(t : ℂ) - w‖) :=
        Real.measurable_log.comp
          (continuous_norm.comp (continuous_const.sub continuous_id)).measurable
      change (∫ w : ℂ, Real.log ‖-(t : ℂ) - w‖ ∂
        Measure.map ((fun s : ℂ => -s) ∘ Complex.ofReal)
          q11FrequencyReferenceMeasure) = _
      rw [integral_map (measurable_neg.comp Complex.measurable_ofReal).aemeasurable
        hmeas.aestronglyMeasurable]
      apply integral_congr_ae
      filter_upwards [] with x
      congr 1
      change ‖-(t : ℂ) - (-(x : ℂ))‖ = _
      rw [show -(t : ℂ) - (-(x : ℂ)) = ((x - t : ℝ) : ℂ) by
        push_cast; ring]
      simp only [Complex.norm_real, Real.norm_eq_abs]
      rw [abs_sub_comm]
    simp only [hfreq]
    rfl
  rw [L6Variations.l6QLog, hI1, hI2, hI3]
  simp [q11ActualReference]
  ring

theorem q11Admissible_qLog_lower_of_envelope
    (C : Q11QLogEnvelopeInputs)
    (hfin : P0FiniteEnergyCondition q11AdmissibleMeasures) :
    (-635537 / 1000000 : ℝ) ≤
      L6Variations.l6QLog q11AdmissibleMeasures.eta
        (p0FrequencyMeasure q11AdmissibleMeasures) := by
  have hq := q11ActualReference_qLog_lower_of_envelope C
  have heq := q11Admissible_l6QLog_eq_actualReference hfin
  rw [heq]
  have hq' : ratioToReal qLogLower < q11ActualReference.qLog := hq
  have hq'' : (-635537 / 1000000 : ℝ) < q11ActualReference.qLog := by
    simpa [qLogLower, ratioToReal] using hq'
  exact hq''.le

end

end Li2Lean.AllNAssembly
