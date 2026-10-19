/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.AllN.B2ShiftedDualEndpoint11SA4
import Li2Lean.P0.Q11CrossEnergy
import Li2Lean.P0.Q11MeasureDomination
import Li2Lean.P0.Q11PenaltyRows
import Li2Lean.P0.Q11ContourRows
import Li2Lean.P0.Q11QLogEnvelope

open MeasureTheory Set Filter
open scoped ENNReal

namespace Li2Lean.AllNAssembly

noncomputable section

open Li2Lean.P0
open Li2Lean.P0.PositiveBase
open Li2Lean.P0.Q11Data
open Li2Lean.P0.ConfigContourReference
open Li2Lean.P0.TubeInterior

/-! A q = 11 reference packet with the exact `P0AdmissibleMeasures` shape.
The analytic finite-energy and cross-energy facts are deliberately not fields
of this definition; they remain explicit hypotheses at every consumer. -/

noncomputable def q11AdmissibleMeasures : P0AdmissibleMeasures := {
  kappa := q11PinnedReferenceMeasure
  nu := q11ContourReferenceMeasure
  mu := q11FrequencyReferenceMeasure
  kappa_le_density := q11PinnedReferenceMeasure_le_restrict
  nu_supported := by
    apply Measure.support_subset_of_isClosed isCompact_Gamma.isClosed
    have hzero : q11ContourReferenceMeasure Gammaᶜ = 0 := by
      rw [q11ContourReferenceMeasure,
        Measure.map_apply ConfigContourMeasure.continuous_ellipse.measurable
          isCompact_Gamma.isClosed.measurableSet.compl]
      have hpre : (Li2Lean.p0EllipsePoint 1 ⁻¹' Gammaᶜ) = (∅ : Set ℝ) := by
        ext u
        simp only [Set.mem_preimage, Set.mem_compl_iff]
        constructor
        · intro h
          exact (h ⟨u, (ellipsePoint_one_eq_gammaPoint u).symm⟩).elim
        · intro h
          exact h.elim
      rw [hpre]
      simp
    exact hzero
  companion_mass := by
    change q11EtaReferenceMeasure Set.univ = 1
    exact q11EtaReferenceMeasure_univ
  mu_le_density := by
    exact le_trans q11FrequencyReferenceMeasure_le_restrict
      (Measure.restrict_mono (Set.Icc_subset_Ici_self) le_rfl)
  frequency_mass := q11FrequencyReferenceMeasure_univ }

theorem q11AdmissibleMeasures_eta_eq :
    q11AdmissibleMeasures.eta = q11EtaReferenceMeasure := by
  rfl

theorem q11AdmissibleMeasures_frequency_eq :
    p0FrequencyMeasure q11AdmissibleMeasures =
      q11FrequencyNegativeMeasure := by
  rfl

private theorem measurable_log_norm_sub_q11 (z : ℂ) :
    Measurable (fun w : ℂ => Real.log ‖z - w‖) :=
  Real.measurable_log.comp
    (continuous_norm.comp (continuous_const.sub continuous_id)).measurable

/-! The q=11 potential definitions are exactly the L6 potentials of the
admissible packet.  The eta identity uses integrability so that the sum of the
pinned and contour measures can be split without changing the Bochner value. -/

theorem q11_eta_potential_eq {z : ℂ}
    (hz : Integrable (fun w : ℂ => Real.log ‖z - w‖)
      q11EtaReferenceMeasure) :
    L6Variations.l6LogPotential q11AdmissibleMeasures.eta z =
      q11EtaReferencePotential z := by
  have hemb := Complex.isometry_ofReal.isClosedEmbedding.measurableEmbedding
  rw [q11AdmissibleMeasures_eta_eq, L6Variations.l6LogPotential,
    q11EtaReferenceMeasure_integral (fun w => Real.log ‖z - w‖)
      (measurable_log_norm_sub_q11 z)
      (by
        have hmap := hz.mono_measure (Measure.le_add_right le_rfl)
        exact (hemb.integrable_map_iff).mp hmap)
      (hz.mono_measure (Measure.le_add_left le_rfl))]
  unfold q11EtaReferencePotential q11PinnedComplexPotential
  rw [q11ContourPotential_eq_integral]

theorem q11_frequency_potential_eq (z : ℂ) :
    L6Variations.l6LogPotential
        (p0FrequencyMeasure q11AdmissibleMeasures) z =
      q11ReflectedFrequencyPotential z := by
  rw [q11AdmissibleMeasures_frequency_eq, q11FrequencyNegativeMeasure,
    L6Variations.l6LogPotential]
  rw [integral_map (by fun_prop)
    (measurable_log_norm_sub_q11 z).aestronglyMeasurable]
  simp only [sub_neg_eq_add]
  rfl

/-! Shifted first-variation fields.  The only hypotheses are the actual
cross-energy integrability fields needed to obtain the ae kernels. -/

theorem q11_shifted_dualWeta_ae_eq
    (M : P0AdmissibleMeasures)
    (hcross : P0.L6Admissible.P0L6CrossEnergy M q11AdmissibleMeasures) :
    (fun z => p0DualWeta q11AdmissibleMeasures z -
      Real.log ((11 : ℝ) / 2) * z.re) =ᵐ[M.eta] q11Weta := by
  have hη := kernel_integrable_of_prod_right hcross.eta_eta₀
  have hφ := kernel_integrable_of_prod_right hcross.eta_freq₀
  filter_upwards [hη, hφ] with z hzη hzφ
  have hqη := q11_eta_potential_eq hzη
  have hqφ := q11_frequency_potential_eq z
  rw [p0DualWeta, hqη, hqφ, companionField_eq]
  simp [q11Weta, q11Phi, q11Lambda, q11ActualReference]
  ring

theorem q11_shifted_dualWmu_ae_eq
    (M : P0AdmissibleMeasures)
    (hcross : P0.L6Admissible.P0L6CrossEnergy M q11AdmissibleMeasures) :
    (fun t => p0DualWmu q11AdmissibleMeasures t +
      Real.log ((11 : ℝ) / 2) * t) =ᵐ[M.mu] q11Wmu := by
  have hw := kernel_integrable_of_prod_left hcross.eta₀_freq
  rw [p0FrequencyMeasure, p0ReflectedFrequencyMeasure] at hw
  have ht := ae_of_ae_map
    (measurable_neg.comp Complex.measurable_ofReal).aemeasurable hw
  filter_upwards [ht] with t hti
  have hqη := q11_eta_potential_eq hti
  have hqη' : L6Variations.l6LogPotential q11AdmissibleMeasures.eta
      (-(t : ℂ)) = q11EtaReferencePotential (-(t : ℂ)) := by
    simpa [Function.comp_def] using hqη
  have hqφ := q11_frequency_potential_eq (-(t : ℂ))
  have hfreq : q11ReflectedFrequencyPotential (-(t : ℂ)) =
      q11FrequencyPotential t := by
    unfold q11ReflectedFrequencyPotential q11FrequencyPotential
    apply integral_congr_ae
    filter_upwards [] with x
    congr 1
    rw [show -(t : ℂ) + (x : ℂ) = ((x - t : ℝ) : ℂ) by
      push_cast; ring]
    simp only [Complex.norm_real, Real.norm_eq_abs]
    rw [abs_sub_comm]
  rw [p0DualWmu, hqφ, hqη', regularizedField_eq]
  simp [q11Wmu, q11Psi, q11Lambda, q11ActualReference]
  rw [hfreq]
  ring

/-! Convert the two genuine q=11 penalty chains into shifted caps.  This is
an adapter: it still requires cross-energy and the row certificate, and does
not manufacture either of those inputs. -/

theorem q11_shifted_caps_of_penalty_rows
    (M : P0AdmissibleMeasures)
    (hM : p0PositiveEnergyDomain M)
    (hcross : P0.L6Admissible.P0L6CrossEnergy M q11AdmissibleMeasures)
    (R : Q11PenaltyRows) :
    (-3359 / 500 : ℝ) - 1 / 1000000 ≤
        ∫ z, (p0DualWeta q11AdmissibleMeasures z -
          Real.log ((11 : ℝ) / 2) * z.re) ∂M.eta ∧
      (1217 / 200 : ℝ) - 1069189 / 1000000 ≤
        ∫ t, (p0DualWmu q11AdmissibleMeasures t +
          Real.log ((11 : ℝ) / 2) * t) ∂M.mu := by
  have hdualEta := p0DualWeta_integrable M q11AdmissibleMeasures hM.1 hcross
  have hdualMu := p0DualWmu_integrable M q11AdmissibleMeasures hM.1 hcross
  have hEtaShift : Integrable
      (fun z => p0DualWeta q11AdmissibleMeasures z -
        Real.log ((11 : ℝ) / 2) * z.re) M.eta :=
    hdualEta.sub (hM.2.const_mul _)
  have hMuShift : Integrable
      (fun t => p0DualWmu q11AdmissibleMeasures t +
        Real.log ((11 : ℝ) / 2) * t) M.mu :=
    hdualMu.add (hM.1.1.const_mul _)
  have hEtaQ : Integrable q11Weta M.eta :=
    hEtaShift.congr (q11_shifted_dualWeta_ae_eq M hcross)
  have hMuQ : Integrable q11Wmu M.mu :=
    hMuShift.congr (q11_shifted_dualWmu_ae_eq M hcross)
  have hEta := actual_eta_cap M hEtaQ R.contour_lower
    (fun x hx => by exact le_max_right _ _)
    (fun x hx => by exact le_max_left _ _)
    R.pinned_integrable
  have hEtaPenalty := q11_pinned_penalty_le R
  have hEta' : (-3359 / 500 : ℝ) - 1 / 1000000 ≤
      ∫ z, q11Weta z ∂M.eta := by
    norm_num [q11EtaFloorQ_eq, q11PinnedPenaltyUpperQ_eq] at hEta hEtaPenalty ⊢
    linarith
  have hMu := actual_mu_cap M hMuQ
    (fun t ht => by exact le_max_right _ _)
    (fun t ht => by exact le_max_left _ _)
    R.frequency_integrable
  have hMuPenalty := q11_frequency_penalty_le R
  have hMu' : (1217 / 200 : ℝ) - 1069189 / 1000000 ≤
      ∫ t, q11Wmu t ∂M.mu := by
    norm_num [q11FrequencyFloorQ_eq, q11FrequencyPenaltyUpperQ_eq]
      at hMu hMuPenalty ⊢
    linarith
  constructor
  · rw [integral_congr_ae (q11_shifted_dualWeta_ae_eq M hcross)]
    exact hEta'
  · rw [integral_congr_ae (q11_shifted_dualWmu_ae_eq M hcross)]
    exact hMu'

/-! Final arithmetic assembly at the user-requested relaxed endpoint.  The
certificate remains explicit because q=11 contour, penalty, qLog and energy
leaves are not all closed in the release yet. -/

structure Q11ShiftedDualCertificate153 where
  dom₀ : p0PositiveEnergyDomain q11AdmissibleMeasures
  finite_energy : Q11FiniteEnergyData
  gamma : Q11GammaContourCertificate
  penalties : Q11PenaltyRows
  qLog_lower : (-635537 / 1000000 : ℝ) ≤
    P0.L6Variations.l6QLog q11AdmissibleMeasures.eta
      (P0.p0FrequencyMeasure q11AdmissibleMeasures)
  cross_energy : ∀ M : P0AdmissibleMeasures, p0PositiveEnergyDomain M →
    Nonempty (P0.L6Admissible.P0L6CrossEnergy M q11AdmissibleMeasures)

theorem p0PositiveEnergyProfileActual_endpoint_eleven_of_certificate
    (C : Q11ShiftedDualCertificate153) :
    (153 / 200 : ℝ) ≤
      p0PositiveEnergyProfileActual (Real.log ((11 : ℝ) / 2)) := by
  have h := p0PositiveEnergyProfileActual_ge_of_uniform_caps_sa4
    (Real.log ((11 : ℝ) / 2)) q11AdmissibleMeasures C.dom₀
    (-3359 / 500) (1217 / 200) (1 / 1000000) (1069189 / 1000000)
    (fun M hM => by
      obtain ⟨hcross⟩ := C.cross_energy M hM
      exact ⟨hcross, (q11_shifted_caps_of_penalty_rows M hM hcross
        C.penalties)⟩)
  have hl2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  simp only [P0.ell] at h
  norm_num at hl2
  linarith [C.qLog_lower]

end

end Li2Lean.AllNAssembly
