/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.AllN.ProducerAssembly
import Li2Lean.P0.Q11Reference

namespace Li2Lean.AllNAssembly

noncomputable section

open MeasureTheory
open Li2Lean.P0
open Li2Lean.P0.PositiveBase
open Li2Lean.P0.Q11Data
open Li2Lean.P0.ConfigContourReference
open Li2Lean.P0.TubeInterior

/-! The q=11 contour support is a genuine map-of-ellipse fact.  This is
separate from the still-open q=11 finite-energy and cross-energy leaves. -/
theorem q11ContourReferenceMeasure_supported_sa4 :
    Measure.support q11ContourReferenceMeasure ⊆ Gamma := by
  apply Measure.support_subset_of_isClosed isCompact_Gamma.isClosed
  have hzero : q11ContourReferenceMeasure Gammaᶜ = 0 := by
    rw [q11ContourReferenceMeasure,
      Measure.map_apply ConfigContourMeasure.continuous_ellipse.measurable
        isCompact_Gamma.isClosed.measurableSet.compl]
    have hpre : (Li2Lean.p0EllipsePoint 1 ⁻¹' Gammaᶜ) = (∅ : Set ℝ) := by
      ext u
      simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_range]
      constructor
      · intro h
        exact (h ⟨u, (ellipsePoint_one_eq_gammaPoint u).symm⟩).elim
      · intro h
        exact h.elim
    rw [hpre]
    simp
  exact hzero

theorem q11EtaReferenceMeasure_eq_companion_sa4 :
    q11EtaReferenceMeasure =
      P0.p0CompanionMeasure q11PinnedReferenceMeasure
        q11ContourReferenceMeasure := by
  rfl

/-! The positive-base profile uses an affine shift of the q=2 P0 energy.
This lemma exposes the shifted dual inequality without hiding any of the
cross-energy or cap obligations. -/
theorem p0PositiveEnergyValue_ge_of_caps_sa4 (lambda : ℝ)
    (M M₀ : P0.P0AdmissibleMeasures) (hM : p0PositiveEnergyDomain M)
    (hfin₀ : P0.P0FiniteEnergyCondition M₀)
    (hcross : P0.L6Admissible.P0L6CrossEnergy M M₀)
    (hEta hMu P T : ℝ)
    (hEtaCap : hEta - P ≤
      ∫ z, (P0.p0DualWeta M₀ z - lambda * z.re) ∂M.eta)
    (hMuCap : hMu - T ≤
      ∫ t, (P0.p0DualWmu M₀ t + lambda * t) ∂M.mu) :
    (9 / 2 : ℝ) - 2 * P0.ell +
        P0.L6Variations.l6QLog M₀.eta (P0.p0FrequencyMeasure M₀) +
        hEta + hMu - P - T ≤ p0PositiveEnergyValue lambda M := by
  obtain ⟨hfin, hRe⟩ := hM
  have hW := P0.p0DualWeta_integrable M M₀ hfin hcross
  have hWm := P0.p0DualWmu_integrable M M₀ hfin hcross
  rw [integral_sub hW (hRe.const_mul lambda), integral_const_mul] at hEtaCap
  rw [integral_add hWm (hfin.1.const_mul lambda), integral_const_mul] at hMuCap
  have hbase := P0.p0Dual_regularizedEnergy_ge_of_caps M M₀ hfin hfin₀ hcross
    hEta hMu (P - lambda * ∫ z, z.re ∂M.eta)
      (T + lambda * ∫ t, t ∂M.mu)
    (by linarith) (by linarith)
  unfold p0PositiveEnergyValue
  linarith

/-! A profile-level form.  The cap and cross-energy facts remain explicit
inputs; this is an adapter, not a claim that q=11 caps are already proved. -/
theorem p0PositiveEnergyProfileActual_ge_of_uniform_caps_sa4 (lambda : ℝ)
    (M₀ : P0.P0AdmissibleMeasures) (hdom₀ : p0PositiveEnergyDomain M₀)
    (hEta hMu P T : ℝ)
    (hCaps : ∀ M : P0.P0AdmissibleMeasures, p0PositiveEnergyDomain M →
      ∃ _hcross : P0.L6Admissible.P0L6CrossEnergy M M₀,
        hEta - P ≤ ∫ z, (P0.p0DualWeta M₀ z - lambda * z.re) ∂M.eta ∧
        hMu - T ≤ ∫ t, (P0.p0DualWmu M₀ t + lambda * t) ∂M.mu) :
    (9 / 2 : ℝ) - 2 * P0.ell +
        P0.L6Variations.l6QLog M₀.eta (P0.p0FrequencyMeasure M₀) +
        hEta + hMu - P - T ≤ p0PositiveEnergyProfileActual lambda := by
  unfold p0PositiveEnergyProfileActual
  refine le_csInf ⟨_, M₀, hdom₀, rfl⟩ ?_
  rintro e ⟨M, hM, rfl⟩
  obtain ⟨hcross, h1, h2⟩ := hCaps M hM
  exact p0PositiveEnergyValue_ge_of_caps_sa4 lambda M M₀ hM hdom₀.1 hcross
    hEta hMu P T h1 h2

/-! q=11's unresolved shifted dual obligations are packaged honestly. -/
structure Q11ShiftedDualCertificateSA4 where
  M₀ : P0.P0AdmissibleMeasures
  dom₀ : p0PositiveEnergyDomain M₀
  qLog_lower : (-635537 / 1000000 : ℝ) ≤
    P0.L6Variations.l6QLog M₀.eta (P0.p0FrequencyMeasure M₀)
  caps : ∀ M : P0.P0AdmissibleMeasures, p0PositiveEnergyDomain M →
    ∃ _hcross : P0.L6Admissible.P0L6CrossEnergy M M₀,
      (-3359 / 500 : ℝ) - 1 / 1000000 ≤
        ∫ z, (P0.p0DualWeta M₀ z - Real.log ((11 : ℝ) / 2) * z.re) ∂M.eta ∧
      (1217 / 200 : ℝ) - 1069189 / 1000000 ≤
        ∫ t, (P0.p0DualWmu M₀ t + Real.log ((11 : ℝ) / 2) * t) ∂M.mu

theorem p0PositiveEnergyProfileActual_endpoint_eleven_of_certificate_sa4
    (C : Q11ShiftedDualCertificateSA4) :
    (77597 / 100000 : ℝ) ≤
      p0PositiveEnergyProfileActual (Real.log ((11 : ℝ) / 2)) := by
  have h := p0PositiveEnergyProfileActual_ge_of_uniform_caps_sa4
    (Real.log ((11 : ℝ) / 2)) C.M₀ C.dom₀
    (-3359 / 500) (1217 / 200) (1 / 1000000) (1069189 / 1000000) C.caps
  have hl2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  simp only [P0.ell] at h
  norm_num at hl2
  linarith [C.qLog_lower]

end

end Li2Lean.AllNAssembly
