/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.AllN.Q11ShiftedDualAeAssembly
import Li2Lean.P0.Q11PinnedContourCap
import Li2Lean.P0.Q11NegativeEtaL6Cap
import Li2Lean.P0.Q11FrequencyL6Cap
import Li2Lean.P0.Q11ContourPotentialLower
import Li2Lean.P0.ReferenceSupportCaps
import Li2Lean.P0.U2GlobalFejer
import Li2Lean.P0.ConfigContourCoarse
import Li2Lean.P0.TubeSweepSources

/-!
The q = 11 L6 cross-energy adapter, following v13 `p0-analytic.tex:222-255`
and the contour comparison at `p0-analytic.tex:759-761`.

The four positive-kernel caps are support-local.  In particular, the Gamma
cap is obtained from the q11 Fourier lower bound and is not a conclusion-shaped
assumption.  The resulting declaration is kept separate from the endpoint
provider so the latter only consumes this analytic input.
-/

open MeasureTheory Set Filter
open scoped ENNReal

namespace Li2Lean.AllNAssembly

noncomputable section

open Li2Lean.P0
open Li2Lean.P0.Q11Data
open Li2Lean.P0.Q11ContourFourier
open Li2Lean.P0.L6Variations
open Li2Lean.P0.EnergyLowerBound
open Li2Lean.P0.L6Admissible
open Li2Lean.P0.ConfigContourReference
open Li2Lean.P0.ConfigContourProductIntegrability
open Li2Lean.P0.ConfigContourCoarse
open Li2Lean.P0.ConfigContourKernel

private theorem q11_contour_log_integrable (z : ℂ) :
    Integrable (fun w : ℂ => Real.log ‖z - w‖)
      q11ContourReferenceMeasure := by
  have hf : Measurable (fun w : ℂ => Real.log ‖z - w‖) := by
    exact Real.measurable_log.comp (by fun_prop)
  rw [q11ContourReferenceMeasure]
  apply (integrable_map_measure hf.aestronglyMeasurable
    ConfigContourMeasure.continuous_ellipse.aemeasurable).2
  let m : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi))
  let f : ℝ → ℝ≥0∞ := fun u => ENNReal.ofReal (q11ContourDensity u)
  have hfmeas : Measurable f := by
    exact ENNReal.measurable_ofReal.comp continuous_q11ContourDensity.measurable
  have hftop : ∀ᵐ u ∂m, f u < ⊤ := by
    filter_upwards [] with u
    exact ENNReal.ofReal_lt_top
  rw [q11ContourParamMeasure]
  apply Integrable.smul_measure _ ENNReal.ofReal_ne_top
  apply (integrable_withDensity_iff_integrable_smul' hfmeas hftop).2
  have hbase : Integrable
      (fun u : ℝ => Real.log ‖z - Li2Lean.p0EllipsePoint 1 u‖) m := by
    dsimp [m]
    exact contour_inner_log_integrable z
  have hdens : ∀ᵐ u ∂m, ‖q11ContourDensity u‖ ≤
      49 * ((2 * contourPairMassUnits.sum : ℝ) / (denominator : ℝ)) := by
    filter_upwards [] with u
    have hnon : 0 ≤ q11ContourDensity u := q11ContourDensity_nonneg u
    rw [Real.norm_of_nonneg hnon]
    calc
      q11ContourDensity u = ∑ j : Fin contourNodeCount,
          q11ContourWeight j * fejer48 (u - contourAngle j) := rfl
      _ ≤ ∑ j : Fin contourNodeCount, q11ContourWeight j * 49 := by
        apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul_of_nonneg_left
          (fejer48_le_49 _) (q11ContourWeight_nonneg _)
      _ = 49 * ((2 * contourPairMassUnits.sum : ℝ) /
          (denominator : ℝ)) := by
        rw [← Finset.sum_mul, q11ContourWeight_sum]
        ring
  have hmul := hbase.mul_bdd
    continuous_q11ContourDensity.aestronglyMeasurable hdens
  have htoReal : ∀ u : ℝ, (f u).toReal = q11ContourDensity u := by
    intro u
    dsimp [f]
    exact ENNReal.toReal_ofReal (q11ContourDensity_nonneg u)
  simpa [Function.comp_apply, smul_eq_mul, htoReal, mul_comm] using hmul

private theorem q11_l6PosKernel_le_of_distance_lower
    {z w : ℂ} {d : ℝ} (hd : 0 < d) (h : d ≤ ‖z - w‖) :
    l6PosKernel z w ≤ ENNReal.ofReal (Real.posLog d⁻¹) := by
  have hne : z ≠ w := by
    intro heq
    rw [heq] at h
    simp at h
    linarith
  have hinv : ‖z - w‖⁻¹ ≤ d⁻¹ := by
    simpa [one_div] using (one_div_le_one_div_of_le hd h)
  have hpos : Real.posLog ‖z - w‖⁻¹ ≤ Real.posLog d⁻¹ :=
    Real.posLog_le_posLog
      (le_trans (by norm_num) (inv_nonneg.mpr (norm_nonneg _))) hinv
  simp only [l6PosKernel, hne, if_false]
  exact ENNReal.ofReal_le_ofReal hpos

private theorem q11Contour_l6PosKernel_bound_of_distance_lower
    {z : ℂ} {d : ℝ} (hd : 0 < d)
    (h : ∀ᵐ w ∂q11ContourReferenceMeasure, d ≤ ‖z - w‖) :
    (∫⁻ w, l6PosKernel z w ∂q11ContourReferenceMeasure) ≤
      ENNReal.ofReal (Real.posLog d⁻¹) * q11ContourReferenceMeasure Set.univ := by
  calc
    (∫⁻ w, l6PosKernel z w ∂q11ContourReferenceMeasure) ≤
        ∫⁻ _w : ℂ, ENNReal.ofReal (Real.posLog d⁻¹)
          ∂q11ContourReferenceMeasure :=
      lintegral_mono_ae (h.mono fun w hw =>
        q11_l6PosKernel_le_of_distance_lower hd hw)
    _ = ENNReal.ofReal (Real.posLog d⁻¹) *
        q11ContourReferenceMeasure Set.univ := by
      rw [lintegral_const]

private theorem q11Contour_l6PosKernel_bound_on_pinned_source
    {z : ℂ} (hz : z ∈ Li2Lean.P0.pinnedRealSourceSupport) :
    (∫⁻ w, l6PosKernel z w ∂q11ContourReferenceMeasure) ≤
      ENNReal.ofReal (Real.posLog (751 / 5000 : ℝ)⁻¹) *
        q11ContourReferenceMeasure Set.univ := by
  have hzreal : z = (z.re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa [hz.1]
  have hx02 : z.re ∈ Set.Icc (0 : ℝ) 2 := by
    constructor <;> linarith [hz.2.1, hz.2.2]
  apply q11Contour_l6PosKernel_bound_of_distance_lower (by norm_num)
  filter_upwards [q11ContourReferenceMeasure_ae_Gamma] with w hw
  rcases hw with ⟨u, rfl⟩
  have hbase : Config.baseEllipse u = Li2Lean.P0.gammaPoint u := by
    simpa [Config.baseEllipse, Li2Lean.P0.ellipsePoint] using
      Li2Lean.P0.ellipsePoint_one_eq_gammaPoint u
  have hclear := Config.s2_mixed_left_candidate
    (Config.baseEllipse u) ⟨u, rfl⟩ z.re hx02
  rw [hzreal, norm_sub_rev, ← hbase]
  simpa [Config.dPlus] using hclear

private theorem q11Contour_l6PosKernel_bound_on_negative_source
    {z : ℂ} (hz : z ∈ Li2Lean.P0.negativeRealSourceSupport) :
    (∫⁻ w, l6PosKernel z w ∂q11ContourReferenceMeasure) ≤
      ENNReal.ofReal (Real.posLog (1749 / 5000 : ℝ)⁻¹) *
        q11ContourReferenceMeasure Set.univ := by
  have hzreal : z = (z.re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa [hz.1]
  apply q11Contour_l6PosKernel_bound_of_distance_lower (by norm_num)
  filter_upwards [q11ContourReferenceMeasure_ae_Gamma] with w hw
  have hsrc : (z.re : ℝ) ≤ -(1 : ℝ) / 2 := by
    norm_num at hz ⊢
    exact hz.2
  have hclear := TubeEnergy.frequency_source_norm_sub_ge
    (x := (z.re : ℂ)) (by simpa using hsrc) hw
  rw [hzreal, norm_sub_rev]
  exact hclear

private theorem q11Contour_l6PosKernel_bound_on_Gamma_of_potential_lower
    {L : ℝ} (hL : ∀ z ∈ Gamma, L ≤ q11ContourPotential z) {z : ℂ}
    (hz : z ∈ Gamma) :
    (∫⁻ w, l6PosKernel z w ∂q11ContourReferenceMeasure) ≤
      ENNReal.ofReal
        (Real.log 5 * q11ContourReferenceMeasure.real Set.univ - L) := by
  obtain ⟨u, rfl⟩ := hz
  have hset : MeasurableSet {w : ℂ |
      ‖Li2Lean.P0.gammaPoint u - w‖ ≤ (5 : ℝ)} := by
    exact (isClosed_le
      (continuous_norm.comp (continuous_const.sub continuous_id))
      continuous_const).measurableSet
  have hdist : ∀ᵐ w ∂q11ContourReferenceMeasure,
      ‖Li2Lean.P0.gammaPoint u - w‖ ≤ (5 : ℝ) := by
    rw [q11ContourReferenceMeasure,
      ae_map_iff ConfigContourMeasure.continuous_ellipse.aemeasurable hset]
    filter_upwards [] with v
    have hu : Li2Lean.p0EllipsePoint 1 u = Li2Lean.P0.gammaPoint u := by
      simpa [Li2Lean.P0.ellipsePoint] using
        (Li2Lean.P0.ellipsePoint_one_eq_gammaPoint u)
    rw [← hu]
    exact ConfigContourCoarse.ellipsePoint_distance_le_five u v
  have hInt := q11_contour_log_integrable (Li2Lean.P0.gammaPoint u)
  have hmain := Li2Lean.P0.U2GlobalFejer.lintegral_l6PosKernel_le_of_log_bound
    q11ContourReferenceMeasure (Li2Lean.P0.gammaPoint u) (B := 5) (by norm_num)
    (q11ContourReferenceMeasure_singleton _) hInt hdist
  have hpot_eq :
      (∫ w, Real.log 5 - Real.log ‖Li2Lean.P0.gammaPoint u - w‖
        ∂q11ContourReferenceMeasure) =
        Real.log 5 * q11ContourReferenceMeasure.real Set.univ -
          q11ContourPotential (Li2Lean.P0.gammaPoint u) := by
    rw [integral_sub (integrable_const _) hInt]
    rw [integral_const, q11ContourPotential_eq_integral]
    simp only [smul_eq_mul]
    ring
  rw [hpot_eq] at hmain
  exact hmain.trans (ENNReal.ofReal_le_ofReal (sub_le_sub_left
    (hL _ ⟨u, rfl⟩) _))

private theorem q11FrequencyReference_l6PosKernel_bound :
    ∀ z : ℂ,
      (∫⁻ w, l6PosKernel z w ∂
        p0FrequencyMeasure q11AdmissibleMeasures) ≤ ENNReal.ofReal 2 := by
  have hμ : q11FrequencyReferenceMeasure ≤
      volume.restrict (Set.Ici (1 / 2 : ℝ)) := by
    exact le_trans q11FrequencyReferenceMeasure_le_restrict
      (Measure.restrict_mono (Set.Icc_subset_Ici_self) le_rfl)
  intro z
  rw [q11AdmissibleMeasures_frequency_eq, q11FrequencyNegativeMeasure]
  exact frequencyReference_l6PosKernel_bound_of_density_le_one
    q11FrequencyReferenceMeasure hμ frequencyHalfLineOneDimensionalCap_proof z

private theorem q11_reference_support_measurable :
    MeasurableSet Li2Lean.P0.referenceEtaSourceSupport := by
  exact (((measurableSet_singleton (0 : ℝ)).preimage
      Complex.continuous_im.measurable).inter
      (measurableSet_Icc.preimage Complex.continuous_re.measurable)).union
      TubeInterior.measurable_Gamma |>.union
    (((measurableSet_singleton (0 : ℝ)).preimage
      Complex.continuous_im.measurable).inter
      (measurableSet_Iic.preimage Complex.continuous_re.measurable))

private theorem q11_admissible_eta_ae_mem_reference_support
    (M : P0AdmissibleMeasures) :
    ∀ᵐ z ∂M.eta, z ∈ Li2Lean.P0.referenceEtaSourceSupport := by
  change ∀ᵐ z ∂(Measure.map Complex.ofReal M.kappa + M.nu),
    z ∈ Li2Lean.P0.referenceEtaSourceSupport
  rw [ae_add_measure_iff]
  constructor
  · apply (ae_map_iff Complex.measurable_ofReal.aemeasurable
      q11_reference_support_measurable).2
    filter_upwards [EnergyLowerBound.kappa_ae_mem M] with x hx
    exact Or.inl (Or.inl (by
      show (x : ℂ).im = 0 ∧ (x : ℂ).re ∈ Set.Icc (1 / 4 : ℝ) (5 / 4)
      exact ⟨by simp, hx⟩))
  · filter_upwards [EnergyLowerBound.nu_ae_mem_Gamma M] with z hz
    exact Or.inl (Or.inr hz)

private theorem q11_admissible_frequency_ae_mem_reference_support
    (M : P0AdmissibleMeasures) :
    ∀ᵐ z ∂(p0FrequencyMeasure M), z ∈ Li2Lean.P0.referenceEtaSourceSupport := by
  rw [p0FrequencyMeasure, p0ReflectedFrequencyMeasure]
  apply (ae_map_iff L6Admissible.measurable_reflect.aemeasurable
      q11_reference_support_measurable).2
  filter_upwards [L6Admissible.mu_ae_ge M] with t ht
  exact Or.inr (by
    simp [negativeRealSourceSupport]
    linarith)

/-! Four support-local caps assembled exactly as the q11 specialization of the
v13 L6 argument. -/
theorem q11_L6CrossEnergy_of_contour_potential_lower
    (M : P0.P0AdmissibleMeasures)
    (hfin : P0.P0FiniteEnergyCondition M)
    (hfin₀ : P0.P0FiniteEnergyCondition q11AdmissibleMeasures)
    {L : ℝ} (hL : ∀ z ∈ Gamma, L ≤ q11ContourPotential z) :
    P0.L6Admissible.P0L6CrossEnergy M q11AdmissibleMeasures := by
  let Cη : ENNReal :=
    ENNReal.ofReal 2 +
      ENNReal.ofReal (Real.posLog (751 / 5000 : ℝ)⁻¹) *
        q11ContourReferenceMeasure Set.univ +
      ENNReal.ofReal
        (Real.log 5 * q11ContourReferenceMeasure.real Set.univ - L) +
      ENNReal.ofReal (Real.posLog (1749 / 5000 : ℝ)⁻¹) *
        q11ContourReferenceMeasure Set.univ
  have hηcap : ∀ z ∈ Li2Lean.P0.referenceEtaSourceSupport,
      (∫⁻ w, l6PosKernel z w ∂q11AdmissibleMeasures.eta) ≤ Cη := by
    intro z hz
    rw [q11AdmissibleMeasures_eta_eq, q11EtaReferenceMeasure,
      lintegral_add_measure]
    have hpin := pinnedReference_l6PosKernel_bound_of_density
      q11PinnedReferenceMeasure q11PinnedReferenceMeasure_le_restrict z
    rcases hz with hz | hz
    · rcases hz with hz | hz
      · have hcont := q11Contour_l6PosKernel_bound_on_pinned_source hz
        calc
          _ ≤ ENNReal.ofReal 2 +
              ENNReal.ofReal (Real.posLog (751 / 5000 : ℝ)⁻¹) *
                q11ContourReferenceMeasure Set.univ := add_le_add hpin hcont
          _ ≤ Cη := by
            dsimp [Cη]
            have htail : ENNReal.ofReal (Real.posLog (751 / 5000 : ℝ)⁻¹) *
                q11ContourReferenceMeasure Set.univ ≤
                ENNReal.ofReal (Real.posLog (751 / 5000 : ℝ)⁻¹) *
                  q11ContourReferenceMeasure Set.univ +
                  ENNReal.ofReal
                    (Real.log 5 * q11ContourReferenceMeasure.real Set.univ - L) +
                  ENNReal.ofReal (Real.posLog (1749 / 5000 : ℝ)⁻¹) *
                    q11ContourReferenceMeasure Set.univ := by
              exact le_add_right (le_add_right (le_refl _))
            simpa [add_assoc] using
              (add_le_add (le_refl (ENNReal.ofReal 2)) htail)
      · have hcont := q11Contour_l6PosKernel_bound_on_Gamma_of_potential_lower hL hz
        calc
          _ ≤ ENNReal.ofReal 2 +
              ENNReal.ofReal
                (Real.log 5 * q11ContourReferenceMeasure.real Set.univ - L) :=
            add_le_add hpin hcont
          _ ≤ Cη := by
            dsimp [Cη]
            have htail : ENNReal.ofReal
                (Real.log 5 * q11ContourReferenceMeasure.real Set.univ - L) ≤
                ENNReal.ofReal (Real.posLog (751 / 5000 : ℝ)⁻¹) *
                  q11ContourReferenceMeasure Set.univ +
                ENNReal.ofReal
                  (Real.log 5 * q11ContourReferenceMeasure.real Set.univ - L) +
                ENNReal.ofReal (Real.posLog (1749 / 5000 : ℝ)⁻¹) *
                  q11ContourReferenceMeasure Set.univ := by
              have h1 : ENNReal.ofReal
                  (Real.log 5 * q11ContourReferenceMeasure.real Set.univ - L) ≤
                  ENNReal.ofReal
                    (Real.log 5 * q11ContourReferenceMeasure.real Set.univ - L) +
                    ENNReal.ofReal (Real.posLog (1749 / 5000 : ℝ)⁻¹) *
                      q11ContourReferenceMeasure Set.univ :=
                le_add_right (le_refl _)
              have h2 : ENNReal.ofReal
                  (Real.log 5 * q11ContourReferenceMeasure.real Set.univ - L) +
                    ENNReal.ofReal (Real.posLog (1749 / 5000 : ℝ)⁻¹) *
                      q11ContourReferenceMeasure Set.univ ≤
                  ENNReal.ofReal (Real.posLog (751 / 5000 : ℝ)⁻¹) *
                      q11ContourReferenceMeasure Set.univ +
                    (ENNReal.ofReal
                      (Real.log 5 * q11ContourReferenceMeasure.real Set.univ - L) +
                      ENNReal.ofReal (Real.posLog (1749 / 5000 : ℝ)⁻¹) *
                        q11ContourReferenceMeasure Set.univ) :=
                le_add_left (le_refl _)
              exact h1.trans (h2.trans_eq (by ac_rfl))
            have hsum := add_le_add (le_refl (ENNReal.ofReal 2)) htail
            simpa [add_assoc, add_comm, add_left_comm] using hsum
    · have hcont := q11Contour_l6PosKernel_bound_on_negative_source hz
      calc
        _ ≤ ENNReal.ofReal 2 +
            ENNReal.ofReal (Real.posLog (1749 / 5000 : ℝ)⁻¹) *
              q11ContourReferenceMeasure Set.univ := add_le_add hpin hcont
        _ ≤ Cη := by
          dsimp [Cη]
          have htail : ENNReal.ofReal (Real.posLog (1749 / 5000 : ℝ)⁻¹) *
              q11ContourReferenceMeasure Set.univ ≤
              ENNReal.ofReal (Real.posLog (751 / 5000 : ℝ)⁻¹) *
                q11ContourReferenceMeasure Set.univ +
              ENNReal.ofReal
                (Real.log 5 * q11ContourReferenceMeasure.real Set.univ - L) +
              ENNReal.ofReal (Real.posLog (1749 / 5000 : ℝ)⁻¹) *
                q11ContourReferenceMeasure Set.univ := by
            have h1 : ENNReal.ofReal (Real.posLog (1749 / 5000 : ℝ)⁻¹) *
                q11ContourReferenceMeasure Set.univ ≤
                ENNReal.ofReal (Real.posLog (1749 / 5000 : ℝ)⁻¹) *
                  q11ContourReferenceMeasure Set.univ +
                  ENNReal.ofReal
                    (Real.log 5 * q11ContourReferenceMeasure.real Set.univ - L) :=
              le_add_right (le_refl _)
            have h2 : ENNReal.ofReal (Real.posLog (1749 / 5000 : ℝ)⁻¹) *
                q11ContourReferenceMeasure Set.univ +
                  ENNReal.ofReal
                    (Real.log 5 * q11ContourReferenceMeasure.real Set.univ - L) ≤
                ENNReal.ofReal (Real.posLog (751 / 5000 : ℝ)⁻¹) *
                    q11ContourReferenceMeasure Set.univ +
                  (ENNReal.ofReal (Real.posLog (1749 / 5000 : ℝ)⁻¹) *
                    q11ContourReferenceMeasure Set.univ +
                    ENNReal.ofReal
                      (Real.log 5 * q11ContourReferenceMeasure.real Set.univ - L)) :=
              le_add_left (le_refl _)
            exact h1.trans (h2.trans_eq (by ac_rfl))
          have hsum := add_le_add (le_refl (ENNReal.ofReal 2)) htail
          simpa [add_assoc, add_comm, add_left_comm] using hsum
  have hφcap : ∀ z : ℂ,
      (∫⁻ w, l6PosKernel z w ∂
        p0FrequencyMeasure q11AdmissibleMeasures) ≤ ENNReal.ofReal 2 :=
    q11FrequencyReference_l6PosKernel_bound
  have hCη : Cη ≠ ⊤ := by
    dsimp [Cη]
    simp [q11ContourReferenceMeasure_univ, ENNReal.add_ne_top,
      ENNReal.mul_ne_top]
  apply P0.L6Admissible.p0L6CrossEnergy_of_support_restricted_of_admissible
    M q11AdmissibleMeasures hfin hfin₀
    (Sη := P0.referenceEtaSourceSupport) (Sφ := Set.univ)
    (Cη := Cη) (Cφ := ENNReal.ofReal 2)
  · exact hηcap
  · intro z _
    exact hφcap z
  · exact q11_admissible_eta_ae_mem_reference_support M
  · exact q11_admissible_frequency_ae_mem_reference_support M
  · exact Filter.Eventually.of_forall (fun _ => Set.mem_univ _)
  · exact Filter.Eventually.of_forall (fun _ => Set.mem_univ _)
  · exact hCη
  · exact ENNReal.ofReal_ne_top

/-! The q11 Fourier lower bound is the concrete v13 contour input, so the
cross-energy theorem can be consumed without an extra conclusion-shaped field.
-/
theorem q11ContourPotential_lower_on_Gamma :
    ∀ z ∈ Gamma,
      -(q11ContourMass * |Real.log contourScale| + 96 * q11ContourMass) ≤
        q11ContourPotential z := by
  intro z hz
  obtain ⟨u, rfl⟩ := hz
  have hu : Li2Lean.p0EllipsePoint 1 u = Li2Lean.P0.gammaPoint u := by
    exact Li2Lean.P0.ellipsePoint_one_eq_gammaPoint u
  rw [← hu]
  exact q11ContourPotential_lower_on_ellipse u

theorem q11_L6CrossEnergy_v13
    (M : P0.P0AdmissibleMeasures)
    (hfin : P0.P0FiniteEnergyCondition M)
    (hfin₀ : P0.P0FiniteEnergyCondition q11AdmissibleMeasures) :
    P0.L6Admissible.P0L6CrossEnergy M q11AdmissibleMeasures := by
  exact q11_L6CrossEnergy_of_contour_potential_lower M hfin hfin₀
    q11ContourPotential_lower_on_Gamma

end

end Li2Lean.AllNAssembly

#print axioms Li2Lean.AllNAssembly.q11_L6CrossEnergy_v13
