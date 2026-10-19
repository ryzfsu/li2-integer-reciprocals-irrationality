/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.AllN.P0PositiveEnergyProfile
import Li2Lean.P0.Tube.Gap.Ledger

namespace Li2Lean.AllNAssembly

noncomputable section

open MeasureTheory
open Li2Lean.P0
open Li2Lean.P0.PositiveBase

/-! ## The shifted pointwise and Fubini interfaces

The two pointwise estimates below are the existing, base-independent sweep
lemmas.  They are exposed here under the shifted-route namespace so that a
q-dependent envelope/cell proof cannot accidentally use a q = 2 conclusion.
-/

theorem shifted_re_sweep_interior {z : ℂ} (hz : 0 < ellipseLevel z) :
    (∫ y, y.re ∂TubeEnergy.tubeSweep z) = z.re := by
  exact TubeGap.re_sweep_interior hz

theorem shifted_re_sweep_exterior {δ : ℝ} {z : ℂ}
    (hz : ellipseLevel z < 0) (hzt : z ∈ tube δ) :
    |(∫ y, y.re ∂TubeEnergy.tubeSweep z) - z.re| ≤
      (semiMajor + semiMinor) * δ / semiMinor := by
  exact TubeGap.re_sweep_exterior hz hzt

/-! The only analytic Fubini step used by the shifted tube route.  The
integrability premise is intentional: it is the exact obligation needed by
`integral_sweptMeasure`, and does not hide a finite-energy conclusion. -/

theorem shifted_re_sweep_fubini {δ : ℝ}
    (M : P0TubeAdmissibleMeasures δ)
    (hInt : Integrable (fun z : ℂ => z.re) (TubeEnergy.tubeSwept M.nu)) :
    (∫ y : ℂ, y.re ∂TubeEnergy.tubeSwept M.nu) =
      ∫ z : ℂ, (∫ y : ℂ, y.re ∂TubeEnergy.tubeSweep z) ∂M.nu := by
  exact integral_sweptMeasure M.nu TubeEnergy.tubeSweep
    (fun z : ℂ => z.re) TubeEnergy.measurable_tubeSweep.aemeasurable hInt

/-! The actual displacement estimate.  The fixed kappa component cancels
after the eta measures are split; only the swept nu component contributes.
The three cases are the pointwise interior, boundary, and exterior sweep
identities from `FieldPointwise`. -/

theorem p0TubeSweep_re_displacement {δ : ℝ} (hδ : 0 < δ)
    (hδmax : δ ≤ tubeRadiusMax) (M : P0TubeAdmissibleMeasures δ)
    (_hM : p0TubeFiniteEnergyCondition M) :
    |(∫ z : ℂ, z.re ∂(p0TubeSweep M).eta) -
      ∫ z : ℂ, z.re ∂M.eta| ≤
      (semiMajor + semiMinor) * δ / semiMinor := by
  obtain ⟨hκfin, hνfin, -, hνtube, hκsupp, hκnorm, -, hmass⟩ :=
    TubeGap.tube_competitor_facts M
  letI : IsFiniteMeasure M.nu := hνfin
  letI : IsFiniteMeasure (Measure.map Complex.ofReal M.kappa) := hκfin
  have hκre : Integrable (fun z : ℂ => z.re)
      (Measure.map Complex.ofReal M.kappa) := by
    apply Integrable.mono' (integrable_const (4 : ℝ))
      Complex.continuous_re.aestronglyMeasurable
    filter_upwards [hκnorm] with z hz
    simpa [Real.norm_eq_abs] using (Complex.abs_re_le_norm z).trans hz
  have hνre : Integrable (fun z : ℂ => z.re) M.nu := by
    have hδmax' := hδmax
    norm_num [tubeRadiusMax] at hδmax'
    apply Integrable.mono' (integrable_const (5 : ℝ))
      Complex.continuous_re.aestronglyMeasurable
    filter_upwards [hνtube] with z hz
    have hz' := TubeEnergy.norm_le_of_mem_tube hz
    have hz5 : ‖z‖ ≤ 5 := by linarith
    simpa [Real.norm_eq_abs] using (Complex.abs_re_le_norm z).trans hz5
  have hSweptRe : Integrable (fun z : ℂ => z.re)
      (TubeEnergy.tubeSwept M.nu) := by
    exact TubeVariance.continuous_integrable _
      (TubeEnergy.tubeSwept_ae_mem_Gamma M.nu) Complex.continuous_re
  set g : ℂ → ℝ := fun z => ∫ y : ℂ, y.re ∂TubeEnergy.tubeSweep z with hg
  have hg_meas : StronglyMeasurable g := by
    have h := StronglyMeasurable.integral_kernel_prod_right'
      (κ := TubeEnergy.tubeKernel)
      (f := fun q : ℂ × ℂ => q.2.re)
      (Complex.continuous_re.stronglyMeasurable.comp_measurable measurable_snd)
    simpa [g] using h
  have hgb : ∀ z : ℂ, |g z| ≤ 4 := by
    intro z
    have h := norm_integral_le_of_norm_le_const
      (μ := TubeEnergy.tubeSweep z) (f := fun y : ℂ => y.re) (C := 4)
      ((TubeEnergy.tubeSweep_ae_mem_Gamma z).mono fun y hy => by
        rw [Real.norm_eq_abs]
        exact (Complex.abs_re_le_norm y).trans
          (TubeVariance.norm_le_four_of_mem_Gamma hy))
    simpa [Real.norm_eq_abs, g] using h
  have hg_int : Integrable g M.nu :=
    TubeEnergy.integrable_of_bound_ae hg_meas.aestronglyMeasurable
      (Filter.Eventually.of_forall hgb)
  have hbind : (∫ y : ℂ, y.re ∂TubeEnergy.tubeSwept M.nu) =
      ∫ z : ℂ, g z ∂M.nu := by
    exact integral_sweptMeasure M.nu TubeEnergy.tubeSweep
      (fun y : ℂ => y.re) TubeEnergy.measurable_tubeSweep.aemeasurable hSweptRe
  have hpoint : ∀ᵐ z ∂M.nu,
      |g z - z.re| ≤ (semiMajor + semiMinor) * δ / semiMinor := by
    filter_upwards [hνtube] with z hz
    rcases lt_trichotomy (ellipseLevel z) 0 with hneg | hzero | hpos
    · simpa [g] using TubeGap.re_sweep_exterior hneg hz
    · have hzG := TubeEnergy.mem_Gamma_of_ellipseLevel_eq_zero hzero
      change |g z - z.re| ≤ (semiMajor + semiMinor) * δ / semiMinor
      have hgz : g z = ∫ y : ℂ, y.re ∂TubeEnergy.tubeSweep z := by
        simpa [hg]
      rw [hgz, TubeEnergy.tubeSweep_eq_dirac_of_mem_Gamma hzG, integral_dirac]
      simp
      have hA : 0 ≤ semiMajor + semiMinor := by
        norm_num [semiMajor, semiMinor]
      have hB : 0 < semiMinor := by norm_num [semiMinor]
      exact div_nonneg (mul_nonneg hA hδ.le) hB.le
    · have h := TubeGap.re_sweep_interior hpos
      change |g z - z.re| ≤ (semiMajor + semiMinor) * δ / semiMinor
      have hgz : g z = ∫ y : ℂ, y.re ∂TubeEnergy.tubeSweep z := by
        simpa [hg]
      rw [hgz, h]
      simp
      have hC : 0 ≤ (semiMajor + semiMinor) * δ / semiMinor := by
        have hA : 0 ≤ semiMajor + semiMinor := by
          norm_num [semiMajor, semiMinor]
        have hB : 0 < semiMinor := by norm_num [semiMinor]
        exact div_nonneg (mul_nonneg hA hδ.le) hB.le
      exact hC
  have hνmass : M.nu.real Set.univ ≤ 1 := by
    have hκnonneg : 0 ≤ (Measure.map Complex.ofReal M.kappa).real Set.univ :=
      measureReal_nonneg
    linarith
  have hCnonneg : 0 ≤ (semiMajor + semiMinor) * δ / semiMinor := by
    have hA : 0 ≤ semiMajor + semiMinor := by
      norm_num [semiMajor, semiMinor]
    have hB : 0 < semiMinor := by norm_num [semiMinor]
    exact div_nonneg (mul_nonneg hA hδ.le) hB.le
  have hnorm := norm_integral_le_of_norm_le_const
    (μ := M.nu) (f := fun z : ℂ => g z - z.re)
    (C := (semiMajor + semiMinor) * δ / semiMinor)
    (hpoint.mono fun z hz => by simpa [Real.norm_eq_abs] using hz)
  have hbound : |∫ z : ℂ, (g z - z.re) ∂M.nu| ≤
      (semiMajor + semiMinor) * δ / semiMinor := by
    have hnorm' : |∫ z : ℂ, (g z - z.re) ∂M.nu| ≤
        ((semiMajor + semiMinor) * δ / semiMinor) * M.nu.real Set.univ := by
      simpa [Real.norm_eq_abs] using hnorm
    calc
      |∫ z : ℂ, (g z - z.re) ∂M.nu| ≤
          ((semiMajor + semiMinor) * δ / semiMinor) * M.nu.real Set.univ := hnorm'
      _ ≤ (semiMajor + semiMinor) * δ / semiMinor * 1 :=
        mul_le_mul_of_nonneg_left hνmass hCnonneg
      _ = (semiMajor + semiMinor) * δ / semiMinor := by ring
  have hdiff :
      (∫ z : ℂ, z.re ∂(p0TubeSweep M).eta) -
        ∫ z : ℂ, z.re ∂M.eta =
      ∫ z : ℂ, (g z - z.re) ∂M.nu := by
    rw [TubeGap.p0TubeSweep_eta, TubeGap.p0Tube_eta,
      integral_add_measure hκre hSweptRe,
      integral_add_measure hκre hνre, hbind,
      integral_sub hg_int hνre]
    ring
  rw [hdiff]
  exact hbound

/-! This is the remaining small analytic leaf.  Its field is the integrated
real-part displacement only; the shifted energy inequality is proved below
from this field and the existing 300δ ledger. -/

structure ShiftedTubeDisplacementHypothesis (δ : ℝ) : Prop where
  re_displacement :
    ∀ M : P0TubeAdmissibleMeasures δ,
      p0TubeFiniteEnergyCondition M →
      |(∫ z : ℂ, z.re ∂(p0TubeSweep M).eta) -
          ∫ z : ℂ, z.re ∂M.eta| ≤
        (semiMajor + semiMinor) * δ / semiMinor

/-! ## Elementary profile bounds needed by the algebraic bridge

These bounds are independent of the q-dependent envelope and cell leaves.
They keep the `sInf` domain explicit and avoid using the unfinished
concavity theorem from `ProducerAssembly`. -/

theorem shifted_re_integrable (N : P0AdmissibleMeasures) :
    Integrable (fun z : ℂ => z.re) N.eta := by
  apply Integrable.mono' (integrable_const (4 : ℝ))
    Complex.continuous_re.aestronglyMeasurable
  filter_upwards [EnergyLowerBound.eta_ae_norm_le N] with z hz
  simpa [Real.norm_eq_abs] using (Complex.abs_re_le_norm z).trans hz

theorem shifted_energy_value_ge_linear
    {lambda : ℝ} (hl : 0 ≤ lambda) {M : P0AdmissibleMeasures}
    (hM : p0PositiveEnergyDomain M) :
    -200 - 4 * lambda ≤ p0PositiveEnergyValue lambda M := by
  obtain ⟨hfin, hRe⟩ := hM
  have hE : (-200 : ℝ) ≤ p0RegularizedEnergyValue M :=
    EnergyLowerBound.p0RegularizedEnergyValue_ge M hfin
  have hmu : 0 ≤ ∫ t : ℝ, t ∂M.mu := by
    apply integral_nonneg_of_ae
    filter_upwards [EnergyLowerBound.mu_ae_mem M] with t ht
    have ht' : (1 / 2 : ℝ) ≤ t := ht
    exact le_trans (by norm_num) ht'
  have heta : ∫ z : ℂ, z.re ∂M.eta ≤ 4 := by
    have h := integral_mono_ae hRe (integrable_const (4 : ℝ)) (by
      filter_upwards [EnergyLowerBound.eta_ae_norm_le M] with z hz
      exact (Complex.re_le_norm z).trans hz)
    simpa using h
  have hbr : (-4 : ℝ) ≤ (∫ t : ℝ, t ∂M.mu) - ∫ z : ℂ, z.re ∂M.eta := by
    linarith
  have hmul := mul_le_mul_of_nonneg_left hbr hl
  unfold p0PositiveEnergyValue
  linarith

theorem shifted_energy_values_bddBelow {lambda : ℝ} (hl : 0 ≤ lambda) :
    BddBelow (p0PositiveEnergyValues lambda) := by
  refine ⟨-200 - 4 * lambda, ?_⟩
  rintro e ⟨M, hM, rfl⟩
  exact shifted_energy_value_ge_linear hl hM

/-! The elementary numerical absorption used at the top endpoint. -/

theorem shifted_log_eleven_half_lt :
    Real.log ((11 : ℝ) / 2) < (171 / 100 : ℝ) := by
  have hcheck :
      Li2Lean.P0.ConfigLogTaylor.logPolynomial (11 / 2 : ℚ) 40 +
        Li2Lean.P0.ConfigLogTaylor.logRemainder (11 / 2 : ℚ) 40 <
          (171 / 100 : ℚ) := by
    norm_num [Li2Lean.P0.ConfigLogTaylor.logPolynomial,
    Li2Lean.P0.ConfigLogTaylor.logRemainder,
    Li2Lean.P0.ConfigLogTaylor.logCoordinate,
    Finset.sum_range_succ]
  have hlog := Li2Lean.P0.ConfigLogTaylor.log_lt_of_rational
    (q := (11 / 2 : ℚ)) (upper := (171 / 100 : ℚ)) (by norm_num) 40 hcheck
  norm_num at hlog ⊢
  exact hlog

theorem shifted_lambda_coefficient_le_four
    {lambda : ℝ} (hl0 : 0 ≤ lambda)
    (hl : lambda ≤ Real.log ((11 : ℝ) / 2)) :
    lambda * ((semiMajor + semiMinor) / semiMinor) ≤ 4 := by
  have hlog : lambda ≤ (171 / 100 : ℝ) :=
    hl.trans shifted_log_eleven_half_lt.le
  have hratio : (semiMajor + semiMinor) / semiMinor ≤
      (212 / 100 : ℝ) := by
    norm_num [semiMajor, semiMinor]
  have hratio0 : 0 ≤ (semiMajor + semiMinor) / semiMinor := by
    norm_num [semiMajor, semiMinor]
  calc
    lambda * ((semiMajor + semiMinor) / semiMinor) ≤
        (171 / 100 : ℝ) * ((semiMajor + semiMinor) / semiMinor) :=
      mul_le_mul_of_nonneg_right hlog hratio0
    _ ≤ (171 / 100 : ℝ) * (212 / 100 : ℝ) :=
      mul_le_mul_of_nonneg_left hratio (by norm_num)
    _ ≤ 4 := by norm_num

/-! ## Shifted tube energy transfer

The profile bound is obtained by exhibiting the swept competitor in the
profile set.  The only open input is `ShiftedTubeDisplacementHypothesis`; the
q-dependent envelope and cell comparison are deliberately not mentioned. -/

noncomputable def p0TubePositiveEnergyValue {δ : ℝ} (lambda : ℝ)
    (M : P0TubeAdmissibleMeasures δ) : ℝ :=
  p0TubeRegularizedEnergyValue M + lambda *
    ((∫ t : ℝ, t ∂M.mu) - ∫ z : ℂ, z.re ∂M.eta)

theorem p0TubePositiveEnergy_ge_profile_of_displacement
    {lambda δ : ℝ}
    (hl0 : 0 ≤ lambda)
    (hl : lambda ≤ Real.log ((11 : ℝ) / 2))
    (hδ : 0 < δ)
    (hδmax : δ ≤ tubeRadiusMax)
    (hDisp : ShiftedTubeDisplacementHypothesis δ)
    (M : P0TubeAdmissibleMeasures δ)
    (hM : p0TubeFiniteEnergyCondition M) :
    p0PositiveEnergyProfileActual lambda - 304 * δ ≤
      p0TubePositiveEnergyValue lambda M := by
  have hSweepFin : P0FiniteEnergyCondition (p0TubeSweep M) :=
    p0TubeSweep_finite hδ.le hδmax M hM
  have hSweepRe : Integrable (fun z : ℂ => z.re) (p0TubeSweep M).eta :=
    shifted_re_integrable (p0TubeSweep M)
  have hProfile :
      p0PositiveEnergyProfileActual lambda ≤
        p0PositiveEnergyValue lambda (p0TubeSweep M) := by
    unfold p0PositiveEnergyProfileActual
    apply csInf_le (shifted_energy_values_bddBelow hl0)
    exact ⟨p0TubeSweep M, ⟨hSweepFin, hSweepRe⟩, rfl⟩
  have hcmp := TubeGap.p0Tube_energy_comparison_actual hδ hδmax M hM
  have hdisp := hDisp.re_displacement M hM
  have hdisp' :
      (∫ z : ℂ, z.re ∂M.eta) -
          ∫ z : ℂ, z.re ∂(p0TubeSweep M).eta ≤
        (semiMajor + semiMinor) * δ / semiMinor := by
    have habs :
        |(∫ z : ℂ, z.re ∂M.eta) -
            ∫ z : ℂ, z.re ∂(p0TubeSweep M).eta| ≤
          (semiMajor + semiMinor) * δ / semiMinor := by
      simpa [abs_sub_comm] using hdisp
    exact (le_abs_self _).trans habs
  have hshiftCoeff := shifted_lambda_coefficient_le_four hl0 hl
  have hshift :
      lambda * ((semiMajor + semiMinor) * δ / semiMinor) ≤ 4 * δ := by
    have hδ0 : 0 ≤ δ := hδ.le
    calc
      lambda * ((semiMajor + semiMinor) * δ / semiMinor) =
          (lambda * ((semiMajor + semiMinor) / semiMinor)) * δ := by ring
      _ ≤ 4 * δ := mul_le_mul_of_nonneg_right hshiftCoeff hδ0
  have henergy :
      p0PositiveEnergyValue lambda (p0TubeSweep M) -
          p0TubePositiveEnergyValue lambda M ≤ 304 * δ := by
    have hdisp_shift := mul_le_mul_of_nonneg_left hdisp' hl0
    have hidentity :
        p0PositiveEnergyValue lambda (p0TubeSweep M) -
            p0TubePositiveEnergyValue lambda M =
          (p0RegularizedEnergyValue (p0TubeSweep M) -
            p0TubeRegularizedEnergyValue M) +
          lambda * ((∫ z : ℂ, z.re ∂M.eta) -
            ∫ z : ℂ, z.re ∂(p0TubeSweep M).eta) := by
      simp [p0PositiveEnergyValue, p0TubePositiveEnergyValue,
        p0TubeSweep_mu]
      ring
    rw [hidentity]
    linarith [hcmp, hdisp_shift, hshift]
  calc
    p0PositiveEnergyProfileActual lambda - 304 * δ ≤
        p0PositiveEnergyValue lambda (p0TubeSweep M) - 304 * δ :=
      sub_le_sub_right hProfile _
    _ ≤ p0TubePositiveEnergyValue lambda M := by linarith [henergy]

/-! Concrete adapter: the displacement obligation above is proved from the
actual sweep, so callers need not pass a conclusion-shaped hypothesis. -/

theorem p0TubePositiveEnergy_ge_profile_actual
    {lambda δ : ℝ}
    (hl0 : 0 ≤ lambda)
    (hl : lambda ≤ Real.log ((11 : ℝ) / 2))
    (hδ : 0 < δ)
    (hδmax : δ ≤ tubeRadiusMax)
    (M : P0TubeAdmissibleMeasures δ)
    (hM : p0TubeFiniteEnergyCondition M) :
    p0PositiveEnergyProfileActual lambda - 304 * δ ≤
      p0TubePositiveEnergyValue lambda M := by
  exact p0TubePositiveEnergy_ge_profile_of_displacement hl0 hl hδ hδmax
    ⟨fun M hM => p0TubeSweep_re_displacement hδ hδmax M hM⟩ M hM

end

end Li2Lean.AllNAssembly
