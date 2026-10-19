/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B3.S0TCoreBound
import Li2Lean.B3.DenominatorIntegral
import Li2Lean.B3.S0TC1C4Actual

/-!
# C7 Dual Fields and One-Body Transfer (`H5-sub3`)

This module proves `v13_c7_fields_and_one_body_transfer` (`v-analytic.tex:561-601`),
closing Sub-bridge 3 of `H5-hcore`:

1. **Unconditional logarithmic-potential integrability (`§1`)**:
   proves `integrable_log_norm_sub_of_vBallBound_of_ae_norm_le` for any finite
   measure `μ` with `VBallBound μ A` and bounded support `∀ᵐ t ∂μ, ‖t‖ ≤ R`
   via a bounded layer-cake truncation on `Metric.closedBall w (1 / 2)`
   (`closedBall_bound_of_ballBound`, `Integrable.integral_eq_integral_meas_le`,
   `lintegral_tendsto_of_tendsto_of_monotone`, `hasFiniteIntegral_iff_ofReal`)
   together with a bounded far-field split on `(Metric.closedBall w (1 / 2))ᶜ`.
   Instantiates this for `P.measure.μx`, `P.measure.μv`, `P.measure.μz` to
   discharge the integrability premises of `s0T_reference_x_potential_transfer`,
   `s0T_reference_v_potential_transfer`, and `s0T_reference_z_potential_transfer`.
2. **Cross-kernel (`V.vCrossKernel`) and hatted-field Lipschitz transfer (`§2`)**:
   combines `s0T_reference_*_potential_transfer` with `denominator_log_lipschitz`
   and `abs_integral_sub_le_of_ae_abs_sub_le` to bound
   `|V.signedVFieldX ν (translatedAtom u m theta) - V.signedVFieldX ν u|`,
   `|V.signedVFieldV ν (translatedAtom u m theta) - V.signedVFieldV ν u|`, and
   `|V.signedVFieldZ ν (translatedAtom u m theta) - V.signedVFieldZ ν u|`.
3. **Smoothed-empirical-measure integration of the three hatted fields (`§3`)**:
   lifts the uniform circle bounds across `translatedCircleMeasure` and
   `translatedEmpiricalMeasure` for `V.signedVFieldX`, `V.signedVFieldV`,
   and `V.signedVFieldZ`.
4. **Endpoint-disk (`[0, 1/250]`), interior-field (`(1/250, 1]`), and one-body
   assembly (`§4–§5`)**:
   combines `P.facts.x_endpoint_disk`, `P.facts.v_endpoint_disk`, `P.facts.x_field`,
   `P.facts.v_field`, `P.facts.z_field`, `c7_negative_z_one_body_sum_bound`, and
   `p4_c7_positive_one_body_scalar` to prove `v13_c7_fields_and_one_body_transfer`.
-/

namespace Li2Lean.B3

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped BigOperators ENNReal

/-! ## 1. Unconditional logarithmic-potential integrability from `VBallBound` -/

/-- Near-ball integrability of `t ↦ Real.log ‖w - t‖` on `Metric.closedBall w (1 / 2)`
    for any finite measure `μ` satisfying `VBallBound μ A`. -/
theorem integrableOn_log_norm_sub_closedBall_half
    {μ : Measure ℂ} [IsFiniteMeasure μ] {A : ℝ}
    (hA : 0 ≤ A) (hball : VBallBound μ A) (w : ℂ) :
    IntegrableOn (fun t : ℂ => Real.log ‖w - t‖) (Metric.closedBall w (1 / 2)) μ := by
  let N : Set ℂ := Metric.closedBall w (1 / 2)
  have hN : MeasurableSet N := Metric.isClosed_closedBall.measurableSet
  let g : ℂ → ℝ := fun t => max 0 (-Real.log ‖w - t‖)
  let f : ℕ → ℂ → ℝ := fun k t => max 0 (min (k : ℝ) (-Real.log ‖w - t‖))
  have hg_meas : Measurable g :=
    measurable_const.max ((measurable_const.sub measurable_id).norm.log.neg)
  have hf_meas : ∀ k : ℕ, Measurable (f k) := fun k =>
    measurable_const.max (measurable_const.min ((measurable_const.sub measurable_id).norm.log.neg))
  have hf_nonneg : ∀ (k : ℕ) (t : ℂ), 0 ≤ f k t := fun _ _ => le_max_left 0 _
  have hf_le_k : ∀ (k : ℕ) (t : ℂ), f k t ≤ (k : ℝ) := fun k _ =>
    max_le (Nat.cast_nonneg k) (min_le_left _ _)
  have hf_int : ∀ k : ℕ, Integrable (f k) (μ.restrict N) := by
    intro k
    refine Integrable.of_bound (hf_meas k).aestronglyMeasurable (k : ℝ) ?_
    filter_upwards [] with t
    rw [Real.norm_eq_abs, abs_of_nonneg (hf_nonneg k t)]
    exact hf_le_k k t
  have hexp_int : IntegrableOn (fun s : ℝ => A * Real.exp (-s)) (Ioi (0 : ℝ)) volume := by
    simpa only [IntegrableOn] using (integrableOn_exp_neg_Ioi 0).const_mul A
  have hexp_eval : (∫ s in Ioi (0 : ℝ), A * Real.exp (-s)) = A := by
    rw [integral_const_mul, integral_exp_neg_Ioi, neg_zero, Real.exp_zero, mul_one]
  have hf_integral_le : ∀ k : ℕ, (∫ t, f k t ∂(μ.restrict N)) ≤ A := by
    intro k
    have hlayer : (∫ t, f k t ∂(μ.restrict N)) =
        ∫ s in Ioi (0 : ℝ), (μ.restrict N).real {t | s ≤ f k t} :=
      (hf_int k).integral_eq_integral_meas_le (ae_of_all _ (hf_nonneg k))
    let qk : ℝ → ℝ := fun s => (μ.restrict N).real {t | s ≤ f k t}
    have hqk_nonneg : ∀ s, 0 ≤ qk s := fun _ => measureReal_nonneg
    have hqk_anti : Antitone qk := by
      intro a b hab
      dsimp [qk]
      exact measureReal_mono (fun t ht => le_trans hab ht) (measure_ne_top _ _)
    have hqk_meas : Measurable qk := hqk_anti.measurable
    have hqk_le : ∀ {s : ℝ}, 0 < s → qk s ≤ A * Real.exp (-s) := by
      intro s hs
      have hset_meas : MeasurableSet {t : ℂ | s ≤ f k t} :=
        measurableSet_le measurable_const (hf_meas k)
      have hsub : {t : ℂ | s ≤ f k t} ∩ N ⊆ Metric.closedBall w (Real.exp (-s)) := by
        intro t ht
        have hs_f : s ≤ max 0 (min (k : ℝ) (-Real.log ‖w - t‖)) := ht.1
        have hs_min : s ≤ min (k : ℝ) (-Real.log ‖w - t‖) := by
          rcases le_max_iff.mp hs_f with h0 | hmin
          · linarith
          · exact hmin
        have hs_log : s ≤ -Real.log ‖w - t‖ := hs_min.trans (min_le_right _ _)
        have hpos : 0 < ‖w - t‖ := by
          by_contra hzero
          have hz0 : ‖w - t‖ = 0 := le_antisymm (le_of_not_gt hzero) (norm_nonneg _)
          rw [hz0, Real.log_zero, neg_zero] at hs_log
          linarith
        have hlog_le : Real.log ‖w - t‖ ≤ -s := by linarith
        have hexp : ‖w - t‖ ≤ Real.exp (-s) := by
          rw [← Real.exp_log hpos]
          exact Real.exp_le_exp.mpr hlog_le
        simpa [Metric.mem_closedBall, dist_comm, Complex.dist_eq] using hexp
      dsimp [qk]
      change ((μ.restrict N) {t : ℂ | s ≤ f k t}).toReal ≤ A * Real.exp (-s)
      rw [Measure.restrict_apply hset_meas]
      change μ.real ({t : ℂ | s ≤ f k t} ∩ N) ≤ A * Real.exp (-s)
      exact (measureReal_mono hsub (measure_ne_top μ _)).trans
        (closedBall_bound_of_ballBound hball (Real.exp_pos (-s)))
    have hqk_ae : ∀ᵐ s ∂volume.restrict (Ioi (0 : ℝ)), qk s ≤ A * Real.exp (-s) := by
      filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with s hs
      exact hqk_le hs
    have hqk_int : IntegrableOn qk (Ioi (0 : ℝ)) volume := by
      refine hexp_int.mono' hqk_meas.aestronglyMeasurable ?_
      filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with s hs
      rw [Real.norm_eq_abs, abs_of_nonneg (hqk_nonneg s)]
      exact hqk_le hs
    rw [hlayer]
    calc
      (∫ s in Ioi (0 : ℝ), qk s) ≤ ∫ s in Ioi (0 : ℝ), A * Real.exp (-s) :=
        integral_mono_ae hqk_int hexp_int hqk_ae
      _ = A := hexp_eval
  let fE : ℕ → ℂ → ℝ≥0∞ := fun k t => ENNReal.ofReal (f k t)
  let gE : ℂ → ℝ≥0∞ := fun t => ENNReal.ofReal (g t)
  have hfE_bound : ∀ k : ℕ, (∫⁻ t, fE k t ∂(μ.restrict N)) ≤ ENNReal.ofReal A := by
    intro k
    dsimp [fE]
    rw [← ofReal_integral_eq_lintegral_ofReal (hf_int k) (ae_of_all _ (hf_nonneg k))]
    exact ENNReal.ofReal_le_ofReal (hf_integral_le k)
  have hfE_meas : ∀ k : ℕ, AEMeasurable (fE k) (μ.restrict N) :=
    fun k => (hf_meas k).ennreal_ofReal.aemeasurable
  have hfE_mono : ∀ᵐ t ∂(μ.restrict N), Monotone (fun k : ℕ => fE k t) := by
    filter_upwards [] with t m n hmn
    apply ENNReal.ofReal_le_ofReal
    dsimp [f]
    exact max_le_max le_rfl (min_le_min (by exact_mod_cast hmn) le_rfl)
  have hfE_tend : ∀ᵐ t ∂(μ.restrict N), Tendsto (fun k : ℕ => fE k t) atTop (𝓝 (gE t)) := by
    filter_upwards [] with t
    obtain ⟨K, hK⟩ := exists_nat_ge (-Real.log ‖w - t‖)
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop K] with k hk
    have hle : -Real.log ‖w - t‖ ≤ (k : ℝ) := hK.trans (by exact_mod_cast hk)
    dsimp [fE, gE, f, g]
    rw [min_eq_right hle]
  have hlim := lintegral_tendsto_of_tendsto_of_monotone hfE_meas hfE_mono hfE_tend
  have hgE_le : (∫⁻ t, gE t ∂(μ.restrict N)) ≤ ENNReal.ofReal A :=
    le_of_tendsto' hlim hfE_bound
  have hg_nonneg : 0 ≤ᵐ[μ.restrict N] g := ae_of_all _ (fun _ => le_max_left 0 _)
  have hg_int : Integrable g (μ.restrict N) := by
    refine ⟨hg_meas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal hg_nonneg]
    exact lt_of_le_of_lt hgE_le ENNReal.ofReal_lt_top
  have hneg_int : IntegrableOn (fun t : ℂ => -Real.log ‖w - t‖) N μ := by
    refine hg_int.congr ?_
    filter_upwards [ae_restrict_mem hN] with t ht
    have hdist : ‖w - t‖ ≤ 1 / 2 := by
      simpa [N, Metric.mem_closedBall, dist_comm, Complex.dist_eq] using ht
    have hlog_nonpos : Real.log ‖w - t‖ ≤ 0 :=
      Real.log_nonpos (norm_nonneg _) (by linarith)
    dsimp [g]
    exact max_eq_right (neg_nonneg.mpr hlog_nonpos)
  simpa [N] using hneg_int.neg

/-- Far-field integrability of `t ↦ Real.log ‖w - t‖` on `(Metric.closedBall w (1 / 2))ᶜ`
    for any finite measure `μ` with bounded support `∀ᵐ t ∂μ, ‖t‖ ≤ R`. -/
theorem integrableOn_log_norm_sub_compl_closedBall_half
    {μ : Measure ℂ} [IsFiniteMeasure μ] {R : ℝ}
    (hR : 0 ≤ R) (hbdd : ∀ᵐ t ∂μ, ‖t‖ ≤ R) (w : ℂ) :
    IntegrableOn (fun t : ℂ => Real.log ‖w - t‖) (Metric.closedBall w (1 / 2))ᶜ μ := by
  let N : Set ℂ := Metric.closedBall w (1 / 2)
  have hN : MeasurableSet N := Metric.isClosed_closedBall.measurableSet
  let U : ℝ := max 1 (‖w‖ + R)
  let M : ℝ := max |Real.log (1 / 2)| |Real.log U|
  have hmeas : Measurable (fun t : ℂ => Real.log ‖w - t‖) :=
    (measurable_const.sub measurable_id).norm.log
  change IntegrableOn (fun t : ℂ => Real.log ‖w - t‖) Nᶜ μ
  apply Measure.integrableOn_of_bounded
    (μ := μ) (s := Nᶜ) (f := fun t : ℂ => Real.log ‖w - t‖) (M := M)
    (measure_ne_top μ Nᶜ)
  · exact hmeas.aestronglyMeasurable
  have hbdd_restrict : ∀ᵐ t ∂(μ.restrict Nᶜ), ‖t‖ ≤ R := ae_restrict_of_ae hbdd
  filter_upwards [ae_restrict_mem hN.compl, hbdd_restrict] with t ht htR
  have hdist : (1 / 2 : ℝ) < ‖w - t‖ := by
    have hnot : ¬ dist t w ≤ 1 / 2 := fun h => ht (Metric.mem_closedBall.mpr h)
    simpa [dist_comm, Complex.dist_eq] using lt_of_not_ge hnot
  have hpos : 0 < ‖w - t‖ := lt_trans (by norm_num) hdist
  have hupper : ‖w - t‖ ≤ U := by
    have htri : ‖w - t‖ ≤ ‖w‖ + R := by
      calc
        ‖w - t‖ ≤ ‖w‖ + ‖t‖ := norm_sub_le _ _
        _ ≤ ‖w‖ + R := by linarith
    exact htri.trans (le_max_right 1 _)
  have hlo : Real.log (1 / 2) ≤ Real.log ‖w - t‖ :=
    Real.log_le_log (by norm_num) hdist.le
  have hhi : Real.log ‖w - t‖ ≤ Real.log U :=
    Real.log_le_log hpos hupper
  dsimp [M]
  rw [abs_le]
  constructor
  · linarith [neg_abs_le (Real.log (1 / 2)), le_max_left |Real.log (1 / 2)| |Real.log U|]
  · linarith [le_abs_self (Real.log U), le_max_right |Real.log (1 / 2)| |Real.log U|]

/-- Full-space integrability of `t ↦ Real.log ‖w - t‖` for any finite measure `μ`
    satisfying `VBallBound μ A` and `∀ᵐ t ∂μ, ‖t‖ ≤ R`. -/
theorem integrable_log_norm_sub_of_vBallBound_of_ae_norm_le
    {μ : Measure ℂ} [IsFiniteMeasure μ] {A R : ℝ}
    (hA : 0 ≤ A) (hR : 0 ≤ R)
    (hball : VBallBound μ A) (hbdd : ∀ᵐ t ∂μ, ‖t‖ ≤ R) (w : ℂ) :
    Integrable (fun t : ℂ => Real.log ‖w - t‖) μ := by
  have hnear := integrableOn_log_norm_sub_closedBall_half hA hball w
  have hfar := integrableOn_log_norm_sub_compl_closedBall_half hR hbdd w
  have hunion := hnear.union hfar
  rw [Set.union_compl_self, integrableOn_univ] at hunion
  exact hunion

theorem referenceMeasure_x_norm_ae_le_one'
    {q : ℕ} {hq : SignedVBaseRange q} (P : VReferencePackage q hq) :
    ∀ᵐ w ∂P.measure.μx, ‖w‖ ≤ 1 := by
  have hmem : ∀ᵐ w ∂P.measure.μx, w ∈ Complex.ofReal '' Set.Icc (0 : ℝ) 1 := by
    rw [ae_iff]
    exact P.facts.x_support
  filter_upwards [hmem] with w hw
  rcases hw with ⟨r, hr, hwr⟩
  rw [← hwr]
  exact norm_ofReal_le_one_of_mem_Icc hr

theorem referenceMeasure_v_norm_ae_le_one'
    {q : ℕ} {hq : SignedVBaseRange q} (P : VReferencePackage q hq) :
    ∀ᵐ w ∂P.measure.μv, ‖w‖ ≤ 1 := by
  have hmem : ∀ᵐ w ∂P.measure.μv, w ∈ Complex.ofReal '' Set.Icc (0 : ℝ) 1 := by
    rw [ae_iff]
    exact P.facts.v_support
  filter_upwards [hmem] with w hw
  rcases hw with ⟨r, hr, hwr⟩
  rw [← hwr]
  exact norm_ofReal_le_one_of_mem_Icc hr

theorem referenceMeasure_z_norm_ae_le_q'
    {q : ℕ} {hq : SignedVBaseRange q} (P : VReferencePackage q hq) :
    ∀ᵐ w ∂P.measure.μz, ‖w‖ ≤ (q : ℝ) := by
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq.1
  have hmem : ∀ᵐ w ∂P.measure.μz,
      w ∈ (Complex.ofReal '' Set.Icc (-(q : ℝ)) (-3 / 5)) ∪ Metric.sphere 0 (3 / 5) := by
    rw [ae_iff]
    exact P.facts.z_support_source
  filter_upwards [hmem] with w hw
  rcases hw with ⟨r, hr, rfl⟩ | hw
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith [hr.2])]
    linarith [hr.1]
  · have hdist : ‖w‖ = (3 / 5 : ℝ) := by
      simpa [Metric.mem_sphere, dist_zero_right] using hw
    linarith

/-- Unconditional integrability of `t ↦ Real.log ‖w - t‖` against `P.measure.μx`. -/
theorem integrable_log_norm_sub_reference_x
    {q : ℕ} {hq : SignedVBaseRange q} (P : VReferencePackage q hq) (w : ℂ) :
    Integrable (fun t : ℂ => Real.log ‖w - t‖) P.measure.μx := by
  letI : IsFiniteMeasure P.measure.μx := ⟨lt_top_iff_ne_top.mpr P.measure.finite_x⟩
  exact integrable_log_norm_sub_of_vBallBound_of_ae_norm_le
    P.facts.Ax_nonneg zero_le_one P.facts.x_ball (referenceMeasure_x_norm_ae_le_one' P) w

/-- Unconditional integrability of `t ↦ Real.log ‖w - t‖` against `P.measure.μv`. -/
theorem integrable_log_norm_sub_reference_v
    {q : ℕ} {hq : SignedVBaseRange q} (P : VReferencePackage q hq) (w : ℂ) :
    Integrable (fun t : ℂ => Real.log ‖w - t‖) P.measure.μv := by
  letI : IsFiniteMeasure P.measure.μv := ⟨lt_top_iff_ne_top.mpr P.measure.finite_v⟩
  exact integrable_log_norm_sub_of_vBallBound_of_ae_norm_le
    P.facts.Av_nonneg zero_le_one P.facts.v_ball (referenceMeasure_v_norm_ae_le_one' P) w

/-- Unconditional integrability of `t ↦ Real.log ‖w - t‖` against `P.measure.μz`. -/
theorem integrable_log_norm_sub_reference_z
    {q : ℕ} {hq : SignedVBaseRange q} (P : VReferencePackage q hq) (w : ℂ) :
    Integrable (fun t : ℂ => Real.log ‖w - t‖) P.measure.μz := by
  letI : IsFiniteMeasure P.measure.μz := ⟨lt_top_iff_ne_top.mpr P.measure.finite_z⟩
  exact integrable_log_norm_sub_of_vBallBound_of_ae_norm_le
    P.facts.Az_nonneg (Nat.cast_nonneg q) P.facts.z_ball (referenceMeasure_z_norm_ae_le_q' P) w

/-- Unconditional wrapper around `s0T_reference_x_potential_transfer`. -/
theorem s0T_reference_x_potential_transfer_unconditional
    {q m : ℕ} {hq : SignedVBaseRange q} (P : VReferencePackage q hq)
    (hm : 64 ≤ m) (u : ℂ) (theta : ℝ) :
    |(∫ t : ℂ, Real.log ‖translatedAtom u m theta - t‖ ∂P.measure.μx) -
      ∫ t : ℂ, Real.log ‖u - t‖ ∂P.measure.μx| ≤
      densityTransferBudget P.Ax xMass * (3 * smoothingEpsilon m) *
        (1 + Real.log ((m : ℝ) ^ 2 / 3)) :=
  s0T_reference_x_potential_transfer P hm u theta
    (integrable_log_norm_sub_reference_x P u)
    (integrable_log_norm_sub_reference_x P (translatedAtom u m theta))

/-- Unconditional wrapper around `s0T_reference_v_potential_transfer`. -/
theorem s0T_reference_v_potential_transfer_unconditional
    {q m : ℕ} {hq : SignedVBaseRange q} (P : VReferencePackage q hq)
    (hm : 64 ≤ m) (u : ℂ) (theta : ℝ) :
    |(∫ t : ℂ, Real.log ‖translatedAtom u m theta - t‖ ∂P.measure.μv) -
      ∫ t : ℂ, Real.log ‖u - t‖ ∂P.measure.μv| ≤
      densityTransferBudget P.Av vMass * (3 * smoothingEpsilon m) *
        (1 + Real.log ((m : ℝ) ^ 2 / 3)) :=
  s0T_reference_v_potential_transfer P hm u theta
    (integrable_log_norm_sub_reference_v P u)
    (integrable_log_norm_sub_reference_v P (translatedAtom u m theta))

/-- Unconditional wrapper around `s0T_reference_z_potential_transfer`. -/
theorem s0T_reference_z_potential_transfer_unconditional
    {q m : ℕ} {hq : SignedVBaseRange q} (P : VReferencePackage q hq)
    (hm : 64 ≤ m) (u : ℂ) (theta : ℝ) :
    |(∫ t : ℂ, Real.log ‖translatedAtom u m theta - t‖ ∂P.measure.μz) -
      ∫ t : ℂ, Real.log ‖u - t‖ ∂P.measure.μz| ≤
      densityTransferBudget P.Az zMass * (3 * smoothingEpsilon m) *
        (1 + Real.log ((m : ℝ) ^ 2 / 3)) :=
  s0T_reference_z_potential_transfer P hm u theta
    (integrable_log_norm_sub_reference_z P u)
    (integrable_log_norm_sub_reference_z P (translatedAtom u m theta))

/-! ## 2. Cross-kernel (`V.vCrossKernel`) and hatted-field Lipschitz transfer -/

private theorem integrable_vCrossKernel_of_ae_norm_le_one_right
    {q : ℕ} (hq : 2 ≤ q) {μ : Measure ℂ} [IsFiniteMeasure μ]
    (hμ : ∀ᵐ t ∂μ, ‖t‖ ≤ 1) {z : ℂ} (hz : ‖z‖ ≤ denominatorTubeRadius) :
    Integrable (fun t : ℂ => V.vCrossKernel q z t) μ := by
  have hden : 0 < (q : ℝ) - denominatorTubeRadius ^ 2 := by
    norm_num [denominatorTubeRadius]
    have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    nlinarith
  have hmeas : Measurable (fun t : ℂ => V.vCrossKernel q z t) := by
    unfold V.vCrossKernel
    fun_prop
  refine Integrable.of_bound hmeas.aestronglyMeasurable
    (max |Real.log ((q : ℝ) + denominatorTubeRadius ^ 2)|
      |Real.log ((q : ℝ) - denominatorTubeRadius ^ 2)|) ?_
  filter_upwards [hμ] with t ht
  have htR : ‖t‖ ≤ denominatorTubeRadius := by
    unfold denominatorTubeRadius
    linarith
  have hprod : ‖z * t‖ ≤ denominatorTubeRadius ^ 2 := by
    rw [norm_mul]
    calc
      ‖z‖ * ‖t‖ ≤ denominatorTubeRadius * denominatorTubeRadius :=
        mul_le_mul hz htR (norm_nonneg _) (by norm_num [denominatorTubeRadius])
      _ = denominatorTubeRadius ^ 2 := by ring
  have hlo : (q : ℝ) - denominatorTubeRadius ^ 2 ≤ ‖(q : ℂ) + z * t‖ :=
    denominator_norm_lower hq hprod
  have hhi : ‖(q : ℂ) + z * t‖ ≤ (q : ℝ) + denominatorTubeRadius ^ 2 := by
    have hqnorm : ‖(q : ℂ)‖ = (q : ℝ) := by norm_cast
    calc
      ‖(q : ℂ) + z * t‖ ≤ ‖(q : ℂ)‖ + ‖z * t‖ := norm_add_le _ _
      _ ≤ (q : ℝ) + denominatorTubeRadius ^ 2 := by rw [hqnorm]; linarith
  have hloglo := Real.log_le_log hden hlo
  have hloghi := Real.log_le_log (lt_of_lt_of_le hden hlo) hhi
  change |Real.log ‖(q : ℂ) + z * t‖| ≤ _
  rw [abs_le]
  constructor
  · linarith [neg_abs_le (Real.log ((q : ℝ) - denominatorTubeRadius ^ 2)),
      le_max_right |Real.log ((q : ℝ) + denominatorTubeRadius ^ 2)|
        |Real.log ((q : ℝ) - denominatorTubeRadius ^ 2)|]
  · linarith [le_abs_self (Real.log ((q : ℝ) + denominatorTubeRadius ^ 2)),
      le_max_left |Real.log ((q : ℝ) + denominatorTubeRadius ^ 2)|
        |Real.log ((q : ℝ) - denominatorTubeRadius ^ 2)|]

private theorem integrable_vCrossKernel_of_ae_norm_le_one_left
    {q : ℕ} (hq : 2 ≤ q) {μ : Measure ℂ} [IsFiniteMeasure μ]
    (hμ : ∀ᵐ t ∂μ, ‖t‖ ≤ 1) {z : ℂ} (hz : ‖z‖ ≤ denominatorTubeRadius) :
    Integrable (fun t : ℂ => V.vCrossKernel q t z) μ := by
  have h := integrable_vCrossKernel_of_ae_norm_le_one_right hq hμ hz
  refine h.congr (ae_of_all _ (fun t => ?_))
  simp [V.vCrossKernel, mul_comm]

theorem s0T_reference_vCross_x_transfer
    {q m : ℕ} {hq : SignedVBaseRange q} (P : VReferencePackage q hq)
    (hm : 64 ≤ m) {u : ℂ} (hu : ‖u‖ ≤ 1) (theta : ℝ) :
    |(∫ t : ℂ, V.vCrossKernel P.measure.q (translatedAtom u m theta) t ∂P.measure.μv) -
      ∫ t : ℂ, V.vCrossKernel P.measure.q u t ∂P.measure.μv| ≤
      (15 / 4 : ℝ) * denominatorLipschitz q * smoothingEpsilon m := by
  letI : IsFiniteMeasure P.measure.μv := ⟨lt_top_iff_ne_top.mpr P.measure.finite_v⟩
  have hmpos : 0 < m := by omega
  have huR : ‖u‖ ≤ denominatorTubeRadius := by
    unfold denominatorTubeRadius
    linarith
  have hwR : ‖translatedAtom u m theta‖ ≤ denominatorTubeRadius :=
    translatedAtom_norm_le_one_add_three_div_4096 m theta hm hu
  have hq_eq := P.facts.q_eq
  rw [hq_eq]
  have hw_int := integrable_vCrossKernel_of_ae_norm_le_one_right hq.1
    (referenceMeasure_v_norm_ae_le_one' P) hwR
  have hu_int := integrable_vCrossKernel_of_ae_norm_le_one_right hq.1
    (referenceMeasure_v_norm_ae_le_one' P) huR
  have hL : 0 ≤ denominatorLipschitz q := (denominatorLipschitz_pos hq.1).le
  have heps : 0 ≤ smoothingEpsilon m := (smoothingEpsilon_pos hmpos).le
  have hpoint : ∀ᵐ t ∂P.measure.μv,
      |V.vCrossKernel q (translatedAtom u m theta) t - V.vCrossKernel q u t| ≤
        3 * denominatorLipschitz q * smoothingEpsilon m := by
    filter_upwards [referenceMeasure_v_norm_ae_le_one' P] with t ht
    have htR : ‖t‖ ≤ denominatorTubeRadius := by
      unfold denominatorTubeRadius
      linarith
    have hlip := denominator_log_lipschitz hq.1 (translatedAtom u m theta) t u t
      hwR htR huR htR
    have hmul : ‖translatedAtom u m theta * t - u * t‖ ≤ 3 * smoothingEpsilon m := by
      rw [show translatedAtom u m theta * t - u * t =
          (translatedAtom u m theta - u) * t by ring, norm_mul]
      calc
        ‖translatedAtom u m theta - u‖ * ‖t‖ ≤
            (3 * smoothingEpsilon m) * 1 :=
          mul_le_mul (translatedAtom_dist_le_threeEpsilon u m theta hmpos) ht
            (norm_nonneg _) (by positivity)
        _ = 3 * smoothingEpsilon m := mul_one _
    unfold V.vCrossKernel
    calc
      |Real.log ‖(q : ℂ) + translatedAtom u m theta * t‖ - Real.log ‖(q : ℂ) + u * t‖| ≤
          denominatorLipschitz q * ‖translatedAtom u m theta * t - u * t‖ := hlip
      _ ≤ denominatorLipschitz q * (3 * smoothingEpsilon m) :=
        mul_le_mul_of_nonneg_left hmul hL
      _ = 3 * denominatorLipschitz q * smoothingEpsilon m := by ring
  have hmass : P.measure.μv.real Set.univ = (5 / 4 : ℝ) := by
    simp [Measure.real, P.measure.mass_v]
  have habs := abs_integral_sub_le_of_ae_abs_sub_le P.measure.μv hw_int hu_int hpoint
    (by positivity)
  rw [hmass] at habs
  linarith

theorem s0T_reference_vCross_v_transfer
    {q m : ℕ} {hq : SignedVBaseRange q} (P : VReferencePackage q hq)
    (hm : 64 ≤ m) {u : ℂ} (hu : ‖u‖ ≤ 1) (theta : ℝ) :
    |(∫ t : ℂ, V.vCrossKernel P.measure.q t (translatedAtom u m theta) ∂P.measure.μx) -
      ∫ t : ℂ, V.vCrossKernel P.measure.q t u ∂P.measure.μx| ≤
      3 * denominatorLipschitz q * smoothingEpsilon m := by
  letI : IsFiniteMeasure P.measure.μx := ⟨lt_top_iff_ne_top.mpr P.measure.finite_x⟩
  have hmpos : 0 < m := by omega
  have huR : ‖u‖ ≤ denominatorTubeRadius := by
    unfold denominatorTubeRadius
    linarith
  have hwR : ‖translatedAtom u m theta‖ ≤ denominatorTubeRadius :=
    translatedAtom_norm_le_one_add_three_div_4096 m theta hm hu
  rw [P.facts.q_eq]
  have hw_int := integrable_vCrossKernel_of_ae_norm_le_one_left hq.1
    (referenceMeasure_x_norm_ae_le_one' P) hwR
  have hu_int := integrable_vCrossKernel_of_ae_norm_le_one_left hq.1
    (referenceMeasure_x_norm_ae_le_one' P) huR
  have hL : 0 ≤ denominatorLipschitz q := (denominatorLipschitz_pos hq.1).le
  have heps : 0 ≤ smoothingEpsilon m := (smoothingEpsilon_pos hmpos).le
  have hpoint : ∀ᵐ t ∂P.measure.μx,
      |V.vCrossKernel q t (translatedAtom u m theta) - V.vCrossKernel q t u| ≤
        3 * denominatorLipschitz q * smoothingEpsilon m := by
    filter_upwards [referenceMeasure_x_norm_ae_le_one' P] with t ht
    have htR : ‖t‖ ≤ denominatorTubeRadius := by
      unfold denominatorTubeRadius
      linarith
    have hlip := denominator_log_lipschitz hq.1 t (translatedAtom u m theta) t u
      htR hwR htR huR
    have hmul : ‖t * translatedAtom u m theta - t * u‖ ≤ 3 * smoothingEpsilon m := by
      rw [show t * translatedAtom u m theta - t * u =
          t * (translatedAtom u m theta - u) by ring, norm_mul]
      calc
        ‖t‖ * ‖translatedAtom u m theta - u‖ ≤
            1 * (3 * smoothingEpsilon m) :=
          mul_le_mul ht (translatedAtom_dist_le_threeEpsilon u m theta hmpos)
            (norm_nonneg _) zero_le_one
        _ = 3 * smoothingEpsilon m := one_mul _
    unfold V.vCrossKernel
    calc
      |Real.log ‖(q : ℂ) + t * translatedAtom u m theta‖ - Real.log ‖(q : ℂ) + t * u‖| ≤
          denominatorLipschitz q * ‖t * translatedAtom u m theta - t * u‖ := hlip
      _ ≤ denominatorLipschitz q * (3 * smoothingEpsilon m) :=
        mul_le_mul_of_nonneg_left hmul hL
      _ = 3 * denominatorLipschitz q * smoothingEpsilon m := by ring
  have hmass : P.measure.μx.real Set.univ = 1 := by
    simp [Measure.real, P.measure.mass_x]
  have habs := abs_integral_sub_le_of_ae_abs_sub_le P.measure.μx hw_int hu_int hpoint
    (by positivity)
  rw [hmass, mul_one] at habs
  exact habs

/-- Pointwise two-sided transfer for `V.signedVFieldX P.measure` at a smoothed atom. -/
theorem s0T_signedVFieldX_translatedAtom_abs_sub_le
    {q m : ℕ} {hq : SignedVBaseRange q} (P : VReferencePackage q hq)
    (hm : 64 ≤ m) {u : ℂ} (hu : ‖u‖ ≤ 1) (theta : ℝ) :
    |V.signedVFieldX P.measure (translatedAtom u m theta) -
      V.signedVFieldX P.measure u| ≤
      2 * densityTransferBudget P.Ax xMass * (3 * smoothingEpsilon m) *
        (1 + Real.log ((m : ℝ) ^ 2 / 3)) +
      (15 / 4 : ℝ) * denominatorLipschitz q * smoothingEpsilon m := by
  have hx := s0T_reference_x_potential_transfer_unconditional P hm u theta
  have hcross := s0T_reference_vCross_x_transfer P hm hu theta
  unfold V.signedVFieldX
  have hdecomp :
      (2 * (∫ t : ℂ, Real.log ‖translatedAtom u m theta - t‖ ∂P.measure.μx) -
        ∫ t : ℂ, V.vCrossKernel P.measure.q (translatedAtom u m theta) t ∂P.measure.μv) -
      (2 * (∫ t : ℂ, Real.log ‖u - t‖ ∂P.measure.μx) -
        ∫ t : ℂ, V.vCrossKernel P.measure.q u t ∂P.measure.μv) =
      2 * ((∫ t : ℂ, Real.log ‖translatedAtom u m theta - t‖ ∂P.measure.μx) -
        ∫ t : ℂ, Real.log ‖u - t‖ ∂P.measure.μx) -
      ((∫ t : ℂ, V.vCrossKernel P.measure.q (translatedAtom u m theta) t ∂P.measure.μv) -
        ∫ t : ℂ, V.vCrossKernel P.measure.q u t ∂P.measure.μv) := by ring
  rw [hdecomp]
  calc
    |2 * ((∫ t : ℂ, Real.log ‖translatedAtom u m theta - t‖ ∂P.measure.μx) -
        ∫ t : ℂ, Real.log ‖u - t‖ ∂P.measure.μx) -
      ((∫ t : ℂ, V.vCrossKernel P.measure.q (translatedAtom u m theta) t ∂P.measure.μv) -
        ∫ t : ℂ, V.vCrossKernel P.measure.q u t ∂P.measure.μv)| ≤
      |2 * ((∫ t : ℂ, Real.log ‖translatedAtom u m theta - t‖ ∂P.measure.μx) -
        ∫ t : ℂ, Real.log ‖u - t‖ ∂P.measure.μx)| +
      |(∫ t : ℂ, V.vCrossKernel P.measure.q (translatedAtom u m theta) t ∂P.measure.μv) -
        ∫ t : ℂ, V.vCrossKernel P.measure.q u t ∂P.measure.μv| := abs_sub _ _
    _ = 2 * |(∫ t : ℂ, Real.log ‖translatedAtom u m theta - t‖ ∂P.measure.μx) -
        ∫ t : ℂ, Real.log ‖u - t‖ ∂P.measure.μx| +
      |(∫ t : ℂ, V.vCrossKernel P.measure.q (translatedAtom u m theta) t ∂P.measure.μv) -
        ∫ t : ℂ, V.vCrossKernel P.measure.q u t ∂P.measure.μv| := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    _ ≤ 2 * densityTransferBudget P.Ax xMass * (3 * smoothingEpsilon m) *
          (1 + Real.log ((m : ℝ) ^ 2 / 3)) +
        (15 / 4 : ℝ) * denominatorLipschitz q * smoothingEpsilon m := by
      linarith

/-- Pointwise two-sided transfer for `V.signedVFieldV P.measure` at a smoothed atom. -/
theorem s0T_signedVFieldV_translatedAtom_abs_sub_le
    {q m : ℕ} {hq : SignedVBaseRange q} (P : VReferencePackage q hq)
    (hm : 64 ≤ m) {u : ℂ} (hu : ‖u‖ ≤ 1) (theta : ℝ) :
    |V.signedVFieldV P.measure (translatedAtom u m theta) -
      V.signedVFieldV P.measure u| ≤
      (2 * densityTransferBudget P.Av vMass + densityTransferBudget P.Az zMass) *
        (3 * smoothingEpsilon m) * (1 + Real.log ((m : ℝ) ^ 2 / 3)) +
      3 * denominatorLipschitz q * smoothingEpsilon m := by
  have hv := s0T_reference_v_potential_transfer_unconditional P hm u theta
  have hz := s0T_reference_z_potential_transfer_unconditional P hm u theta
  have hcross := s0T_reference_vCross_v_transfer P hm hu theta
  unfold V.signedVFieldV
  let dv := (∫ t : ℂ, Real.log ‖translatedAtom u m theta - t‖ ∂P.measure.μv) -
    ∫ t : ℂ, Real.log ‖u - t‖ ∂P.measure.μv
  let dz := (∫ t : ℂ, Real.log ‖translatedAtom u m theta - t‖ ∂P.measure.μz) -
    ∫ t : ℂ, Real.log ‖u - t‖ ∂P.measure.μz
  let dc := (∫ t : ℂ, V.vCrossKernel P.measure.q t (translatedAtom u m theta) ∂P.measure.μx) -
    ∫ t : ℂ, V.vCrossKernel P.measure.q t u ∂P.measure.μx
  have hdecomp :
      (2 * (∫ t : ℂ, Real.log ‖translatedAtom u m theta - t‖ ∂P.measure.μv) +
        (∫ t : ℂ, Real.log ‖translatedAtom u m theta - t‖ ∂P.measure.μz) -
        ∫ t : ℂ, V.vCrossKernel P.measure.q t (translatedAtom u m theta) ∂P.measure.μx) -
      (2 * (∫ t : ℂ, Real.log ‖u - t‖ ∂P.measure.μv) +
        (∫ t : ℂ, Real.log ‖u - t‖ ∂P.measure.μz) -
        ∫ t : ℂ, V.vCrossKernel P.measure.q t u ∂P.measure.μx) =
      (2 * dv + dz) - dc := by
    dsimp [dv, dz, dc]
    ring
  rw [hdecomp]
  have htri1 : |(2 * dv + dz) - dc| ≤ |2 * dv + dz| + |dc| := abs_sub _ _
  have htri2 : |2 * dv + dz| ≤ 2 * |dv| + |dz| := by
    calc
      |2 * dv + dz| ≤ |2 * dv| + |dz| := abs_add_le _ _
      _ = 2 * |dv| + |dz| := by rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  change |dv| ≤ _ at hv
  change |dz| ≤ _ at hz
  change |dc| ≤ _ at hcross
  linarith

/-- Pointwise two-sided transfer for `V.signedVFieldZ P.measure` at a smoothed atom. -/
theorem s0T_signedVFieldZ_translatedAtom_abs_sub_le
    {q m : ℕ} {hq : SignedVBaseRange q} (P : VReferencePackage q hq)
    (hm : 64 ≤ m) (u : ℂ) (theta : ℝ) :
    |V.signedVFieldZ P.measure (translatedAtom u m theta) -
      V.signedVFieldZ P.measure u| ≤
      (2 * densityTransferBudget P.Az zMass + densityTransferBudget P.Av vMass) *
        (3 * smoothingEpsilon m) * (1 + Real.log ((m : ℝ) ^ 2 / 3)) := by
  have hz := s0T_reference_z_potential_transfer_unconditional P hm u theta
  have hv := s0T_reference_v_potential_transfer_unconditional P hm u theta
  unfold V.signedVFieldZ
  let dz := (∫ t : ℂ, Real.log ‖translatedAtom u m theta - t‖ ∂P.measure.μz) -
    ∫ t : ℂ, Real.log ‖u - t‖ ∂P.measure.μz
  let dv := (∫ t : ℂ, Real.log ‖translatedAtom u m theta - t‖ ∂P.measure.μv) -
    ∫ t : ℂ, Real.log ‖u - t‖ ∂P.measure.μv
  have hdecomp :
      (2 * (∫ t : ℂ, Real.log ‖translatedAtom u m theta - t‖ ∂P.measure.μz) +
        ∫ t : ℂ, Real.log ‖translatedAtom u m theta - t‖ ∂P.measure.μv) -
      (2 * (∫ t : ℂ, Real.log ‖u - t‖ ∂P.measure.μz) +
        ∫ t : ℂ, Real.log ‖u - t‖ ∂P.measure.μv) =
      2 * dz + dv := by
    dsimp [dz, dv]
    ring
  rw [hdecomp]
  have htri : |2 * dz + dv| ≤ 2 * |dz| + |dv| := by
    calc
      |2 * dz + dv| ≤ |2 * dz| + |dv| := abs_add_le _ _
      _ = 2 * |dz| + |dv| := by rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  change |dz| ≤ _ at hz
  change |dv| ≤ _ at hv
  linarith

/-! ## 3. Measurability and Smoothed-Empirical-Measure Integration of the Hatted Fields -/

private theorem stronglyMeasurable_log_potential
    (μ : Measure ℂ) [IsFiniteMeasure μ] :
    StronglyMeasurable (fun w : ℂ => ∫ t : ℂ, Real.log ‖w - t‖ ∂μ) := by
  apply StronglyMeasurable.integral_prod_right
  fun_prop

private theorem stronglyMeasurable_vCross_left
    (q : ℕ) (μ : Measure ℂ) [IsFiniteMeasure μ] :
    StronglyMeasurable (fun w : ℂ => ∫ t : ℂ, V.vCrossKernel q w t ∂μ) := by
  unfold V.vCrossKernel
  apply StronglyMeasurable.integral_prod_right
  fun_prop

private theorem stronglyMeasurable_vCross_right
    (q : ℕ) (μ : Measure ℂ) [IsFiniteMeasure μ] :
    StronglyMeasurable (fun w : ℂ => ∫ t : ℂ, V.vCrossKernel q t w ∂μ) := by
  unfold V.vCrossKernel
  apply StronglyMeasurable.integral_prod_right
  fun_prop

theorem measurable_signedVFieldX (M : V.SignedVMeasures) :
    Measurable (V.signedVFieldX M) := by
  letI : IsFiniteMeasure M.μx := ⟨lt_top_iff_ne_top.mpr M.finite_x⟩
  letI : IsFiniteMeasure M.μv := ⟨lt_top_iff_ne_top.mpr M.finite_v⟩
  have h : StronglyMeasurable (V.signedVFieldX M) := by
    unfold V.signedVFieldX
    exact ((stronglyMeasurable_const.mul (stronglyMeasurable_log_potential M.μx)).sub
      (stronglyMeasurable_vCross_left M.q M.μv))
  exact h.measurable

theorem measurable_signedVFieldV (M : V.SignedVMeasures) :
    Measurable (V.signedVFieldV M) := by
  letI : IsFiniteMeasure M.μx := ⟨lt_top_iff_ne_top.mpr M.finite_x⟩
  letI : IsFiniteMeasure M.μv := ⟨lt_top_iff_ne_top.mpr M.finite_v⟩
  letI : IsFiniteMeasure M.μz := ⟨lt_top_iff_ne_top.mpr M.finite_z⟩
  have h : StronglyMeasurable (V.signedVFieldV M) := by
    unfold V.signedVFieldV
    exact (((stronglyMeasurable_const.mul (stronglyMeasurable_log_potential M.μv)).add
      (stronglyMeasurable_log_potential M.μz)).sub
      (stronglyMeasurable_vCross_right M.q M.μx))
  exact h.measurable

theorem measurable_signedVFieldZ (M : V.SignedVMeasures) :
    Measurable (V.signedVFieldZ M) := by
  letI : IsFiniteMeasure M.μv := ⟨lt_top_iff_ne_top.mpr M.finite_v⟩
  letI : IsFiniteMeasure M.μz := ⟨lt_top_iff_ne_top.mpr M.finite_z⟩
  have h : StronglyMeasurable (V.signedVFieldZ M) := by
    unfold V.signedVFieldZ
    exact ((stronglyMeasurable_const.mul (stronglyMeasurable_log_potential M.μz)).add
      (stronglyMeasurable_log_potential M.μv))
  exact h.measurable

theorem ae_translatedCircleMeasure_of_forall_translatedAtom
    {P_prop : ℂ → Prop} (hmeas : MeasurableSet {w : ℂ | P_prop w})
    (u : ℂ) (m : ℕ) (hall : ∀ theta : ℝ, P_prop (translatedAtom u m theta)) :
    ∀ᵐ w ∂(translatedCircleMeasure u m), P_prop w := by
  have hpre : (P0.circlePoint (translatedAtomCenter u m) (smoothingEpsilon m)) ⁻¹'
      {w : ℂ | P_prop w}ᶜ = ∅ := by
    ext theta
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_setOf_eq,
      Set.mem_empty_iff_false, iff_false, not_not]
    rw [ContourKit.p0CirclePoint_eq_circleMap]
    exact hall theta
  rw [ae_iff]
  change translatedCircleMeasure u m {w : ℂ | P_prop w}ᶜ = 0
  simp only [translatedCircleMeasure, P0.circleProbability, Measure.smul_apply,
    smul_eq_mul, Measure.map_apply (P0.continuous_circlePoint _ _).measurable hmeas.compl,
    hpre, measure_empty, mul_zero]

theorem integral_translatedCircleMeasure_le_of_abs_sub_le
    {F : ℂ → ℝ} (hF_meas : Measurable F) (u : ℂ) (m : ℕ) {E : ℝ}
    (hE : ∀ theta : ℝ, |F (translatedAtom u m theta) - F u| ≤ E) :
    Integrable F (translatedCircleMeasure u m) ∧
      (∫ w : ℂ, F w ∂(translatedCircleMeasure u m)) ≤ F u + E := by
  have hF_int : Integrable F (translatedCircleMeasure u m) := by
    refine Integrable.of_bound hF_meas.aestronglyMeasurable (|F u| + E) ?_
    apply ae_translatedCircleMeasure_of_forall_translatedAtom
      (measurableSet_le hF_meas.norm measurable_const) u m
    intro theta
    rw [Real.norm_eq_abs]
    calc
      |F (translatedAtom u m theta)| =
          |F u + (F (translatedAtom u m theta) - F u)| := by ring_nf
      _ ≤ |F u| + |F (translatedAtom u m theta) - F u| := abs_add_le _ _
      _ ≤ |F u| + E := by linarith [hE theta]
  refine ⟨hF_int, ?_⟩
  have hae : ∀ᵐ w ∂(translatedCircleMeasure u m), F w ≤ F u + E := by
    apply ae_translatedCircleMeasure_of_forall_translatedAtom
      (measurableSet_le hF_meas measurable_const) u m
    intro theta
    have hle := (le_abs_self (F (translatedAtom u m theta) - F u)).trans (hE theta)
    linarith
  calc
    (∫ w : ℂ, F w ∂(translatedCircleMeasure u m)) ≤
        ∫ _w : ℂ, (F u + E) ∂(translatedCircleMeasure u m) :=
      integral_mono_ae hF_int (integrable_const (F u + E)) hae
    _ = F u + E := by
      rw [integral_const, translatedCircleMeasure_mass, one_smul]

theorem integral_translatedEmpiricalMeasure_le_of_abs_sub_le
    {d m : ℕ} (u : Fin d → ℂ) {F : ℂ → ℝ} (hF_meas : Measurable F) {E : ℝ}
    (hE : ∀ (i : Fin d) (theta : ℝ), |F (translatedAtom (u i) m theta) - F (u i)| ≤ E) :
    (∫ w : ℂ, F w ∂(translatedEmpiricalMeasure u m)) ≤
      (m : ℝ)⁻¹ * (∑ i : Fin d, F (u i)) + ((d : ℝ) / (m : ℝ)) * E := by
  have hcircle := fun i : Fin d =>
    integral_translatedCircleMeasure_le_of_abs_sub_le hF_meas (u i) m (hE i)
  have hsum_eq :
      (∫ w : ℂ, F w ∂(translatedEmpiricalMeasure u m)) =
        (m : ℝ)⁻¹ * ∑ i : Fin d, ∫ w : ℂ, F w ∂(translatedCircleMeasure (u i) m) := by
    unfold translatedEmpiricalMeasure P0.circleEmpiricalMeasure
    rw [integral_smul_measure,
      ENNReal.toReal_ofReal (inv_nonneg.mpr (Nat.cast_nonneg m)),
      smul_eq_mul, Measure.sum_fintype]
    rw [integral_finsetSum_measure]
    · rfl
    · intro i _
      exact (hcircle i).1
  rw [hsum_eq]
  have hsum_le :
      (∑ i : Fin d, ∫ w : ℂ, F w ∂(translatedCircleMeasure (u i) m)) ≤
        (∑ i : Fin d, F (u i)) + (d : ℝ) * E := by
    calc
      (∑ i : Fin d, ∫ w : ℂ, F w ∂(translatedCircleMeasure (u i) m)) ≤
          ∑ i : Fin d, (F (u i) + E) :=
        Finset.sum_le_sum (fun i _ => (hcircle i).2)
      _ = (∑ i : Fin d, F (u i)) + (d : ℝ) * E := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]
  calc
    (m : ℝ)⁻¹ * (∑ i : Fin d, ∫ w : ℂ, F w ∂(translatedCircleMeasure (u i) m)) ≤
        (m : ℝ)⁻¹ * ((∑ i : Fin d, F (u i)) + (d : ℝ) * E) :=
      mul_le_mul_of_nonneg_left hsum_le (inv_nonneg.mpr (Nat.cast_nonneg m))
    _ = (m : ℝ)⁻¹ * (∑ i : Fin d, F (u i)) + ((d : ℝ) / (m : ℝ)) * E := by ring

/-! ## 4. Endpoint-Disk (`[0, 1/250]`), Interior-Field (`(1/250, 1]`), and One-Body Lemmas -/

theorem vEx_le_vKx {q : ℕ} (hq : SignedVBaseRange q) :
    ((vEx q : ℚ) : ℝ) ≤ ((vKx q : ℚ) : ℝ) := by
  obtain ⟨h2, h7⟩ := hq
  interval_cases q <;> norm_num [vEx, vKx]

theorem vEv_le_vKv {q : ℕ} (hq : SignedVBaseRange q) :
    ((vEv q : ℚ) : ℝ) ≤ ((vKv q : ℚ) : ℝ) := by
  obtain ⟨h2, h7⟩ := hq
  interval_cases q <;> norm_num [vEv, vKv]

/-- Endpoint-disk field bound for `X` using `P.facts.x_endpoint_disk` and `vEx_le_vKx`. -/
theorem c7_endpoint_disk_field_bound_x
    {q : ℕ} {hq : SignedVBaseRange q} (P : VReferencePackage q hq)
    {w : ℂ} (hw0 : 0 < ‖w‖) (hw_disk : ‖w‖ ≤ 1 / 250) :
    V.signedVFullFieldX P.measure w ≤ (vKx q : ℝ) :=
  (P.facts.x_endpoint_disk w hw0 hw_disk).trans (vEx_le_vKx hq)

/-- Endpoint-disk field bound for `V` using `P.facts.v_endpoint_disk` and `vEv_le_vKv`. -/
theorem c7_endpoint_disk_field_bound_v
    {q : ℕ} {hq : SignedVBaseRange q} (P : VReferencePackage q hq)
    {w : ℂ} (hw0 : 0 < ‖w‖) (hw_disk : ‖w‖ ≤ 1 / 250) :
    V.signedVFullFieldV P.measure w ≤ (vKv q : ℝ) :=
  (P.facts.v_endpoint_disk w hw0 hw_disk).trans (vEv_le_vKv hq)

/-- Combined endpoint-disk (`t ≤ 1 / 250`, via `P.facts.x_endpoint_disk`) and
    interior (`1 / 250 < t`, via `P.facts.x_field`) full-field bound for `X`. -/
theorem c7_unsmoothed_fullFieldX_le_vKx
    {q : ℕ} {hq : SignedVBaseRange q} (P : VReferencePackage q hq)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (ht0 : (t : ℂ) ≠ 0) :
    V.signedVFullFieldX P.measure (t : ℂ) ≤ (vKx q : ℝ) := by
  have ht_pos : 0 < t := lt_of_le_of_ne ht.1 (fun h => ht0 (by simp [← h]))
  have hnorm_pos : 0 < ‖(t : ℂ)‖ := norm_pos_iff.mpr ht0
  by_cases hdisk : t ≤ 1 / 250
  · have hnorm_disk : ‖(t : ℂ)‖ ≤ 1 / 250 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht_pos]
      exact hdisk
    exact c7_endpoint_disk_field_bound_x P hnorm_pos hnorm_disk
  · exact le_of_lt (P.facts.x_field t ⟨ht_pos, ht.2⟩)

/-- Combined endpoint-disk (`t ≤ 1 / 250`, via `P.facts.v_endpoint_disk`) and
    interior (`1 / 250 < t`, via `P.facts.v_field`) full-field bound for `V`. -/
theorem c7_unsmoothed_fullFieldV_le_vKv
    {q : ℕ} {hq : SignedVBaseRange q} (P : VReferencePackage q hq)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (ht0 : (t : ℂ) ≠ 0) :
    V.signedVFullFieldV P.measure (t : ℂ) ≤ (vKv q : ℝ) := by
  have ht_pos : 0 < t := lt_of_le_of_ne ht.1 (fun h => ht0 (by simp [← h]))
  have hnorm_pos : 0 < ‖(t : ℂ)‖ := norm_pos_iff.mpr ht0
  by_cases hdisk : t ≤ 1 / 250
  · have hnorm_disk : ‖(t : ℂ)‖ ≤ 1 / 250 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht_pos]
      exact hdisk
    exact c7_endpoint_disk_field_bound_v P hnorm_pos hnorm_disk
  · exact le_of_lt (P.facts.v_field t ⟨ht_pos, ht.2⟩)

/-- Contour full-field bound for `Z` via `P.facts.z_field`. -/
theorem c7_unsmoothed_fullFieldZ_le_vKz
    {q : ℕ} {hq : SignedVBaseRange q} (P : VReferencePackage q hq)
    {w : ℂ} (hw : w ∈ V.vContourTrace q) :
    V.signedVFullFieldZ P.measure w ≤ (vKz q : ℝ) :=
  le_of_lt (P.facts.z_field w hw)

/-- Explicit specialization of `c7_negative_z_one_body_sum_bound` at zero angle. -/
theorem c7_negative_z_one_body_sum_bound_at_zero
    {q n : ℕ} (hq : 2 ≤ q) (hn : 64 ≤ 4 * n)
    (z : Fin (4 * n) → ℂ) (hz : ∀ i, z i ∈ V.vContourTrace q) :
    -(5 * n : ℝ) * (∑ i : Fin (4 * n), Real.log ‖z i‖) ≤
      ((4 * n : ℕ) : ℝ) *
        (∑ i : Fin (4 * n),
          -(5 / 4 : ℝ) * Real.log ‖translatedAtom (z i) (4 * n) 0‖) + 7 :=
  c7_negative_z_one_body_sum_bound hq hn z hz (fun _ => 0)

/-- The C7 positive one-body scalar budget `130` dominates the exact `m ≥ 64`
    perturbed disk cost from `p4_c7_positive_one_body_scalar`. -/
theorem c7_positive_one_body_budget_pos {m : ℕ} (hm : 64 ≤ m) :
    0 ≤ (m : ℝ) ^ 2 *
        ((17 / 2 : ℝ) * smoothingEpsilon m ^ 2 / (1 / 250 : ℝ) ^ 2) ∧
      (m : ℝ) ^ 2 *
        ((17 / 2 : ℝ) * smoothingEpsilon m ^ 2 / (1 / 250 : ℝ) ^ 2) < 130 := by
  refine ⟨?_, p4_c7_positive_one_body_scalar hm⟩
  positivity

/-! ## 5. Main C7 Fields and One-Body Transfer Theorem (`H5-sub3`) -/

/-- Combined C7 field + positive/negative one-body transfer on the smoothed
    empirical measures (`v-analytic.tex:561-601`), using
    `s0T_reference_*_potential_transfer`, `c7_negative_z_one_body_sum_bound`,
    `p4_c7_positive_one_body_scalar`, `P.facts.x_field`, `P.facts.v_field`,
    `P.facts.z_field`, `P.facts.x_endpoint_disk`, and `P.facts.v_endpoint_disk`. -/
theorem v13_c7_fields_and_one_body_transfer
    {q n : ℕ} (hq : SignedVBaseRange q) (P : VReferencePackage q hq)
    (hn : 64 ≤ 4 * n)
    (x : Fin (4 * n) → ℝ) (v : Fin (5 * n) → ℝ) (z : Fin (4 * n) → ℂ)
    (hx : ∀ i, x i ∈ Set.Icc (0 : ℝ) 1)
    (hv : ∀ b, v b ∈ Set.Icc (0 : ℝ) 1)
    (hz : ∀ i, z i ∈ V.vContourTrace q)
    (hx0 : ∀ i, (x i : ℂ) ≠ 0)
    (hv0 : ∀ b, (v b : ℂ) ≠ 0) :
    let μ := v13SmoothedEmpiricalMeasures hq (by omega)
      (fun i => (x i : ℂ)) (fun b => (v b : ℂ)) z
    let ν := P.measure
    ((4 * n : ℕ) : ℝ) ^ 2 *
        ((∫ w : ℂ, V.signedVFieldX ν w ∂μ.μx) +
          (∫ w : ℂ, V.signedVFieldV ν w ∂μ.μv) +
          (∫ w : ℂ, V.signedVFieldZ ν w ∂μ.μz)) +
      (3 * n : ℝ) * (∑ i : Fin (4 * n), Real.log |x i|) +
      (n : ℝ) * (∑ b : Fin (5 * n), Real.log |v b|) -
      (5 * n : ℝ) * (∑ i : Fin (4 * n), Real.log ‖z i‖) ≤
    (((vKx q : ℝ) + (5 / 4 : ℝ) * (vKv q : ℝ) + (vKz q : ℝ)) *
        ((4 * n : ℕ) : ℝ) ^ 2) +
      3 * sigmaBudget P.Ax P.Av P.Az *
        (1 + Real.log (((4 * n : ℕ) : ℝ) ^ 2 / 3)) +
      (denominatorTransferCost q + 7 + 130) := by
  intro μ ν
  let m : ℕ := 4 * n
  have hm : 64 ≤ m := hn
  have hmpos : 0 < m := by omega
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmpos
  have hmR_ne : (m : ℝ) ≠ 0 := hmR.ne'
  let Lm : ℝ := (3 * smoothingEpsilon m) * (1 + Real.log ((m : ℝ) ^ 2 / 3))
  let Ex : ℝ := 2 * densityTransferBudget P.Ax xMass * Lm +
    (15 / 4 : ℝ) * denominatorLipschitz q * smoothingEpsilon m
  let Ev : ℝ := (2 * densityTransferBudget P.Av vMass + densityTransferBudget P.Az zMass) * Lm +
    3 * denominatorLipschitz q * smoothingEpsilon m
  let Ez : ℝ := (2 * densityTransferBudget P.Az zMass + densityTransferBudget P.Av vMass) * Lm
  have hFx_emp :
      (∫ w : ℂ, V.signedVFieldX ν w ∂μ.μx) ≤
        (m : ℝ)⁻¹ * (∑ i : Fin (4 * n), V.signedVFieldX ν (x i : ℂ)) +
          ((m : ℝ) / (m : ℝ)) * Ex := by
    refine integral_translatedEmpiricalMeasure_le_of_abs_sub_le
      (fun i => (x i : ℂ)) (measurable_signedVFieldX ν) ?_
    intro i theta
    simpa [ν, m, Ex, Lm, mul_assoc] using
      (s0T_signedVFieldX_translatedAtom_abs_sub_le P hm
        (norm_ofReal_le_one_of_mem_Icc (hx i)) theta)
  have hFv_emp :
      (∫ w : ℂ, V.signedVFieldV ν w ∂μ.μv) ≤
        (m : ℝ)⁻¹ * (∑ b : Fin (5 * n), V.signedVFieldV ν (v b : ℂ)) +
          (((5 * n : ℕ) : ℝ) / (m : ℝ)) * Ev := by
    refine integral_translatedEmpiricalMeasure_le_of_abs_sub_le
      (fun b => (v b : ℂ)) (measurable_signedVFieldV ν) ?_
    intro b theta
    simpa [ν, m, Ev, Lm, mul_assoc] using
      (s0T_signedVFieldV_translatedAtom_abs_sub_le P hm
        (norm_ofReal_le_one_of_mem_Icc (hv b)) theta)
  have hFz_emp :
      (∫ w : ℂ, V.signedVFieldZ ν w ∂μ.μz) ≤
        (m : ℝ)⁻¹ * (∑ i : Fin (4 * n), V.signedVFieldZ ν (z i)) +
          ((m : ℝ) / (m : ℝ)) * Ez := by
    refine integral_translatedEmpiricalMeasure_le_of_abs_sub_le
      z (measurable_signedVFieldZ ν) ?_
    intro i theta
    simpa [ν, m, Ez, Lm, mul_assoc] using
      (s0T_signedVFieldZ_translatedAtom_abs_sub_le P hm (z i) theta)
  have hFullX_sum :
      (∑ i : Fin (4 * n), V.signedVFieldX ν (x i : ℂ)) +
          (3 / 4 : ℝ) * (∑ i : Fin (4 * n), Real.log |x i|) ≤
        (m : ℝ) * (vKx q : ℝ) := by
    have hrewrite :
        (∑ i : Fin (4 * n), V.signedVFieldX ν (x i : ℂ)) +
            (3 / 4 : ℝ) * (∑ i : Fin (4 * n), Real.log |x i|) =
          ∑ i : Fin (4 * n), V.signedVFullFieldX ν (x i : ℂ) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp [V.signedVFullFieldX, Complex.norm_real, Real.norm_eq_abs]
    rw [hrewrite]
    calc
      (∑ i : Fin (4 * n), V.signedVFullFieldX ν (x i : ℂ)) ≤
          ∑ _i : Fin (4 * n), (vKx q : ℝ) :=
        Finset.sum_le_sum (fun i _ => c7_unsmoothed_fullFieldX_le_vKx P (hx i) (hx0 i))
      _ = (m : ℝ) * (vKx q : ℝ) := by
        simp [m, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hFullV_sum :
      (∑ b : Fin (5 * n), V.signedVFieldV ν (v b : ℂ)) +
          (1 / 4 : ℝ) * (∑ b : Fin (5 * n), Real.log |v b|) ≤
        ((5 * n : ℕ) : ℝ) * (vKv q : ℝ) := by
    have hrewrite :
        (∑ b : Fin (5 * n), V.signedVFieldV ν (v b : ℂ)) +
            (1 / 4 : ℝ) * (∑ b : Fin (5 * n), Real.log |v b|) =
          ∑ b : Fin (5 * n), V.signedVFullFieldV ν (v b : ℂ) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      simp [V.signedVFullFieldV, Complex.norm_real, Real.norm_eq_abs]
    rw [hrewrite]
    calc
      (∑ b : Fin (5 * n), V.signedVFullFieldV ν (v b : ℂ)) ≤
          ∑ _b : Fin (5 * n), (vKv q : ℝ) :=
        Finset.sum_le_sum (fun b _ => c7_unsmoothed_fullFieldV_le_vKv P (hv b) (hv0 b))
      _ = ((5 * n : ℕ) : ℝ) * (vKv q : ℝ) := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hFullZ_sum :
      (∑ i : Fin (4 * n), V.signedVFieldZ ν (z i)) -
          (5 / 4 : ℝ) * (∑ i : Fin (4 * n), Real.log ‖z i‖) ≤
        (m : ℝ) * (vKz q : ℝ) := by
    have hrewrite :
        (∑ i : Fin (4 * n), V.signedVFieldZ ν (z i)) -
            (5 / 4 : ℝ) * (∑ i : Fin (4 * n), Real.log ‖z i‖) =
          ∑ i : Fin (4 * n), V.signedVFullFieldZ ν (z i) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      rfl
    rw [hrewrite]
    calc
      (∑ i : Fin (4 * n), V.signedVFullFieldZ ν (z i)) ≤
          ∑ _i : Fin (4 * n), (vKz q : ℝ) :=
        Finset.sum_le_sum (fun i _ => c7_unsmoothed_fullFieldZ_le_vKz P (hz i))
      _ = (m : ℝ) * (vKz q : ℝ) := by
        simp [m, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hm_sq_eps : (m : ℝ) ^ 2 * smoothingEpsilon m = 1 := by
    rw [smoothingEpsilon_eq_inv_sq, mul_inv_cancel₀ (pow_ne_zero 2 hmR_ne)]
  have hfive_four : ((5 * n : ℕ) : ℝ) = (5 / 4 : ℝ) * (m : ℝ) := by
    dsimp [m]
    push_cast
    ring
  have h3n : (3 * n : ℝ) = (m : ℝ) * (3 / 4 : ℝ) := by
    dsimp [m]
    push_cast
    ring
  have h1n : (n : ℝ) = (m : ℝ) * (1 / 4 : ℝ) := by
    dsimp [m]
    push_cast
    ring
  have h5n : (5 * n : ℝ) = (m : ℝ) * (5 / 4 : ℝ) := by
    dsimp [m]
    push_cast
    ring
  have herr_eq :
      (m : ℝ) ^ 2 * (((m : ℝ) / (m : ℝ)) * Ex +
        (((5 * n : ℕ) : ℝ) / (m : ℝ)) * Ev +
        ((m : ℝ) / (m : ℝ)) * Ez) =
      3 * sigmaBudget P.Ax P.Av P.Az * (1 + Real.log ((m : ℝ) ^ 2 / 3)) +
        (15 / 2 : ℝ) * denominatorLipschitz q := by
    rw [hfive_four]
    dsimp [Ex, Ev, Ez, Lm, sigmaBudget]
    calc
      (m : ℝ) ^ 2 * (((m : ℝ) / (m : ℝ)) *
          (2 * densityTransferBudget P.Ax xMass *
            ((3 * smoothingEpsilon m) * (1 + Real.log ((m : ℝ) ^ 2 / 3))) +
            (15 / 4 : ℝ) * denominatorLipschitz q * smoothingEpsilon m) +
        ((5 / 4 : ℝ) * (m : ℝ) / (m : ℝ)) *
          ((2 * densityTransferBudget P.Av vMass + densityTransferBudget P.Az zMass) *
            ((3 * smoothingEpsilon m) * (1 + Real.log ((m : ℝ) ^ 2 / 3))) +
            3 * denominatorLipschitz q * smoothingEpsilon m) +
        ((m : ℝ) / (m : ℝ)) *
          ((2 * densityTransferBudget P.Az zMass + densityTransferBudget P.Av vMass) *
            ((3 * smoothingEpsilon m) * (1 + Real.log ((m : ℝ) ^ 2 / 3))))) =
        ((m : ℝ) ^ 2 * smoothingEpsilon m) *
          (3 * (2 * densityTransferBudget P.Ax xMass +
            (7 / 2 : ℝ) * densityTransferBudget P.Av vMass +
            (13 / 4 : ℝ) * densityTransferBudget P.Az zMass) *
            (1 + Real.log ((m : ℝ) ^ 2 / 3)) +
          (15 / 2 : ℝ) * denominatorLipschitz q) := by
        field_simp [hmR_ne]
        ring
      _ = 3 * (2 * densityTransferBudget P.Ax xMass +
            (7 / 2 : ℝ) * densityTransferBudget P.Av vMass +
            (13 / 4 : ℝ) * densityTransferBudget P.Az zMass) *
            (1 + Real.log ((m : ℝ) ^ 2 / 3)) +
          (15 / 2 : ℝ) * denominatorLipschitz q := by
        rw [hm_sq_eps, one_mul]
  have hden_le : (15 / 2 : ℝ) * denominatorLipschitz q ≤ denominatorTransferCost q := by
    have hL : 0 ≤ denominatorLipschitz q := (denominatorLipschitz_pos hq.1).le
    unfold denominatorTransferCost
    linarith
  have hpos_budget := c7_positive_one_body_budget_pos hm
  have h130_pos : (0 : ℝ) < 130 := lt_of_le_of_lt hpos_budget.1 hpos_budget.2
  have _hz_sum := c7_negative_z_one_body_sum_bound_at_zero hq.1 hn z hz
  have hsum_emp := add_le_add (add_le_add hFx_emp hFv_emp) hFz_emp
  have hmul_emp := mul_le_mul_of_nonneg_left hsum_emp (sq_nonneg (m : ℝ))
  have hm_inv_cancel : (m : ℝ) ^ 2 * (m : ℝ)⁻¹ = (m : ℝ) := by
    field_simp [hmR_ne]
  have hcomb_fields :
      (m : ℝ) * (∑ i : Fin (4 * n), V.signedVFieldX ν (x i : ℂ)) +
      (m : ℝ) * (∑ b : Fin (5 * n), V.signedVFieldV ν (v b : ℂ)) +
      (m : ℝ) * (∑ i : Fin (4 * n), V.signedVFieldZ ν (z i)) +
      (3 * n : ℝ) * (∑ i : Fin (4 * n), Real.log |x i|) +
      (n : ℝ) * (∑ b : Fin (5 * n), Real.log |v b|) -
      (5 * n : ℝ) * (∑ i : Fin (4 * n), Real.log ‖z i‖) ≤
      ((vKx q : ℝ) + (5 / 4 : ℝ) * (vKv q : ℝ) + (vKz q : ℝ)) * (m : ℝ) ^ 2 := by
    have hX := mul_le_mul_of_nonneg_left hFullX_sum hmR.le
    have hV := mul_le_mul_of_nonneg_left hFullV_sum hmR.le
    have hZ := mul_le_mul_of_nonneg_left hFullZ_sum hmR.le
    rw [hfive_four] at hV
    rw [h5n, h3n, h1n]
    linarith
  have hexpand :
      (m : ℝ) ^ 2 *
        (((m : ℝ)⁻¹ * (∑ i : Fin (4 * n), V.signedVFieldX ν (x i : ℂ)) +
            ((m : ℝ) / (m : ℝ)) * Ex) +
          ((m : ℝ)⁻¹ * (∑ b : Fin (5 * n), V.signedVFieldV ν (v b : ℂ)) +
            (((5 * n : ℕ) : ℝ) / (m : ℝ)) * Ev) +
          ((m : ℝ)⁻¹ * (∑ i : Fin (4 * n), V.signedVFieldZ ν (z i)) +
            ((m : ℝ) / (m : ℝ)) * Ez)) =
      (m : ℝ) * (∑ i : Fin (4 * n), V.signedVFieldX ν (x i : ℂ)) +
      (m : ℝ) * (∑ b : Fin (5 * n), V.signedVFieldV ν (v b : ℂ)) +
      (m : ℝ) * (∑ i : Fin (4 * n), V.signedVFieldZ ν (z i)) +
      (m : ℝ) ^ 2 * (((m : ℝ) / (m : ℝ)) * Ex +
        (((5 * n : ℕ) : ℝ) / (m : ℝ)) * Ev +
        ((m : ℝ) / (m : ℝ)) * Ez) := by
    calc
      (m : ℝ) ^ 2 *
          (((m : ℝ)⁻¹ * (∑ i : Fin (4 * n), V.signedVFieldX ν (x i : ℂ)) +
              ((m : ℝ) / (m : ℝ)) * Ex) +
            ((m : ℝ)⁻¹ * (∑ b : Fin (5 * n), V.signedVFieldV ν (v b : ℂ)) +
              (((5 * n : ℕ) : ℝ) / (m : ℝ)) * Ev) +
            ((m : ℝ)⁻¹ * (∑ i : Fin (4 * n), V.signedVFieldZ ν (z i)) +
              ((m : ℝ) / (m : ℝ)) * Ez)) =
        ((m : ℝ) ^ 2 * (m : ℝ)⁻¹) *
          ((∑ i : Fin (4 * n), V.signedVFieldX ν (x i : ℂ)) +
            (∑ b : Fin (5 * n), V.signedVFieldV ν (v b : ℂ)) +
            (∑ i : Fin (4 * n), V.signedVFieldZ ν (z i))) +
        (m : ℝ) ^ 2 * (((m : ℝ) / (m : ℝ)) * Ex +
          (((5 * n : ℕ) : ℝ) / (m : ℝ)) * Ev +
          ((m : ℝ) / (m : ℝ)) * Ez) := by ring
      _ = _ := by rw [hm_inv_cancel]; ring
  rw [hexpand, herr_eq] at hmul_emp
  change (m : ℝ) ^ 2 *
        ((∫ w : ℂ, V.signedVFieldX ν w ∂μ.μx) +
          (∫ w : ℂ, V.signedVFieldV ν w ∂μ.μv) +
          (∫ w : ℂ, V.signedVFieldZ ν w ∂μ.μz)) +
      (3 * n : ℝ) * (∑ i : Fin (4 * n), Real.log |x i|) +
      (n : ℝ) * (∑ b : Fin (5 * n), Real.log |v b|) -
      (5 * n : ℝ) * (∑ i : Fin (4 * n), Real.log ‖z i‖) ≤
    (((vKx q : ℝ) + (5 / 4 : ℝ) * (vKv q : ℝ) + (vKz q : ℝ)) *
        (m : ℝ) ^ 2) +
      3 * sigmaBudget P.Ax P.Av P.Az *
        (1 + Real.log ((m : ℝ) ^ 2 / 3)) +
      (denominatorTransferCost q + 7 + 130)
  linarith

end

end Li2Lean.B3

#print axioms Li2Lean.B3.integrable_log_norm_sub_of_vBallBound_of_ae_norm_le
#print axioms Li2Lean.B3.v13_c7_fields_and_one_body_transfer
