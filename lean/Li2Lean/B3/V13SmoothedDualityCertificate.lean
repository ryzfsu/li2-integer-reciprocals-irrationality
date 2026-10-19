/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B3.S0TCoreBound
import Li2Lean.B3.S0TC4
import Li2Lean.B3.S0TC1C4Actual
import Li2Lean.V.S4Integrability

/-!
# S0-T Duality Comparison (`H5-sub2`) — C1–C4 Square Certificate and Reference Field Comparison

This module constructs the concrete `V.SignedVSquareCertificate` for the
circle-smoothed empirical measure triple
`μ = v13SmoothedEmpiricalMeasures hq hn (fun i => (x i : ℂ)) (fun b => (v b : ℂ)) z`
against the reference measure `ν = P.measure` of `P : VReferencePackage q hq`,
and applies `V.signedV_duality_field_comparison_of_square` (`B3/S0TC4.lean:105`)
together with `p4_reference_negative_energy_bound` (`B3/S0TAllMConstructionPieces.lean:132`)
to prove `v13_smoothed_duality_comparison_of_reference` (and its unshifted
companion `v13_smoothed_duality_comparison_of_reference_unshifted`).
-/

namespace Li2Lean.B3

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal

/-! ## 1. Cross-integrability of `li2LogKernel` between a smoothed empirical measure and any bounded-support finite measure -/

private theorem circlePoint_sub_ofReal_zero (x : ℂ) (r : ℝ) :
    P0.circlePoint (x - (r : ℂ)) r 0 = x := by
  rw [ContourKit.p0CirclePoint_eq_circleMap]
  simp [circleMap]

private theorem integral_norm_realLogKernel_circleAngleMeasure_le
    (x w : ℂ) {r : ℝ} (hr : 0 < r) {C : ℝ} (hx : ‖x‖ ≤ C) :
    (∫ v : ℝ, ‖P0.realLogKernel x (P0.circlePoint w r v)‖ ∂P0.circleAngleMeasure) ≤
      (2 * Real.pi) * (2 * (C + r + ‖w‖ + 2 * r) - Real.log r) := by
  have h0 := P0.integral_norm_circle_kernel_le (x - (r : ℂ)) w hr 0
  rw [circlePoint_sub_ofReal_zero] at h0
  have hdist : ‖x - (r : ℂ) - w‖ ≤ C + r + ‖w‖ := by
    have hr_norm : ‖(r : ℂ)‖ = r := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    calc
      ‖x - (r : ℂ) - w‖ = ‖(x - (r : ℂ)) - w‖ := rfl
      _ ≤ ‖x - (r : ℂ)‖ + ‖w‖ := norm_sub_le _ _
      _ ≤ (‖x‖ + ‖(r : ℂ)‖) + ‖w‖ := add_le_add (norm_sub_le _ _) le_rfl
      _ = ‖x‖ + r + ‖w‖ := by rw [hr_norm]
      _ ≤ C + r + ‖w‖ := by linarith
  refine h0.trans ?_
  apply mul_le_mul_of_nonneg_left _ Real.two_pi_pos.le
  linarith

theorem integrable_realLogKernel_prod_circleProbability_of_ae_norm_le
    {σ : Measure ℂ} [IsFiniteMeasure σ] {C : ℝ} (hσ : ∀ᵐ x ∂σ, ‖x‖ ≤ C)
    (w : ℂ) {r : ℝ} (hr : 0 < r) :
    Integrable (fun p : ℂ × ℂ => P0.realLogKernel p.1 p.2)
      (σ.prod (P0.circleProbability w r)) := by
  have hmeas_ang : AEStronglyMeasurable
      (fun p : ℂ × ℝ => P0.realLogKernel p.1 (P0.circlePoint w r p.2))
      (σ.prod P0.circleAngleMeasure) := by
    apply Measurable.aestronglyMeasurable
    exact P0.measurable_realLogKernel.comp
      (measurable_fst.prodMk ((P0.continuous_circlePoint w r).measurable.comp measurable_snd))
  have hint_ang : Integrable
      (fun p : ℂ × ℝ => P0.realLogKernel p.1 (P0.circlePoint w r p.2))
      (σ.prod P0.circleAngleMeasure) := by
    apply (integrable_prod_iff hmeas_ang).mpr
    constructor
    · exact ae_of_all _ (fun x => P0.integrable_realLogKernel_circlePoint x w r)
    · apply (integrable_const ((2 * Real.pi) * (2 * (C + r + ‖w‖ + 2 * r) - Real.log r))).mono'
        hmeas_ang.norm.integral_prod_right'
      filter_upwards [hσ] with x hx
      rw [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
      exact integral_norm_realLogKernel_circleAngleMeasure_le x w hr hx
  have hmap : Measurable (Prod.map (id : ℂ → ℂ) (P0.circlePoint w r)) :=
    measurable_id.prodMap (P0.continuous_circlePoint w r).measurable
  unfold P0.circleProbability
  rw [Measure.prod_smul_right]
  apply Integrable.smul_measure _ ENNReal.ofReal_ne_top
  have hprod_map :
      σ.prod (Measure.map (P0.circlePoint w r) P0.circleAngleMeasure) =
        Measure.map (Prod.map id (P0.circlePoint w r)) (σ.prod P0.circleAngleMeasure) := by
    simpa only [Measure.map_id] using
      (Measure.map_prod_map σ P0.circleAngleMeasure measurable_id
        (P0.continuous_circlePoint w r).measurable)
  rw [hprod_map]
  exact (integrable_map_measure P0.measurable_realLogKernel.aestronglyMeasurable
    hmap.aemeasurable).mpr hint_ang

theorem integrable_li2LogKernel_prod_translatedEmpiricalMeasure_of_ae_norm_le
    {d m : ℕ} (hm : 0 < m) (u : Fin d → ℂ)
    {σ : Measure ℂ} [IsFiniteMeasure σ] {C : ℝ} (hσ : ∀ᵐ x ∂σ, ‖x‖ ≤ C) :
    Integrable (fun p : ℂ × ℂ => li2LogKernel p.1 p.2)
      (σ.prod (translatedEmpiricalMeasure u m)) := by
  change Integrable (fun p : ℂ × ℂ => P0.realLogKernel p.1 p.2)
    (σ.prod (translatedEmpiricalMeasure u m))
  unfold translatedEmpiricalMeasure P0.circleEmpiricalMeasure
  rw [Measure.prod_smul_right]
  apply Integrable.smul_measure _ ENNReal.ofReal_ne_top
  rw [Measure.prod_sum_right, Measure.sum_fintype]
  apply integrable_finsetSum_measure.mpr
  intro i _
  exact integrable_realLogKernel_prod_circleProbability_of_ae_norm_le hσ
    (translatedAtomCenter (u i) m) (smoothingEpsilon_pos hm)

theorem integrable_li2LogKernel_translatedEmpiricalMeasure_prod_of_ae_norm_le
    {d m : ℕ} (hm : 0 < m) (u : Fin d → ℂ)
    {σ : Measure ℂ} [IsFiniteMeasure σ] {C : ℝ} (hσ : ∀ᵐ x ∂σ, ‖x‖ ≤ C) :
    Integrable (fun p : ℂ × ℂ => li2LogKernel p.1 p.2)
      ((translatedEmpiricalMeasure u m).prod σ) :=
  P0.L6Variations.integrable_kernel_swap
    (integrable_li2LogKernel_prod_translatedEmpiricalMeasure_of_ae_norm_le hm u hσ)

/-! ## 2. Support and `Real.log ‖w‖` integrability for `P.measure` and `v13SmoothedEmpiricalMeasures` -/

theorem referenceMeasure_x_norm_ae_le_one
    {q : ℕ} {hq : SignedVBaseRange q} (P : VReferencePackage q hq) :
    ∀ᵐ w ∂P.measure.μx, ‖w‖ ≤ 1 := by
  have hmem : ∀ᵐ w ∂P.measure.μx, w ∈ Complex.ofReal '' Set.Icc (0 : ℝ) 1 := by
    rw [ae_iff]
    exact P.facts.x_support
  filter_upwards [hmem] with w ⟨r, hr, h_rw⟩
  rw [← h_rw]
  exact norm_ofReal_le_one_of_mem_Icc hr

theorem referenceMeasure_x_norm_ae_le_tubeRadius
    {q : ℕ} {hq : SignedVBaseRange q} (P : VReferencePackage q hq) :
    ∀ᵐ w ∂P.measure.μx, ‖w‖ ≤ V.v13DenominatorTubeRadius := by
  filter_upwards [referenceMeasure_x_norm_ae_le_one P] with w hw
  unfold V.v13DenominatorTubeRadius
  linarith

theorem referenceMeasure_v_norm_ae_bounds
    {q : ℕ} {hq : SignedVBaseRange q} (P : VReferencePackage q hq) :
    ∀ᵐ w ∂P.measure.μv, ((vVLow q : ℚ) : ℝ) ≤ ‖w‖ ∧ ‖w‖ ≤ 1 := by
  have hlow : (0 : ℝ) < ((vVLow q : ℚ) : ℝ) := by
    norm_num [vVLow]
  have hmem : ∀ᵐ w ∂P.measure.μv, w ∈ Complex.ofReal '' Set.Icc (vVLow q : ℝ) 1 := by
    rw [ae_iff]
    exact P.facts.v_support_low
  filter_upwards [hmem] with w ⟨r, hr, h_rw⟩
  rw [← h_rw]
  have hr0 : 0 ≤ r := le_trans hlow.le hr.1
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
  exact hr

theorem referenceMeasure_v_norm_ae_le_one
    {q : ℕ} {hq : SignedVBaseRange q} (P : VReferencePackage q hq) :
    ∀ᵐ w ∂P.measure.μv, ‖w‖ ≤ 1 := by
  filter_upwards [referenceMeasure_v_norm_ae_bounds P] with w hw
  exact hw.2

theorem referenceMeasure_v_norm_ae_le_tubeRadius
    {q : ℕ} {hq : SignedVBaseRange q} (P : VReferencePackage q hq) :
    ∀ᵐ w ∂P.measure.μv, ‖w‖ ≤ V.v13DenominatorTubeRadius := by
  filter_upwards [referenceMeasure_v_norm_ae_le_one P] with w hw
  unfold V.v13DenominatorTubeRadius
  linarith

theorem referenceMeasure_z_norm_ae_le_q
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

theorem v13SmoothedCircle_norm_ae_ge_epsilon (t : ℝ) {m : ℕ} (hm : 0 < m) :
    ∀ᵐ z ∂(V.v13SmoothedCircleMeasure t m), smoothingEpsilon m ≤ ‖z‖ := by
  have hr : 0 < smoothingEpsilon m := smoothingEpsilon_pos hm
  have hmem : ∀ᵐ z ∂(V.v13SmoothedCircleMeasure t m),
      z ∈ Metric.sphere (translatedAtomCenter (Complex.ofReal t) m)
        (smoothingEpsilon m) := by
    unfold V.v13SmoothedCircleMeasure translatedCircleMeasure
    have h := P0.circleProbability_outside_sphere
      (translatedAtomCenter (Complex.ofReal t) m) hr
    rw [ae_iff]
    exact h
  filter_upwards [hmem] with z hz
  have hnorm : ‖z - translatedAtomCenter (Complex.ofReal t) m‖ = smoothingEpsilon m := by
    simpa only [Metric.mem_sphere, dist_eq_norm] using hz
  have him_sub : |(z - translatedAtomCenter (Complex.ofReal t) m).im| ≤ smoothingEpsilon m := by
    rw [← hnorm]
    exact Complex.abs_im_le_norm _
  have hcenter_im : (translatedAtomCenter (Complex.ofReal t) m).im = 2 * smoothingEpsilon m := by
    simp [translatedAtomCenter]
  have hzim : smoothingEpsilon m ≤ z.im := by
    have h1 := (abs_le.mp him_sub).1
    simp only [Complex.sub_im, hcenter_im] at h1
    linarith
  have habs_im : z.im ≤ |z.im| := le_abs_self _
  exact hzim.trans (habs_im.trans (Complex.abs_im_le_norm z))

theorem v13SmoothedRealEmpirical_norm_ae_ge_epsilon {d : ℕ}
    (t : Fin d → ℝ) {m : ℕ} (hm : 0 < m) :
    ∀ᵐ z ∂(V.v13SmoothedRealEmpirical t m), smoothingEpsilon m ≤ ‖z‖ := by
  let E : Set ℂ := {z | ¬ smoothingEpsilon m ≤ ‖z‖}
  have hE : MeasurableSet E := by
    dsimp [E]
    simpa only [not_le] using (measurableSet_lt measurable_norm measurable_const)
  have hzero (i : Fin d) :
      P0.circleProbability (translatedAtomCenter (Complex.ofReal (t i)) m)
        (smoothingEpsilon m) E = 0 := by
    have hi := v13SmoothedCircle_norm_ae_ge_epsilon (t i) hm
    rw [ae_iff] at hi
    exact hi
  have hzero' : V.v13SmoothedRealEmpirical t m E = 0 := by
    unfold V.v13SmoothedRealEmpirical translatedEmpiricalMeasure P0.circleEmpiricalMeasure
    rw [Measure.smul_apply, Measure.sum_apply _ hE]
    simp only [hzero, tsum_zero, smul_zero]
  rw [ae_iff]
  exact hzero'

theorem v13SmoothedRealEmpirical_ae_ne_zero {d : ℕ}
    (t : Fin d → ℝ) {m : ℕ} (hm : 0 < m) :
    ∀ᵐ z ∂(V.v13SmoothedRealEmpirical t m), z ≠ 0 := by
  have hr : 0 < smoothingEpsilon m := smoothingEpsilon_pos hm
  filter_upwards [v13SmoothedRealEmpirical_norm_ae_ge_epsilon t hm] with z hz hz0
  rw [hz0, norm_zero] at hz
  linarith

theorem integrable_log_norm_of_ae_bounds
    {σ : Measure ℂ} [IsFiniteMeasure σ] {c C : ℝ}
    (hc : 0 < c) (hσ : ∀ᵐ w ∂σ, c ≤ ‖w‖ ∧ ‖w‖ ≤ C) :
    Integrable (fun w : ℂ => Real.log ‖w‖) σ := by
  have hmeas : Measurable (fun w : ℂ => Real.log ‖w‖) := by fun_prop
  refine Integrable.of_bound hmeas.aestronglyMeasurable
    (max |Real.log c| |Real.log C|) ?_
  filter_upwards [hσ] with w ⟨hlo, hhi⟩
  have hw0 : 0 < ‖w‖ := lt_of_lt_of_le hc hlo
  have hlog_lo : Real.log c ≤ Real.log ‖w‖ := Real.log_le_log hc hlo
  have hlog_hi : Real.log ‖w‖ ≤ Real.log C := Real.log_le_log hw0 hhi
  change |Real.log ‖w‖| ≤ max |Real.log c| |Real.log C|
  rw [abs_le]
  constructor
  · linarith [neg_abs_le (Real.log c), le_max_left |Real.log c| |Real.log C|]
  · linarith [le_abs_self (Real.log C), le_max_right |Real.log c| |Real.log C|]

theorem integrable_log_norm_referenceMeasure_v
    {q : ℕ} {hq : SignedVBaseRange q} (P : VReferencePackage q hq) :
    Integrable (fun w : ℂ => Real.log ‖w‖) P.measure.μv := by
  letI : IsFiniteMeasure P.measure.μv := ⟨lt_top_iff_ne_top.mpr P.measure.finite_v⟩
  exact integrable_log_norm_of_ae_bounds (by norm_num [vVLow])
    (referenceMeasure_v_norm_ae_bounds P)

theorem integrable_log_norm_v13SmoothedRealEmpirical {d m : ℕ}
    (hm : 64 ≤ m) (t : Fin d → ℝ) (ht : ∀ i, |t i| ≤ 1) :
    Integrable (fun w : ℂ => Real.log ‖w‖) (V.v13SmoothedRealEmpirical t m) := by
  have hm0 : 0 < m := by omega
  refine integrable_log_norm_of_ae_bounds
    (C := 1 + (3 / 4096 : ℝ)) (smoothingEpsilon_pos hm0) ?_
  filter_upwards [v13SmoothedRealEmpirical_norm_ae_ge_epsilon t hm0,
    V.v13SmoothedRealEmpirical_norm_ae_le_one_add_three_div_4096 t hm ht] with w hlo hhi
  exact ⟨hlo, hhi⟩

/-! ## 3. Reflection pushforward properties (`R_q(v) = -q / v`) -/

theorem map_vReflection_univ (q : ℕ) (σ : Measure ℂ) :
    (Measure.map (V.vReflection q) σ) Set.univ = σ Set.univ := by
  rw [Measure.map_apply (V.v13Reflection_measurable q) MeasurableSet.univ, Set.preimage_univ]

theorem map_vReflection_real_univ (q : ℕ) (σ : Measure ℂ) :
    (Measure.map (V.vReflection q) σ).real Set.univ = σ.real Set.univ := by
  simp [Measure.real, map_vReflection_univ]

theorem vReflection_involutive (q : ℕ) (hq : 0 < q) {w : ℂ} (hw : w ≠ 0) :
    V.vReflection q (V.vReflection q w) = w := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  have h1 : V.vReflection q w ≠ 0 := by
    rw [V.vReflection_apply q hw]
    exact div_ne_zero (neg_ne_zero.mpr hq0) hw
  rw [V.vReflection_apply q h1, V.vReflection_apply q hw]
  field_simp [hq0, hw]

theorem map_vReflection_atomless (q : ℕ) (hq : 0 < q) (σ : Measure ℂ)
    (hσ : ∀ z : ℂ, σ {z} = 0) (z : ℂ) :
    (Measure.map (V.vReflection q) σ) {z} = 0 := by
  rw [Measure.map_apply (V.v13Reflection_measurable q) (measurableSet_singleton z)]
  have hsub : V.vReflection q ⁻¹' {z} ⊆ ({0} : Set ℂ) ∪ {V.vReflection q z} := by
    intro w hw
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hw
    by_cases hw0 : w = 0
    · exact Or.inl hw0
    · right
      simp only [Set.mem_singleton_iff]
      rw [← hw, vReflection_involutive q hq hw0]
  exact measure_mono_null hsub (measure_union_null (hσ 0) (hσ (V.vReflection q z)))

theorem vReflection_cross_integrable_and_interaction_eq
    {q : ℕ} (hq : 2 ≤ q) (σx τv : Measure ℂ)
    [IsFiniteMeasure σx] [IsFiniteMeasure τv]
    (hx : ∀ᵐ x ∂σx, ‖x‖ ≤ V.v13DenominatorTubeRadius)
    (hv : ∀ᵐ v ∂τv, ‖v‖ ≤ V.v13DenominatorTubeRadius)
    (hv0 : ∀ᵐ v ∂τv, v ≠ 0)
    (hlogv : Integrable (fun v : ℂ => Real.log ‖v‖) τv) :
    Integrable (fun p : ℂ × ℂ => li2LogKernel p.1 p.2)
        (σx.prod (Measure.map (V.vReflection q) τv)) ∧
      li2LogInteraction σx (Measure.map (V.vReflection q) τv) =
        (σx.real Set.univ) * (∫ v : ℂ, Real.log ‖v‖ ∂τv) -
          V.vCrossInteraction q σx τv := by
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hrad_pos : 0 < (q : ℝ) - V.v13DenominatorTubeRadius ^ 2 := by
    unfold V.v13DenominatorTubeRadius
    nlinarith
  have hae : ∀ᵐ p : ℂ × ℂ ∂(σx.prod τv),
      li2LogKernel p.1 (V.vReflection q p.2) =
        Real.log ‖p.2‖ - V.v13DenominatorKernel q p := by
    filter_upwards [
      (Measure.quasiMeasurePreserving_fst (μ := σx) (ν := τv)).ae hx,
      (Measure.quasiMeasurePreserving_snd (μ := σx) (ν := τv)).ae hv,
      (Measure.quasiMeasurePreserving_snd (μ := σx) (ν := τv)).ae hv0] with p hp1 hp2 hpv0
    have hlo := V.v13DenominatorKernel_norm_lower hq hp1 hp2
    have hden_ne : (q : ℂ) + p.1 * p.2 ≠ 0 := by
      rw [← norm_pos_iff]
      linarith
    have hcoll : p.1 - V.vReflection q p.2 ≠ 0 := by
      intro h0
      apply hden_ne
      rw [V.vCross_factorization q hpv0, h0, zero_mul]
    have hlog := V.vCross_log_factorization q hpv0 hcoll
    unfold li2LogKernel V.v13DenominatorKernel
    linarith
  have hden_int : Integrable (V.v13DenominatorKernel q) (σx.prod τv) :=
    V.v13_denominatorKernel_integrable hq σx τv hx hv
      (by norm_num [V.v13DenominatorTubeRadius])
      (by unfold V.v13DenominatorTubeRadius; nlinarith)
  have hlog_int : Integrable (fun p : ℂ × ℂ => Real.log ‖p.2‖) (σx.prod τv) :=
    hlogv.comp_snd σx
  have hdiff_int : Integrable
      (fun p : ℂ × ℂ => Real.log ‖p.2‖ - V.v13DenominatorKernel q p) (σx.prod τv) :=
    hlog_int.sub hden_int
  have hpull_int : Integrable
      (fun p : ℂ × ℂ => li2LogKernel p.1 (V.vReflection q p.2)) (σx.prod τv) :=
    hdiff_int.congr (hae.mono (fun p hp => hp.symm))
  have hmap : Measurable (Prod.map (id : ℂ → ℂ) (V.vReflection q)) :=
    measurable_id.prodMap (V.v13Reflection_measurable q)
  have hint_map : Integrable (fun p : ℂ × ℂ => li2LogKernel p.1 p.2)
      (σx.prod (Measure.map (V.vReflection q) τv)) := by
    rw [V.v13Reflection_map_prod_map_right q σx τv]
    exact (integrable_map_measure P0.L6Admissible.measurable_li2LogKernel.aestronglyMeasurable
      hmap.aemeasurable).mpr hpull_int
  refine ⟨hint_map, ?_⟩
  unfold li2LogInteraction
  rw [V.v13Reflection_map_prod_map_right q σx τv,
    integral_map hmap.aemeasurable P0.L6Admissible.measurable_li2LogKernel.aestronglyMeasurable]
  change (∫ p : ℂ × ℂ, li2LogKernel p.1 (V.vReflection q p.2) ∂(σx.prod τv)) = _
  rw [integral_congr_ae hae, integral_sub hlog_int hden_int]
  have h1 : (∫ p : ℂ × ℂ, Real.log ‖p.2‖ ∂(σx.prod τv)) =
      (σx.real Set.univ) * ∫ v : ℂ, Real.log ‖v‖ ∂τv := by
    rw [integral_prod _ hlog_int]
    simp only [Prod.snd]
    rw [integral_const, Measure.real, smul_eq_mul]
  rw [h1]
  rfl

theorem vReflection_self_integrable_and_interaction_eq
    {q : ℕ} (hq : 0 < q) (σ τ : Measure ℂ)
    [IsFiniteMeasure σ] [IsFiniteMeasure τ]
    (hσ0 : ∀ᵐ v ∂σ, v ≠ 0) (hτ0 : ∀ᵐ w ∂τ, w ≠ 0)
    (hτ_atomless : ∀ z : ℂ, τ {z} = 0)
    (hστ : Integrable (fun p : ℂ × ℂ => li2LogKernel p.1 p.2) (σ.prod τ))
    (hlogσ : Integrable (fun v : ℂ => Real.log ‖v‖) σ)
    (hlogτ : Integrable (fun w : ℂ => Real.log ‖w‖) τ) :
    Integrable (fun p : ℂ × ℂ => li2LogKernel p.1 p.2)
        ((Measure.map (V.vReflection q) σ).prod (Measure.map (V.vReflection q) τ)) ∧
      li2LogInteraction (Measure.map (V.vReflection q) σ)
          (Measure.map (V.vReflection q) τ) =
        -(σ.real Set.univ * τ.real Set.univ * Real.log (q : ℝ)) +
          li2LogInteraction σ τ +
          (τ.real Set.univ) * (∫ v : ℂ, Real.log ‖v‖ ∂σ) +
          (σ.real Set.univ) * (∫ w : ℂ, Real.log ‖w‖ ∂τ) := by
  have hdiag : (σ.prod τ) (Set.diagonal ℂ) = 0 :=
    P0.L6Variations.prod_diagonal_null_of_right_atomless σ τ hτ_atomless
  have hne : ∀ᵐ p : ℂ × ℂ ∂(σ.prod τ), p.1 ≠ p.2 :=
    P0.L6Variations.ae_ne_of_diagonal_null hdiag
  have hae : ∀ᵐ p : ℂ × ℂ ∂(σ.prod τ),
      li2LogKernel (V.vReflection q p.1) (V.vReflection q p.2) =
        ((-Real.log (q : ℝ) + li2LogKernel p.1 p.2) + Real.log ‖p.1‖) + Real.log ‖p.2‖ := by
    filter_upwards [
      (Measure.quasiMeasurePreserving_fst (μ := σ) (ν := τ)).ae hσ0,
      (Measure.quasiMeasurePreserving_snd (μ := σ) (ν := τ)).ae hτ0,
      hne] with p hp1 hp2 hp12
    have hdist := V.vReflection_log_distance q hq hp1 hp2 hp12
    unfold li2LogKernel
    linarith
  have hc_int : Integrable (fun _ : ℂ × ℂ => -Real.log (q : ℝ)) (σ.prod τ) :=
    integrable_const _
  have h1_int : Integrable (fun p : ℂ × ℂ => Real.log ‖p.1‖) (σ.prod τ) :=
    hlogσ.comp_fst τ
  have h2_int : Integrable (fun p : ℂ × ℂ => Real.log ‖p.2‖) (σ.prod τ) :=
    hlogτ.comp_snd σ
  have hsum_int : Integrable
      (fun p : ℂ × ℂ =>
        ((-Real.log (q : ℝ) + li2LogKernel p.1 p.2) + Real.log ‖p.1‖) + Real.log ‖p.2‖)
      (σ.prod τ) :=
    ((hc_int.add hστ).add h1_int).add h2_int
  have hpull_int : Integrable
      (fun p : ℂ × ℂ => li2LogKernel (V.vReflection q p.1) (V.vReflection q p.2))
      (σ.prod τ) :=
    hsum_int.congr (hae.mono (fun p hp => hp.symm))
  have hmap : Measurable (Prod.map (V.vReflection q) (V.vReflection q)) :=
    (V.v13Reflection_measurable q).prodMap (V.v13Reflection_measurable q)
  have hprod_map :
      (Measure.map (V.vReflection q) σ).prod (Measure.map (V.vReflection q) τ) =
        Measure.map (Prod.map (V.vReflection q) (V.vReflection q)) (σ.prod τ) :=
    Measure.map_prod_map σ τ (V.v13Reflection_measurable q) (V.v13Reflection_measurable q)
  have hint_map : Integrable (fun p : ℂ × ℂ => li2LogKernel p.1 p.2)
      ((Measure.map (V.vReflection q) σ).prod (Measure.map (V.vReflection q) τ)) := by
    rw [hprod_map]
    exact (integrable_map_measure P0.L6Admissible.measurable_li2LogKernel.aestronglyMeasurable
      hmap.aemeasurable).mpr hpull_int
  refine ⟨hint_map, ?_⟩
  unfold li2LogInteraction
  rw [hprod_map,
    integral_map hmap.aemeasurable P0.L6Admissible.measurable_li2LogKernel.aestronglyMeasurable]
  change (∫ p : ℂ × ℂ, li2LogKernel (V.vReflection q p.1) (V.vReflection q p.2) ∂(σ.prod τ)) = _
  rw [integral_congr_ae hae]
  have hsum_eval :
      (∫ p : ℂ × ℂ,
        -Real.log (q : ℝ) + li2LogKernel p.1 p.2 + Real.log ‖p.1‖ +
          Real.log ‖p.2‖ ∂(σ.prod τ)) =
        (∫ p : ℂ × ℂ, -Real.log (q : ℝ) ∂(σ.prod τ)) +
        (∫ p : ℂ × ℂ, li2LogKernel p.1 p.2 ∂(σ.prod τ)) +
        (∫ p : ℂ × ℂ, Real.log ‖p.1‖ ∂(σ.prod τ)) +
        (∫ p : ℂ × ℂ, Real.log ‖p.2‖ ∂(σ.prod τ)) := by
    have hA := integral_add (hc_int.add hστ) h1_int
    have hB := integral_add ((hc_int.add hστ).add h1_int) h2_int
    have hA' :
        (∫ p : ℂ × ℂ,
          -Real.log (q : ℝ) + li2LogKernel p.1 p.2 + Real.log ‖p.1‖
            ∂(σ.prod τ)) =
          (∫ p : ℂ × ℂ,
            (-Real.log (q : ℝ) + li2LogKernel p.1 p.2) ∂(σ.prod τ)) +
            (∫ p : ℂ × ℂ, Real.log ‖p.1‖ ∂(σ.prod τ)) := by
      simpa only [Pi.add_apply] using hA
    calc
      (∫ p : ℂ × ℂ,
          -Real.log (q : ℝ) + li2LogKernel p.1 p.2 + Real.log ‖p.1‖ +
            Real.log ‖p.2‖ ∂(σ.prod τ)) =
          (∫ p : ℂ × ℂ,
            (-Real.log (q : ℝ) + li2LogKernel p.1 p.2 + Real.log ‖p.1‖)
              ∂(σ.prod τ)) +
            (∫ p : ℂ × ℂ, Real.log ‖p.2‖ ∂(σ.prod τ)) := by
              simpa only [Pi.add_apply] using hB
      _ = ((∫ p : ℂ × ℂ,
              (-Real.log (q : ℝ) + li2LogKernel p.1 p.2) ∂(σ.prod τ)) +
            (∫ p : ℂ × ℂ, Real.log ‖p.1‖ ∂(σ.prod τ))) +
            (∫ p : ℂ × ℂ, Real.log ‖p.2‖ ∂(σ.prod τ)) := by
              have hA'' := congrArg
                (fun t : ℝ => t + (∫ p : ℂ × ℂ, Real.log ‖p.2‖ ∂(σ.prod τ))) hA'
              simpa only [add_assoc] using hA''
      _ = (∫ p : ℂ × ℂ, -Real.log (q : ℝ) ∂(σ.prod τ)) +
            (∫ p : ℂ × ℂ, li2LogKernel p.1 p.2 ∂(σ.prod τ)) +
            (∫ p : ℂ × ℂ, Real.log ‖p.1‖ ∂(σ.prod τ)) +
            (∫ p : ℂ × ℂ, Real.log ‖p.2‖ ∂(σ.prod τ)) := by
              rw [integral_add hc_int hστ]
  rw [hsum_eval]
  have hconst_eval : (∫ _ : ℂ × ℂ, -Real.log (q : ℝ) ∂(σ.prod τ)) =
      -(σ.real Set.univ * τ.real Set.univ * Real.log (q : ℝ)) := by
    rw [integral_const, Measure.real, Measure.real, ← Set.univ_prod_univ,
      Measure.prod_prod, ENNReal.toReal_mul, smul_eq_mul]
    simp only [Measure.real]
    ring
  have h1_eval : (∫ p : ℂ × ℂ, Real.log ‖p.1‖ ∂(σ.prod τ)) =
      (τ.real Set.univ) * ∫ v : ℂ, Real.log ‖v‖ ∂σ := by
    rw [integral_prod _ h1_int]
    simp only [integral_const, Measure.real, smul_eq_mul]
    rw [ ← integral_const_mul]
    
  have h2_eval : (∫ p : ℂ × ℂ, Real.log ‖p.2‖ ∂(σ.prod τ)) =
      (σ.real Set.univ) * ∫ w : ℂ, Real.log ‖w‖ ∂τ := by
    rw [integral_prod _ h2_int]
    simp only [Prod.snd]
    rw [integral_const, Measure.real, smul_eq_mul]
  rw [hconst_eval, h1_eval, h2_eval]

/-! ## 4. Generic `L6PairCertificate` constructor from `P0.L6Variations.L6FourMeasureData` -/

noncomputable def l6PairCertificate_sum_of_fourMeasureData
    {η η₀ φ φ₀ : Measure ℂ}
    (h : P0.L6Variations.L6FourMeasureData η η₀ φ φ₀) :
    V.L6PairCertificate := by
  letI := h.fin_η
  letI := h.fin_η₀
  letI := h.fin_φ
  letI := h.fin_φ₀
  have iφη := P0.L6Variations.integrable_kernel_swap h.int_ηφ
  have iφ₀η₀ := P0.L6Variations.integrable_kernel_swap h.int_η₀φ₀
  have iφη₀ := P0.L6Variations.integrable_kernel_swap h.int_η₀φ
  refine V.l6PairCertificate_of_data (η + φ) (η₀ + φ₀)
    (measure_ne_top _ _) (measure_ne_top _ _)
    (by simp [Measure.coe_add, Pi.add_apply, h.mass_η, h.mass_φ])
    (fun z => by simp [h.atomless_η z, h.atomless_φ z])
    (fun z => by simp [h.atomless_η₀ z, h.atomless_φ₀ z])
    (P0.L6Variations.integrable_kernel_add_left
      (P0.L6Variations.integrable_kernel_add_right h.int_ηη h.int_ηφ)
      (P0.L6Variations.integrable_kernel_add_right iφη h.int_φφ))
    (P0.L6Variations.integrable_kernel_add_left
      (P0.L6Variations.integrable_kernel_add_right h.int_η₀η₀ h.int_η₀φ₀)
      (P0.L6Variations.integrable_kernel_add_right iφ₀η₀ h.int_φ₀φ₀))
    (P0.L6Variations.integrable_kernel_add_left
      (P0.L6Variations.integrable_kernel_add_right h.int_ηη₀ h.int_ηφ₀)
      (P0.L6Variations.integrable_kernel_add_right iφη₀ h.int_φφ₀))

theorem l6PairCertificate_sum_square_eq
    {η η₀ φ φ₀ : Measure ℂ}
    (h : P0.L6Variations.L6FourMeasureData η η₀ φ φ₀) :
    let c := l6PairCertificate_sum_of_fourMeasureData h
    li2LogInteraction c.left c.left +
      li2LogInteraction c.right c.right -
        2 * li2LogInteraction c.left c.right =
      P0.L6Variations.l6PairDifference η η₀ +
        P0.L6Variations.l6PairDifference φ φ₀ +
        2 * (li2LogInteraction η φ - li2LogInteraction η φ₀ -
          li2LogInteraction η₀ φ + li2LogInteraction η₀ φ₀) := by
  intro c
  have hsum := P0.L6Variations.l6QuadraticRemainder_eq_half_sum h
  unfold P0.L6Variations.l6QuadraticRemainder at hsum
  change P0.L6Variations.l6PairDifference (η + φ) (η₀ + φ₀) = _
  linarith

/-! ## 5. Concrete `V.SignedVSquareCertificate` and Fubini field identities -/

private theorem abs_le_one_of_mem_Icc {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |t| ≤ 1 := by
  rw [abs_of_nonneg ht.1]
  exact ht.2

noncomputable def v13_smoothed_reference_squareCertificate
    {q n : ℕ} {hq : SignedVBaseRange q} (P : VReferencePackage q hq)
    (hn : 64 ≤ 4 * n)
    (x : Fin (4 * n) → ℝ) (v : Fin (5 * n) → ℝ) (z : Fin (4 * n) → ℂ)
    (hx : ∀ i, x i ∈ Set.Icc (0 : ℝ) 1)
    (hv : ∀ b, v b ∈ Set.Icc (0 : ℝ) 1) :
    let μ := v13SmoothedEmpiricalMeasures hq (by omega)
      (fun i => (x i : ℂ)) (fun b => (v b : ℂ)) z
    V.SignedVSquareCertificate μ P.measure := by
  intro μ
  let ν := P.measure
  have hm : 0 < 4 * n := by omega
  have hq0 : 0 < q := by linarith [hq.1]
  have hx_abs : ∀ i, |x i| ≤ 1 := fun i => abs_le_one_of_mem_Icc (hx i)
  have hv_abs : ∀ b, |v b| ≤ 1 := fun b => abs_le_one_of_mem_Icc (hv b)
  letI : IsFiniteMeasure μ.μx := ⟨lt_top_iff_ne_top.mpr μ.finite_x⟩
  letI : IsFiniteMeasure μ.μv := ⟨lt_top_iff_ne_top.mpr μ.finite_v⟩
  letI : IsFiniteMeasure μ.μz := ⟨lt_top_iff_ne_top.mpr μ.finite_z⟩
  letI : IsFiniteMeasure ν.μx := ⟨lt_top_iff_ne_top.mpr ν.finite_x⟩
  letI : IsFiniteMeasure ν.μv := ⟨lt_top_iff_ne_top.mpr ν.finite_v⟩
  letI : IsFiniteMeasure ν.μz := ⟨lt_top_iff_ne_top.mpr ν.finite_z⟩
  have hμx_tube : ∀ᵐ w ∂μ.μx, ‖w‖ ≤ V.v13DenominatorTubeRadius :=
    V.v13SmoothedRealEmpirical_norm_ae_le_one_add_three_div_4096 x hn hx_abs
  have hμv_tube : ∀ᵐ w ∂μ.μv, ‖w‖ ≤ V.v13DenominatorTubeRadius :=
    V.v13SmoothedRealEmpirical_norm_ae_le_one_add_three_div_4096 v hn hv_abs
  have hνx_tube : ∀ᵐ w ∂ν.μx, ‖w‖ ≤ V.v13DenominatorTubeRadius :=
    referenceMeasure_x_norm_ae_le_tubeRadius P
  have hνv_tube : ∀ᵐ w ∂ν.μv, ‖w‖ ≤ V.v13DenominatorTubeRadius :=
    referenceMeasure_v_norm_ae_le_tubeRadius P
  have hμv_ne0 : ∀ᵐ w ∂μ.μv, w ≠ 0 :=
    v13SmoothedRealEmpirical_ae_ne_zero v hm
  have hνv_ne0 : ∀ᵐ w ∂ν.μv, w ≠ 0 :=
    referenceMeasure_v_ae_ne_zero P
  have hlog_μv : Integrable (fun w : ℂ => Real.log ‖w‖) μ.μv :=
    integrable_log_norm_v13SmoothedRealEmpirical hn v hv_abs
  have hlog_νv : Integrable (fun w : ℂ => Real.log ‖w‖) ν.μv :=
    integrable_log_norm_referenceMeasure_v P
  have h_atom_μx : ∀ w : ℂ, μ.μx {w} = 0 :=
    v13SmoothedEmpiricalMeasures_atomless_x hq (by omega) _ _ _
  have h_atom_μv : ∀ w : ℂ, μ.μv {w} = 0 :=
    v13SmoothedEmpiricalMeasures_atomless_v hq (by omega) _ _ _
  have h_atom_μz : ∀ w : ℂ, μ.μz {w} = 0 :=
    v13SmoothedEmpiricalMeasures_atomless_z hq (by omega) _ _ _
  have hint_μxμx : Integrable (fun p : ℂ × ℂ => li2LogKernel p.1 p.2) (μ.μx.prod μ.μx) :=
    V.v13SmoothedRealEmpirical_log_integrable x hm
  have hint_μvμv : Integrable (fun p : ℂ × ℂ => li2LogKernel p.1 p.2) (μ.μv.prod μ.μv) :=
    V.v13SmoothedRealEmpirical_log_integrable v hm
  have hint_μzμz : Integrable (fun p : ℂ × ℂ => li2LogKernel p.1 p.2) (μ.μz.prod μ.μz) :=
    translatedEmpiricalMeasure_log_integrable z hm
  have hint_μxνx : Integrable (fun p : ℂ × ℂ => li2LogKernel p.1 p.2) (μ.μx.prod ν.μx) :=
    integrable_li2LogKernel_translatedEmpiricalMeasure_prod_of_ae_norm_le hm _
      (referenceMeasure_x_norm_ae_le_one P)
  have hint_μvνv : Integrable (fun p : ℂ × ℂ => li2LogKernel p.1 p.2) (μ.μv.prod ν.μv) :=
    integrable_li2LogKernel_translatedEmpiricalMeasure_prod_of_ae_norm_le hm _
      (referenceMeasure_v_norm_ae_le_one P)
  have hint_νvμv : Integrable (fun p : ℂ × ℂ => li2LogKernel p.1 p.2) (ν.μv.prod μ.μv) :=
    P0.L6Variations.integrable_kernel_swap hint_μvνv
  have hint_μzνz : Integrable (fun p : ℂ × ℂ => li2LogKernel p.1 p.2) (μ.μz.prod ν.μz) :=
    integrable_li2LogKernel_translatedEmpiricalMeasure_prod_of_ae_norm_le hm z
      (referenceMeasure_z_norm_ae_le_q P)
  have hint_μvμz : Integrable (fun p : ℂ × ℂ => li2LogKernel p.1 p.2) (μ.μv.prod μ.μz) :=
    translatedEmpiricalMeasure_log_cross_integrable (fun b => (v b : ℂ)) z hm
  have hint_μvνz : Integrable (fun p : ℂ × ℂ => li2LogKernel p.1 p.2) (μ.μv.prod ν.μz) :=
    integrable_li2LogKernel_translatedEmpiricalMeasure_prod_of_ae_norm_le hm _
      (referenceMeasure_z_norm_ae_le_q P)
  have hint_νvμz : Integrable (fun p : ℂ × ℂ => li2LogKernel p.1 p.2) (ν.μv.prod μ.μz) :=
    integrable_li2LogKernel_prod_translatedEmpiricalMeasure_of_ae_norm_le hm z
      (referenceMeasure_v_norm_ae_le_one P)
  have hR_νvνv := vReflection_self_integrable_and_interaction_eq hq0 ν.μv ν.μv
    hνv_ne0 hνv_ne0 P.facts.v_atomless P.facts.dual_admissible.vv hlog_νv hlog_νv
  have hR_μvμv := vReflection_self_integrable_and_interaction_eq hq0 μ.μv μ.μv
    hμv_ne0 hμv_ne0 h_atom_μv hint_μvμv hlog_μv hlog_μv
  have hR_νvμv := vReflection_self_integrable_and_interaction_eq hq0 ν.μv μ.μv
    hνv_ne0 hμv_ne0 h_atom_μv hint_νvμv hlog_νv hlog_μv
  have hR_μxνv := vReflection_cross_integrable_and_interaction_eq hq.1 μ.μx ν.μv
    hμx_tube hνv_tube hνv_ne0 hlog_νv
  have hR_μxμv := vReflection_cross_integrable_and_interaction_eq hq.1 μ.μx μ.μv
    hμx_tube hμv_tube hμv_ne0 hlog_μv
  have hR_νxνv := vReflection_cross_integrable_and_interaction_eq hq.1 ν.μx ν.μv
    hνx_tube hνv_tube hνv_ne0 hlog_νv
  have hR_νxμv := vReflection_cross_integrable_and_interaction_eq hq.1 ν.μx μ.μv
    hνx_tube hμv_tube hμv_ne0 hlog_μv
  have hfour_xv : P0.L6Variations.L6FourMeasureData
      μ.μx ν.μx (Measure.map (V.vReflection q) ν.μv) (Measure.map (V.vReflection q) μ.μv) :=
    { fin_η := inferInstance
      fin_η₀ := inferInstance
      fin_φ := Measure.isFiniteMeasure_map _ _
      fin_φ₀ := Measure.isFiniteMeasure_map _ _
      mass_η := μ.mass_x.trans ν.mass_x.symm
      mass_φ := by rw [map_vReflection_univ, map_vReflection_univ, ν.mass_v, μ.mass_v]
      atomless_η := h_atom_μx
      atomless_η₀ := P.facts.x_atomless
      atomless_φ := map_vReflection_atomless q hq0 ν.μv P.facts.v_atomless
      atomless_φ₀ := map_vReflection_atomless q hq0 μ.μv h_atom_μv
      int_ηη := hint_μxμx
      int_η₀η₀ := P.facts.dual_admissible.xx
      int_φφ := hR_νvνv.1
      int_φ₀φ₀ := hR_μvμv.1
      int_ηη₀ := hint_μxνx
      int_φφ₀ := hR_νvμv.1
      int_ηφ := hR_μxνv.1
      int_ηφ₀ := hR_μxμv.1
      int_η₀φ := hR_νxνv.1
      int_η₀φ₀ := hR_νxμv.1 }
  have hfour_vz : P0.L6Variations.L6FourMeasureData μ.μv ν.μv μ.μz ν.μz :=
    { fin_η := inferInstance
      fin_η₀ := inferInstance
      fin_φ := inferInstance
      fin_φ₀ := inferInstance
      mass_η := μ.mass_v.trans ν.mass_v.symm
      mass_φ := μ.mass_z.trans ν.mass_z.symm
      atomless_η := h_atom_μv
      atomless_η₀ := P.facts.v_atomless
      atomless_φ := h_atom_μz
      atomless_φ₀ := P.facts.z_atomless
      int_ηη := hint_μvμv
      int_η₀η₀ := P.facts.dual_admissible.vv
      int_φφ := hint_μzμz
      int_φ₀φ₀ := P.facts.dual_admissible.zz
      int_ηη₀ := hint_μvνv
      int_φφ₀ := hint_μzνz
      int_ηφ := hint_μvμz
      int_ηφ₀ := hint_μvνz
      int_η₀φ := hint_νvμz
      int_η₀φ₀ := P.facts.dual_admissible.vz }
  let d : V.SignedVQuadraticData :=
    { xSelf := P0.L6Variations.l6PairDifference μ.μx ν.μx
      vSelf := P0.L6Variations.l6PairDifference μ.μv ν.μv
      zSelf := P0.L6Variations.l6PairDifference μ.μz ν.μz
      xvPair := -(V.vCrossInteraction q μ.μx μ.μv + V.vCrossInteraction q ν.μx ν.μv -
        V.vCrossInteraction q μ.μx ν.μv - V.vCrossInteraction q ν.μx μ.μv)
      vzPair := -(li2LogInteraction μ.μv μ.μz + li2LogInteraction ν.μv ν.μz -
        li2LogInteraction μ.μv ν.μz - li2LogInteraction ν.μv μ.μz) }
  refine
    { first := l6PairCertificate_sum_of_fourMeasureData hfour_xv
      second := l6PairCertificate_sum_of_fourMeasureData hfour_vz
      third := V.l6PairCertificate_of_data μ.μx ν.μx μ.finite_x ν.finite_x
        (μ.mass_x.trans ν.mass_x.symm) h_atom_μx P.facts.x_atomless
        hint_μxμx P.facts.dual_admissible.xx hint_μxνx
      fourth := V.l6PairCertificate_of_data μ.μz ν.μz μ.finite_z ν.finite_z
        (μ.mass_z.trans ν.mass_z.symm) h_atom_μz P.facts.z_atomless
        hint_μzμz P.facts.dual_admissible.zz hint_μzνz
      data := d
      remainder := V.signedVQuadraticForm d
      remainder_eq := rfl
      first_square_eq := ?_
      second_square_eq := ?_
      third_square_eq := rfl
      fourth_square_eq := rfl }
  · rw [l6PairCertificate_sum_square_eq hfour_xv]
    have hmx_μ : μ.μx.real Set.univ = 1 := by simp [Measure.real, μ.mass_x]
    have hmx_ν : ν.μx.real Set.univ = 1 := by simp [Measure.real, ν.mass_x]
    have hmv_μ : μ.μv.real Set.univ = (5 / 4 : ℝ) := by simp [Measure.real, μ.mass_v]
    have hmv_ν : ν.μv.real Set.univ = (5 / 4 : ℝ) := by simp [Measure.real, ν.mass_v]
    have hcomm_vv : li2LogInteraction ν.μv μ.μv = li2LogInteraction μ.μv ν.μv :=
      P0.L6Variations.li2LogInteraction_comm ν.μv μ.μv
    dsimp [d, P0.L6Variations.l6PairDifference]
    rw [hR_νvνv.2, hR_μvμv.2, hR_νvμv.2, hR_μxνv.2, hR_μxμv.2, hR_νxνv.2, hR_νxμv.2,
      hmx_μ, hmx_ν, hmv_μ, hmv_ν, hcomm_vv]
    ring
  · rw [l6PairCertificate_sum_square_eq hfour_vz]
    dsimp [d, P0.L6Variations.l6PairDifference]
    ring

/-! ## 6. Fubini field identities (`hFx`, `hFv`, `hFz`) -/

private theorem integral_log_norm_sub_eq_vLogInteraction
    (μ ν : Measure ℂ) [SFinite μ] [SFinite ν]
    (h : Integrable (fun p : ℂ × ℂ => li2LogKernel p.1 p.2) (μ.prod ν)) :
    (∫ w : ℂ, (∫ t : ℂ, Real.log ‖w - t‖ ∂ν) ∂μ) = V.vLogInteraction ν μ := by
  have h1 := P0.L6Variations.li2LogInteraction_eq_neg_integral_potential h
  unfold P0.L6Variations.l6LogPotential at h1
  rw [P0.L6Variations.li2LogInteraction_comm μ ν] at h1
  unfold V.vLogInteraction
  linarith

private theorem integrable_log_norm_sub_of_kernel
    (μ ν : Measure ℂ) [SFinite μ] [SFinite ν]
    (h : Integrable (fun p : ℂ × ℂ => li2LogKernel p.1 p.2) (μ.prod ν)) :
    Integrable (fun w : ℂ => ∫ t : ℂ, Real.log ‖w - t‖ ∂ν) μ :=
  P0.L6Variations.integrable_potential h

/-! ## 7. Main C1–C4 Duality Comparison Theorems -/

/-- Exact unshifted C1–C4 duality comparison for `v13SmoothedEmpiricalMeasures`
    against `P.measure`. -/
theorem v13_smoothed_duality_comparison_of_reference_unshifted
    {q n : ℕ} {hq : SignedVBaseRange q} (P : VReferencePackage q hq)
    (hn : 64 ≤ 4 * n)
    (x : Fin (4 * n) → ℝ) (v : Fin (5 * n) → ℝ) (z : Fin (4 * n) → ℂ)
    (hx : ∀ i, x i ∈ Set.Icc (0 : ℝ) 1)
    (hv : ∀ b, v b ∈ Set.Icc (0 : ℝ) 1) :
    let μ := v13SmoothedEmpiricalMeasures hq (by omega)
      (fun i => (x i : ℂ)) (fun b => (v b : ℂ)) z
    let ν := P.measure
    V.signedVQuadratic μ ≤
      -((vQlow q : ℚ) : ℝ) +
        (∫ w : ℂ, V.signedVFieldX ν w ∂μ.μx) +
        (∫ w : ℂ, V.signedVFieldV ν w ∂μ.μv) +
        (∫ w : ℂ, V.signedVFieldZ ν w ∂μ.μz) := by
  intro μ ν
  have hm : 0 < 4 * n := by omega
  have hx_abs : ∀ i, |x i| ≤ 1 := fun i => abs_le_one_of_mem_Icc (hx i)
  have hv_abs : ∀ b, |v b| ≤ 1 := fun b => abs_le_one_of_mem_Icc (hv b)
  letI : IsFiniteMeasure μ.μx := ⟨lt_top_iff_ne_top.mpr μ.finite_x⟩
  letI : IsFiniteMeasure μ.μv := ⟨lt_top_iff_ne_top.mpr μ.finite_v⟩
  letI : IsFiniteMeasure μ.μz := ⟨lt_top_iff_ne_top.mpr μ.finite_z⟩
  letI : IsFiniteMeasure ν.μx := ⟨lt_top_iff_ne_top.mpr ν.finite_x⟩
  letI : IsFiniteMeasure ν.μv := ⟨lt_top_iff_ne_top.mpr ν.finite_v⟩
  letI : IsFiniteMeasure ν.μz := ⟨lt_top_iff_ne_top.mpr ν.finite_z⟩
  have hint_μxνx : Integrable (fun p : ℂ × ℂ => li2LogKernel p.1 p.2) (μ.μx.prod ν.μx) :=
    integrable_li2LogKernel_translatedEmpiricalMeasure_prod_of_ae_norm_le hm _
      (referenceMeasure_x_norm_ae_le_one P)
  have hint_μvνv : Integrable (fun p : ℂ × ℂ => li2LogKernel p.1 p.2) (μ.μv.prod ν.μv) :=
    integrable_li2LogKernel_translatedEmpiricalMeasure_prod_of_ae_norm_le hm _
      (referenceMeasure_v_norm_ae_le_one P)
  have hint_μvνz : Integrable (fun p : ℂ × ℂ => li2LogKernel p.1 p.2) (μ.μv.prod ν.μz) :=
    integrable_li2LogKernel_translatedEmpiricalMeasure_prod_of_ae_norm_le hm _
      (referenceMeasure_z_norm_ae_le_q P)
  have hint_μzνz : Integrable (fun p : ℂ × ℂ => li2LogKernel p.1 p.2) (μ.μz.prod ν.μz) :=
    integrable_li2LogKernel_translatedEmpiricalMeasure_prod_of_ae_norm_le hm z
      (referenceMeasure_z_norm_ae_le_q P)
  have hint_μzνv : Integrable (fun p : ℂ × ℂ => li2LogKernel p.1 p.2) (μ.μz.prod ν.μv) :=
    integrable_li2LogKernel_translatedEmpiricalMeasure_prod_of_ae_norm_le hm z
      (referenceMeasure_v_norm_ae_le_one P)
  have hμx_tube : ∀ᵐ w ∂μ.μx, ‖w‖ ≤ V.v13DenominatorTubeRadius :=
    V.v13SmoothedRealEmpirical_norm_ae_le_one_add_three_div_4096 x hn hx_abs
  have hμv_tube : ∀ᵐ w ∂μ.μv, ‖w‖ ≤ V.v13DenominatorTubeRadius :=
    V.v13SmoothedRealEmpirical_norm_ae_le_one_add_three_div_4096 v hn hv_abs
  have hνx_tube : ∀ᵐ w ∂ν.μx, ‖w‖ ≤ V.v13DenominatorTubeRadius :=
    referenceMeasure_x_norm_ae_le_tubeRadius P
  have hνv_tube : ∀ᵐ w ∂ν.μv, ‖w‖ ≤ V.v13DenominatorTubeRadius :=
    referenceMeasure_v_norm_ae_le_tubeRadius P
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq.1
  have hden_μxνv : Integrable (V.v13DenominatorKernel q) (μ.μx.prod ν.μv) :=
    V.v13_denominatorKernel_integrable hq.1 μ.μx ν.μv hμx_tube hνv_tube
      (by norm_num [V.v13DenominatorTubeRadius])
      (by unfold V.v13DenominatorTubeRadius; nlinarith)
  have hden_νxμv : Integrable (V.v13DenominatorKernel q) (ν.μx.prod μ.μv) :=
    V.v13_denominatorKernel_integrable hq.1 ν.μx μ.μv hνx_tube hμv_tube
      (by norm_num [V.v13DenominatorTubeRadius])
      (by unfold V.v13DenominatorTubeRadius; nlinarith)
  have hxx : V.vLogInteraction μ.μx ν.μx = V.vLogInteraction ν.μx μ.μx := by
    unfold V.vLogInteraction
    rw [P0.L6Variations.li2LogInteraction_comm]
  have hvv : V.vLogInteraction μ.μv ν.μv = V.vLogInteraction ν.μv μ.μv := by
    unfold V.vLogInteraction
    rw [P0.L6Variations.li2LogInteraction_comm]
  have hzz : V.vLogInteraction μ.μz ν.μz = V.vLogInteraction ν.μz μ.μz := by
    unfold V.vLogInteraction
    rw [P0.L6Variations.li2LogInteraction_comm]
  have hvz : li2LogInteraction ν.μz μ.μv = li2LogInteraction μ.μv ν.μz :=
    P0.L6Variations.li2LogInteraction_comm ν.μz μ.μv
  have hFx : (∫ w : ℂ, V.signedVFieldX ν w ∂μ.μx) =
      2 * V.vLogInteraction ν.μx μ.μx - V.vCrossInteraction ν.q μ.μx ν.μv := by
    unfold V.signedVFieldX
    have hpot := integrable_log_norm_sub_of_kernel μ.μx ν.μx hint_μxνx
    have hcross : Integrable (fun w : ℂ => ∫ t : ℂ, V.vCrossKernel ν.q w t ∂ν.μv) μ.μx := by
      rw [P.facts.q_eq]
      exact hden_μxνv.integral_prod_left
    have hcross_prod : Integrable
        (fun p : ℂ × ℂ => V.vCrossKernel ν.q p.1 p.2)
        (μ.μx.prod ν.μv) := by
      have hden := hden_μxνv
      rw [← P.facts.q_eq] at hden
      change Integrable (fun p : ℂ × ℂ => Real.log ‖(ν.q : ℂ) + p.1 * p.2‖)
        (μ.μx.prod ν.μv) at hden
      simpa [V.vCrossKernel] using hden
    rw [integral_sub (hpot.const_mul 2) hcross, integral_const_mul,
      integral_log_norm_sub_eq_vLogInteraction μ.μx ν.μx hint_μxνx]
    congr 1
    rw [V.vCrossInteraction, ← integral_prod _ hcross_prod]
  have hFv : (∫ w : ℂ, V.signedVFieldV ν w ∂μ.μv) =
      2 * V.vLogInteraction ν.μv μ.μv + V.vLogInteraction ν.μz μ.μv -
        V.vCrossInteraction ν.q ν.μx μ.μv := by
    unfold V.signedVFieldV
    rw [P.facts.q_eq]
    have hpot_v := integrable_log_norm_sub_of_kernel μ.μv ν.μv hint_μvνv
    have hpot_z := integrable_log_norm_sub_of_kernel μ.μv ν.μz hint_μvνz
    have hcross : Integrable (fun w : ℂ => ∫ t : ℂ, V.vCrossKernel q t w ∂ν.μx) μ.μv := by
      exact hden_νxμv.integral_prod_right
    have hcross_prod : Integrable
        (fun p : ℂ × ℂ => V.vCrossKernel q p.2 p.1)
        (μ.μv.prod ν.μx) := by
      rw [← Measure.prod_swap]
      have hm : Measurable (Prod.swap : ℂ × ℂ → ℂ × ℂ) := measurable_swap
      have hf : Measurable (fun p : ℂ × ℂ => V.vCrossKernel q p.2 p.1) := by
        unfold V.vCrossKernel
        fun_prop
      apply (integrable_map_measure hf.aestronglyMeasurable hm.aemeasurable).mpr
      have hden := hden_νxμv
      change Integrable (fun p : ℂ × ℂ => Real.log ‖(q : ℂ) + p.1 * p.2‖)
        (ν.μx.prod μ.μv) at hden
      simpa [Function.comp_def, V.vCrossKernel] using hden
    let f : ℂ → ℝ := fun w => ∫ t : ℂ, Real.log ‖w - t‖ ∂ν.μv
    let g : ℂ → ℝ := fun w => ∫ t : ℂ, Real.log ‖w - t‖ ∂ν.μz
    let k : ℂ → ℝ := fun w => ∫ t : ℂ, V.vCrossKernel q t w ∂ν.μx
    have hf : Integrable f μ.μv := by simpa [f] using hpot_v
    have hg : Integrable g μ.μv := by simpa [g] using hpot_z
    have hk : Integrable k μ.μv := by simpa [k] using hcross
    change (∫ w : ℂ, (2 * f w + g w) - k w ∂μ.μv) = _
    have hsplit :
        (∫ w : ℂ, (2 * f w + g w) - k w ∂μ.μv) =
          (∫ w : ℂ, 2 * f w + g w ∂μ.μv) - ∫ w : ℂ, k w ∂μ.μv := by
      exact integral_sub ((hf.const_mul 2).add hg) hk
    rw [hsplit, integral_add (hf.const_mul 2) hg, integral_const_mul,
      integral_log_norm_sub_eq_vLogInteraction μ.μv ν.μv hint_μvνv,
      integral_log_norm_sub_eq_vLogInteraction μ.μv ν.μz hint_μvνz]
    rw [V.vCrossInteraction, ← integral_prod _ hcross_prod]
    have hcross_swap :
        (∫ p : ℂ × ℂ, V.vCrossKernel q p.2 p.1 ∂(μ.μv.prod ν.μx)) =
          ∫ p : ℂ × ℂ, V.vCrossKernel q p.1 p.2 ∂(ν.μx.prod μ.μv) := by
      simpa [Prod.swap] using
        (MeasureTheory.integral_prod_swap
          (μ := ν.μx) (ν := μ.μv)
          (fun p : ℂ × ℂ => V.vCrossKernel q p.1 p.2))
    rw [hcross_swap]
  have hFz : (∫ w : ℂ, V.signedVFieldZ ν w ∂μ.μz) =
      2 * V.vLogInteraction ν.μz μ.μz + V.vLogInteraction ν.μv μ.μz := by
    unfold V.signedVFieldZ
    have hpot_z := integrable_log_norm_sub_of_kernel μ.μz ν.μz hint_μzνz
    have hpot_v := integrable_log_norm_sub_of_kernel μ.μz ν.μv hint_μzνv
    rw [integral_add (hpot_z.const_mul 2) hpot_v, integral_const_mul,
      integral_log_norm_sub_eq_vLogInteraction μ.μz ν.μz hint_μzνz,
      integral_log_norm_sub_eq_vLogInteraction μ.μz ν.μv hint_μzνv]
  let c := v13_smoothed_reference_squareCertificate P hn x v z hx hv
  have hSquare : V.signedVDualRemainder μ ν = c.remainder := by
    dsimp only [μ, ν]
    unfold V.signedVDualRemainder V.vLogInteraction
    change _ = V.signedVQuadraticForm c.data
    unfold V.signedVQuadraticForm
    dsimp [μ, ν, c, v13_smoothed_reference_squareCertificate,
      P0.L6Variations.l6PairDifference]
    rw [P.facts.q_eq,
      P0.L6Variations.li2LogInteraction_comm ν.μx μ.μx,
      P0.L6Variations.li2LogInteraction_comm ν.μv μ.μv,
      P0.L6Variations.li2LogInteraction_comm ν.μz μ.μz,
      hvz]
    simp only [μ, ν]
    simp only [v13SmoothedEmpiricalMeasures]
    ring
  have hResidual : V.signedVDualResidual μ ν = c.remainder :=
    (V.signedVDualResidual_eq_remainder μ ν hxx hvv hzz hFx hFv hFz).trans hSquare
  have hcmp := V.signedV_duality_field_comparison_of_square μ ν c hSquare
    hxx hvv hzz hFx hFv hFz
  have href := p4_reference_negative_energy_bound P
  linarith

/-- Full `V.SignedVDualityCertificate` for `v13SmoothedEmpiricalMeasures`
    against `P.measure`. -/
def v13SmoothedDualityCertificate
    {q n : ℕ} {hq : SignedVBaseRange q} (P : VReferencePackage q hq)
    (hn : 64 ≤ 4 * n)
    (x : Fin (4 * n) → ℝ) (v : Fin (5 * n) → ℝ) (z : Fin (4 * n) → ℂ)
    (hx : ∀ i, x i ∈ Set.Icc (0 : ℝ) 1)
    (hv : ∀ b, v b ∈ Set.Icc (0 : ℝ) 1) :
    V.SignedVDualityCertificate
      (v13SmoothedEmpiricalMeasures hq (by omega)
        (fun i => (x i : ℂ)) (fun b => (v b : ℂ)) z)
      P.measure := by
  let μ := v13SmoothedEmpiricalMeasures hq (by omega)
    (fun i => (x i : ℂ)) (fun b => (v b : ℂ)) z
  let ν := P.measure
  have hm : 0 < 4 * n := by omega
  have hx_abs : ∀ i, |x i| ≤ 1 := fun i => abs_le_one_of_mem_Icc (hx i)
  have hv_abs : ∀ b, |v b| ≤ 1 := fun b => abs_le_one_of_mem_Icc (hv b)
  letI : IsFiniteMeasure μ.μx := ⟨lt_top_iff_ne_top.mpr μ.finite_x⟩
  letI : IsFiniteMeasure μ.μv := ⟨lt_top_iff_ne_top.mpr μ.finite_v⟩
  letI : IsFiniteMeasure μ.μz := ⟨lt_top_iff_ne_top.mpr μ.finite_z⟩
  letI : IsFiniteMeasure ν.μx := ⟨lt_top_iff_ne_top.mpr ν.finite_x⟩
  letI : IsFiniteMeasure ν.μv := ⟨lt_top_iff_ne_top.mpr ν.finite_v⟩
  letI : IsFiniteMeasure ν.μz := ⟨lt_top_iff_ne_top.mpr ν.finite_z⟩
  have hint_μxνx : Integrable (fun p : ℂ × ℂ => li2LogKernel p.1 p.2) (μ.μx.prod ν.μx) :=
    integrable_li2LogKernel_translatedEmpiricalMeasure_prod_of_ae_norm_le hm _
      (referenceMeasure_x_norm_ae_le_one P)
  have hint_μvνv : Integrable (fun p : ℂ × ℂ => li2LogKernel p.1 p.2) (μ.μv.prod ν.μv) :=
    integrable_li2LogKernel_translatedEmpiricalMeasure_prod_of_ae_norm_le hm _
      (referenceMeasure_v_norm_ae_le_one P)
  have hint_μvνz : Integrable (fun p : ℂ × ℂ => li2LogKernel p.1 p.2) (μ.μv.prod ν.μz) :=
    integrable_li2LogKernel_translatedEmpiricalMeasure_prod_of_ae_norm_le hm _
      (referenceMeasure_z_norm_ae_le_q P)
  have hint_μzνz : Integrable (fun p : ℂ × ℂ => li2LogKernel p.1 p.2) (μ.μz.prod ν.μz) :=
    integrable_li2LogKernel_translatedEmpiricalMeasure_prod_of_ae_norm_le hm z
      (referenceMeasure_z_norm_ae_le_q P)
  have hint_μzνv : Integrable (fun p : ℂ × ℂ => li2LogKernel p.1 p.2) (μ.μz.prod ν.μv) :=
    integrable_li2LogKernel_translatedEmpiricalMeasure_prod_of_ae_norm_le hm z
      (referenceMeasure_v_norm_ae_le_one P)
  have hμx_tube : ∀ᵐ w ∂μ.μx, ‖w‖ ≤ V.v13DenominatorTubeRadius :=
    V.v13SmoothedRealEmpirical_norm_ae_le_one_add_three_div_4096 x hn hx_abs
  have hμv_tube : ∀ᵐ w ∂μ.μv, ‖w‖ ≤ V.v13DenominatorTubeRadius :=
    V.v13SmoothedRealEmpirical_norm_ae_le_one_add_three_div_4096 v hn hv_abs
  have hνx_tube : ∀ᵐ w ∂ν.μx, ‖w‖ ≤ V.v13DenominatorTubeRadius :=
    referenceMeasure_x_norm_ae_le_tubeRadius P
  have hνv_tube : ∀ᵐ w ∂ν.μv, ‖w‖ ≤ V.v13DenominatorTubeRadius :=
    referenceMeasure_v_norm_ae_le_tubeRadius P
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq.1
  have hden_μxνv : Integrable (V.v13DenominatorKernel q) (μ.μx.prod ν.μv) :=
    V.v13_denominatorKernel_integrable hq.1 μ.μx ν.μv hμx_tube hνv_tube
      (by norm_num [V.v13DenominatorTubeRadius])
      (by unfold V.v13DenominatorTubeRadius; nlinarith)
  have hden_νxμv : Integrable (V.v13DenominatorKernel q) (ν.μx.prod μ.μv) :=
    V.v13_denominatorKernel_integrable hq.1 ν.μx μ.μv hνx_tube hμv_tube
      (by norm_num [V.v13DenominatorTubeRadius])
      (by unfold V.v13DenominatorTubeRadius; nlinarith)
  have hxx : V.vLogInteraction μ.μx ν.μx = V.vLogInteraction ν.μx μ.μx := by
    unfold V.vLogInteraction
    rw [P0.L6Variations.li2LogInteraction_comm]
  have hvv : V.vLogInteraction μ.μv ν.μv = V.vLogInteraction ν.μv μ.μv := by
    unfold V.vLogInteraction
    rw [P0.L6Variations.li2LogInteraction_comm]
  have hzz : V.vLogInteraction μ.μz ν.μz = V.vLogInteraction ν.μz μ.μz := by
    unfold V.vLogInteraction
    rw [P0.L6Variations.li2LogInteraction_comm]
  have hvz : li2LogInteraction ν.μz μ.μv = li2LogInteraction μ.μv ν.μz :=
    P0.L6Variations.li2LogInteraction_comm ν.μz μ.μv
  have hFx : (∫ w : ℂ, V.signedVFieldX ν w ∂μ.μx) =
      2 * V.vLogInteraction ν.μx μ.μx - V.vCrossInteraction ν.q μ.μx ν.μv := by
    unfold V.signedVFieldX
    have hpot := integrable_log_norm_sub_of_kernel μ.μx ν.μx hint_μxνx
    have hcross : Integrable (fun w : ℂ => ∫ t : ℂ, V.vCrossKernel ν.q w t ∂ν.μv) μ.μx := by
      rw [P.facts.q_eq]
      exact hden_μxνv.integral_prod_left
    have hcross_prod : Integrable
        (fun p : ℂ × ℂ => V.vCrossKernel ν.q p.1 p.2)
        (μ.μx.prod ν.μv) := by
      have hden := hden_μxνv
      rw [← P.facts.q_eq] at hden
      change Integrable (fun p : ℂ × ℂ => Real.log ‖(ν.q : ℂ) + p.1 * p.2‖)
        (μ.μx.prod ν.μv) at hden
      simpa [V.vCrossKernel] using hden
    rw [integral_sub (hpot.const_mul 2) hcross, integral_const_mul,
      integral_log_norm_sub_eq_vLogInteraction μ.μx ν.μx hint_μxνx]
    congr 1
    rw [V.vCrossInteraction, ← integral_prod _ hcross_prod]
  have hFv : (∫ w : ℂ, V.signedVFieldV ν w ∂μ.μv) =
      2 * V.vLogInteraction ν.μv μ.μv + V.vLogInteraction ν.μz μ.μv -
        V.vCrossInteraction ν.q ν.μx μ.μv := by
    unfold V.signedVFieldV
    rw [P.facts.q_eq]
    have hpot_v := integrable_log_norm_sub_of_kernel μ.μv ν.μv hint_μvνv
    have hpot_z := integrable_log_norm_sub_of_kernel μ.μv ν.μz hint_μvνz
    have hcross : Integrable (fun w : ℂ => ∫ t : ℂ, V.vCrossKernel q t w ∂ν.μx) μ.μv := by
      exact hden_νxμv.integral_prod_right
    have hcross_prod : Integrable
        (fun p : ℂ × ℂ => V.vCrossKernel q p.2 p.1)
        (μ.μv.prod ν.μx) := by
      rw [← Measure.prod_swap]
      have hm : Measurable (Prod.swap : ℂ × ℂ → ℂ × ℂ) := measurable_swap
      have hf : Measurable (fun p : ℂ × ℂ => V.vCrossKernel q p.2 p.1) := by
        unfold V.vCrossKernel
        fun_prop
      apply (integrable_map_measure hf.aestronglyMeasurable hm.aemeasurable).mpr
      have hden := hden_νxμv
      change Integrable (fun p : ℂ × ℂ => Real.log ‖(q : ℂ) + p.1 * p.2‖)
        (ν.μx.prod μ.μv) at hden
      simpa [Function.comp_def, V.vCrossKernel] using hden
    let f : ℂ → ℝ := fun w => ∫ t : ℂ, Real.log ‖w - t‖ ∂ν.μv
    let g : ℂ → ℝ := fun w => ∫ t : ℂ, Real.log ‖w - t‖ ∂ν.μz
    let k : ℂ → ℝ := fun w => ∫ t : ℂ, V.vCrossKernel q t w ∂ν.μx
    have hf : Integrable f μ.μv := by simpa [f] using hpot_v
    have hg : Integrable g μ.μv := by simpa [g] using hpot_z
    have hk : Integrable k μ.μv := by simpa [k] using hcross
    change (∫ w : ℂ, (2 * f w + g w) - k w ∂μ.μv) = _
    have hsplit :
        (∫ w : ℂ, (2 * f w + g w) - k w ∂μ.μv) =
          (∫ w : ℂ, 2 * f w + g w ∂μ.μv) - ∫ w : ℂ, k w ∂μ.μv := by
      exact integral_sub ((hf.const_mul 2).add hg) hk
    rw [hsplit, integral_add (hf.const_mul 2) hg, integral_const_mul,
      integral_log_norm_sub_eq_vLogInteraction μ.μv ν.μv hint_μvνv,
      integral_log_norm_sub_eq_vLogInteraction μ.μv ν.μz hint_μvνz]
    rw [V.vCrossInteraction, ← integral_prod _ hcross_prod]
    have hcross_swap :
        (∫ p : ℂ × ℂ, V.vCrossKernel q p.2 p.1 ∂(μ.μv.prod ν.μx)) =
          ∫ p : ℂ × ℂ, V.vCrossKernel q p.1 p.2 ∂(ν.μx.prod μ.μv) := by
      simpa [Prod.swap] using
        (MeasureTheory.integral_prod_swap
          (μ := ν.μx) (ν := μ.μv)
          (fun p : ℂ × ℂ => V.vCrossKernel q p.1 p.2))
    rw [hcross_swap]
  have hFz : (∫ w : ℂ, V.signedVFieldZ ν w ∂μ.μz) =
      2 * V.vLogInteraction ν.μz μ.μz + V.vLogInteraction ν.μv μ.μz := by
    unfold V.signedVFieldZ
    have hpot_z := integrable_log_norm_sub_of_kernel μ.μz ν.μz hint_μzνz
    have hpot_v := integrable_log_norm_sub_of_kernel μ.μz ν.μv hint_μzνv
    rw [integral_add (hpot_z.const_mul 2) hpot_v, integral_const_mul,
      integral_log_norm_sub_eq_vLogInteraction μ.μz ν.μz hint_μzνz,
      integral_log_norm_sub_eq_vLogInteraction μ.μz ν.μv hint_μzνv]
  let c := v13_smoothed_reference_squareCertificate P hn x v z hx hv
  have hSquare : V.signedVDualRemainder μ ν = c.remainder := by
    dsimp only [μ, ν]
    unfold V.signedVDualRemainder V.vLogInteraction
    change _ = V.signedVQuadraticForm c.data
    unfold V.signedVQuadraticForm
    dsimp [μ, ν, c, v13_smoothed_reference_squareCertificate,
      P0.L6Variations.l6PairDifference]
    rw [P.facts.q_eq,
      P0.L6Variations.li2LogInteraction_comm ν.μx μ.μx,
      P0.L6Variations.li2LogInteraction_comm ν.μv μ.μv,
      P0.L6Variations.li2LogInteraction_comm ν.μz μ.μz,
      hvz]
    simp only [μ, ν]
    simp only [v13SmoothedEmpiricalMeasures]
    ring
  refine
    { square := c
      residual_eq :=
        (V.signedVDualResidual_eq_remainder μ ν hxx hvv hzz hFx hFv hFz).trans hSquare }

/-- C1–C4 duality comparison of `v13SmoothedEmpiricalMeasures` against `P.measure`
    in the `H5-hcore/README.md` §4 interface form (including the non-negative
    `(3 / 2) * Real.log (q : ℝ)` shift). -/
theorem v13_smoothed_duality_comparison_of_reference
    {q n : ℕ} {hq : SignedVBaseRange q} (P : VReferencePackage q hq)
    (hn : 64 ≤ 4 * n)
    (x : Fin (4 * n) → ℝ) (v : Fin (5 * n) → ℝ) (z : Fin (4 * n) → ℂ)
    (hx : ∀ i, x i ∈ Set.Icc (0 : ℝ) 1)
    (hv : ∀ b, v b ∈ Set.Icc (0 : ℝ) 1)
    (_hz : ∀ i, z i ∈ V.vContourTrace q) :
    let μ := v13SmoothedEmpiricalMeasures hq (by omega)
      (fun i => (x i : ℂ)) (fun b => (v b : ℂ)) z
    let ν := P.measure
    V.signedVQuadratic μ ≤
      -(((vQlow q : ℚ) : ℝ) - (3 / 2 : ℝ) * Real.log (q : ℝ)) +
        (∫ w : ℂ, V.signedVFieldX ν w ∂μ.μx) +
        (∫ w : ℂ, V.signedVFieldV ν w ∂μ.μv) +
        (∫ w : ℂ, V.signedVFieldZ ν w ∂μ.μz) := by
  intro μ ν
  have hunshifted := v13_smoothed_duality_comparison_of_reference_unshifted P hn x v z hx hv
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
    have : 1 ≤ q := by linarith [hq.1]
    exact_mod_cast this
  have hlog : 0 ≤ (3 / 2 : ℝ) * Real.log (q : ℝ) :=
    mul_nonneg (by norm_num) (Real.log_nonneg hq1)
  linarith

/-- Field-assembled constructor alias for `v13SmoothedDualityCertificate`. -/
def v13SmoothedDualityCertificate_of_fields
    {q n : ℕ} {hq : SignedVBaseRange q} (P : VReferencePackage q hq)
    (hn : 64 ≤ 4 * n)
    (x : Fin (4 * n) → ℝ) (v : Fin (5 * n) → ℝ) (z : Fin (4 * n) → ℂ)
    (hx : ∀ i, x i ∈ Set.Icc (0 : ℝ) 1)
    (hv : ∀ b, v b ∈ Set.Icc (0 : ℝ) 1) :
    V.SignedVDualityCertificate
      (v13SmoothedEmpiricalMeasures hq (by omega)
        (fun i => (x i : ℂ)) (fun b => (v b : ℂ)) z)
      P.measure :=
  v13SmoothedDualityCertificate P hn x v z hx hv

/-- Exported alias for the C1–C4 smoothed duality comparison with the
    `(3 / 2) * Real.log (q : ℝ)` shift. -/
theorem s0T_smoothed_duality_comparison
    {q n : ℕ} {hq : SignedVBaseRange q} (P : VReferencePackage q hq)
    (hn : 64 ≤ 4 * n)
    (x : Fin (4 * n) → ℝ) (v : Fin (5 * n) → ℝ) (z : Fin (4 * n) → ℂ)
    (hx : ∀ i, x i ∈ Set.Icc (0 : ℝ) 1)
    (hv : ∀ b, v b ∈ Set.Icc (0 : ℝ) 1)
    (hz : ∀ i, z i ∈ V.vContourTrace q) :
    let μ := v13SmoothedEmpiricalMeasures hq (by omega)
      (fun i => (x i : ℂ)) (fun b => (v b : ℂ)) z
    let ν := P.measure
    V.signedVQuadratic μ ≤
      -(((vQlow q : ℚ) : ℝ) - (3 / 2 : ℝ) * Real.log (q : ℝ)) +
        (∫ w : ℂ, V.signedVFieldX ν w ∂μ.μx) +
        (∫ w : ℂ, V.signedVFieldV ν w ∂μ.μv) +
        (∫ w : ℂ, V.signedVFieldZ ν w ∂μ.μz) :=
  v13_smoothed_duality_comparison_of_reference P hn x v z hx hv hz

/-- Exported alias for the unshifted C1–C4 smoothed duality comparison. -/
theorem s0T_smoothed_duality_lower
    {q n : ℕ} {hq : SignedVBaseRange q} (P : VReferencePackage q hq)
    (hn : 64 ≤ 4 * n)
    (x : Fin (4 * n) → ℝ) (v : Fin (5 * n) → ℝ) (z : Fin (4 * n) → ℂ)
    (hx : ∀ i, x i ∈ Set.Icc (0 : ℝ) 1)
    (hv : ∀ b, v b ∈ Set.Icc (0 : ℝ) 1) :
    let μ := v13SmoothedEmpiricalMeasures hq (by omega)
      (fun i => (x i : ℂ)) (fun b => (v b : ℂ)) z
    let ν := P.measure
    V.signedVQuadratic μ ≤
      -((vQlow q : ℚ) : ℝ) +
        (∫ w : ℂ, V.signedVFieldX ν w ∂μ.μx) +
        (∫ w : ℂ, V.signedVFieldV ν w ∂μ.μv) +
        (∫ w : ℂ, V.signedVFieldZ ν w ∂μ.μz) :=
  v13_smoothed_duality_comparison_of_reference_unshifted P hn x v z hx hv

/-- Lower-bound orientation of the unshifted C1–C4 smoothed duality inequality
    for `-V.signedVQuadratic μ`. -/
theorem s0T_smoothed_duality_lower_actual
    {q n : ℕ} {hq : SignedVBaseRange q} (P : VReferencePackage q hq)
    (hn : 64 ≤ 4 * n)
    (x : Fin (4 * n) → ℝ) (v : Fin (5 * n) → ℝ) (z : Fin (4 * n) → ℂ)
    (hx : ∀ i, x i ∈ Set.Icc (0 : ℝ) 1)
    (hv : ∀ b, v b ∈ Set.Icc (0 : ℝ) 1) :
    let μ := v13SmoothedEmpiricalMeasures hq (by omega)
      (fun i => (x i : ℂ)) (fun b => (v b : ℂ)) z
    let ν := P.measure
    ((vQlow q : ℚ) : ℝ) -
        (∫ w : ℂ, V.signedVFieldX ν w ∂μ.μx) -
        (∫ w : ℂ, V.signedVFieldV ν w ∂μ.μv) -
        (∫ w : ℂ, V.signedVFieldZ ν w ∂μ.μz) ≤
      -V.signedVQuadratic μ := by
  intro μ ν
  have h := v13_smoothed_duality_comparison_of_reference_unshifted P hn x v z hx hv
  linarith

end

end Li2Lean.B3

#print axioms Li2Lean.B3.v13_smoothed_reference_squareCertificate
#print axioms Li2Lean.B3.v13SmoothedDualityCertificate
#print axioms Li2Lean.B3.v13SmoothedDualityCertificate_of_fields
#print axioms Li2Lean.B3.v13_smoothed_duality_comparison_of_reference_unshifted
#print axioms Li2Lean.B3.v13_smoothed_duality_comparison_of_reference
#print axioms Li2Lean.B3.s0T_smoothed_duality_comparison
#print axioms Li2Lean.B3.s0T_smoothed_duality_lower
#print axioms Li2Lean.B3.s0T_smoothed_duality_lower_actual
