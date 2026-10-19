/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B3.ReferencePackageGeneric
import Li2Lean.B3.E1ConcreteInteractions
import Li2Lean.B3.VBallBoundClosedBall

/-!
# `q`-Generic Product Integrability (`SignedVReferenceIntegrable` and `V13InteractionIntegrability`) (`H6-dual`)

This module proves the `q`-generic product-measure integrability obligations for
every `q ∈ {2, 3, 4, 5, 6, 7}` reference measure `v13RefMeasure R N`:

1. **Uniform Fixed-Centre `L¹` Bound (`integral_norm_li2LogKernel_le_of_vBallBound`)**:
   For any finite measure `μ` satisfying `VBallBound μ A` (`0 ≤ A`) and bounded support
   `∀ᵐ t ∂μ, ‖t‖ ≤ R₂` (`0 ≤ R₂`), and any centre `w : ℂ` with `‖w‖ ≤ R₁` (`0 ≤ R₁`),
   `t ↦ li2LogKernel w t = -Real.log ‖w - t‖` is `μ`-integrable and satisfies the
   centre-independent bound
   `∫ t, ‖li2LogKernel w t‖ ∂μ ≤ A + μ.real Set.univ * max |Real.log (1 / 2)| (Real.log (max 1 (R₁ + R₂)))`.
2. **Product Integrability of `li2LogKernel` (`integrable_li2LogKernel_prod_of_vBallBound`)**:
   For any two finite measures `μ₁, μ₂` where `∀ᵐ w ∂μ₁, ‖w‖ ≤ R₁`, `VBallBound μ₂ A₂`, and
   `∀ᵐ t ∂μ₂, ‖t‖ ≤ R₂`, `fun p : ℂ × ℂ => li2LogKernel p.1 p.2` is integrable on `μ₁.prod μ₂`
   via `MeasureTheory.integrable_prod_iff`.
3. **Product Integrability of `V.vCrossKernel q` (`integrable_vCrossKernel_prod`)**:
   For `2 ≤ q` and finite measures `μ₁, μ₂` supported a.e. in the closed unit disk
   (`‖u‖ ≤ 1`, `‖v‖ ≤ 1`), `1 ≤ ‖(q : ℂ) + u * v‖ ≤ q + 1` a.e. on `μ₁.prod μ₂`, so
   `0 ≤ V.vCrossKernel q u v ≤ Real.log (q + 1)` and `V.vCrossKernel q` is integrable
   on `μ₁.prod μ₂`.
4. **Package-Level Constructors**:
   - `signedVReferenceIntegrable_of_supports_and_ballBounds`
   - `signedVReferenceIntegrable_of_ballBound`
   - `v13InteractionIntegrability_of_ballBound`
-/

namespace Li2Lean.B3

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped BigOperators ENNReal

/-! ## 1. Near-Field and Far-Field Uniform `L¹` Bounds for `Real.log ‖w - t‖` -/

/-- Near-ball integrability and uniform `L¹` bound `≤ A` for `t ↦ Real.log ‖w - t‖`
    on `Metric.closedBall w (1 / 2)` under `VBallBound μ A`. -/
theorem integrableOn_and_integral_norm_log_sub_closedBall_half_le
    {μ : Measure ℂ} [IsFiniteMeasure μ] {A : ℝ}
    (hA : 0 ≤ A) (hball : VBallBound μ A) (w : ℂ) :
    IntegrableOn (fun t : ℂ => Real.log ‖w - t‖) (Metric.closedBall w (1 / 2)) μ ∧
      (∫ t in Metric.closedBall w (1 / 2), ‖Real.log ‖w - t‖‖ ∂μ) ≤ A := by
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
        (vBallBound_closedBall hball w (le_of_lt (Real.exp_pos (-s))))
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
  have hneg_ae : (fun t : ℂ => -Real.log ‖w - t‖) =ᵐ[μ.restrict N] g := by
    filter_upwards [ae_restrict_mem hN] with t ht
    have hdist : ‖w - t‖ ≤ 1 / 2 := by
      simpa [N, Metric.mem_closedBall, dist_comm, Complex.dist_eq] using ht
    have hlog_nonpos : Real.log ‖w - t‖ ≤ 0 :=
      Real.log_nonpos (norm_nonneg _) (by linarith)
    dsimp [g]
    exact (max_eq_right (neg_nonneg.mpr hlog_nonpos)).symm
  have hnorm_ae : (fun t : ℂ => ‖Real.log ‖w - t‖‖) =ᵐ[μ.restrict N] g := by
    filter_upwards [ae_restrict_mem hN] with t ht
    have hdist : ‖w - t‖ ≤ 1 / 2 := by
      simpa [N, Metric.mem_closedBall, dist_comm, Complex.dist_eq] using ht
    have hlog_nonpos : Real.log ‖w - t‖ ≤ 0 :=
      Real.log_nonpos (norm_nonneg _) (by linarith)
    rw [Real.norm_eq_abs, abs_of_nonpos hlog_nonpos]
    dsimp [g]
    exact (max_eq_right (neg_nonneg.mpr hlog_nonpos)).symm
  have hneg_int : IntegrableOn (fun t : ℂ => -Real.log ‖w - t‖) N μ :=
    hg_int.congr hneg_ae.symm
  have hint : IntegrableOn (fun t : ℂ => Real.log ‖w - t‖) N μ := by
    have htmp := hneg_int.neg
    refine htmp.congr ?_
    filter_upwards [] with t
    simp
  have hg_integral_le : (∫ t, g t ∂(μ.restrict N)) ≤ A := by
    have hofReal : ENNReal.ofReal (∫ t, g t ∂(μ.restrict N)) ≤ ENNReal.ofReal A := by
      rw [ofReal_integral_eq_lintegral_ofReal hg_int hg_nonneg]
      exact hgE_le
    have hI : 0 ≤ ∫ t, g t ∂(μ.restrict N) :=
      integral_nonneg (fun _ => le_max_left 0 _)
    have hto := ENNReal.toReal_mono ENNReal.ofReal_ne_top hofReal
    rw [ENNReal.toReal_ofReal hI, ENNReal.toReal_ofReal hA] at hto
    exact hto
  refine ⟨hint, ?_⟩
  rw [integral_congr_ae hnorm_ae]
  exact hg_integral_le

/-- Far-field integrability of `t ↦ Real.log ‖w - t‖` on `(Metric.closedBall w (1 / 2))ᶜ`
    for any finite measure `μ` with bounded support `∀ᵐ t ∂μ, ‖t‖ ≤ R`. -/
theorem integrableOn_log_norm_sub_compl_closedBall_half'
    {μ : Measure ℂ} [IsFiniteMeasure μ] {R : ℝ}
    (_hR : 0 ≤ R) (hbdd : ∀ᵐ t ∂μ, ‖t‖ ≤ R) (w : ℂ) :
    IntegrableOn (fun t : ℂ => Real.log ‖w - t‖) (Metric.closedBall w (1 / 2))ᶜ μ := by
  let N : Set ℂ := Metric.closedBall w (1 / 2)
  have hN : MeasurableSet N := Metric.isClosed_closedBall.measurableSet
  let U : ℝ := max 1 (‖w‖ + R)
  let M : ℝ := max |Real.log (1 / 2)| |Real.log U|
  have hmeas : Measurable (fun t : ℂ => Real.log ‖w - t‖) :=
    (measurable_const.sub measurable_id).norm.log
  refine Measure.integrableOn_of_bounded (M := M) (measure_ne_top μ Nᶜ)
    hmeas.aestronglyMeasurable ?_
  have hbdd_restrict : ∀ᵐ t ∂(μ.restrict Nᶜ), ‖t‖ ≤ R := ae_restrict_of_ae hbdd
  filter_upwards [ae_restrict_mem hN.compl, hbdd_restrict] with t ht htR
  have hdist : (1 / 2 : ℝ) < ‖w - t‖ := by
    have hnot : ¬ dist t w ≤ 1 / 2 := fun h => ht (Metric.mem_closedBall.mpr h)
    simpa [dist_comm, Complex.dist_eq] using lt_of_not_ge hnot
  have hpos : 0 < ‖w - t‖ := lt_trans (by norm_num) hdist
  have hupper : ‖w - t‖ ≤ U := by
    have htri : ‖w - t‖ ≤ ‖w‖ + R := by
      calc
        ‖w - t‖ ≤ ‖w‖ + ‖t‖ := norm_sub_le w t
        _ ≤ ‖w‖ + R := add_le_add (le_refl _) htR
    exact htri.trans (le_max_right 1 _)
  have hlo : Real.log (1 / 2) ≤ Real.log ‖w - t‖ :=
    Real.log_le_log (by norm_num) hdist.le
  have hhi : Real.log ‖w - t‖ ≤ Real.log U :=
    Real.log_le_log hpos hupper
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · linarith [neg_abs_le (Real.log (1 / 2)), le_max_left |Real.log (1 / 2)| |Real.log U|]
  · linarith [le_abs_self (Real.log U), le_max_right |Real.log (1 / 2)| |Real.log U|]

/-- Far-field uniform `L¹` bound on `(Metric.closedBall w (1 / 2))ᶜ` when `‖w‖ ≤ R₁`
    and `∀ᵐ t ∂μ, ‖t‖ ≤ R₂`. -/
theorem integral_norm_log_sub_compl_closedBall_half_le
    {μ : Measure ℂ} [IsFiniteMeasure μ] {R₁ R₂ : ℝ}
    (_hR₁ : 0 ≤ R₁) (hR₂ : 0 ≤ R₂)
    (hbdd : ∀ᵐ t ∂μ, ‖t‖ ≤ R₂) {w : ℂ} (hw : ‖w‖ ≤ R₁) :
    (∫ t in (Metric.closedBall w (1 / 2))ᶜ, ‖Real.log ‖w - t‖‖ ∂μ) ≤
      μ.real Set.univ * max |Real.log (1 / 2)| (Real.log (max 1 (R₁ + R₂))) := by
  let N : Set ℂ := Metric.closedBall w (1 / 2)
  have hN : MeasurableSet N := Metric.isClosed_closedBall.measurableSet
  let U : ℝ := max 1 (R₁ + R₂)
  let M : ℝ := max |Real.log (1 / 2)| (Real.log U)
  have hM_nonneg : 0 ≤ M := le_trans (abs_nonneg _) (le_max_left _ _)
  have hfar := integrableOn_log_norm_sub_compl_closedBall_half' hR₂ hbdd w
  have hbdd_restrict : ∀ᵐ t ∂(μ.restrict Nᶜ), ‖t‖ ≤ R₂ := ae_restrict_of_ae hbdd
  have hpointwise : ∀ᵐ t ∂(μ.restrict Nᶜ), ‖Real.log ‖w - t‖‖ ≤ M := by
    filter_upwards [ae_restrict_mem hN.compl, hbdd_restrict] with t ht htR
    have hdist : (1 / 2 : ℝ) < ‖w - t‖ := by
      have hnot : ¬ dist t w ≤ 1 / 2 := fun h => ht (Metric.mem_closedBall.mpr h)
      simpa [dist_comm, Complex.dist_eq] using lt_of_not_ge hnot
    have hpos : 0 < ‖w - t‖ := lt_trans (by norm_num) hdist
    have hupper : ‖w - t‖ ≤ U := by
      have htri : ‖w - t‖ ≤ R₁ + R₂ :=
        (norm_sub_le w t).trans (add_le_add hw htR)
      exact htri.trans (le_max_right 1 _)
    have hlo : Real.log (1 / 2) ≤ Real.log ‖w - t‖ :=
      Real.log_le_log (by norm_num) hdist.le
    have hhi : Real.log ‖w - t‖ ≤ Real.log U :=
      Real.log_le_log hpos hupper
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · linarith [neg_abs_le (Real.log (1 / 2)), le_max_left |Real.log (1 / 2)| (Real.log U)]
    · linarith [le_max_right |Real.log (1 / 2)| (Real.log U)]
  calc
    (∫ t in Nᶜ, ‖Real.log ‖w - t‖‖ ∂μ)
        ≤ ∫ _t in Nᶜ, M ∂μ :=
      integral_mono_ae hfar.norm (integrable_const M) hpointwise
    _ = μ.real Nᶜ * M := by
      rw [integral_const, Measure.real, Measure.restrict_apply_univ, smul_eq_mul]
      rfl
    _ ≤ μ.real Set.univ * M := by
      exact mul_le_mul_of_nonneg_right
        (measureReal_mono (Set.subset_univ Nᶜ) (measure_ne_top μ Set.univ)) hM_nonneg

/-- Full-space integrability of `t ↦ li2LogKernel w t = -Real.log ‖w - t‖` for any finite
    measure `μ` satisfying `VBallBound μ A` and `∀ᵐ t ∂μ, ‖t‖ ≤ R`. -/
theorem integrable_li2LogKernel_of_vBallBound_of_ae_norm_le
    {μ : Measure ℂ} [IsFiniteMeasure μ] {A R : ℝ}
    (hA : 0 ≤ A) (hR : 0 ≤ R)
    (hball : VBallBound μ A) (hbdd : ∀ᵐ t ∂μ, ‖t‖ ≤ R) (w : ℂ) :
    Integrable (fun t : ℂ => li2LogKernel w t) μ := by
  have hnear := (integrableOn_and_integral_norm_log_sub_closedBall_half_le hA hball w).1
  have hfar := integrableOn_log_norm_sub_compl_closedBall_half' hR hbdd w
  have hunion := hnear.union hfar
  rw [Set.union_compl_self, integrableOn_univ] at hunion
  have hneg := hunion.neg
  change Integrable (fun t : ℂ => -Real.log ‖w - t‖) μ
  refine hneg.congr ?_
  filter_upwards [] with t
  rfl

/-- Uniform centre-independent `L¹` bound for `t ↦ li2LogKernel w t` when `‖w‖ ≤ R₁`. -/
theorem integral_norm_li2LogKernel_le_of_vBallBound
    {μ : Measure ℂ} [IsFiniteMeasure μ] {A R₁ R₂ : ℝ}
    (hA : 0 ≤ A) (hR₁ : 0 ≤ R₁) (hR₂ : 0 ≤ R₂)
    (hball : VBallBound μ A) (hbdd : ∀ᵐ t ∂μ, ‖t‖ ≤ R₂)
    {w : ℂ} (hw : ‖w‖ ≤ R₁) :
    (∫ t : ℂ, ‖li2LogKernel w t‖ ∂μ) ≤
      A + μ.real Set.univ * max |Real.log (1 / 2)| (Real.log (max 1 (R₁ + R₂))) := by
  let N : Set ℂ := Metric.closedBall w (1 / 2)
  have hN : MeasurableSet N := Metric.isClosed_closedBall.measurableSet
  have hnear := integrableOn_and_integral_norm_log_sub_closedBall_half_le hA hball w
  have hfar := integral_norm_log_sub_compl_closedBall_half_le hR₁ hR₂ hbdd hw
  have hint_log : Integrable (fun t : ℂ => Real.log ‖w - t‖) μ := by
    have hunion := hnear.1.union (integrableOn_log_norm_sub_compl_closedBall_half' hR₂ hbdd w)
    rw [Set.union_compl_self, integrableOn_univ] at hunion
    exact hunion
  have hnorm_eq : (fun t : ℂ => ‖li2LogKernel w t‖) = (fun t : ℂ => ‖Real.log ‖w - t‖‖) := by
    funext t
    simp [li2LogKernel]
  rw [hnorm_eq, ← integral_add_compl hN hint_log.norm]
  exact add_le_add hnear.2 hfar

/-! ## 2. Product Integrability of `li2LogKernel` and `V.vCrossKernel q` -/

theorem measurable_li2LogKernel_uncurry :
    Measurable (fun p : ℂ × ℂ => li2LogKernel p.1 p.2) := by
  unfold li2LogKernel
  exact (measurable_fst.sub measurable_snd).norm.log.neg

/-- Product-measure integrability of `li2LogKernel` on `μ₁.prod μ₂` for any two finite
    measures where `μ₁` has bounded support and `μ₂` has `VBallBound` + bounded support. -/
theorem integrable_li2LogKernel_prod_of_vBallBound
    {μ₁ μ₂ : Measure ℂ} [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂]
    {A₂ R₁ R₂ : ℝ} (hA₂ : 0 ≤ A₂) (hR₁ : 0 ≤ R₁) (hR₂ : 0 ≤ R₂)
    (hbdd₁ : ∀ᵐ w ∂μ₁, ‖w‖ ≤ R₁)
    (hball₂ : VBallBound μ₂ A₂)
    (hbdd₂ : ∀ᵐ t ∂μ₂, ‖t‖ ≤ R₂) :
    Integrable (fun p : ℂ × ℂ => li2LogKernel p.1 p.2) (μ₁.prod μ₂) := by
  have hmeas : AEStronglyMeasurable (fun p : ℂ × ℂ => li2LogKernel p.1 p.2)
      (μ₁.prod μ₂) :=
    measurable_li2LogKernel_uncurry.aestronglyMeasurable
  rw [integrable_prod_iff hmeas]
  refine ⟨?_, ?_⟩
  · exact ae_of_all μ₁ (fun w =>
      integrable_li2LogKernel_of_vBallBound_of_ae_norm_le hA₂ hR₂ hball₂ hbdd₂ w)
  · let K : ℝ :=
      A₂ + μ₂.real Set.univ * max |Real.log (1 / 2)| (Real.log (max 1 (R₁ + R₂)))
    refine Integrable.of_bound hmeas.norm.integral_prod_right' K ?_
    filter_upwards [hbdd₁] with w hw
    rw [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    exact integral_norm_li2LogKernel_le_of_vBallBound hA₂ hR₁ hR₂ hball₂ hbdd₂ hw

theorem measurable_vCrossKernel_uncurry (q : ℕ) :
    Measurable (fun p : ℂ × ℂ => V.vCrossKernel q p.1 p.2) := by
  unfold V.vCrossKernel
  exact (measurable_const.add (measurable_fst.mul measurable_snd)).norm.log

/-- Product-measure integrability of `V.vCrossKernel q` on `μ₁.prod μ₂` for `2 ≤ q`
    and finite measures supported a.e. in the closed unit disk. -/
theorem integrable_vCrossKernel_prod
    {μ₁ μ₂ : Measure ℂ} [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂]
    {q : ℕ} (hq : 2 ≤ q)
    (hbdd₁ : ∀ᵐ u ∂μ₁, ‖u‖ ≤ 1)
    (hbdd₂ : ∀ᵐ v ∂μ₂, ‖v‖ ≤ 1) :
    Integrable (fun p : ℂ × ℂ => V.vCrossKernel q p.1 p.2) (μ₁.prod μ₂) := by
  have hmeas : AEStronglyMeasurable (fun p : ℂ × ℂ => V.vCrossKernel q p.1 p.2)
      (μ₁.prod μ₂) :=
    (measurable_vCrossKernel_uncurry q).aestronglyMeasurable
  have h1 := (Measure.quasiMeasurePreserving_fst (μ := μ₁) (ν := μ₂)).ae hbdd₁
  have h2 := (Measure.quasiMeasurePreserving_snd (μ := μ₁) (ν := μ₂)).ae hbdd₂
  refine Integrable.of_bound hmeas (Real.log ((q : ℝ) + 1)) ?_
  filter_upwards [h1, h2] with p hp1 hp2
  have huv : ‖p.1 * p.2‖ ≤ 1 := by
    rw [norm_mul]
    exact mul_le_one₀ hp1 (norm_nonneg _) hp2
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hq_norm : ‖(q : ℂ)‖ = (q : ℝ) := Complex.norm_natCast q
  have htri_lo : ‖(q : ℂ)‖ ≤ ‖(q : ℂ) + p.1 * p.2‖ + ‖p.1 * p.2‖ := by
    have h := norm_add_le ((q : ℂ) + p.1 * p.2) (-(p.1 * p.2))
    simpa only [add_neg_cancel_right, norm_neg] using h
  have hlo : 1 ≤ ‖(q : ℂ) + p.1 * p.2‖ := by linarith
  have hhi : ‖(q : ℂ) + p.1 * p.2‖ ≤ (q : ℝ) + 1 := by
    have h := norm_add_le (q : ℂ) (p.1 * p.2)
    linarith
  have hlog_nonneg : 0 ≤ Real.log ‖(q : ℂ) + p.1 * p.2‖ :=
    Real.log_nonneg hlo
  have hlog_le : Real.log ‖(q : ℂ) + p.1 * p.2‖ ≤ Real.log ((q : ℝ) + 1) :=
    Real.log_le_log (by linarith) hhi
  unfold V.vCrossKernel
  rw [Real.norm_eq_abs, abs_of_nonneg hlog_nonneg]
  exact hlog_le

/-! ## 3. Support-to-Norm Helpers and Package-Level Integrability Theorems -/

theorem ae_norm_le_one_of_support_Icc
    {μ : Measure ℂ} (hsupp : μ (Complex.ofReal '' Set.Icc (0 : ℝ) 1)ᶜ = 0) :
    ∀ᵐ w ∂μ, ‖w‖ ≤ 1 := by
  have hmem : ∀ᵐ w ∂μ, w ∈ Complex.ofReal '' Set.Icc (0 : ℝ) 1 := by
    rw [ae_iff]
    exact hsupp
  filter_upwards [hmem] with w ⟨r, hr, hwr⟩
  subst w
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr.1]
  exact hr.2

theorem ae_norm_le_q_of_support_source
    {μ : Measure ℂ} {q : ℕ} (hq : 2 ≤ q)
    (hsupp : μ ((Complex.ofReal '' Set.Icc (-(q : ℝ)) (-3 / 5)) ∪
      Metric.sphere 0 (3 / 5))ᶜ = 0) :
    ∀ᵐ w ∂μ, ‖w‖ ≤ (q : ℝ) := by
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hmem : ∀ᵐ w ∂μ,
      w ∈ (Complex.ofReal '' Set.Icc (-(q : ℝ)) (-3 / 5)) ∪ Metric.sphere 0 (3 / 5) := by
    rw [ae_iff]
    exact hsupp
  filter_upwards [hmem] with w hw
  rcases hw with ⟨r, hr, rfl⟩ | hw
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith [hr.2])]
    linarith [hr.1]
  · have hdist : ‖w‖ = (3 / 5 : ℝ) := by
      simpa [Metric.mem_sphere, dist_zero_right] using hw
    linarith

/-- `SignedVReferenceIntegrable ν` for any `ν : V.SignedVMeasures` satisfying the standard
    support and `VBallBound` conditions. -/
theorem signedVReferenceIntegrable_of_supports_and_ballBounds
    (ν : V.SignedVMeasures) {Ax Av Az : ℝ}
    (hAx : 0 ≤ Ax) (hAv : 0 ≤ Av) (hAz : 0 ≤ Az)
    (hx_supp : ν.μx (Complex.ofReal '' Set.Icc (0 : ℝ) 1)ᶜ = 0)
    (hv_supp : ν.μv (Complex.ofReal '' Set.Icc (0 : ℝ) 1)ᶜ = 0)
    (hz_supp : ν.μz ((Complex.ofReal '' Set.Icc (-(ν.q : ℝ)) (-3 / 5)) ∪
      Metric.sphere 0 (3 / 5))ᶜ = 0)
    (hx_ball : VBallBound ν.μx Ax)
    (hv_ball : VBallBound ν.μv Av)
    (hz_ball : VBallBound ν.μz Az) :
    SignedVReferenceIntegrable ν := by
  letI : IsFiniteMeasure ν.μx := ⟨ν.finite_x.lt_top⟩
  letI : IsFiniteMeasure ν.μv := ⟨ν.finite_v.lt_top⟩
  letI : IsFiniteMeasure ν.μz := ⟨ν.finite_z.lt_top⟩
  have hq0 : (0 : ℝ) ≤ (ν.q : ℝ) := Nat.cast_nonneg ν.q
  have hx_ae := ae_norm_le_one_of_support_Icc hx_supp
  have hv_ae := ae_norm_le_one_of_support_Icc hv_supp
  have hz_ae := ae_norm_le_q_of_support_source ν.q_lower hz_supp
  refine {
    xx := integrable_li2LogKernel_prod_of_vBallBound hAx zero_le_one zero_le_one
      hx_ae hx_ball hx_ae
    vv := integrable_li2LogKernel_prod_of_vBallBound hAv zero_le_one zero_le_one
      hv_ae hv_ball hv_ae
    zz := integrable_li2LogKernel_prod_of_vBallBound hAz hq0 hq0
      hz_ae hz_ball hz_ae
    vz := integrable_li2LogKernel_prod_of_vBallBound hAz zero_le_one hq0
      hv_ae hz_ball hz_ae
    xv := integrable_vCrossKernel_prod ν.q_lower hx_ae hv_ae }

/-- `q`-generic constructor of `SignedVReferenceIntegrable (v13RefMeasure R N)`
    from `V13DecodedRowBounds q R`, `V13MeasureNormalization`, and the three
    `VBallBound` certificates. -/
theorem signedVReferenceIntegrable_of_ballBound
    {q : ℕ} {hq : SignedVBaseRange q}
    (R : V13DecodedRows q)
    (rows : V13DecodedRowBounds q R)
    (N : V13MeasureNormalization hq (v13RefRaw R))
    {Ax Av Az : ℝ}
    (hAx : 0 ≤ Ax) (hAv : 0 ≤ Av) (hAz : 0 ≤ Az)
    (hx_ball : VBallBound (v13RefMeasure R N).μx Ax)
    (hv_ball : VBallBound (v13RefMeasure R N).μv Av)
    (hz_ball : VBallBound (v13RefMeasure R N).μz Az) :
    SignedVReferenceIntegrable (v13RefMeasure R N) := by
  have hs := v13RefMeasure_supports_of_bounds R N
    (vXLow q) (vVLow q) rows.x_low rows.x_full
    rows.v_low rows.v_full rows.z_source
  exact signedVReferenceIntegrable_of_supports_and_ballBounds
    (v13RefMeasure R N) hAx hAv hAz
    hs.2.2.2.1 hs.2.2.2.2.1 hs.2.2.1
    hx_ball hv_ball hz_ball

theorem vBallBound_mono {μ₁ μ₂ : Measure ℂ} [IsFiniteMeasure μ₂] {A : ℝ}
    (hle : μ₁ ≤ μ₂) (hball : VBallBound μ₂ A) : VBallBound μ₁ A := by
  intro w t ht
  have hle_ball : μ₁ (Metric.ball w t) ≤ μ₂ (Metric.ball w t) := hle (Metric.ball w t)
  have hreal : μ₁.real (Metric.ball w t) ≤ μ₂.real (Metric.ball w t) :=
    ENNReal.toReal_mono (measure_ne_top μ₂ _) hle_ball
  exact hreal.trans (hball w t ht)

/-- `q`-generic constructor of `V13InteractionIntegrability (v13RefMeasure R N) (v13ZChain R) (v13ZPoisson R)`
    from the same decoded row bounds, normalization, and `VBallBound` certificates. -/
theorem v13InteractionIntegrability_of_ballBound
    {q : ℕ} {hq : SignedVBaseRange q}
    (R : V13DecodedRows q)
    (rows : V13DecodedRowBounds q R)
    (N : V13MeasureNormalization hq (v13RefRaw R))
    {Ax Av Az : ℝ}
    (hAx : 0 ≤ Ax) (hAv : 0 ≤ Av) (hAz : 0 ≤ Az)
    (hx_ball : VBallBound (v13RefMeasure R N).μx Ax)
    (hv_ball : VBallBound (v13RefMeasure R N).μv Av)
    (hz_ball : VBallBound (v13RefMeasure R N).μz Az) :
    V13InteractionIntegrability (v13RefMeasure R N)
      (v13ZChain R) (v13ZPoisson R) := by
  let M : V.SignedVMeasures := v13RefMeasure R N
  let zc : Measure ℂ := v13ZChain R
  let zp : Measure ℂ := v13ZPoisson R
  have hz_eq : M.μz = zc + zp := rfl
  have hzc_le : zc ≤ M.μz := by
    rw [hz_eq]
    exact Measure.le_add_right le_rfl
  have hzp_le : zp ≤ M.μz := by
    rw [hz_eq]
    exact Measure.le_add_left le_rfl
  letI : IsFiniteMeasure M.μx := ⟨M.finite_x.lt_top⟩
  letI : IsFiniteMeasure M.μv := ⟨M.finite_v.lt_top⟩
  letI : IsFiniteMeasure M.μz := ⟨M.finite_z.lt_top⟩
  letI : IsFiniteMeasure zc :=
    ⟨lt_of_le_of_lt (hzc_le Set.univ) M.finite_z.lt_top⟩
  letI : IsFiniteMeasure zp :=
    ⟨lt_of_le_of_lt (hzp_le Set.univ) M.finite_z.lt_top⟩
  have hs := v13RefMeasure_supports_of_bounds R N
    (vXLow q) (vVLow q) rows.x_low rows.x_full
    rows.v_low rows.v_full rows.z_source
  have hq0 : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
  have hx_ae := ae_norm_le_one_of_support_Icc hs.2.2.2.1
  have hv_ae := ae_norm_le_one_of_support_Icc hs.2.2.2.2.1
  have hz_ae := ae_norm_le_q_of_support_source hq.1 hs.2.2.1
  have hzc_ae : ∀ᵐ w ∂zc, ‖w‖ ≤ (q : ℝ) :=
    hz_ae.filter_mono (ae_mono hzc_le)
  have hzp_ae : ∀ᵐ w ∂zp, ‖w‖ ≤ (q : ℝ) :=
    hz_ae.filter_mono (ae_mono hzp_le)
  have hzc_ball : VBallBound zc Az := vBallBound_mono hzc_le hz_ball
  have hzp_ball : VBallBound zp Az := vBallBound_mono hzp_le hz_ball
  refine {
    sx := inferInstance
    sv := inferInstance
    szc := inferInstance
    szp := inferInstance
    xx := integrable_li2LogKernel_prod_of_vBallBound hAx zero_le_one zero_le_one
      hx_ae hx_ball hx_ae
    vv := integrable_li2LogKernel_prod_of_vBallBound hAv zero_le_one zero_le_one
      hv_ae hv_ball hv_ae
    zcc := integrable_li2LogKernel_prod_of_vBallBound hAz hq0 hq0
      hzc_ae hzc_ball hzc_ae
    zcp := integrable_li2LogKernel_prod_of_vBallBound hAz hq0 hq0
      hzc_ae hzp_ball hzp_ae
    zpp := integrable_li2LogKernel_prod_of_vBallBound hAz hq0 hq0
      hzp_ae hzp_ball hzp_ae
    vzc := integrable_li2LogKernel_prod_of_vBallBound hAz zero_le_one hq0
      hv_ae hzc_ball hzc_ae
    vzp := integrable_li2LogKernel_prod_of_vBallBound hAz zero_le_one hq0
      hv_ae hzp_ball hzp_ae }

end

end Li2Lean.B3
