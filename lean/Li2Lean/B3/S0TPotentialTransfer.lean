/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Li2Lean.B3.ReferencePackage
import Li2Lean.V.AllMSmoothing
import Li2Lean.B3.S0ModulusClosed
import Li2Lean.B3.S0ModulusLayerCake
import Li2Lean.B3.S0ModulusReciprocalTail
import Li2Lean.B3.S0ModulusNear

/-!
# S0-T logarithmic-potential transfer

This is the measure-theoretic integration half of the potential estimate in
`v-analytic.tex:561-601`.  The pointwise modulus estimate is deliberately an
explicit input: deriving it from `VBallBound` is the separate layer-cake
argument for the concrete v13 reference measures.  Once that estimate is
available, this theorem performs the finite-measure integral transfer and
retains the actual mass factor needed by the three weighted S0 terms.
-/

namespace Li2Lean.B3

noncomputable section

open MeasureTheory Set

theorem s0T_potential_transfer_bound
    {μ : Measure ℂ} [IsFiniteMeasure μ]
    {A M δ : ℝ}
    (hA : 0 ≤ A) (hM : 0 ≤ M)
    (hmass : μ.real Set.univ ≤ M)
    (hδ : 0 < δ) (hδsmall : δ ≤ (1 / 3 : ℝ))
    {x y : ℂ}
    (hx : Integrable (fun t : ℂ => Real.log ‖x - t‖) μ)
    (hy : Integrable (fun t : ℂ => Real.log ‖y - t‖) μ)
    (hpoint : ∀ᵐ t ∂μ,
      |Real.log ‖x - t‖ - Real.log ‖y - t‖| ≤
        potentialModulusCoefficient A M * δ *
          (1 + Real.log (1 / δ))) :
    |(∫ t : ℂ, Real.log ‖x - t‖ ∂μ) -
      ∫ t : ℂ, Real.log ‖y - t‖ ∂μ| ≤
        potentialModulusCoefficient A M * δ *
          (1 + Real.log (1 / δ)) * M := by
  have hlog : 0 ≤ Real.log (1 / δ) := by
    apply Real.log_nonneg
    apply (one_le_div hδ).2
    linarith
  have hcoeff : 0 ≤ potentialModulusCoefficient A M := by
    unfold potentialModulusCoefficient
    nlinarith
  have hC : 0 ≤ potentialModulusCoefficient A M * δ *
      (1 + Real.log (1 / δ)) := by
    have hsum : 0 ≤ 1 + Real.log (1 / δ) := by linarith
    positivity
  have hsub : Integrable
      (fun t : ℂ => Real.log ‖x - t‖ - Real.log ‖y - t‖) μ :=
    hx.sub hy
  rw [← integral_sub hx hy]
  calc
    |∫ t : ℂ, Real.log ‖x - t‖ - Real.log ‖y - t‖ ∂μ| ≤
        ∫ t : ℂ, |Real.log ‖x - t‖ - Real.log ‖y - t‖| ∂μ :=
      abs_integral_le_integral_abs
    _ ≤ ∫ _t : ℂ,
        potentialModulusCoefficient A M * δ *
          (1 + Real.log (1 / δ)) ∂μ := by
      apply integral_mono_ae hsub.abs (integrable_const _)
      exact hpoint
    _ = potentialModulusCoefficient A M * δ *
          (1 + Real.log (1 / δ)) * μ.real Set.univ := by
      rw [integral_const]
      simp [smul_eq_mul, mul_comm]
    _ ≤ potentialModulusCoefficient A M * δ *
          (1 + Real.log (1 / δ)) * M := by
      exact mul_le_mul_of_nonneg_left hmass hC

/-!
The scalar comparison in the layer-cake modulus calculation is the
elementary absorption used in v13 `v-analytic.tex:516-520`.  It keeps the
near-field `log (1 / (2 * δ))` term inside the coefficient `6 A + 2 M`.
-/
theorem s0_modulus_scalar_absorption
    {A M δ : ℝ}
    (hA : 0 ≤ A) (hM : 0 ≤ M)
    (hδ : 0 < δ) (hδsmall : δ ≤ (1 / 3 : ℝ)) :
    6 * A * δ * Real.log (1 / (2 * δ)) + 4 * A * δ + 2 * M * δ ≤
      (6 * A + 2 * M) * δ * (1 + Real.log (1 / δ)) := by
  have hδleone : δ ≤ 1 := by linarith
  have hlogδ : 0 ≤ Real.log (1 / δ) := by
    apply Real.log_nonneg
    exact (one_le_div hδ).2 hδleone
  have hlog2 : 0 ≤ Real.log (2 : ℝ) := by
    apply Real.log_nonneg
    norm_num
  have hsplit : Real.log (1 / (2 * δ)) =
      Real.log (1 / δ) - Real.log (2 : ℝ) := by
    rw [show (1 / (2 * δ) : ℝ) = (1 / 2 : ℝ) * (1 / δ) by
      field_simp]
    rw [Real.log_mul (by norm_num : (1 / 2 : ℝ) ≠ 0)
      (one_div_ne_zero hδ.ne')]
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv,
      one_div, Real.log_inv]
    ring
  rw [hsplit]
  have hδnonneg : 0 ≤ δ := le_of_lt hδ
  have hAδ : 0 ≤ A * δ := mul_nonneg hA hδnonneg
  have hMδ : 0 ≤ M * δ := mul_nonneg hM hδnonneg
  have hAδlog2 : 0 ≤ (A * δ) * Real.log 2 :=
    mul_nonneg hAδ hlog2
  have hMδlogδ : 0 ≤ (M * δ) * Real.log (1 / δ) :=
    mul_nonneg hMδ hlogδ
  nlinarith

theorem s0T_far_log_diff_pointwise_bound
    {δ : ℝ} (hδ : 0 < δ) {x y t : ℂ}
    (hxy : ‖x - y‖ ≤ δ) (ht : 2 * δ < ‖x - t‖) :
    |Real.log ‖x - t‖ - Real.log ‖y - t‖| ≤ 2 * δ / ‖x - t‖ := by
  have hx_pos : 0 < ‖x - t‖ := by linarith
  have htri1 : ‖x - t‖ ≤ ‖x - y‖ + ‖y - t‖ := by
    simpa [sub_add_sub_cancel] using norm_add_le (x - y) (y - t)
  have htri2 : ‖y - t‖ ≤ ‖x - y‖ + ‖x - t‖ := by
    have h := norm_add_le (y - x) (x - t)
    simpa [sub_add_sub_cancel, norm_sub_rev] using h
  have hy_half : ‖x - t‖ / 2 ≤ ‖y - t‖ := by linarith
  have hy_pos : 0 < ‖y - t‖ := by linarith
  rw [abs_sub_le_iff]
  constructor
  · calc
      Real.log ‖x - t‖ - Real.log ‖y - t‖
          = Real.log (‖x - t‖ / ‖y - t‖) :=
            (Real.log_div hx_pos.ne' hy_pos.ne').symm
      _ ≤ ‖x - t‖ / ‖y - t‖ - 1 :=
            Real.log_le_sub_one_of_pos (div_pos hx_pos hy_pos)
      _ = (‖x - t‖ - ‖y - t‖) / ‖y - t‖ := by
            field_simp [hy_pos.ne']
      _ ≤ δ / ‖y - t‖ :=
            div_le_div_of_nonneg_right (by linarith) hy_pos.le
      _ ≤ δ / (‖x - t‖ / 2) :=
            div_le_div_of_nonneg_left hδ.le (by linarith) hy_half
      _ = 2 * δ / ‖x - t‖ := by ring
  · calc
      Real.log ‖y - t‖ - Real.log ‖x - t‖
          = Real.log (‖y - t‖ / ‖x - t‖) :=
            (Real.log_div hy_pos.ne' hx_pos.ne').symm
      _ ≤ ‖y - t‖ / ‖x - t‖ - 1 :=
            Real.log_le_sub_one_of_pos (div_pos hy_pos hx_pos)
      _ = (‖y - t‖ - ‖x - t‖) / ‖x - t‖ := by
            field_simp [hx_pos.ne']
      _ ≤ δ / ‖x - t‖ :=
            div_le_div_of_nonneg_right (by linarith) hx_pos.le
      _ ≤ 2 * δ / ‖x - t‖ :=
            div_le_div_of_nonneg_right (by linarith) hx_pos.le

/-!
The reciprocal tail bound on the complement of the near closed ball.  The
indicator is bounded by `1 / (2 * δ)`, so it is integrable for every finite
measure; the existing layer-cake estimate then supplies the logarithmic tail.
-/
theorem s0T_far_reciprocal_tail_bound
    {μ : Measure ℂ} [IsFiniteMeasure μ]
    {A M δ : ℝ}
    (hA : 0 ≤ A) (hM : 0 ≤ M) (hmass : μ.real Set.univ ≤ M)
    (hball : VBallBound μ A)
    (hδ : 0 < δ) (hδsmall : δ ≤ (1 / 3 : ℝ))
    (x : ℂ) :
    (∫ t in (Metric.closedBall x (2 * δ))ᶜ, 2 * δ / ‖x - t‖ ∂μ) ≤
      2 * δ * (M + A * Real.log (1 / δ)) := by
  classical
  let r : ℂ → ℝ := fun z =>
    if 2 * δ < dist x z then 1 / dist x z else 0
  have hcond : MeasurableSet {z : ℂ | 2 * δ < dist x z} := by
    exact measurableSet_lt measurable_const
      (Measurable.dist measurable_const measurable_id)
  have hr_meas : Measurable r := by
    dsimp [r]
    apply Measurable.ite hcond
    · exact measurable_const.div (Measurable.dist measurable_const measurable_id)
    · exact measurable_const
  let L : ℝ := 1 / (2 * δ)
  have hL : 0 < L := by
    dsimp [L]
    positivity
  have hr_bdd : ∀ᵐ z ∂μ, ‖r z‖ ≤ L := by
    filter_upwards [] with z
    by_cases hz : 2 * δ < dist x z
    · have hdist : 0 < dist x z := lt_trans (by positivity) hz
      have hle : 1 / dist x z ≤ L := by
        dsimp [L]
        exact one_div_le_one_div_of_le (by positivity) (le_of_lt hz)
      simpa [r, hz, L, Real.norm_eq_abs,
        abs_of_pos (one_div_pos.mpr hdist)] using hle
    · simpa [r, hz, Real.norm_eq_abs] using hL.le
  have hr_int : Integrable r μ :=
    Integrable.of_bound hr_meas.aestronglyMeasurable L hr_bdd
  have htail := v13_reciprocal_tail_bound hA hM hmass hball hδ hδsmall hr_int (w := x)
  let N : Set ℂ := Metric.closedBall x (2 * δ)
  have hN : MeasurableSet N := Metric.isClosed_closedBall.measurableSet
  have hset_eq :
      (∫ t in Nᶜ, 2 * δ / ‖x - t‖ ∂μ) =
        ∫ t, (2 * δ) * r t ∂μ := by
    rw [← integral_indicator hN.compl]
    apply integral_congr_ae
    filter_upwards [] with t
    by_cases ht : t ∈ Nᶜ
    · have hdist : 2 * δ < dist x t := by
        have hnot : ¬ dist t x ≤ 2 * δ := by
          intro h
          exact ht (Metric.mem_closedBall.mpr h)
        simpa [dist_comm] using (lt_of_not_ge hnot)
      simp only [Set.indicator_of_mem ht]
      dsimp [r]
      rw [if_pos hdist, Complex.dist_eq]
      ring
    · have hdist : dist x t ≤ 2 * δ := by
        have hmem : t ∈ N := by simpa [N] using not_not.mp ht
        simpa [N, Metric.mem_closedBall, dist_comm] using hmem
      have hnotdist : ¬ 2 * δ < dist x t := not_lt_of_ge hdist
      simp only [Set.indicator]
      rw [if_neg ht]
      dsimp [r]
      rw [if_neg hnotdist]
      ring
  have hδ0 : 0 ≤ δ := hδ.le
  have hlog2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have hlogsplit : Real.log (1 / (2 * δ)) =
      Real.log (1 / δ) - Real.log (2 : ℝ) := by
    rw [show (1 / (2 * δ) : ℝ) = (1 / 2 : ℝ) * (1 / δ) by field_simp]
    rw [Real.log_mul (by norm_num : (1 / 2 : ℝ) ≠ 0)
      (one_div_ne_zero hδ.ne')]
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv,
      one_div, Real.log_inv]
    ring
  rw [hset_eq, integral_const_mul]
  calc
    2 * δ * (∫ x, r x ∂μ) ≤
        2 * δ * (M + A * Real.log (1 / (2 * δ))) := by
      exact mul_le_mul_of_nonneg_left htail (mul_nonneg (by positivity) hδ0)
    _ ≤ 2 * δ * (M + A * Real.log (1 / δ)) := by
      rw [hlogsplit]
      nlinarith [mul_nonneg hA hδ0]

/-!
The complete finite-measure modulus estimate.  The near ball is handled by
the layer-cake logarithmic estimate, while the complement uses the pointwise
log-difference bound and the reciprocal tail above.
-/
theorem s0T_potential_transfer_modulus
    {μ : Measure ℂ} [IsFiniteMeasure μ]
    {A M δ : ℝ}
    (hA : 0 ≤ A) (hM : 0 ≤ M)
    (hmass : μ.real Set.univ ≤ M)
    (hball : VBallBound μ A)
    (hδ : 0 < δ) (hδsmall : δ ≤ (1 / 3 : ℝ))
    {x y : ℂ} (hxy : ‖x - y‖ ≤ δ)
    (hx : Integrable (fun t : ℂ => Real.log ‖x - t‖) μ)
    (hy : Integrable (fun t : ℂ => Real.log ‖y - t‖) μ) :
    |(∫ t : ℂ, Real.log ‖x - t‖ ∂μ) -
      ∫ t : ℂ, Real.log ‖y - t‖ ∂μ| ≤
        potentialModulusCoefficient A M * δ *
          (1 + Real.log (1 / δ)) := by
  let N : Set ℂ := Metric.closedBall x (2 * δ)
  have hN : MeasurableSet N := by
    dsimp [N]
    exact Metric.isClosed_closedBall.measurableSet
  have hsub : Integrable
      (fun t : ℂ => Real.log ‖x - t‖ - Real.log ‖y - t‖) μ := hx.sub hy
  have hlog : 0 ≤ Real.log (1 / δ) := by
    apply Real.log_nonneg
    exact (one_le_div hδ).2 (by linarith [hδsmall])
  have hnear_x := s0T_near_ball_log_integral_bound hA hball hδ hδsmall
      (x := x) (c := x) (by simp [hδ.le]) hx
  have hnear_y := s0T_near_ball_log_integral_bound hA hball hδ hδsmall
      (x := x) (c := y) (by simpa [norm_sub_rev] using hxy) hy
  have hfx : IntegrableOn (fun t : ℂ => |Real.log ‖x - t‖|) N μ := by
    simpa [N] using hx.norm.integrableOn
  have hfy : IntegrableOn (fun t : ℂ => |Real.log ‖y - t‖|) N μ := by
    simpa [N] using hy.norm.integrableOn
  have hfsum : IntegrableOn
      (fun t : ℂ => (|Real.log ‖x - t‖|) + (|Real.log ‖y - t‖|)) N μ :=
    hfx.add hfy
  have hnear :
      (∫ t in N, |Real.log ‖x - t‖ - Real.log ‖y - t‖| ∂μ) ≤
        (∫ t in N, |Real.log ‖x - t‖| ∂μ) +
          ∫ t in N, |Real.log ‖y - t‖| ∂μ := by
    calc
      (∫ t in N, |Real.log ‖x - t‖ - Real.log ‖y - t‖| ∂μ) ≤
          ∫ t in N, (abs (Real.log ‖x - t‖) + abs (Real.log ‖y - t‖)) ∂μ := by
        apply setIntegral_mono_on hsub.norm.integrableOn hfsum hN
        intro t ht
        simpa [Real.norm_eq_abs] using
          (norm_sub_le (Real.log ‖x - t‖) (Real.log ‖y - t‖))
      _ = (∫ t in N, |Real.log ‖x - t‖| ∂μ) +
          ∫ t in N, |Real.log ‖y - t‖| ∂μ := by
        rw [integral_add hfx hfy]
  have hfar_log : IntegrableOn
      (fun t : ℂ => |Real.log ‖x - t‖ - Real.log ‖y - t‖|) Nᶜ μ := by
    exact hsub.norm.integrableOn
  have hfar_inv : IntegrableOn (fun t : ℂ => 2 * δ / ‖x - t‖) Nᶜ μ := by
    apply Measure.integrableOn_of_bounded
      (μ := μ) (s := Nᶜ) (f := fun t : ℂ => 2 * δ / ‖x - t‖)
      (by exact measure_ne_top μ Nᶜ)
    · exact (measurable_const.div
        (measurable_norm.comp (measurable_const.sub measurable_id))).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem hN.compl] with t ht
      have hdist : 2 * δ < ‖x - t‖ := by
        have hnot : ¬ dist t x ≤ 2 * δ := by
          intro h
          exact ht (Metric.mem_closedBall.mpr h)
        simpa [dist_comm, Complex.dist_eq] using (lt_of_not_ge hnot)
      have hden : 0 < ‖x - t‖ := lt_trans (by positivity) hdist
      have hinv : 1 / ‖x - t‖ ≤ 1 / (2 * δ) := by
        exact one_div_le_one_div_of_le (by positivity) (le_of_lt hdist)
      have hnonneg : 0 ≤ 2 * δ / ‖x - t‖ := by positivity
      have hbound : 2 * δ / ‖x - t‖ ≤ 1 := by
        rw [div_le_iff₀ hden]
        nlinarith [hinv]
      simpa [Real.norm_eq_abs, abs_of_pos hδ, abs_of_nonneg hnonneg] using hbound
  have hfar :
      (∫ t in Nᶜ, |Real.log ‖x - t‖ - Real.log ‖y - t‖| ∂μ) ≤
        ∫ t in Nᶜ, 2 * δ / ‖x - t‖ ∂μ := by
    apply setIntegral_mono_on hfar_log hfar_inv hN.compl
    intro t ht
    have hnot : ¬ dist t x ≤ 2 * δ := by
      intro h
      exact ht (Metric.mem_closedBall.mpr h)
    apply s0T_far_log_diff_pointwise_bound hδ hxy
    simpa [dist_comm, Complex.dist_eq] using (lt_of_not_ge hnot)
  have hsplit :
      (∫ t : ℂ, |Real.log ‖x - t‖ - Real.log ‖y - t‖| ∂μ) =
        (∫ t in N, |Real.log ‖x - t‖ - Real.log ‖y - t‖| ∂μ) +
          ∫ t in Nᶜ, |Real.log ‖x - t‖ - Real.log ‖y - t‖| ∂μ := by
    exact (integral_add_compl hN hsub.norm).symm
  have hsum_bound :
      2 * (A * δ * (1 + 2 * Real.log (1 / δ))) +
          2 * δ * (M + A * Real.log (1 / δ)) ≤
        potentialModulusCoefficient A M * δ *
          (1 + Real.log (1 / δ)) := by
    have hAδ : 0 ≤ A * δ := mul_nonneg hA hδ.le
    have hMδL : 0 ≤ M * δ * Real.log (1 / δ) :=
      mul_nonneg (mul_nonneg hM hδ.le) hlog
    unfold potentialModulusCoefficient
    nlinarith
  rw [← integral_sub hx hy]
  calc
    |∫ t : ℂ, Real.log ‖x - t‖ - Real.log ‖y - t‖ ∂μ| ≤
        ∫ t : ℂ, |Real.log ‖x - t‖ - Real.log ‖y - t‖| ∂μ :=
      abs_integral_le_integral_abs
    _ = (∫ t in N, |Real.log ‖x - t‖ - Real.log ‖y - t‖| ∂μ) +
          ∫ t in Nᶜ, |Real.log ‖x - t‖ - Real.log ‖y - t‖| ∂μ := hsplit
    _ ≤ (A * δ * (1 + 2 * Real.log (1 / δ)) +
          A * δ * (1 + 2 * Real.log (1 / δ))) +
          2 * δ * (M + A * Real.log (1 / δ)) := by
      linarith [hnear, hfar, hnear_x, hnear_y,
        (s0T_far_reciprocal_tail_bound hA hM hmass hball hδ hδsmall x)]
    _ ≤ potentialModulusCoefficient A M * δ *
          (1 + Real.log (1 / δ)) := by
      nlinarith [hsum_bound]

end

end Li2Lean.B3

#print axioms Li2Lean.B3.s0T_potential_transfer_bound
#print axioms Li2Lean.B3.s0T_potential_transfer_modulus
