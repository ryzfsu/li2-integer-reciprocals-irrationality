/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.Q11Reference
import Li2Lean.P0.ConfigContourPotentialActual
import Li2Lean.P0.ConfigContourExternalFourierFejer

open MeasureTheory
open Filter
open scoped BigOperators Interval

namespace Li2Lean.P0.Q11Data

noncomputable section

open Li2Lean.P0
open Li2Lean.P0.ConfigContourAnalytic
open Li2Lean.P0.ConfigContourReference
open Li2Lean.P0.ConfigContourSelfPotential
open Li2Lean.P0.ConfigContourKernel
open Li2Lean.P0.ConfigContourAbelPOC
open Li2Lean.P0.ConfigFejerMass
open Li2Lean.P0.ConfigFejerLog
open Li2Lean.P0.ConfigContourExternalPOC
open Li2Lean.P0.ConfigContourExternalFourier

private def q11ContourWeight64 (j : Fin 64) : ℝ :=
  q11ContourWeight (⟨j.val, by simpa [contourNodeCount] using j.isLt⟩)

def q11ContourFourierMoment (n : ℕ) : ℝ :=
  if n ≤ 48 then
    (1 - (n : ℝ) / 49) *
      ∑ j : Fin contourNodeCount,
        q11ContourWeight j * Real.cos ((n : ℝ) * contourAngle j)
  else 0

private theorem q11ContourFourierMoment_eq_sum64 (n : ℕ) :
    q11ContourFourierMoment n =
      if n ≤ 48 then
        (1 - (n : ℝ) / 49) *
          ∑ j : Fin 64,
            q11ContourWeight64 j * Real.cos ((n : ℝ) * contourAngle j)
      else 0 := by
  rfl

private theorem q11ContourFourierMoment_succ_eq (n : ℕ) :
    q11ContourFourierMoment (n + 1) =
      if n + 1 ≤ 48 then
        (1 - ((n : ℝ) + 1) / 49) *
          ∑ j : Fin 64,
            q11ContourWeight64 j *
              Real.cos (((n : ℝ) + 1) * contourAngle j)
      else 0 := by
  rw [q11ContourFourierMoment_eq_sum64]
  simp only [Nat.cast_add, Nat.cast_one]

private theorem q11ContourDensity_eq_sum64 (u : ℝ) :
    q11ContourDensity u =
      ∑ j : Fin 64,
        q11ContourWeight64 j * fejer48 (u - contourAngle j) := by
  rfl

private theorem q11ContourSineFourierMoment64_eq_zero (n : ℕ) :
    (∑ j : Fin 64,
      q11ContourWeight64 j * Real.sin ((n : ℝ) * contourAngle j)) = 0 := by
  let S : ℝ := ∑ j : Fin 64,
    q11ContourWeight64 j * Real.sin ((n : ℝ) * contourAngle j)
  have hrev : S = ∑ j : Fin 64,
      q11ContourWeight64 (reverseIndex j) *
        Real.sin ((n : ℝ) * contourAngle (reverseIndex j)) := by
    dsimp [S]
    rw [← Equiv.sum_comp reverseIndex
      (fun j => q11ContourWeight64 j *
        Real.sin ((n : ℝ) * contourAngle j))]
  have hneg : (∑ j : Fin 64,
      q11ContourWeight64 (reverseIndex j) *
        Real.sin ((n : ℝ) * contourAngle (reverseIndex j))) = -S := by
    dsimp [S]
    calc
      (∑ j : Fin 64,
          q11ContourWeight64 (reverseIndex j) *
            Real.sin ((n : ℝ) * contourAngle (reverseIndex j))) =
          ∑ j : Fin 64, -(q11ContourWeight64 j *
            Real.sin ((n : ℝ) * contourAngle j)) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hweight_reverse (j : Fin 64) :
            q11ContourWeight64 (reverseIndex j) = q11ContourWeight64 j := by
          exact q11ContourWeight_reverse j
        rw [hweight_reverse, contourAngle_reverse]
        have harg : (n : ℝ) * (2 * Real.pi - contourAngle j) =
            -(n : ℝ) * contourAngle j + (n : ℤ) * (2 * Real.pi) := by
          push_cast
          ring
        rw [harg, Real.sin_add_int_mul_two_pi]
        rw [show -(n : ℝ) * contourAngle j =
          -((n : ℝ) * contourAngle j) by ring, Real.sin_neg]
        ring
      _ = -S := by rw [Finset.sum_neg_distrib]
  have hself : S = -S := hrev.trans hneg
  dsimp [S] at hself
  have hzero : (2 : ℝ) *
      (∑ j : Fin 64, q11ContourWeight64 j *
        Real.sin ((n : ℝ) * contourAngle j)) = 0 := by
    linarith [hself]
  nlinarith

def q11ContourLogPolynomial (a : ℂ) : ℝ :=
  ∑ j : Fin contourNodeCount,
    q11ContourWeight j *
      (fejerLogPolynomial (a * phase (contourAngle j))).re

def q11ContourPotentialFourier (u : ℝ) : ℝ :=
  q11ContourMass * Real.log contourScale -
    ∑ n ∈ Finset.range 48,
      ((1 + contourRatio ^ (n + 1)) *
        q11ContourFourierMoment (n + 1) / (n + 1 : ℝ)) *
        Real.cos ((n + 1 : ℝ) * u)

theorem q11ContourDensity_continuous : Continuous q11ContourDensity := by
  unfold q11ContourDensity
  exact continuous_finsetSum _ fun j _ =>
    continuous_const.mul
      (ConfigContourMeasure.continuous_fejer48.comp
        (continuous_id.sub continuous_const))

private theorem q11_externalKernel_eq_correction (q u v : ℝ) :
    externalLogKernel q u v =
      Real.log ‖1 - (q : ℂ) / (phase u * phase v)‖ := by
  have hz : circleZeta (-(u + v)) = (phase u * phase v)⁻¹ := by
    rw [circleZeta_eq_phase]
    unfold phase
    rw [← Complex.exp_add, ← Complex.exp_neg]
    congr 1
    push_cast
    ring
  unfold externalLogKernel
  rw [hz]
  rfl

private theorem q11_diagonalKernel_eq_phase_difference (u v : ℝ) :
    diagonalLogKernel u v = Real.log ‖phase u - phase v‖ := by
  simp [diagonalLogKernel, circleZeta_eq_phase]

private theorem q11_diagonalKernel_symm (u v : ℝ) :
    diagonalLogKernel u v = diagonalLogKernel v u := by
  rw [q11_diagonalKernel_eq_phase_difference,
    q11_diagonalKernel_eq_phase_difference]
  rw [norm_sub_rev]

private theorem q11_externalLogKernel_symm (q u v : ℝ) :
    externalLogKernel q u v = externalLogKernel q v u := by
  simp [externalLogKernel, add_comm]

private theorem q11_phase_collision_countable (u : ℝ) :
    ({v : ℝ | phase v = phase u}).Countable := by
  have hsub : {v : ℝ | phase v = phase u} ⊆
      (fun n : ℤ => u + (n : ℝ) * (2 * Real.pi)) '' (Set.univ : Set ℤ) := by
    intro v hv
    have hZ : circleZeta v = circleZeta u := by
      rw [circleZeta_eq_phase, circleZeta_eq_phase]
      exact hv
    have hexp : Complex.exp (Complex.I * (v : ℂ)) =
        Complex.exp (Complex.I * (u : ℂ)) := hZ
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp
    have him := congrArg Complex.im hn
    have hv' : v = u + (n : ℝ) * (2 * Real.pi) := by
      simpa [Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im] using him
    exact ⟨n, by simp, hv'.symm⟩
  have himage :
      ((fun n : ℤ => u + (n : ℝ) * (2 * Real.pi)) ''
        (Set.univ : Set ℤ)).Countable := by
    simpa only [Set.image_univ] using
      Set.countable_range (fun n : ℤ => u + (n : ℝ) * (2 * Real.pi))
  exact himage.mono hsub

private theorem q11_phase_ne_ae (u : ℝ) :
    ∀ᵐ v ∂volume, phase v ≠ phase u := by
  have hc := q11_phase_collision_countable u
  simpa only [ae_iff, Classical.not_not] using hc.measure_zero volume

private theorem q11_externalLogKernel_continuous (q u : ℝ)
    (hq : ‖(q : ℂ)‖ < 1) :
    Continuous (fun v : ℝ => externalLogKernel q u v) := by
  have hcont := ConfigFejerLog.continuous_log_norm (a := (q : ℂ)) hq
  have hEq : (fun v : ℝ => externalLogKernel q u v) =
      fun v => Real.log ‖1 - (q : ℂ) * phase (-(u + v))‖ := by
    funext v
    simp [externalLogKernel, circleZeta_eq_phase]
  rw [hEq]
  exact hcont.comp (continuous_neg.comp (continuous_const.add continuous_id))

def q11ExternalFourierCoefficient (n : ℕ) (v : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..(2 * Real.pi),
    q11ContourDensity u * Real.cos ((n + 1 : ℝ) * (u + v))

theorem q11ExternalFourierCoefficient_eq_actual_moment_succ
    (n : ℕ) (v : ℝ) :
    q11ExternalFourierCoefficient n v =
        2 * Real.pi * q11ContourFourierMoment (n + 1) *
        Real.cos ((n + 1 : ℝ) * v) := by
  unfold q11ExternalFourierCoefficient
  simp_rw [q11ContourDensity_eq_sum64]
  simp_rw [Finset.sum_mul]
  rw [intervalIntegral.integral_finsetSum]
  · rw [q11ContourFourierMoment_succ_eq]
    by_cases hn : n + 1 ≤ 48
    · simp only [if_pos hn]
      calc
        (∑ j : Fin 64, ∫ u in (0 : ℝ)..(2 * Real.pi),
            q11ContourWeight64 j * fejer48 (u - contourAngle j) *
              Real.cos ((n + 1 : ℝ) * (u + v))) =
          ∑ j : Fin 64,
            q11ContourWeight64 j *
              (2 * Real.pi * (1 - (n + 1 : ℝ) / 49) *
                Real.cos ((n + 1 : ℝ) * (contourAngle j + v))) := by
            apply Finset.sum_congr rfl
            intro j hj
            have hfun :
                (fun u : ℝ =>
                  q11ContourWeight64 j * fejer48 (u - contourAngle j) *
                    Real.cos ((n + 1 : ℝ) * (u + v))) =
                (fun u : ℝ =>
                  q11ContourWeight64 j *
                    (fejer48 (u - contourAngle j) *
                      Real.cos ((n + 1 : ℝ) * (u + v)))) := by
              funext u
              ring
            rw [hfun, intervalIntegral.integral_const_mul]
            have hfejer :
                (∫ x in (0 : ℝ)..(2 * Real.pi),
                  fejer48 (x - contourAngle j) *
                    Real.cos (((n : ℝ) + 1) * (x + v))) =
                  (2 * Real.pi *
                    (if n + 1 ≤ 48 then 1 - ((n : ℝ) + 1) / 49 else 0)) *
                    Real.cos (((n : ℝ) + 1) * (contourAngle j + v)) := by
              simpa only [Nat.cast_add, Nat.cast_one] using
                (ConfigContourExternalFourier.fejer48_shifted_cosine
                  (n + 1) (contourAngle j) v)
            rw [hfejer]
            simp only [if_pos hn]
        _ = (2 * Real.pi * (1 - (n + 1 : ℝ) / 49) *
              Real.cos ((n + 1 : ℝ) * v)) *
            (∑ j : Fin 64,
              q11ContourWeight64 j *
                Real.cos ((n + 1 : ℝ) * contourAngle j)) := by
            have hsum :
                ∑ j : Fin 64,
                  q11ContourWeight64 j *
                    (2 * Real.pi * (1 - (n + 1 : ℝ) / 49) *
                      Real.cos ((n + 1 : ℝ) * (contourAngle j + v))) =
                ∑ j : Fin 64,
                  ((2 * Real.pi * (1 - (n + 1 : ℝ) / 49) *
                    Real.cos ((n + 1 : ℝ) * v)) *
                    (q11ContourWeight64 j *
                      Real.cos ((n + 1 : ℝ) * contourAngle j)) -
                   (2 * Real.pi * (1 - (n + 1 : ℝ) / 49) *
                    Real.sin ((n + 1 : ℝ) * v)) *
                    (q11ContourWeight64 j *
                      Real.sin ((n + 1 : ℝ) * contourAngle j))) := by
              apply Finset.sum_congr rfl
              intro j hj
              have harg :
                  (n + 1 : ℝ) * (contourAngle j + v) =
                    (n + 1 : ℝ) * contourAngle j +
                      (n + 1 : ℝ) * v := by ring
              rw [harg, Real.cos_add]
              ring
            rw [hsum, Finset.sum_sub_distrib,
              ← Finset.mul_sum, ← Finset.mul_sum]
            have hsine := q11ContourSineFourierMoment64_eq_zero (n + 1)
            have hsine' :
                (∑ j : Fin 64, q11ContourWeight64 j *
                  Real.sin ((n + 1 : ℝ) * contourAngle j)) = 0 := by
              simpa only [Nat.cast_add, Nat.cast_one] using hsine
            rw [hsine']
            ring
        _ = 2 * Real.pi *
              ((1 - (n + 1 : ℝ) / 49) *
                (∑ j : Fin 64,
                  q11ContourWeight64 j *
                    Real.cos ((n + 1 : ℝ) * contourAngle j))) *
            Real.cos ((n + 1 : ℝ) * v) := by
              ring
    · simp only [if_neg hn]
      have hzero_rhs :
          2 * Real.pi * 0 * Real.cos ((n + 1 : ℝ) * v) = 0 := by ring
      rw [hzero_rhs]
      apply Finset.sum_eq_zero
      intro j hj
      have hfun :
          (fun u : ℝ =>
            q11ContourWeight64 j * fejer48 (u - contourAngle j) *
              Real.cos ((n + 1 : ℝ) * (u + v))) =
          (fun u : ℝ =>
            q11ContourWeight64 j *
              (fejer48 (u - contourAngle j) *
                Real.cos ((n + 1 : ℝ) * (u + v)))) := by
        funext u
        ring
      rw [hfun, intervalIntegral.integral_const_mul]
      have hfejer :
          (∫ x in (0 : ℝ)..(2 * Real.pi),
            fejer48 (x - contourAngle j) *
              Real.cos (((n : ℝ) + 1) * (x + v))) =
            (2 * Real.pi *
              (if n + 1 ≤ 48 then 1 - ((n : ℝ) + 1) / 49 else 0)) *
              Real.cos (((n : ℝ) + 1) * (contourAngle j + v)) := by
        simpa only [Nat.cast_add, Nat.cast_one] using
          (ConfigContourExternalFourier.fejer48_shifted_cosine
            (n + 1) (contourAngle j) v)
      rw [hfejer]
      simp only [if_neg hn, mul_zero, zero_mul]
  · intro j hj
    exact ((continuous_const.mul
      (ConfigContourMeasure.continuous_fejer48.comp
        (continuous_id.sub continuous_const))).mul
        (by fun_prop)).intervalIntegrable _ _

private theorem q11_abs_q_lt_one {q : ℝ} (hq : ‖(q : ℂ)‖ < 1) :
    |q| < 1 := by
  simpa [Complex.norm_real, Real.norm_eq_abs] using hq

private theorem q11_geom_succ_summable {q : ℝ} (hq : |q| < 1) :
    Summable (fun n : ℕ => |q| ^ (n + 1)) := by
  have h := summable_geometric_of_lt_one (abs_nonneg q) hq
  have h' := h.mul_left |q|
  simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using h'

private theorem q11_externalTerm_norm_bound (q : ℝ) (n : ℕ) (v u : ℝ) :
    ‖externalTerm q n v u‖ ≤ |q| ^ (n + 1) := by
  have hden : 1 ≤ ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n))
  have hden0 : 0 < ((n + 1 : ℕ) : ℝ) := lt_of_lt_of_le zero_lt_one hden
  have hcos : |Real.cos ((n + 1) * (u + v))| ≤ 1 :=
    Real.abs_cos_le_one _
  rw [externalTerm, Real.norm_eq_abs, abs_neg, abs_div, abs_mul, abs_pow]
  rw [show |(↑n + 1 : ℝ)| = (↑n + 1 : ℝ) from
    abs_of_nonneg (by positivity)]
  have hqnon : 0 ≤ |q| ^ (n + 1) := pow_nonneg (abs_nonneg q) _
  have hmul : |q| ^ (n + 1) * |Real.cos ((n + 1) * (u + v))| ≤
      |q| ^ (n + 1) * ((n + 1 : ℕ) : ℝ) := by
    calc
      |q| ^ (n + 1) * |Real.cos ((n + 1) * (u + v))| ≤
          |q| ^ (n + 1) * 1 := mul_le_mul_of_nonneg_left hcos hqnon
      _ ≤ |q| ^ (n + 1) * ((n + 1 : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hden hqnon
  simpa only [Nat.cast_add, Nat.cast_one] using
    (div_le_iff₀ hden0).2 hmul

private def q11ExternalTermBound (q : ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  |q| ^ (n + 1) * |q11ContourDensity u|

theorem q11ExternalLogKernel_integral_tsum (q v : ℝ)
    (hq : ‖(q : ℂ)‖ < 1) :
    (∫ u in (0 : ℝ)..(2 * Real.pi),
      q11ContourDensity u * externalLogKernel q u v) =
      ∑' n : ℕ, ∫ u in (0 : ℝ)..(2 * Real.pi),
        q11ContourDensity u * externalTerm q n v u := by
  let r : ℝ := |q|
  have hr : r < 1 := by exact q11_abs_q_lt_one hq
  have hgeom : Summable (fun n : ℕ => r ^ (n + 1)) := by
    simpa [r] using q11_geom_succ_summable hr
  let F : ℕ → ℝ → ℝ := fun n u => q11ContourDensity u * externalTerm q n v u
  let B : ℕ → ℝ → ℝ := fun n u => q11ExternalTermBound q n u
  have hterm (u : ℝ) : HasSum (fun n => externalTerm q n v u)
      (externalLogKernel q u v) := by
    have hsum : Summable (fun n : ℕ =>
        q ^ (n + 1) * Real.cos ((n + 1) * (u + v)) / (n + 1)) := by
      refine hgeom.of_norm_bounded ?_
      intro n
      have hbound := q11_externalTerm_norm_bound q n v u
      simpa [externalTerm, r, Real.norm_eq_abs, abs_neg] using hbound
    rw [externalLogKernel_eq_tsum q u v hq]
    simpa [externalTerm] using hsum.hasSum.neg
  have hlim : ∀ᵐ u ∂volume, u ∈ Set.uIoc (0 : ℝ) (2 * Real.pi) →
      HasSum (fun n => F n u) (q11ContourDensity u * externalLogKernel q u v) := by
    filter_upwards [] with u hu
    exact (hterm u).mul_left (q11ContourDensity u)
  have hmeas (n : ℕ) : AEStronglyMeasurable (F n)
      (volume.restrict (Set.uIoc (0 : ℝ) (2 * Real.pi))) := by
    apply (q11ContourDensity_continuous.mul ?_).aestronglyMeasurable
    unfold externalTerm
    fun_prop
  have hbound (n : ℕ) : ∀ᵐ u ∂volume, u ∈ Set.uIoc (0 : ℝ) (2 * Real.pi) →
      ‖F n u‖ ≤ B n u := by
    filter_upwards [] with u hu
    dsimp [F, B, q11ExternalTermBound]
    rw [abs_mul]
    have hterm := q11_externalTerm_norm_bound q n v u
    have hterm' : |externalTerm q n v u| ≤ |q| ^ (n + 1) := by
      simpa [Real.norm_eq_abs] using hterm
    calc
      |q11ContourDensity u| * |externalTerm q n v u| ≤
          |q11ContourDensity u| * |q| ^ (n + 1) :=
            mul_le_mul_of_nonneg_left hterm' (abs_nonneg _)
      _ = |q| ^ (n + 1) * |q11ContourDensity u| := mul_comm _ _
  have hboundSummable : ∀ᵐ u ∂volume,
      u ∈ Set.uIoc (0 : ℝ) (2 * Real.pi) → Summable (fun n => B n u) := by
    filter_upwards [] with u hu
    dsimp [B, q11ExternalTermBound]
    exact hgeom.mul_right _
  have hboundInt : IntervalIntegrable (fun u => ∑' n : ℕ, B n u)
      volume 0 (2 * Real.pi) := by
    have heq (u : ℝ) : (∑' n : ℕ, B n u) =
        (∑' n : ℕ, r ^ (n + 1)) * |q11ContourDensity u| := by
      dsimp [B, q11ExternalTermBound]
      rw [Summable.tsum_mul_right _ hgeom]
    have hcont : Continuous (fun u : ℝ =>
        (∑' n : ℕ, r ^ (n + 1)) * |q11ContourDensity u|) :=
      continuous_const.mul (continuous_abs.comp q11ContourDensity_continuous)
    exact (hcont.congr fun u => (heq u).symm).intervalIntegrable _ _
  have hseries := intervalIntegral.hasSum_integral_of_dominated_convergence
    (a := (0 : ℝ)) (b := 2 * Real.pi) (μ := volume) (F := F)
    (bound := B) hmeas hbound hboundSummable hboundInt hlim
  simpa only [F] using hseries.tsum_eq.symm

theorem q11ExternalLogKernel_integral_eq_finite_moment (q v : ℝ)
    (hq : ‖(q : ℂ)‖ < 1) :
    (∫ u in (0 : ℝ)..(2 * Real.pi),
      q11ContourDensity u * externalLogKernel q u v) =
      ∑ n ∈ Finset.range 48,
        (-(q ^ (n + 1) / (n + 1 : ℝ))) *
          (2 * Real.pi * q11ContourFourierMoment (n + 1) *
            Real.cos ((n + 1 : ℝ) * v)) := by
  rw [q11ExternalLogKernel_integral_tsum q v hq]
  have hterm (n : ℕ) :
      (∫ u in (0 : ℝ)..(2 * Real.pi),
        q11ContourDensity u * externalTerm q n v u) =
      (-(q ^ (n + 1) / (n + 1 : ℝ))) *
        q11ExternalFourierCoefficient n v := by
    have hfun :
        (fun u : ℝ => q11ContourDensity u * externalTerm q n v u) =
        (fun u : ℝ =>
          (-(q ^ (n + 1) / (n + 1 : ℝ))) *
            (q11ContourDensity u * Real.cos ((n + 1 : ℝ) * (u + v)))) := by
      funext u
      dsimp [externalTerm]
      ring
    rw [hfun, intervalIntegral.integral_const_mul]
    rfl
  simp_rw [hterm]
  have hzero : ∀ n ∉ Finset.range 48,
      (-(q ^ (n + 1) / (n + 1 : ℝ))) *
        q11ExternalFourierCoefficient n v = 0 := by
    intro n hn
    have hnlarge : 48 ≤ n := Nat.le_of_not_gt (by simpa using hn)
    have hmoment := q11ExternalFourierCoefficient_eq_actual_moment_succ n v
    rw [hmoment]
    have hcoeff : q11ContourFourierMoment (n + 1) = 0 := by
      unfold q11ContourFourierMoment
      simp [Nat.not_le_of_gt (by omega : 48 < n + 1)]
    rw [hcoeff]
    ring
  rw [tsum_eq_sum hzero]
  apply Finset.sum_congr rfl
  intro n hn
  have h := q11ExternalFourierCoefficient_eq_actual_moment_succ n v
  simpa using congrArg
    (fun x : ℝ => (-(q ^ (n + 1) / (n + 1 : ℝ))) * x) h

theorem q11ContourSineFourierMoment_eq_zero (n : ℕ) :
    (∑ j : Fin contourNodeCount,
      q11ContourWeight j * Real.sin ((n : ℝ) * contourAngle j)) = 0 := by
  change (∑ j : Fin 64,
      q11ContourWeight j * Real.sin ((n : ℝ) * contourAngle j)) = 0
  let S : ℝ := ∑ j : Fin 64,
    q11ContourWeight j * Real.sin ((n : ℝ) * contourAngle j)
  have hrev : S = ∑ j : Fin 64,
      q11ContourWeight (reverseIndex j) *
        Real.sin ((n : ℝ) * contourAngle (reverseIndex j)) := by
    dsimp [S]
    rw [← Equiv.sum_comp reverseIndex
      (fun j => q11ContourWeight j *
        Real.sin ((n : ℝ) * contourAngle j))]
  have hneg : (∑ j : Fin 64,
      q11ContourWeight (reverseIndex j) *
        Real.sin ((n : ℝ) * contourAngle (reverseIndex j))) = -S := by
    dsimp [S]
    calc
      (∑ j : Fin 64,
          q11ContourWeight (reverseIndex j) *
            Real.sin ((n : ℝ) * contourAngle (reverseIndex j))) =
          ∑ j : Fin 64, -(q11ContourWeight j *
            Real.sin ((n : ℝ) * contourAngle j)) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hweight_reverse (j : Fin 64) :
            q11ContourWeight (reverseIndex j) = q11ContourWeight j := by
          exact q11ContourWeight_reverse j
        rw [hweight_reverse]
        have hangle_reverse (j : Fin 64) :
            contourAngle (reverseIndex j) = 2 * Real.pi - contourAngle j :=
          contourAngle_reverse j
        rw [hangle_reverse]
        have harg : (n : ℝ) * (2 * Real.pi - contourAngle j) =
            -(n : ℝ) * contourAngle j + (n : ℤ) * (2 * Real.pi) := by
          push_cast
          ring
        rw [harg, Real.sin_add_int_mul_two_pi]
        rw [show -(n : ℝ) * contourAngle j =
          -((n : ℝ) * contourAngle j) by ring, Real.sin_neg]
        ring
      _ = -S := by rw [Finset.sum_neg_distrib]
  have hself : S = -S := hrev.trans hneg
  dsimp [S] at hself
  have hzero : (2 : ℝ) *
      (∑ j : Fin 64, q11ContourWeight j *
        Real.sin ((n : ℝ) * contourAngle j)) = 0 := by
    linarith [hself]
  nlinarith

theorem q11ContourLogPolynomial_phase_neg (u : ℝ) :
    q11ContourLogPolynomial (phase (-u)) =
      ∑ n ∈ Finset.range 49,
        q11ContourFourierMoment n * ((1 : ℝ) / (n : ℝ)) *
          Real.cos ((n : ℝ) * u) := by
  have harg (j : Fin contourNodeCount) :
      phase (-u) * phase (contourAngle j) =
        (1 : ℂ) * phase (contourAngle j - u) := by
    unfold phase
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  unfold q11ContourLogPolynomial
  have hterm (j : Fin contourNodeCount) :
      (fejerLogPolynomial (phase (-u) * phase (contourAngle j))).re =
        ∑ n ∈ Finset.range 49,
          (1 - (n : ℝ) / 49) * ((1 : ℝ) ^ n / (n : ℝ)) *
            Real.cos ((n : ℝ) * (contourAngle j - u)) := by
    rw [harg]
    simpa [Complex.ofReal_one] using
      (fejerLogPolynomial_ofReal_re (1 : ℝ) (contourAngle j - u))
  simp_rw [hterm]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [Finset.mem_range] at hn
  have hangle (j : Fin contourNodeCount) :
      (n : ℝ) * (contourAngle j - u) =
        (n : ℝ) * contourAngle j - (n : ℝ) * u := by ring
  simp_rw [hangle, Real.cos_sub]
  by_cases hn48 : n ≤ 48
  · have hsin0 := q11ContourSineFourierMoment_eq_zero n
    have hcos :
        (∑ j : Fin contourNodeCount, q11ContourWeight j *
          ((1 - (n : ℝ) / 49) * ((1 : ℝ) ^ n / (n : ℝ)) *
            (Real.cos ((n : ℝ) * contourAngle j) *
              Real.cos ((n : ℝ) * u)))) =
          ((1 - (n : ℝ) / 49) * ((1 : ℝ) ^ n / (n : ℝ))) *
            Real.cos ((n : ℝ) * u) *
              (∑ j : Fin contourNodeCount, q11ContourWeight j *
                Real.cos ((n : ℝ) * contourAngle j)) := by
      calc
        _ = ∑ j : Fin contourNodeCount,
            ((((1 - (n : ℝ) / 49) * ((1 : ℝ) ^ n / (n : ℝ))) *
              Real.cos ((n : ℝ) * u)) *
              (q11ContourWeight j *
                Real.cos ((n : ℝ) * contourAngle j))) := by
          apply Finset.sum_congr rfl
          intro j hj
          ring
        _ = _ := by rw [Finset.mul_sum]
    have hsine :
        (∑ j : Fin contourNodeCount, q11ContourWeight j *
          ((1 - (n : ℝ) / 49) * ((1 : ℝ) ^ n / (n : ℝ)) *
            (Real.sin ((n : ℝ) * contourAngle j) *
              Real.sin ((n : ℝ) * u)))) = 0 := by
      calc
        _ = ((1 - (n : ℝ) / 49) * ((1 : ℝ) ^ n / (n : ℝ))) *
              Real.sin ((n : ℝ) * u) *
              (∑ j : Fin contourNodeCount, q11ContourWeight j *
                Real.sin ((n : ℝ) * contourAngle j)) := by
          calc
            _ = ∑ j : Fin contourNodeCount,
                (((1 - (n : ℝ) / 49) * ((1 : ℝ) ^ n / (n : ℝ))) *
                  Real.sin ((n : ℝ) * u)) *
                  (q11ContourWeight j *
                    Real.sin ((n : ℝ) * contourAngle j)) := by
              apply Finset.sum_congr rfl
              intro j hj
              ring
            _ = _ := by rw [Finset.mul_sum]
        _ = 0 := by rw [hsin0]; ring
    calc
      _ = (∑ j : Fin contourNodeCount, q11ContourWeight j *
            ((1 - (n : ℝ) / 49) * ((1 : ℝ) ^ n / (n : ℝ)) *
              (Real.cos ((n : ℝ) * contourAngle j) *
                Real.cos ((n : ℝ) * u)))) +
          ∑ j : Fin contourNodeCount, q11ContourWeight j *
            ((1 - (n : ℝ) / 49) * ((1 : ℝ) ^ n / (n : ℝ)) *
              (Real.sin ((n : ℝ) * contourAngle j) *
                Real.sin ((n : ℝ) * u))) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = ((1 - (n : ℝ) / 49) * ((1 : ℝ) ^ n / (n : ℝ))) *
            Real.cos ((n : ℝ) * u) *
              (∑ j : Fin contourNodeCount, q11ContourWeight j *
                Real.cos ((n : ℝ) * contourAngle j)) := by
        rw [hcos, hsine]
        ring
      _ = q11ContourFourierMoment n * ((1 : ℝ) / (n : ℝ)) *
            Real.cos ((n : ℝ) * u) := by
        unfold q11ContourFourierMoment
        simp only [if_pos hn48, one_pow]
        ring
  · omega

private theorem q11ContourLogPolynomial_phase_neg_succ_sum (u : ℝ) :
    q11ContourLogPolynomial (phase (-u)) =
      ∑ n ∈ Finset.range 48,
        q11ContourFourierMoment (n + 1) * (1 / (n + 1 : ℝ)) *
          Real.cos ((n + 1 : ℝ) * u) := by
  rw [q11ContourLogPolynomial_phase_neg]
  let f : ℕ → ℝ := fun n =>
    q11ContourFourierMoment n * (1 / (n : ℝ)) *
      Real.cos ((n : ℝ) * u)
  have h := Finset.sum_range_succ' f 48
  have hzero : f 0 = 0 := by simp [f]
  rw [hzero, add_zero] at h
  convert h using 1 <;> simp [f, Nat.cast_add]

theorem q11ContourLogNorm_fejer (a : ℂ) (ha : ‖a‖ < 1) :
    (∫ u in (0 : ℝ)..(2 * Real.pi),
      q11ContourDensity u * Real.log ‖1 - a * phase u‖) =
      -(2 * Real.pi) * q11ContourLogPolynomial a := by
  unfold q11ContourDensity
  simp_rw [Finset.sum_mul]
  rw [intervalIntegral.integral_finsetSum]
  · simp_rw [mul_assoc, intervalIntegral.integral_const_mul,
      ConfigFejerLog.integral_fejer48_log_norm ha]
    unfold q11ContourLogPolynomial
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  · intro j hj
    exact ((continuous_const.mul
      (ConfigContourMeasure.continuous_fejer48.comp
        (continuous_id.sub continuous_const))).mul
        (ConfigFejerLog.continuous_log_norm ha)).intervalIntegrable _ _

theorem q11ContourDensity_diagonalAbel_integral {r : ℝ}
    (hr : ‖(r : ℂ)‖ < 1) (v : ℝ) :
    (∫ u in (0 : ℝ)..(2 * Real.pi),
      q11ContourDensity u * diagonalAbelKernel r u v) =
      -(2 * Real.pi) *
        q11ContourLogPolynomial ((r : ℂ) * phase (-v)) := by
  have hparam : ‖((r : ℂ) * phase (-v))‖ < 1 := by
    simpa only [norm_mul, norm_phase, mul_one] using hr
  have hkernel (u : ℝ) : diagonalAbelKernel r u v =
      Real.log ‖1 - ((r : ℂ) * phase (-v)) * phase u‖ := by
    unfold diagonalAbelKernel
    rw [circleZeta_eq_phase, phase_neg_conj]
    have hconj :
        (1 : ℂ) - (r : ℂ) * (starRingEnd ℂ) (phase (u - v)) =
          (starRingEnd ℂ) ((1 : ℂ) - (r : ℂ) * phase (u - v)) := by
      simp
    rw [hconj, Complex.norm_conj, phase_sub]
    congr 3
    ring
  have hfun :
      (fun u : ℝ => q11ContourDensity u * diagonalAbelKernel r u v) =
        (fun u : ℝ => q11ContourDensity u *
          Real.log ‖1 - ((r : ℂ) * phase (-v)) * phase u‖) := by
    funext u
    rw [hkernel]
  rw [hfun]
  exact q11ContourLogNorm_fejer _ hparam

theorem q11ContourDensity_diagonalLog_integral (v : ℝ) :
    (∫ u in (0 : ℝ)..(2 * Real.pi),
      q11ContourDensity u * diagonalLogKernel u v) =
      -(2 * Real.pi) * q11ContourLogPolynomial (phase (-v)) := by
  have hlim := diagonalAbel_weighted_limit q11ContourDensity
    q11ContourDensity_continuous v
  have heq : (fun r : ℝ =>
      ∫ u in (0 : ℝ)..(2 * Real.pi),
        diagonalAbelKernel r u v * q11ContourDensity u) =ᶠ[
          nhdsWithin (1 : ℝ) (Set.Iio 1)] (fun r : ℝ =>
      -(2 * Real.pi) *
        q11ContourLogPolynomial ((r : ℂ) * phase (-v))) := by
    filter_upwards [show ∀ᶠ r : ℝ in nhdsWithin (1 : ℝ) (Set.Iio 1),
        0 ≤ r ∧ r < 1 by
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds
          (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))] with r hr hpos
      exact ⟨le_of_lt hpos, hr⟩] with r ⟨hr0, hr1⟩
    have hrnorm : ‖(r : ℂ)‖ < 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
      exact hr1
    simpa [mul_comm] using q11ContourDensity_diagonalAbel_integral hrnorm v
  have hlim' := hlim.congr' heq
  have hp : Continuous (fun r : ℝ =>
      q11ContourLogPolynomial ((r : ℂ) * phase (-v))) := by
    unfold q11ContourLogPolynomial fejerLogPolynomial
    fun_prop
  have hpt : Tendsto (fun r : ℝ =>
      -(2 * Real.pi) * q11ContourLogPolynomial ((r : ℂ) * phase (-v)))
      (nhdsWithin (1 : ℝ) (Set.Iio 1))
      (nhds (-(2 * Real.pi) * q11ContourLogPolynomial (phase (-v)))) := by
    have ht : Tendsto (fun r : ℝ =>
        q11ContourLogPolynomial ((r : ℂ) * phase (-v)))
        (nhdsWithin (1 : ℝ) (Set.Iio 1))
        (nhds (q11ContourLogPolynomial (phase (-v)))) := by
      convert (hp.continuousAt : ContinuousAt
        (fun r : ℝ => q11ContourLogPolynomial ((r : ℂ) * phase (-v))) 1).tendsto.mono_left
          (nhdsWithin_le_nhds :
            nhdsWithin (1 : ℝ) (Set.Iio 1) ≤ nhds (1 : ℝ)) using 1 <;> simp
    simpa using (tendsto_const_nhds.mul ht)
  have huniq := tendsto_nhds_unique hlim' hpt
  simpa [mul_comm, q11_diagonalKernel_eq_phase_difference] using huniq

private theorem q11ContourPotential_joukowski_split (u : ℝ) :
    q11ContourPotential (Li2Lean.p0EllipsePoint 1 u) =
      q11ContourMass * Real.log contourScale +
        (2 * Real.pi)⁻¹ *
          ((∫ v in (0 : ℝ)..(2 * Real.pi),
              q11ContourDensity v * diagonalLogKernel u v) +
            (∫ v in (0 : ℝ)..(2 * Real.pi),
              q11ContourDensity v * externalLogKernel contourRatio u v)) := by
  have hq : ‖(contourRatio : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg contourRatio_nonneg]
    exact contourRatio_lt_one
  have hdiag : IntervalIntegrable
      (fun v : ℝ => q11ContourDensity v * diagonalLogKernel u v)
      volume (0 : ℝ) (2 * Real.pi) := by
    have hlog := DiagonalLogClassicalProbe.diagonalLogKernel_intervalIntegrable u
    have hmul := hlog.mul_continuousOn
      q11ContourDensity_continuous.continuousOn
    have hfun : (fun v : ℝ =>
        q11ContourDensity v * diagonalLogKernel u v) =
        fun v => diagonalLogKernel v u * q11ContourDensity v := by
      funext v
      rw [q11_diagonalKernel_symm]
      ring
    rw [hfun]
    exact hmul
  have hext : IntervalIntegrable
      (fun v : ℝ => q11ContourDensity v *
        externalLogKernel contourRatio u v)
      volume (0 : ℝ) (2 * Real.pi) := by
    exact ((q11ContourDensity_continuous.mul
      (q11_externalLogKernel_continuous contourRatio u hq)).intervalIntegrable _ _)
  have hconst : IntervalIntegrable
      (fun v : ℝ => q11ContourDensity v * Real.log contourScale)
      volume (0 : ℝ) (2 * Real.pi) := by
    exact (q11ContourDensity_continuous.mul continuous_const).intervalIntegrable _ _
  have hsplit :
      (∫ v in (0 : ℝ)..(2 * Real.pi),
        q11ContourDensity v *
          Real.log ‖Li2Lean.p0EllipsePoint 1 u -
            Li2Lean.p0EllipsePoint 1 v‖) =
      ∫ v in (0 : ℝ)..(2 * Real.pi),
        q11ContourDensity v * Real.log contourScale +
          (q11ContourDensity v * diagonalLogKernel u v +
            q11ContourDensity v * externalLogKernel contourRatio u v) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [q11_phase_ne_ae u] with v hv
    intro hvI
    have hphase : phase u ≠ phase v := fun h => hv h.symm
    rw [ellipse_log_distance u v hphase,
      q11_diagonalKernel_eq_phase_difference,
      q11_externalKernel_eq_correction]
    ring
  unfold q11ContourPotential q11ContourIntegral
  rw [hsplit,
    intervalIntegral.integral_add hconst (hdiag.add hext),
    intervalIntegral.integral_add hdiag hext,
    intervalIntegral.integral_mul_const,
    q11IntegralContourDensity]
  unfold q11ContourMass
  rw [q11ContourWeight_sum]
  field_simp

theorem q11ContourPotential_eq_fourier (u : ℝ) :
    q11ContourPotential (Li2Lean.p0EllipsePoint 1 u) =
      q11ContourPotentialFourier u := by
  have hq : ‖(contourRatio : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg contourRatio_nonneg]
    exact contourRatio_lt_one
  have hext :
      (∫ v in (0 : ℝ)..(2 * Real.pi),
        q11ContourDensity v * externalLogKernel contourRatio u v) =
      ∑ n ∈ Finset.range 48,
        (-(contourRatio ^ (n + 1) / (n + 1 : ℝ))) *
          (2 * Real.pi * q11ContourFourierMoment (n + 1) *
            Real.cos ((n + 1 : ℝ) * u)) := by
    have hsymfun :
        (fun v : ℝ => q11ContourDensity v *
          externalLogKernel contourRatio u v) =
        (fun v => q11ContourDensity v *
          externalLogKernel contourRatio v u) := by
      funext v
      rw [q11_externalLogKernel_symm contourRatio u v]
    rw [hsymfun]
    exact q11ExternalLogKernel_integral_eq_finite_moment contourRatio u hq
  have hdiag :
      (∫ v in (0 : ℝ)..(2 * Real.pi),
        q11ContourDensity v * diagonalLogKernel u v) =
      -(2 * Real.pi) * q11ContourLogPolynomial (phase (-u)) := by
    calc
      _ = ∫ v in (0 : ℝ)..(2 * Real.pi),
            q11ContourDensity v * diagonalLogKernel v u := by
          congr 1
          funext v
          rw [q11_diagonalKernel_symm]
      _ = _ := q11ContourDensity_diagonalLog_integral u
  rw [q11ContourPotential_joukowski_split,
    hdiag, hext,
    q11ContourLogPolynomial_phase_neg_succ_sum]
  unfold q11ContourPotentialFourier
  have hp : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  rw [mul_add]
  rw [Finset.mul_sum]
  have hscale (S : ℝ) :
      (2 * Real.pi)⁻¹ * (-(2 * Real.pi) * S) = -S := by
    field_simp
  have hfirst :
      (2 * Real.pi)⁻¹ *
          (∑ i ∈ Finset.range 48,
            -(2 * Real.pi) *
              (q11ContourFourierMoment (i + 1) * (1 / (i + 1 : ℝ)) *
                Real.cos ((i + 1 : ℝ) * u))) =
        -(∑ i ∈ Finset.range 48,
            q11ContourFourierMoment (i + 1) * (1 / (i + 1 : ℝ)) *
              Real.cos ((i + 1 : ℝ) * u)) := by
    rw [← Finset.mul_sum, hscale]
  have hsecond :
      (2 * Real.pi)⁻¹ *
          (∑ n ∈ Finset.range 48,
            -(contourRatio ^ (n + 1) / (n + 1 : ℝ)) *
              (2 * Real.pi * q11ContourFourierMoment (n + 1) *
                Real.cos ((n + 1 : ℝ) * u))) =
        ∑ n ∈ Finset.range 48,
          (2 * Real.pi)⁻¹ *
            (-(contourRatio ^ (n + 1) / (n + 1 : ℝ)) *
              (2 * Real.pi * q11ContourFourierMoment (n + 1) *
                Real.cos ((n + 1 : ℝ) * u))) := by
    rw [Finset.mul_sum]
  rw [hfirst, hsecond, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  have hsum : ∀ n ∈ Finset.range 48,
      -(q11ContourFourierMoment (n + 1) * (1 / (n + 1 : ℝ)) *
          Real.cos ((n + 1 : ℝ) * u)) +
        (2 * Real.pi)⁻¹ *
          (-(contourRatio ^ (n + 1) / (n + 1 : ℝ)) *
            (2 * Real.pi * q11ContourFourierMoment (n + 1) *
              Real.cos ((n + 1 : ℝ) * u))) =
        -((1 + contourRatio ^ (n + 1)) *
            q11ContourFourierMoment (n + 1) / (n + 1 : ℝ) *
          Real.cos ((n + 1 : ℝ) * u)) := by
    intro n hn
    have hpi : (Real.pi : ℝ) ≠ 0 := ne_of_gt Real.pi_pos
    field_simp [hpi]
    ring
  rw [Finset.sum_congr rfl hsum]
  rw [Finset.sum_neg_distrib]
  ring

end

end Li2Lean.P0.Q11Data
