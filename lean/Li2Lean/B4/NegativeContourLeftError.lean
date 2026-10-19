/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B4.NegativeContourBottomLeft
import Li2Lean.B4.NegativeContourRealAnalysis

open Complex Real Set
open scoped BigOperators Interval

namespace Li2Lean.B4.NegContour

noncomputable section

open Li2Lean.P0.Config
open MeasureTheory

/-- The normalized point attached to a point on the finite contour. -/
def hpNegLeftScaledPoint (n : ℕ) (w : ℂ) : ℂ :=
  ⟨w.re / (n : ℝ), w.im / (n : ℝ)⟩

private theorem hp_neg_left_side_coordinates {n : ℕ} {w : ℂ}
    (hw : w ∈ hpNegLeftSide n) :
    w.re = (-1 / 2 : ℝ) ∧
      -((n : ℝ) / 5) ≤ w.im ∧ w.im ≤ (n : ℝ) / 5 := by
  have h := hw
  simp [hpNegLeftSide, hpRectLower, hpRectUpper] at h
  rcases h with ⟨hre, hlo, hhi⟩
  have hlo' : -((n : ℝ) / 5) ≤ w.im := by
    simpa [div_eq_mul_inv] using hlo
  have hhi' : w.im ≤ (n : ℝ) / 5 := by
    simpa [div_eq_mul_inv] using hhi
  exact ⟨hre, hlo', hhi'⟩

private theorem hp_neg_left_scaled_point_coordinates {n : ℕ}
    (hn : 30 ≤ n) {w : ℂ} (hw : w ∈ hpNegLeftSide n) :
    (hpNegLeftScaledPoint n w).re = -1 / (2 * (n : ℝ)) ∧
      -(1 / 5 : ℝ) ≤ (hpNegLeftScaledPoint n w).im ∧
      (hpNegLeftScaledPoint n w).im ≤ 1 / 5 := by
  have hnpos : 0 < n := by omega
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  rcases hp_neg_left_side_coordinates hw with ⟨hre, himlo, himhi⟩
  constructor
  · simp [hpNegLeftScaledPoint, hre]
    field_simp
  · constructor
    · apply (le_div_iff₀ hnR).2
      nlinarith
    · apply (div_le_iff₀ hnR).2
      nlinarith

private theorem hp_neg_left_scaled_point_norm_bounds {n : ℕ}
    (hn : 30 ≤ n) {w : ℂ} (hw : w ∈ hpNegLeftSide n) :
    1 / (2 * (n : ℝ)) ≤ ‖hpNegLeftScaledPoint n w‖ ∧
      ‖hpNegLeftScaledPoint n w‖ ≤ 1 / 4 := by
  let xi := hpNegLeftScaledPoint n w
  rcases hp_neg_left_scaled_point_coordinates hn hw with
    ⟨hre, himlo, himhi⟩
  have hre' : xi.re = -(1 / (2 * (n : ℝ))) := by
    convert hre using 1 <;> simp [xi] <;> ring
  have hnR30 : (30 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hfrac : 1 / (2 * (n : ℝ)) ≤ (1 / 60 : ℝ) := by
    apply (div_le_div_iff₀ (by positivity) (by norm_num)).2
    nlinarith
  have hreabs : |xi.re| = 1 / (2 * (n : ℝ)) := by
    rw [hre', abs_of_nonpos (by nlinarith [show (0 : ℝ) < 1 / (2 * (n : ℝ)) by positivity])]
    ring
  have hreabs' : |xi.re| ≤ 1 / 60 := by rw [hreabs]; exact hfrac
  have himabs : |xi.im| ≤ 1 / 5 := abs_le.mpr ⟨himlo, himhi⟩
  have hsq : ‖xi‖ ^ 2 = xi.re ^ 2 + xi.im ^ 2 := by
    simpa using Li2Lean.P0.Config.cp_sq_norm xi 0
  have hre_sq : xi.re ^ 2 ≤ (1 / 60 : ℝ) ^ 2 := by
    have hmul := mul_le_mul hreabs' hreabs' (abs_nonneg xi.re) (by norm_num)
    nlinarith [sq_abs xi.re, hmul]
  have him_sq : xi.im ^ 2 ≤ (1 / 5 : ℝ) ^ 2 := by
    have hmul := mul_le_mul himabs himabs (abs_nonneg xi.im) (by norm_num)
    nlinarith [sq_abs xi.im, hmul]
  have hsq_le : ‖xi‖ ^ 2 ≤ (1 / 4 : ℝ) ^ 2 := by
    nlinarith [hsq, hre_sq, him_sq]
  have hnormnonneg : 0 ≤ ‖xi‖ := norm_nonneg _
  have hnormle : ‖xi‖ ≤ 1 / 4 := by nlinarith
  have hnormlo : 1 / (2 * (n : ℝ)) ≤ ‖xi‖ := by
    have h := Complex.abs_re_le_norm xi
    rw [hreabs] at h
    exact h
  exact ⟨hnormlo, hnormle⟩

private theorem hp_neg_left_scaled_target_distance_bounds {n : ℕ}
    (hn : 30 ≤ n) {w : ℂ} (hw : w ∈ hpNegLeftSide n) :
    1 ≤ ‖hpNegLeftScaledPoint n w -
          ((((3 * n + 1 : ℕ) : ℝ) / (n : ℝ)) : ℂ)‖ ∧
      ‖hpNegLeftScaledPoint n w -
          ((((3 * n + 1 : ℕ) : ℝ) / (n : ℝ)) : ℂ)‖ ≤ 4 := by
  let xi := hpNegLeftScaledPoint n w
  let t : ℝ := ((3 * n + 1 : ℕ) : ℝ) / (n : ℝ)
  rcases hp_neg_left_scaled_point_coordinates hn hw with
    ⟨hre, himlo, himhi⟩
  have hre' : xi.re = -(1 / (2 * (n : ℝ))) := by
    convert hre using 1 <;> simp [xi] <;> ring
  rcases hp_neg_left_scaled_point_norm_bounds hn hw with ⟨_, hxi⟩
  have hnR : (0 : ℝ) < (n : ℝ) := by
    have hnpos : 0 < n := by omega
    exact_mod_cast hnpos
  have hnR30 : (30 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have htlo : 3 ≤ t := by
    dsimp [t]
    apply (le_div_iff₀ hnR).2
    push_cast
    nlinarith
  have hthi : t ≤ 31 / 10 := by
    dsimp [t]
    apply (div_le_iff₀ hnR).2
    push_cast
    nlinarith
  have hreal : (xi - (t : ℂ)).re ≤ -1 := by
    rw [Complex.sub_re, Complex.ofReal_re]
    dsimp [xi]
    rw [hre']
    have hpos : 0 < 1 / (2 * (n : ℝ)) := by positivity
    nlinarith [htlo, hpos]
  have hnormlo : 1 ≤ ‖xi - (t : ℂ)‖ := by
    have hreal0 : (xi - (t : ℂ)).re ≤ 0 := le_trans hreal (by norm_num)
    have habs : 1 ≤ |(xi - (t : ℂ)).re| := by
      rw [abs_of_nonpos hreal0]
      linarith
    exact le_trans habs (Complex.abs_re_le_norm _)
  have hnormhi : ‖xi - (t : ℂ)‖ ≤ 4 := by
    calc
      ‖xi - (t : ℂ)‖ ≤ ‖xi‖ + ‖(t : ℂ)‖ := norm_sub_le _ _
      _ = ‖xi‖ + t := by simp [Complex.norm_real, abs_of_nonneg (le_trans (by norm_num) htlo)]
      _ ≤ 1 / 4 + 31 / 10 := add_le_add hxi hthi
      _ ≤ 4 := by norm_num
  have htC : (t : ℂ) = ((3 * n + 1 : ℕ) : ℂ) / (n : ℂ) := by
    simp [t, Complex.ofReal_div]
  have hnormlo' : 1 ≤ ‖hpNegLeftScaledPoint n w -
      ((3 * n + 1 : ℕ) : ℂ) / (n : ℂ)‖ := by
    rw [← htC]
    simpa [xi] using hnormlo
  have hnormhi' : ‖hpNegLeftScaledPoint n w -
      ((3 * n + 1 : ℕ) : ℂ) / (n : ℂ)‖ ≤ 4 := by
    rw [← htC]
    simpa [xi] using hnormhi
  exact ⟨hnormlo', hnormhi'⟩

/-- The endpoint allowance holds for normalized points on the actual left
side; no estimate for arbitrary complex `xi` is asserted. -/
theorem hp_neg_left_endpoint_bound_three {n : ℕ}
    (hn : 30 ≤ n) {w : ℂ} (hw : w ∈ hpNegLeftSide n) :
    HpEndpointBound 3 n (hpNegLeftScaledPoint n w) := by
  let xi := hpNegLeftScaledPoint n w
  rcases hp_neg_left_scaled_point_norm_bounds hn hw with ⟨hlo, hhi⟩
  have hhi' : ‖xi‖ ≤ 1 / 4 := by simpa [xi] using hhi
  rcases hp_neg_left_scaled_target_distance_bounds hn hw with ⟨hnumlo, hnumhi⟩
  have hnRpos : (0 : ℝ) < (n : ℝ) := by
    have hnpos : 0 < n := by omega
    exact_mod_cast hnpos
  have hlogNnonneg : 0 ≤ Real.log ((n + 1 : ℕ) : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ n + 1 by omega)
  have hnumpos : 0 < ‖xi - ((((3 * n + 1 : ℕ) : ℝ) / (n : ℝ)) : ℂ)‖ :=
    lt_of_lt_of_le (by norm_num) hnumlo
  have hnumlog0 : 0 ≤ Real.log ‖xi -
      ((((3 * n + 1 : ℕ) : ℝ) / (n : ℝ)) : ℂ)‖ := by
    apply Real.log_nonneg
    exact hnumlo
  have hnumlog3 : Real.log ‖xi -
      ((((3 * n + 1 : ℕ) : ℝ) / (n : ℝ)) : ℂ)‖ ≤ 3 := by
    calc
      Real.log ‖xi - ((((3 * n + 1 : ℕ) : ℝ) / (n : ℝ)) : ℂ)‖ ≤
          ‖xi - ((((3 * n + 1 : ℕ) : ℝ) / (n : ℝ)) : ℂ)‖ - 1 :=
        Real.log_le_sub_one_of_pos hnumpos
      _ ≤ 3 := by linarith
  have hxiPos : 0 < ‖xi‖ := by
    exact lt_of_lt_of_le (by positivity) hlo
  have hxiLog0 : Real.log ‖xi‖ ≤ 0 := by
    calc
      Real.log ‖xi‖ ≤ Real.log 1 := Real.log_le_log hxiPos (le_trans hhi' (by norm_num))
      _ = 0 := by simp
  have hxiLogLower : Real.log (1 / (2 * (n : ℝ))) ≤ Real.log ‖xi‖ :=
    Real.log_le_log (by positivity) hlo
  have hinv : Real.log (1 / (2 * (n : ℝ))) = -Real.log (2 * (n : ℝ)) := by
    rw [one_div, Real.log_inv]
  have hlogn : Real.log (n : ℝ) ≤ Real.log ((n + 1 : ℕ) : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast Nat.le_succ n
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    calc
      Real.log 2 ≤ 2 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
      _ = 1 := by norm_num
  have hlogprod : Real.log (2 * (n : ℝ)) = Real.log 2 + Real.log (n : ℝ) :=
    Real.log_mul (by norm_num) (by positivity)
  have hxiLogBound : -Real.log ‖xi‖ ≤
      3 * (1 + Real.log ((n + 1 : ℕ) : ℝ)) := by
    rw [hinv] at hxiLogLower
    rw [hlogprod] at hxiLogLower
    have : -Real.log ‖xi‖ ≤ Real.log 2 + Real.log (n : ℝ) := by linarith
    nlinarith
  unfold HpEndpointBound hpNumeratorEndpoint hpDenominatorEndpoint hpLog
  change |Real.log ‖hpNegLeftScaledPoint n w -
      (↑((↑(3 * n + 1 : ℕ) : ℝ) / (↑n : ℝ)) : ℂ)‖| ≤
      3 * (1 + Real.log ((n + 1 : ℕ) : ℝ)) ∧
    |Real.log ‖hpNegLeftScaledPoint n w - (0 : ℂ)‖| ≤
      3 * (1 + Real.log ((n + 1 : ℕ) : ℝ))
  constructor
  · have hnumlog0' : 0 ≤ Real.log ‖hpNegLeftScaledPoint n w -
        (↑((↑(3 * n + 1 : ℕ) : ℝ) / (↑n : ℝ)) : ℂ)‖ := by
      simpa [xi] using hnumlog0
    have hnumlog3' : Real.log ‖hpNegLeftScaledPoint n w -
        (↑((↑(3 * n + 1 : ℕ) : ℝ) / (↑n : ℝ)) : ℂ)‖ ≤ 3 := by
      simpa [xi] using hnumlog3
    rw [abs_of_nonneg hnumlog0']
    nlinarith [hnumlog3', hlogNnonneg]
  · have hxiLog0' : Real.log ‖hpNegLeftScaledPoint n w - (0 : ℂ)‖ ≤ 0 := by
      simpa [xi] using hxiLog0
    rw [abs_of_nonpos hxiLog0']
    simpa [sub_zero, xi] using hxiLogBound

private theorem hp_neg_cp_cell_right_le (ζ : ℂ) {a : ℝ}
    (ha : 0 < a + ζ.re) (hne : ζ + ((a + 1 : ℝ) : ℂ) ≠ 0) :
    (∫ u in a..a + 1, cpLog ζ u) ≤ cpLog ζ (a + 1) := by
  have hmono : ∀ u ∈ Set.Icc a (a + 1), cpLog ζ u ≤ cpLog ζ (a + 1) := by
    intro u hu
    have hleft : 0 < u + ζ.re := by
      have hbase : 0 < a + ζ.re := ha
      nlinarith [hu.1, hbase]
    have hright : 0 ≤ a + 1 + ζ.re := by linarith
    have hsq : (u + ζ.re) ^ 2 ≤ (a + 1 + ζ.re) ^ 2 := by
      nlinarith [hu.1, hu.2, hleft, hright]
    have hnorm := cp_norm_le ζ hsq
    have hzero : ζ + (u : ℂ) ≠ 0 := by
      intro hz
      have hzre := congrArg Complex.re hz
      simp at hzre
      linarith
    exact Real.log_le_log (norm_pos_iff.mpr hzero) hnorm
  have h := intervalIntegral.integral_mono_on (f := cpLog ζ)
    (g := fun _ : ℝ => cpLog ζ (a + 1)) (by linarith)
    (cp_integrable ζ a (a + 1)) intervalIntegrable_const hmono
  simpa using h

private theorem hp_neg_cp_sum_sub_integral_abs (ζ : ℂ) (g : ℕ)
    (hζ : 0 < ζ.re)
    (hne : ∀ k : ℕ, 1 ≤ k → k ≤ g →
      ζ + ((k : ℝ) : ℂ) ≠ 0) :
    |(∑ k ∈ Finset.range g, cpLog ζ ((k : ℝ) + 1)) -
        (∫ u in (0 : ℝ)..(g : ℝ), cpLog ζ u)| ≤
      Real.log ((g : ℝ) + 1) + 2 := by
  have hsplit : (∫ u in (0 : ℝ)..(g : ℝ), cpLog ζ u) =
      ∑ k ∈ Finset.range g,
        ∫ u in (k : ℝ)..(k : ℝ) + 1, cpLog ζ u := by
    have h := intervalIntegral.sum_integral_adjacent_intervals (f := cpLog ζ)
      (μ := volume) (a := fun k : ℕ => (k : ℝ)) (n := g)
      (fun k _ => cp_integrable ζ _ _)
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero] at h
    exact h.symm
  have hnonneg : 0 ≤
      (∑ k ∈ Finset.range g, cpLog ζ ((k : ℝ) + 1)) -
        (∫ u in (0 : ℝ)..(g : ℝ), cpLog ζ u) := by
    rw [hsplit, ← Finset.sum_sub_distrib]
    apply Finset.sum_nonneg
    intro k hk
    have hkR : 0 < (k : ℝ) + ζ.re := by positivity
    have hendpoint : ζ + (((k : ℝ) + 1 : ℝ) : ℂ) ≠ 0 := by
      have hk1 : 1 ≤ k + 1 := by omega
      have hkg : k + 1 ≤ g := by
        exact Finset.mem_range.mp hk
      simpa [Nat.cast_add, Nat.cast_one] using hne (k + 1) hk1 hkg
    exact sub_nonneg.mpr (hp_neg_cp_cell_right_le ζ hkR hendpoint)
  have hupper := cp_sum_sub_integral ζ g hne
  rw [abs_of_nonneg hnonneg]
  exact hupper

private theorem hp_neg_left_scaled_sample_ne {n : ℕ}
    (hn : 0 < n) {xi : ℂ} (hxi : xi.re < 0) (u : ℝ) (hu : 0 ≤ u) :
    xi - ((u / (n : ℝ)) : ℂ) ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  simp at hre
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hdiv : 0 ≤ u / (n : ℝ) := div_nonneg hu hnR.le
  linarith

private theorem hp_neg_left_right_error_eq_cp (n a m : ℕ)
    (hn : 0 < n) (xi : ℂ) (hxi : xi.re < 0) :
    hpRightLogSum n a m xi - hpScaledLogIntegral n a m xi =
      (∑ k ∈ Finset.range m,
        cpLog (-((n : ℂ) * xi) + (a : ℝ)) ((k : ℝ) + 1)) -
      (∫ u in (0 : ℝ)..(m : ℝ),
        cpLog (-((n : ℂ) * xi) + (a : ℝ)) u) := by
  let η : ℂ := -((n : ℂ) * xi)
  let ζ : ℂ := η + (a : ℝ)
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsum : hpRightLogSum n a m xi =
      (∑ k ∈ Finset.range m, cpLog ζ ((k : ℝ) + 1)) -
        (m : ℝ) * Real.log (n : ℝ) := by
    unfold hpRightLogSum
    calc
      (∑ k ∈ Finset.range m,
          hpLog xi (((a + k + 1 : ℕ) : ℝ) / (n : ℝ))) =
          ∑ k ∈ Finset.range m,
            (cpLog ζ ((k : ℝ) + 1) - Real.log (n : ℝ)) := by
        apply Finset.sum_congr rfl
        intro k hk
        have hu : 0 ≤ ((a + k + 1 : ℕ) : ℝ) := by positivity
        have hne := hp_neg_left_scaled_sample_ne hn hxi _ hu
        have hshift : cpLog η (((a + k + 1 : ℕ) : ℝ)) =
            cpLog ζ ((k : ℝ) + 1) := by
          have harg : η + (((a + k + 1 : ℕ) : ℝ) : ℂ) =
              ζ + (((k : ℝ) + 1) : ℂ) := by
            dsimp [ζ, η]
            push_cast
            ring
          simpa [cpLog] using
            congrArg (fun z : ℂ => Real.log ‖z‖) harg
        rw [hp_log_scale n hn xi _ hne, hshift]
      _ = (∑ k ∈ Finset.range m, cpLog ζ ((k : ℝ) + 1)) -
          (m : ℝ) * Real.log (n : ℝ) := by
        simp [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range]
  have hcomp := intervalIntegral.integral_comp_mul_left (hpLog xi)
    (c := (n : ℝ)⁻¹) (a := (a : ℝ))
    (b := ((a + m : ℕ) : ℝ)) (by exact inv_ne_zero (by exact_mod_cast hn.ne'))
  have hscaled : hpScaledLogIntegral n a m xi =
      ∫ u in (a : ℝ)..((a + m : ℕ) : ℝ), hpLog xi ((n : ℝ)⁻¹ * u) := by
    unfold hpScaledLogIntegral
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc,
      smul_eq_mul] using hcomp.symm
  have hintegrand :
      (∫ u in (a : ℝ)..((a + m : ℕ) : ℝ),
        hpLog xi ((n : ℝ)⁻¹ * u)) =
      (∫ u in (a : ℝ)..((a + m : ℕ) : ℝ),
        cpLog η u - Real.log (n : ℝ)) := by
    apply intervalIntegral.integral_congr
    intro u hu
    have hab : (a : ℝ) ≤ ((a + m : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right a m
    rw [Set.uIcc_of_le hab] at hu
    have hu0 : 0 ≤ u := le_trans (by positivity) hu.1
    have hne := hp_neg_left_scaled_sample_ne hn hxi u hu0
    simpa [div_eq_mul_inv, mul_comm, η] using hp_log_scale n hn xi u hne
  have hintegral : hpScaledLogIntegral n a m xi =
      (∫ u in (a : ℝ)..((a + m : ℕ) : ℝ), cpLog η u) -
        (m : ℝ) * Real.log (n : ℝ) := by
    rw [hscaled, hintegrand,
      intervalIntegral.integral_sub (cp_integrable η _ _) intervalIntegrable_const]
    simp
  have hshift :
      (∫ u in (a : ℝ)..((a + m : ℕ) : ℝ), cpLog η u) =
        (∫ u in (0 : ℝ)..(m : ℝ), cpLog ζ u) := by
    have hadd := intervalIntegral.integral_comp_add_right (cpLog η)
      (d := (a : ℝ)) (a := (0 : ℝ)) (b := (m : ℝ))
    calc
      (∫ u in (a : ℝ)..((a + m : ℕ) : ℝ), cpLog η u) =
          ∫ u in (0 : ℝ)..(m : ℝ), cpLog η (u + (a : ℝ)) := by
        symm
        simpa [Nat.cast_add, add_comm] using hadd
      _ = (∫ u in (0 : ℝ)..(m : ℝ), cpLog ζ u) := by
        apply intervalIntegral.integral_congr
        intro u hu
        have harg : η + ((u + (a : ℝ)) : ℂ) = ζ + (u : ℂ) := by
          dsimp [ζ]
          push_cast
          ring
        simpa [cpLog] using
          congrArg (fun z : ℂ => Real.log ‖z‖) harg
  change hpRightLogSum n a m xi - hpScaledLogIntegral n a m xi =
    (∑ k ∈ Finset.range m, cpLog ζ ((k : ℝ) + 1)) -
      (∫ u in (0 : ℝ)..(m : ℝ), cpLog ζ u)
  calc
    hpRightLogSum n a m xi - hpScaledLogIntegral n a m xi =
        ((∑ k ∈ Finset.range m, cpLog ζ ((k : ℝ) + 1)) -
            (m : ℝ) * Real.log (n : ℝ)) -
          ((∫ u in (a : ℝ)..((a + m : ℕ) : ℝ), cpLog η u) -
            (m : ℝ) * Real.log (n : ℝ)) := by rw [hsum, hintegral]
    _ = (∑ k ∈ Finset.range m, cpLog ζ ((k : ℝ) + 1)) -
        (∫ u in (0 : ℝ)..(m : ℝ), cpLog ζ u) := by rw [hshift]; ring

private theorem hp_neg_right_error_bound_three (n a m : ℕ)
    (hn : 30 ≤ n) (xi : ℂ) (hxi : xi.re < 0) (hm : m ≤ 2 * n) :
    HpRightErrorBound 3 n a m xi := by
  have hnpos : 0 < n := by omega
  let ζ : ℂ := -((n : ℂ) * xi) + (a : ℝ)
  have hζ : 0 < ζ.re := by
    dsimp [ζ]
    simp only [Complex.mul_re]
    simp
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hnpos
    have haR : 0 ≤ (a : ℝ) := by positivity
    nlinarith
  have hne : ∀ k : ℕ, 1 ≤ k → k ≤ m →
      ζ + ((k : ℝ) : ℂ) ≠ 0 := by
    intro k hk1 hkm hz
    have hre := congrArg Complex.re hz
    simp at hre
    have hkR : 0 ≤ (k : ℝ) := by positivity
    linarith
  have hquad := hp_neg_cp_sum_sub_integral_abs ζ m hζ hne
  have hlogN : 0 ≤ Real.log ((n + 1 : ℕ) : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ n + 1 by omega)
  have hmR : (m : ℝ) + 1 ≤ 2 * ((n : ℝ) + 1) := by
    have hm' : (m : ℝ) ≤ 2 * (n : ℝ) := by exact_mod_cast hm
    nlinarith
  have hlogm : Real.log ((m : ℝ) + 1) ≤
      Real.log 2 + Real.log ((n : ℝ) + 1) := by
    rw [← Real.log_mul (by norm_num) (by positivity)]
    exact Real.log_le_log (by positivity) hmR
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    calc
      Real.log 2 ≤ 2 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
      _ = 1 := by norm_num
  have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  unfold HpRightErrorBound
  rw [hp_neg_left_right_error_eq_cp n a m hnpos xi hxi]
  rw [hcast] at hlogN ⊢
  have hbound : Real.log ((m : ℝ) + 1) + 2 ≤
      3 * (1 + Real.log ((n : ℝ) + 1)) := by
    nlinarith
  exact hquad.trans hbound

/-- The product logarithm error is bounded at every point on the actual
normalized left contour. -/
theorem hp_neg_left_product_log_error_bound {n : ℕ}
    (hn : 30 ≤ n) {w : ℂ} (hw : w ∈ hpNegLeftSide n) :
    |hpProductLogError n (w / (n : ℂ))| ≤
      18 * (1 + Real.log ((n + 1 : ℕ) : ℝ)) := by
  have hnpos : 0 < n := by omega
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  have hxi : hpNegLeftScaledPoint n w = w / (n : ℂ) := by
    apply Complex.ext <;>
      simp [hpNegLeftScaledPoint, Complex.div_re, Complex.div_im] <;>
      field_simp [hnR.ne']
  have hxiR : (hpNegLeftScaledPoint n w).re =
      -1 / (2 * (n : ℝ)) :=
    (hp_neg_left_scaled_point_coordinates hn hw).1
  have hxiNeg : (hpNegLeftScaledPoint n w).re < 0 := by
    rw [hxiR]
    have hfrac : 0 < (1 : ℝ) / (2 * (n : ℝ)) := by positivity
    rw [show -1 / (2 * (n : ℝ)) = -(1 / (2 * (n : ℝ))) by ring]
    exact neg_neg_of_pos hfrac
  have hnum : HpRightErrorBound 3 n n (2 * n)
      (hpNegLeftScaledPoint n w) := by
    apply hp_neg_right_error_bound_three n n (2 * n) hn
    · exact hxiNeg
    · omega
  have hden : HpRightErrorBound 3 n 0 n
      (hpNegLeftScaledPoint n w) := by
    apply hp_neg_right_error_bound_three n 0 n hn
    · exact hxiNeg
    · omega
  have hend := hp_neg_left_endpoint_bound_three hn hw
  have herr := hp_neg_product_log_error_bound_three n hnpos
    (hpNegLeftScaledPoint n w) hnum hden hend
  rw [← hxi]
  exact herr

end

end Li2Lean.B4.NegContour

#print axioms Li2Lean.B4.NegContour.hp_neg_left_endpoint_bound_three
#print axioms Li2Lean.B4.NegContour.hp_neg_left_product_log_error_bound
