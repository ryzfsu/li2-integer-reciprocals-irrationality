/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B4.NegativeContourBottomCellAdapter
import Li2Lean.B4.NegativeContourValley

open Complex Real Set
open scoped BigOperators Interval

namespace Li2Lean.B4.NegContour

noncomputable section

open Li2Lean.P0.Config

/-!
Concrete cell producers for the lower horizontal side in `hp-tail.tex:307-316`.
The one-half quadrature theorem gives the upper error bound for every `cpLog`.
On the bottom side the translated parameter can have either real sign, so the
matching lower error bound is supplied by the construction-bound
`valley_lower` field from `HpNegBottomLeftEnvelope`.
-/

private theorem hp_neg_bottom_scaled_sample_ne {n : ℕ}
    {xi : ℂ} (hxi_im : xi.im ≠ 0) (u : ℝ) :
    xi - ((u / (n : ℝ)) : ℂ) ≠ 0 := by
  intro h
  apply hxi_im
  have him := congrArg Complex.im h
  simpa using him

private theorem hp_neg_bottom_right_error_eq_cp (n a m : ℕ)
    (hn : 0 < n) (xi : ℂ) (hxi_im : xi.im ≠ 0) :
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
        have hne := hp_neg_bottom_scaled_sample_ne (n := n) hxi_im
          (((a + k + 1 : ℕ) : ℝ))
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
      ∫ u in (a : ℝ)..((a + m : ℕ) : ℝ),
        hpLog xi ((n : ℝ)⁻¹ * u) := by
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
    have hab : (a : ℝ) ≤ ((a + m : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_add_right a m
    rw [Set.uIcc_of_le hab] at hu
    have hu0 : 0 ≤ u := le_trans (by positivity) hu.1
    have hne := hp_neg_bottom_scaled_sample_ne (n := n) hxi_im u
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

private theorem hp_neg_bottom_right_error_bound_three
    (n a m : ℕ) (hn : 30 ≤ n) (hm : 0 < m) (hmle : m ≤ 2 * n)
    {w : ℂ} (hw : w ∈ hpNegBottomSide n)
    (valley_lower : ∀ (ζ : ℂ) (g : ℕ), 1 ≤ g → 1 ≤ ζ.im →
      -Real.log (8 * ((g : ℝ) + 1)) ≤ hpNegValleyError ζ g) :
    HpRightErrorBound 3 n a m (w / (n : ℂ)) := by
  have hnpos : 0 < n := by omega
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hnpos
  have hxi_im : (w / (n : ℂ)).im = -(1 / 5 : ℝ) := by
    have hcoords := hp_neg_bottom_side_coordinates hw
    simp [Complex.div_im]
    rw [hcoords.2.2]
    field_simp [hnR.ne']
  have hxi_im_ne : (w / (n : ℂ)).im ≠ 0 := by
    rw [hxi_im]
    norm_num
  let xi : ℂ := w / (n : ℂ)
  let ζ : ℂ := -((n : ℂ) * xi) + (a : ℝ)
  have hζ_im : ζ.im = (n : ℝ) / 5 := by
    dsimp [ζ, xi]
    simp [Complex.mul_im, hxi_im]
    ring
  have hζ_im_ne : ζ.im ≠ 0 := by rw [hζ_im]; positivity
  have hne : ∀ k : ℕ, 1 ≤ k → k ≤ m →
      ζ + ((k : ℝ) : ℂ) ≠ 0 := by
    intro k hk1 hkm hz
    apply hζ_im_ne
    have him := congrArg Complex.im hz
    simpa using him
  have hupper := cp_sum_sub_integral ζ m hne
  have hζ_im_ge : 1 ≤ ζ.im := by
    rw [hζ_im]
    have hnR30 : (30 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hlower := valley_lower ζ m (by omega) hζ_im_ge
  have hupper' :
      (∑ k ∈ Finset.range m, cpLog ζ ((k : ℝ) + 1)) -
        (∫ u in (0 : ℝ)..(m : ℝ), cpLog ζ u) ≤
      3 * (1 + Real.log ((n + 1 : ℕ) : ℝ)) := by
    have hlogN : 0 ≤ Real.log ((n + 1 : ℕ) : ℝ) := by
      apply Real.log_nonneg
      exact_mod_cast (show 1 ≤ n + 1 by omega)
    have hmR : (m : ℝ) + 1 ≤ 2 * ((n : ℝ) + 1) := by
      have hm' : (m : ℝ) ≤ 2 * (n : ℝ) := by exact_mod_cast hmle
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
    rw [hcast] at hlogN ⊢
    exact hupper.trans (by nlinarith)
  have hlower' :
      -(3 * (1 + Real.log ((n + 1 : ℕ) : ℝ))) ≤
        (∑ k ∈ Finset.range m, cpLog ζ ((k : ℝ) + 1)) -
          (∫ u in (0 : ℝ)..(m : ℝ), cpLog ζ u) := by
    have hN4 : (4 : ℝ) ≤ (n : ℝ) + 1 := by
      have hnR30 : (30 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      nlinarith
    have hmR : (m : ℝ) + 1 ≤ 2 * ((n : ℝ) + 1) := by
      have hm' : (m : ℝ) ≤ 2 * (n : ℝ) := by exact_mod_cast hmle
      nlinarith
    have hN0 : 0 ≤ (n : ℝ) + 1 := by positivity
    have hNm4 : 0 ≤ (n : ℝ) + 1 - 4 := by linarith
    have hNp4 : 0 ≤ (n : ℝ) + 1 + 4 := by linarith
    have hNcube : 16 * ((n : ℝ) + 1) ≤ ((n : ℝ) + 1) ^ 3 := by
      have hprod : 0 ≤ ((n : ℝ) + 1) *
          (((n : ℝ) + 1 - 4) * ((n : ℝ) + 1 + 4)) :=
        mul_nonneg hN0 (mul_nonneg hNm4 hNp4)
      nlinarith
    have hfactor : 8 * ((m : ℝ) + 1) ≤ ((n : ℝ) + 1) ^ 3 := by
      calc
        8 * ((m : ℝ) + 1) ≤ 8 * (2 * ((n : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left hmR (by norm_num)
        _ = 16 * ((n : ℝ) + 1) := by ring
        _ ≤ ((n : ℝ) + 1) ^ 3 := hNcube
    have hlogfactor : Real.log (8 * ((m : ℝ) + 1)) ≤
        3 * Real.log ((n : ℝ) + 1) := by
      have hlog := Real.log_le_log
        (by positivity : (0 : ℝ) < 8 * ((m : ℝ) + 1)) hfactor
      rw [Real.log_pow] at hlog
      exact hlog
    have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    have hlowerE : -Real.log (8 * ((m : ℝ) + 1)) ≤
        (∑ k ∈ Finset.range m, cpLog ζ ((k : ℝ) + 1)) -
          (∫ u in (0 : ℝ)..(m : ℝ), cpLog ζ u) := by
      simpa [hpNegValleyError] using hlower
    nlinarith [hlowerE, hlogfactor]
  unfold HpRightErrorBound
  rw [hp_neg_bottom_right_error_eq_cp n a m hnpos (w / (n : ℂ)) hxi_im_ne]
  simpa [ζ, xi] using (abs_le.mpr ⟨hlower', hupper'⟩)

theorem hp_neg_bottom_numerator_cell_bound_of_valley
    (valley_lower : ∀ (ζ : ℂ) (g : ℕ), 1 ≤ g → 1 ≤ ζ.im →
      -Real.log (8 * ((g : ℝ) + 1)) ≤ hpNegValleyError ζ g)
    {n : ℕ} (hn : 30 ≤ n) {w : ℂ} (hw : w ∈ hpNegBottomSide n) :
    HpRightErrorBound 3 n n (2 * n) (w / (n : ℂ)) := by
  exact hp_neg_bottom_right_error_bound_three n n (2 * n) hn (by omega)
    (by omega) hw valley_lower

theorem hp_neg_bottom_denominator_cell_bound_of_valley
    (valley_lower : ∀ (ζ : ℂ) (g : ℕ), 1 ≤ g → 1 ≤ ζ.im →
      -Real.log (8 * ((g : ℝ) + 1)) ≤ hpNegValleyError ζ g)
    {n : ℕ} (hn : 30 ≤ n) {w : ℂ} (hw : w ∈ hpNegBottomSide n) :
    HpRightErrorBound 3 n 0 n (w / (n : ℂ)) := by
  exact hp_neg_bottom_right_error_bound_three n 0 n hn (by omega)
    (by omega) hw valley_lower

/-- Both bottom-side right-cell estimates follow from the explicit valley
lower certificate and the one-half `ConfigFgBound` upper estimate. -/
theorem hp_neg_bottom_cell_input_of_valley
    (valley_lower : ∀ (ζ : ℂ) (g : ℕ), 1 ≤ g → 1 ≤ ζ.im →
      -Real.log (8 * ((g : ℝ) + 1)) ≤ hpNegValleyError ζ g) :
    HpNegBottomCellEndpointInput := by
  refine
    { numerator_cell := ?_
      denominator_cell := ?_
      endpoint := ?_ }
  · intro n hn w hw
    exact hp_neg_bottom_numerator_cell_bound_of_valley valley_lower hn hw
  · intro n hn w hw
    exact hp_neg_bottom_denominator_cell_bound_of_valley valley_lower hn hw
  · intro n hn w hw
    exact hp_neg_bottom_endpoint_bound_three hn hw

theorem hp_neg_bottom_cell_input_v13 : HpNegBottomCellEndpointInput :=
  hp_neg_bottom_cell_input_of_valley hp_neg_valley_lower_restricted

end

end Li2Lean.B4.NegContour

#print axioms Li2Lean.B4.NegContour.hp_neg_bottom_cell_input_of_valley
