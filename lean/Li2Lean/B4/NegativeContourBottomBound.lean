/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B4.NegativeContourBottomClosedForm
import Li2Lean.B4.NegativeContourConcreteEnvelope

open Complex Real Set
open scoped BigOperators Interval

namespace Li2Lean.B4.NegContour

noncomputable section

open Li2Lean.B4
open Li2Lean.P0.Config

/-!
The lower horizontal side estimate follows the v13 product-to-integral
decomposition at `hp-tail.tex:307-316`, followed by the tangent bound in
`hp-tail.tex:319-355`.  This file keeps the concrete `hpNegPhi` product and
the full phase in `hpNegBoundaryLog`; the sum-to-integral inputs are the
reused one-half `P0/ConfigFgBound` estimates.
-/

private theorem hp_neg_bottom_scaled_point {n : ℕ} (hn : 0 < n)
    {w : ℂ} (hw : w ∈ hpNegBottomSide n) :
    w / (n : ℂ) = hpBottomPoint (hpNegScaledX n w) := by
  have hcoords := hp_neg_bottom_side_coordinates hw
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hw_eq : w = (n : ℂ) * hpBottomPoint (hpNegScaledX n w) := by
    apply Complex.ext
    · simp [hpBottomPoint, hpNegScaledX, Complex.mul_re]
      field_simp [hnR]
    · simp [hpBottomPoint, hpNegScaledX, Complex.mul_im]
      rw [hcoords.2.2]
      field_simp [hnR]
  conv_lhs => rw [hw_eq]
  field_simp [hnC]

private theorem hp_neg_scaled_factor {n : ℕ} (hn : 0 < n)
    (w : ℂ) (r : ℕ) :
    w - (r : ℂ) = (n : ℂ) *
      (w / (n : ℂ) - (((r : ℝ) / (n : ℝ)) : ℂ)) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  field_simp [hnR, hnC]
  push_cast
  ring

private theorem hp_neg_log_scaled_factor {n : ℕ} (hn : 0 < n)
    (w : ℂ) (r : ℕ) (hfac : w - (r : ℂ) ≠ 0) :
    Real.log ‖w - (r : ℂ)‖ =
      Real.log (n : ℝ) + hpLog (w / (n : ℂ)) ((r : ℝ) / (n : ℝ)) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hscaled := hp_neg_scaled_factor hn w r
  have hscaled_ne : w / (n : ℂ) -
      (((r : ℝ) / (n : ℝ)) : ℂ) ≠ 0 := by
    intro h
    apply hfac
    rw [hscaled, h]
    simp
  rw [hscaled, norm_mul, Complex.norm_natCast,
    Real.log_mul hnR.ne' (norm_ne_zero_iff.mpr hscaled_ne)]
  simp [hpLog, Complex.ofReal_div]

theorem hp_neg_bottom_phi_ne_zero {n : ℕ} (hn : 0 < n)
    {w : ℂ} (hw : w ∈ hpNegBottomSide n) : hpNegPhi n w ≠ 0 := by
  have him : w.im ≠ 0 := by
    rw [(hp_neg_bottom_side_coordinates hw).2.2]
    apply neg_ne_zero.mpr
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    exact div_ne_zero (ne_of_gt hnR) (by norm_num)
  have hfactor {r : ℕ} : w - (r : ℂ) ≠ 0 := by
    intro hz
    have him0 : w.im = 0 := by
      have hz' := congrArg Complex.im hz
      simpa using hz'
    exact him him0
  have hnum : (∏ r ∈ Finset.Icc (n + 1) (3 * n + 1),
      (w - (r : ℂ))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (by intro r hr; exact hfactor)
  have hden : (∏ j ∈ Finset.range (n + 1),
      ((w - (j : ℂ)) ^ 2)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (by intro j hj; exact pow_ne_zero 2 hfactor)
  rw [hpNegPhi, div_ne_zero_iff]
  exact ⟨hnum, hden⟩

theorem hp_neg_phi_log_norm_eq_sum {n : ℕ} (hn : 0 < n)
    {w : ℂ} (hphi : hpNegPhi n w ≠ 0) :
    Real.log ‖hpNegPhi n w‖ =
      hpProductLogSum n (w / (n : ℂ)) - Real.log (n : ℝ) := by
  have hnum : (∏ r ∈ Finset.Icc (n + 1) (3 * n + 1),
      (w - (r : ℂ))) ≠ 0 := by
    have h := (div_ne_zero_iff.mp (by simpa [hpNegPhi] using hphi)).1
    exact h
  have hden : (∏ j ∈ Finset.range (n + 1),
      ((w - (j : ℂ)) ^ 2)) ≠ 0 := by
    have h := (div_ne_zero_iff.mp (by simpa [hpNegPhi] using hphi)).2
    exact h
  have hnum_factor {r : ℕ} (hr : r ∈ Finset.Icc (n + 1) (3 * n + 1)) :
        w - (r : ℂ) ≠ 0 := by
    exact (Finset.prod_ne_zero_iff.mp hnum) r hr
  have hden_factor {j : ℕ} (hj : j ∈ Finset.range (n + 1)) :
      w - (j : ℂ) ≠ 0 := by
    have hpow := (Finset.prod_ne_zero_iff.mp hden) j hj
    intro hz
    apply hpow
    rw [hz]
    simp
  have hnum_log :
      Real.log ‖∏ r ∈ Finset.Icc (n + 1) (3 * n + 1), (w - (r : ℂ))‖ =
        ∑ r ∈ Finset.Icc (n + 1) (3 * n + 1),
          Real.log ‖w - (r : ℂ)‖ := by
    rw [norm_prod,
      Real.log_prod (fun r hr => norm_ne_zero_iff.mpr (hnum_factor hr))]
  have hden_log :
      Real.log ‖∏ j ∈ Finset.range (n + 1), ((w - (j : ℂ)) ^ 2)‖ =
        2 * ∑ j ∈ Finset.range (n + 1), Real.log ‖w - (j : ℂ)‖ := by
    rw [norm_prod,
      Real.log_prod (fun j hj => norm_ne_zero_iff.mpr (pow_ne_zero 2 (hden_factor hj)))]
    calc
      (∑ j ∈ Finset.range (n + 1), Real.log ‖(w - (j : ℂ)) ^ 2‖) =
          ∑ j ∈ Finset.range (n + 1), 2 * Real.log ‖w - (j : ℂ)‖ := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [norm_pow]
        have hnorm : ‖w - (j : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr (hden_factor hj)
        rw [show ‖w - (j : ℂ)‖ ^ 2 =
          ‖w - (j : ℂ)‖ * ‖w - (j : ℂ)‖ by ring,
          Real.log_mul hnorm hnorm]
        ring
      _ = 2 * ∑ j ∈ Finset.range (n + 1), Real.log ‖w - (j : ℂ)‖ := by
        rw [Finset.mul_sum]
  have hphi_log :
      Real.log ‖hpNegPhi n w‖ =
        (∑ r ∈ Finset.Icc (n + 1) (3 * n + 1),
          Real.log ‖w - (r : ℂ)‖) -
          2 * ∑ j ∈ Finset.range (n + 1), Real.log ‖w - (j : ℂ)‖ := by
    have hnum_norm : ‖∏ r ∈ Finset.Icc (n + 1) (3 * n + 1),
        (w - (r : ℂ))‖ ≠ 0 := norm_ne_zero_iff.mpr hnum
    have hden_norm : ‖∏ j ∈ Finset.range (n + 1),
        ((w - (j : ℂ)) ^ 2)‖ ≠ 0 := norm_ne_zero_iff.mpr hden
    rw [hpNegPhi, norm_div,
      Real.log_div hnum_norm hden_norm, hnum_log, hden_log]
  have hnum_scale :
      ∀ r ∈ Finset.Icc (n + 1) (3 * n + 1),
        Real.log ‖w - (r : ℂ)‖ =
          Real.log (n : ℝ) + hpLog (w / (n : ℂ)) ((r : ℝ) / (n : ℝ)) := by
    intro r hr
    exact hp_neg_log_scaled_factor hn w r (hnum_factor hr)
  have hden_scale :
      ∀ j ∈ Finset.range (n + 1),
        Real.log ‖w - (j : ℂ)‖ =
          Real.log (n : ℝ) + hpLog (w / (n : ℂ)) ((j : ℝ) / (n : ℝ)) := by
    intro j hj
    exact hp_neg_log_scaled_factor hn w j (hden_factor hj)
  have hcard_num : (Finset.Icc (n + 1) (3 * n + 1)).card = 2 * n + 1 := by
    simp
    omega
  have hcard_den : (Finset.range (n + 1)).card = n + 1 := by simp
  rw [hphi_log, Finset.sum_congr rfl hnum_scale, Finset.sum_congr rfl hden_scale]
  unfold hpProductLogSum hpLog
  have hrange : Finset.Icc 0 n = Finset.range (n + 1) := by
    ext j
    simp
  rw [hrange]
  simp only [Finset.sum_add_distrib, Finset.sum_const, hcard_num]
  rw [Finset.card_range]
  push_cast
  ring

/-! The actual bottom-side estimate is assembled from the product identity,
the closed-form integral, the tangent certificate, and the explicit error
bound.  The `error` premise is the analytic cell estimate supplied by the
parallel lower-left producer, not a free envelope field.
-/
theorem hp_neg_bottom_side_log_bound_of_error
    {q n : ℕ} (hq : q = 8 ∨ q = 9 ∨ q = 10)
    (hn : 30 ≤ n) (tangent : HpNegBottomTangentCertificate q)
    {w : ℂ} (hw : w ∈ hpNegBottomSide n)
    (error : |hpProductLogError n (w / (n : ℂ))| ≤
      18 * (1 + Real.log ((n + 1 : ℕ) : ℝ))) :
    hpNegBoundaryLog q n w ≤
      (n : ℝ) * (hpNegT q : ℝ) +
        18 * (1 + Real.log ((n + 1 : ℕ) : ℝ)) := by
  have hnpos : 0 < n := by omega
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hnpos
  have hcoords := hp_neg_bottom_side_coordinates hw
  have hborder : w ∈ hpNegBorder n := by
    rw [hpNegBorder_eq_union_sides]
    exact Or.inl (Or.inl (Or.inl hw))
  have hphi : hpNegPhi n w ≠ 0 := hp_neg_bottom_phi_ne_zero hnpos hw
  have hscaled := hp_neg_bottom_scaled_point hnpos hw
  have hx := hp_neg_bottom_scaled_window hn hw
  have hphase := hp_neg_boundary_log_full_phase (q := q) (n := n) hphi
  rw [hp_neg_phi_log_norm_eq_sum hnpos hphi] at hphase
  rw [show w / (n : ℂ) = hpBottomPoint (hpNegScaledX n w) by exact hscaled] at hphase
  have hsum : hpProductLogSum n (hpBottomPoint (hpNegScaledX n w)) =
      hpProductLogError n (hpBottomPoint (hpNegScaledX n w)) +
        (n : ℝ) * hpBottomClosed (hpNegScaledX n w) := by
    unfold hpProductLogError
    rw [hp_product_log_integral_bottom_closed n (hpNegScaledX n w)]
    ring
  rw [hsum] at hphase
  have hxi_error : hpProductLogError n (w / (n : ℂ)) =
      hpProductLogError n (hpBottomPoint (hpNegScaledX n w)) := by rw [hscaled]
  rw [← hxi_error] at hphase
  have hre : w.re = (n : ℝ) * hpNegScaledX n w := by
    unfold hpNegScaledX
    field_simp [ne_of_gt hnR]
  rw [hcoords.2.2, hre] at hphase
  have htangent := tangent.tangent (hpNegScaledX n w) hx.1 hx.2
  have hlogn : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (Nat.succ_le_of_lt hnpos))
  rw [show hpNegBoundaryLog q n w =
      hpProductLogError n (w / (n : ℂ)) +
        (n : ℝ) * (hpBottomClosed (hpNegScaledX n w) -
          Real.log (q : ℝ) * hpNegScaledX n w + Real.pi / 5) -
        Real.log (n : ℝ) by
          rw [hphase]
          ring] at *
  have hnnonneg : 0 ≤ (n : ℝ) := by positivity
  calc
    hpProductLogError n (w / (n : ℂ)) +
        (n : ℝ) * (hpBottomClosed (hpNegScaledX n w) -
          Real.log (q : ℝ) * hpNegScaledX n w + Real.pi / 5) -
        Real.log (n : ℝ)
      ≤ hpProductLogError n (w / (n : ℂ)) + (n : ℝ) * (hpNegT q : ℝ) := by
          nlinarith [mul_le_mul_of_nonneg_left htangent hnnonneg]
    _ ≤ 18 * (1 + Real.log ((n + 1 : ℕ) : ℝ)) +
          (n : ℝ) * (hpNegT q : ℝ) := by
          linarith [abs_le.mp error]
    _ = (n : ℝ) * (hpNegT q : ℝ) +
          18 * (1 + Real.log ((n + 1 : ℕ) : ℝ)) := by ring

/-- The producer-facing bottom estimate packages the two v13 right-cell
errors and endpoint shifts from `hp-tail.tex:307-316`; no complete
bottom/left envelope is assumed. -/
theorem hp_neg_bottom_side_log_bound_of_cell_bounds
    {q n : ℕ} (hq : q = 8 ∨ q = 9 ∨ q = 10)
    (hn : 30 ≤ n) (tangent : HpNegBottomTangentCertificate q)
    {w : ℂ} (hw : w ∈ hpNegBottomSide n)
    (hnum : HpRightErrorBound 3 n n (2 * n) (w / (n : ℂ)))
    (hden : HpRightErrorBound 3 n 0 n (w / (n : ℂ)))
    (hend : HpEndpointBound 3 n (w / (n : ℂ))) :
    hpNegBoundaryLog q n w ≤
      (n : ℝ) * (hpNegT q : ℝ) +
        18 * (1 + Real.log ((n + 1 : ℕ) : ℝ)) := by
  have hnpos : 0 < n := by omega
  exact hp_neg_bottom_side_log_bound_of_error hq hn tangent hw
    (hp_neg_product_log_error_bound_three n hnpos (w / (n : ℂ)) hnum hden hend)

end

end Li2Lean.B4.NegContour

#print axioms Li2Lean.B4.NegContour.hp_neg_bottom_side_log_bound_of_error
