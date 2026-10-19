/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B4.NegativeContourBottomBound

open Complex Real Set
open scoped BigOperators Interval

namespace Li2Lean.B4.NegContour

noncomputable section

/-!
Construction-bound adapters for the lower horizontal side in
`hp-tail.tex:307-355`.  The inputs below are the two actual right-endpoint
cell errors and the two endpoint errors evaluated at `w / n` on the concrete
`hpNegPhi` bottom side.  In particular, this file does not use the final
`.bottom` field of `HpNegBottomLeftEnvelope` as a premise.
-/

/-- Actual bottom-side cell and endpoint estimates needed by the product
logarithm decomposition.  The value `3` is the bound supplied by the
one-half quadrature adapter and is kept explicit so that a producer can prove
these fields directly from the v13 cells. -/
structure HpNegBottomCellEndpointInput where
  numerator_cell : ∀ n : ℕ, 30 ≤ n → ∀ w ∈ hpNegBottomSide n,
    HpRightErrorBound 3 n n (2 * n) (w / (n : ℂ))
  denominator_cell : ∀ n : ℕ, 30 ≤ n → ∀ w ∈ hpNegBottomSide n,
    HpRightErrorBound 3 n 0 n (w / (n : ℂ))
  endpoint : ∀ n : ℕ, 30 ≤ n → ∀ w ∈ hpNegBottomSide n,
    HpEndpointBound 3 n (w / (n : ℂ))

/-- The endpoint part of the concrete bottom-side estimate.  It uses only the
fixed imaginary height `-1/5` and the coordinate bounds of the actual
rectangle, so it is independent of the cell quadrature fields. -/
theorem hp_neg_bottom_endpoint_bound_three {n : ℕ} (hn : 30 ≤ n)
    {w : ℂ} (hw : w ∈ hpNegBottomSide n) :
    HpEndpointBound 3 n (w / (n : ℂ)) := by
  have hnpos : 0 < n := by omega
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  have hcoords := hp_neg_bottom_side_coordinates hw
  have hxi_re : (w / (n : ℂ)).re = w.re / (n : ℝ) := by
    simp [Complex.div_re, Complex.div_im]
    field_simp [hnR.ne']
  have hxi_im : (w / (n : ℂ)).im = -(1 / 5 : ℝ) := by
    simp [Complex.div_re, Complex.div_im]
    rw [hcoords.2.2]
    field_simp [hnR.ne']
  have hxi_re_lo : -(1 / 60 : ℝ) ≤ (w / (n : ℂ)).re := by
    rw [hxi_re]
    apply (le_div_iff₀ hnR).2
    have hnR30 : (30 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith [hcoords.1]
  have hxi_re_hi : (w / (n : ℂ)).re ≤ 61 / 60 := by
    rw [hxi_re]
    apply (div_le_iff₀ hnR).2
    have hnR30 : (30 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith [hcoords.2.1]
  have hxi_norm_lo : (1 / 5 : ℝ) ≤ ‖w / (n : ℂ)‖ := by
    have h := Complex.abs_im_le_norm (w / (n : ℂ))
    rw [hxi_im] at h
    simpa [abs_of_nonpos (by norm_num : -(1 / 5 : ℝ) ≤ 0)] using h
  have hxi_sq : ‖w / (n : ℂ)‖ ^ 2 =
      (w / (n : ℂ)).re ^ 2 + (w / (n : ℂ)).im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hxi_norm_hi : ‖w / (n : ℂ)‖ ≤ 2 := by
    have hresq : ‖w / (n : ℂ)‖ ^ 2 ≤ 4 := by
      rw [hxi_sq, hxi_im]
      have hreabs : |(w / (n : ℂ)).re| ≤ 61 / 60 := by
        exact (abs_le.mpr ⟨by linarith [hxi_re_lo], hxi_re_hi⟩)
      have hmul := mul_self_le_mul_self (abs_nonneg ((w / (n : ℂ)).re)) hreabs
      nlinarith [sq_abs ((w / (n : ℂ)).re)]
    nlinarith [norm_nonneg (w / (n : ℂ))]
  have ht_lo : (3 : ℝ) ≤ ((3 * n + 1 : ℕ) : ℝ) / (n : ℝ) := by
    apply (le_div_iff₀ hnR).2
    push_cast
    nlinarith
  have ht_hi : ((3 * n + 1 : ℕ) : ℝ) / (n : ℝ) ≤ 31 / 10 := by
    apply (div_le_iff₀ hnR).2
    push_cast
    have hnR30 : (30 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith
  have hnum_im : (w / (n : ℂ) -
      ((((3 * n + 1 : ℕ) : ℝ) / (n : ℝ)) : ℂ)).im = -(1 / 5 : ℝ) := by
    simp [Complex.sub_im, hxi_im]
  have hnum_dist_lo : (1 / 5 : ℝ) ≤ ‖w / (n : ℂ) -
      ((((3 * n + 1 : ℕ) : ℝ) / (n : ℝ)) : ℂ)‖ := by
    have h := Complex.abs_im_le_norm (w / (n : ℂ) -
      ((((3 * n + 1 : ℕ) : ℝ) / (n : ℝ)) : ℂ))
    rw [hnum_im] at h
    simpa [abs_of_nonpos (by norm_num : -(1 / 5 : ℝ) ≤ 0)] using h
  have hnum_re_lo : -(187 / 60 : ℝ) ≤
      (w / (n : ℂ) -
        ((((3 * n + 1 : ℕ) : ℝ) / (n : ℝ)) : ℂ)).re := by
    have heq : (w / (n : ℂ) -
        ((((3 * n + 1 : ℕ) : ℝ) / (n : ℝ)) : ℂ)).re =
        w.re / (n : ℝ) - ((3 * n + 1 : ℕ) : ℝ) / (n : ℝ) := by
      simp [Complex.sub_re, hxi_re]
    rw [heq]
    nlinarith [hxi_re_lo, ht_hi]
  have hnum_re_hi :
      (w / (n : ℂ) -
        ((((3 * n + 1 : ℕ) : ℝ) / (n : ℝ)) : ℂ)).re ≤ 61 / 60 := by
    have heq : (w / (n : ℂ) -
        ((((3 * n + 1 : ℕ) : ℝ) / (n : ℝ)) : ℂ)).re =
        w.re / (n : ℝ) - ((3 * n + 1 : ℕ) : ℝ) / (n : ℝ) := by
      simp [Complex.sub_re, hxi_re]
    rw [heq]
    nlinarith [hxi_re_hi, ht_lo]
  have hnum_dist_hi : ‖w / (n : ℂ) -
      ((((3 * n + 1 : ℕ) : ℝ) / (n : ℝ)) : ℂ)‖ ≤ 4 := by
    let z : ℂ := w / (n : ℂ) -
      ((((3 * n + 1 : ℕ) : ℝ) / (n : ℝ)) : ℂ)
    have hsq : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring
    have hresq : ‖w / (n : ℂ) -
        ((((3 * n + 1 : ℕ) : ℝ) / (n : ℝ)) : ℂ)‖ ^ 2 ≤ 16 := by
      change ‖z‖ ^ 2 ≤ 16
      rw [hsq]
      have hz_im : z.im = -(1 / 5 : ℝ) := by
        exact hnum_im
      rw [hz_im]
      have hreabs : |z.re| ≤ 187 / 60 := by
        exact abs_le.mpr ⟨hnum_re_lo, by linarith [hnum_re_hi]⟩
      have hmul := mul_self_le_mul_self (abs_nonneg z.re) hreabs
      have hsqre : z.re ^ 2 ≤ (187 / 60 : ℝ) ^ 2 := by
        nlinarith [sq_abs z.re]
      nlinarith [sq_abs z.re, hsqre]
    nlinarith [norm_nonneg (w / (n : ℂ) -
      ((((3 * n + 1 : ℕ) : ℝ) / (n : ℝ)) : ℂ))]
  have hlogn : 0 ≤ Real.log ((n + 1 : ℕ) : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ n + 1 by omega)
  have hlog5 : Real.log (5 : ℝ) ≤ 3 := by
    have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
      calc
        Real.log 2 ≤ 2 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
        _ = 1 := by norm_num
    have h58 : (5 : ℝ) ≤ 8 := by norm_num
    have hlog58 := Real.log_le_log (by norm_num : (0 : ℝ) < 5) h58
    have hlog8 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 * 2 * 2 by norm_num]
      rw [Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num)]
      ring
    rw [hlog8] at hlog58
    nlinarith
  have hlog4 : Real.log (4 : ℝ) ≤ 2 := by
    have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
      calc
        Real.log 2 ≤ 2 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
        _ = 1 := by norm_num
    have hlog4eq : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
      ring
    rw [hlog4eq]
    nlinarith
  have hnum_abs : |Real.log ‖w / (n : ℂ) -
      ((((3 * n + 1 : ℕ) : ℝ) / (n : ℝ)) : ℂ)‖| ≤
      3 * (1 + Real.log ((n + 1 : ℕ) : ℝ)) := by
    have hpos : 0 < ‖w / (n : ℂ) -
      ((((3 * n + 1 : ℕ) : ℝ) / (n : ℝ)) : ℂ)‖ :=
        lt_of_lt_of_le (by norm_num) hnum_dist_lo
    have hloglo : -3 ≤ Real.log ‖w / (n : ℂ) -
        ((((3 * n + 1 : ℕ) : ℝ) / (n : ℝ)) : ℂ)‖ := by
      have hloglower := Real.log_le_log
        (by norm_num : (0 : ℝ) < 1 / 5) hnum_dist_lo
      have hlog15 : Real.log (1 / 5 : ℝ) = -Real.log 5 := by
        rw [show (1 / 5 : ℝ) = (5 : ℝ)⁻¹ by norm_num, Real.log_inv]
      rw [hlog15] at hloglower
      linarith [hlog5]
    have hloghi : Real.log ‖w / (n : ℂ) -
        ((((3 * n + 1 : ℕ) : ℝ) / (n : ℝ)) : ℂ)‖ ≤ 2 := by
      have h := Real.log_le_log hpos hnum_dist_hi
      linarith [hlog4]
    rw [abs_le]
    have hrhs : (3 : ℝ) ≤ 3 * (1 + Real.log ((n + 1 : ℕ) : ℝ)) := by
      nlinarith [hlogn]
    constructor <;> linarith
  have hden_abs : |Real.log ‖w / (n : ℂ)‖| ≤
      3 * (1 + Real.log ((n + 1 : ℕ) : ℝ)) := by
    have hpos : 0 < ‖w / (n : ℂ)‖ := lt_of_lt_of_le (by norm_num) hxi_norm_lo
    have hloghi : Real.log ‖w / (n : ℂ)‖ ≤ 2 := by
      have h := Real.log_le_sub_one_of_pos hpos
      linarith [hxi_norm_hi]
    have hloglo : -3 ≤ Real.log ‖w / (n : ℂ)‖ := by
      have hloglower := Real.log_le_log
        (by norm_num : (0 : ℝ) < 1 / 5) hxi_norm_lo
      have hlog15 : Real.log (1 / 5 : ℝ) = -Real.log 5 := by
        rw [show (1 / 5 : ℝ) = (5 : ℝ)⁻¹ by norm_num, Real.log_inv]
      rw [hlog15] at hloglower
      linarith [hlog5]
    rw [abs_le]
    have hrhs : (3 : ℝ) ≤ 3 * (1 + Real.log ((n + 1 : ℕ) : ℝ)) := by
      nlinarith [hlogn]
    constructor <;> linarith
  unfold HpEndpointBound hpNumeratorEndpoint hpDenominatorEndpoint hpLog
  constructor
  · convert hnum_abs using 1 <;> norm_num <;> push_cast
  · simpa [sub_zero] using hden_abs

/-- The actual product-log error on the bottom side, obtained from the
three cell/endpoint estimates and the v13 linear combination
`U + V - 2 W - 2 X` (`hp-tail.tex:307-316`). -/
theorem hp_neg_bottom_product_log_error_bound_of_cells
    (input : HpNegBottomCellEndpointInput)
    {n : ℕ} (hn : 30 ≤ n) {w : ℂ} (hw : w ∈ hpNegBottomSide n) :
    |hpProductLogError n (w / (n : ℂ))| ≤
      18 * (1 + Real.log ((n + 1 : ℕ) : ℝ)) := by
  have hnpos : 0 < n := by omega
  exact hp_neg_product_log_error_bound_three n hnpos
    (w / (n : ℂ))
    (input.numerator_cell n hn w hw)
    (input.denominator_cell n hn w hw)
    (input.endpoint n hn w hw)

/-- The complete bottom-side boundary estimate from the same concrete cell
and endpoint producer.  The tangent certificate is the rational-height
certificate for `hp-tail.tex:343-355`; the phase remains in
`hpNegBoundaryLog` via `hp_neg_bottom_side_log_bound_of_error`. -/
theorem hp_neg_bottom_side_log_bound_of_cells
    {q : ℕ} (hq : q = 8 ∨ q = 9 ∨ q = 10)
    (tangent : HpNegBottomTangentCertificate q)
    (input : HpNegBottomCellEndpointInput)
    {n : ℕ} (hn : 30 ≤ n) {w : ℂ} (hw : w ∈ hpNegBottomSide n) :
    hpNegBoundaryLog q n w ≤
      (n : ℝ) * (hpNegT q : ℝ) +
        18 * (1 + Real.log ((n + 1 : ℕ) : ℝ)) := by
  exact hp_neg_bottom_side_log_bound_of_error hq hn tangent hw
    (hp_neg_bottom_product_log_error_bound_of_cells input hn hw)

end

end Li2Lean.B4.NegContour

#print axioms Li2Lean.B4.NegContour.hp_neg_bottom_product_log_error_bound_of_cells
#print axioms Li2Lean.B4.NegContour.hp_neg_bottom_side_log_bound_of_cells
