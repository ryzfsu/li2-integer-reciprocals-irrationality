/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B4.NegativeContourRight
import Li2Lean.B4.NegativeContourRightProduct
import Li2Lean.B4.NegativeContourRightDenominator
import Li2Lean.P0.ConfigQuadrature
import Li2Lean.P0.ConfigSelfStirling
import Li2Lean.P0.ConfigLogTaylor

open Complex Real Set
open scoped BigOperators Interval
open Li2Lean.P0.ConfigLogTaylor

namespace Li2Lean.B4.NegContour

noncomputable section

/-!
Right-edge logarithmic bookkeeping for the exceptional rectangle in
v13 `hp-tail.tex:319-337`.

The geometric product is supplied by `NegativeContourRightSide` and
`NegativeContourRightProduct`.  This file records only elementary logarithmic
consequences and the named analytic envelope consumed by the final contour
glue.  In particular, the envelope is an explicit hypothesis: no contour
estimate is hidden in this module.
-/

/-! ### Factorial bounds used by the denominator estimate -/

/-- The elementary lower factorial estimate used in the v13 right-edge
product comparison (`hp-tail.tex:319-337`). -/
theorem hp_neg_log_factorial_lower (n : ℕ) :
    (n : ℝ) * Real.log n - n ≤ Real.log (n.factorial : ℝ) := by
  exact Li2Lean.P0.Config.quad_log_factorial_lower n

/-- A Stirling upper envelope for the factorial term in the same discrete
right-edge comparison.  The theorem is reused from the 1/2 release's
`Config.SelfStirling` module; it is only a bookkeeping lemma here. -/
theorem hp_neg_log_factorial_upper (n : ℕ) (hn : 0 < n) :
    Real.log (n.factorial : ℝ) ≤
      (n : ℝ) * Real.log n - n + Real.log n / 2 +
        Real.log (2 * Real.pi) / 2 + 1 / (12 * n) := by
  exact Li2Lean.P0.Config.SelfCells.log_factorial_stirling_upper n hn

/-- The factorial denominator is strictly positive, so its logarithm is
defined without an additional side condition.  This is the denominator
nonvanishing fact in v13 `hp-tail.tex:319-337`. -/
theorem hp_neg_factorial_cast_pos (n : ℕ) :
    0 < (n.factorial : ℝ) := by
  exact_mod_cast Nat.factorial_pos n

/-- The square-over-four denominator allowance is nonnegative. -/
theorem hp_neg_factorial_square_div_four_nonneg (n : ℕ) :
    0 ≤ ((n.factorial : ℝ) ^ 2) / 4 := by
  positivity

/-! ### Finite product cardinality and the single-factor logarithm -/

/-- There are `2n+1` numerator factors in the right-edge product of
v13 `hp-tail.tex:319-337`. -/
theorem hp_neg_right_numerator_card (n : ℕ) :
    ((Finset.Icc (n + 1) (3 * n + 1)).card : ℝ) =
      2 * (n : ℝ) + 1 := by
  rw [Nat.card_Icc]
  have hnat : 3 * n + 1 + 1 - (n + 1) = 2 * n + 1 := by
    omega
  rw [hnat]
  norm_num

/-- The coarse factor `((11/5)n+1)` has a logarithm bounded by one linear
`log(n+1)` term and a fixed constant.  This is the algebraic envelope used
after the discrete product in v13 `hp-tail.tex:319-337`. -/
theorem hp_neg_right_upper_log_le (n : ℕ) :
    Real.log (hpNegRightUpper n) ≤
      Real.log (16 / 5 : ℝ) + Real.log ((n + 1 : ℕ) : ℝ) := by
  have hpos : 0 < hpNegRightUpper n := by
    dsimp [hpNegRightUpper]
    positivity
  have hn1 : 0 < ((n + 1 : ℕ) : ℝ) := by
    positivity
  have hprod : hpNegRightUpper n ≤
      (16 / 5 : ℝ) * ((n + 1 : ℕ) : ℝ) := by
    dsimp [hpNegRightUpper]
    push_cast
    nlinarith
  have hlog := Real.log_le_log hpos hprod
  rw [Real.log_mul (by norm_num) hn1.ne'] at hlog
  exact hlog

/-- The corresponding cardinal-weighted logarithm bound, leaving the
factorial and phase terms to the caller. -/
theorem hp_neg_right_card_mul_upper_log_le (n : ℕ) :
    (2 * (n : ℝ) + 1) * Real.log (hpNegRightUpper n) ≤
      (2 * (n : ℝ) + 1) *
        (Real.log (16 / 5 : ℝ) + Real.log ((n + 1 : ℕ) : ℝ)) := by
  have hcard : 0 ≤ 2 * (n : ℝ) + 1 := by positivity
  exact mul_le_mul_of_nonneg_left (hp_neg_right_upper_log_le n) hcard

private theorem hp_neg_log_eight_gt_two :
    (2 : ℝ) < Real.log (8 : ℝ) := by
  have hrat : (2 : ℚ) < logPolynomial (8 : ℚ) 20 := by
    norm_num [logPolynomial, logCoordinate]
  have hcast : (2 : ℝ) < (logPolynomial (8 : ℚ) 20 : ℝ) := by
    exact_mod_cast hrat
  exact lt_of_lt_of_le hcast
    (logPolynomial_le_log (q := (8 : ℚ)) (by norm_num) 20)

private theorem hp_neg_log_16_5_lt_six_fifths :
    Real.log (16 / 5 : ℝ) < (6 / 5 : ℝ) := by
  have hrem := (abs_le.mp
    (logPolynomial_remainder (q := (16 / 5 : ℚ)) (by norm_num) 4)).2
  have hcast :
      (logPolynomial (16 / 5 : ℚ) 4 : ℝ) +
        (logRemainder (16 / 5 : ℚ) 4 : ℝ) < (6 / 5 : ℝ) := by
    norm_num [logPolynomial, logRemainder, logCoordinate]
  have hupper : Real.log (16 / 5 : ℝ) ≤
      (logPolynomial (16 / 5 : ℚ) 4 : ℝ) +
        (logRemainder (16 / 5 : ℚ) 4 : ℝ) := by
    linarith
  exact lt_of_le_of_lt hupper hcast

private theorem hp_neg_right_slope_le_t {q : ℕ}
    (hq : q = 8 ∨ q = 9 ∨ q = 10) :
    2 * Real.log (16 / 5 : ℝ) + 2 - Real.log (q : ℝ) +
      Real.pi / 5 ≤ (hpNegT q : ℝ) := by
  have hq8 : (8 : ℝ) ≤ (q : ℝ) := by
    rcases hq with h | h | h <;> subst q <;> norm_num
  have hlogq : (2 : ℝ) < Real.log (q : ℝ) := by
    have hmono := Real.log_le_log (by norm_num : (0 : ℝ) < 8) hq8
    exact lt_of_lt_of_le hp_neg_log_eight_gt_two hmono
  have hpi : Real.pi / 5 ≤ (4 / 5 : ℝ) := by
    have h := Real.pi_lt_four
    nlinarith
  have ht : (16 / 5 : ℝ) ≤ (hpNegT q : ℝ) := by
    rcases hq with h | h | h <;> subst q <;>
      norm_num [hpNegT, hpNegT8, hpNegT9, hpNegT10]
  have hlog := hp_neg_log_16_5_lt_six_fifths
  nlinarith

private theorem hp_neg_right_numerator_factor_pos {n r : ℕ} {w : ℂ}
    (hr : r ∈ Finset.Icc (n + 1) (3 * n + 1))
    (hw : w ∈ hpNegRightSide n) :
    0 < ‖w - (r : ℂ)‖ := by
  have hnr : (n : ℝ) + 1 ≤ (r : ℝ) := by
    exact_mod_cast (Finset.mem_Icc.mp hr).1
  have hre := hp_neg_right_re_eq n hw
  have hreal : (1 / 2 : ℝ) ≤ |(w - (r : ℂ)).re| := by
    have hrre : ((r : ℂ).re) = (r : ℝ) := by norm_num
    rw [Complex.sub_re, hrre, hre]
    have hnonpos : (n : ℝ) + 1 / 2 - (r : ℝ) ≤ 0 := by linarith
    rw [abs_of_nonpos hnonpos]
    linarith
  exact lt_of_lt_of_le (by norm_num) (hreal.trans (Complex.abs_re_le_norm _))

private theorem hp_neg_right_phi_norm_pos {n : ℕ} {w : ℂ}
    (hw : w ∈ hpNegRightSide n) :
    0 < ‖hpNegPhi n w‖ := by
  have hnum :
      0 < ∏ r ∈ Finset.Icc (n + 1) (3 * n + 1), ‖w - (r : ℂ)‖ := by
    apply Finset.prod_pos
    intro r hr
    exact hp_neg_right_numerator_factor_pos hr hw
  have hden :
      0 < ∏ j ∈ Finset.range (n + 1), ‖w - (j : ℂ)‖ ^ 2 := by
    have hfactorial :
        0 < ((Nat.factorial n : ℝ) ^ 2) / 4 := by positivity
    exact lt_of_lt_of_le hfactorial
      (hp_neg_right_denominator_factorial_lower hw)
  rw [hpNegPhi, Complex.norm_div, Complex.norm_prod, Complex.norm_prod]
  simp only [norm_pow]
  exact div_pos hnum hden

private theorem hp_neg_right_boundary_log_eq {q n : ℕ} {w : ℂ}
    (hphi : hpNegPhi n w ≠ 0) :
    hpNegBoundaryLog q n w =
      Real.log ‖hpNegPhi n w‖ +
        (-Real.log (q : ℝ) * w.re - Real.pi * w.im) := by
  unfold hpNegBoundaryLog
  rw [norm_mul]
  have hphi_norm : ‖hpNegPhi n w‖ ≠ 0 := norm_ne_zero_iff.mpr hphi
  have hexp : ‖Complex.exp (hpNegLambda q * w)‖ ≠ 0 := by
    rw [hpNegPhaseNorm]
    exact ne_of_gt (Real.exp_pos _)
  rw [Real.log_mul hphi_norm hexp, hpNegPhaseNorm, Real.log_exp]

private theorem hp_neg_log_succ_sub_le {n : ℕ} (hn : 0 < n) :
    Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ) ≤ 1 / (n : ℝ) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hratio_pos : 0 < ((n + 1 : ℕ) : ℝ) / (n : ℝ) := by positivity
  have hlog := Real.log_le_sub_one_of_pos hratio_pos
  have hlogdiv :
      Real.log (((n + 1 : ℕ) : ℝ) / (n : ℝ)) =
        Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ) := by
    rw [Real.log_div (by positivity) hnR.ne']
  rw [hlogdiv] at hlog
  have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by
    norm_num [Nat.cast_add]
  rw [hcast] at hlog ⊢
  have hratio : ((n : ℝ) + 1) / (n : ℝ) - 1 = 1 / (n : ℝ) := by
    field_simp
    ring
  rw [hratio] at hlog
  exact hlog

private theorem hp_neg_right_log_polynomial_error {n : ℕ} (hn : 0 < n) :
    (2 * (n : ℝ) + 1) * Real.log ((n + 1 : ℕ) : ℝ) -
        2 * (n : ℝ) * Real.log (n : ℝ) ≤
      Real.log ((n + 1 : ℕ) : ℝ) + 2 := by
  have hdiff := hp_neg_log_succ_sub_le hn
  have hmul := mul_le_mul_of_nonneg_left hdiff
    (by positivity : 0 ≤ 2 * (n : ℝ))
  have htwo : 2 * (n : ℝ) * (1 / (n : ℝ)) = 2 := by
    field_simp
  nlinarith

private theorem hp_neg_right_log_norm_le {n : ℕ} {w : ℂ}
    (hw : w ∈ hpNegRightSide n) :
    Real.log ‖hpNegPhi n w‖ ≤
      (2 * (n : ℝ) + 1) *
          (Real.log (16 / 5 : ℝ) + Real.log ((n + 1 : ℕ) : ℝ)) -
        2 * ((n : ℝ) * Real.log (n : ℝ) - (n : ℝ)) +
          Real.log (4 : ℝ) := by
  have hphi_pos := hp_neg_right_phi_norm_pos hw
  have hden_pos : 0 < ((Nat.factorial n : ℝ) ^ 2) / 4 := by positivity
  have hnum_factor_pos : 0 < hpNegRightUpper n := by
    dsimp [hpNegRightUpper]
    positivity
  have hnum_pos :
      0 < ∏ r ∈ Finset.Icc (n + 1) (3 * n + 1), hpNegRightUpper n := by
    apply Finset.prod_pos
    intro r hr
    exact hnum_factor_pos
  have hnorm_bound :
      ‖hpNegPhi n w‖ ≤
        (∏ r ∈ Finset.Icc (n + 1) (3 * n + 1), hpNegRightUpper n) /
          (((Nat.factorial n : ℝ) ^ 2) / 4) := by
    exact hp_neg_right_norm_phi_le_of_denominator hw hden_pos
      (hp_neg_right_denominator_factorial_lower hw)
  have hlog_num :
      Real.log (∏ r ∈ Finset.Icc (n + 1) (3 * n + 1), hpNegRightUpper n) =
        (2 * (n : ℝ) + 1) * Real.log (hpNegRightUpper n) := by
    calc
      _ = Real.log (hpNegRightUpper n ^
          (Finset.Icc (n + 1) (3 * n + 1)).card) := by
        rw [Finset.prod_const]
      _ = ((Finset.Icc (n + 1) (3 * n + 1)).card : ℝ) *
          Real.log (hpNegRightUpper n) := by
        rw [Real.log_pow]
      _ = (2 * (n : ℝ) + 1) * Real.log (hpNegRightUpper n) := by
        rw [hp_neg_right_numerator_card]
  have hlog_den :
      Real.log (((Nat.factorial n : ℝ) ^ 2) / 4) =
        2 * Real.log (Nat.factorial n : ℝ) - Real.log (4 : ℝ) := by
    rw [Real.log_div (by positivity) (by norm_num), pow_two,
      Real.log_mul (by positivity) (by positivity)]
    ring
  have hlog_ratio := Real.log_le_log hphi_pos hnorm_bound
  have hlog_norm_upper :
      Real.log ‖hpNegPhi n w‖ ≤
        (2 * (n : ℝ) + 1) * Real.log (hpNegRightUpper n) -
          2 * Real.log (Nat.factorial n : ℝ) + Real.log (4 : ℝ) := by
    calc
      Real.log ‖hpNegPhi n w‖ ≤
          Real.log ((∏ r ∈ Finset.Icc (n + 1) (3 * n + 1),
            hpNegRightUpper n) / (((Nat.factorial n : ℝ) ^ 2) / 4)) :=
        hlog_ratio
      _ = _ := by
        rw [Real.log_div hnum_pos.ne' hden_pos.ne', hlog_num, hlog_den]
        ring
  have hcard_upper := hp_neg_right_card_mul_upper_log_le n
  have hfactorial_lower := hp_neg_log_factorial_lower n
  have hfactorial_term :
      -2 * Real.log (Nat.factorial n : ℝ) ≤
        -2 * ((n : ℝ) * Real.log (n : ℝ) - (n : ℝ)) :=
    mul_le_mul_of_nonpos_left hfactorial_lower (by norm_num)
  calc
    Real.log ‖hpNegPhi n w‖ ≤
        (2 * (n : ℝ) + 1) * Real.log (hpNegRightUpper n) -
          2 * Real.log (Nat.factorial n : ℝ) + Real.log (4 : ℝ) :=
      hlog_norm_upper
    _ ≤ (2 * (n : ℝ) + 1) *
          (Real.log (16 / 5 : ℝ) + Real.log ((n + 1 : ℕ) : ℝ)) -
        2 * ((n : ℝ) * Real.log (n : ℝ) - (n : ℝ)) +
          Real.log (4 : ℝ) := by
      nlinarith

private theorem hp_neg_right_phase_log_le {q n : ℕ} {w : ℂ}
    (hq : q = 8 ∨ q = 9 ∨ q = 10)
    (hw : w ∈ hpNegRightSide n) :
    -Real.log (q : ℝ) * w.re - Real.pi * w.im ≤
      (n : ℝ) * (-Real.log (q : ℝ) + Real.pi / 5) := by
  have hq1 : 1 ≤ q := by
    rcases hq with h | h | h <;> omega
  have hphase := hp_neg_right_phase_exponent_le hq1 hw
  have hlogq : 0 ≤ Real.log (q : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hq1)
  nlinarith

private theorem hp_neg_right_slope_scaled_le {q n : ℕ}
    (hq : q = 8 ∨ q = 9 ∨ q = 10) :
    (n : ℝ) *
        (2 * Real.log (16 / 5 : ℝ) + 2 - Real.log (q : ℝ) +
          Real.pi / 5) ≤
      (n : ℝ) * (hpNegT q : ℝ) := by
  exact mul_le_mul_of_nonneg_left (hp_neg_right_slope_le_t hq) (by positivity)

private theorem hp_neg_right_logarithmic_bound_core {q n : ℕ} {w : ℂ}
    (hq : q = 8 ∨ q = 9 ∨ q = 10)
    (hn : 30 ≤ n) (hw : w ∈ hpNegRightSide n) :
    hpNegBoundaryLog q n w ≤
      (n : ℝ) * (hpNegT q : ℝ) +
        (18 : ℝ) * (1 + Real.log ((n + 1 : ℕ) : ℝ)) := by
  have hnpos : 0 < n := by omega
  have hn1_ge : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ n + 1 by omega)
  have hlog_n1_nonneg : 0 ≤ Real.log ((n + 1 : ℕ) : ℝ) :=
    Real.log_nonneg hn1_ge
  have hlog_16_5 := hp_neg_log_16_5_lt_six_fifths.le
  have hlog_four : Real.log (4 : ℝ) ≤ 3 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    nlinarith
  have hconstant :
      Real.log ((n + 1 : ℕ) : ℝ) + 2 + Real.log (16 / 5 : ℝ) +
          Real.log (4 : ℝ) ≤
        18 * (1 + Real.log ((n + 1 : ℕ) : ℝ)) := by
    nlinarith
  have hphi : hpNegPhi n w ≠ 0 := by
    intro hzero
    have hpos := hp_neg_right_phi_norm_pos hw
    rw [hzero] at hpos
    norm_num at hpos
  have hnorm := hp_neg_right_log_norm_le hw
  have hphase := hp_neg_right_phase_log_le hq hw
  have herr := hp_neg_right_log_polynomial_error hnpos
  have htotal :
      Real.log ‖hpNegPhi n w‖ +
          (-Real.log (q : ℝ) * w.re - Real.pi * w.im) ≤
        (n : ℝ) *
            (2 * Real.log (16 / 5 : ℝ) + 2 - Real.log (q : ℝ) +
              Real.pi / 5) +
          Real.log ((n + 1 : ℕ) : ℝ) + 2 + Real.log (16 / 5 : ℝ) +
            Real.log (4 : ℝ) := by
    nlinarith [hnorm, hphase, herr]
  rw [hp_neg_right_boundary_log_eq hphi]
  have hslope := hp_neg_right_slope_scaled_le (n := n) hq
  calc
    Real.log ‖hpNegPhi n w‖ +
        (-Real.log (q : ℝ) * w.re - Real.pi * w.im) ≤
      (n : ℝ) *
          (2 * Real.log (16 / 5 : ℝ) + 2 - Real.log (q : ℝ) +
            Real.pi / 5) +
        (Real.log ((n + 1 : ℕ) : ℝ) + 2 + Real.log (16 / 5 : ℝ) +
          Real.log (4 : ℝ)) := by
      nlinarith [htotal]
    _ ≤ (n : ℝ) * (hpNegT q : ℝ) +
        18 * (1 + Real.log ((n + 1 : ℕ) : ℝ)) :=
      add_le_add hslope hconstant

/-! ### Explicit analytic input for the final right-edge rate -/

/-- The unresolved logarithmic estimate for the right side of the rectangle.
Its shape is exactly the boundary inequality used by the v13 contour passage
`hp-tail.tex:319-337`; the definition is specialized to `hpNegBoundaryLog`,
whose `hpBpoly` sequence is fixed in `NegativeContourBoundary`. -/
def HpNegRightLogarithmicEnvelope (q : ℕ) : Prop :=
  (q = 8 ∨ q = 9 ∨ q = 10) ∧
    ∀ n : ℕ, 30 ≤ n → ∀ w ∈ hpNegRightSide n,
      hpNegBoundaryLog q n w ≤
        (n : ℝ) * (hpNegT q : ℝ) +
          (18 : ℝ) * (1 + Real.log ((n + 1 : ℕ) : ℝ))

/-- The explicit right-edge estimate for the actual finite product, matching
the right-side comparison in v13 `hp-tail.tex:319-337`. -/
theorem hp_neg_right_logarithmic_bound
    {q n : ℕ} (hq : q = 8 ∨ q = 9 ∨ q = 10)
    (hn : 30 ≤ n) {w : ℂ} (hw : w ∈ hpNegRightSide n) :
    hpNegBoundaryLog q n w ≤
      (n : ℝ) * (hpNegT q : ℝ) +
        (18 : ℝ) * (1 + Real.log ((n + 1 : ℕ) : ℝ)) :=
  hp_neg_right_logarithmic_bound_core hq hn hw

/-- The logarithmic envelope obtained from the proved product estimate. -/
theorem hp_neg_right_logarithmic_envelope
    {q : ℕ} (hq : q = 8 ∨ q = 9 ∨ q = 10) :
    HpNegRightLogarithmicEnvelope q := by
  refine ⟨hq, ?_⟩
  intro n hn w hw
  exact hp_neg_right_logarithmic_bound hq hn hw

/-- A named right-edge rate certificate.  The proof of this field is the
rectangle boundary analysis from v13 `hp-tail.tex:319-337`; keeping it as a
field makes the remaining contour obligation explicit and prevents an
arbitrary sequence from entering the typed interface. -/
structure HpNegRightLogRateCertificate (q : ℕ) where
  q_spec : q = 8 ∨ q = 9 ∨ q = 10
  n0 : ℕ
  n0_spec : 30 ≤ n0
  exponent : ℕ
  exponent_spec : exponent = 18
  logarithmic : ∀ n : ℕ, n0 ≤ n → ∀ w ∈ hpNegRightSide n,
    hpNegBoundaryLog q n w ≤
      (n : ℝ) * (hpNegT q : ℝ) +
        (exponent : ℝ) * (1 + Real.log ((n + 1 : ℕ) : ℝ))

/-- Package an envelope proved by the contour analysis at the fixed threshold
`n=30`. -/
def hp_neg_right_log_rate_certificate_of_envelope {q : ℕ}
    (h : HpNegRightLogarithmicEnvelope q) :
    HpNegRightLogRateCertificate q := by
  refine
    { q_spec := h.1
      n0 := 30
      n0_spec := by norm_num
      exponent := 18
      exponent_spec := by rfl
      logarithmic := ?_ }
  intro n hn w hw
  simpa using h.2 n (by exact hn) w hw

/-- Construct the named logarithmic rate certificate from the proved
right-edge product estimate. -/
def hp_neg_right_log_rate_certificate {q : ℕ}
    (hq : q = 8 ∨ q = 9 ∨ q = 10) :
    HpNegRightLogRateCertificate q :=
  hp_neg_right_log_rate_certificate_of_envelope
    (hp_neg_right_logarithmic_envelope hq)

/-- Fill all three right-edge fields using the actual product and its proved
logarithmic estimate. -/
theorem hp_neg_right_factor_certificate {q : ℕ}
    (hq : q = 8 ∨ q = 9 ∨ q = 10) : HpNegRightFactorCertificate q := by
  refine
    { q_spec := hq
      numerator := ?_
      denominator := ?_
      logarithmic := ?_ }
  · intro n hn w hw r hr
    simpa [hpNegRightUpper] using hp_neg_right_factor_bound hr hw
  · intro n hn w hw
    exact hp_neg_right_denominator_factorial_lower hw
  · intro n hn w hw
    exact hp_neg_right_logarithmic_bound hq hn hw

/-- Extract the final right-edge logarithmic inequality from the named
certificate. -/
theorem hp_neg_right_log_rate_bound
    {q : ℕ} (cert : HpNegRightLogRateCertificate q)
    {n : ℕ} (hn : cert.n0 ≤ n) {w : ℂ}
    (hw : w ∈ hpNegRightSide n) :
    hpNegBoundaryLog q n w ≤
      (n : ℝ) * (hpNegT q : ℝ) +
        (cert.exponent : ℝ) * (1 + Real.log ((n + 1 : ℕ) : ℝ)) := by
  exact cert.logarithmic n hn w hw

end

end Li2Lean.B4.NegContour

#print axioms Li2Lean.B4.NegContour.hp_neg_log_factorial_lower
#print axioms Li2Lean.B4.NegContour.hp_neg_log_factorial_upper
#print axioms Li2Lean.B4.NegContour.hp_neg_right_numerator_card
#print axioms Li2Lean.B4.NegContour.hp_neg_right_upper_log_le
#print axioms Li2Lean.B4.NegContour.hp_neg_right_card_mul_upper_log_le
#print axioms Li2Lean.B4.NegContour.hp_neg_right_logarithmic_bound
#print axioms Li2Lean.B4.NegContour.hp_neg_right_logarithmic_envelope
#print axioms Li2Lean.B4.NegContour.hp_neg_right_log_rate_certificate_of_envelope
#print axioms Li2Lean.B4.NegContour.hp_neg_right_log_rate_certificate
#print axioms Li2Lean.B4.NegContour.hp_neg_right_factor_certificate
#print axioms Li2Lean.B4.NegContour.hp_neg_right_log_rate_bound
