/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

H4 leaf L4: exact rational lower bounds for `log q`, q = 2..7, and the strict
rate hint consumed by `qv13PrimeSumRate_of_budget`.

This release module is independent of
the profile construction: the hint is stated for any real `I` equal to the
exact profile integral `v13H4IntegralQ`.

Numerics (the finite-data checks, master slab data):
  margin vTau q - (I + 13/160 - (53/48) * Lq), Lq = rational lower bound used here
  q=2 6.047e-6, q=3 7.104e-6, q=4 6.059e-6, q=5 3.730e-6, q=6 7.116e-6, q=7 5.147e-6.
The bounds below cost at most 1.2e-8 of margin (q = 7).

Paper source: `v-arithmetic.tex:353-421`.
-/

import Mathlib.Analysis.Complex.ExponentialBounds   -- note: module path (has Real.log_two_gt_d9 …)
import Mathlib.Analysis.SpecialFunctions.Log.Deriv  -- Real.hasSum_log_one_add_inv
import Li2Lean.B3.ProducerInterfaces                -- vTau, SignedVBaseRange

namespace Li2Lean.B3

noncomputable section

open scoped BigOperators

/-- The exact integral of `v13H4Profile` (412 slab pieces on `[1/40, 5/4]` plus the
two outer pieces on `[5/4, 11/4)`).  Recomputed from the committed shards
`H4SlabData00..08` (master `b099d190`): slab part
`93557483955345022282648630919852486249295731657 / 26020759561732371877438650035601516684254668800`,
outer part `45/32`. -/
def v13H4IntegralQ : ℚ :=
  130149177089031170235296732532417119086528859657 /
    26020759561732371877438650035601516684254668800

/-! ## Rational lower bounds for `log q` -/

theorem h4_log_two_lower : (6931471803 / 10000000000 : ℝ) < Real.log 2 :=
  lt_of_eq_of_lt (by norm_num) Real.log_two_gt_d9

theorem h4_log_three_lower : (10986122885 / 10000000000 : ℝ) < Real.log 3 :=
  lt_of_eq_of_lt (by norm_num) Real.log_three_gt_d9

theorem h4_log_five_lower : (16094379123 / 10000000000 : ℝ) < Real.log 5 :=
  lt_of_eq_of_lt (by norm_num) Real.log_five_gt_d9

theorem h4_log_four_eq : Real.log 4 = 2 * Real.log 2 := by
  -- `Real.log_four_eq` exists in Mathlib (ExponentialBounds); alternative kept explicit.
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  norm_num

theorem h4_log_six_eq : Real.log 6 = Real.log 2 + Real.log 3 := by
  rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]

/-- Three terms of the atanh series for `log (1 + 1/6) = log (7/6)`.
Partial sum `858526/5569395 = 0.1541506752…`; true value `0.1541506798…`. -/
theorem h4_log_seven_sixths_lower :
    (15415067 / 100000000 : ℝ) ≤ Real.log (1 + (6 : ℝ)⁻¹) := by
  have hsum := Real.hasSum_log_one_add_inv (a := (6 : ℝ)) (by norm_num)
  have hnn : ∀ k : ℕ, 0 ≤ (2 : ℝ) * (1 / (2 * (k : ℝ) + 1)) *
      (1 / (2 * (6 : ℝ) + 1)) ^ (2 * k + 1) := by
    intro k
    positivity
  have hle := sum_le_hasSum (Finset.range 3) (fun k _ => hnn k) hsum
  have hval : (15415067 / 100000000 : ℝ) ≤
      ∑ k ∈ Finset.range 3, (2 : ℝ) * (1 / (2 * (k : ℝ) + 1)) *
        (1 / (2 * (6 : ℝ) + 1)) ^ (2 * k + 1) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
  exact hval.trans hle

theorem h4_log_seven_eq :
    Real.log 7 = Real.log 2 + Real.log 3 + Real.log (1 + (6 : ℝ)⁻¹) := by
  have h7 : (7 : ℝ) = 2 * 3 * (1 + (6 : ℝ)⁻¹) := by norm_num
  rw [h7, Real.log_mul (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num)]

theorem h4_log_seven_lower :
    (6931471803 / 10000000000 + 10986122885 / 10000000000 + 15415067 / 100000000 : ℝ) <
      Real.log 7 := by
  rw [h4_log_seven_eq]
  have h2 := h4_log_two_lower
  have h3 := h4_log_three_lower
  have h76 := h4_log_seven_sixths_lower
  linarith

/-! ## The strict rate hint -/

/-- L4 main statement, profile-agnostic: if `I` is the exact profile integral,
then `I + 13/160 - (53/48) log q < vTau q` for every base `q ∈ [2, 7]`.
This is the `hint` argument of `qv13PrimeSumRate_of_budget` with
`c = (53/48) * Real.log q`. -/
theorem v13H4_rate_hint_of_integral {q : ℕ} (hq : SignedVBaseRange q)
    {I : ℝ} (hI : I = ((v13H4IntegralQ : ℚ) : ℝ)) :
    I + 13 / 160 - (53 / 48) * Real.log (q : ℝ) < vTau q := by
  subst hI
  rcases hq with ⟨hq2, hq7⟩
  -- note: if `norm_num [v13H4IntegralQ]` does not close a `key` goal, use
  --   `simp only [v13H4IntegralQ]; push_cast; norm_num`.
  -- note: if the cast rewrite `((k : ℕ) : ℝ) = k` fails to match after
  --   `interval_cases`, replace it by `simp only [Nat.cast_ofNat]`.
  interval_cases q
  · -- q = 2: slack 5.48e-6 on log 2
    have hv : vTau 2 = 431765 / 100000 := by norm_num [vTau]
    have hL := h4_log_two_lower
    have key : ((v13H4IntegralQ : ℚ) : ℝ) + 13 / 160 -
        53 / 48 * (6931471803 / 10000000000 : ℝ) < 431765 / 100000 := by
      norm_num [v13H4IntegralQ]
    rw [hv, show ((2 : ℕ) : ℝ) = 2 by norm_num]
    linarith
  · -- q = 3
    have hv : vTau 3 = 386995 / 100000 := by norm_num [vTau]
    have hL := h4_log_three_lower
    have key : ((v13H4IntegralQ : ℚ) : ℝ) + 13 / 160 -
        53 / 48 * (10986122885 / 10000000000 : ℝ) < 386995 / 100000 := by
      norm_num [v13H4IntegralQ]
    rw [hv, show ((3 : ℕ) : ℝ) = 3 by norm_num]
    linarith
  · -- q = 4: log 4 = 2 log 2
    have hv : vTau 4 = 355230 / 100000 := by norm_num [vTau]
    have hL := h4_log_two_lower
    have key : ((v13H4IntegralQ : ℚ) : ℝ) + 13 / 160 -
        53 / 48 * (2 * (6931471803 / 10000000000 : ℝ)) < 355230 / 100000 := by
      norm_num [v13H4IntegralQ]
    rw [hv, show ((4 : ℕ) : ℝ) = 4 by norm_num, h4_log_four_eq]
    linarith
  · -- q = 5: the tightest case, slack 3.38e-6 on log 5 (margin 3.73e-6)
    have hv : vTau 5 = 330591 / 100000 := by norm_num [vTau]
    have hL := h4_log_five_lower
    have key : ((v13H4IntegralQ : ℚ) : ℝ) + 13 / 160 -
        53 / 48 * (16094379123 / 10000000000 : ℝ) < 330591 / 100000 := by
      norm_num [v13H4IntegralQ]
    rw [hv, show ((5 : ℕ) : ℝ) = 5 by norm_num]
    linarith
  · -- q = 6: log 6 = log 2 + log 3
    have hv : vTau 6 = 310460 / 100000 := by norm_num [vTau]
    have h2 := h4_log_two_lower
    have h3 := h4_log_three_lower
    have key : ((v13H4IntegralQ : ℚ) : ℝ) + 13 / 160 -
        53 / 48 * ((6931471803 / 10000000000 : ℝ) + 10986122885 / 10000000000) <
          310460 / 100000 := by
      norm_num [v13H4IntegralQ]
    rw [hv, show ((6 : ℕ) : ℝ) = 6 by norm_num, h4_log_six_eq]
    linarith
  · -- q = 7: log 7 = log 2 + log 3 + log (7/6)
    have hv : vTau 7 = 293439 / 100000 := by norm_num [vTau]
    have hL := h4_log_seven_lower
    have key : ((v13H4IntegralQ : ℚ) : ℝ) + 13 / 160 -
        53 / 48 * ((6931471803 / 10000000000 : ℝ) + 10986122885 / 10000000000 +
          15415067 / 100000000) < 293439 / 100000 := by
      norm_num [v13H4IntegralQ]
    rw [hv, show ((7 : ℕ) : ℝ) = 7 by norm_num]
    linarith

/-- the construction's `v13_log_lower` form (plan §3, L2c/L4). -/
theorem v13_log_lower {q : ℕ} (hq : SignedVBaseRange q) :
    (48 / 53 : ℝ) * (((v13H4IntegralQ : ℚ) : ℝ) + 13 / 160 - vTau q) <
      Real.log (q : ℝ) := by
  have h := v13H4_rate_hint_of_integral hq (I := ((v13H4IntegralQ : ℚ) : ℝ)) rfl
  linarith

end
end Li2Lean.B3

#print axioms Li2Lean.B3.v13H4_rate_hint_of_integral
#print axioms Li2Lean.B3.v13_log_lower
