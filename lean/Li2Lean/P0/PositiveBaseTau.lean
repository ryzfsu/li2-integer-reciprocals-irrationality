/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/

import Li2Lean.P0.PositiveBaseParam

namespace Li2Lean.P0.PositiveBase

noncomputable section

/-- The fixed-base rate decreases strictly after the q = 2 endpoint.
The proof uses only the affine rate formula and Mathlib's certified decimal
bounds for `log 2` and `log 3`; it is independent of the analytic producer. -/
theorem tauSharp_lt_two (q : ℤ) (hq : 2 < q) :
    p0TauSharp q < p0TauSharp 2 := by
  rw [tauSharp_affine q (by omega)]
  have hq0 : (0 : ℝ) < q := by
    exact_mod_cast (show (0 : ℤ) < q by omega)
  have hqm1 : (0 : ℝ) < q - 1 := by
    exact_mod_cast (show (0 : ℤ) < q - 1 by omega)
  have hlog_le : Real.log ((q - 1 : ℤ) : ℝ) ≤ Real.log (q : ℝ) := by
    have hcast : ((q - 1 : ℤ) : ℝ) = (q : ℝ) - 1 := by norm_num
    rw [hcast]
    apply Real.log_le_log hqm1
    linarith
  have hlog_q : Real.log (3 : ℝ) ≤ Real.log (q : ℝ) := by
    apply Real.log_le_log (by norm_num)
    exact_mod_cast (show (3 : ℤ) ≤ q by omega)
  have hstrength : (13 : ℝ) * Real.log 2 < 12 * Real.log (q : ℝ) := by
    have h2 := Real.log_two_lt_d9
    have h3 := Real.log_three_gt_d9
    nlinarith
  nlinarith

theorem tauSharp_le_two_of_range {q : ℤ} (hq : 2 ≤ q) :
    p0TauSharp q ≤ p0TauSharp 2 := by
  rcases hq.eq_or_lt with rfl | hq'
  · rfl
  · exact (tauSharp_lt_two q hq').le

theorem tauSharp_lt_rateClaim_of_range {q : ℤ} (hq : 2 ≤ q) :
    p0TauSharp q < (1979 / 1000 : ℝ) := by
  exact lt_of_le_of_lt (tauSharp_le_two_of_range hq)
    p0TauSharp_two_lt_1979_over_1000

end

end Li2Lean.P0.PositiveBase
