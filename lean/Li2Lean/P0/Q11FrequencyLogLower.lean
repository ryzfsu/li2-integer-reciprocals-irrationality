/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.CA.Frequency.Arith
import Li2Lean.P0.Q11FrequencyTerms

open Li2Lean.P0.ConfigLogTaylor

namespace Li2Lean.P0.Q11Data

/-!
The q = 11 frequency certificate has a margin below 2e-6.  The coarse
`2 < log 11` bound used by the first probe is not sufficient at that
precision.  This bound is the finite Taylor certificate used by the v13
logarithm enclosure (`certificate-algorithm.tex:86-91`).
-/
theorem q11_log11_gt_2397895272e9 :
    (2397895272 / 1000000000 : ℝ) < Real.log (11 : ℝ) := by
  have h := logPolynomial_le_log (q := (11 : ℚ)) (by norm_num) 64
  norm_num [logPolynomial, logCoordinate] at h ⊢
  linarith

theorem q11_log_linear_lower_tight :
    (2397895272 / 1000000000 : ℝ) < Real.log 2 + q11Lambda := by
  have h := logPolynomial_le_log (q := (11 : ℚ)) (by norm_num) 64
  have hsum : Real.log 2 + q11Lambda = Real.log (11 : ℝ) := by
    unfold q11Lambda
    calc
      Real.log 2 + Real.log (11 / 2 : ℝ) =
          Real.log (2 * (11 / 2) : ℝ) := by
        rw [Real.log_mul (by norm_num) (by norm_num)]
      _ = Real.log (11 : ℝ) := by norm_num
  rw [hsum]
  norm_num [logPolynomial, logCoordinate] at h ⊢
  linarith

end Li2Lean.P0.Q11Data

#print axioms Li2Lean.P0.Q11Data.q11_log11_gt_2397895272e9
#print axioms Li2Lean.P0.Q11Data.q11_log_linear_lower_tight
