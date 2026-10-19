/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.Q11EndpointArithmetic

namespace Li2Lean.P0.Q11Data

/-!
The scalar inequality used for the q = 11 endpoint estimate. The rational
logarithm bounds below are deliberately coarse; the actual measure-to-field
comparison is a separate lemma.

Paper source: v13 `chapters/p0-analytic.tex:749-800`.
-/
theorem q11_endpoint_coarse_log_lower_v2 :
    (56 / 5 : ℝ) <
      3 * Real.log (81 / 10) + (81 / 10) * Real.log (11 / 2) -
        2 * Real.log (38 / 5) - Real.log (111 / 10) := by
  have hlog2 : (2 : ℝ) / 3 ≤ Real.log 2 := by
    have h := Real.le_log_one_add_of_nonneg (x := (1 : ℝ)) (by norm_num)
    norm_num at h
    exact h
  have hlog81_80 : (2 : ℝ) / 161 ≤ Real.log (81 / 80) := by
    have h := Real.le_log_one_add_of_nonneg (x := (1 : ℝ) / 80) (by norm_num)
    norm_num at h
    exact h
  have hlog11_8 : (6 : ℝ) / 19 ≤ Real.log (11 / 8) := by
    have h := Real.le_log_one_add_of_nonneg (x := (3 : ℝ) / 8) (by norm_num)
    norm_num at h
    exact h
  have hlog81 : Real.log (81 / 10) =
      3 * Real.log 2 + Real.log (81 / 80) := by
    calc
      Real.log (81 / 10) = Real.log ((2 : ℝ) ^ 3 * (81 / 80)) := by
        congr 1 <;> norm_num
      _ = Real.log ((2 : ℝ) ^ 3) + Real.log (81 / 80) := by
        rw [Real.log_mul (by norm_num) (by norm_num)]
      _ = 3 * Real.log 2 + Real.log (81 / 80) := by
        rw [Real.log_pow]
        norm_num
  have hlog11 : Real.log (11 / 2) =
      2 * Real.log 2 + Real.log (11 / 8) := by
    calc
      Real.log (11 / 2) = Real.log ((2 : ℝ) ^ 2 * (11 / 8)) := by
        congr 1 <;> norm_num
      _ = Real.log ((2 : ℝ) ^ 2) + Real.log (11 / 8) := by
        rw [Real.log_mul (by norm_num) (by norm_num)]
      _ = 2 * Real.log 2 + Real.log (11 / 8) := by
        rw [Real.log_pow]
        norm_num
  have hlog38 : Real.log (38 / 5) < 5 * (501 / 1000 : ℝ) := by
    have hpow : (38 / 5 : ℝ) < (1501 / 1000) ^ 5 := by norm_num
    have hmono := Real.log_lt_log (by norm_num : (0 : ℝ) < 38 / 5) hpow
    rw [Real.log_pow] at hmono
    have hbase := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1501 / 1000)
    norm_num at hbase
    linarith
  have hlog111 : Real.log (111 / 10) < 5 * (31 / 50 : ℝ) := by
    have hpow : (111 / 10 : ℝ) < (81 / 50) ^ 5 := by norm_num
    have hmono := Real.log_lt_log (by norm_num : (0 : ℝ) < 111 / 10) hpow
    rw [Real.log_pow] at hmono
    have hbase := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 81 / 50)
    norm_num at hbase
    linarith
  have hA : (2 + 2 / 161 : ℝ) ≤ Real.log (81 / 10) := by
    rw [hlog81]
    linarith
  have hB : (4 / 3 + 6 / 19 : ℝ) ≤ Real.log (11 / 2) := by
    rw [hlog11]
    linarith
  have hnum : (56 / 5 : ℝ) <
      3 * (2 + 2 / 161) + (81 / 10) * (4 / 3 + 6 / 19) -
        2 * (5 * (501 / 1000 : ℝ)) - 5 * (31 / 50 : ℝ) := by
    norm_num
  linarith

end Li2Lean.P0.Q11Data
