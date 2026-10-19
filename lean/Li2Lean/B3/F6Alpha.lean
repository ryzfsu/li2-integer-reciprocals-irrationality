/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B3.ReferencePackage
import Li2Lean.P0.ConfigLogTaylor

/-!
F6: exact numerical alpha bounds for the concrete signed-V bases.

The logarithm is bounded with the rational atanh enclosure from
`ConfigLogTaylor`; all endpoint comparisons after that are rational
`norm_num`/`nlinarith` checks.  No floating-point or unrestricted `decide`
certificate is used here.
-/

namespace Li2Lean
namespace B3

open Li2Lean.P0.ConfigLogTaylor

private theorem log_upper_f6_q2 :
    Real.log (2 : ℝ) < (693152 / 1000000 : ℝ) := by
  have h := log_lt_of_rational (q := (2 : ℚ))
    (upper := 693152 / 1000000) (by norm_num) 40 (by
      norm_num [logPolynomial, logRemainder, logCoordinate,
        Finset.sum_range_succ])
  norm_num at h ⊢
  exact h

private theorem log_upper_f6_q3 :
    Real.log (3 : ℝ) < (1098615 / 1000000 : ℝ) := by
  have h := log_lt_of_rational (q := (3 : ℚ))
    (upper := 1098615 / 1000000) (by norm_num) 40 (by
      norm_num [logPolynomial, logRemainder, logCoordinate,
        Finset.sum_range_succ])
  norm_num at h ⊢
  exact h

private theorem log_upper_f6_q4 :
    Real.log (4 : ℝ) < (13862945 / 10000000 : ℝ) := by
  have h := log_lt_of_rational (q := (4 : ℚ))
    (upper := 13862945 / 10000000) (by norm_num) 40 (by
      norm_num [logPolynomial, logRemainder, logCoordinate,
        Finset.sum_range_succ])
  norm_num at h ⊢
  exact h

private theorem log_upper_f6_q5 :
    Real.log (5 : ℝ) < (1609438 / 1000000 : ℝ) := by
  have h := log_lt_of_rational (q := (5 : ℚ))
    (upper := 1609438 / 1000000) (by norm_num) 40 (by
      norm_num [logPolynomial, logRemainder, logCoordinate,
        Finset.sum_range_succ])
  norm_num at h ⊢
  exact h

private theorem log_upper_f6_q6 :
    Real.log (6 : ℝ) < (1791766 / 1000000 : ℝ) := by
  have h := log_lt_of_rational (q := (6 : ℚ))
    (upper := 1791766 / 1000000) (by norm_num) 40 (by
      norm_num [logPolynomial, logRemainder, logCoordinate,
        Finset.sum_range_succ])
  norm_num at h ⊢
  exact h

private theorem log_upper_f6_q7 :
    Real.log (7 : ℝ) < (1945914 / 1000000 : ℝ) := by
  have h := log_lt_of_rational (q := (7 : ℚ))
    (upper := 1945914 / 1000000) (by norm_num) 40 (by
      norm_num [logPolynomial, logRemainder, logCoordinate,
        Finset.sum_range_succ])
  norm_num at h ⊢
  exact h

theorem v13_alpha_le_q2 :
    vAlpha 2 ≤ (vQlow 2 : ℝ) - 3 / 2 * Real.log (2 : ℝ) -
      (vKx 2 : ℝ) - 5 / 4 * (vKv 2 : ℝ) - (vKz 2 : ℝ) := by
  have hlog := log_upper_f6_q2
  norm_num [vAlpha, vQlow, vKx, vKv, vKz]
  nlinarith

theorem v13_alpha_le_q3 :
    vAlpha 3 ≤ (vQlow 3 : ℝ) - 3 / 2 * Real.log (3 : ℝ) -
      (vKx 3 : ℝ) - 5 / 4 * (vKv 3 : ℝ) - (vKz 3 : ℝ) := by
  have hlog := log_upper_f6_q3
  norm_num [vAlpha, vQlow, vKx, vKv, vKz]
  nlinarith

theorem v13_alpha_le_q4 :
    vAlpha 4 ≤ (vQlow 4 : ℝ) - 3 / 2 * Real.log (4 : ℝ) -
      (vKx 4 : ℝ) - 5 / 4 * (vKv 4 : ℝ) - (vKz 4 : ℝ) := by
  have hlog := log_upper_f6_q4
  norm_num [vAlpha, vQlow, vKx, vKv, vKz]
  nlinarith

theorem v13_alpha_le_q5 :
    vAlpha 5 ≤ (vQlow 5 : ℝ) - 3 / 2 * Real.log (5 : ℝ) -
      (vKx 5 : ℝ) - 5 / 4 * (vKv 5 : ℝ) - (vKz 5 : ℝ) := by
  have hlog := log_upper_f6_q5
  norm_num [vAlpha, vQlow, vKx, vKv, vKz]
  nlinarith

theorem v13_alpha_le_q6 :
    vAlpha 6 ≤ (vQlow 6 : ℝ) - 3 / 2 * Real.log (6 : ℝ) -
      (vKx 6 : ℝ) - 5 / 4 * (vKv 6 : ℝ) - (vKz 6 : ℝ) := by
  have hlog := log_upper_f6_q6
  norm_num [vAlpha, vQlow, vKx, vKv, vKz]
  nlinarith

theorem v13_alpha_le_q7 :
    vAlpha 7 ≤ (vQlow 7 : ℝ) - 3 / 2 * Real.log (7 : ℝ) -
      (vKx 7 : ℝ) - 5 / 4 * (vKv 7 : ℝ) - (vKz 7 : ℝ) := by
  have hlog := log_upper_f6_q7
  norm_num [vAlpha, vQlow, vKx, vKv, vKz]
  nlinarith

theorem v13_alpha_le_of_range {q : ℕ} (hq : SignedVBaseRange q) :
    vAlpha q ≤ (vQlow q : ℝ) - 3 / 2 * Real.log (q : ℝ) -
      (vKx q : ℝ) - 5 / 4 * (vKv q : ℝ) - (vKz q : ℝ) := by
  obtain ⟨h2, h7⟩ := hq
  interval_cases q
  · exact v13_alpha_le_q2
  · exact v13_alpha_le_q3
  · exact v13_alpha_le_q4
  · exact v13_alpha_le_q5
  · exact v13_alpha_le_q6
  · exact v13_alpha_le_q7

end B3
end Li2Lean

#print axioms Li2Lean.B3.v13_alpha_le_of_range
