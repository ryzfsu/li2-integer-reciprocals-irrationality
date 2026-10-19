/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.CoefficientStepAssembly

namespace Li2Lean.P0.CoefficientAssembly

open Li2Lean.P0
open Li2Lean.P0.Config

noncomputable section

/-! The q-parametric smoothing route uses the existing paper budget with two
additional linear units for the q-cell shift. This file keeps that arithmetic
separate from the analytic envelope and contour modules. -/

theorem q_cell_linear_budget_lt_58 :
    cStar + 2 + Real.log 39 + 1 + (12783 / 10000 : ℝ) < 58 := by
  have h := FrequencyHeadCount.paper_linear_budget_lt_56 cStar_lt
  nlinarith

theorem q_smoothing_constant_budget {m : ℕ} (hm8 : 8 ≤ m) :
    (304 : ℝ) + 2 / 3 ≤ 301 + 40 * Real.log (m : ℝ) := by
  have hmR : (8 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast hm8
  have hlogm : Real.log (8 : ℝ) ≤ Real.log (m : ℝ) :=
    Real.log_le_log (by norm_num) hmR
  have hlog8 : (2 : ℝ) < Real.log (8 : ℝ) := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    have h := Real.log_two_gt_d9
    norm_num at h ⊢
    nlinarith
  nlinarith

end

end Li2Lean.P0.CoefficientAssembly

#print axioms Li2Lean.P0.CoefficientAssembly.q_cell_linear_budget_lt_58
#print axioms Li2Lean.P0.CoefficientAssembly.q_smoothing_constant_budget
