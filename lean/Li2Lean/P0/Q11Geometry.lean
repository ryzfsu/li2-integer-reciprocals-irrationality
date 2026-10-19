/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.Q11Data

namespace Li2Lean.P0.Q11Data

def pinnedEdge (j : ℕ) : ℚ :=
  (pinnedEdge32Units.getD j 0 : ℚ) / 32

def frequencyEdge (j : ℕ) : ℚ :=
  (frequencyEdge2Units.getD j 0 : ℚ) / 2

theorem pinnedEdge_zero : pinnedEdge 0 = (1 / 4 : ℚ) := by
  norm_num [pinnedEdge, pinnedEdge32Units]

theorem pinnedEdge_eight : pinnedEdge 8 = (5 / 4 : ℚ) := by
  norm_num [pinnedEdge, pinnedEdge32Units]

theorem frequencyEdge_zero : frequencyEdge 0 = (1 / 2 : ℚ) := by
  norm_num [frequencyEdge, frequencyEdge2Units]

theorem frequencyEdge_four : frequencyEdge 4 = (9 / 2 : ℚ) := by
  norm_num [frequencyEdge, frequencyEdge2Units]

theorem pinnedEdge_strictMono {j : ℕ} (hj : j < 8) :
    pinnedEdge j < pinnedEdge (j + 1) := by
  interval_cases j <;> norm_num [pinnedEdge, pinnedEdge32Units]

theorem frequencyEdge_strictMono {j : ℕ} (hj : j < 4) :
    frequencyEdge j < frequencyEdge (j + 1) := by
  interval_cases j <;> norm_num [frequencyEdge, frequencyEdge2Units]

theorem pinnedEdge_width {j : ℕ} (hj : j < 8) :
    pinnedEdge (j + 1) - pinnedEdge j = (1 / 8 : ℚ) := by
  interval_cases j <;> norm_num [pinnedEdge, pinnedEdge32Units]

theorem frequencyEdge_width {j : ℕ} (hj : j < 4) :
    frequencyEdge (j + 1) - frequencyEdge j = (1 : ℚ) := by
  interval_cases j <;> norm_num [frequencyEdge, frequencyEdge2Units]

end Li2Lean.P0.Q11Data
