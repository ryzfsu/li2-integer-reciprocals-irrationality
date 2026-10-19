/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.Q11Geometry

namespace Li2Lean.P0.Q11Data

/-!
The q=11 endpoint scalar connection from paper v13:
* `p0-analytic.tex:749-765` gives `alpha(log (11/2)) >= 77597/100000`;
* `p0-analytic.tex:804-826` records the directed q=11 penalties;
* `p0-analytic.tex:828-877` gives the tangent upper bound
  `0.772577360778` and the strict `3/1000` endpoint margin;
* `p0-arithmetic.tex:705-716` supplies the fixed-base rate specialized at 11.

This file connects those printed rational bounds to the q=11 data record and
its endpoint geometry. All comparisons reduce to signed-integer
cross-multiplication; it does not establish the analytic directed-field checks.
-/

noncomputable def ratioToReal (x : IntRatio) : ℝ := (x.num : ℝ) / (x.den : ℝ)

def ratioGapNumerator (x y : IntRatio) : ℤ :=
  x.num * (y.den : ℤ) - y.num * (x.den : ℤ)

theorem ratioToReal_sub_eq_cross (x y : IntRatio)
    (hx : x.den ≠ 0) (hy : y.den ≠ 0) :
    ratioToReal x - ratioToReal y =
      (ratioGapNumerator x y : ℝ) / ((x.den * y.den : ℕ) : ℝ) := by
  have hxd : (x.den : ℝ) ≠ 0 := by exact_mod_cast hx
  have hyd : (y.den : ℝ) ≠ 0 := by exact_mod_cast hy
  unfold ratioToReal ratioGapNumerator
  push_cast
  field_simp [hxd, hyd]

theorem q11_endpoint_margin_crossmul :
    1000 * ratioGapNumerator alphaLower endpointTangentUpper >
      3 * (alphaLower.den : ℤ) * (endpointTangentUpper.den : ℤ) := by
  norm_num [ratioGapNumerator, alphaLower, endpointTangentUpper]

theorem q11_endpoint_alpha_minus_tangent_gt_three_per_thousand :
    (3 : ℝ) / 1000 < ratioToReal alphaLower - ratioToReal endpointTangentUpper := by
  norm_num [ratioToReal, alphaLower, endpointTangentUpper]

theorem q11_geometry_matches_table :
    pinnedEdge 0 = (1 / 4 : ℚ) ∧ pinnedEdge 8 = (5 / 4 : ℚ) ∧
      frequencyEdge 0 = (1 / 2 : ℚ) ∧ frequencyEdge 4 = (9 / 2 : ℚ) := by
  exact ⟨pinnedEdge_zero, pinnedEdge_eight, frequencyEdge_zero, frequencyEdge_four⟩

end Li2Lean.P0.Q11Data
