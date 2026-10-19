/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B4.HPNoAdjSeriesBridge

open Filter Topology Polynomial
open scoped BigOperators

namespace Li2Lean.B4.TailAnalytic

noncomputable section

lemma hp_inv_abs_lt_one_of_v13_range {a : ℤ}
    (ha : (12 : ℤ) ≤ a ∨ a ≤ -8) : |(a : ℝ)⁻¹| < 1 := by
  have ha0 : a ≠ 0 := by
    rcases ha with hp | hn <;> omega
  have har : (a : ℝ) ≠ 0 := by exact_mod_cast ha0
  have haabs : (1 : ℝ) < |(a : ℝ)| := by
    rcases ha with hp | hn
    · rw [abs_of_pos (by exact_mod_cast (show 0 < a by omega))]
      exact_mod_cast (by omega : (1 : ℤ) < a)
    · rw [abs_of_neg (by exact_mod_cast (show a < 0 by omega))]
      exact_mod_cast (by omega : (1 : ℤ) < -a)
  rw [abs_inv]
  exact (inv_lt_one₀ (abs_pos.mpr har)).2 haabs

/-- The actual v13 tail-series field, proved from the coefficient construction
and the unconditional residue-tail certificate. -/
theorem hpTailRepresentation_of_v13_range {a : ℤ}
    (ha : (12 : ℤ) ≤ a ∨ a ≤ -8) :
    ∀ n, hpTailCombinationAt a n = hpRR n ((a : ℝ)⁻¹) := by
  intro n
  exact hpTailCombination_eq_hpRR_of_abs_inv_lt_one a n
    (hp_inv_abs_lt_one_of_v13_range ha)

/-- Package the proved tail field with the two remaining producer obligations.
The latter are explicit arguments and are not inferred here. -/
theorem hpNoAdjacentV13Input_of_producers {a : ℤ}
    (ha : (12 : ℤ) ≤ a ∨ a ≤ -8)
    (hrem : ∀ n, hpRR n ((a : ℝ)⁻¹) ≠ 0)
    (hdelta : ∀ n,
      hpThreeFormDeterminantAt a n =
        (hpDeltaNormalForm n).eval ((a : ℝ)⁻¹)) :
    HPNoAdjacentV13Input a := by
  refine ⟨hpTailRepresentation_of_v13_range ha, hrem, hdelta⟩

end
end Li2Lean.B4.TailAnalytic

#print axioms Li2Lean.B4.TailAnalytic.hpTailRepresentation_of_v13_range
