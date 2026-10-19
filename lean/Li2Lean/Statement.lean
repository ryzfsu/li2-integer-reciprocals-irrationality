/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Mathlib

namespace Li2Lean

/--
The exact real series in the all-n target of v13 `main.tex:97-103`.
-/
noncomputable def li2InvValue (n : ℤ) : ℝ :=
  ∑' k : ℕ, ((n : ℝ)⁻¹) ^ (k + 1) / ((k : ℝ) + 1) ^ 2

/--
The unconditional theorem target from v13 `main.tex:101-103`; its proof is
assembled in `Li2Lean.AllN.Producers` and exported by `Solution`.
-/
noncomputable def li2InvIrrationalStatement : Prop :=
  ∀ n : ℤ, n ≠ 0 → Irrational (li2InvValue n)

/--
Every nonzero integer lies in one of the v13 ranges used by the conditional
assembly: the classical endpoints, positive P0, signed V, or an HP tail. The
theorem states coverage only; bridge hypotheses remain explicit elsewhere.
-/
theorem li2InvRangeSplit (n : ℤ) (hn : n ≠ 0) :
    n = 1 ∨ n = -1 ∨
      ((2 : ℤ) ≤ n ∧ n ≤ 11) ∨ ((-7 : ℤ) ≤ n ∧ n ≤ -2) ∨
      (12 : ℤ) ≤ n ∨ n ≤ -8 := by
  omega

end Li2Lean
