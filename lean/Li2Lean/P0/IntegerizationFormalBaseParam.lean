/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/

import Li2Lean.P0.IntegerizationFormalBase

namespace Li2Lean.P0.Integerization

noncomputable section

/-!
## Base-parametric specialization of the denominator-free formal factors

`formalQNum` is the numerator obtained after clearing the factor
`(a - 1)^s` from `Q_s(a)`. These lemmas expose its specialization at an
arbitrary rational base. They are the algebraic input for the q-adic port;
they do not assert coefficient integrality or the pole divisor.
-/

lemma outerEval_aVar (a : ℚ) :
    outerEval a aVar = Polynomial.C a := by
  simp [outerEval, aVar]

lemma outerEval_ratConst (a r : ℚ) :
    outerEval a (ratConst r) = Polynomial.C r := by
  simp [outerEval, ratConst]

theorem formalQNum_outerEval (a : ℚ) (g s : ℕ) :
    outerEval a (formalQNum g s) =
      Polynomial.C ((a - 1) ^ (g - s) * (a ^ s - (a - 1) ^ s)) := by
  simp only [formalQNum, map_mul, map_sub, map_pow,
    outerEval_aVar, outerEval_ratConst]

theorem formalQNum_outerEval_eq_scale_mul_p0Q
    (a : ℚ) (g s : ℕ) (hs : s ≤ g) (ha : a ≠ 1) :
    outerEval a (formalQNum g s) =
      Polynomial.C ((a - 1) ^ g * p0Q a s) := by
  rw [formalQNum_outerEval]
  congr 1
  unfold p0Q
  have hne : a - 1 ≠ 0 := sub_ne_zero.mpr ha
  have hg : (a - 1) ^ g = (a - 1) ^ (g - s) * (a - 1) ^ s := by
    rw [← pow_add, Nat.sub_add_cancel hs]
  rw [hg]
  rw [div_pow]
  field_simp [hne]

theorem formalU_outerEval (a : ℚ) (g i : ℕ) :
    outerEval a (formalU g i) =
      Polynomial.C (p0UQ a g i) := by
  simp only [formalU, map_mul, map_pow, outerEval_aVar,
    outerEval_ratConst]
  simp [p0UQ]
  ring_nf

#print axioms formalQNum_outerEval
#print axioms formalQNum_outerEval_eq_scale_mul_p0Q
#print axioms formalU_outerEval

end

end Li2Lean.P0.Integerization
