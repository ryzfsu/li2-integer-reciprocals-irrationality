/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/

import Li2Lean.B3.ActualFrobeniusTowerRange
import Li2Lean.B3.Q2SeedResidueInterface

/-!
# Construction-bound nonvanishing wiring

This file is the downstream bridge from the finite seed reduction to the
Frobenius producer consumed by the signed endpoint criterion. It does not
prove the coefficientwise divisibility or the strict p-adic tail estimate:
those remain explicit fields of the producer. In particular, a finite q = 2
residue computation is not treated as a complete Frobenius argument.

The mathematical source is v13 `nonvanishing.tex:146-198` (seed reduction),
`:200-258` (scaled coefficient and unit conditions), and `:262-275`
(eventual nonvanishing). The construction-bound polynomial and scaled
polynomial are reused from `B3.ActualFrobeniusProducer`; q = 2's finite-place
matrix is reused from `B3.Q2SeedResidueInterface`.
-/

namespace Li2Lean.B3

noncomputable section

/-! ## q = 2 construction boundary -/

/-- The q = 2 producer fields after the printed 9 by 9 residue boundary.

The residue interface is retained as a separate field so the finite LU
calculation cannot be replaced by an unrelated seed constant. The remaining
fields are exactly the two infinite families of obligations in
`nonvanishing.tex:200-275`.
-/
structure VActualFrobeniusTowerQ2Inputs : Prop where
  residue : Q2ActualSeedResidueInterface
  scaled_coefficients_integral :
    ∀ k : ℕ, 0 < k → ∀ i : ℕ,
      (V.vFrobeniusScaledPolynomial 2 (vSeedPrime 2) k).coeff i ≠ 0 →
        0 ≤ padicValRat (vSeedPrime 2)
          ((V.vFrobeniusScaledPolynomial 2 (vSeedPrime 2) k).coeff i)
  scaled_constant_unit :
    ∀ k : ℕ, 0 < k →
      (V.vFrobeniusScaledPolynomial 2 (vSeedPrime 2) k).coeff 0 ≠ 0 ∧
        padicValRat (vSeedPrime 2)
          ((V.vFrobeniusScaledPolynomial 2 (vSeedPrime 2) k).coeff 0) = 0
  strict_tail :
    ∀ r : ℚ, ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      V.VUnitConstantEvaluationInput 2 (vSeedPrime 2) k
        (((vSeedPrime 2 ^ k : ℕ) : ℚ) ^ 2 * r)

/-- Convert the q = 2 boundary to the common construction-bound producer.

The target proof uses the exact residue boundary's `boundary` field; no
valuation or determinant is inferred from the residue determinant. -/
theorem VActualFrobeniusTowerQ2Inputs.toProducer
    (P : VActualFrobeniusTowerQ2Inputs) :
    VActualFrobeniusTowerProducer 2 q2SignedRange :=
  { seed_boundary := P.residue.boundary
    scaled_coefficients_integral := P.scaled_coefficients_integral
    scaled_constant_unit := P.scaled_constant_unit
    strict_tail := P.strict_tail }

theorem VActualFrobeniusTowerQ2Inputs.toTower
    (P : VActualFrobeniusTowerQ2Inputs) :
    V.VActualFrobeniusTower 2 (vSeedPrime 2) :=
  P.toProducer.toTower

theorem VActualFrobeniusTowerQ2Inputs.eventual_nonvanishing
    (P : VActualFrobeniusTowerQ2Inputs) :
    VEventualNonvanishing 2 (vSeedPrime 2) :=
  eventualNonvanishing_of_VActualFrobeniusTowerProducer P.toProducer

/-! ## Unified q = 2,...,7 bundle -/

/-- Construction-bound producers for all six signed bases. The q = 2 entry
is the residue-aware input above; q = 3,...,7 use the same actual polynomial
and fixed-prime producer aliases from `ActualFrobeniusTowerRange`.
-/
structure VActualFrobeniusTowerRangeInputs : Prop where
  q2 : VActualFrobeniusTowerQ2Inputs
  q3 : VActualFrobeniusTowerProducerQ3
  q4 : VActualFrobeniusTowerProducerQ4
  q5 : VActualFrobeniusTowerProducerQ5
  q6 : VActualFrobeniusTowerProducerQ6
  q7 : VActualFrobeniusTowerProducerQ7

/-- Expose the common family expected by the range selector. -/
theorem VActualFrobeniusTowerRangeInputs.toProducers
    (P : VActualFrobeniusTowerRangeInputs) :
    VActualFrobeniusTowerProducers :=
  { q2 := fun hq => by
      have hq_eq : hq = q2SignedRange := Subsingleton.elim _ _
      exact hq_eq ▸ P.q2.toProducer
    q3 := P.q3
    q4 := P.q4
    q5 := P.q5
    q6 := P.q6
    q7 := P.q7 }

theorem nonvanishing_plan_of_range_inputs
    (P : VActualFrobeniusTowerRangeInputs) {q : ℕ}
    (hq : SignedVBaseRange q) :
    NonvanishingPlan q :=
  nonvanishing_plan_of_actual_frobenius_producers P.toProducers hq

theorem nonvanishing_plan_q2_of_range_inputs
    (P : VActualFrobeniusTowerRangeInputs) :
    NonvanishingPlan 2 := by
  have hq : SignedVBaseRange 2 := by
    constructor <;> norm_num
  exact nonvanishing_plan_of_range_inputs P hq

theorem nonvanishing_plan_q3_of_range_inputs
    (P : VActualFrobeniusTowerRangeInputs) :
    NonvanishingPlan 3 := by
  have hq : SignedVBaseRange 3 := by
    constructor <;> norm_num
  exact nonvanishing_plan_of_range_inputs P hq

theorem nonvanishing_plan_q4_of_range_inputs
    (P : VActualFrobeniusTowerRangeInputs) :
    NonvanishingPlan 4 := by
  have hq : SignedVBaseRange 4 := by
    constructor <;> norm_num
  exact nonvanishing_plan_of_range_inputs P hq

theorem nonvanishing_plan_q5_of_range_inputs
    (P : VActualFrobeniusTowerRangeInputs) :
    NonvanishingPlan 5 := by
  have hq : SignedVBaseRange 5 := by
    constructor <;> norm_num
  exact nonvanishing_plan_of_range_inputs P hq

theorem nonvanishing_plan_q6_of_range_inputs
    (P : VActualFrobeniusTowerRangeInputs) :
    NonvanishingPlan 6 := by
  have hq : SignedVBaseRange 6 := by
    constructor <;> norm_num
  exact nonvanishing_plan_of_range_inputs P hq

theorem nonvanishing_plan_q7_of_range_inputs
    (P : VActualFrobeniusTowerRangeInputs) :
    NonvanishingPlan 7 := by
  have hq : SignedVBaseRange 7 := by
    constructor <;> norm_num
  exact nonvanishing_plan_of_range_inputs P hq

/-! ## q = 2 regression -/

/-- The generalized selector leaves the q = 2 parameter instance intact. -/
theorem q2_nonvanishing_regression
    (P : VActualFrobeniusTowerRangeInputs) :
    NonvanishingPlan 2 :=
  nonvanishing_plan_q2_of_range_inputs P

end
end Li2Lean.B3

#print axioms Li2Lean.B3.VActualFrobeniusTowerQ2Inputs.toTower
#print axioms Li2Lean.B3.nonvanishing_plan_of_range_inputs
#print axioms Li2Lean.B3.q2_nonvanishing_regression
