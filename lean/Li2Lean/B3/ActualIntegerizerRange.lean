/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/

/-
# Fixed-base rational integerizer range adapters

This file is the small downstream boundary for the construction-bound
rational integerizer.  The existing Nat-valued
`V.VActualIntegerizerCertificate` is retained as a legacy interface, but it
cannot represent the formal divisor when v13 has negative local exponents.
The range route therefore consumes the rational producer from
`ActualRationalIntegerizerProducer`.

The definitions below only select q = 2,...,7 fields and transport the
already explicit residue/outer-pole and PNT obligations.  They do not prove
those obligations and do not introduce a free valuation or determinant.

Paper anchors: `v-arithmetic.tex:24-32` (degree), `:128-351`
(residue-block/outer-pole exponents), and `:353-421` (rational clearing and
the weighted prime-sum rate).  The q = 2 regression is the same
`V.vPolynomial`/source-matrix identity used by the frozen Li2(1/2) route.
-/

import Li2Lean.B3.ActualRationalIntegerizerProducer

namespace Li2Lean.B3

noncomputable section

/-! ## Fixed-base selection -/

/-- Select the rational producer corresponding to a base in the v13 signed
range.  `interval_cases` only performs finite index bookkeeping; every
mathematical certificate remains a field of the selected producer.

v13: `v-arithmetic.tex:128-421`. -/
def VActualRationalIntegerizerProducerFamily.at
    (P : VActualRationalIntegerizerProducerFamily) {q : ℕ}
    (hq : SignedVBaseRange q) :
    VActualRationalIntegerizerProducer q (vTau q) := by
  obtain ⟨hlo, hhi⟩ := hq
  interval_cases q
  · exact P.q2
  · exact P.q3
  · exact P.q4
  · exact P.q5
  · exact P.q6
  · exact P.q7

/-! ## Arithmetic-plan transport -/

/-- A rational construction-bound producer supplies the endpoint arithmetic
plan.  The degree component is the unconditional polynomial degree lemma;
the rational clearing and PNT rate are carried by `P`.

v13: `v-arithmetic.tex:24-32,353-421`. -/
theorem arithmeticPlan_of_actual_rational_producer
    {q : ℕ} (P : VActualRationalIntegerizerProducer q (vTau q)) :
    ArithmeticPlan q :=
  { degree := actual_rational_degree_bound q
    integerizer := vIntegerizerBound_of_actual_rational_producer P }

theorem arithmetic_plan_q2_of_actual_rational_integerizer_producers
    (P : VActualRationalIntegerizerProducerQ2) : ArithmeticPlan 2 :=
  arithmeticPlan_of_actual_rational_producer P

theorem arithmetic_plan_q3_of_actual_rational_integerizer_producers
    (P : VActualRationalIntegerizerProducerQ3) : ArithmeticPlan 3 :=
  arithmeticPlan_of_actual_rational_producer P

theorem arithmetic_plan_q4_of_actual_rational_integerizer_producers
    (P : VActualRationalIntegerizerProducerQ4) : ArithmeticPlan 4 :=
  arithmeticPlan_of_actual_rational_producer P

theorem arithmetic_plan_q5_of_actual_rational_integerizer_producers
    (P : VActualRationalIntegerizerProducerQ5) : ArithmeticPlan 5 :=
  arithmeticPlan_of_actual_rational_producer P

theorem arithmetic_plan_q6_of_actual_rational_integerizer_producers
    (P : VActualRationalIntegerizerProducerQ6) : ArithmeticPlan 6 :=
  arithmeticPlan_of_actual_rational_producer P

theorem arithmetic_plan_q7_of_actual_rational_integerizer_producers
    (P : VActualRationalIntegerizerProducerQ7) : ArithmeticPlan 7 :=
  arithmeticPlan_of_actual_rational_producer P

/-- Family-level plan transport, with no hidden q-specific assumptions.
v13: `v-arithmetic.tex:128-421`. -/
theorem arithmeticPlan_of_actual_rational_family
    (P : VActualRationalIntegerizerProducerFamily)
    {q : ℕ} (hq : SignedVBaseRange q) : ArithmeticPlan q :=
  arithmeticPlan_of_actual_rational_producer (P.at hq)

/-! ## 1/2 regression -/

/-- The generalized signed infrastructure leaves the positive `a = 2`
determinant unchanged.  This delegates to the existing regression theorem,
rather than recreating the frozen 1/2 construction.

v13: `v-arithmetic.tex:24-35`; reuse the 1/2 source-matrix identity. -/
theorem actual_integerizer_range_a2_regression (n : ℕ) :
    V.actualDeterminantAt 2 (4 * n) = V.vPolynomial n (2 : ℤ) :=
  actual_rational_a2_regression n

end
end Li2Lean.B3

#print axioms Li2Lean.B3.arithmeticPlan_of_actual_rational_producer
#print axioms Li2Lean.B3.arithmeticPlan_of_actual_rational_family
#print axioms Li2Lean.B3.actual_integerizer_range_a2_regression
