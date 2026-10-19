/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/

import Li2Lean.B3.ActualIntegerizerProducer
import Li2Lean.B3.ActualFrobeniusProducer

/-!
# Range adapters for the signed-V arithmetic and nonvanishing inputs

The endpoint interfaces consume one `ArithmeticPlan` and one
`NonvanishingPlan` for a selected base `q`.  The construction-bound producer
files already pin those inputs to the actual determinant and to the fixed
paper prime.  This module supplies only the finite-range selection layer:
given explicit producers for q = 2, ..., 7, it selects the requested field
and applies the existing adapters.

No certificate is synthesized here.  In particular, the integerizer and
Frobenius tower remain explicit fields of the producer bundles, so these
theorems close the interface wiring without claiming that the v13 arithmetic
or Frobenius estimates have been proved unconditionally.
-/

namespace Li2Lean
namespace B3

noncomputable section

/-! ## Fixed-prime Frobenius producer bundle -/

/-- Construction-bound Frobenius producers for the six signed bases.

The range proof is an argument to each field rather than stored in the
bundle, which keeps the bundle independent of proof-term choices for
`SignedVBaseRange q`. -/
structure VActualFrobeniusTowerProducers where
  q2 : ∀ hq : SignedVBaseRange 2,
    VActualFrobeniusTowerProducer 2 hq
  q3 : ∀ hq : SignedVBaseRange 3,
    VActualFrobeniusTowerProducer 3 hq
  q4 : ∀ hq : SignedVBaseRange 4,
    VActualFrobeniusTowerProducer 4 hq
  q5 : ∀ hq : SignedVBaseRange 5,
    VActualFrobeniusTowerProducer 5 hq
  q6 : ∀ hq : SignedVBaseRange 6,
    VActualFrobeniusTowerProducer 6 hq
  q7 : ∀ hq : SignedVBaseRange 7,
    VActualFrobeniusTowerProducer 7 hq

/-- Select the construction-bound Frobenius producer at a signed base in the
allowed range. -/
def VActualFrobeniusTowerProducers.at
    (P : VActualFrobeniusTowerProducers) {q : ℕ}
    (hq : SignedVBaseRange q) :
    VActualFrobeniusTowerProducer q hq := by
  obtain ⟨hq2, hq7⟩ := hq
  interval_cases q
  · exact P.q2 ⟨by norm_num, by norm_num⟩
  · exact P.q3 ⟨by norm_num, by norm_num⟩
  · exact P.q4 ⟨by norm_num, by norm_num⟩
  · exact P.q5 ⟨by norm_num, by norm_num⟩
  · exact P.q6 ⟨by norm_num, by norm_num⟩
  · exact P.q7 ⟨by norm_num, by norm_num⟩

/-! ## Endpoint-facing plan adapters -/

/-- A complete actual integerizer producer bundle supplies an arithmetic plan
for every signed base in the v13 range.  The degree field is the unconditional
degree bound from `ActualIntegerizerProducer`; the remaining fields come from
the selected producer's actual determinant certificate. -/
theorem arithmetic_plan_of_actual_integerizer_producers
    (P : VActualIntegerizerProducers) {q : ℕ}
    (hq : SignedVBaseRange q) : ArithmeticPlan q :=
  arithmeticPlan_of_actual_integerizer_producer (P.at hq)

/-- A complete actual Frobenius producer bundle supplies the nonvanishing plan
for every signed base in the v13 range.  The fixed auxiliary prime is the
paper's `vSeedPrime q`, as enforced by the producer type. -/
theorem nonvanishing_plan_of_actual_frobenius_producers
    (P : VActualFrobeniusTowerProducers) {q : ℕ}
    (hq : SignedVBaseRange q) : NonvanishingPlan q :=
  { eventual := eventualNonvanishing_of_VActualFrobeniusTowerProducer
      (P.at hq) }

/-! ## q = 3, ..., 7 named entry points -/

theorem arithmetic_plan_q3_of_actual_integerizer_producers
    (P : VActualIntegerizerProducers) : ArithmeticPlan 3 :=
  arithmetic_plan_of_actual_integerizer_producers P ⟨by norm_num, by norm_num⟩

theorem arithmetic_plan_q4_of_actual_integerizer_producers
    (P : VActualIntegerizerProducers) : ArithmeticPlan 4 :=
  arithmetic_plan_of_actual_integerizer_producers P ⟨by norm_num, by norm_num⟩

theorem arithmetic_plan_q5_of_actual_integerizer_producers
    (P : VActualIntegerizerProducers) : ArithmeticPlan 5 :=
  arithmetic_plan_of_actual_integerizer_producers P ⟨by norm_num, by norm_num⟩

theorem arithmetic_plan_q6_of_actual_integerizer_producers
    (P : VActualIntegerizerProducers) : ArithmeticPlan 6 :=
  arithmetic_plan_of_actual_integerizer_producers P ⟨by norm_num, by norm_num⟩

theorem arithmetic_plan_q7_of_actual_integerizer_producers
    (P : VActualIntegerizerProducers) : ArithmeticPlan 7 :=
  arithmetic_plan_of_actual_integerizer_producers P ⟨by norm_num, by norm_num⟩

theorem nonvanishing_plan_q3_of_actual_frobenius_producers
    (P : VActualFrobeniusTowerProducers) : NonvanishingPlan 3 :=
  nonvanishing_plan_of_actual_frobenius_producers P ⟨by norm_num, by norm_num⟩

theorem nonvanishing_plan_q4_of_actual_frobenius_producers
    (P : VActualFrobeniusTowerProducers) : NonvanishingPlan 4 :=
  nonvanishing_plan_of_actual_frobenius_producers P ⟨by norm_num, by norm_num⟩

theorem nonvanishing_plan_q5_of_actual_frobenius_producers
    (P : VActualFrobeniusTowerProducers) : NonvanishingPlan 5 :=
  nonvanishing_plan_of_actual_frobenius_producers P ⟨by norm_num, by norm_num⟩

theorem nonvanishing_plan_q6_of_actual_frobenius_producers
    (P : VActualFrobeniusTowerProducers) : NonvanishingPlan 6 :=
  nonvanishing_plan_of_actual_frobenius_producers P ⟨by norm_num, by norm_num⟩

theorem nonvanishing_plan_q7_of_actual_frobenius_producers
    (P : VActualFrobeniusTowerProducers) : NonvanishingPlan 7 :=
  nonvanishing_plan_of_actual_frobenius_producers P ⟨by norm_num, by norm_num⟩

end
end B3
end Li2Lean

#print axioms Li2Lean.B3.arithmetic_plan_of_actual_integerizer_producers
#print axioms Li2Lean.B3.nonvanishing_plan_of_actual_frobenius_producers
#print axioms Li2Lean.B3.arithmetic_plan_q3_of_actual_integerizer_producers
#print axioms Li2Lean.B3.arithmetic_plan_q4_of_actual_integerizer_producers
#print axioms Li2Lean.B3.arithmetic_plan_q5_of_actual_integerizer_producers
#print axioms Li2Lean.B3.arithmetic_plan_q6_of_actual_integerizer_producers
#print axioms Li2Lean.B3.arithmetic_plan_q7_of_actual_integerizer_producers
#print axioms Li2Lean.B3.nonvanishing_plan_q3_of_actual_frobenius_producers
#print axioms Li2Lean.B3.nonvanishing_plan_q4_of_actual_frobenius_producers
#print axioms Li2Lean.B3.nonvanishing_plan_q5_of_actual_frobenius_producers
#print axioms Li2Lean.B3.nonvanishing_plan_q6_of_actual_frobenius_producers
#print axioms Li2Lean.B3.nonvanishing_plan_q7_of_actual_frobenius_producers
