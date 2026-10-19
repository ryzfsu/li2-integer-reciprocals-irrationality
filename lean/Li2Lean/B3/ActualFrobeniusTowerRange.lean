/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/

import Li2Lean.B3.RangeArithmeticNonvanishingAdapters

/-!
# Fixed-base views of the signed Frobenius tower

This file is only a naming and projection layer. The construction-bound fields
remain those of VActualFrobeniusTowerProducer in ActualFrobeniusProducer;
every polynomial is the actual V.vPolynomial and the auxiliary prime is
vSeedPrime q.

The mathematical obligations are the six finite seed/Frobenius reductions and
the strict p-adic tail estimate in nonvanishing.tex:146-275. The endpoint
nonvanishing conclusion is reused from V.NonvanishingPlan, while q-selection
follows B3.RangeArithmeticNonvanishingAdapters.
-/

namespace Li2Lean.B3

noncomputable section

/-! ## Fixed-base producer aliases

The range proof is retained in each alias because the seed boundary in
VActualFrobeniusTowerProducer is part of the construction input. -/

abbrev VActualFrobeniusTowerProducerQ2 :=
  forall hq : SignedVBaseRange 2, VActualFrobeniusTowerProducer 2 hq

abbrev VActualFrobeniusTowerProducerQ3 :=
  forall hq : SignedVBaseRange 3, VActualFrobeniusTowerProducer 3 hq

abbrev VActualFrobeniusTowerProducerQ4 :=
  forall hq : SignedVBaseRange 4, VActualFrobeniusTowerProducer 4 hq

abbrev VActualFrobeniusTowerProducerQ5 :=
  forall hq : SignedVBaseRange 5, VActualFrobeniusTowerProducer 5 hq

abbrev VActualFrobeniusTowerProducerQ6 :=
  forall hq : SignedVBaseRange 6, VActualFrobeniusTowerProducer 6 hq

abbrev VActualFrobeniusTowerProducerQ7 :=
  forall hq : SignedVBaseRange 7, VActualFrobeniusTowerProducer 7 hq

/-! ## Raw-tower projections

These projections expose the exact V.VActualFrobeniusTower expected by the
nonvanishing input. They only apply the existing toTower theorem, so no seed,
valuation, or Frobenius statement is synthesized here.

v13: nonvanishing.tex:146-275; reused Lean modules:
V.NonvanishingPlan and B3.ActualFrobeniusProducer. -/

theorem actual_frobenius_tower_q2
    (P : VActualFrobeniusTowerProducerQ2) :
    V.VActualFrobeniusTower 2 (vSeedPrime 2) := by
  have hq : SignedVBaseRange 2 := by
    constructor <;> norm_num
  exact (P hq).toTower

theorem actual_frobenius_tower_q3
    (P : VActualFrobeniusTowerProducerQ3) :
    V.VActualFrobeniusTower 3 (vSeedPrime 3) := by
  have hq : SignedVBaseRange 3 := by
    constructor <;> norm_num
  exact (P hq).toTower

theorem actual_frobenius_tower_q4
    (P : VActualFrobeniusTowerProducerQ4) :
    V.VActualFrobeniusTower 4 (vSeedPrime 4) := by
  have hq : SignedVBaseRange 4 := by
    constructor <;> norm_num
  exact (P hq).toTower

theorem actual_frobenius_tower_q5
    (P : VActualFrobeniusTowerProducerQ5) :
    V.VActualFrobeniusTower 5 (vSeedPrime 5) := by
  have hq : SignedVBaseRange 5 := by
    constructor <;> norm_num
  exact (P hq).toTower

theorem actual_frobenius_tower_q6
    (P : VActualFrobeniusTowerProducerQ6) :
    V.VActualFrobeniusTower 6 (vSeedPrime 6) := by
  have hq : SignedVBaseRange 6 := by
    constructor <;> norm_num
  exact (P hq).toTower

theorem actual_frobenius_tower_q7
    (P : VActualFrobeniusTowerProducerQ7) :
    V.VActualFrobeniusTower 7 (vSeedPrime 7) := by
  have hq : SignedVBaseRange 7 := by
    constructor <;> norm_num
  exact (P hq).toTower

/-! ## Endpoint-facing q = 2 adapter

The generic range adapter already supplies q = 3, ..., 7 named endpoints.
The q = 2 entry is stated here as well, so all six signed bases have the
same producer-facing API. -/

theorem nonvanishing_plan_q2_of_actual_frobenius_producers
    (P : VActualFrobeniusTowerProducers) : NonvanishingPlan 2 := by
  have hq : SignedVBaseRange 2 := by
    constructor <;> norm_num
  exact nonvanishing_plan_of_actual_frobenius_producers P hq

/-! The frozen a = 2 route is the regression instance: the tower interface
is unchanged at the positive half-value base, with only the signed parameter
pinning changing from -q to the existing actual family. -/

theorem actual_frobenius_tower_q2_regression
    (P : VActualFrobeniusTowerProducerQ2) :
    V.VActualFrobeniusTower 2 (vSeedPrime 2) :=
  actual_frobenius_tower_q2 P

end
end Li2Lean.B3

#print axioms Li2Lean.B3.actual_frobenius_tower_q2
#print axioms Li2Lean.B3.actual_frobenius_tower_q3
#print axioms Li2Lean.B3.actual_frobenius_tower_q4
#print axioms Li2Lean.B3.actual_frobenius_tower_q5
#print axioms Li2Lean.B3.actual_frobenius_tower_q6
#print axioms Li2Lean.B3.actual_frobenius_tower_q7
#print axioms Li2Lean.B3.nonvanishing_plan_q2_of_actual_frobenius_producers
