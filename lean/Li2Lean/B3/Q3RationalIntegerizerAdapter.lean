/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/

import Li2Lean.B3.ActualRationalIntegerizerProducer
import Li2Lean.B3.ActualIntegerizerRange
import Li2Lean.V.Q3IntegerizerBridge

/-!
# q = 3 bridge for the construction-bound rational integerizer

The q = 3 arithmetic file predates the generic B3 rational producer.  This
module transports its actual determinant, exponent and rate interfaces into
that producer.  The only inputs are the two q = 3 construction obligations
(`Q3ActualIntegerizerInputs`); no valuation function or determinant can be
chosen by the caller.

The generic producer quantifies its valuation bound at `n = 0`, although the
v13 index is positive.  At that unused index the exponent is defined as the
negative of the actual Gauss valuation, making the required inequality an
identity.  For every positive index the exponent is exactly the v13 q = 3
exponent from `Q3IntegerizerBridge`.
-/

namespace Li2Lean.B3

noncomputable section

open scoped BigOperators
open Li2Lean.P0.Integerization
open Li2Lean.V.Q3Integerizer

private def q3DenominatorCutoff (n : ℕ) : ℕ :=
  Li2Lean.V.Q3Arithmetic.denominatorCutoff n

private def q3PrimeExponentWithZero (n p : ℕ) : ℤ :=
  if 0 < n then
    q3V13PrimeExponent n p
  else
    -V.actualGaussValuation p (V.actualVDeterminant 3 (4 * n))

private def q3PrimeProductWithZero (n : ℕ) : ℚ :=
  rationalPrimeProduct
    (Nat.primesLE (q3DenominatorCutoff n))
    (q3PrimeExponentWithZero n)

private theorem q3_actual_valuation_eq (n p : ℕ) :
    V.actualGaussValuation p (V.actualVDeterminant 3 (4 * n)) =
      Li2Lean.V.Q3Arithmetic.actualGaussValuation p
        (Li2Lean.V.Q3Arithmetic.actualDeterminant n) := by
  have hpoly : V.actualVDeterminant 3 (4 * n) =
      Li2Lean.V.Q3Arithmetic.actualDeterminant n := by
    simp [V.actualVDeterminant, V.actualDeterminantAt,
      Li2Lean.V.Q3Arithmetic.actualDeterminant,
      Li2Lean.V.Q3Arithmetic.a]
  rw [hpoly]
  by_cases hzero : V.vPolynomial n (-3) = 0
  · have hs : ¬(V.vPolynomial n (-3)).support.Nonempty := by
      simpa [hzero]
    simp [V.actualGaussValuation,
      Li2Lean.V.Q3Arithmetic.actualGaussValuation, hzero, hs]
  · have hs : (V.vPolynomial n (-3)).support.Nonempty :=
      Polynomial.support_nonempty.mpr hzero
    simp [V.actualGaussValuation,
      Li2Lean.V.Q3Arithmetic.actualGaussValuation, hzero, hs]

private theorem q3_prime_exponent_eq_v13 {n p : ℕ} (hn : 0 < n) :
    q3PrimeExponentWithZero n p = q3V13PrimeExponent n p := by
  simp [q3PrimeExponentWithZero, hn]

private theorem q3_valuation_bound
    (h : Li2Lean.V.Q3Integerizer.Q3ActualIntegerizerInputs (vTau 3)) :
    QActualPrimeValuationBound 3 q3PrimeExponentWithZero := by
  intro n p hp
  by_cases hn : 0 < n
  · have hq := h.local_valuation n hn p hp
    rw [q3_actual_valuation_eq]
    simpa [q3PrimeExponentWithZero, hn] using hq
  · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    simp [q3PrimeExponentWithZero]

theorem q3_positive_valuation_of_inputs
    (h : Li2Lean.V.Q3Integerizer.Q3ActualIntegerizerInputs (vTau 3))
    {n p : ℕ} (hn : 0 < n) (hp : p.Prime) :
    V.actualGaussValuation p (V.actualVDeterminant 3 (4 * n)) ≥
      -q3V13PrimeExponent n p := by
  rw [q3_actual_valuation_eq]
  exact h.local_valuation n hn p hp

theorem valuation_bound_of_actual_inputs
    (h : Li2Lean.V.Q3Integerizer.Q3ActualIntegerizerInputs (vTau 3)) :
    QActualPrimeValuationBound 3
      (fun n p => if 0 < n then q3V13PrimeExponent n p
        else -V.actualGaussValuation p (V.actualVDeterminant 3 (4 * n))) := by
  change QActualPrimeValuationBound 3 q3PrimeExponentWithZero
  exact q3_valuation_bound h

private theorem q3_exponent_zero_of_gt_cutoff
    {n p : ℕ} (hn : 0 < n)
    (hp : q3DenominatorCutoff n < p) :
    q3PrimeExponentWithZero n p = 0 := by
  rw [q3_prime_exponent_eq_v13 hn]
  exact q3V13PrimeExponent_eq_zero_of_gtU hn hp

private theorem q3_prime_sum_rate
    (h : Li2Lean.V.Q3Integerizer.Q3ActualIntegerizerInputs (vTau 3)) :
    QV13PrimeSumRate q3DenominatorCutoff q3PrimeExponentWithZero (vTau 3) := by
  intro ε hε
  obtain ⟨N, hN⟩ := h.prime_sum_rate ε hε
  refine ⟨max N 1, ?_⟩
  intro n hn hnpos
  have hNn : N ≤ n := le_trans (Nat.le_max_left N 1) hn
  have hpos : 0 < n := hnpos
  have hq := hN n hNn hpos
  simpa [q3DenominatorCutoff, q3PrimeExponentWithZero, hpos] using hq

/-- Transport the q = 3 actual valuation and PNT inputs into the generic
q-parameterized rational producer. -/
def q3ActualRationalIntegerizerProducer
    (h : Li2Lean.V.Q3Integerizer.Q3ActualIntegerizerInputs (vTau 3)) :
    VActualRationalIntegerizerProducer 3 (vTau 3) :=
  { denominatorCutoff := q3DenominatorCutoff
    primeExponent := q3PrimeExponentWithZero
    D := fun m => q3PrimeProductWithZero (m / 4)
    D_eq_primeProduct := by
      intro n
      simp [q3PrimeProductWithZero, q3DenominatorCutoff]
    valuation_bound := q3_valuation_bound h
    exponent_zero_of_gt_cutoff := by
      intro n p hn hp
      exact q3_exponent_zero_of_gt_cutoff hn hp
    prime_sum_rate := q3_prime_sum_rate h }

theorem q3_arithmetic_plan_of_actual_inputs
    (h : Li2Lean.V.Q3Integerizer.Q3ActualIntegerizerInputs (vTau 3)) :
    ArithmeticPlan 3 :=
  arithmeticPlan_of_actual_rational_producer
    (q3ActualRationalIntegerizerProducer h)

end
end Li2Lean.B3

#print axioms Li2Lean.B3.q3_arithmetic_plan_of_actual_inputs
