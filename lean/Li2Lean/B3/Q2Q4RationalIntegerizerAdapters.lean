/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/

import Li2Lean.B3.ActualRationalIntegerizerProducer
import Li2Lean.B3.ActualIntegerizerRange
import Li2Lean.V.Q2Arithmetic
import Li2Lean.V.Q4Arithmetic

/-!
# q = 2 and q = 4 rational integerizer adapters

This file fixes the v13 ordered exponent for the two composite/exceptional
rows and transports construction-bound valuation and PNT inputs to the common
`VActualRationalIntegerizerProducer`.  The determinant is always the actual
`V.actualVDeterminant`; no valuation function or scalar is supplied by a
caller.  The two input structures are propositions containing only the
remaining coefficientwise valuation and weighted prime-sum obligations.

The formal credits are the v13 credits
`v_p(q) * D_m + v_p(q+1) * m`: for q = 2 they are `D_m` at p = 2 and `m` at
p = 3; for q = 4 they are `2 * D_m` at p = 2 and `m` at p = 5.  In
particular, the old q = 4 one-copy credit is not reused.
-/

namespace Li2Lean.B3

noncomputable section

open scoped BigOperators
open Li2Lean.P0.Integerization

namespace V13Q24Walls

def line (c : ℚ) (b : ℤ) : Prop :=
  (c = 0 ∧ 0 ≤ b) ∨
  (c = -(1 / 4 : ℚ) ∧ 1 ≤ b) ∨
  ((c = 1 / 4 ∨ c = 1 / 2 ∨ c = 3 / 2 ∨ c = 5 / 2) ∧ b ≤ 0)

def active (c : ℚ) (b : ℤ) : Prop :=
  line c b ∧
    ∃ rho : ℚ, (1 / 40 : ℚ) ≤ rho ∧ rho ≤ 5 / 4 ∧
      0 ≤ c + (b : ℚ) * rho ∧ c + (b : ℚ) * rho ≤ rho

def wall40 (rho : ℚ) : Prop :=
  rho = 1 / 40 ∨ rho = 5 / 4 ∨
    (1 / 40 : ℚ) < rho ∧ rho < 5 / 4 ∧
      ∃ c c' : ℚ, ∃ b b' : ℤ,
        active c b ∧ active c' b' ∧ b ≠ b' ∧
          (b' : ℚ) * rho - (b : ℚ) * rho = c - c'

end V13Q24Walls

namespace Q2RationalIntegerizer

open Li2Lean.V

def exponent (n p : ℕ) : ℤ :=
  letI : Decidable (V13Q24Walls.wall40 (Q2Arithmetic.rho n p)) :=
    Classical.propDecidable _
  if p = 2 then
    Q2Arithmetic.naturalExponent n p - Q2Arithmetic.formalDivisorExponent n
  else if p = 3 then
    Q2Arithmetic.naturalExponent n p - Q2Arithmetic.mSize n
  else if Q2Arithmetic.denominatorCutoff n < p then 0
  else if 40 * p ≤ Q2Arithmetic.mSize n then
    Q2Arithmetic.naturalExponent n p
  else if p ^ 2 ≤ max (Q2Arithmetic.numeratorCutoff n)
      (Q2Arithmetic.denominatorCutoff n) then
    Q2Arithmetic.naturalExponent n p
  else if V13Q24Walls.wall40 (Q2Arithmetic.rho n p) then
    Q2Arithmetic.naturalExponent n p
  else if (1 / 40 : ℚ) < Q2Arithmetic.rho n p ∧
      Q2Arithmetic.rho n p < 5 / 4 then
    (Q2Arithmetic.mSize n : ℤ) +
      ∑ u ∈ Finset.range p, (Q2Arithmetic.profileRank n p u : ℤ)
  else if 5 * n < p ∧ p ≤ Q2Arithmetic.denominatorCutoff n then
    Q2Arithmetic.outerExponent n p
  else 0

private def exponentWithZero (n p : ℕ) : ℤ :=
  if 0 < n then exponent n p
  else -V.actualGaussValuation p (V.actualVDeterminant 2 (4 * n))

private def primeProduct (n : ℕ) : ℚ :=
  rationalPrimeProduct (Nat.primesLE (Q2Arithmetic.denominatorCutoff n))
    (exponentWithZero n)

def ActualInputs (tau : ℝ) : Prop :=
  (∀ n : ℕ, 0 < n →
    ∀ p : ℕ, p.Prime →
      V.actualGaussValuation p (V.actualVDeterminant 2 (4 * n)) ≥
        -exponent n p) ∧
  QV13PrimeSumRate Q2Arithmetic.denominatorCutoff exponentWithZero tau

private theorem exponent_zero_of_gt_cutoff {n p : ℕ} (hn : 0 < n)
    (hp : Q2Arithmetic.denominatorCutoff n < p) : exponent n p = 0 := by
  have hp2 : p ≠ 2 := by
    intro h
    subst p
    simp [Q2Arithmetic.denominatorCutoff] at hp
    omega
  have hp3 : p ≠ 3 := by
    intro h
    subst p
    simp [Q2Arithmetic.denominatorCutoff] at hp
    omega
  simp [exponent, hp2, hp3, hp]

private theorem valuation_bound (h : ActualInputs (vTau 2)) :
    QActualPrimeValuationBound 2 exponentWithZero := by
  intro n p hp
  by_cases hn : 0 < n
  · simpa [exponentWithZero, hn] using h.1 n hn p hp
  · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    simp [exponentWithZero]

theorem valuation_bound_of_actual_inputs (h : ActualInputs (vTau 2)) :
    QActualPrimeValuationBound 2
      (fun n p => if 0 < n then exponent n p
        else -V.actualGaussValuation p (V.actualVDeterminant 2 (4 * n))) := by
  change QActualPrimeValuationBound 2 exponentWithZero
  exact valuation_bound h

private theorem prime_sum_rate (h : ActualInputs (vTau 2)) :
    QV13PrimeSumRate Q2Arithmetic.denominatorCutoff exponentWithZero (vTau 2) :=
  h.2

def actualProducer (h : ActualInputs (vTau 2)) :
    VActualRationalIntegerizerProducer 2 (vTau 2) :=
  { denominatorCutoff := Q2Arithmetic.denominatorCutoff
    primeExponent := exponentWithZero
    D := fun m => primeProduct (m / 4)
    D_eq_primeProduct := by
      intro n
      simp [primeProduct]
    valuation_bound := valuation_bound h
    exponent_zero_of_gt_cutoff := by
      intro n p hn hp
      simp [exponentWithZero, hn, exponent_zero_of_gt_cutoff hn hp]
    prime_sum_rate := prime_sum_rate h }

theorem arithmetic_plan_of_actual_inputs (h : ActualInputs (vTau 2)) :
    ArithmeticPlan 2 :=
  arithmeticPlan_of_actual_rational_producer (actualProducer h)

end Q2RationalIntegerizer

namespace Q4RationalIntegerizer

open Li2Lean.V

def exponent (n p : ℕ) : ℤ :=
  letI : Decidable (V13Q24Walls.wall40 (Q4Arithmetic.rho n p)) :=
    Classical.propDecidable _
  if p = 2 then
    Q4Arithmetic.naturalExponent n p -
      (2 * Q4Arithmetic.formalDivisorExponent n : ℕ)
  else if p = 5 then
    Q4Arithmetic.naturalExponent n p - Q4Arithmetic.mSize n
  else if Q4Arithmetic.denominatorCutoff n < p then 0
  else if 40 * p ≤ Q4Arithmetic.mSize n then
    Q4Arithmetic.naturalExponent n p
  else if p ^ 2 ≤ max (Q4Arithmetic.numeratorCutoff n)
      (Q4Arithmetic.denominatorCutoff n) then
    Q4Arithmetic.naturalExponent n p
  else if V13Q24Walls.wall40 (Q4Arithmetic.rho n p) then
    Q4Arithmetic.naturalExponent n p
  else if (1 / 40 : ℚ) < Q4Arithmetic.rho n p ∧
      Q4Arithmetic.rho n p < 5 / 4 then
    (Q4Arithmetic.mSize n : ℤ) +
      ∑ u ∈ Finset.range p, (Q4Arithmetic.profileRank n p u : ℤ)
  else if 5 * n < p ∧ p ≤ Q4Arithmetic.denominatorCutoff n then
    Q4Arithmetic.outerExponent n p
  else 0

private def exponentWithZero (n p : ℕ) : ℤ :=
  if 0 < n then exponent n p
  else -V.actualGaussValuation p (V.actualVDeterminant 4 (4 * n))

private def primeProduct (n : ℕ) : ℚ :=
  rationalPrimeProduct (Nat.primesLE (Q4Arithmetic.denominatorCutoff n))
    (exponentWithZero n)

def ActualInputs (tau : ℝ) : Prop :=
  (∀ n : ℕ, 0 < n →
    ∀ p : ℕ, p.Prime →
      V.actualGaussValuation p (V.actualVDeterminant 4 (4 * n)) ≥
        -exponent n p) ∧
  QV13PrimeSumRate Q4Arithmetic.denominatorCutoff exponentWithZero tau

private theorem exponent_zero_of_gt_cutoff {n p : ℕ} (hn : 0 < n)
    (hp : Q4Arithmetic.denominatorCutoff n < p) : exponent n p = 0 := by
  have hp2 : p ≠ 2 := by
    intro h
    subst p
    simp [Q4Arithmetic.denominatorCutoff] at hp
    omega
  have hp5 : p ≠ 5 := by
    intro h
    subst p
    simp [Q4Arithmetic.denominatorCutoff] at hp
    omega
  simp [exponent, hp2, hp5, hp]

private theorem valuation_bound (h : ActualInputs (vTau 4)) :
    QActualPrimeValuationBound 4 exponentWithZero := by
  intro n p hp
  by_cases hn : 0 < n
  · simpa [exponentWithZero, hn] using h.1 n hn p hp
  · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    simp [exponentWithZero]

theorem valuation_bound_of_actual_inputs (h : ActualInputs (vTau 4)) :
    QActualPrimeValuationBound 4
      (fun n p => if 0 < n then exponent n p
        else -V.actualGaussValuation p (V.actualVDeterminant 4 (4 * n))) := by
  change QActualPrimeValuationBound 4 exponentWithZero
  exact valuation_bound h

private theorem prime_sum_rate (h : ActualInputs (vTau 4)) :
    QV13PrimeSumRate Q4Arithmetic.denominatorCutoff exponentWithZero (vTau 4) :=
  h.2

def actualProducer (h : ActualInputs (vTau 4)) :
    VActualRationalIntegerizerProducer 4 (vTau 4) :=
  { denominatorCutoff := Q4Arithmetic.denominatorCutoff
    primeExponent := exponentWithZero
    D := fun m => primeProduct (m / 4)
    D_eq_primeProduct := by
      intro n
      simp [primeProduct]
    valuation_bound := valuation_bound h
    exponent_zero_of_gt_cutoff := by
      intro n p hn hp
      simp [exponentWithZero, hn, exponent_zero_of_gt_cutoff hn hp]
    prime_sum_rate := prime_sum_rate h }

theorem arithmetic_plan_of_actual_inputs (h : ActualInputs (vTau 4)) :
    ArithmeticPlan 4 :=
  arithmeticPlan_of_actual_rational_producer (actualProducer h)

end Q4RationalIntegerizer

end
end Li2Lean.B3

#print axioms Li2Lean.B3.Q2RationalIntegerizer.arithmetic_plan_of_actual_inputs
#print axioms Li2Lean.B3.Q4RationalIntegerizer.arithmetic_plan_of_actual_inputs
