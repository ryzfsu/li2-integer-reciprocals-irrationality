/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B3.ActualRationalIntegerizerProducer
import Li2Lean.B3.ArithmeticPinning
import Li2Lean.V.Q5Certificate
import Li2Lean.V.Q5ActualSeed
import Li2Lean.V.Q6Arithmetic
import Li2Lean.V.Q7Arithmetic

/-!
Construction-bound arithmetic contracts for the signed `V` determinants at
`q = 5, 6, 7`.

The exponent at an exceptional prime is
`3*m*floor(log_p N) + n*floor(log_p U) - v_p(q)*D_n - v_p(q+1)*m`,
with `m = 4*n`. The coefficientwise and PNT parts remain explicit producer
inputs; this module does not manufacture either estimate.

The q = 7 rule is written separately because the older q7 interface
interchanged the q and q+1 credits.
-/

namespace Li2Lean.B3

noncomputable section
open scoped BigOperators
open Li2Lean.P0.Integerization

def q567NumeratorCutoff (n : ℕ) : ℕ := 10 * n - 1
def q567DenominatorCutoff (n : ℕ) : ℕ := 11 * n - 1
def q567FormalDivisorExponent (n : ℕ) : ℕ :=
  (53 * n ^ 2 + 2) / 3 - 4 * n
def q567NaturalExponent (n p : ℕ) : ℤ :=
  ((3 * (4 * n) * Nat.log p (q567NumeratorCutoff n) +
      n * Nat.log p (q567DenominatorCutoff n) : ℕ) : ℤ)

def q5FormalCredit (n p : ℕ) : ℤ :=
  if p = 5 then (q567FormalDivisorExponent n : ℤ)
  else if p = 2 ∨ p = 3 then (4 * n : ℤ)
  else 0

def q6FormalCredit (n p : ℕ) : ℤ :=
  if p = 2 ∨ p = 3 then (q567FormalDivisorExponent n : ℤ)
  else if p = 7 then (4 * n : ℤ)
  else 0

/-- For q = 7, p = 2 divides q+1 = 8 with valuation three. -/
def q7FormalCreditV13 (n p : ℕ) : ℤ :=
  if p = 7 then (q567FormalDivisorExponent n : ℤ)
  else if p = 2 then (3 * (4 * n) : ℤ)
  else 0

theorem q5FormalCredit_at_exceptions (n : ℕ) :
    q5FormalCredit n 2 = (4 * n : ℤ) ∧
      q5FormalCredit n 3 = (4 * n : ℤ) ∧
      q5FormalCredit n 5 = (q567FormalDivisorExponent n : ℤ) := by
  simp [q5FormalCredit]

theorem q6FormalCredit_at_exceptions (n : ℕ) :
    q6FormalCredit n 2 = (q567FormalDivisorExponent n : ℤ) ∧
      q6FormalCredit n 3 = (q567FormalDivisorExponent n : ℤ) ∧
      q6FormalCredit n 7 = (4 * n : ℤ) := by
  simp [q6FormalCredit]

theorem q7FormalCreditV13_at_exceptions (n : ℕ) :
    q7FormalCreditV13 n 2 = (3 * (4 * n) : ℤ) ∧
      q7FormalCreditV13 n 7 = (q567FormalDivisorExponent n : ℤ) := by
  simp [q7FormalCreditV13]

theorem q7FormalCreditV13_eq_corrected_interface (n p : ℕ) :
    q7FormalCreditV13 n p = V.Q7Arithmetic.q7FormalCredit n p := by
  simp [q7FormalCreditV13, q567FormalDivisorExponent,
    V.Q7Arithmetic.q7FormalCredit,
    V.Q7Arithmetic.formalDivisorExponent, V.Q7Arithmetic.mSize, V.vM]

def q5TargetExponent (n p : ℕ) : ℤ :=
  if p = 2 ∨ p = 3 ∨ p = 5 then
    q567NaturalExponent n p - q5FormalCredit n p
  else if q567DenominatorCutoff n < p then 0
  else if 5 * n < p then V.Q5Certificate.q5OuterCost n p
  else if max (q567NumeratorCutoff n) (q567DenominatorCutoff n) < p ^ 2 then
    V.Q5Certificate.q5ResidueExponent (4 * n) p
  else q567NaturalExponent n p

def q6TargetExponent (n p : ℕ) : ℤ :=
  if p = 2 ∨ p = 3 ∨ p = 7 then
    q567NaturalExponent n p - q6FormalCredit n p
  else if q567DenominatorCutoff n < p then 0
  else if 5 * n < p then V.Q6Arithmetic.outerExponent n p
  else if max (q567NumeratorCutoff n) (q567DenominatorCutoff n) < p ^ 2 then
    V.Q6Arithmetic.residueExponent n p
  else q567NaturalExponent n p

def q7TargetExponent (n p : ℕ) : ℤ :=
  if p = 2 ∨ p = 7 then
    q567NaturalExponent n p - q7FormalCreditV13 n p
  else if q567DenominatorCutoff n < p then 0
  else if 5 * n < p then V.Q7Arithmetic.outerExponent n p
  else if max (q567NumeratorCutoff n) (q567DenominatorCutoff n) < p ^ 2 then
    V.Q7Arithmetic.residueExponent n p
  else q567NaturalExponent n p

theorem q7TargetExponent_two (n : ℕ) :
    q7TargetExponent n 2 =
      q567NaturalExponent n 2 - (3 * (4 * n) : ℤ) := by
  simp [q7TargetExponent, q7FormalCreditV13]

theorem q7TargetExponent_seven (n : ℕ) :
    q7TargetExponent n 7 =
      q567NaturalExponent n 7 - (q567FormalDivisorExponent n : ℤ) := by
  simp [q7TargetExponent, q7FormalCreditV13]

def q5ActualGaussValuation (n p : ℕ) : ℤ :=
  V.actualGaussValuation p (V.actualVDeterminant 5 (4 * n))
def q6ActualGaussValuation (n p : ℕ) : ℤ :=
  V.actualGaussValuation p (V.actualVDeterminant 6 (4 * n))
def q7ActualGaussValuation (n p : ℕ) : ℤ :=
  V.actualGaussValuation p (V.actualVDeterminant 7 (4 * n))

def Q5CoefficientValuationInput : Prop :=
  ∀ n p : ℕ, Nat.Prime p →
    q5ActualGaussValuation n p ≥ -q5TargetExponent n p
def Q6CoefficientValuationInput : Prop :=
  ∀ n p : ℕ, Nat.Prime p →
    q6ActualGaussValuation n p ≥ -q6TargetExponent n p
def Q7CoefficientValuationInput : Prop :=
  ∀ n p : ℕ, Nat.Prime p →
    q7ActualGaussValuation n p ≥ -q7TargetExponent n p

def Q5PrimeSumRateInput (tau : ℝ) : Prop :=
  QV13PrimeSumRate q567DenominatorCutoff
    (fun n p => q5TargetExponent n p) tau
def Q6PrimeSumRateInput (tau : ℝ) : Prop :=
  QV13PrimeSumRate q567DenominatorCutoff
    (fun n p => q6TargetExponent n p) tau
def Q7PrimeSumRateInput (tau : ℝ) : Prop :=
  QV13PrimeSumRate q567DenominatorCutoff
    (fun n p => q7TargetExponent n p) tau

theorem q5_target_inputs_are_exact
    (hval : Q5CoefficientValuationInput)
    (hrate : Q5PrimeSumRateInput (vTau 5)) :
    QActualPrimeValuationBound 5 (fun n p => q5TargetExponent n p) ∧
      QV13PrimeSumRate q567DenominatorCutoff
        (fun n p => q5TargetExponent n p) (vTau 5) := by
  exact ⟨hval, hrate⟩

theorem q6_target_inputs_are_exact
    (hval : Q6CoefficientValuationInput)
    (hrate : Q6PrimeSumRateInput (vTau 6)) :
    QActualPrimeValuationBound 6 (fun n p => q6TargetExponent n p) ∧
      QV13PrimeSumRate q567DenominatorCutoff
        (fun n p => q6TargetExponent n p) (vTau 6) := by
  exact ⟨hval, hrate⟩

theorem q7_target_inputs_are_exact
    (hval : Q7CoefficientValuationInput)
    (hrate : Q7PrimeSumRateInput (vTau 7)) :
    QActualPrimeValuationBound 7 (fun n p => q7TargetExponent n p) ∧
      QV13PrimeSumRate q567DenominatorCutoff
        (fun n p => q7TargetExponent n p) (vTau 7) := by
  exact ⟨hval, hrate⟩

/-! ## Prime-product adapters

These constructors turn the honest q-specific inputs into the generic
construction-bound producer.  The divisor is the explicit v13 prime product;
the constructors do not prove either input field.
-/

def q567PrimeProduct (E : ℕ → ℕ → ℤ) (n : ℕ) : ℚ :=
  rationalPrimeProduct (Nat.primesLE (q567DenominatorCutoff n)) (E n)

theorem q567PrimeProduct_pos (E : ℕ → ℕ → ℤ) (n : ℕ) :
    0 < q567PrimeProduct E n := by
  exact rationalPrimeProduct_pos _ _ (fun p hp => Nat.prime_of_mem_primesLE hp)

noncomputable def q5Producer_of_inputs
    (hval : Q5CoefficientValuationInput)
    (hrate : Q5PrimeSumRateInput (vTau 5)) :
    VActualRationalIntegerizerProducer 5 (vTau 5) := by
  let E := fun n p => q5TargetExponent n p
  refine
    { denominatorCutoff := q567DenominatorCutoff
      primeExponent := E
      D := fun m => q567PrimeProduct E (m / 4)
      D_eq_primeProduct := by
        intro n
        simp [q567PrimeProduct,
          Nat.mul_div_cancel_left n (by norm_num : (0 : ℕ) < 4)]
      valuation_bound := ?_
      exponent_zero_of_gt_cutoff := ?_
      prime_sum_rate := ?_ }
  · simpa [E, Q5CoefficientValuationInput, q5ActualGaussValuation,
      QActualPrimeValuationBound] using hval
  · intro n p hn hp
    have hp2 : p ≠ 2 := by
      intro h; subst p
      simp [q567DenominatorCutoff] at hp
      omega
    have hp3 : p ≠ 3 := by
      intro h; subst p
      simp [q567DenominatorCutoff] at hp
      omega
    have hp5 : p ≠ 5 := by
      intro h; subst p
      simp [q567DenominatorCutoff] at hp
      omega
    simp [E, q5TargetExponent, hp, hp2, hp3, hp5]
  · exact hrate

noncomputable def q6Producer_of_inputs
    (hval : Q6CoefficientValuationInput)
    (hrate : Q6PrimeSumRateInput (vTau 6)) :
    VActualRationalIntegerizerProducer 6 (vTau 6) := by
  let E := fun n p => q6TargetExponent n p
  refine
    { denominatorCutoff := q567DenominatorCutoff
      primeExponent := E
      D := fun m => q567PrimeProduct E (m / 4)
      D_eq_primeProduct := by
        intro n
        simp [q567PrimeProduct,
          Nat.mul_div_cancel_left n (by norm_num : (0 : ℕ) < 4)]
      valuation_bound := ?_
      exponent_zero_of_gt_cutoff := ?_
      prime_sum_rate := ?_ }
  · simpa [E, Q6CoefficientValuationInput, q6ActualGaussValuation,
      QActualPrimeValuationBound] using hval
  · intro n p hn hp
    have hp2 : p ≠ 2 := by
      intro h; subst p
      simp [q567DenominatorCutoff] at hp
      omega
    have hp3 : p ≠ 3 := by
      intro h; subst p
      simp [q567DenominatorCutoff] at hp
      omega
    have hp7 : p ≠ 7 := by
      intro h; subst p
      simp [q567DenominatorCutoff] at hp
      omega
    simp [E, q6TargetExponent, hp, hp2, hp3, hp7]
  · exact hrate

noncomputable def q7Producer_of_inputs
    (hval : Q7CoefficientValuationInput)
    (hrate : Q7PrimeSumRateInput (vTau 7)) :
    VActualRationalIntegerizerProducer 7 (vTau 7) := by
  let E := fun n p => q7TargetExponent n p
  refine
    { denominatorCutoff := q567DenominatorCutoff
      primeExponent := E
      D := fun m => q567PrimeProduct E (m / 4)
      D_eq_primeProduct := by
        intro n
        simp [q567PrimeProduct,
          Nat.mul_div_cancel_left n (by norm_num : (0 : ℕ) < 4)]
      valuation_bound := ?_
      exponent_zero_of_gt_cutoff := ?_
      prime_sum_rate := ?_ }
  · simpa [E, Q7CoefficientValuationInput, q7ActualGaussValuation,
      QActualPrimeValuationBound] using hval
  · intro n p hn hp
    have hp2 : p ≠ 2 := by
      intro h; subst p
      simp [q567DenominatorCutoff] at hp
      omega
    have hp7 : p ≠ 7 := by
      intro h; subst p
      simp [q567DenominatorCutoff] at hp
      omega
    simp [E, q7TargetExponent, hp, hp2, hp7]
  · exact hrate

end
end Li2Lean.B3

#print axioms Li2Lean.B3.q7FormalCreditV13_eq_corrected_interface
#print axioms Li2Lean.B3.q5_target_inputs_are_exact
#print axioms Li2Lean.B3.q6_target_inputs_are_exact
#print axioms Li2Lean.B3.q7_target_inputs_are_exact
#print axioms Li2Lean.B3.q5Producer_of_inputs
#print axioms Li2Lean.B3.q6Producer_of_inputs
#print axioms Li2Lean.B3.q7Producer_of_inputs
