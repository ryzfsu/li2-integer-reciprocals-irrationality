/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/

import Li2Lean.P0.ActualRationalIntegerizerProducer
import Li2Lean.P0.IntegerizationFormalBaseParam
import Li2Lean.P0.RateDetValuation

namespace Li2Lean.P0

noncomputable section

open scoped BigOperators
open PositiveBase
open Li2Lean.P0.Integerization

/-!
## Named leaves for the positive-base integerizer

This file is an obligation-first interface. The existential plan below
contains the actual denominator and exponent data, while each coefficient,
degree, and rate estimate remains a separately named proposition. In
particular, no `Prop` structure stores Type-valued certificate data.
-/

def p0FormalDivisorCoeff (q m p i : ℕ) : Prop :=
  (p0CanonicalPolynomial (q : ℤ) m).coeff i = 0 ∨
    -(formalDivisorCredit q m p) ≤
      padicValRat p ((p0CanonicalPolynomial (q : ℤ) m).coeff i)

def p0PoleCoeff (q m p i : ℕ) : Prop :=
  p0FormalDivisorCoeff q m p i

def p0FormalBaseCoeff (q m p i : ℕ) : Prop :=
  p0FormalDivisorCoeff q m p i

def p0MovingCoeff (movingExponent : ℕ → ℕ → ℤ)
    (q m p i : ℕ) : Prop :=
  (p0CanonicalPolynomial (q : ℤ) m).coeff i = 0 ∨
    -(movingExponent m p) ≤
      padicValRat p ((p0CanonicalPolynomial (q : ℤ) m).coeff i)

def p0QAdicCoeff (movingExponent : ℕ → ℕ → ℤ)
    (q m p i : ℕ) : Prop :=
  p0MovingCoeff movingExponent q m p i

def p0MovingPrimeCoeff (movingExponent : ℕ → ℕ → ℤ)
    (q m p i : ℕ) : Prop :=
  p0MovingCoeff movingExponent q m p i

/-! The exceptional-prime and ordinary-prime leaves are deliberately
separate. The proof is purely a case split; the two leaves are where the
pole corollary and `IntegerizationFormalBaseParam` port are supplied. -/
theorem p0FormalDivisorCoeff_of_leaves
    (q : ℕ) (m p i : ℕ) (hm : 0 < m) (h4 : 4 ∣ m)
    (hp : p.Prime)
    (hPole : p ∣ q * (q - 1) → p0PoleCoeff q m p i)
    (hBase : ¬ p ∣ q * (q - 1) → p0FormalBaseCoeff q m p i) :
    p0FormalDivisorCoeff q m p i := by
  by_cases hex : p ∣ q * (q - 1)
  · exact hPole hex
  · exact hBase hex

/-! ### The q - 1 exceptional branch

The ordinary q-adic branch only assumes p does not divide q; it must not
infer p does not divide q * (q - 1), since a prime can divide q - 1 (for
example q = 3, p = 2). These arithmetic bridges keep the pole credit
explicit and are used before applying the two coefficient leaves. -/

theorem p0Prime_dvd_q_mul_qSubOne_iff {p q : ℕ} (hp : p.Prime) :
    p ∣ q * (q - 1) ↔ p ∣ q ∨ p ∣ q - 1 :=
  hp.dvd_mul

theorem p0Prime_dvd_qSubOne_of_dvd_product {p q : ℕ} (hp : p.Prime)
    (hpq : ¬ p ∣ q) (hprod : p ∣ q * (q - 1)) :
    p ∣ q - 1 := by
  exact (hp.dvd_mul.mp hprod).resolve_left hpq

theorem p0PadicValNat_q_mul_qSubOne_of_not_dvd_q {p q : ℕ}
    (hp : p.Prime) (hpq : ¬ p ∣ q) :
    padicValNat p (q * (q - 1)) = padicValNat p (q - 1) := by
  letI : Fact p.Prime := ⟨hp⟩
  by_cases hq1 : q - 1 = 0
  · simp [hq1]
  have hq : q ≠ 0 := by
    intro hq
    apply hpq
    simp [hq]
  rw [padicValNat.mul hq hq1,
    padicValNat.eq_zero_of_not_dvd hpq, zero_add]

theorem formalDivisorCredit_of_not_dvd_q (q m p : ℕ)
    (hpq : ¬ p ∣ q) :
    formalDivisorCredit q m p =
      ((3 * m * Nat.log p (formalDivisorCutoff m) : ℕ) : ℤ) +
        formalDivisorH m * (padicValNat p (q - 1) : ℤ) := by
  unfold formalDivisorCredit
  rw [padicValNat.eq_zero_of_not_dvd hpq]
  simp

theorem p0Exceptional_qSubOne_credit {p q m : ℕ} (hp : p.Prime)
    (hpq : ¬ p ∣ q) (hprod : p ∣ q * (q - 1)) :
    p ∣ q - 1 ∧
      formalDivisorCredit q m p =
        ((3 * m * Nat.log p (formalDivisorCutoff m) : ℕ) : ℤ) +
          formalDivisorH m * (padicValNat p (q - 1) : ℤ) := by
  exact ⟨p0Prime_dvd_qSubOne_of_dvd_product hp hpq hprod,
    formalDivisorCredit_of_not_dvd_q q m p hpq⟩

theorem p0MovingCoeff_of_leaves
    (movingExponent : ℕ → ℕ → ℤ)
    (q : ℕ) (m p i : ℕ) (hm : 0 < m) (h4 : 4 ∣ m)
    (hp : p.Prime)
    (hQ : p ∣ q → p0QAdicCoeff movingExponent q m p i)
    (hMoving : ¬ p ∣ q → p0MovingPrimeCoeff movingExponent q m p i) :
    p0MovingCoeff movingExponent q m p i := by
  by_cases hq : p ∣ q
  · exact hQ hq
  · exact hMoving hq

/-! ### Generic witness data

The four existential fields of `P0IntegerizerProofPlan` are independent of
the coefficient, degree, and rate leaves below. The cutoff includes the
fixed base factors, while the exponent is the minimum of the formal divisor
credit and the moving-prime budget. -/

noncomputable def p0IntegerizerCutoff (q m : ℕ) : ℕ :=
  formalDivisorCutoff m + q

noncomputable def p0IntegerizerMovingExponent (q m p : ℕ) : ℤ :=
  if p ∣ q * (q - 1) then
    formalDivisorCredit q m p
  else if p ≤ formalDivisorCutoff m then
    min (p0RateW m p)
      (((3 * m * Nat.log p (formalDivisorCutoff m) : ℕ) : ℤ))
  else 0

noncomputable def p0IntegerizerExponent (q m p : ℕ) : ℤ :=
  min (formalDivisorCredit q m p) (p0IntegerizerMovingExponent q m p)

noncomputable def p0IntegerizerDenominator (q m : ℕ) : ℚ :=
  rationalPrimeProduct (Nat.primesLE (p0IntegerizerCutoff q m))
    (p0IntegerizerExponent q m)

theorem p0IntegerizerPlanData (q : ℕ) (h3 : 3 ≤ q) :
    ∃ (cutoff : ℕ → ℕ) (movingExponent : ℕ → ℕ → ℤ)
        (exponent : ℕ → ℕ → ℤ) (D : ℕ → ℚ),
      (∀ m : ℕ, 0 < m → 4 ∣ m →
        formalDivisorCutoff m ≤ cutoff m) ∧
      (∀ m p : ℕ,
        exponent m p = min (formalDivisorCredit q m p) (movingExponent m p)) ∧
      (∀ m p : ℕ, 0 < m → 4 ∣ m → cutoff m < p → exponent m p = 0) ∧
      (∀ m : ℕ, 0 < m → 4 ∣ m →
        D m = rationalPrimeProduct (Nat.primesLE (cutoff m)) (exponent m)) := by
  refine ⟨p0IntegerizerCutoff q, p0IntegerizerMovingExponent q,
    p0IntegerizerExponent q, p0IntegerizerDenominator q, ?_, ?_, ?_, ?_⟩
  · intro m _ _
    simp only [p0IntegerizerCutoff]
    omega
  · intro m p
    rfl
  · intro m p hm h4 hcut
    have hU : formalDivisorCutoff m < p := by
      dsimp [p0IntegerizerCutoff] at hcut
      omega
    have hq : q < p := by
      dsimp [p0IntegerizerCutoff] at hcut
      omega
    have hpq : ¬ p ∣ q := by
      intro hd
      have hp_le : p ≤ q := Nat.le_of_dvd (by omega) hd
      omega
    have hpq1 : ¬ p ∣ q - 1 := by
      intro hd
      have hp_le : p ≤ q - 1 := Nat.le_of_dvd (by omega) hd
      omega
    have hvq : padicValNat p q = 0 :=
      padicValNat.eq_zero_of_not_dvd hpq
    have hvq1 : padicValNat p (q - 1) = 0 :=
      padicValNat.eq_zero_of_not_dvd hpq1
    have hlog : Nat.log p (formalDivisorCutoff m) = 0 :=
      Nat.log_of_lt hU
    have hcredit : formalDivisorCredit q m p = 0 := by
      simp [formalDivisorCredit, hlog, hvq, hvq1]
    have hmoving : p0IntegerizerMovingExponent q m p = 0 := by
      unfold p0IntegerizerMovingExponent
      by_cases hex : p ∣ q * (q - 1)
      · simp [hex, hcredit]
      · have hnotU : ¬ p ≤ formalDivisorCutoff m := Nat.not_le.mpr hU
        simp [hex, hnotU]
    simp [p0IntegerizerExponent, hcredit, hmoving]
  · intro m _ _
    rfl

/-! A Prop-valued plan. The four existential values are the actual
denominator construction; all remaining components are named leaves. -/
def P0IntegerizerProofPlan (q : ℕ) (rate : ℝ) : Prop :=
  ∃ (cutoff : ℕ → ℕ) (movingExponent : ℕ → ℕ → ℤ)
      (exponent : ℕ → ℕ → ℤ) (D : ℕ → ℚ),
    (∀ m : ℕ, 0 < m → 4 ∣ m → formalDivisorCutoff m ≤ cutoff m) ∧
    (∀ m p : ℕ,
      exponent m p = min (formalDivisorCredit q m p) (movingExponent m p)) ∧
    (∀ m p : ℕ, 0 < m → 4 ∣ m → cutoff m < p → exponent m p = 0) ∧
    (∀ m : ℕ, 0 < m → 4 ∣ m →
      D m = rationalPrimeProduct (Nat.primesLE (cutoff m)) (exponent m)) ∧
    (∀ m p i : ℕ, 0 < m → 4 ∣ m → p.Prime →
      p ∣ q * (q - 1) → p0PoleCoeff q m p i) ∧
    (∀ m p i : ℕ, 0 < m → 4 ∣ m → p.Prime →
      ¬ p ∣ q * (q - 1) → p0FormalBaseCoeff q m p i) ∧
    (∀ m p i : ℕ, 0 < m → 4 ∣ m → p.Prime →
      p ∣ q → p0QAdicCoeff movingExponent q m p i) ∧
    (∀ m p i : ℕ, 0 < m → 4 ∣ m → p.Prime →
      ¬ p ∣ q → p0MovingPrimeCoeff movingExponent q m p i) ∧
    (∀ m : ℕ, 0 < m → 4 ∣ m →
      ((p0CanonicalPolynomial (q : ℤ) m).map (algebraMap ℚ ℝ)).natDegree ≤ m) ∧
    (∀ ε : ℝ, 0 < ε → ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
      0 < m → 4 ∣ m →
        (∑ p ∈ Nat.primesLE (cutoff m),
          (exponent m p : ℝ) * Real.log p) / (m : ℝ) ^ 2 ≤ rate + ε)

/-- Convert a fully proved actual rational-integerizer producer into the
proposition-valued plan consumed by the AllN producer.  This is a structural
repackaging: the coefficient, degree, and rate fields remain exactly the
producer's fields, while the plan's exceptional/ordinary and q-adic/moving
splits are discharged by the corresponding case hypotheses. -/
theorem proofPlan_of_actual_producer
    {q : ℕ} {hq : InRange (q : ℤ)} {rate : ℝ}
    (P : ActualRationalIntegerizerProducer q hq rate) :
    P0IntegerizerProofPlan q rate := by
  refine ⟨P.cutoff, P.movingExponent, P.exponent, P.D,
    P.cutoff_ge_formal, P.exponent_eq_min,
    P.exponent_zero_of_gt_cutoff, P.D_eq_primeProduct, ?_, ?_, ?_, ?_,
    P.degree_bound, P.pnt_rate⟩
  · intro m p i hm h4 hp hprod
    exact P.formal_divisor_coeff m hm h4 p hp i
  · intro m p i hm h4 hp hprod
    exact P.formal_divisor_coeff m hm h4 p hp i
  · intro m p i hm h4 hp hqdiv
    exact P.moving_coeff m hm h4 p hp i
  · intro m p i hm h4 hp hqndiv
    exact P.moving_coeff m hm h4 p hp i

theorem integerizerBoundAt_of_proof_plan
    {q : ℕ} {hq : InRange (q : ℤ)} {rate : ℝ}
    (plan : P0IntegerizerProofPlan q rate) :
    P0IntegerizerBoundAt (family (q : ℤ) hq) rate := by
  rcases plan with ⟨cutoff, movingExponent, exponent, D,
    hcut, hmin, hzero, hD, hPole, hBase, hQ, hMoving, hdegree, hrate⟩
  let P : ActualRationalIntegerizerProducer q hq rate :=
    { cutoff := cutoff
      movingExponent := movingExponent
      exponent := exponent
      D := D
      cutoff_ge_formal := hcut
      exponent_eq_min := hmin
      exponent_zero_of_gt_cutoff := hzero
      D_eq_primeProduct := hD
      formal_divisor_coeff := by
        intro m hm h4 p hp i
        exact p0FormalDivisorCoeff_of_leaves q m p i hm h4 hp
          (hPole m p i hm h4 hp) (hBase m p i hm h4 hp)
      moving_coeff := by
        intro m hm h4 p hp i
        exact p0MovingCoeff_of_leaves movingExponent q m p i hm h4 hp
          (hQ m p i hm h4 hp) (hMoving m p i hm h4 hp)
      degree_bound := hdegree
      pnt_rate := hrate }
  exact integerizerBoundAt_of_actual_producer P

end

end Li2Lean.P0

namespace Li2Lean.P0
noncomputable section
open Li2Lean.P0.Integerization

/-- Away from the fixed exceptional primes, the generic plan exponent is
exactly the settled q=2 moving exponent below the paper's cutoff. -/
theorem p0IntegerizerExponent_eq_settled_of_not_dvd
    (q m p : ℕ) (hex : ¬ p ∣ q * (q-1))
    (hpU : p ≤ formalDivisorCutoff m) :
    p0IntegerizerExponent q m p =
      min (p0RateW m p) (((3*m*Nat.log p (formalDivisorCutoff m) : ℕ) : ℤ)) := by
  have hpq : ¬ p ∣ q := fun h => hex (dvd_mul_of_dvd_left h _)
  have hpq1 : ¬ p ∣ q-1 := fun h => hex (dvd_mul_of_dvd_right h _)
  simp only [p0IntegerizerExponent, p0IntegerizerMovingExponent,
    if_neg hex, if_pos hpU, formalDivisorCredit,
    padicValNat.eq_zero_of_not_dvd hpq, padicValNat.eq_zero_of_not_dvd hpq1,
    Nat.cast_zero, mul_zero, add_zero, sub_zero]
  exact min_eq_right (min_le_right _ _)

/-- The nonsquarefull range eventually excludes every exceptional base
prime. This uses only the fixed-base size, not coefficient arithmetic. -/
theorem p0Integerizer_not_exceptional_of_not_squarefull
    (q m p : ℕ) (hq : 2 ≤ q) (hm : 0 < m) (hqm : q^2 ≤ m)
    (hp : p.Prime) (hlarge : p ∉ p0SquarefullPrimes m) :
    ¬ p ∣ q * (q-1) := by
  intro hdiv
  have hpq : p ≤ q := by
    rcases hp.dvd_mul.mp hdiv with hd | hd
    · exact Nat.le_of_dvd (by omega) hd
    · exact (Nat.le_of_dvd (by omega : 0 < q-1) hd).trans (Nat.sub_le _ _)
  apply hlarge
  apply mem_p0SquarefullPrimes.mpr
  have hmU : m ≤ p0DenominatorU m := by unfold p0DenominatorU; omega
  exact ⟨hp, (Nat.pow_le_pow_left hpq 2).trans
    (hqm.trans (hmU.trans (Nat.le_add_right _ _)))⟩

/-- Actual generic nonsquarefull exponents reuse the same moving-profile
weights as q=2, once m >= q². The finite profile majorant is still required. -/
theorem p0IntegerizerExponent_eq_settled_of_not_squarefull
    (q m p : ℕ) (hq : 2 ≤ q) (hm : 0 < m) (hqm : q^2 ≤ m)
    (hp : p.Prime) (hlarge : p ∉ p0SquarefullPrimes m)
    (hpU : p ≤ formalDivisorCutoff m) :
    p0IntegerizerExponent q m p =
      min (p0RateW m p) (((3*m*Nat.log p (formalDivisorCutoff m) : ℕ) : ℤ)) :=
  p0IntegerizerExponent_eq_settled_of_not_dvd q m p
    (p0Integerizer_not_exceptional_of_not_squarefull q m p hq hm hqm hp hlarge) hpU

end
end Li2Lean.P0
#print axioms Li2Lean.P0.p0IntegerizerExponent_eq_settled_of_not_squarefull
