/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/

import Li2Lean.P0.PositiveBaseParam
import Li2Lean.P0.A2DegreeBound
import Li2Lean.P0.IntegerizationActualOddPrimeRate

/-!
# Construction-bound rational P0 integerizer producer

This file is the positive-base counterpart of the signed-V rational bridge.
The determinant is always the actual `p0CanonicalPolynomial q m`; no
polynomial sequence, valuation function, or conclusion-shaped integerizer is
an input.  The formal divisor credit and the moving-prime coefficient bound
are kept separate, as in v13 `p0-arithmetic.tex:11-24,326-358`.  Their
minimum is the exponent used by the finite rational prime product.

The generic finite-product, p-adic, and polynomial-lifting lemmas are reused
from the frozen Li2(1/2) integerization kit
`P0.IntegerizationActualOddPrimeRate`.
-/

namespace Li2Lean.P0

noncomputable section

open scoped BigOperators
open Li2Lean.P0.Integerization
open PositiveBase

/-! ## v13 formal divisor data -/

/-- The denominator cutoff `U = 2m - 1` from v13 `p0-arithmetic.tex:11-18`.
The actual prime product may enlarge this cutoff through its producer field to
include the fixed exceptional factors of `q(q-1)`. -/
def formalDivisorCutoff (m : ℕ) : ℕ := 2 * m - 1

/-- The `N_m = 13h^2 - 4h` formal credit, with `m = 4h`, from
v13 `p0-arithmetic.tex:13-18,62-126`. -/
def formalDivisorN (m : ℕ) : ℕ :=
  13 * (m / 4) ^ 2 - 4 * (m / 4)

/-- The endpoint pole credit `H_m = h^2 - 3h`, v13
`p0-arithmetic.tex:13-18,247-324`. -/
def formalDivisorH (m : ℕ) : ℤ :=
  ((m / 4 : ℕ) : ℤ) ^ 2 - 3 * (m / 4 : ℕ)

/-- The coefficientwise lower-bound exponent supplied by the formal divisor.
For `m = 4h` this is
`3m floor(log_p U) + H_m v_p(q-1) - N_m v_p(q)`, exactly the quantity
`F_{m,p}(a)` in v13 `p0-arithmetic.tex:326-351`. -/
def formalDivisorCredit (q m p : ℕ) : ℤ :=
  ((3 * m * Nat.log p (formalDivisorCutoff m) : ℕ) : ℤ) +
    formalDivisorH m * (padicValNat p (q - 1) : ℤ) -
    (formalDivisorN m : ℤ) * (padicValNat p q : ℤ)

theorem formalDivisorCutoff_eq_paper (m : ℕ) :
    formalDivisorCutoff m = 2 * m - 1 := rfl

theorem formalDivisorN_eq_paper {m h : ℕ} (hm : m = 4 * h) :
    formalDivisorN m = 13 * h ^ 2 - 4 * h := by
  simp [formalDivisorN, hm]

theorem formalDivisorH_eq_paper {m h : ℕ} (hm : m = 4 * h) :
    formalDivisorH m = (h : ℤ) ^ 2 - 3 * h := by
  simp [formalDivisorH, hm]

/-! ## Actual q-parameterized producer -/

/-- A rational-D producer for one fixed positive base `3 <= q <= 11`.

The polynomial in every field is the actual v13 determinant
`p0CanonicalPolynomial (q : Z) m` (v13 `p0-arithmetic.tex:24-32`).
`formal_divisor_coeff` is the formal-divisor/residue-free coefficient bound;
`moving_coeff` is the large-prime assignment bound from
`p0-arithmetic.tex:326-358`.  Their minimum is tied to `exponent` by
`exponent_eq_min`, so the clearing factor cannot be chosen independently.
The PNT rate is the separate limiting input from `p0-arithmetic.tex:353-421`.
-/
structure ActualRationalIntegerizerProducer
    (q : ℕ) (hq : InRange (q : ℤ)) (rate : ℝ) : Type where
  cutoff : ℕ → ℕ
  movingExponent : ℕ → ℕ → ℤ
  exponent : ℕ → ℕ → ℤ
  D : ℕ → ℚ
  cutoff_ge_formal : ∀ m : ℕ, 0 < m → 4 ∣ m →
    formalDivisorCutoff m ≤ cutoff m
  exponent_eq_min : ∀ m p : ℕ,
    exponent m p = min (formalDivisorCredit q m p) (movingExponent m p)
  exponent_zero_of_gt_cutoff : ∀ m p : ℕ, 0 < m → 4 ∣ m →
    cutoff m < p → exponent m p = 0
  D_eq_primeProduct : ∀ m : ℕ, 0 < m → 4 ∣ m →
    D m = rationalPrimeProduct (Nat.primesLE (cutoff m)) (exponent m)
  /-- Formal divisor bound, pinned to the actual P0 coefficient.  v13:
  `p0-arithmetic.tex:11-24,247-351`. -/
  formal_divisor_coeff : ∀ m : ℕ, 0 < m → 4 ∣ m → ∀ p : ℕ, p.Prime →
    ∀ i : ℕ,
      (p0CanonicalPolynomial (q : ℤ) m).coeff i = 0 ∨
        -(formalDivisorCredit q m p) ≤
          padicValRat p ((p0CanonicalPolynomial (q : ℤ) m).coeff i)
  /-- Moving-prime/residue-block bound, pinned to the same actual
  determinant.  v13: `p0-arithmetic.tex:326-358`. -/
  moving_coeff : ∀ m : ℕ, 0 < m → 4 ∣ m → ∀ p : ℕ, p.Prime →
    ∀ i : ℕ,
      (p0CanonicalPolynomial (q : ℤ) m).coeff i = 0 ∨
        -(movingExponent m p) ≤
          padicValRat p ((p0CanonicalPolynomial (q : ℤ) m).coeff i)
  /-- The row-count degree bound for the actual determinant.  v13:
  `p0-arithmetic.tex:24-32`; q=2 reuses the frozen A2 proof. -/
  degree_bound : ∀ m : ℕ, 0 < m → 4 ∣ m →
    ((p0CanonicalPolynomial (q : ℤ) m).map (algebraMap ℚ ℝ)).natDegree ≤ m
  /-- Weighted prime-sum PNT input.  v13: `p0-arithmetic.tex:353-421`. -/
  pnt_rate : ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
    0 < m → 4 ∣ m →
      (∑ p ∈ Nat.primesLE (cutoff m),
        (exponent m p : ℝ) * Real.log p) / (m : ℝ) ^ 2 ≤ rate + ε

/-! ## Primewise bridge -/

theorem actual_coeff_lower
    {q : ℕ} {hq : InRange (q : ℤ)} {rate : ℝ}
    (P : ActualRationalIntegerizerProducer q hq rate)
    (m : ℕ) (hm : 0 < m) (h4 : 4 ∣ m) (p : ℕ) (hp : p.Prime) (i : ℕ) :
    (p0CanonicalPolynomial (q : ℤ) m).coeff i = 0 ∨
      -(P.exponent m p) ≤
        padicValRat p ((p0CanonicalPolynomial (q : ℤ) m).coeff i) := by
  obtain hF | hF := P.formal_divisor_coeff m hm h4 p hp i
  · exact Or.inl hF
  obtain hM | hM := P.moving_coeff m hm h4 p hp i
  · exact Or.inl hM
  rw [P.exponent_eq_min]
  by_cases h : formalDivisorCredit q m p ≤ P.movingExponent m p
  · rw [min_eq_left h]
    exact Or.inr hF
  · have h' : P.movingExponent m p ≤ formalDivisorCredit q m p := le_of_not_ge h
    rw [min_eq_right h']
    exact Or.inr hM

theorem actual_coefficient_is_int
    {q : ℕ} {hq : InRange (q : ℤ)} {rate : ℝ}
    (P : ActualRationalIntegerizerProducer q hq rate)
    (m : ℕ) (hm : 0 < m) (h4 : 4 ∣ m) (i : ℕ) :
    ∃ z : ℤ,
      P.D m * (p0CanonicalPolynomial (q : ℤ) m).coeff i = z := by
  rw [P.D_eq_primeProduct m hm h4]
  apply rat_mul_is_int_of_prime_padic_lower _ _
    (ne_of_gt (rationalPrimeProduct_pos _ _ (fun p hp =>
      Nat.prime_of_mem_primesLE hp)))
  intro p hp
  letI : Fact p.Prime := ⟨hp⟩
  let d := (p0CanonicalPolynomial (q : ℤ) m).coeff i
  by_cases hd : d = 0
  · exact Or.inl hd
  · right
    obtain hcoeff := actual_coeff_lower P m hm h4 p hp i
    have hcoeff' := hcoeff.resolve_left hd
    have hval :
        padicValRat p
            (rationalPrimeProduct (Nat.primesLE (P.cutoff m))
              (P.exponent m)) =
          if p ≤ P.cutoff m then P.exponent m p else 0 := by
      rw [rationalPrimeProduct_padicVal hp _ _ (fun r hr =>
        Nat.prime_of_mem_primesLE hr)]
      simp only [Nat.mem_primesLE, hp, and_true]
    rw [hval]
    by_cases hpU : p ≤ P.cutoff m
    · rw [if_pos hpU]
      exact hcoeff'
    · rw [if_neg hpU]
      have hpAbove : P.cutoff m < p := not_le.mp hpU
      have hzero := P.exponent_zero_of_gt_cutoff m p hm h4 hpAbove
      have hcoeff'' := hcoeff'
      rw [hzero] at hcoeff''
      simpa using hcoeff''

theorem actual_clears
    {q : ℕ} {hq : InRange (q : ℤ)} {rate : ℝ}
    (P : ActualRationalIntegerizerProducer q hq rate)
    (m : ℕ) (hm : 0 < m) (h4 : 4 ∣ m) :
    ∃ R : Polynomial ℤ,
      R.map (Int.castRingHom ℚ) =
        Polynomial.C (P.D m) * p0CanonicalPolynomial (q : ℤ) m := by
  rw [← Polynomial.mem_lifts, Polynomial.lifts_iff_coeff_lifts]
  intro i
  rw [Polynomial.coeff_C_mul]
  obtain ⟨z, hz⟩ := actual_coefficient_is_int P m hm h4 i
  exact ⟨z, hz.symm⟩

/-! ## Endpoint-facing P0 bound -/

theorem integerizerBoundAt_of_actual_producer
    {q : ℕ} {hq : InRange (q : ℤ)} {rate : ℝ}
    (P : ActualRationalIntegerizerProducer q hq rate) :
    P0IntegerizerBoundAt (family (q : ℤ) hq) rate := by
  refine ⟨P.D, ?_, ?_, ?_, ?_⟩
  · intro m hm h4
    rw [P.D_eq_primeProduct m hm h4]
    exact rationalPrimeProduct_pos _ _ (fun p hp =>
      Nat.prime_of_mem_primesLE hp)
  · exact P.degree_bound
  · intro m hm h4
    obtain ⟨R, hR⟩ := actual_clears P m hm h4
    refine ⟨R, ?_⟩
    have hR' := congrArg
      (fun S : Polynomial ℚ => S.map (algebraMap ℚ ℝ)) hR
    have hcomp :
        (algebraMap ℚ ℝ).comp (Int.castRingHom ℚ) =
          Int.castRingHom ℝ := by
      ext z
      norm_num
    rw [Polynomial.map_map, hcomp] at hR'
    simpa [family] using hR'
  · intro ε hε
    obtain ⟨M, hM⟩ := P.pnt_rate ε hε
    refine ⟨M, ?_⟩
    intro m hmM hm h4
    rw [P.D_eq_primeProduct m hm h4,
      rationalPrimeProduct_log _ _ (fun p hp =>
        Nat.prime_of_mem_primesLE hp)]
    exact hM m hmM hm h4

/-! ## q=3..11 package and q=2 regression -/

structure ActualRationalIntegerizerFamily (rate : ℕ → ℝ) : Type where
  q3 : ActualRationalIntegerizerProducer 3 (by norm_num [InRange]) (rate 3)
  q4 : ActualRationalIntegerizerProducer 4 (by norm_num [InRange]) (rate 4)
  q5 : ActualRationalIntegerizerProducer 5 (by norm_num [InRange]) (rate 5)
  q6 : ActualRationalIntegerizerProducer 6 (by norm_num [InRange]) (rate 6)
  q7 : ActualRationalIntegerizerProducer 7 (by norm_num [InRange]) (rate 7)
  q8 : ActualRationalIntegerizerProducer 8 (by norm_num [InRange]) (rate 8)
  q9 : ActualRationalIntegerizerProducer 9 (by norm_num [InRange]) (rate 9)
  q10 : ActualRationalIntegerizerProducer 10 (by norm_num [InRange]) (rate 10)
  q11 : ActualRationalIntegerizerProducer 11 (by norm_num [InRange]) (rate 11)

theorem integerizerBoundAt_of_family
    {rate : ℕ → ℝ} (P : ActualRationalIntegerizerFamily rate)
    {q : ℕ} (hq3 : 3 ≤ q) (hq11 : q ≤ 11)
    (hq : InRange (q : ℤ)) :
    P0IntegerizerBoundAt (family (q : ℤ) hq) (rate q) := by
  interval_cases q
  · exact integerizerBoundAt_of_actual_producer P.q3
  · exact integerizerBoundAt_of_actual_producer P.q4
  · exact integerizerBoundAt_of_actual_producer P.q5
  · exact integerizerBoundAt_of_actual_producer P.q6
  · exact integerizerBoundAt_of_actual_producer P.q7
  · exact integerizerBoundAt_of_actual_producer P.q8
  · exact integerizerBoundAt_of_actual_producer P.q9
  · exact integerizerBoundAt_of_actual_producer P.q10
  · exact integerizerBoundAt_of_actual_producer P.q11

/-! This wrapper has exactly the quantifier shape consumed by
`AllN/Producers.lean`: the family remains an explicit named producer input,
while the theorem itself contains no conclusion-shaped field. -/
theorem p0Integerizer_producer_of_actual_family
    {rate : ℕ → ℝ} (P : ActualRationalIntegerizerFamily rate)
    (q : ℕ) (hq : InRange (q : ℤ)) (hq3 : 3 ≤ q) (hq11 : q ≤ 11) :
    P0IntegerizerBoundAt (family (q : ℤ) hq) (rate q) :=
  integerizerBoundAt_of_family P hq3 hq11 hq

theorem a2_regression (m : ℕ) :
    (family 2 two_inRange).G m = p0A2CanonicalFamily.G m := by
  rfl

end
end Li2Lean.P0

#print axioms Li2Lean.P0.actual_coeff_lower
#print axioms Li2Lean.P0.actual_coefficient_is_int
#print axioms Li2Lean.P0.integerizerBoundAt_of_actual_producer
