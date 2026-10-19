/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/

import Li2Lean.B3.ArithmeticPinning
import Li2Lean.B3.ProducerInterfaces
import Li2Lean.P0.IntegerizationActualOddPrimeRate

/-!
# Rational, construction-bound signed-V integerizer producer

This is the q-parameterized version of the q = 3 rational prime-product
bridge.  The scale is a rational prime product, never a natural-number
placeholder.  The determinant in every field is the actual signed
`V.vPolynomial n (-q)`, and the remaining residue-block/outer-pole and PNT
claims are explicit producer inputs.

Paper sources: `v-arithmetic.tex:37-421`, with the local credits at
`:128-133`, the outer-pole exponent at `:289-351`, and the prime-product rate
at `:353-421`.  Generic product and logarithm lemmas are reused from the
1/2 IntegerizationActualOddPrimeRate module.
-/

namespace Li2Lean.B3

noncomputable section

open scoped BigOperators
open Li2Lean.P0.Integerization

/-! ## q-parameterized arithmetic inputs -/

/-- Coefficientwise Gauss valuation bound for the actual signed determinant.
The exponent `E` is supplied by the q-specific v13 residue/outer-pole
calculation; no valuation function is free in this definition.

v13: `v-arithmetic.tex:128-351`. -/
def QActualPrimeValuationBound (q : ℕ) (E : ℕ → ℕ → ℤ) : Prop :=
  ∀ n p : ℕ, p.Prime →
    V.actualGaussValuation p (V.actualVDeterminant q (4 * n)) ≥ -E n p

/-- Weighted prime-sum rate for a q-specific exponent and cutoff.

v13: `v-arithmetic.tex:353-421`. -/
def QV13PrimeSumRate (cutoff : ℕ → ℕ) (E : ℕ → ℕ → ℤ) (tau : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 0 < n →
    (∑ p ∈ Nat.primesLE (cutoff n),
      (E n p : ℝ) * Real.log p) /
        (((4 * n : ℕ) : ℝ) ^ 2) ≤ tau + ε

/-- Rational producer for the actual signed determinant.  The field `D` is
definitionally tied, at every consumed index `4*n`, to the explicit rational
prime product.  `valuation_bound` and `prime_sum_rate` are honest q-specific
inputs and are not proved here.

v13: `v-arithmetic.tex:128-421`. -/
structure VActualRationalIntegerizerProducer (q : ℕ) (tau : ℝ) where
  denominatorCutoff : ℕ → ℕ
  primeExponent : ℕ → ℕ → ℤ
  D : ℕ → ℚ
  D_eq_primeProduct : ∀ n : ℕ,
    D (4 * n) =
      rationalPrimeProduct (Nat.primesLE (denominatorCutoff n)) (primeExponent n)
  valuation_bound : QActualPrimeValuationBound q primeExponent
  exponent_zero_of_gt_cutoff : ∀ n p : ℕ, 0 < n →
    denominatorCutoff n < p → primeExponent n p = 0
  prime_sum_rate : QV13PrimeSumRate denominatorCutoff primeExponent tau

/-! ## Generic rational adapter -/

theorem actual_rational_coefficient_is_int
    {q : ℕ} {tau : ℝ}
    (P : VActualRationalIntegerizerProducer q tau)
    (n : ℕ) (hn : 0 < n) (i : ℕ) :
    ∃ z : ℤ,
      P.D (4 * n) * (V.actualVDeterminant q (4 * n)).coeff i = z := by
  rw [P.D_eq_primeProduct n]
  apply rat_mul_is_int_of_prime_padic_lower _ _
    (ne_of_gt (rationalPrimeProduct_pos _ _ (fun p hp =>
      Nat.prime_of_mem_primesLE hp)))
  intro p hp
  letI : Fact p.Prime := ⟨hp⟩
  let d := (V.actualVDeterminant q (4 * n)).coeff i
  by_cases hd : d = 0
  · exact Or.inl hd
  · right
    have hcoeff := V.actualGaussValuation_coeff
      (P.valuation_bound n p hp) i hd
    have hval :
        padicValRat p
            (rationalPrimeProduct (Nat.primesLE (P.denominatorCutoff n))
              (P.primeExponent n)) =
          if p ≤ P.denominatorCutoff n then P.primeExponent n p else 0 := by
      rw [rationalPrimeProduct_padicVal hp _ _
        (fun r hr => Nat.prime_of_mem_primesLE hr)]
      simp only [Nat.mem_primesLE, hp, and_true]
    rw [hval]
    by_cases hpU : p ≤ P.denominatorCutoff n
    · rw [if_pos hpU]
      exact hcoeff
    · rw [if_neg hpU]
      have hpAbove : P.denominatorCutoff n < p := not_le.mp hpU
      have hzero := P.exponent_zero_of_gt_cutoff n p hn hpAbove
      rw [hzero] at hcoeff
      simpa using hcoeff

theorem actual_rational_clears
    {q : ℕ} {tau : ℝ}
    (P : VActualRationalIntegerizerProducer q tau)
    (n : ℕ) (hn : 0 < n) :
    ∃ R : Polynomial ℤ,
      R.map (Int.castRingHom ℚ) =
        Polynomial.C (P.D (4 * n)) * V.actualVDeterminant q (4 * n) := by
  rw [← Polynomial.mem_lifts, Polynomial.lifts_iff_coeff_lifts]
  intro i
  rw [Polynomial.coeff_C_mul]
  obtain ⟨z, hz⟩ := actual_rational_coefficient_is_int P n hn i
  exact ⟨z, hz.symm⟩

theorem vIntegerizerBound_of_actual_rational_producer
    {q : ℕ} {tau : ℝ}
    (P : VActualRationalIntegerizerProducer q tau) :
    VIntegerizerBound q tau := by
  refine ⟨P.D, ?_, ?_, ?_⟩
  · intro n hn
    rw [P.D_eq_primeProduct]
    exact rationalPrimeProduct_pos _ _ (fun p hp =>
      Nat.prime_of_mem_primesLE hp)
  · intro n hn
    obtain ⟨R, hR⟩ := actual_rational_clears P n hn
    rw [V.actualVDeterminant_four_mul] at hR
    refine ⟨R, ?_⟩
    have hR' := congrArg
      (fun S : Polynomial ℚ => S.map (algebraMap ℚ ℝ)) hR
    have hcomp :
        (algebraMap ℚ ℝ).comp (Int.castRingHom ℚ) =
          Int.castRingHom ℝ := by
      ext z
      norm_num
    rw [vRealPoly_four_mul]
    simpa [hcomp, Polynomial.map_map] using hR'
  · intro ε hε
    obtain ⟨N, hN⟩ := P.prime_sum_rate ε hε
    refine ⟨N, ?_⟩
    intro n hn hnpos
    rw [P.D_eq_primeProduct,
      rationalPrimeProduct_log _ _ (fun p hp =>
        Nat.prime_of_mem_primesLE hp)]
    exact hN n hn hnpos

/-! ## Six fixed-base producer types -/

abbrev VActualRationalIntegerizerProducerQ2 :=
  VActualRationalIntegerizerProducer 2 (vTau 2)

abbrev VActualRationalIntegerizerProducerQ3 :=
  VActualRationalIntegerizerProducer 3 (vTau 3)

abbrev VActualRationalIntegerizerProducerQ4 :=
  VActualRationalIntegerizerProducer 4 (vTau 4)

abbrev VActualRationalIntegerizerProducerQ5 :=
  VActualRationalIntegerizerProducer 5 (vTau 5)

abbrev VActualRationalIntegerizerProducerQ6 :=
  VActualRationalIntegerizerProducer 6 (vTau 6)

abbrev VActualRationalIntegerizerProducerQ7 :=
  VActualRationalIntegerizerProducer 7 (vTau 7)

structure VActualRationalIntegerizerProducerFamily where
  q2 : VActualRationalIntegerizerProducerQ2
  q3 : VActualRationalIntegerizerProducerQ3
  q4 : VActualRationalIntegerizerProducerQ4
  q5 : VActualRationalIntegerizerProducerQ5
  q6 : VActualRationalIntegerizerProducerQ6
  q7 : VActualRationalIntegerizerProducerQ7

/-- The degree side remains pure algebra and preserves the positive `a = 2`
regression.  v13: `v-arithmetic.tex:24-32`. -/
theorem actual_rational_degree_bound (q : ℕ) : VDegreeBound q := by
  intro n _hn
  rw [vRealPoly_four_mul]
  exact Polynomial.natDegree_map_le.trans (V.vPolynomial_natDegree_le n _)

theorem actual_rational_a2_regression (n : ℕ) :
    V.actualDeterminantAt 2 (4 * n) = V.vPolynomial n (2 : ℤ) := by
  simp [V.actualDeterminantAt, Nat.mul_div_cancel_left n
    (by norm_num : (0 : ℕ) < 4)]

end
end Li2Lean.B3

#print axioms Li2Lean.B3.vIntegerizerBound_of_actual_rational_producer
#print axioms Li2Lean.B3.actual_rational_degree_bound
