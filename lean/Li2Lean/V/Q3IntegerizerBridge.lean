/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Mathlib
import Li2Lean.B3.ProducerInterfaces
import Li2Lean.P0.IntegerizationActualOddPrimeRate
import Li2Lean.V.Q3Arithmetic

/-!
The q = 3 integerizer bridge for the v13 signed determinant. It reuses only
the generic rational prime-product and rational integrality lemmas from the
frozen 1/2 IntegerizationActualOddPrimeRate module. The q-specific exponent
and every valuation below are pinned to `V.Q3Arithmetic.actualDeterminant`.

Paper source: v-arithmetic.tex:128-133, 319-421. In particular, the formal
credit at q = 3 is 2m at p = 2 and D_m at p = 3. The old Q3Arithmetic
`q3FormalCredit` ordering is not used here.
-/

namespace Li2Lean.V.Q3Integerizer

noncomputable section

open Li2Lean.P0.Integerization

def q3Rho (n p : ℕ) : ℚ := (p : ℚ) / (Q3Arithmetic.mSize n : ℚ)

/-- Offsets and slopes of the affine walls listed in v13
`v-arithmetic.tex:250-275`. -/
def q3WallLine (c : ℚ) (b : ℤ) : Prop :=
  (c = 0 ∧ 0 ≤ b) ∨
  (c = -(1 / 4 : ℚ) ∧ 1 ≤ b) ∨
  ((c = 1 / 4 ∨ c = 1 / 2 ∨ c = 3 / 2 ∨ c = 5 / 2) ∧ b ≤ 0)

/-- A listed wall is active only if it meets the closed `(rho,x)` strip. -/
def q3WallLineActive (c : ℚ) (b : ℤ) : Prop :=
  q3WallLine c b ∧
    ∃ rho : ℚ, (1 / 40 : ℚ) ≤ rho ∧ rho ≤ 5 / 4 ∧
      0 ≤ c + (b : ℚ) * rho ∧ c + (b : ℚ) * rho ≤ rho

/-- Exact critical rho values from pairwise intersections of the active
affine walls, together with the two closed-strip endpoints in v13
`v-arithmetic.tex:267-275`. -/
def q3Wall40 (rho : ℚ) : Prop :=
  rho = 1 / 40 ∨ rho = 5 / 4 ∨
    (1 / 40 : ℚ) < rho ∧ rho < 5 / 4 ∧
      ∃ c c' : ℚ, ∃ b b' : ℤ,
        q3WallLineActive c b ∧ q3WallLineActive c' b' ∧ b ≠ b' ∧
          (b' : ℚ) * rho - (b : ℚ) * rho = c - c'

/-- Correct q = 3 formal credit from `v-arithmetic.tex:128-133`:
`v_2(4)m = 2m` and `v_3(3)D_m = D_m`. -/
def q3V13FormalCredit (n p : ℕ) : ℤ :=
  if p = 2 then (2 * Q3Arithmetic.mSize n : ℕ)
  else if p = 3 then Q3Arithmetic.formalDivisorExponent n
  else 0

theorem q3V13FormalCredit_two (n : ℕ) :
    q3V13FormalCredit n 2 = (2 * Q3Arithmetic.mSize n : ℤ) := by
  simp [q3V13FormalCredit]

theorem q3V13FormalCredit_three (n : ℕ) :
    q3V13FormalCredit n 3 = (Q3Arithmetic.formalDivisorExponent n : ℤ) := by
  simp [q3V13FormalCredit]

/-- The exact ordered q = 3 exponent from v13 `v-arithmetic.tex:319-351`.
The `p > U` branch is stated before the nonexceptional regions; for n > 0
this is equivalent to the paper's ordered rule because the exceptional primes
2 and 3 are at most U. -/
noncomputable def q3V13PrimeExponent (n p : ℕ) : ℤ := by
  classical
  exact if p = 2 then
      Q3Arithmetic.naturalExponent n p - (2 * Q3Arithmetic.mSize n : ℕ)
    else if p = 3 then
      Q3Arithmetic.naturalExponent n p - Q3Arithmetic.formalDivisorExponent n
    else if Q3Arithmetic.denominatorCutoff n < p then 0
    else if 40 * p ≤ Q3Arithmetic.mSize n then
      Q3Arithmetic.naturalExponent n p
    else if p ^ 2 ≤ max (Q3Arithmetic.numeratorCutoff n)
        (Q3Arithmetic.denominatorCutoff n) then
      Q3Arithmetic.naturalExponent n p
    else if q3Wall40 (q3Rho n p) then
      Q3Arithmetic.naturalExponent n p
    else if (1 / 40 : ℚ) < q3Rho n p ∧ q3Rho n p < 5 / 4 then
      (Q3Arithmetic.mSize n : ℤ) +
        ∑ u ∈ Finset.range p, (Q3Arithmetic.profileRank n p u : ℤ)
    else if 5 * n < p ∧ p ≤ Q3Arithmetic.denominatorCutoff n then
      Q3Arithmetic.outerExponent n p
    else 0

theorem q3V13PrimeExponent_two (n : ℕ) :
    q3V13PrimeExponent n 2 =
      Q3Arithmetic.naturalExponent n 2 - (2 * Q3Arithmetic.mSize n : ℕ) := by
  simp [q3V13PrimeExponent]

theorem q3V13PrimeExponent_three (n : ℕ) :
    q3V13PrimeExponent n 3 =
      Q3Arithmetic.naturalExponent n 3 - Q3Arithmetic.formalDivisorExponent n := by
  simp [q3V13PrimeExponent]

theorem q3V13PrimeExponent_eq_zero_of_gtU {n p : ℕ}
    (hn : 0 < n) (hp : Q3Arithmetic.denominatorCutoff n < p) :
    q3V13PrimeExponent n p = 0 := by
  have hp2 : p ≠ 2 := by
    intro h
    subst p
    simp [Q3Arithmetic.denominatorCutoff] at hp
    omega
  have hp3 : p ≠ 3 := by
    intro h
    subst p
    simp [Q3Arithmetic.denominatorCutoff] at hp
    omega
  simp [q3V13PrimeExponent, hp2, hp3, hp]

def q3PrimeProduct (n : ℕ) : ℚ :=
  rationalPrimeProduct (Nat.primesLE (Q3Arithmetic.denominatorCutoff n))
    (q3V13PrimeExponent n)

theorem q3PrimeProduct_pos (n : ℕ) : 0 < q3PrimeProduct n := by
  apply rationalPrimeProduct_pos
  intro p hp
  exact Nat.prime_of_mem_primesLE hp

theorem q3PrimeProduct_padicVal {p : ℕ} (hp : p.Prime) (n : ℕ) :
    padicValRat p (q3PrimeProduct n) =
      if p ≤ Q3Arithmetic.denominatorCutoff n then
        q3V13PrimeExponent n p else 0 := by
  rw [q3PrimeProduct, rationalPrimeProduct_padicVal hp _ _
    (fun r hr => Nat.prime_of_mem_primesLE hr)]
  simp only [Nat.mem_primesLE, hp, and_true]

theorem q3PrimeProduct_log (n : ℕ) :
    Real.log (q3PrimeProduct n : ℝ) =
      ∑ p ∈ Nat.primesLE (Q3Arithmetic.denominatorCutoff n),
        (q3V13PrimeExponent n p : ℝ) * Real.log p := by
  exact rationalPrimeProduct_log _ _
    (fun p hp => Nat.prime_of_mem_primesLE hp)

/-- All-prime local valuation obligation, pinned to the q = 3 v13 determinant
and the ordered exponent above (`v-arithmetic.tex:128-351`). -/
def Q3ActualPrimeValuationBound (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime →
    Q3Arithmetic.actualGaussValuation p (Q3Arithmetic.actualDeterminant n) ≥
      -q3V13PrimeExponent n p

/-- The remaining analytic-number-theory input is exactly the weighted PNT
sum for the q = 3 v13 exponent (`v-arithmetic.tex:353-421`). -/
def Q3V13PrimeSumRate (tau : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 0 < n →
    (∑ p ∈ Nat.primesLE (Q3Arithmetic.denominatorCutoff n),
      (q3V13PrimeExponent n p : ℝ) * Real.log p) /
        ((4 * n : ℕ) : ℝ) ^ 2 ≤ tau + ε

structure Q3ActualIntegerizerInputs (tau : ℝ) : Prop where
  local_valuation : ∀ n : ℕ, 0 < n → Q3ActualPrimeValuationBound n
  prime_sum_rate : Q3V13PrimeSumRate tau

theorem q3Coefficient_is_int (n : ℕ) (hn : 0 < n)
    (hlocal : Q3ActualPrimeValuationBound n) (i : ℕ) :
    ∃ z : ℤ, q3PrimeProduct n * (Q3Arithmetic.actualDeterminant n).coeff i = z := by
  apply rat_mul_is_int_of_prime_padic_lower _ _ (ne_of_gt (q3PrimeProduct_pos n))
  intro p hp
  letI : Fact p.Prime := ⟨hp⟩
  let d := (Q3Arithmetic.actualDeterminant n).coeff i
  by_cases hd : d = 0
  · exact Or.inl hd
  · right
    have hcoeff := Q3Arithmetic.actualGaussValuation_coeff (hlocal p hp) i hd
    rw [q3PrimeProduct_padicVal hp n]
    by_cases hpU : p ≤ Q3Arithmetic.denominatorCutoff n
    · rw [if_pos hpU]
      exact hcoeff
    · rw [if_neg hpU]
      have hpAbove : Q3Arithmetic.denominatorCutoff n < p := not_le.mp hpU
      have hzero := q3V13PrimeExponent_eq_zero_of_gtU hn hpAbove
      rw [hzero] at hcoeff
      simpa using hcoeff

theorem q3ActualIntegerizer_clears (n : ℕ) (hn : 0 < n)
    (hlocal : Q3ActualPrimeValuationBound n) :
    ∃ P : Polynomial ℤ,
      P.map (Int.castRingHom ℚ) =
        Polynomial.C (q3PrimeProduct n) * Q3Arithmetic.actualDeterminant n := by
  rw [← Polynomial.mem_lifts, Polynomial.lifts_iff_coeff_lifts]
  intro i
  rw [Polynomial.coeff_C_mul]
  obtain ⟨z, hz⟩ := q3Coefficient_is_int n hn hlocal i
  exact ⟨z, hz.symm⟩

/-- Convert the q = 3 rational prime product into B3's real-coefficient
integerizer. The fields remain the explicit local valuation and PNT inputs;
the multiplier is the v13 signed prime product, not an arbitrary scalar. -/
theorem q3VIntegerizerBound_of_actual_inputs (tau : ℝ)
    (h : Q3ActualIntegerizerInputs tau) :
    Li2Lean.B3.VIntegerizerBound 3 tau := by
  let D : ℕ → ℚ := fun m => q3PrimeProduct (m / 4)
  refine ⟨D, ?_, ?_, ?_⟩
  · intro n hn
    simpa [D, Nat.mul_div_cancel_left n (by norm_num : (0 : ℕ) < 4)] using
      q3PrimeProduct_pos n
  · intro n hn
    obtain ⟨P, hP⟩ :=
      q3ActualIntegerizer_clears n hn (h.local_valuation n hn)
    refine ⟨P, ?_⟩
    have hP' := congrArg
      (fun R : Polynomial ℚ => R.map (algebraMap ℚ ℝ)) hP
    have hcomp :
        (algebraMap ℚ ℝ).comp (Int.castRingHom ℚ) =
          Int.castRingHom ℝ := by
      ext z
      norm_num
    rw [Li2Lean.B3.vRealPoly_four_mul]
    simpa [D, Nat.mul_div_cancel_left n (by norm_num : (0 : ℕ) < 4),
      hcomp, Polynomial.map_map, Q3Arithmetic.actualDeterminant,
      Q3Arithmetic.a] using hP'
  · intro ε hε
    obtain ⟨N, hN⟩ := h.prime_sum_rate ε hε
    refine ⟨N, ?_⟩
    intro n hn hnpos
    have hlog := q3PrimeProduct_log n
    simpa [D, Nat.mul_div_cancel_left n (by norm_num : (0 : ℕ) < 4), hlog] using
      hN n hn hnpos

/-- The generalized determinant keeps the positive `a = 2` instance unchanged
as a regression against the source-matrix definition (`v-arithmetic.tex:18-35`). -/
theorem positive_a2_regression (n : ℕ) :
    V.vPolynomial n (2 : ℤ) = Matrix.det (V.vSourceMatrix n (2 : ℤ)) :=
  V.vPolynomial_two n

end
end Li2Lean.V.Q3Integerizer
