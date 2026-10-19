/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/

import Li2Lean.B3.ActualRationalIntegerizerProducer
import Li2Lean.B3.ActualVFormalBase

namespace Li2Lean.V

/-- v13 v-arithmetic.tex:13-32: the empty-index source is the unit determinant. -/
theorem vPolynomial_zero_generic (a : ℤ) : vPolynomial 0 a = 1 := by
  have : IsEmpty (Fin (vMatrixSize 0)) := by
    simp [vMatrixSize, vM, vS]
  exact Matrix.det_isEmpty

/-- The index-zero polynomial used by the generic signed integerizer is one. -/
theorem actualVDeterminant_zero_generic (q : ℕ) : actualVDeterminant q 0 = 1 := by
  simp [actualVDeterminant, actualDeterminantAt, vPolynomial_zero_generic]

/-- The zero-index Gauss valuation needs no arbitrary exponent correction. -/
theorem actualGaussValuation_zero_index (q p : ℕ) :
    actualGaussValuation p (actualVDeterminant q 0) = 0 := by
  rw [actualVDeterminant_zero_generic]
  have hsupp : (1 : Polynomial ℚ).support = {0} := by
    simpa using (Polynomial.support_C (show (1 : ℚ) ≠ 0 by norm_num))
  simp [actualGaussValuation, hsupp]

end Li2Lean.V

#print axioms Li2Lean.V.vPolynomial_zero_generic
#print axioms Li2Lean.V.actualGaussValuation_zero_index

namespace Li2Lean.B3

open Li2Lean.P0.Integerization Li2Lean.P0.Integerization.S08

/-- Integer specialization of the same formal outer parameter used in S08. -/
theorem outerEval_psi_int (Z : Polynomial (Polynomial ℤ)) (a : ℤ) :
    outerEval (a : ℚ) (psi Z) =
      (Z.eval (Polynomial.C a)).map (Int.castRingHom ℚ) := by
  simp [outerEval, psi]

/-- v13 v-arithmetic.tex:37-46: the literal V denominator scale clears all
coefficients at every integral base; no formal-divisor credit is used. -/
theorem vActualDenominatorClears (q n : ℕ) (hn : 0 < n) :
    ∃ R : Polynomial ℤ, R.map (Int.castRingHom ℚ) =
      Polynomial.C ((denominatorLcm (V.vN n) : ℚ) ^ (12 * n) *
        (denominatorLcm (V.vU n) : ℚ) ^ n) *
          V.actualVDeterminant q (4 * n) := by
  classical
  obtain ⟨Z, hZ⟩ := vActualFormalDeterminant_integerized n hn
  refine ⟨(Matrix.det Z).eval (Polynomial.C (-(q : ℤ))), ?_⟩
  have heval := congrArg (outerEval (-(q : ℚ))) hZ
  have hi := outerEval_psi_int (Matrix.det Z) (-(q : ℤ))
  simp only [Int.cast_neg, Int.cast_natCast] at hi
  rw [hi, map_mul, outerEval_actualVDeterminant] at heval
  have hscale :
      outerEval (-(q : ℚ))
          (∏ r : Fin (V.vMatrixSize n), ratConst (vActualFormalRowScale n r)) =
        Polynomial.C ((denominatorLcm (V.vN n) : ℚ) ^ (12 * n) *
          (denominatorLcm (V.vU n) : ℚ) ^ n) := by
    simp only [map_prod, outerEval_ratConst]
    rw [← map_prod, vActualFormalRowScale_prod]
  rw [hscale] at heval
  exact heval

/-- The unoptimized, actual V denominator scale. -/
def vActualBaselineD (n : ℕ) : ℚ :=
  (denominatorLcm (V.vN n) : ℚ) ^ (12 * n) *
    (denominatorLcm (V.vU n) : ℚ) ^ n

private theorem denominatorLcm_pos_generic (U : ℕ) : 0 < denominatorLcm U := by
  apply Nat.pos_of_ne_zero
  exact Finset.lcm_ne_zero_iff.mpr (by
    intro x hx
    change x ≠ 0
    have := (Finset.mem_Icc.mp hx).1
    omega)

theorem vActualBaselineD_pos (n : ℕ) : 0 < vActualBaselineD n := by
  have hN := denominatorLcm_pos_generic (V.vN n)
  have hU := denominatorLcm_pos_generic (V.vU n)
  unfold vActualBaselineD
  positivity

/-- The baseline cost depends on the two actual V cutoffs, not on P0's
`2*m-1` cutoff (v13 v-arithmetic.tex:37-46). -/
theorem vActualBaselineD_padicVal (n p : ℕ) (hp : p.Prime) :
    padicValRat p (vActualBaselineD n) =
      ((12 * n * Nat.log p (V.vN n) + n * Nat.log p (V.vU n) : ℕ) : ℤ) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hd (U : ℕ) : padicValNat p (denominatorLcm U) = Nat.log p U := by
    have h := Nat.factorization_lcmUpto U hp
    rw [Nat.factorization_def _ hp] at h
    exact h
  have hN : (denominatorLcm (V.vN n) : ℚ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (denominatorLcm_pos_generic (V.vN n)))
  have hU : (denominatorLcm (V.vU n) : ℚ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (denominatorLcm_pos_generic (V.vU n)))
  rw [vActualBaselineD, padicValRat.mul (pow_ne_zero _ hN) (pow_ne_zero _ hU),
    padicValRat.pow, padicValRat.pow, padicValRat.of_nat,
    padicValRat.of_nat, hd, hd]
  push_cast
  ring

/-- A source-backed q-generic coarse coefficient bound for the actual V
polynomial. Formal-divisor, residue-block, and outer-pole savings remain separate. -/
theorem vActualBaseline_coeff_valuation_lower (q n p i : ℕ)
    (hn : 0 < n) (hp : p.Prime)
    (hc : (V.actualVDeterminant q (4 * n)).coeff i ≠ 0) :
    -((12 * n * Nat.log p (V.vN n) + n * Nat.log p (V.vU n) : ℕ) : ℤ) ≤
      padicValRat p ((V.actualVDeterminant q (4 * n)).coeff i) := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨R, hR⟩ := vActualDenominatorClears q n hn
  have hcoeff := congrArg (fun P : Polynomial ℚ => P.coeff i) hR
  simp only [Polynomial.coeff_map, Polynomial.coeff_C_mul] at hcoeff
  change (R.coeff i : ℚ) =
    vActualBaselineD n * (V.actualVDeterminant q (4 * n)).coeff i at hcoeff
  have hv := congrArg (padicValRat p) hcoeff
  rw [padicValRat.of_int, padicValRat.mul (ne_of_gt (vActualBaselineD_pos n)) hc,
    vActualBaselineD_padicVal n p hp] at hv
  omega

/-- The coarse actual Gauss bound also covers the zero-polynomial convention. -/
theorem vActualBaseline_gauss_lower (q n p : ℕ)
    (hn : 0 < n) (hp : p.Prime) :
    -((12 * n * Nat.log p (V.vN n) + n * Nat.log p (V.vU n) : ℕ) : ℤ) ≤
      V.actualGaussValuation p (V.actualVDeterminant q (4 * n)) := by
  exact actualGaussValuation_ge_of_coeff_ge p _ _ (by positivity)
    (fun i hi => vActualBaseline_coeff_valuation_lower q n p i hn hp hi)

/-- All primes beyond the literal V denominator cutoff are integral in the
actual determinant, uniformly in q (v13 v-arithmetic.tex:37-46). -/
theorem v_actualGaussValuation_nonneg_of_gt_cutoff
    (q n p : ℕ) (hn : 0 < n) (hp : p.Prime) (hcut : 11 * n - 1 < p) :
    0 ≤ V.actualGaussValuation p (V.actualVDeterminant q (4 * n)) := by
  have hN : V.vN n < p := by dsimp [V.vN]; omega
  have hU : V.vU n < p := hcut
  have hlogN : Nat.log p (V.vN n) = 0 := Nat.log_eq_zero_iff.mpr (Or.inl hN)
  have hlogU : Nat.log p (V.vU n) = 0 := Nat.log_eq_zero_iff.mpr (Or.inl hU)
  simpa only [hlogN, hlogU, mul_zero, add_zero, Nat.cast_zero, neg_zero] using
    vActualBaseline_gauss_lower q n p hn hp

end Li2Lean.B3

#print axioms Li2Lean.B3.outerEval_psi_int

#print axioms Li2Lean.B3.vActualDenominatorClears

#print axioms Li2Lean.B3.vActualBaseline_gauss_lower
#print axioms Li2Lean.B3.v_actualGaussValuation_nonneg_of_gt_cutoff
