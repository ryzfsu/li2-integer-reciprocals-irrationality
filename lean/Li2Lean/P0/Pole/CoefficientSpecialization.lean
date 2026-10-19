/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.IntegerizationS08ChainParam
import Li2Lean.P0.Pole.ConcreteDivisor

namespace Li2Lean.P0.Integerization.S08

open Li2Lean Li2Lean.P0.Integerization Li2Lean.P0.Pole

noncomputable section

/-- The rational pole divisor descends through the literal integer baseline
and yields the full signed coefficient credit after specialization. -/
theorem canonical_formal_coeff_of_pole_divisor (q m p i : ℕ) (hq : 2 ≤ q)
    (hm : 0 < m) (h4 : 4 ∣ m) (hp : p.Prime) (hpq : ¬ p ∣ q)
    (hPole : (aVar - ratConst 1) ^ (7 * (m / 4)^2 + 3 * (m / 4)) ∣
      Matrix.det (Li2Lean.P0.PoleMatrixCore.poleMatrix m)) :
    Li2Lean.P0.p0FormalDivisorCoeff q m p i := by
  let : Fact p.Prime := ⟨hp⟩
  have hqInt : (q : ℤ) ≠ 1 := by omega
  have hqm1 : 0 < q - 1 := by omega
  have hqm1Q : (q : ℚ) - 1 = ((q - 1 : ℕ) : ℚ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ q)]
    norm_num
  have hqm1Qne : (q : ℚ) - 1 ≠ 0 := by
    rw [hqm1Q]
    exact_mod_cast (Nat.ne_of_gt hqm1)
  have hW : ∃ P : Polynomial ℤ,
      (∀ n, ((q - 1 : ℕ) : ℤ) ^ (7 * (m / 4)^2 + 3 * (m / 4)) ∣ P.coeff n) ∧
      Polynomial.map (Int.castRingHom ℚ) P =
        Polynomial.C (((p0DenominatorLcm m : ℚ) ^ (3*m)) *
          ((q : ℚ) - 1) ^ (m * (m / 2))) *
            p0CanonicalPolynomial (q : ℤ) m := by
    obtain ⟨h, rfl⟩ := h4
    have hh : 1 ≤ h := by omega
    obtain ⟨Z, hZ⟩ := formalCanonical_integerized h hh
    let Zs := Li2Lean.P0.Pole.tScaleZ ((4*h)/2) Z
    have hZs : psi Zs = ratConst ((p0DenominatorLcm (4*h) : ℚ) ^ (3*(4*h))) *
        Matrix.det (Li2Lean.P0.PoleMatrixCore.poleMatrix (4*h)) := by
      rw [show psi Zs = Li2Lean.P0.PoleMatrixCore.tScale ((4*h)/2) (psi Z) from
        Li2Lean.P0.Pole.psi_tScaleZ _ _, hZ, map_mul,
        Li2Lean.P0.PoleMatrixCore.tScale_ratConst,
        ← Li2Lean.P0.PoleMatrixCore.det_poleMatrix_eq]
    let shiftZ : Polynomial (Polynomial ℤ) →+* Polynomial (Polynomial ℤ) :=
      Polynomial.compRingHom (Polynomial.X + 1)
    have hshift (Y : Polynomial (Polynomial ℤ)) :
        psi (shiftZ Y) = shiftB (psi Y) := by
      simp [shiftZ, psi, shiftB, Polynomial.map_comp]
    have hdivQ : (Polynomial.X : BivPoly) ^ (7*h^2+3*h) ∣ psi (shiftZ Zs) := by
      rw [hshift, hZs, map_mul, shiftB_ratConst]
      have hd := map_dvd shiftB hPole
      simp only [map_pow, map_sub, shiftB_aVar, shiftB_ratConst] at hd
      have hx : (Polynomial.X : BivPoly) + 1 - ratConst 1 = Polynomial.X := by
        simp [ratConst]
      rw [hx] at hd
      exact dvd_mul_of_dvd_right (by simpa using hd) _
    have hdivZ := int_bivariate_x_pow_dvd_of_rat_map hdivQ
    have hspec := IntegerizationScalarSpecialization.eval_dvd_eval_of_X_pow
      (shiftZ Zs) (Polynomial.C ((q - 1 : ℕ) : ℤ)) (7*h^2+3*h) hdivZ
    have hspecEq : (shiftZ Zs).eval (Polynomial.C ((q - 1 : ℕ) : ℤ)) =
        Zs.eval (Polynomial.C (q : ℤ)) := by
      change (Zs.comp (Polynomial.X + 1)).eval (Polynomial.C ((q - 1 : ℕ) : ℤ)) = _
      rw [Polynomial.eval_comp]
      have he : ((q - 1 : ℕ) : ℤ) + 1 = (q : ℤ) := by omega
      simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
      rw [← Polynomial.C_1, ← Polynomial.C_add, he]
    rw [hspecEq] at hspec
    refine ⟨Zs.eval (Polynomial.C (q : ℤ)), ?_, ?_⟩
    · intro n
      have hs : Polynomial.C (((q - 1 : ℕ) : ℤ) ^ (7*h^2+3*h)) ∣
          Zs.eval (Polynomial.C (q : ℤ)) := by
        simpa only [Polynomial.C_pow] using hspec
      simpa using (Polynomial.C_dvd_iff_dvd_coeff _ _).mp hs n
    · have hqQ : (q : ℚ) ≠ 1 := by exact_mod_cast hqInt
      rw [← outerEval_psi_int, hZs, map_mul]
      have hcast : ((q : ℤ) : ℚ) = (q : ℚ) := by simp
      rw [hcast, poleDet_outerEval_param _ hqQ]
      simp only [outerEval_ratConst, p0CanonicalPolynomial, dvd_mul_right, ite_true]
      rw [Polynomial.C_mul]
      push_cast
      ring
  obtain ⟨P, hdiv, hP⟩ := hW
  change (p0CanonicalPolynomial (q : ℤ) m).coeff i = 0 ∨ _
  by_cases hc : (p0CanonicalPolynomial (q : ℤ) m).coeff i = 0
  · exact Or.inl hc
  right
  have hcoeff := congrArg (fun R : Polynomial ℚ => R.coeff i) hP
  simp only [Polynomial.coeff_map, Polynomial.coeff_C_mul] at hcoeff
  change (P.coeff i : ℚ) = _ at hcoeff
  obtain ⟨z, hz⟩ := hdiv i
  rw [hz] at hcoeff
  push_cast at hcoeff
  rw [← hqm1Q] at hcoeff
  have hbase : ((p0DenominatorLcm m : ℚ) ^ (3*m)) ≠ 0 :=
    ne_of_gt (p0A2BaselineD_pos hm)
  have hz0 : (z : ℚ) ≠ 0 := by
    intro hz0
    rw [hz0, mul_zero] at hcoeff
    exact mul_ne_zero (mul_ne_zero hbase (pow_ne_zero _ hqm1Qne)) hc hcoeff.symm
  have hval := congrArg (padicValRat p) hcoeff
  rw [padicValRat.mul (pow_ne_zero _ hqm1Qne) hz0,
    padicValRat.mul (mul_ne_zero hbase (pow_ne_zero _ hqm1Qne)) hc,
    padicValRat.mul hbase (pow_ne_zero _ hqm1Qne)] at hval
  have hbval : padicValRat p ((p0DenominatorLcm m : ℚ) ^ (3*m)) =
      (3*m*Nat.log p (p0DenominatorU m) : ℕ) := p0A2BaselineD_padicVal hp m
  rw [hbval, padicValRat.pow, hqm1Q,
    padicValRat.of_nat, padicValRat.pow, padicValRat.of_int,
    padicValRat.of_nat] at hval
  unfold Li2Lean.P0.formalDivisorCredit
  rw [padicValNat.eq_zero_of_not_dvd hpq]
  simp only [Nat.cast_zero, mul_zero, sub_zero]
  obtain ⟨h, rfl⟩ := h4
  have hU : p0DenominatorU (4*h) = 2 * (4*h) - 1 := rfl
  rw [hU] at hval
  simp [Li2Lean.P0.formalDivisorH, Li2Lean.P0.formalDivisorCutoff]
  have hzvalInt : (0 : ℤ) ≤ padicValInt p z := Int.natCast_nonneg _
  have hdiv2 : 4 * h / 2 = 2 * h := by omega
  rw [hdiv2] at hval
  simp at hval
  push_cast at hval
  rw [padicValRat.of_nat] at hval
  ring_nf at hval ⊢
  nlinarith

/-- Full formal coefficient credit at every prime not dividing the base,
using the proved divisor on the actual pole determinant. -/
theorem canonical_formal_coeff_of_not_dvd (q m p i : ℕ) (hq : 2 ≤ q)
    (hm : 0 < m) (h4 : 4 ∣ m) (hp : p.Prime) (hpq : ¬ p ∣ q) :
    Li2Lean.P0.p0FormalDivisorCoeff q m p i := by
  apply canonical_formal_coeff_of_pole_divisor q m p i hq hm h4 hp hpq
  obtain ⟨h, rfl⟩ := h4
  simpa using pole_det_aSubOne_pow_dvd h

/-- The exceptional `q-1` branch required by the canonical integerizer. -/
theorem canonical_formal_coeff_of_qSubOne_dvd (q m p i : ℕ) (hq : 2 ≤ q)
    (hm : 0 < m) (h4 : 4 ∣ m) (hp : p.Prime) (_hpq1 : p ∣ q-1)
    (hpq : ¬ p ∣ q) : Li2Lean.P0.p0FormalDivisorCoeff q m p i :=
  canonical_formal_coeff_of_not_dvd q m p i hq hm h4 hp hpq

end
end Li2Lean.P0.Integerization.S08

#print axioms Li2Lean.P0.Integerization.S08.canonical_formal_coeff_of_pole_divisor

#print axioms Li2Lean.P0.Integerization.S08.canonical_formal_coeff_of_not_dvd
#print axioms Li2Lean.P0.Integerization.S08.canonical_formal_coeff_of_qSubOne_dvd
