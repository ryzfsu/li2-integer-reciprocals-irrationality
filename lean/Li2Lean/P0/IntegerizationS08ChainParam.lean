/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.IntegerizationS08Lift
import Li2Lean.P0.IntegerizationFormalBaseParam
import Li2Lean.P0.IntegerizationFormalMomentsParam
import Li2Lean.P0.Pole.MatrixCore
import Li2Lean.P0.Pole.IntegerizationPoleTransport
import Li2Lean.P0.IntegerizerObligationPlan

namespace Li2Lean.P0.Integerization.S08

noncomputable section

open Finset
open Li2Lean

/-! The S08 lift is formal in the outer base variable. These lemmas expose
the specialization at an arbitrary rational base. The factor `(a - 1)^g`
is retained explicitly; at `a = 2` it is the unit used by the old regression.
-/

theorem formalTScaled_outerEval_param_chain (a : ℚ) (ha : a ≠ 1) (g i : ℕ) :
    outerEval a (formalTScaled g i) =
      Polynomial.C ((a - 1) ^ g * p0TQ a g i) := by
  exact Li2Lean.P0.Integerization.formalTScaled_outerEval_param a ha g i

theorem formalBScaled_outerEval_param_chain (a : ℚ) (ha : a ≠ 1) (g i : ℕ) :
    outerEval a (formalBScaled g i) =
      Polynomial.C ((a - 1) ^ g * p0BQQ a g i) := by
  exact Li2Lean.P0.Integerization.formalBScaled_outerEval_param a ha g i

theorem formalC_outerEval_param_chain (a : ℚ) (g i j : ℕ) :
    outerEval a (formalC g i j) =
      Polynomial.C (p0CQ a g i j) := by
  by_cases hij : i = j
  · subst j
    simp only [formalC, if_true, map_mul, map_neg]
    rw [formalU_outerEval a]
    simp [outerEval, ratConst, Polynomial.evalRingHom,
      Polynomial.eval₂RingHom, p0CQ]
  · simp only [formalC, hij, if_false, map_mul, map_sub]
    rw [formalU_outerEval a, formalU_outerEval a]
    simp [outerEval, ratConst, Polynomial.evalRingHom,
      Polynomial.eval₂RingHom, p0CQ, hij, div_eq_mul_inv]

theorem formalA_outerEval_param_chain (a : ℚ) (g i j : ℕ) :
    outerEval a (formalA g i j) =
      Polynomial.C (p0AQ a g i j) := by
  by_cases hij : i = j
  · subst j
    simp only [formalA, if_true]
    rw [formalU_outerEval a]
    simp [p0AQ]
  · simp [formalA, hij, p0AQ]

theorem formalB_outerEval_param_chain (a : ℚ) (ha : a ≠ 1) (g i j : ℕ) :
    outerEval a (formalB g i j) =
      Polynomial.C ((a - 1) ^ g * p0BQ a g i j) := by
  by_cases hij : i = j
  · subst j
    simp only [formalB, if_true]
    rw [formalBScaled_outerEval_param_chain a ha]
    simp [p0BQ]
  · simp only [formalB, hij, if_false, map_mul, map_sub]
    rw [formalTScaled_outerEval_param_chain a ha,
      formalTScaled_outerEval_param_chain a ha]
    simp [outerEval, ratConst, Polynomial.evalRingHom,
      Polynomial.eval₂RingHom, p0BQ, hij, div_eq_mul_inv]
    ring

/-- Integer specialization commutes with the coefficient embedding. -/
theorem outerEval_psi_int (Z : Polynomial (Polynomial ℤ)) (q : ℤ) :
    outerEval (q : ℚ) (psi Z) =
      Polynomial.map (Int.castRingHom ℚ) (Z.eval (Polynomial.C q)) := by
  symm
  change Polynomial.mapRingHom (Int.castRingHom ℚ)
    (Z.eval (Polynomial.C q)) = _
  rw [mapRingHom_eval]
  have hqcast : Polynomial.mapRingHom (Int.castRingHom ℚ)
      (Polynomial.C q) = Polynomial.C (q : ℚ) := by
    rw [Polynomial.coe_mapRingHom, Polynomial.map_C]
    rfl
  rw [hqcast]
  rfl

/-- The integral formal determinant and its feature divisor specialize at
any integer base. The right side deliberately retains `outerEval`: the
identification with the actual canonical pencil includes its lower-block
scale and must be proved separately. Source: v13 p0-arithmetic.tex:62-126. -/
theorem formal_feature_coeff_witness_int (q : ℤ) (h : ℕ) (hh : 1 ≤ h) :
    ∃ P : Polynomial ℤ,
      (∀ n, q ^ (13 * h ^ 2 - 4 * h) ∣ P.coeff n) ∧
        Polynomial.map (Int.castRingHom ℚ) P =
          Polynomial.C ((p0DenominatorLcm (4 * h) : ℚ) ^ (3 * (4 * h))) *
            outerEval (q : ℚ) (formalCanonicalPolynomial (4 * h)) := by
  obtain ⟨Z, hZ⟩ := formalCanonical_integerized h hh
  have hdivQ : (Polynomial.X : BivPoly) ^ (13 * h ^ 2 - 4 * h) ∣
      Polynomial.map (Polynomial.mapRingHom (Int.castRingHom ℚ)) Z := by
    change (Polynomial.X : BivPoly) ^ (13 * h ^ 2 - 4 * h) ∣ psi Z
    rw [hZ]
    exact dvd_mul_of_dvd_right (formalCanonical_feature_dvd h hh) _
  have hdivZ := int_bivariate_x_pow_dvd_of_rat_map hdivQ
  have hspec := IntegerizationScalarSpecialization.eval_dvd_eval_of_X_pow
    Z (Polynomial.C q) (13 * h ^ 2 - 4 * h) hdivZ
  refine ⟨Z.eval (Polynomial.C q), ?_, ?_⟩
  · intro n
    have hspec' : Polynomial.C (q ^ (13 * h ^ 2 - 4 * h)) ∣
        Z.eval (Polynomial.C q) := by
      simpa only [Polynomial.C_pow] using hspec
    exact (Polynomial.C_dvd_iff_dvd_coeff _ _).mp hspec' n
  · change Polynomial.mapRingHom (Int.castRingHom ℚ)
      (Z.eval (Polynomial.C q)) = _
    rw [mapRingHom_eval]
    have hqcast : Polynomial.mapRingHom (Int.castRingHom ℚ)
        (Polynomial.C q) = Polynomial.C (q : ℚ) := by
      rw [Polynomial.coe_mapRingHom, Polynomial.map_C]
      rfl
    rw [hqcast]
    change outerEval (q : ℚ) (psi Z) = _
    rw [hZ, map_mul]
    simp [outerEval, ratConst]

/-- Evaluating the rescaled formal pencil gives the actual pencil with
exactly the lower-block `(a-1)^g` row factor. -/
theorem poleMatrix_outerEval_param (a : ℚ) (ha : a ≠ 1) (m : ℕ) :
    (outerEval a).mapMatrix (Li2Lean.P0.PoleMatrixCore.poleMatrix m) =
      fun r c => Polynomial.C (p0RowScale a m 1 r) * p0MatrixQ a m r c := by
  classical
  apply Matrix.ext
  intro r c
  change outerEval a (Li2Lean.P0.PoleMatrixCore.poleMatrix m r c) = _
  have hT : outerEval a (Polynomial.C Polynomial.X) = Polynomial.X := by
    simp [outerEval]
  by_cases hr : r.val < m
  · simp [Li2Lean.P0.PoleMatrixCore.poleMatrix, p0MatrixQ, p0RowScale, hr,
      formalC_outerEval_param_chain]
  · simp [Li2Lean.P0.PoleMatrixCore.poleMatrix, p0MatrixQ, p0RowScale, hr,
      formalB_outerEval_param_chain a ha, formalA_outerEval_param_chain,
      outerEval_aVar, outerEval_ratConst, hT]
    ring

/-- The exact generic pencil specialization, retaining the baseline scale. -/
theorem poleDet_outerEval_param (a : ℚ) (ha : a ≠ 1) (m : ℕ) :
    outerEval a (Matrix.det (Li2Lean.P0.PoleMatrixCore.poleMatrix m)) =
      Polynomial.C ((a - 1) ^ (m * (m / 2))) * (p0MatrixQ a m).det := by
  rw [RingHom.map_det, poleMatrix_outerEval_param a ha m, det_row_scale]
  rw [← map_prod, p0RowScale_prod]
  simp

/-- The actual canonical polynomial has an integer baseline witness with
its full `q^N` feature divisor, uniformly in the integer base. The retained
`(q-1)^(gm)` is the exact baseline pole payment; sharpening it to `H_m`
requires the independent endpoint pole lemma. -/
theorem canonical_feature_coeff_witness_int (q : ℤ) (hq : q ≠ 1)
    (h : ℕ) (hh : 1 ≤ h) :
    ∃ P : Polynomial ℤ,
      (∀ n, q ^ (13 * h ^ 2 - 4 * h) ∣ P.coeff n) ∧
        Polynomial.map (Int.castRingHom ℚ) P =
          Polynomial.C
            (((p0DenominatorLcm (4 * h) : ℚ) ^ (3 * (4 * h))) *
              ((q : ℚ) - 1) ^ ((4 * h) * ((4 * h) / 2))) *
            p0CanonicalPolynomial q (4 * h) := by
  obtain ⟨Z, hZ⟩ := formalCanonical_integerized h hh
  let Zs := Li2Lean.P0.Pole.tScaleZ ((4 * h) / 2) Z
  have hZs : psi Zs =
      ratConst ((p0DenominatorLcm (4 * h) : ℚ) ^ (3 * (4 * h))) *
        Matrix.det (Li2Lean.P0.PoleMatrixCore.poleMatrix (4 * h)) := by
    rw [show psi Zs = Li2Lean.P0.PoleMatrixCore.tScale ((4 * h) / 2)
      (psi Z) from Li2Lean.P0.Pole.psi_tScaleZ _ _, hZ, map_mul]
    rw [Li2Lean.P0.PoleMatrixCore.tScale_ratConst,
      ← Li2Lean.P0.PoleMatrixCore.det_poleMatrix_eq]
  have hdiv : (aVar : BivPoly) ^ (13 * h ^ 2 - 4 * h) ∣ psi Z := by
    rw [hZ]
    exact dvd_mul_of_dvd_right (formalCanonical_feature_dvd h hh) _
  have hdivs : (Polynomial.X : BivPoly) ^ (13 * h ^ 2 - 4 * h) ∣ psi Zs := by
    rw [Li2Lean.P0.Pole.psi_tScaleZ]
    have hd := map_dvd (Li2Lean.P0.PoleMatrixCore.tScale ((4 * h) / 2)) hdiv
    rw [map_pow, Li2Lean.P0.PoleMatrixCore.tScale_aVar] at hd
    exact hd
  have hspec := IntegerizationScalarSpecialization.eval_dvd_eval_of_X_pow
    Zs (Polynomial.C q) (13 * h ^ 2 - 4 * h)
    (int_bivariate_x_pow_dvd_of_rat_map hdivs)
  refine ⟨Zs.eval (Polynomial.C q), ?_, ?_⟩
  · intro n
    have hs : Polynomial.C (q ^ (13 * h ^ 2 - 4 * h)) ∣
        Zs.eval (Polynomial.C q) := by
      simpa only [Polynomial.C_pow] using hspec
    exact (Polynomial.C_dvd_iff_dvd_coeff _ _).mp hs n
  · have hqQ : (q : ℚ) ≠ 1 := by exact_mod_cast hq
    rw [← outerEval_psi_int, hZs, map_mul, poleDet_outerEval_param _ hqQ]
    simp only [outerEval_ratConst, p0CanonicalPolynomial, dvd_mul_right, if_true]
    rw [Polynomial.C_mul]
    ring


/-- Away from the fixed factors `q(q-1)`, the coarse integer baseline
already supplies the full formal coefficient credit. This is uniform in
`q`; the pole-order improvement is used only at primes dividing `q-1`.
Source: v13 p0-arithmetic.tex:326-351. -/
theorem canonical_formal_base_coeff (q m p i : ℕ) (hq : 2 ≤ q)
    (hm : 0 < m) (h4 : 4 ∣ m) (hp : p.Prime)
    (hnot : ¬ p ∣ q * (q - 1)) : Li2Lean.P0.p0FormalBaseCoeff q m p i := by
  letI : Fact p.Prime := ⟨hp⟩
  have hpq : ¬ p ∣ q := fun hd => hnot (dvd_mul_of_dvd_left hd _)
  have hpq1 : ¬ p ∣ q - 1 := fun hd => hnot (dvd_mul_of_dvd_right hd _)
  have hqm1 : 0 < q - 1 := by omega
  have hqInt : (q : ℤ) ≠ 1 := by omega
  obtain ⟨h, rfl⟩ := h4
  have hh : 1 ≤ h := by omega
  obtain ⟨P, _, hP⟩ := canonical_feature_coeff_witness_int (q : ℤ) hqInt h hh
  change (p0CanonicalPolynomial (q : ℤ) (4*h)).coeff i = 0 ∨ _
  by_cases hc : (p0CanonicalPolynomial (q : ℤ) (4*h)).coeff i = 0
  · exact Or.inl hc
  · right
    have hcoeff := congrArg (fun R : Polynomial ℚ => R.coeff i) hP
    simp only [Polynomial.coeff_map, Polynomial.coeff_C_mul, Int.cast_natCast] at hcoeff
    change (P.coeff i : ℚ) = _ at hcoeff
    have hbase : ((p0DenominatorLcm (4*h) : ℚ) ^ (3*(4*h))) ≠ 0 :=
      ne_of_gt (p0A2BaselineD_pos hm)
    have hqm1Q : (q : ℚ) - 1 = ((q - 1 : ℕ) : ℚ) := by
      rw [Nat.cast_sub (by omega : 1 ≤ q)]
      norm_num
    have hqm1Qne : (q : ℚ) - 1 ≠ 0 := by
      rw [hqm1Q]
      exact_mod_cast (Nat.ne_of_gt hqm1)
    have hscale : ((p0DenominatorLcm (4*h) : ℚ) ^ (3*(4*h))) *
        ((q : ℚ)-1)^((4*h)*((4*h)/2)) ≠ 0 :=
      mul_ne_zero hbase (pow_ne_zero _ hqm1Qne)
    have hval := congrArg (padicValRat p) hcoeff
    rw [padicValRat.mul hscale hc, padicValRat.mul hbase
      (pow_ne_zero _ hqm1Qne)] at hval
    have hbval : padicValRat p ((p0DenominatorLcm (4*h) : ℚ) ^ (3*(4*h))) =
        (3*(4*h)*Nat.log p (p0DenominatorU (4*h)) : ℕ) :=
      p0A2BaselineD_padicVal hp (4*h)
    rw [hbval, padicValRat.pow, hqm1Q, padicValRat.of_nat,
      padicValNat.eq_zero_of_not_dvd hpq1, padicValRat.of_int] at hval
    simp only [Nat.cast_zero, mul_zero, add_zero] at hval
    unfold Li2Lean.P0.formalDivisorCredit
    rw [padicValNat.eq_zero_of_not_dvd hpq,
      padicValNat.eq_zero_of_not_dvd hpq1]
    simp only [Nat.cast_zero, mul_zero, add_zero, sub_zero]
    change -((3*(4*h)*Nat.log p (p0DenominatorU (4*h)) : ℕ) : ℤ) ≤ _
    omega


/-- At primes where `q-1` is a unit, the complete feature divisor gives
the full signed formal coefficient credit, including the q-adic case.
Source: v13 p0-arithmetic.tex:62-126,326-351. -/
theorem canonical_formal_coeff_of_qSubOne_unit (q m p i : ℕ) (hq : 2 ≤ q)
    (hm : 0 < m) (h4 : 4 ∣ m) (hp : p.Prime)
    (hpq1 : ¬ p ∣ q - 1) : Li2Lean.P0.p0FormalDivisorCoeff q m p i := by
  letI : Fact p.Prime := ⟨hp⟩
  have hqm1 : 0 < q - 1 := by omega
  have hqInt : (q : ℤ) ≠ 1 := by omega
  obtain ⟨h, rfl⟩ := h4
  have hh : 1 ≤ h := by omega
  obtain ⟨P, hdiv, hP⟩ := canonical_feature_coeff_witness_int (q : ℤ) hqInt h hh
  change (p0CanonicalPolynomial (q : ℤ) (4*h)).coeff i = 0 ∨ _
  by_cases hc : (p0CanonicalPolynomial (q : ℤ) (4*h)).coeff i = 0
  · exact Or.inl hc
  · right
    have hcoeff := congrArg (fun R : Polynomial ℚ => R.coeff i) hP
    simp only [Polynomial.coeff_map, Polynomial.coeff_C_mul, Int.cast_natCast] at hcoeff
    change (P.coeff i : ℚ) = _ at hcoeff
    obtain ⟨z, hz⟩ := hdiv i
    rw [hz] at hcoeff
    push_cast at hcoeff
    have hbase : ((p0DenominatorLcm (4*h) : ℚ) ^ (3*(4*h))) ≠ 0 :=
      ne_of_gt (p0A2BaselineD_pos hm)
    have hqm1Q : (q : ℚ) - 1 = ((q - 1 : ℕ) : ℚ) := by
      rw [Nat.cast_sub (by omega : 1 ≤ q)]
      norm_num
    have hqm1Qne : (q : ℚ) - 1 ≠ 0 := by
      rw [hqm1Q]
      exact_mod_cast (Nat.ne_of_gt hqm1)
    have hscale : ((p0DenominatorLcm (4*h) : ℚ) ^ (3*(4*h))) *
        ((q : ℚ)-1)^((4*h)*((4*h)/2)) ≠ 0 :=
      mul_ne_zero hbase (pow_ne_zero _ hqm1Qne)
    have hz0 : (z : ℚ) ≠ 0 := by
      intro hz0
      rw [hz0, mul_zero] at hcoeff
      exact mul_ne_zero hscale hc hcoeff.symm
    have hq0 : (q : ℚ) ≠ 0 := by positivity
    have hval := congrArg (padicValRat p) hcoeff
    rw [padicValRat.mul (pow_ne_zero _ hq0) hz0,
      padicValRat.mul hscale hc, padicValRat.mul hbase
        (pow_ne_zero _ hqm1Qne)] at hval
    have hbval : padicValRat p ((p0DenominatorLcm (4*h) : ℚ) ^ (3*(4*h))) =
        (3*(4*h)*Nat.log p (p0DenominatorU (4*h)) : ℕ) :=
      p0A2BaselineD_padicVal hp (4*h)
    rw [hbval, padicValRat.pow, padicValRat.pow, hqm1Q,
      padicValRat.of_nat, padicValRat.of_nat,
      padicValNat.eq_zero_of_not_dvd hpq1, padicValRat.of_int] at hval
    simp only [Nat.cast_zero, mul_zero, add_zero] at hval
    unfold Li2Lean.P0.formalDivisorCredit
    rw [padicValNat.eq_zero_of_not_dvd hpq1]
    simp only [Nat.cast_zero, mul_zero, add_zero]
    have hN : Li2Lean.P0.formalDivisorN (4*h) = 13*h^2-4*h := by
      simp [Li2Lean.P0.formalDivisorN]
    rw [hN]
    change -((3*(4*h)*Nat.log p (p0DenominatorU (4*h)) : ℕ) -
      (13*h^2-4*h : ℕ)*(padicValNat p q : ℤ)) ≤ _
    omega

/-- The q-adic formal coefficient field of the actual canonical polynomial. -/
theorem canonical_qadic_coeff (q m p i : ℕ) (hq : 2 ≤ q)
    (hm : 0 < m) (h4 : 4 ∣ m) (hp : p.Prime) (hpq : p ∣ q) :
    Li2Lean.P0.p0FormalDivisorCoeff q m p i := by
  have hpq1 : ¬ p ∣ q - 1 := by
    intro hd
    have hp1 : p ∣ 1 := by
      have := Nat.dvd_sub hpq hd
      simpa [Nat.sub_sub_self (by omega : 1 ≤ q)] using this
    exact hp.not_dvd_one hp1
  exact canonical_formal_coeff_of_qSubOne_unit q m p i hq hm h4 hp hpq1

end

end Li2Lean.P0.Integerization.S08

#print axioms Li2Lean.P0.Integerization.S08.formalTScaled_outerEval_param_chain
#print axioms Li2Lean.P0.Integerization.S08.formalBScaled_outerEval_param_chain
#print axioms Li2Lean.P0.Integerization.S08.formalC_outerEval_param_chain
#print axioms Li2Lean.P0.Integerization.S08.formalA_outerEval_param_chain
#print axioms Li2Lean.P0.Integerization.S08.formalB_outerEval_param_chain

#print axioms Li2Lean.P0.Integerization.S08.outerEval_psi_int
#print axioms Li2Lean.P0.Integerization.S08.formal_feature_coeff_witness_int

#print axioms Li2Lean.P0.Integerization.S08.canonical_feature_coeff_witness_int

#print axioms Li2Lean.P0.Integerization.S08.canonical_formal_base_coeff

#print axioms Li2Lean.P0.Integerization.S08.canonical_formal_coeff_of_qSubOne_unit
#print axioms Li2Lean.P0.Integerization.S08.canonical_qadic_coeff
