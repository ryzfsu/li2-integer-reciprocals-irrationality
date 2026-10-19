/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B3.ActualVFormalBase
import Li2Lean.P0.Pole.P0PoleCoefficientsSkeleton
import Li2Lean.P0.Pole.SeparableOrder

namespace Li2Lean.B3

noncomputable section

open Li2Lean.P0.Integerization Li2Lean.P0.Integerization.S08
open Li2Lean.P0.Pole

/-- At the outer point `a = 1`, every signed-V `C` entry has order at least one. -/
theorem vFormalCEntry_shift_X_dvd (i j : ℕ) :
    (Polynomial.X : BivPoly) ∣ shiftB (vFormalCEntry i j) := by
  have hC : vFormalCEntry i j = formalC 0 i j := by
    by_cases hij : i = j
    · simp [vFormalCEntry, formalC, formalU, aVar, ratConst, hij]
    · simp [vFormalCEntry, formalC, formalU, aVar, ratConst, hij,
        div_eq_mul_inv]
  rw [hC, Polynomial.X_dvd_iff, coeff_zero_shift_formalC]
  simp [dd, cq]

/-- Lemma S with row order one on the `4*n` C rows and zero elsewhere.
This is exactly the `(a - 1)^m` credit in the signed v13 formal divisor. -/
theorem vActualFormalDeterminant_shift_X_pow_dvd (n : ℕ) :
    (Polynomial.X : BivPoly) ^ (4 * n) ∣
      shiftB (Matrix.det (vActualFormalSourceMatrix n)) := by
  classical
  let e : Fin (V.vMatrixSize n) → ℕ := fun r =>
    if r.val < 4 * n then 1 else 0
  have hsum : (∑ r, e r) = 4 * n := by
    change (∑ r : Fin (V.vMatrixSize n), if r.val < 4*n then 1 else 0) = _
    rw [Fin.sum_univ_eq_sum_range (fun r => if r < 4*n then 1 else 0)]
    rw [show V.vMatrixSize n = 4*n + 5*n by simp [V.vMatrixSize_eq]; omega,
      Finset.sum_range_add]
    have ht : (∑ r ∈ Finset.range (4*n), if r < 4*n then 1 else 0) = 4*n := by
      calc
        (∑ r ∈ Finset.range (4*n), if r < 4*n then 1 else 0) =
            ∑ _r ∈ Finset.range (4*n), (1 : ℕ) := by
          apply Finset.sum_congr rfl
          intro r hr
          simp [Finset.mem_range.mp hr]
        _ = 4*n := by simp
    have hb : (∑ r ∈ Finset.range (5*n), if 4*n+r < 4*n then 1 else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro r _hr
      simp [show ¬4*n+r < 4*n by omega]
    rw [ht, hb, add_zero]
  have he : ∀ r c : Fin (V.vMatrixSize n),
      (Polynomial.X : BivPoly) ^ (e r + 0) ∣
        (shiftB.mapMatrix (vActualFormalSourceMatrix n)) r c := by
    intro r c
    by_cases hr : r.val < 4*n
    · have hr' : r.val < V.vM n := hr
      simpa [e, hr, vActualFormalSourceMatrix, hr'] using
        vFormalCEntry_shift_X_dvd (V.vIIndexNat n r.val) (V.vJIndex n c)
    · simp [e, hr]
  have hd := separable_order_dvd_det
    (shiftB.mapMatrix (vActualFormalSourceMatrix n)) e (fun _ => 0) he
  rw [hsum] at hd
  simpa only [Finset.sum_const_zero, add_zero, ← RingHom.map_det] using hd

/-- The signed determinant has the outer formal divisor required by v13. -/
theorem vActualFormalDeterminant_aSubOne_pow_dvd (n : ℕ) :
    (aVar - ratConst 1) ^ (4 * n) ∣
      Matrix.det (vActualFormalSourceMatrix n) := by
  have hd := map_dvd unshiftB (vActualFormalDeterminant_shift_X_pow_dvd n)
  simp only [map_pow, unshiftB_shiftB] at hd
  simpa [aVar, ratConst] using hd

private def qSuccBaselineD (n : ℕ) : ℚ :=
  (denominatorLcm (V.vN n) : ℚ) ^ (12 * n) *
    (denominatorLcm (V.vU n) : ℚ) ^ n

private theorem qSuccBaselineD_pos (n : ℕ) : 0 < qSuccBaselineD n := by
  have hN : 0 < denominatorLcm (V.vN n) := Nat.lcmUpto_pos _
  have hU : 0 < denominatorLcm (V.vU n) := Nat.lcmUpto_pos _
  unfold qSuccBaselineD
  positivity

private theorem qSuccBaselineD_padicVal (n p : ℕ) (hp : p.Prime) :
    padicValRat p (qSuccBaselineD n) =
      ((12 * n * Nat.log p (V.vN n) + n * Nat.log p (V.vU n) : ℕ) : ℤ) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hd (U : ℕ) : padicValNat p (denominatorLcm U) = Nat.log p U := by
    have h := Nat.factorization_lcmUpto U hp
    rw [Nat.factorization_def _ hp] at h
    exact h
  have hN : (denominatorLcm (V.vN n) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.lcmUpto_ne_zero (V.vN n))
  have hU : (denominatorLcm (V.vU n) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.lcmUpto_ne_zero (V.vU n))
  rw [qSuccBaselineD, padicValRat.mul (pow_ne_zero _ hN) (pow_ne_zero _ hU),
    padicValRat.pow, padicValRat.pow, padicValRat.of_nat,
    padicValRat.of_nat, hd, hd]
  push_cast <;> ring

private theorem qSucc_outerEval_psi_int
    (Z : Polynomial (Polynomial ℤ)) (a : ℤ) :
    outerEval (a : ℚ) (psi Z) =
      (Z.eval (Polynomial.C a)).map (Int.castRingHom ℚ) := by
  simp [outerEval, psi]

private theorem qSucc_actualVDeterminant_zero (q : ℕ) :
    V.actualVDeterminant q 0 = 1 := by
  change V.vPolynomial 0 (-(q : ℤ)) = 1
  haveI : IsEmpty (Fin (V.vMatrixSize 0)) := by
    simp [V.vMatrixSize, V.vM, V.vS]
  exact Matrix.det_isEmpty

private theorem actualV_q_succ_coeff_witness_of_divisor
    (q n : ℕ) (hn : 0 < n)
    (hPole : (aVar - ratConst 1) ^ (4 * n) ∣
      Matrix.det (vActualFormalSourceMatrix n)) :
    ∃ P : Polynomial ℤ,
      (∀ i, (-((q + 1 : ℕ) : ℤ)) ^ (4 * n) ∣ P.coeff i) ∧
      P.map (Int.castRingHom ℚ) =
        Polynomial.C (qSuccBaselineD n) * V.actualVDeterminant q (4 * n) := by
  obtain ⟨Z, hZ⟩ := vActualFormalDeterminant_integerized n hn
  let W := Matrix.det Z
  have hW : psi W = ratConst (qSuccBaselineD n) *
      Matrix.det (vActualFormalSourceMatrix n) := by
    rw [show psi W = _ from hZ]
    congr 1
    change (∏ r, rc (vActualFormalRowScale n r)) = rc (qSuccBaselineD n)
    rw [← map_prod, vActualFormalRowScale_prod] <;> rfl
  let shiftZ : Polynomial (Polynomial ℤ) →+* Polynomial (Polynomial ℤ) :=
    Polynomial.compRingHom (Polynomial.X + 1)
  have hshift (Y : Polynomial (Polynomial ℤ)) :
      psi (shiftZ Y) = shiftB (psi Y) := by
    simp [shiftZ, psi, shiftB, Polynomial.map_comp]
  have hdivQ : (Polynomial.X : BivPoly) ^ (4 * n) ∣ psi (shiftZ W) := by
    rw [hshift, hW, map_mul, shiftB_ratConst]
    have hd := map_dvd shiftB hPole
    exact dvd_mul_of_dvd_right
      (by simpa only [map_pow, shiftB_aVar_sub_one] using hd) _
  have hdivZ := int_bivariate_x_pow_dvd_of_rat_map hdivQ
  have heval := IntegerizationScalarSpecialization.eval_dvd_eval_of_X_pow
    (shiftZ W) (Polynomial.C (-((q + 1 : ℕ) : ℤ))) (4 * n) hdivZ
  have heval_eq : (shiftZ W).eval (Polynomial.C (-((q + 1 : ℕ) : ℤ))) =
      W.eval (Polynomial.C (-(q : ℤ))) := by
    change (W.comp (Polynomial.X + 1)).eval
      (Polynomial.C (-((q + 1 : ℕ) : ℤ))) = _
    rw [Polynomial.eval_comp]
    have he : -((q + 1 : ℕ) : ℤ) + 1 = -(q : ℤ) := by omega
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
    rw [← Polynomial.C_1, ← Polynomial.C_add, he]
  rw [heval_eq] at heval
  refine ⟨W.eval (Polynomial.C (-(q : ℤ))), ?_, ?_⟩
  · intro i
    have hd : Polynomial.C ((-((q + 1 : ℕ) : ℤ)) ^ (4 * n)) ∣
        W.eval (Polynomial.C (-(q : ℤ))) := by
      simpa only [Polynomial.C_pow] using heval
    exact (Polynomial.C_dvd_iff_dvd_coeff _ _).mp hd i
  · rw [← qSucc_outerEval_psi_int, hW, map_mul]
    simp only [Int.cast_neg, Int.cast_natCast, outerEval_ratConst,
      outerEval_actualVDeterminant]

private theorem actualV_q_succ_coeff_val_of_divisor
    (q n p i : ℕ) (hn : 0 < n) (hp : p.Prime)
    (hPole : (aVar - ratConst 1) ^ (4 * n) ∣
      Matrix.det (vActualFormalSourceMatrix n))
    (hc : (V.actualVDeterminant q (4 * n)).coeff i ≠ 0) :
    ((4 * n * padicValNat p (q + 1) : ℕ) : ℤ) -
        ((12 * n * Nat.log p (V.vN n) + n * Nat.log p (V.vU n) : ℕ) : ℤ) ≤
      padicValRat p ((V.actualVDeterminant q (4 * n)).coeff i) := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, hdiv, hP⟩ := actualV_q_succ_coeff_witness_of_divisor q n hn hPole
  have hcoeff := congrArg (fun Q : Polynomial ℚ => Q.coeff i) hP
  simp only [Polynomial.coeff_map, Polynomial.coeff_C_mul] at hcoeff
  change (P.coeff i : ℚ) =
    qSuccBaselineD n * (V.actualVDeterminant q (4 * n)).coeff i at hcoeff
  obtain ⟨z, hz⟩ := hdiv i
  rw [hz] at hcoeff
  simp only [Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_natCast] at hcoeff
  have hbase : qSuccBaselineD n ≠ 0 := ne_of_gt (qSuccBaselineD_pos n)
  have ha : (-((q + 1 : ℕ) : ℚ)) ≠ 0 := by
    apply neg_ne_zero.mpr
    positivity
  have hz0 : (z : ℚ) ≠ 0 := by
    intro hz0
    rw [hz0, mul_zero] at hcoeff
    exact mul_ne_zero hbase hc hcoeff.symm
  have hval := congrArg (padicValRat p) hcoeff
  rw [padicValRat.mul (pow_ne_zero _ ha) hz0,
    padicValRat.mul hbase hc, padicValRat.pow,
    padicValRat.neg, padicValRat.of_nat, padicValRat.of_int,
    qSuccBaselineD_padicVal n p hp] at hval
  push_cast at hval ⊢
  omega

/-- The v13 exceptional-prime credit at every prime dividing `q + 1`.
The zero coefficient is stated separately because `padicValRat p 0 = 0`.
-/
theorem actualV_coeff_val_of_dvd_q_succ
    (q n p i : ℕ) (hp : p.Prime) (_hpq1 : p ∣ q + 1) :
    (V.actualVDeterminant q (4 * n)).coeff i = 0 ∨
      ((4 * n * padicValNat p (q + 1) : ℕ) : ℤ) -
          ((12 * n * Nat.log p (V.vN n) + n * Nat.log p (V.vU n) : ℕ) : ℤ) ≤
        padicValRat p ((V.actualVDeterminant q (4 * n)).coeff i) := by
  by_cases hc : (V.actualVDeterminant q (4 * n)).coeff i = 0
  · exact Or.inl hc
  right
  by_cases hn : n = 0
  · subst n
    by_cases hi : i = 0 <;>
      simp [hi, qSucc_actualVDeterminant_zero, Polynomial.coeff_one]
  · exact actualV_q_succ_coeff_val_of_divisor q n p i
      (Nat.pos_of_ne_zero hn) hp (vActualFormalDeterminant_aSubOne_pow_dvd n) hc

private theorem actualV_q_succ_exponent_nonneg
    (q n p : ℕ) (hq : q ≤ 7) :
    0 ≤ ((12 * n * Nat.log p (V.vN n) +
        n * Nat.log p (V.vU n) : ℕ) : ℤ) -
      ((4 * n * padicValNat p (q + 1) : ℕ) : ℤ) := by
  by_cases hn : n = 0
  · simp [hn]
  have hqN : q + 1 ≤ V.vN n := by
    dsimp [V.vN]
    omega
  have hlog : padicValNat p (q + 1) ≤ Nat.log p (V.vN n) :=
    (padicValNat_le_nat_log (q + 1)).trans (Nat.log_mono_right hqN)
  have hnat : 4 * n * padicValNat p (q + 1) ≤
      12 * n * Nat.log p (V.vN n) + n * Nat.log p (V.vU n) := by
    calc
      4 * n * padicValNat p (q + 1) ≤
          4 * n * Nat.log p (V.vN n) := Nat.mul_le_mul_left _ hlog
      _ ≤ 12 * n * Nat.log p (V.vN n) :=
        Nat.mul_le_mul_right _ (by omega)
      _ ≤ 12 * n * Nat.log p (V.vN n) + n * Nat.log p (V.vU n) :=
        Nat.le_add_right _ _
  exact sub_nonneg.mpr (by exact_mod_cast hnat)

/-- Gauss valuation form of the exceptional `q+1` credit, including the
empty-support convention and the index zero. -/
theorem actualV_gauss_val_of_dvd_q_succ
    (q n p : ℕ) (hq : q ≤ 7) (hp : p.Prime) (hpq1 : p ∣ q + 1) :
    ((4 * n * padicValNat p (q + 1) : ℕ) : ℤ) -
        ((12 * n * Nat.log p (V.vN n) + n * Nat.log p (V.vU n) : ℕ) : ℤ) ≤
      V.actualGaussValuation p (V.actualVDeterminant q (4 * n)) := by
  have h := actualGaussValuation_ge_of_coeff_ge p
    (V.actualVDeterminant q (4 * n))
    (((12 * n * Nat.log p (V.vN n) + n * Nat.log p (V.vU n) : ℕ) : ℤ) -
      ((4 * n * padicValNat p (q + 1) : ℕ) : ℤ))
    (actualV_q_succ_exponent_nonneg q n p hq)
    (fun i hi => by
      simpa only [neg_sub] using
        (actualV_coeff_val_of_dvd_q_succ q n p i hp hpq1).resolve_left hi)
  simpa only [neg_sub] using h

/-- The literal first-line v13 exponent on the `p ∣ q+1` branch.
The `q` credit vanishes because consecutive integers are coprime. -/
theorem actualV_v13_gauss_val_of_dvd_q_succ
    (q n p : ℕ) (hq : q ≤ 7) (hp : p.Prime) (hpq1 : p ∣ q + 1) :
    V.actualGaussValuation p (V.actualVDeterminant q (4 * n)) ≥
      -(((12 * n * Nat.log p (V.vN n) + n * Nat.log p (V.vU n) : ℕ) : ℤ) -
        (padicValNat p q : ℤ) *
          (((53 * n ^ 2 + 2) / 3 - 4 * n : ℕ) : ℤ) -
        ((4 * n * padicValNat p (q + 1) : ℕ) : ℤ)) := by
  have hpq : ¬ p ∣ q := by
    intro hd
    have h1 : p ∣ 1 := by
      simpa using Nat.dvd_sub hpq1 hd
    exact hp.ne_one (Nat.dvd_one.mp h1)
  simpa only [padicValNat.eq_zero_of_not_dvd hpq, Nat.cast_zero,
    zero_mul, sub_zero, neg_sub] using
    actualV_gauss_val_of_dvd_q_succ q n p hq hp hpq1

end
end Li2Lean.B3

#print axioms Li2Lean.B3.vActualFormalDeterminant_aSubOne_pow_dvd
#print axioms Li2Lean.B3.actualV_coeff_val_of_dvd_q_succ
#print axioms Li2Lean.B3.actualV_v13_gauss_val_of_dvd_q_succ
