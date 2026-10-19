/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B3.ActualFrobeniusProducer

namespace Li2Lean.B3

noncomputable section

open Li2Lean

/-- If every entry of an integer polynomial matrix is affine in `X` and its
linear part carries `Q^2`, then the `i`-th determinant coefficient carries
`Q^(2*i)`.  This is the algebraic Frobenius divisibility kernel; it does not
assert that a particular row-clearing witness has this affine shape. -/
theorem det_coeff_dvd_pow_of_affine
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q i : ℕ) (M : Matrix ι ι (Polynomial ℤ))
    (A B : Matrix ι ι ℤ)
    (hM : ∀ r c,
      M r c = Polynomial.C (A r c) +
        Polynomial.C (Q ^ 2 : ℤ) * Polynomial.X * Polynomial.C (B r c)) :
    (Q ^ (2 * i) : ℤ) ∣ (M.det).coeff i := by
  let f : Polynomial ℤ →+* Polynomial ℤ :=
    Polynomial.eval₂RingHom Polynomial.C
      (Polynomial.C (Q ^ 2 : ℤ) * Polynomial.X)
  let K : Matrix ι ι (Polynomial ℤ) :=
    fun r c => Polynomial.C (A r c) + Polynomial.X * Polynomial.C (B r c)
  have hC (z : ℤ) : f (Polynomial.C z) = Polynomial.C z := by
    simp [f]
  have hX : f Polynomial.X = Polynomial.C (Q ^ 2 : ℤ) * Polynomial.X := by
    simp [f, Polynomial.eval₂RingHom, Polynomial.eval₂_X]
  have hmatrix : M = f.mapMatrix K := by
    funext r c
    change M r c = f (K r c)
    rw [hM r c]
    change Polynomial.C (A r c) +
      Polynomial.C (Q ^ 2 : ℤ) * Polynomial.X * Polynomial.C (B r c) =
      f (Polynomial.C (A r c) + Polynomial.X * Polynomial.C (B r c))
    rw [map_add, map_mul, hC, hX, hC]
  have hdet : M.det = f (K.det) := by
    rw [hmatrix, RingHom.map_det]
  have hcomp : f (K.det) =
      (K.det).comp (Polynomial.C (Q ^ 2 : ℤ) * Polynomial.X) := rfl
  rw [hdet, hcomp, Polynomial.comp_C_mul_X_coeff]
  refine ⟨(K.det).coeff i, ?_⟩
  rw [← pow_mul]
  ring

/-- Coefficients of the actual scaled polynomial after the linear substitution.
The index bound is explicit because the exponent is represented in `Nat`.
This is only an algebraic transport identity; it does not assert a valuation
bound for the determinant polynomial. -/
theorem scaled_coeff_eq {q p k i : ℕ}
    (hp : 0 < p) (hi : i ≤ 4 * p ^ k) :
    (V.vFrobeniusScaledPolynomial q p k).coeff i =
      (((p ^ k : ℕ) : ℚ) ^ (13 * (p ^ k) - 2 * i)) *
        (V.vPolynomial (p ^ k) (-(q : ℤ))).coeff i := by
  unfold V.vFrobeniusScaledPolynomial
  rw [Polynomial.coeff_C_mul, Polynomial.comp_C_mul_X_coeff]
  have hQr : (((p ^ k : ℕ) : ℚ) ^ 2) ≠ 0 := by positivity
  have h2 : 2 * i ≤ 13 * (p ^ k) := by omega
  rw [← inv_pow]
  rw [← pow_mul]
  rw [inv_pow]
  field_simp [hQr]
  have hpow :
      (((p ^ k : ℕ) : ℚ) ^ (2 * i)) *
          (((p ^ k : ℕ) : ℚ) ^ (13 * p ^ k - 2 * i)) =
        ((p ^ k : ℕ) : ℚ) ^ (13 * p ^ k) := by
    rw [← pow_add, Nat.add_comm, Nat.sub_add_cancel h2]
  calc
    ((p ^ k : ℕ) : ℚ) ^ (13 * p ^ k) *
        (V.vPolynomial (p ^ k) (-(q : ℤ))).coeff i =
      (V.vPolynomial (p ^ k) (-(q : ℤ))).coeff i *
        ((p ^ k : ℕ) : ℚ) ^ (13 * p ^ k) := by ring
    _ = (V.vPolynomial (p ^ k) (-(q : ℤ))).coeff i *
        ((((p ^ k : ℕ) : ℚ) ^ (2 * i)) *
          (((p ^ k : ℕ) : ℚ) ^ (13 * p ^ k - 2 * i))) := by rw [hpow]
    _ = (V.vPolynomial (p ^ k) (-(q : ℤ))).coeff i *
        ((p ^ k : ℕ) : ℚ) ^ (2 * i) *
        ((p ^ k : ℕ) : ℚ) ^ (13 * p ^ k - 2 * i) := by ring

/-- A source-level row valuation bound transports to integrality of the
actual scaled coefficient.  The row bound is deliberately an input: finite
seed residue data does not imply it. -/
theorem scaled_coeff_integral_of_row_bound
    {q p k i : ℕ} (hp : Nat.Prime p)
    (hi : i ≤ 4 * p ^ k)
    (hrow : -(((13 * p ^ k - 2 * i : ℕ) : ℤ) * (k : ℤ)) ≤
      padicValRat p ((V.vPolynomial (p ^ k) (-(q : ℤ))).coeff i))
    (hscaled : (V.vFrobeniusScaledPolynomial q p k).coeff i ≠ 0) :
    0 ≤ padicValRat p ((V.vFrobeniusScaledPolynomial q p k).coeff i) := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  have hQrat : (((p ^ k : ℕ) : ℚ) ^ (13 * p ^ k - 2 * i)) ≠ 0 := by
    exact pow_ne_zero _ (Nat.cast_ne_zero.mpr (pow_ne_zero _ hp.ne_zero))
  have hP : (V.vPolynomial (p ^ k) (-(q : ℤ))).coeff i ≠ 0 := by
    intro hzero
    rw [scaled_coeff_eq (q := q) (p := p) (k := k) (i := i) hp.pos hi,
      hzero, mul_zero] at hscaled
    exact hscaled rfl
  have hval := congrArg (padicValRat p)
    (scaled_coeff_eq (q := q) (p := p) (k := k) (i := i) hp.pos hi)
  have hpval : padicValRat p (((p ^ k : ℕ) : ℚ)) = (k : ℤ) := by
    rw [padicValRat.of_nat, padicValNat.pow, padicValNat_self]
    simp
  rw [padicValRat.mul hQrat hP, padicValRat.pow, hpval] at hval
  omega


/-!
The finite p-adic tail estimate used by v13's scaled determinant argument.
The application below remains pinned to the existing
V.vFrobeniusScaledPolynomial from V.NonvanishingPlan.
Sources: v13 nonvanishing.tex:200-275.
-/

theorem padicNorm_poly_eval_sub_coeff_zero_lt
    {p : ℕ} [Fact (Nat.Prime p)] (P : Polynomial ℚ) (x : ℚ)
    (hcoeff : ∀ i : ℕ, P.coeff i ≠ 0 → 0 ≤ padicValRat p (P.coeff i))
    (hconst : P.coeff 0 ≠ 0)
    (hunit : padicValRat p (P.coeff 0) = 0)
    (hx : padicNorm p x < 1) :
    padicNorm p (P.eval x - P.coeff 0) < padicNorm p (P.coeff 0) := by
  have hconst_norm : padicNorm p (P.coeff 0) = 1 := by
    rw [padicNorm.eq_zpow_of_nonzero hconst, hunit]
    simp
  let T : Polynomial ℚ := P - Polynomial.C (P.coeff 0)
  have hT0 : T.coeff 0 = 0 := by simp [T]
  have heval : P.eval x - P.coeff 0 = T.eval x := by
    dsimp [T]
    rw [Polynomial.eval_sub, Polynomial.eval_C]
  have hnorm_pow (i : ℕ) : padicNorm p (x ^ i) = padicNorm p x ^ i := by
    induction i with
    | zero => simp
    | succ i ih =>
        rw [pow_succ, padicNorm.mul, ih, pow_succ]
  rw [heval, hconst_norm]
  rw [Polynomial.eval_eq_sum]
  change padicNorm p (∑ i ∈ T.support, T.coeff i * x ^ i) < 1
  apply padicNorm.sum_lt' (s := T.support) ?_ (by norm_num)
  intro i hi
  have hTi : T.coeff i ≠ 0 := Polynomial.mem_support_iff.mp hi
  have hi_pos : 0 < i := by
    cases i with
    | zero => simp [hT0] at hTi
    | succ i => omega
  have hcoeff_eq : T.coeff i = P.coeff i := by
    cases i with
    | zero => omega
    | succ j => simp [T]
  have hPi : P.coeff i ≠ 0 := by rw [← hcoeff_eq]; exact hTi
  have hval : 0 ≤ padicValRat p (T.coeff i) := by
    rw [hcoeff_eq]
    exact hcoeff i hPi
  have hnorm_coeff : padicNorm p (T.coeff i) ≤ 1 := by
    by_cases hzero : T.coeff i = 0
    · simp [hzero]
    · rw [padicNorm.eq_zpow_of_nonzero hzero]
      apply zpow_le_one_of_nonpos₀
      · exact_mod_cast (Nat.Prime.one_le (Fact.out : Nat.Prime p))
      · exact neg_nonpos.mpr hval
  rw [padicNorm.mul, hnorm_pow]
  calc
    padicNorm p (T.coeff i) * padicNorm p x ^ i ≤
        1 * padicNorm p x ^ i :=
      mul_le_mul_of_nonneg_right hnorm_coeff
        (pow_nonneg (padicNorm.nonneg x) i)
    _ = padicNorm p x ^ i := one_mul _
    _ < 1 := pow_lt_one₀ (padicNorm.nonneg _) hx hi_pos.ne'

/-!
The scaled argument in v13 is p^(2k) * r; its valuation tends to
+∞ with k. This is the eventual smallness input for the strict tail
estimate above. Source: v13 nonvanishing.tex:200-275.
-/
theorem padicNorm_scaled_argument_lt_eventually
    {p : ℕ} [Fact (Nat.Prime p)] (r : ℚ) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      padicNorm p ((((p ^ k : ℕ) : ℚ) ^ 2) * r) < 1 := by
  by_cases hr : r = 0
  · refine ⟨0, fun k hk => ?_⟩
    simp [hr]
  · let v : ℤ := padicValRat p r
    let k₀ : ℕ := v.natAbs + 1
    refine ⟨k₀, fun k hk => ?_⟩
    let c : ℚ := ((p ^ k : ℕ) : ℚ)
    have hc : c ≠ 0 := by
      dsimp [c]
      exact_mod_cast (pow_ne_zero k (Nat.Prime.ne_zero (Fact.out : Nat.Prime p)))
    have hval_c : padicValRat p c = (k : ℤ) := by
      dsimp [c]
      rw [padicValRat.of_nat, padicValNat.pow, padicValNat_self]
      simp
    have hval_x : padicValRat p (c ^ 2 * r) = 2 * (k : ℤ) + v := by
      dsimp [v]
      rw [padicValRat.mul (pow_ne_zero 2 hc) hr, padicValRat.pow, hval_c]
      ring
    have hkz : ((k₀ : ℕ) : ℤ) ≤ k := by exact_mod_cast hk
    have hvneg : -v ≤ (v.natAbs : ℤ) := by
      calc
        -v ≤ (-v).natAbs := Int.le_natAbs
        _ = (v.natAbs : ℤ) := by simp
    have hpositive : 0 < 2 * (k : ℤ) + v := by
      dsimp [k₀] at hkz
      omega
    have hxne : c ^ 2 * r ≠ 0 := mul_ne_zero (pow_ne_zero 2 hc) hr
    have hp_gt : (1 : ℚ) < p := by
      exact_mod_cast (Nat.Prime.one_lt (Fact.out : Nat.Prime p))
    rw [show ((((p ^ k : ℕ) : ℚ) ^ 2) * r) = c ^ 2 * r by rfl,
      padicNorm.eq_zpow_of_nonzero hxne, hval_x]
    exact (zpow_lt_one_iff_right₀ hp_gt).2 (by omega)

/-- v13's strict-tail field follows from the actual scaled coefficients being
p-integral and the actual scaled constant being a nonzero p-adic unit. This
uses the unchanged scaled determinant definition in V.NonvanishingPlan.
Source: v13 nonvanishing.tex:200-275. -/
theorem vActualStrictTail_of_coefficient_fields
    {q p : ℕ} (hp : Nat.Prime p)
    (hcoeff : ∀ k : ℕ, 0 < k → ∀ i : ℕ,
      (V.vFrobeniusScaledPolynomial q p k).coeff i ≠ 0 →
        0 ≤ padicValRat p ((V.vFrobeniusScaledPolynomial q p k).coeff i))
    (hconst : ∀ k : ℕ, 0 < k →
      (V.vFrobeniusScaledPolynomial q p k).coeff 0 ≠ 0 ∧
        padicValRat p ((V.vFrobeniusScaledPolynomial q p k).coeff 0) = 0) :
    ∀ r : ℚ, ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      V.VUnitConstantEvaluationInput q p k
        ((((p ^ k : ℕ) : ℚ) ^ 2) * r) := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  intro r
  obtain ⟨k₀, hk₀⟩ :=
    padicNorm_scaled_argument_lt_eventually (p := p) r
  refine ⟨max 1 k₀, fun k hk => ?_⟩
  have hkpos : 0 < k :=
    lt_of_lt_of_le Nat.zero_lt_one (le_trans (le_max_left 1 k₀) hk)
  have hkarg : k₀ ≤ k :=
    le_trans (le_max_right 1 k₀) hk
  have hxsmall := hk₀ k hkarg
  refine ⟨hp, (hconst k hkpos).1, (hconst k hkpos).2, ?_⟩
  exact padicNorm_poly_eval_sub_coeff_zero_lt
    (V.vFrobeniusScaledPolynomial q p k)
    ((((p ^ k : ℕ) : ℚ) ^ 2) * r)
    (fun i hi => hcoeff k hkpos i hi)
    (hconst k hkpos).1 (hconst k hkpos).2 hxsmall

end
end Li2Lean.B3

#print axioms Li2Lean.B3.scaled_coeff_eq
#print axioms Li2Lean.B3.scaled_coeff_integral_of_row_bound
#print axioms Li2Lean.B3.det_coeff_dvd_pow_of_affine
