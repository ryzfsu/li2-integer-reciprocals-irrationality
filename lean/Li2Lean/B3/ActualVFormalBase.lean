/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/

import Li2Lean.B3.ArithmeticPinning
import Li2Lean.P0.IntegerizationFormalBaseParam
import Li2Lean.P0.IntegerizationS08Lift

/-!
# Formal outer parameter for the signed V determinant

This module keeps the V construction separate from the P0 determinant.  It
provides the outer-evaluation interface needed to transfer formal coefficient
bounds to the actual signed determinant.
-/

namespace Li2Lean.B3

noncomputable section

open Li2Lean.P0.Integerization
open Li2Lean.P0.Integerization.S08

abbrev VActualBivPoly := BivPoly

def vFormalMomentT (j : ℕ) : VActualBivPoly :=
  ∑ r ∈ Finset.range j,
    aVar ^ (j - (r + 1)) * ratConst (((r + 1 : ℕ) : ℚ)⁻¹)

def vFormalMomentB (j : ℕ) : VActualBivPoly :=
  ∑ r ∈ Finset.range j,
    aVar ^ (j - (r + 1)) *
      ratConst ((((r + 1 : ℕ) : ℚ) ^ 2)⁻¹)

def vFormalCEntry (i j : ℕ) : VActualBivPoly :=
  if i = j then 0 else
    (aVar ^ i - aVar ^ j) * ratConst (((j : ℚ) - (i : ℚ))⁻¹)

def vFormalBEntry (i j : ℕ) : VActualBivPoly :=
  if i = j then vFormalMomentB i else
    (vFormalMomentT i - vFormalMomentT j) *
      ratConst (((j : ℚ) - (i : ℚ))⁻¹)

def vFormalAEntry (i j : ℕ) : VActualBivPoly :=
  if i = j then aVar ^ i else 0

def vFormalVEntry (j ell : ℕ) : VActualBivPoly :=
  ratConst (((j + ell : ℕ) : ℚ)⁻¹)

def vFormalT : VActualBivPoly := Polynomial.C Polynomial.X

theorem outerEval_vFormalT (a : ℤ) :
    outerEval (a : ℚ) vFormalT = Polynomial.X := by
  simp [vFormalT, outerEval]

theorem outerEval_vFormalVEntry (a : ℤ) (j ell : ℕ) :
    outerEval (a : ℚ) (vFormalVEntry j ell) =
      Polynomial.C (V.vVEntry j ell) := by
  simp [vFormalVEntry, V.vVEntry, outerEval_ratConst]

/-- The formal source matrix for v13's signed-V determinant, with the outer
base left as a polynomial variable. This is defined from V's `[C; B-XA; V]`
matrix itself, independently of P0's formal determinant. -/
def vActualFormalSourceMatrix (n : ℕ) :
    Matrix (Fin (V.vMatrixSize n)) (Fin (V.vMatrixSize n)) VActualBivPoly :=
  fun r c =>
    let j := V.vJIndex n c
    if r.val < V.vM n then
      vFormalCEntry (V.vIIndexNat n r.val) j
    else if r.val < 2 * V.vM n then
      let i := 2 * n + (r.val - V.vM n)
      vFormalBEntry i j - vFormalT * vFormalAEntry i j
    else
      vFormalVEntry j (1 + (r.val - 2 * V.vM n))

theorem outerEval_vFormalMomentT (a : ℤ) (j : ℕ) :
    outerEval (a : ℚ) (vFormalMomentT j) =
      Polynomial.C (V.vMomentT a j) := by
  simp [vFormalMomentT, V.vMomentT, outerEval_aVar, outerEval_ratConst]

theorem outerEval_vFormalMomentB (a : ℤ) (j : ℕ) :
    outerEval (a : ℚ) (vFormalMomentB j) =
      Polynomial.C (V.vMomentB a j) := by
  simp [vFormalMomentB, V.vMomentB, outerEval_aVar, outerEval_ratConst]

theorem outerEval_vFormalCEntry (a : ℤ) (i j : ℕ) :
    outerEval (a : ℚ) (vFormalCEntry i j) =
      Polynomial.C (V.vCEntry a i j) := by
  by_cases hij : i = j <;>
    simp [vFormalCEntry, V.vCEntry, hij, outerEval_aVar,
      outerEval_ratConst, div_eq_mul_inv]

theorem outerEval_vFormalBEntry (a : ℤ) (i j : ℕ) :
    outerEval (a : ℚ) (vFormalBEntry i j) =
      Polynomial.C (V.vBEntry a i j) := by
  by_cases hij : i = j
  · simp [vFormalBEntry, V.vBEntry, hij, outerEval_vFormalMomentB]
  · simp [vFormalBEntry, V.vBEntry, hij, outerEval_vFormalMomentT,
      outerEval_ratConst, div_eq_mul_inv]

theorem outerEval_vFormalAEntry (a : ℤ) (i j : ℕ) :
    outerEval (a : ℚ) (vFormalAEntry i j) =
      Polynomial.C (V.vAEntry a i j) := by
  by_cases hij : i = j <;>
    simp [vFormalAEntry, V.vAEntry, hij, outerEval_aVar]

theorem vActualFormalSourceMatrix_outerEval (n : ℕ) (a : ℤ) :
    (outerEval (a : ℚ)).mapMatrix (vActualFormalSourceMatrix n) =
      V.vSourceMatrix n a := by
  funext r c
  change outerEval (a : ℚ) (vActualFormalSourceMatrix n r c) =
    V.vSourceMatrix n a r c
  dsimp [vActualFormalSourceMatrix, V.vSourceMatrix]
  by_cases h1 : r.val < V.vM n
  · simp [h1, outerEval_vFormalCEntry]
  · by_cases h2 : r.val < 2 * V.vM n
    · simp [h1, h2, outerEval_vFormalBEntry, outerEval_vFormalAEntry,
        outerEval_vFormalT]
    · simp [h1, h2, outerEval_vFormalVEntry]

theorem outerEval_vActualFormalDeterminant (n : ℕ) (a : ℤ) :
    outerEval (a : ℚ) (Matrix.det (vActualFormalSourceMatrix n)) =
      V.vPolynomial n a := by
  calc
    outerEval (a : ℚ) (Matrix.det (vActualFormalSourceMatrix n)) =
        Matrix.det ((outerEval (a : ℚ)).mapMatrix
          (vActualFormalSourceMatrix n)) :=
          RingHom.map_det (outerEval (a : ℚ)) (vActualFormalSourceMatrix n)
    _ = Matrix.det (V.vSourceMatrix n a) := by
      rw [vActualFormalSourceMatrix_outerEval]
    _ = V.vPolynomial n a := rfl

theorem outerEval_actualVDeterminant (q n : ℕ) :
    outerEval (-(q : ℚ)) (Matrix.det (vActualFormalSourceMatrix n)) =
      V.actualVDeterminant q (4 * n) := by
  have h := outerEval_vActualFormalDeterminant n (-(q : ℤ))
  rw [V.actualVDeterminant_four_mul]
  simpa using h

private theorem vFormalMomentT_eq_formalTScaled (j : ℕ) :
    vFormalMomentT j = formalTScaled 0 j := by
  simp [vFormalMomentT, formalTScaled, formalU, formalQNum, aVar, ratConst]

private theorem vFormalMomentB_eq_formalBScaled (j : ℕ) :
    vFormalMomentB j = formalBScaled 0 j := by
  simp [vFormalMomentB, formalBScaled, formalU, formalQNum, aVar, ratConst]

private theorem vFormalCEntry_eq_formalC (i j : ℕ) :
    vFormalCEntry i j = formalC 0 i j := by
  by_cases hij : i = j
  · simp [vFormalCEntry, formalC, formalU, aVar, ratConst, hij]
  · simp [vFormalCEntry, formalC, formalU, aVar, ratConst, hij,
      div_eq_mul_inv]

private theorem vFormalBEntry_eq_formalB (i j : ℕ) :
    vFormalBEntry i j = formalB 0 i j := by
  by_cases hij : i = j
  · simp [vFormalBEntry, formalB, vFormalMomentB_eq_formalBScaled, hij]
  · simp [vFormalBEntry, formalB, vFormalMomentT_eq_formalTScaled, hij,
      div_eq_mul_inv]

private theorem vFormalAEntry_eq_formalA (i j : ℕ) :
    vFormalAEntry i j = formalA 0 i j := by
  by_cases hij : i = j <;>
    simp [vFormalAEntry, formalA, formalU, aVar, ratConst, hij]

/-- Denominator scales for the literal V rows. The first two row blocks use
the `10*n-1` cutoff; the Cauchy block uses the larger `11*n-1` cutoff. -/
def vActualFormalRowScale (n : ℕ) : Fin (V.vMatrixSize n) → ℚ := fun r =>
  if r.val < V.vM n then (denominatorLcm (V.vN n) : ℚ)
  else if r.val < 2 * V.vM n then (denominatorLcm (V.vN n) : ℚ) ^ 2
  else (denominatorLcm (V.vU n) : ℚ)

/-- Every row-scaled entry of the actual formal V pencil lies in the integer
bivariate subring. This is only denominator clearing; it does not assert the
separate formal divisor needed for the exceptional-prime credits. -/
theorem vActualFormalScaledEntry_mem (n : ℕ) (hn : 0 < n)
    (r c : Fin (V.vMatrixSize n)) :
    ratConst (vActualFormalRowScale n r) *
      vActualFormalSourceMatrix n r c ∈ psi.range := by
  let dN := denominatorLcm (V.vN n)
  let dU := denominatorLcm (V.vU n)
  have hdN : ∀ s, 1 ≤ s → s ≤ V.vN n → s ∣ dN := by
    intro s hs hsN
    exact dvd_denominatorLcm hs hsN
  have hdU : ∀ s, 1 ≤ s → s ≤ V.vU n → s ∣ dU := by
    intro s hs hsU
    exact dvd_denominatorLcm hs hsU
  have hjN : V.vJIndex n c ≤ V.vN n := by
    have hc : c.val < 9 * n := by
      simpa [V.vMatrixSize_eq] using c.isLt
    change n + c.val ≤ 10 * n - 1
    omega
  by_cases htop : r.val < V.vM n
  · have hiN : V.vIIndexNat n r.val ≤ V.vN n := by
      have htop' : r.val < 4 * n := by
        simpa [V.vM] using htop
      change 2 * n + r.val ≤ 10 * n - 1
      omega
    have hscale : vActualFormalRowScale n r = (dN : ℚ) := by
      simp [vActualFormalRowScale, htop, dN]
    rw [hscale]
    simp only [vActualFormalSourceMatrix, if_pos htop]
    change ratConst (dN : ℚ) *
      vFormalCEntry (V.vIIndexNat n r.val) (V.vJIndex n c) ∈ psi.range
    rw [vFormalCEntry_eq_formalC]
    exact scaled_formalC_mem hdN hiN hjN (by omega)
  · by_cases hmid : r.val < 2 * V.vM n
    · let i := 2 * n + (r.val - V.vM n)
      have hiN : i ≤ V.vN n := by
        have hr : r.val < 9 * n := by
          simpa [V.vMatrixSize_eq] using r.isLt
        have hlow : 4 * n ≤ r.val := by
          simpa [V.vM] using Nat.le_of_not_gt htop
        have htmp : r.val < 2 * (4 * n) := by
          simpa [V.vM] using hmid
        have hhigh : r.val < 8 * n := by
          calc
            r.val < 2 * (4 * n) := htmp
            _ = 8 * n := by ring
        dsimp [i, V.vN, V.vM]
        omega
      have hscale : vActualFormalRowScale n r = (dN : ℚ) ^ 2 := by
        simp [vActualFormalRowScale, htop, hmid, dN]
      rw [hscale]
      simp only [vActualFormalSourceMatrix, if_neg htop, if_pos hmid]
      change ratConst ((dN : ℚ) ^ 2) *
        (vFormalBEntry i (V.vJIndex n c) -
          vFormalT * vFormalAEntry i (V.vJIndex n c)) ∈ psi.range
      rw [vFormalBEntry_eq_formalB, vFormalAEntry_eq_formalA,
        vFormalT]
      exact scaled_lower_mem hdN hiN hjN (by omega)
    · let j := V.vJIndex n c
      let ell := 1 + (r.val - 2 * V.vM n)
      have hell_lo : 1 ≤ ell := by dsimp [ell]; omega
      have hell_hi : ell ≤ n := by
        have hr : r.val < 9 * n := by
          simpa [V.vMatrixSize_eq] using r.isLt
        have htmp : 2 * (4 * n) ≤ r.val := by
          simpa [V.vM] using Nat.le_of_not_gt hmid
        have hlow : 8 * n ≤ r.val := by
          calc
            8 * n = 2 * (4 * n) := by ring
            _ ≤ r.val := htmp
        dsimp [ell, V.vM]
        omega
      have hjell : j + ell ≤ V.vU n := by
        have hc : c.val < 9 * n := by
          simpa [V.vMatrixSize_eq] using c.isLt
        change n + c.val + ell ≤ 11 * n - 1
        omega
      have hjell_lo : 1 ≤ j + ell := by
        dsimp [j, V.vJIndex]
        omega
      have hscale : vActualFormalRowScale n r = (dU : ℚ) := by
        simp [vActualFormalRowScale, htop, hmid, dU]
      rw [hscale]
      simp only [vActualFormalSourceMatrix, if_neg htop, if_neg hmid]
      change ratConst (dU : ℚ) * vFormalVEntry j ell ∈ psi.range
      rw [vFormalVEntry, ← ratConst_mul]
      exact isInt_mem (isInt_div_of_le hdU hjell_lo hjell)
/-- Exact denominator product contributed by the three V row blocks. -/
theorem vActualFormalRowScale_prod (n : ℕ) :
    (∏ r : Fin (V.vMatrixSize n), vActualFormalRowScale n r) =
      (denominatorLcm (V.vN n) : ℚ) ^ (12 * n) *
        (denominatorLcm (V.vU n) : ℚ) ^ n := by
  classical
  let M := V.vM n
  let dN := denominatorLcm (V.vN n)
  let dU := denominatorLcm (V.vU n)
  let f : ℕ → ℚ := fun k =>
    if k < M then (dN : ℚ)
    else if k < 2 * M then (dN : ℚ) ^ 2 else (dU : ℚ)
  change (∏ r : Fin (V.vMatrixSize n), f r.val) = _
  rw [Fin.prod_univ_eq_prod_range f (V.vMatrixSize n)]
  rw [show V.vMatrixSize n = 2 * M + n by
    simp [M, V.vMatrixSize, V.vS]]
  rw [show 2 * M + n = M + (M + n) by ring,
    Finset.prod_range_add, Finset.prod_range_add]
  have h1 : (∏ k ∈ Finset.range M, f k) = (dN : ℚ) ^ M := by
    calc
      (∏ k ∈ Finset.range M, f k) =
          ∏ k ∈ Finset.range M, (dN : ℚ) := by
        apply Finset.prod_congr rfl
        intro k hk
        have hk' := Finset.mem_range.mp hk
        simp [f, hk']
      _ = (dN : ℚ) ^ M := by simp
  have h2 : (∏ k ∈ Finset.range M, f (M + k)) =
      ((dN : ℚ) ^ 2) ^ M := by
    calc
      (∏ k ∈ Finset.range M, f (M + k)) =
          ∏ k ∈ Finset.range M, ((dN : ℚ) ^ 2) := by
        apply Finset.prod_congr rfl
        intro k hk
        have hk' := Finset.mem_range.mp hk
        have hnot : ¬ M + k < M := by omega
        have hlt : M + k < 2 * M := by omega
        simp [f, hnot, hlt]
      _ = ((dN : ℚ) ^ 2) ^ M := by simp
  have h3 : (∏ k ∈ Finset.range n, f (M + (M + k))) =
      (dU : ℚ) ^ n := by
    calc
      (∏ k ∈ Finset.range n, f (M + (M + k))) =
          ∏ k ∈ Finset.range n, (dU : ℚ) := by
        apply Finset.prod_congr rfl
        intro k hk
        have hnot₁ : ¬ M + (M + k) < M := by omega
        have hnot₂ : ¬ M + (M + k) < 2 * M := by omega
        simp [f, hnot₁, hnot₂]
      _ = (dU : ℚ) ^ n := by simp
  rw [h1, h2, h3]
  have hpow : (dN : ℚ) ^ M * ((dN : ℚ) ^ 2) ^ M =
      (dN : ℚ) ^ (12 * n) := by
    calc
      (dN : ℚ) ^ M * ((dN : ℚ) ^ 2) ^ M =
          (dN : ℚ) ^ M * (dN : ℚ) ^ (2 * M) := by
            rw [pow_mul]
      _ = (dN : ℚ) ^ (M + 2 * M) := by
            rw [← pow_add]
      _ = (dN : ℚ) ^ (12 * n) := by
            congr 1
            dsimp [M, V.vM]
            ring
  calc
    (dN : ℚ) ^ M * (((dN : ℚ) ^ 2) ^ M * (dU : ℚ) ^ n) =
        ((dN : ℚ) ^ M * ((dN : ℚ) ^ 2) ^ M) * (dU : ℚ) ^ n := by ring
    _ = (dN : ℚ) ^ (12 * n) * (dU : ℚ) ^ n := by rw [hpow]
    _ = (denominatorLcm (V.vN n) : ℚ) ^ (12 * n) *
        (denominatorLcm (V.vU n) : ℚ) ^ n := by rfl

/-- The scaled V determinant has an integer bivariate polynomial witness.
This packages the preceding rowwise proof by the generic determinant
row-scaling identity; no feature-divisibility is asserted here. -/
theorem vActualFormalDeterminant_integerized (n : ℕ) (hn : 0 < n) :
    ∃ Z : Matrix (Fin (V.vMatrixSize n)) (Fin (V.vMatrixSize n))
        (Polynomial (Polynomial ℤ)),
      psi (Matrix.det Z) =
        (∏ r : Fin (V.vMatrixSize n), ratConst (vActualFormalRowScale n r)) *
          Matrix.det (vActualFormalSourceMatrix n) := by
  classical
  let Z : Matrix (Fin (V.vMatrixSize n)) (Fin (V.vMatrixSize n))
      (Polynomial (Polynomial ℤ)) :=
    fun r c => Classical.choose
      (Set.mem_range.mp (vActualFormalScaledEntry_mem n hn r c))
  have hZ (r c : Fin (V.vMatrixSize n)) :
      psi (Z r c) =
        ratConst (vActualFormalRowScale n r) *
          vActualFormalSourceMatrix n r c :=
    Classical.choose_spec
      (Set.mem_range.mp (vActualFormalScaledEntry_mem n hn r c))
  refine ⟨Z, ?_⟩
  calc
    psi (Matrix.det Z) =
        Matrix.det (fun r c => psi (Z r c)) :=
      RingHom.map_det psi Z
    _ = Matrix.det (fun r c =>
        ratConst (vActualFormalRowScale n r) *
          vActualFormalSourceMatrix n r c) := by
      congr 1
      funext r c
      exact hZ r c
    _ = (∏ r : Fin (V.vMatrixSize n),
          ratConst (vActualFormalRowScale n r)) *
          Matrix.det (vActualFormalSourceMatrix n) :=
      det_row_scale (vActualFormalSourceMatrix n)
        (fun r => ratConst (vActualFormalRowScale n r))

/-- A coefficientwise lower bound implies the corresponding Gauss valuation
bound when the exponent is nonnegative.  The nonnegativity condition is needed
for the empty-support (zero polynomial) case, where the valuation is defined
to be zero. -/
theorem actualGaussValuation_ge_of_coeff_ge
    (p : ℕ) (P : Polynomial ℚ) (E : ℤ) (hE : 0 ≤ E)
    (hcoeff : ∀ i : ℕ, P.coeff i ≠ 0 →
      -E ≤ padicValRat p (P.coeff i)) :
    V.actualGaussValuation p P ≥ -E := by
  unfold V.actualGaussValuation
  split_ifs with hsupport
  · apply Finset.le_inf'
    intro i hi
    exact hcoeff i (Polynomial.mem_support_iff.mp hi)
  · omega

/-- Specialize the S08 integer bivariate row witness to any integer base.
This is the unrefined row denominator from v13 `v-arithmetic.tex:128-198`;
the exceptional-prime feature credit and the sharp prime-sum rate are separate.
-/
theorem vActualPolynomial_integerized (n : ℕ) (hn : 0 < n) (a : ℤ) :
    ∃ P : Polynomial ℤ,
      P.map (Int.castRingHom ℚ) =
        Polynomial.C ((denominatorLcm (V.vN n) : ℚ) ^ (12 * n) *
          (denominatorLcm (V.vU n) : ℚ) ^ n) * V.vPolynomial n a := by
  obtain ⟨Z, hZ⟩ := vActualFormalDeterminant_integerized n hn
  refine ⟨(Matrix.det Z).eval (Polynomial.C a), ?_⟩
  have heval := mapRingHom_eval (Int.castRingHom ℚ) (Matrix.det Z)
    (Polynomial.C a)
  rw [Polynomial.coe_mapRingHom] at heval
  rw [heval]
  rw [Polynomial.map_C]
  change Polynomial.eval (Polynomial.C (a : ℚ)) (psi (Matrix.det Z)) = _
  change outerEval (a : ℚ) (psi (Matrix.det Z)) = _
  rw [hZ, map_mul, outerEval_vActualFormalDeterminant]
  congr 1
  change outerEval (a : ℚ) (∏ r, rc (vActualFormalRowScale n r)) = _
  rw [← map_prod]
  rw [vActualFormalRowScale_prod]
  simp [outerEval_ratConst]

/-- Coefficient witness for the literal signed determinant, obtained from
the same three row blocks as the formal S08 proof. Source: v13
`v-arithmetic.tex:128-198`; no coefficient or valuation hypothesis is added.
-/
theorem vActualPolynomial_coeff_integerized
    (n : ℕ) (hn : 0 < n) (a : ℤ) (i : ℕ) :
    ∃ z : ℤ,
      ((denominatorLcm (V.vN n) : ℚ) ^ (12 * n) *
        (denominatorLcm (V.vU n) : ℚ) ^ n) * (V.vPolynomial n a).coeff i = z := by
  obtain ⟨P, hP⟩ := vActualPolynomial_integerized n hn a
  refine ⟨P.coeff i, ?_⟩
  have hi := congrArg (fun Q : Polynomial ℚ => Q.coeff i) hP
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_map] at hi
  exact hi.symm

/-- Coarse row-denominator valuation bound for every actual V coefficient.
This is the row-clearing input of v13 `v-arithmetic.tex:128-198`, before
the residue and exceptional-prime credits sharpen its exponent. -/
theorem vActualPolynomial_coeff_valuation_lower
    (n : ℕ) (hn : 0 < n) (a : ℤ) (i p : ℕ) (hp : p.Prime) :
    (V.vPolynomial n a).coeff i = 0 ∨
      -(((12 * n * Nat.log p (V.vN n) + n * Nat.log p (V.vU n) : ℕ)) : ℤ) ≤
        padicValRat p ((V.vPolynomial n a).coeff i) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hd (U : ℕ) : denominatorLcm U ≠ 0 := by
    unfold denominatorLcm
    rw [Finset.lcm_ne_zero_iff]
    intro s hs
    exact Nat.ne_of_gt ((Finset.mem_Icc.mp hs).1)
  have hdQ (U : ℕ) : (denominatorLcm U : ℚ) ≠ 0 := by
    exact_mod_cast hd U
  have hval (U : ℕ) : padicValRat p (denominatorLcm U : ℚ) = Nat.log p U := by
    rw [padicValRat.of_nat]
    have h := Nat.factorization_lcmUpto U hp
    rw [Nat.factorization_def _ hp] at h
    exact_mod_cast h
  by_cases hc : (V.vPolynomial n a).coeff i = 0
  · exact Or.inl hc
  right
  obtain ⟨z, hz⟩ := vActualPolynomial_coeff_integerized n hn a i
  have hv := congrArg (padicValRat p) hz
  rw [padicValRat.mul (mul_ne_zero (pow_ne_zero _ (hdQ _))
    (pow_ne_zero _ (hdQ _))) hc,
    padicValRat.mul (pow_ne_zero _ (hdQ _)) (pow_ne_zero _ (hdQ _)),
    padicValRat.pow, padicValRat.pow, hval, hval, padicValRat.of_int] at hv
  push_cast at hv ⊢
  omega

/-- The row-integrality estimate transported to the actual determinant's
Gauss valuation, uniformly in q. It supplies a coarse row bound, rather than
the sharp exponent required by the final v13 prime-sum rate. -/
theorem actualVDeterminant_gauss_valuation_lower
    (q n p : ℕ) (hn : 0 < n) (hp : p.Prime) :
    V.actualGaussValuation p (V.actualVDeterminant q (4 * n)) ≥
      -(((12 * n * Nat.log p (V.vN n) + n * Nat.log p (V.vU n) : ℕ)) : ℤ) := by
  rw [V.actualVDeterminant_four_mul]
  apply actualGaussValuation_ge_of_coeff_ge _ _ _ (by positivity)
  intro i hi
  exact (vActualPolynomial_coeff_valuation_lower n hn (-(q : ℤ)) i p hp).resolve_left hi

end
end Li2Lean.B3

#print axioms Li2Lean.B3.actualGaussValuation_ge_of_coeff_ge
#print axioms Li2Lean.B3.vActualPolynomial_integerized
#print axioms Li2Lean.B3.vActualPolynomial_coeff_integerized
#print axioms Li2Lean.B3.vActualPolynomial_coeff_valuation_lower
#print axioms Li2Lean.B3.actualVDeterminant_gauss_valuation_lower
