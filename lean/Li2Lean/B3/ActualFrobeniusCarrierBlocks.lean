/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B3.ActualFrobeniusCarrierGeneric
import Li2Lean.V.SignedVFrobeniusResidue

/-!
# Actual signed-V Frobenius carrier blocks

This module records the source-level pieces used by the Frobenius pencil in
`nonvanishing.tex:216-246`.  The bottom block of `V.vSourceMatrix` is a
Cauchy block, so its scaled entry has one surviving residue in each block of
length `p^k`.  The coefficient carrier below keeps the two genuinely global
obligations explicit: a sharp source-coefficient valuation bound and the
coefficientwise Frobenius congruence for the actual scaled determinant.

The carrier is intentionally an input boundary.  The row and congruence
fields mention `V.vPolynomial` and `V.vFrobeniusScaledPolynomial` directly;
finite seed data or a coarse denominator estimate cannot inhabit them.
-/

namespace Li2Lean.B3

noncomputable section

open Li2Lean.V.SignedVFrobenius

/-! ## The literal V block -/

/-- The `ell` index of a row in the bottom Cauchy block. -/
def vBottomRowEll (n : ℕ) (r : Fin (V.vMatrixSize n)) : ℕ :=
  1 + (r.val - 2 * V.vM n)

theorem vBottomRowEll_bounds {n : ℕ} (r : Fin (V.vMatrixSize n))
    (hr : 2 * V.vM n ≤ r.val) :
    1 ≤ vBottomRowEll n r ∧ vBottomRowEll n r ≤ V.vS n := by
  have hlt := r.isLt
  simp [vBottomRowEll, V.vMatrixSize, V.vM, V.vS] at hlt ⊢
  omega

/-- A bottom-block source entry is exactly the Cauchy entry from
`v-arithmetic.tex:31`. -/
theorem vSourceMatrix_bottom_entry
    (n : ℕ) (a : ℤ) (r c : Fin (V.vMatrixSize n))
    (hr : 2 * V.vM n ≤ r.val) :
    V.vSourceMatrix n a r c =
      Polynomial.C
        (V.vVEntry (V.vJIndex n c) (vBottomRowEll n r)) := by
  have htop : ¬ r.val < V.vM n := by omega
  have hmid : ¬ r.val < 2 * V.vM n := Nat.not_lt_of_ge hr
  simp [V.vSourceMatrix, vBottomRowEll, htop, hmid]

theorem vSourceMatrix_bottom_entry_coeff_zero
    (n : ℕ) (a : ℤ) (r c : Fin (V.vMatrixSize n))
    (hr : 2 * V.vM n ≤ r.val) :
    (V.vSourceMatrix n a r c).coeff 0 =
      V.vVEntry (V.vJIndex n c) (vBottomRowEll n r) := by
  rw [vSourceMatrix_bottom_entry n a r c hr]
  simp

/-- Every column of the `n`-level V matrix has a quotient/remainder
decomposition with respect to the block length `n`. -/
theorem vJIndex_block_decompose {n : ℕ} (hn : 0 < n)
    (c : Fin (V.vMatrixSize n)) :
    ∃ j0 u, j0 < 10 ∧ u < n ∧
      V.vJIndex n c = j0 * n + u := by
  have hj := V.vJIndex_mem n c
  refine ⟨V.vJIndex n c / n, V.vJIndex n c % n, ?_,
    Nat.mod_lt _ hn, ?_⟩
  · apply Nat.div_lt_of_lt_mul
    simpa [Nat.mul_comm] using hj.2
  · calc
      V.vJIndex n c = n * (V.vJIndex n c / n) +
          V.vJIndex n c % n :=
        (Nat.div_add_mod (V.vJIndex n c) n).symm
      _ = (V.vJIndex n c / n) * n +
          V.vJIndex n c % n := by ring

/-- The scaled residue of a literal V-block entry.  The arbitrary denominator
proof is deliberate: `residueOf` is proof-indexed, while proof irrelevance
identifies it with the canonical proof used by the generic row theorem. -/
theorem vVBlock_scaled_entry_residue
    {p k j0 u ell : ℕ} [Fact (Nat.Prime p)]
    (hp11 : 11 ≤ p)
    (hj0 : j0 < 10)
    (hu : u < p ^ k) (hell : 0 < ell) (hellq : ell ≤ p ^ k)
    (hden : Nat.Coprime
      ((((p ^ k : ℕ) : Rat) /
        ((j0 * p ^ k + u + ell : ℕ) : Rat)).den) p) :
    residueOf (p := p)
      ((((p ^ k : ℕ) : Rat) *
        V.vVEntry (j0 * p ^ k + u) ell)) hden =
      if u + ell = p ^ k then
        ((j0 + 1 : ℕ) : ZMod p)⁻¹
      else 0 := by
  have h := signedVScaledVEntry_residue
    (p := p) k j0 u ell hp11 hj0 hu hell hellq
  simpa [signedVScaledVEntry_eq, V.vVEntry, div_eq_mul_inv] using h

/-! ## Coefficient-level Frobenius carrier -/

/-- The residue target predicted by the coefficientwise Frobenius congruence.
The quotient index is only used in the divisible block, where the displayed
degree bound proves it is at most four. -/
def vScaledFrobeniusTargetResidue
    (q p : ℕ) [Fact (Nat.Prime p)] (k i : ℕ)
    (hi : i ≤ 4 * p ^ k)
    (hseed : ∀ j : ℕ, j ≤ 4 →
      Nat.Coprime
        ((V.vPolynomial 1 (-(q : ℤ))).coeff j).den p) : ZMod p :=
  if hq : p ^ k ∣ i then
    let j := i / p ^ k
    have hj : j ≤ 4 := by
      dsimp [j]
      exact Nat.div_le_of_le_mul (Nat.mul_comm 4 (p ^ k) ▸ hi)
    (residueOf (p := p)
        ((V.vPolynomial 1 (-(q : ℤ))).coeff j)
        (hseed j hj)) ^ (p ^ k)
  else 0

/-- Construction-bound coefficient data for the actual scaled V pencil.

`source_row_bound` is the sharp valuation statement needed to transport
integrality through `scaled_coeff_eq`.  `coefficientwise_frobenius` is the
remaining all-`k` residue congruence; it is stated over the actual scaled
polynomial and the actual seed polynomial, rather than an unconstrained
surrogate. -/
structure VActualScaledCoefficientCarrier (q p : ℕ)
    [Fact (Nat.Prime p)] : Prop where
  prime : Nat.Prime p
  seed_coeff_den_coprime : ∀ j : ℕ, j ≤ 4 →
    Nat.Coprime
      ((V.vPolynomial 1 (-(q : ℤ))).coeff j).den p
  source_row_bound :
    ∀ k : ℕ, 0 < k → ∀ i : ℕ, i ≤ 4 * p ^ k →
      -(((13 * p ^ k - 2 * i : ℕ) : ℤ) * (k : ℤ)) ≤
        padicValRat p
          ((V.vPolynomial (p ^ k) (-(q : ℤ))).coeff i)
  coefficientwise_frobenius :
    ∀ k : ℕ, 0 < k → ∀ i : ℕ, ∀ hi : i ≤ 4 * p ^ k,
      ∀ hscaled : Nat.Coprime
        ((V.vFrobeniusScaledPolynomial q p k).coeff i).den p,
        residueOf (p := p)
            ((V.vFrobeniusScaledPolynomial q p k).coeff i) hscaled =
          vScaledFrobeniusTargetResidue q p k i
            hi seed_coeff_den_coprime

theorem vFrobeniusScaledPolynomial_natDegree_le
    (q p k : ℕ) (hp : 0 < p) :
    (V.vFrobeniusScaledPolynomial q p k).natDegree ≤ 4 * p ^ k := by
  unfold V.vFrobeniusScaledPolynomial
  let Q : ℕ := p ^ k
  have hQ : (Q : ℚ) ≠ 0 := by
    dsimp [Q]
    positivity
  have hsub :
      (Polynomial.C (((Q : ℚ) ^ 2)⁻¹) * Polynomial.X).natDegree = 1 := by
    rw [Polynomial.natDegree_C_mul]
    · simp
    · exact inv_ne_zero (pow_ne_zero 2 hQ)
  calc
    (Polynomial.C ((Q : ℚ) ^ (13 * Q)) *
        (V.vPolynomial Q (-(q : ℤ))).comp
          (Polynomial.C (((Q : ℚ) ^ 2)⁻¹) * Polynomial.X)).natDegree ≤
      ((V.vPolynomial Q (-(q : ℤ))).comp
        (Polynomial.C (((Q : ℚ) ^ 2)⁻¹) * Polynomial.X)).natDegree :=
      Polynomial.natDegree_C_mul_le _ _
    _ ≤ (V.vPolynomial Q (-(q : ℤ))).natDegree := by
      calc
        ((V.vPolynomial Q (-(q : ℤ))).comp
            (Polynomial.C (((Q : ℚ) ^ 2)⁻¹) * Polynomial.X)).natDegree ≤
            (V.vPolynomial Q (-(q : ℤ))).natDegree *
              (Polynomial.C (((Q : ℚ) ^ 2)⁻¹) * Polynomial.X).natDegree :=
          Polynomial.natDegree_comp_le
        _ = (V.vPolynomial Q (-(q : ℤ))).natDegree := by
          rw [hsub, mul_one]
    _ ≤ 4 * Q := by
      simpa [V.vM] using V.vPolynomial_natDegree_le Q (-(q : ℤ))
    _ = 4 * p ^ k := by rfl

theorem VActualScaledCoefficientCarrier.scaled_coeff_integral
    {q p : ℕ} [Fact (Nat.Prime p)]
    (H : VActualScaledCoefficientCarrier q p) :
    ∀ k : ℕ, 0 < k → ∀ i : ℕ,
      (V.vFrobeniusScaledPolynomial q p k).coeff i ≠ 0 →
        0 ≤ padicValRat p
          ((V.vFrobeniusScaledPolynomial q p k).coeff i) := by
  intro k hk i hne
  have hdeg := vFrobeniusScaledPolynomial_natDegree_le q p k H.prime.pos
  have hi : i ≤ 4 * p ^ k := by
    by_contra hnot
    have hlt : (V.vFrobeniusScaledPolynomial q p k).natDegree < i :=
      lt_of_le_of_lt hdeg (Nat.lt_of_not_ge hnot)
    exact hne (Polynomial.coeff_eq_zero_of_natDegree_lt hlt)
  exact scaled_coeff_integral_of_row_bound H.prime hi
    (H.source_row_bound k hk i hi) hne

end
end Li2Lean.B3

#print axioms Li2Lean.B3.vSourceMatrix_bottom_entry
#print axioms Li2Lean.B3.vJIndex_block_decompose
