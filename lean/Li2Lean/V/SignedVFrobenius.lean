/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/

import Mathlib
import Li2Lean.Kit.ReducedRational
import Li2Lean.V.VFamily

/-!
# Signed-V Frobenius producer interface

This is the q-dependent version of the frozen 1/2 `P0FrobeniusTowerCertificate`.
Every value in the certificate is the actual v13 determinant
`V.vPolynomial M (-q)`; no arbitrary polynomial, valuation, or determinant
field is accepted.  The fields are exactly the seed argument and Frobenius
congruence used in `paper-v13/chapters/nonvanishing.tex:200-275`.  The
elementary residue propagation theorem below is reused from the 1/2
`ContourKit.ReducedRational` pattern and does not change the construction.
-/

namespace Li2Lean.V

noncomputable section

open scoped BigOperators

structure SignedVFrobeniusTowerCertificate (q M p : ℕ) where
  q_ge_two : 2 ≤ q
  q_le_seven : q ≤ 7
  M_pos : 0 < M
  M_multiple_four : 4 ∣ M
  p_prime : Nat.Prime p
  /-- v13 `eq:nv-pencil`: the auxiliary prime is beyond the pole cutoff. -/
  p_gt_twoM_plus_half : 2 * M + M / 2 < p
  seed : ContourKit.ReducedRational p
  seed_value : seed.value = (vPolynomial M (-(q : ℤ))).eval 0
  seed_residue_nonzero : seed.residue ≠ 0
  /-- v13 `nonvanishing.tex:200-214`, continuity at the scaled rational point. -/
  seed_argument : ∀ r : ℚ, ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
    ∃ s : ContourKit.ReducedRational p,
      s.value = (vPolynomial M (-(q : ℤ))).eval
        (((p ^ k : ℕ) : ℚ) ^ 2 * r) ∧
      s.residue = seed.residue
  /-- v13 `nonvanishing.tex:215-275`, the Frobenius pencil congruence. -/
  frobenius : ∀ r : ℚ, ∃ k₁ : ℕ, ∀ k : ℕ, k₁ ≤ k →
    ∃ lhs rhs : ContourKit.ReducedRational p,
      lhs.value = ((p ^ k : ℕ) : ℚ) ^ (3 * M * p ^ k) *
        (vPolynomial (M * p ^ k) (-(q : ℤ))).eval r ∧
      rhs.value =
        ((vPolynomial M (-(q : ℤ))).eval
          (((p ^ k : ℕ) : ℚ) ^ 2 * r)) ^ (p ^ k) ∧
      lhs.residue = rhs.residue ∧
      (∀ s : ContourKit.ReducedRational p,
        s.value = (vPolynomial M (-(q : ℤ))).eval
          (((p ^ k : ℕ) : ℚ) ^ 2 * r) →
          rhs.residue = s.residue ^ (p ^ k))

abbrev Q2FrobeniusTowerCertificate (M p : ℕ) :=
  SignedVFrobeniusTowerCertificate 2 M p

abbrev Q3FrobeniusTowerCertificate (M p : ℕ) :=
  SignedVFrobeniusTowerCertificate 3 M p

theorem signedV_source_nonzero
    {q M p : ℕ} (hcert : SignedVFrobeniusTowerCertificate q M p) :
    ∀ r : ℚ, ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      (vPolynomial (M * p ^ k) (-(q : ℤ))).eval r ≠ 0 := by
  letI : Fact (Nat.Prime p) := ⟨hcert.p_prime⟩
  intro r
  obtain ⟨k₀, hk₀⟩ := hcert.seed_argument r
  obtain ⟨k₁, hk₁⟩ := hcert.frobenius r
  refine ⟨max k₀ k₁, ?_⟩
  intro k hkk
  have hk_seed : k₀ ≤ k := le_trans (Nat.le_max_left _ _) hkk
  have hk_frob : k₁ ≤ k := le_trans (Nat.le_max_right _ _) hkk
  obtain ⟨s, hsval, hsres⟩ := hk₀ k hk_seed
  obtain ⟨lhs, rhs, hlhsval, _hrhsval, hlhsres, hrhsres⟩ := hk₁ k hk_frob
  have hrhs : rhs.residue ≠ 0 := by
    rw [hrhsres s hsval, hsres]
    exact pow_ne_zero _ hcert.seed_residue_nonzero
  have hlhs : lhs.residue ≠ 0 := by rwa [hlhsres]
  have hlhsval_ne : lhs.value ≠ 0 :=
    ContourKit.ReducedRational.value_ne_zero lhs hlhs
  intro hzero
  apply hlhsval_ne
  rw [hlhsval, hzero]
  simp

theorem q2_source_nonzero_of_certificate
    {M p : ℕ} (hcert : Q2FrobeniusTowerCertificate M p) :
    ∀ r : ℚ, ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      (vPolynomial (M * p ^ k) (-2 : ℤ)).eval r ≠ 0 := by
  simpa using (signedV_source_nonzero hcert)

theorem q3_source_nonzero_of_certificate
    {M p : ℕ} (hcert : Q3FrobeniusTowerCertificate M p) :
    ∀ r : ℚ, ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      (vPolynomial (M * p ^ k) (-3 : ℤ)).eval r ≠ 0 := by
  simpa using (signedV_source_nonzero hcert)

/- The positive `a = 2` family remains the regression reference; this module
only generalizes the nonvanishing transport around the v13 V determinant. -/
theorem positive_a2_family_regression (n : ℕ) :
    vPolynomial n (2 : ℤ) = Matrix.det (vSourceMatrix n (2 : ℤ)) :=
  vPolynomial_two n

end
end Li2Lean.V

