/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B4.ResidueTailAlgebra

open Finset Polynomial

namespace Li2Lean.B4.ResidueTailBridge

noncomputable section

open Li2Lean.B4.Residues

/-!  This file is the finite-product bridge for the explicit residue formula
    in `hp-tail.tex:12-45`.  The generic partial-fraction existence theorem
    in `Residues` is deliberately not used as the explicit certificate: the
    factorial and harmonic coefficients remain an explicit input until that
    finite identity is proved. -/

/-- The product of the pole factors with the pole at `j` removed.
    v13 `hp-tail.tex:12-18`. -/
def hpOffPoly (n j : ℕ) : ℚ[X] :=
  ∏ i ∈ (Finset.range (n + 1)).erase j, hpPole i

/-- The squared pole denominator in the integer evaluation of `Phi_n`.
    v13 `hp-tail.tex:12-18`. -/
def hpDen (n k : ℕ) : ℚ :=
  ∏ j ∈ Finset.range (n + 1),
    (((k : ℚ) - (j : ℚ)) ^ 2)

/-- The explicit finite-product certificate for the displayed coefficients
    `u_{n,j},v_{n,j}`.  This is the exact algebraic content of the residue
    formula in v13 `hp-tail.tex:12-23`; it is kept separate from the generic
    existence theorem in `Residues`. -/
structure ExplicitResidueCertificate (n : ℕ) : Prop where
  polynomial_identity :
    hpNumerator n =
      ∑ j ∈ Finset.range (n + 1),
        (Polynomial.C (hpResidueU n j) +
            Polynomial.C (hpResidueV n j) * hpPole j) *
          (hpOffPoly n j) ^ 2

/-! The zero row is a fully checkable normalization regression for the
    factorial and harmonic conventions. -/

/-- The explicit residue certificate at `n=0`, v13 `hp-tail.tex:12-23`. -/
theorem explicitResidueCertificate_zero : ExplicitResidueCertificate 0 := by
  refine ⟨?_⟩
  norm_num [hpNumerator, hpResidueU, hpResidueV, hpHarmonic, hpOffPoly,
    hpPole]
  ring

/-! ## Product and coefficient normalizations -/

/-- The removed-pole product is nonzero at every integer node `k>n`.
    v13 `hp-tail.tex:12-18`. -/
theorem hpOffPoly_eval_ne_zero (n j k : ℕ)
    (hj : j ∈ Finset.range (n + 1)) (hkn : n < k) :
    (hpOffPoly n j).eval (k : ℚ) ≠ 0 := by
  unfold hpOffPoly hpPole
  simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C]
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  have hi' : i ∈ Finset.range (n + 1) :=
    Finset.mem_of_mem_erase hi
  have hik : i < k := by
    simp only [Finset.mem_range] at hi' ⊢
    omega
  exact sub_ne_zero.mpr (by exact_mod_cast (Nat.ne_of_gt hik))

/-- The squared denominator is nonzero away from the integer pole set.
    v13 `hp-tail.tex:12-18`. -/
theorem hpDen_ne_zero (n k : ℕ) (hkn : n < k) : hpDen n k ≠ 0 := by
  unfold hpDen
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  have hjk : j < k := by
    simp only [Finset.mem_range] at hj ⊢
    omega
  have hsub : (k : ℚ) - (j : ℚ) ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast (Nat.ne_of_gt hjk))
  exact pow_ne_zero 2 hsub

/-- The full denominator factors into the pole at `j` and the removed-pole
    product.  This is the finite-product normalization used in the residue
    evaluation, v13 `hp-tail.tex:12-18`. -/
theorem hpDen_factor (n j k : ℕ)
    (hj : j ∈ Finset.range (n + 1)) :
    hpDen n k =
      (((k : ℚ) - (j : ℚ)) ^ 2) *
        ((hpOffPoly n j).eval (k : ℚ)) ^ 2 := by
  unfold hpDen hpOffPoly hpPole
  simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C]
  rw [← Finset.prod_pow]
  rw [← Finset.mul_prod_erase (Finset.range (n + 1))
    (fun i => ((k : ℚ) - (i : ℚ)) ^ 2) hj]

/-- For `k>n`, the truncated coefficient sum has no terms at or above its
    pole cutoff, and natural subtraction is the corresponding rational pole
    difference.  v13 `hp-tail.tex:34-41`. -/
theorem hpResidueConvolution_eq_residueSum
    (n k : ℕ) (hkn : n < k) :
    hpResidueConvolution n k =
      ∑ j ∈ Finset.range (n + 1),
        (hpResidueV n j / (((k : ℚ) - (j : ℚ)) ^ 1) +
          hpResidueU n j / (((k : ℚ) - (j : ℚ)) ^ 2)) := by
  unfold hpResidueConvolution
  apply Finset.sum_congr rfl
  intro j hj
  have hjk : j < k := by
    simp only [Finset.mem_range] at hj
    omega
  rw [if_pos hjk]
  simp [pow_one, div_eq_mul_inv]

/-! ## Evaluation of the explicit certificate -/

/-- Evaluation of an explicit residue certificate gives the rational
    partial-fraction sum at `k>n`, v13 `hp-tail.tex:12-23`. -/
theorem hpPhiValue_eq_residueSum_of_certificate
    (n k : ℕ) (hkn : n < k)
    (hcert : ExplicitResidueCertificate n) :
    hpPhiValue n k =
      ∑ j ∈ Finset.range (n + 1),
        (hpResidueU n j / (((k : ℚ) - (j : ℚ)) ^ 2) +
          hpResidueV n j / ((k : ℚ) - (j : ℚ))) := by
  unfold hpPhiValue
  have hden : hpDen n k ≠ 0 := hpDen_ne_zero n k hkn
  have hev := congrArg (fun p : ℚ[X] => p.eval (k : ℚ))
    hcert.polynomial_identity
  have hev' :
      (hpNumerator n).eval (k : ℚ) =
        ∑ j ∈ Finset.range (n + 1),
          (hpResidueU n j +
              hpResidueV n j * ((k : ℚ) - (j : ℚ))) *
            ((hpOffPoly n j).eval (k : ℚ)) ^ 2 := by
    simpa [hpPole, hpOffPoly, Polynomial.eval_finsetSum,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_prod] using hev
  apply (div_eq_iff hden).2
  rw [hev', Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  have hjk : j < k := by
    simp only [Finset.mem_range] at hj ⊢
    omega
  have hsub : (k : ℚ) - (j : ℚ) ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast (Nat.ne_of_gt hjk))
  have hoff : (hpOffPoly n j).eval (k : ℚ) ≠ 0 :=
    hpOffPoly_eval_ne_zero n j k hj hkn
  rw [hpDen_factor n j k hj]
  field_simp [hsub, hoff]

/-- The explicit certificate supplies the partial-fraction comparison at
    every integer `k>n`, before restricting to the high tail.  This is the
    coefficient identity used for both the middle zero range and the tail,
    v13 `hp-tail.tex:34-41`. -/
theorem hpartial_for_residueTailAlgebra
    (n : ℕ) (hcert : ExplicitResidueCertificate n) :
    ∀ k, n < k →
      hpResidueConvolution n k = hpPhiValue n k := by
  intro k hkn
  rw [hpResidueConvolution_eq_residueSum n k hkn]
  simpa [div_eq_mul_inv, add_comm, add_left_comm, add_assoc] using
    (hpPhiValue_eq_residueSum_of_certificate n k hkn hcert).symm

/-- The exact hpartial input expected by `hpTailCoeff_of_partial_fraction`.
    For `k≥3n+2`, the explicit residue sum equals `Phi_n(k)`, v13
    `hp-tail.tex:34-41`. -/
theorem hpartial_bridge
    (n : ℕ) (hcert : ExplicitResidueCertificate n) :
    ∀ k, 3 * n + 2 ≤ k →
      hpResidueConvolution n k = hpPhiValue n k := by
  intro k hk
  have hkn : n < k := by omega
  exact hpartial_for_residueTailAlgebra n hcert k hkn

/-- The high-tail coefficient identity after feeding the explicit bridge into
    the existing `ResidueTailAlgebra` theorem. -/
theorem hpTailCoeff_of_certificate
    (n : ℕ) (hcert : ExplicitResidueCertificate n) :
    ∀ k, 3 * n + 2 ≤ k →
      hpThreeFormCoeff n k = hpPhiValue n k := by
  intro k hk
  exact (hpTailCoeff_of_partial_fraction n k (by
    intro hk'
    exact hpartial_bridge n hcert k hk')) hk

end

end Li2Lean.B4.ResidueTailBridge
