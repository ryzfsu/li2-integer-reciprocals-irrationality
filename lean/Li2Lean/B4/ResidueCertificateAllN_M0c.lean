/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B4.ResidueTailBridge
import Li2Lean.B4.ResidueCertificateAllN
import Li2Lean.B4.ResidueCertificateFactorialHarmonic

open Finset Polynomial

namespace Li2Lean.B4.ResidueTailBridge

noncomputable section
open Li2Lean.B4.Residues

/- E0/E1 bridge for the concrete v13 construction.
   Paper source: hp-tail.tex:20-22, with the repeated-pole shape at
   hp-tail.tex:12-18.  Closed factorial/product evaluations are explicit
   hypotheses so this file can compile while M0a/M0b are assembled. -/

theorem m0c_hpNumerator_eval_eq
    (n j : ℕ) (hj : j ≤ n)
    (hN : ((n - j).factorial : ℚ) *
        (hpNumerator n).eval (j : ℚ) =
          -((3 * n + 1 - j).factorial : ℚ))
    (hO : ((hpOffPoly n j).eval (j : ℚ)) ^ 2 =
        (j.factorial : ℚ) ^ 2 * ((n - j).factorial : ℚ) ^ 2) :
    (hpNumerator n).eval (j : ℚ) =
      hpResidueU n j * ((hpOffPoly n j).eval (j : ℚ)) ^ 2 := by
  have hF : ((n - j).factorial : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (n - j)
  have hB : (j.factorial : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero j
  apply mul_left_cancel₀ hF
  rw [hN, hO]
  unfold hpResidueU
  field_simp

theorem m0c_hpNumerator_deriv_eq
    (n j : ℕ) (hj : j ≤ n)
    (hN : (derivative (hpNumerator n)).eval (j : ℚ) =
      (hpNumerator n).eval (j : ℚ) *
        (hpHarmonic (n - j) - hpHarmonic (3 * n + 1 - j)))
    (hO : (derivative (hpOffPoly n j)).eval (j : ℚ) =
      (hpOffPoly n j).eval (j : ℚ) *
        (hpHarmonic j - hpHarmonic (n - j)))
    (hE0 : (hpNumerator n).eval (j : ℚ) =
      hpResidueU n j * ((hpOffPoly n j).eval (j : ℚ)) ^ 2) :
    (derivative (hpNumerator n)).eval (j : ℚ) =
      hpResidueV n j * ((hpOffPoly n j).eval (j : ℚ)) ^ 2 +
        hpResidueU n j *
          (2 * (hpOffPoly n j).eval (j : ℚ) *
            (derivative (hpOffPoly n j)).eval (j : ℚ)) := by
  rw [hN, hE0, hO]
  unfold hpResidueV
  ring

theorem m0c_eval_derivative_hpNumerator_all
    (n j : ℕ) (hj : j ≤ n) :
    (derivative (hpNumerator n)).eval (j : ℚ) =
      (hpNumerator n).eval (j : ℚ) *
        (hpHarmonic (n - j) - hpHarmonic (3 * n + 1 - j)) := by
  have hne : ∀ r ∈ Finset.Icc (n + 1) (3 * n + 1),
      (j : ℚ) - (r : ℚ) ≠ 0 := by
    intro r hr
    have hr' := (Finset.mem_Icc.mp hr).1
    have hjr : (j : ℚ) ≠ (r : ℚ) := by
      exact_mod_cast (show j ≠ r by omega)
    exact sub_ne_zero.mpr hjr
  have h := eval_derivative_prod_X_sub_C
    (Finset.Icc (n + 1) (3 * n + 1)) (j : ℚ) hne
  rw [sum_inv_numerator n j hj] at h
  unfold hpNumerator
  rw [h, eval_prod]
  simp only [eval_sub, eval_X, eval_C]

theorem m0c_eval_derivative_hpOffPoly_all
    (n j : ℕ) (hj : j ≤ n) :
    (derivative (hpOffPoly n j)).eval (j : ℚ) =
      (hpOffPoly n j).eval (j : ℚ) *
        (hpHarmonic j - hpHarmonic (n - j)) := by
  have hne : ∀ i ∈ (Finset.range (n + 1)).erase j,
      (j : ℚ) - (i : ℚ) ≠ 0 := by
    intro i hi
    have hij : i ≠ j := Finset.ne_of_mem_erase hi
    have hji : (j : ℚ) ≠ (i : ℚ) := by
      exact_mod_cast (Ne.symm hij)
    exact sub_ne_zero.mpr hji
  have h := eval_derivative_prod_X_sub_C
    ((Finset.range (n + 1)).erase j) (j : ℚ) hne
  rw [sum_inv_offPoly n j hj] at h
  unfold hpOffPoly hpPole
  rw [h, eval_prod]
  simp only [eval_sub, eval_X, eval_C]

theorem m0c_hpNumerator_eval_eq_all
    (n j : ℕ) (hj : j ≤ n) :
    (hpNumerator n).eval (j : ℚ) =
      hpResidueU n j * ((hpOffPoly n j).eval (j : ℚ)) ^ 2 :=
  m0c_hpNumerator_eval_eq n j hj
    (eval_hpNumerator_at_pole n j hj)
    (eval_hpOffPoly_sq_at_pole n j hj)

theorem m0c_hpNumerator_deriv_eq_all
    (n j : ℕ) (hj : j ≤ n) :
    (derivative (hpNumerator n)).eval (j : ℚ) =
      hpResidueV n j * ((hpOffPoly n j).eval (j : ℚ)) ^ 2 +
        hpResidueU n j *
          (2 * (hpOffPoly n j).eval (j : ℚ) *
            (derivative (hpOffPoly n j)).eval (j : ℚ)) :=
  m0c_hpNumerator_deriv_eq n j hj
    (m0c_eval_derivative_hpNumerator_all n j hj)
    (m0c_eval_derivative_hpOffPoly_all n j hj)
    (m0c_hpNumerator_eval_eq_all n j hj)

theorem m0c_eval_hpResidueTerm_self (n j : ℕ) :
    ((Polynomial.C (hpResidueU n j) +
        Polynomial.C (hpResidueV n j) * hpPole j) *
      (hpOffPoly n j) ^ 2).eval (j : ℚ) =
        hpResidueU n j * ((hpOffPoly n j).eval (j : ℚ)) ^ 2 := by
  simp [hpPole]

theorem m0c_eval_derivative_hpResidueTerm_self (n j : ℕ) :
    (derivative ((Polynomial.C (hpResidueU n j) +
        Polynomial.C (hpResidueV n j) * hpPole j) *
      (hpOffPoly n j) ^ 2)).eval (j : ℚ) =
        hpResidueV n j * ((hpOffPoly n j).eval (j : ℚ)) ^ 2 +
          hpResidueU n j *
            (2 * (hpOffPoly n j).eval (j : ℚ) *
              (derivative (hpOffPoly n j)).eval (j : ℚ)) := by
  unfold hpPole
  rw [derivative_mul, derivative_sq, derivative_add, derivative_C,
    derivative_C_mul, derivative_X_sub_C]
  simp only [eval_add, eval_mul, eval_C, eval_sub, eval_X, eval_one,
    eval_pow, sub_self, mul_zero, add_zero, zero_add, mul_one]

theorem m0c_sq_pole_dvd_of_eval
    {p : ℚ[X]} {a : ℕ}
    (h0 : p.eval (a : ℚ) = 0)
    (h1 : (derivative p).eval (a : ℚ) = 0) :
    hpPole a ^ 2 ∣ p := by
  obtain ⟨g, hg⟩ := Polynomial.dvd_iff_isRoot.mpr h0
  have hga : g.eval (a : ℚ) = 0 := by
    rw [hg, derivative_mul] at h1
    simpa [hpPole] using h1
  obtain ⟨h, hh⟩ := Polynomial.dvd_iff_isRoot.mpr hga
  refine ⟨h, ?_⟩
  rw [hg, hh]
  simp [hpPole]
  ring

theorem m0c_sq_pole_dvd_residual
    (n j : ℕ) (hj : j ∈ Finset.range (n + 1))
    (hE0 : (hpNumerator n).eval (j : ℚ) =
      hpResidueU n j * ((hpOffPoly n j).eval (j : ℚ)) ^ 2)
    (hE1 : (derivative (hpNumerator n)).eval (j : ℚ) =
      hpResidueV n j * ((hpOffPoly n j).eval (j : ℚ)) ^ 2 +
        hpResidueU n j *
          (2 * (hpOffPoly n j).eval (j : ℚ) *
            (derivative (hpOffPoly n j)).eval (j : ℚ)))
    (hOther : ∀ i ∈ Finset.range (n + 1), i ≠ j →
      hpPole j ^ 2 ∣
        ((Polynomial.C (hpResidueU n i) +
            Polynomial.C (hpResidueV n i) * hpPole i) *
          (hpOffPoly n i) ^ 2)) :
    hpPole j ^ 2 ∣
      hpNumerator n -
        ∑ i ∈ Finset.range (n + 1),
          ((Polynomial.C (hpResidueU n i) +
              Polynomial.C (hpResidueV n i) * hpPole i) *
            (hpOffPoly n i) ^ 2) := by
  have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [← Finset.add_sum_erase (Finset.range (n + 1))
      (fun i => (Polynomial.C (hpResidueU n i) +
        Polynomial.C (hpResidueV n i) * hpPole i) *
        (hpOffPoly n i) ^ 2) hj,
    sub_add_eq_sub_sub]
  apply dvd_sub
  · apply m0c_sq_pole_dvd_of_eval
    · rw [eval_sub, hE0, m0c_eval_hpResidueTerm_self]
      ring
    · rw [derivative_sub, eval_sub, hE1,
        m0c_eval_derivative_hpResidueTerm_self]
      ring
  · apply Finset.dvd_sum
    intro i hi
    exact hOther i (Finset.mem_of_mem_erase hi) (Finset.ne_of_mem_erase hi)

theorem m0c_sq_pole_dvd_residual_all
    (n j : ℕ) (hj : j ∈ Finset.range (n + 1)) :
    hpPole j ^ 2 ∣
      hpNumerator n -
        ∑ i ∈ Finset.range (n + 1), hpResidueTerm n i := by
  apply m0c_sq_pole_dvd_residual n j hj
    (m0c_hpNumerator_eval_eq_all n j
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)))
    (m0c_hpNumerator_deriv_eq_all n j
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)))
  intro i hi hij
  exact sq_pole_dvd_hpResidueTerm n i j hj hij

theorem m0c_certificate_of_residual_zero
    (n : ℕ)
    (hR0 : hpNumerator n -
        ∑ i ∈ Finset.range (n + 1),
          ((Polynomial.C (hpResidueU n i) +
              Polynomial.C (hpResidueV n i) * hpPole i) *
            (hpOffPoly n i) ^ 2) = 0) :
    ExplicitResidueCertificate n := by
  refine ⟨?_⟩
  exact sub_eq_zero.mp hR0

set_option maxHeartbeats 800000 in
theorem m0c_explicitResidueCertificate_all (n : ℕ) :
    ExplicitResidueCertificate n := by
  apply explicitResidueCertificate_of_dvd_degree n
  · have hcop : (↑(Finset.range (n + 1)) : Set ℕ).Pairwise
        (fun a b => IsCoprime (hpPole a ^ 2) (hpPole b ^ 2)) := by
      intro a ha b hb hab
      exact (Polynomial.isCoprime_X_sub_C_of_isUnit_sub
        (isUnit_iff_ne_zero.mpr
          (sub_ne_zero.mpr (by exact_mod_cast hab)))).pow
    exact Finset.prod_dvd_of_coprime hcop
      (fun j hj => m0c_sq_pole_dvd_residual_all n j hj)
  · have hS := Polynomial.natDegree_sum_le_of_forall_le
        (s := Finset.range (n + 1)) (f := hpResidueTerm n)
        (n := 2 * n + 1)
        (fun j hj => natDegree_hpResidueTerm_le n j hj)
    have hR := (natDegree_sub_le _ _).trans
      (max_le (natDegree_hpNumerator_le n) hS)
    rw [natDegree_hpPoleSq_prod] at *
    omega

theorem m0c_hpartial_for_residueTailAlgebra_all
    (n : ℕ) (hcert : ExplicitResidueCertificate n) :
    ∀ k, n < k → hpResidueConvolution n k = hpPhiValue n k :=
  hpartial_for_residueTailAlgebra n hcert

theorem m0c_hpartial_for_residueTailAlgebra_unconditional
    (n : ℕ) :
    ∀ k, n < k → hpResidueConvolution n k = hpPhiValue n k :=
  m0c_hpartial_for_residueTailAlgebra_all n
    (m0c_explicitResidueCertificate_all n)

theorem m0c_hpTailCoeff_all
    (n : ℕ) (hcert : ExplicitResidueCertificate n) :
    ∀ k, 3 * n + 2 ≤ k → hpThreeFormCoeff n k = hpPhiValue n k :=
  hpTailCoeff_of_certificate n hcert

theorem m0c_hpTailCoeff_unconditional (n : ℕ) :
    ∀ k, 3 * n + 2 ≤ k → hpThreeFormCoeff n k = hpPhiValue n k :=
  m0c_hpTailCoeff_all n (m0c_explicitResidueCertificate_all n)

/- Compatibility exports used by the root construction.  These aliases
   retain the concrete construction and do not introduce an abstract
   certificate field.  Paper source: hp-tail.tex:12-23 and :34-41. -/
theorem explicitResidueCertificate_all (n : ℕ) :
    ExplicitResidueCertificate n :=
  m0c_explicitResidueCertificate_all n

theorem hpartial_for_residueTailAlgebra_all (n : ℕ) :
    ∀ k, n < k → hpResidueConvolution n k = hpPhiValue n k :=
  m0c_hpartial_for_residueTailAlgebra_unconditional n

theorem hpTailCoeff_all (n : ℕ) :
    ∀ k, 3 * n + 2 ≤ k → hpThreeFormCoeff n k = hpPhiValue n k :=
  m0c_hpTailCoeff_unconditional n

end

end Li2Lean.B4.ResidueTailBridge

/- Root-level exports used by the final B4 assembly and axiom audit. -/
namespace Li2Lean.B4

open ResidueTailBridge Residues

theorem explicitResidueCertificate_all (n : ℕ) :
    ResidueTailBridge.ExplicitResidueCertificate n :=
  ResidueTailBridge.explicitResidueCertificate_all n

theorem hpartial_for_residueTailAlgebra_all (n : ℕ) :
    ∀ k, n < k →
      Residues.hpResidueConvolution n k = Residues.hpPhiValue n k :=
  ResidueTailBridge.hpartial_for_residueTailAlgebra_all n

theorem hpTailCoeff_all (n : ℕ) :
    ∀ k, 3 * n + 2 ≤ k →
      Residues.hpThreeFormCoeff n k = Residues.hpPhiValue n k :=
  ResidueTailBridge.hpTailCoeff_all n

end Li2Lean.B4



