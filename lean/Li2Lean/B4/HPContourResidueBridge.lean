/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B4.ResidueTailAlgebra

open Finset Polynomial

namespace Li2Lean.B4

noncomputable section

open Residues

/-! The coefficient sum produced by multiplying the v13 principal parts by
`exp(lambda w)`.  At an integer pole `j`, the exponential contributes
`z^j`; this is the `B_n + lambda C_n` combination in hp-tail.tex:256-266.
-/
def hpContourResidueSum (n : ℕ) (z lam : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (n + 1),
    z ^ j * (lam * (hpResidueU n j : ℂ) + (hpResidueV n j : ℂ))

theorem hpContourResidueSum_eq_forms (n : ℕ) (z lam : ℂ) :
    hpContourResidueSum n z lam =
      Polynomial.eval₂ (algebraMap ℚ ℂ) z (hpBpoly n) +
        lam * Polynomial.eval₂ (algebraMap ℚ ℂ) z (hpCpoly n) := by
  classical
  unfold hpContourResidueSum hpBpoly hpCpoly
  simp only [Polynomial.eval₂_finsetSum, Polynomial.eval₂_monomial]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib, Finset.mul_sum]
  conv_lhs => rw [← Finset.sum_add_distrib]
  conv_rhs => rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  norm_num
  ring

end

end Li2Lean.B4

#print axioms Li2Lean.B4.hpContourResidueSum_eq_forms
