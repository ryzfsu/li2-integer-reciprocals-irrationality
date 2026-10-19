/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B4.ResidueTailBridge

open Finset Polynomial

namespace Li2Lean.B4.ResidueTailBridge

noncomputable section

open Li2Lean.B4.Residues

/-!  Generic and degree-side pieces of the all-`n` explicit residue
    certificate.  The objects in this file remain the construction from
    `hp-tail.tex:12-23`; no abstract numerator or pole family is introduced. -/

/-! ## The finite summand -/

/-- The `j`-th numerator summand after clearing the squared pole denominator,
    v13 `hp-tail.tex:16-17`. -/
def hpResidueTerm (n j : ℕ) : ℚ[X] :=
  (Polynomial.C (hpResidueU n j) +
      Polynomial.C (hpResidueV n j) * hpPole j) *
    (hpOffPoly n j) ^ 2

/-! ## Local polynomial facts -/

/-- A value and its formal derivative both vanish at `a` exactly enough for
    the squared linear factor `(X-a)^2` to divide the polynomial. -/
theorem sq_X_sub_C_dvd_of_eval {p : ℚ[X]} {a : ℚ}
    (h0 : p.eval a = 0) (h1 : (derivative p).eval a = 0) :
    (X - C a) ^ 2 ∣ p := by
  obtain ⟨g, rfl⟩ := Polynomial.dvd_iff_isRoot.mpr h0
  have hg : g.eval a = 0 := by
    simpa [derivative_mul] using h1
  obtain ⟨h, rfl⟩ := Polynomial.dvd_iff_isRoot.mpr hg
  exact ⟨h, by ring⟩

/-- Logarithmic derivative of a finite product of distinct linear factors,
    evaluated away from all of its roots. -/
theorem eval_derivative_prod_X_sub_C (S : Finset ℕ) (a : ℚ)
    (ha : ∀ r ∈ S, a - (r : ℚ) ≠ 0) :
    (derivative (∏ r ∈ S, (X - C (r : ℚ)))).eval a =
      (∏ r ∈ S, (a - (r : ℚ))) * ∑ r ∈ S, (a - (r : ℚ))⁻¹ := by
  revert ha
  refine Finset.induction_on S ?_ ?_
  · intro _
    simp
  · intro r S hr ih ha
    have har : a - (r : ℚ) ≠ 0 := ha r (Finset.mem_insert_self r S)
    have ih' := ih (fun s hs => ha s (Finset.mem_insert_of_mem hs))
    rw [Finset.prod_insert hr, derivative_mul, Finset.prod_insert hr,
      Finset.sum_insert hr]
    simp only [eval_add, eval_mul]
    rw [ih']
    simp only [derivative_X_sub_C, eval_one, eval_sub, eval_X, eval_C,
      eval_prod]
    have hinv : (a - (r : ℚ)) * (a - (r : ℚ))⁻¹ = 1 :=
      mul_inv_cancel₀ har
    linear_combination (-(∏ s ∈ S, (a - (s : ℚ)))) * hinv

/-- The interval used by `hpNumerator` is an `Ico` after increasing its upper
    endpoint by one. -/
theorem Icc_eq_Ico_succ (a b : ℕ) :
    Finset.Icc a b = Finset.Ico a (b + 1) := by
  ext x
  simp only [Finset.mem_Icc, Finset.mem_Ico]
  omega

/-! ## Divisibility of the non-self summands -/

/-- If `i ≠ j`, the `i`-th summand contains the squared pole factor at `j`.
    This is the off-node part of the double-root argument in
    `hp-tail.tex:20-23`. -/
theorem sq_pole_dvd_hpResidueTerm (n i j : ℕ)
    (hj : j ∈ Finset.range (n + 1)) (hij : i ≠ j) :
    hpPole j ^ 2 ∣ hpResidueTerm n i := by
  have hmem : j ∈ (Finset.range (n + 1)).erase i :=
    Finset.mem_erase.mpr ⟨Ne.symm hij, hj⟩
  have hoff : hpPole j ∣ hpOffPoly n i := by
    unfold hpOffPoly
    exact Finset.dvd_prod_of_mem hpPole hmem
  unfold hpResidueTerm
  exact Dvd.dvd.mul_left (pow_dvd_pow_of_dvd hoff 2) _

/-! ## Degree bounds for the concrete certificate -/

theorem natDegree_hpNumerator_le (n : ℕ) :
    (hpNumerator n).natDegree ≤ 2 * n + 1 := by
  unfold hpNumerator
  refine (natDegree_prod_le _ _).trans ?_
  simp only [natDegree_X_sub_C, Finset.sum_const, smul_eq_mul, mul_one,
    Nat.card_Icc]
  omega

theorem natDegree_hpOffPoly_le (n j : ℕ)
    (hj : j ∈ Finset.range (n + 1)) :
    (hpOffPoly n j).natDegree ≤ n := by
  unfold hpOffPoly hpPole
  refine (natDegree_prod_le _ _).trans ?_
  simp only [natDegree_X_sub_C, Finset.sum_const, smul_eq_mul, mul_one,
    Finset.card_erase_of_mem hj, Finset.card_range]
  omega

theorem natDegree_hpResidueTerm_le (n j : ℕ)
    (hj : j ∈ Finset.range (n + 1)) :
    (hpResidueTerm n j).natDegree ≤ 2 * n + 1 := by
  have h1 : (Polynomial.C (hpResidueU n j) +
      Polynomial.C (hpResidueV n j) * hpPole j).natDegree ≤ 1 := by
    refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
    · simp
    · refine (natDegree_C_mul_le _ _).trans ?_
      change (X - C (j : ℚ)).natDegree ≤ 1
      rw [natDegree_X_sub_C]
  have h2 : ((hpOffPoly n j) ^ 2).natDegree ≤ 2 * n := by
    have h := natDegree_hpOffPoly_le n j hj
    refine natDegree_pow_le.trans ?_
    omega
  unfold hpResidueTerm
  refine natDegree_mul_le.trans ?_
  omega

theorem natDegree_hpPoleSq_prod (n : ℕ) :
    (∏ j ∈ Finset.range (n + 1), hpPole j ^ 2).natDegree = 2 * n + 2 := by
  unfold hpPole
  have hm : ∀ j ∈ Finset.range (n + 1),
      ((X - C (j : ℚ)) ^ 2 : ℚ[X]).Monic := by
    intro j hj
    exact (Polynomial.monic_X_sub_C (j : ℚ)).pow 2
  rw [natDegree_prod_of_monic (Finset.range (n + 1))
    (fun j => (X - C (j : ℚ)) ^ 2) hm]
  simp only [natDegree_pow, natDegree_X_sub_C, Finset.sum_const,
    Finset.card_range, smul_eq_mul]
  ring

/-! ## Assembly once the concrete double-root producer is supplied -/

/-- The actual residual-divisibility and degree obligations imply the actual
    polynomial identity.  This is the construction-bound assembly point for
    the E0/E1 proof, with all numerator and summand definitions fixed. -/
theorem explicitResidueCertificate_of_dvd_degree (n : ℕ)
    (hdvd : (∏ j ∈ Finset.range (n + 1), hpPole j ^ 2) ∣
      hpNumerator n - ∑ j ∈ Finset.range (n + 1), hpResidueTerm n j)
    (hdeg : (hpNumerator n -
      ∑ j ∈ Finset.range (n + 1), hpResidueTerm n j).natDegree <
      (∏ j ∈ Finset.range (n + 1), hpPole j ^ 2).natDegree) :
    ExplicitResidueCertificate n := by
  refine ⟨?_⟩
  have hR0 := Polynomial.eq_zero_of_dvd_of_natDegree_lt hdvd hdeg
  exact sub_eq_zero.mp hR0

end

end Li2Lean.B4.ResidueTailBridge
