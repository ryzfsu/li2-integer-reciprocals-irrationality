/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Mathlib

open Finset Polynomial

namespace Li2Lean.B4.Residues

noncomputable section

/-- The v13 harmonic number convention `H_k`; `hp-tail.tex:19`. -/
def hpHarmonic (k : ℕ) : ℚ :=
  ∑ r ∈ Finset.range k, ((r + 1 : ℕ) : ℚ)⁻¹

/-- The v13 numerator of `Phi_n`; `hp-tail.tex:12-18`. -/
def hpNumerator (n : ℕ) : ℚ[X] :=
  ∏ r ∈ Finset.Icc (n + 1) (3 * n + 1),
    (Polynomial.X - Polynomial.C (r : ℚ))

/-- The v13 linear pole at `j`; `hp-tail.tex:14-18`. -/
def hpPole (j : ℕ) : ℚ[X] := Polynomial.X - Polynomial.C (j : ℚ)

/-- The repeated-pole partial-fraction data exists by Mathlib's generic
Hermite partial-fraction theorem; this is only an existence scaffold for
the v13 formula `hp-tail.tex:14-18`. -/
theorem hp_partial_fraction_exists (n : ℕ) :
    ∃ q : ℚ[X], ∃ r : ℕ → Fin 2 → ℚ[X],
      (∀ i ∈ Finset.range (n + 1), ∀ k, (r i k).degree < (hpPole i).degree) ∧
      hpNumerator n =
        q * (∏ i ∈ Finset.range (n + 1), hpPole i ^ 2) +
          ∑ i ∈ Finset.range (n + 1),
            ∑ k : Fin 2,
              r i k * hpPole i ^ (k.1 : ℕ) *
                ∏ l ∈ (Finset.range (n + 1)).erase i, hpPole l ^ 2 := by
  classical
  let s : Finset ℕ := Finset.range (n + 1)
  let g : ℕ → ℚ[X] := hpPole
  have hg : ∀ i ∈ s, (g i).Monic := by
    intro i hi
    simp only [g, hpPole]
    exact Polynomial.monic_X_sub_C (i : ℚ)
  have hcop : Set.Pairwise (↑s : Set ℕ) fun i j => IsCoprime (g i) (g j) := by
    intro i hi j hj hij
    apply Polynomial.isCoprime_X_sub_C_of_isUnit_sub
    apply isUnit_iff_ne_zero.mpr
    have hij' : (i : ℚ) ≠ (j : ℚ) := by exact_mod_cast hij
    exact sub_ne_zero.mpr hij'
  obtain ⟨q, r, hr, heq⟩ :=
    Polynomial.eq_quo_mul_prod_pow_add_sum_rem_mul_prod_pow
      (f := hpNumerator n) (g := g) (s := s) hg hcop (fun _ => 2)
  refine ⟨q, r, ?_, ?_⟩
  · intro i hi k
    simpa [g, hpPole] using hr i hi k
  · simpa [s, g, hpPole, hpNumerator] using heq

end

end Li2Lean.B4.Residues
