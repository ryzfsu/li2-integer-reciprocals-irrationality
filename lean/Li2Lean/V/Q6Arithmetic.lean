/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Mathlib
import Li2Lean.V.VFamily

/-!
# The q = 6 arithmetic interface for the signed V-family

This file records the fixed-base arithmetic data from v13.  It is deliberately
an interface: the p-adic determinant estimates are represented by explicit
certificate fields, rather than being replaced by an unproved `sorry` or by a
different determinant construction.

Source ledger:

* `source/chapters/v-arithmetic.tex:37-145`: the formal q = 6 credit and
  exceptional-prime exponent.
* `source/chapters/v-arithmetic.tex:128-287`: p-unit residue blocks,
  `K/L/W`, the rank profile, and the coefficientwise residue exponent.
* `source/chapters/v-arithmetic.tex:289-351`: outer pole ranges, potentials,
  costs, and precedence.

The q = 6 specialization is `a = -6`, `m = 4 n`, `N = 10 n - 1`, and
`U = 11 n - 1`.  No P0 numerical profile is imported here.
-/

namespace Li2Lean
namespace V
namespace Q6Arithmetic

open scoped BigOperators

noncomputable section

/-! ## Fixed q = 6 data -/

def q : ℕ := 6

def a : ℤ := -6

def exceptionalPrimes : Finset ℕ := {2, 3, 7}

theorem exceptionalPrimes_eq : exceptionalPrimes = ({2, 3, 7} : Finset ℕ) := rfl

theorem mem_exceptionalPrimes_iff {p : ℕ} :
    p ∈ exceptionalPrimes ↔ p = 2 ∨ p = 3 ∨ p = 7 := by
  simp [exceptionalPrimes]

theorem prime_not_exceptional_of_gt_seven {p : ℕ} (hp : p.Prime)
    (hgt : 7 < p) : p ∉ exceptionalPrimes := by
  intro h
  rcases (mem_exceptionalPrimes_iff.mp h) with rfl | rfl | rfl <;> omega

/-! ## v13 index geometry and formal divisor -/

def mSize (n : ℕ) : ℕ := 4 * n

def iRows (n : ℕ) : Finset ℕ := Finset.Ico (2 * n) (6 * n)

def jCols (n : ℕ) : Finset ℕ := Finset.Ico n (10 * n)

def lambdaRows (n : ℕ) : Finset ℕ := Finset.Icc 1 n

def numeratorCutoff (n : ℕ) : ℕ := 10 * n - 1

def denominatorCutoff (n : ℕ) : ℕ := 11 * n - 1

theorem card_iRows (n : ℕ) : (iRows n).card = 4 * n := by
  simp [iRows]
  omega

theorem card_jCols (n : ℕ) : (jCols n).card = 9 * n := by
  simp [jCols]
  omega

theorem card_lambdaRows (n : ℕ) : (lambdaRows n).card = n := by
  simp [lambdaRows]

theorem numeratorCutoff_eq (n : ℕ) (hn : 0 < n) :
    numeratorCutoff n + 1 = 10 * n := by
  unfold numeratorCutoff
  exact Nat.sub_add_cancel (by omega)

theorem denominatorCutoff_eq (n : ℕ) (hn : 0 < n) :
    denominatorCutoff n + 1 = 11 * n := by
  unfold denominatorCutoff
  exact Nat.sub_add_cancel (by omega)

/-
The paper's formal exponent is
`D_m = ceil (53 n^2 / 3) - 4 n`.  The natural-number expression below is
the exact ceiling for an integer numerator.  Keeping it as a separate name
also prevents the q = 6 formal factor from being confused with the residue
rank exponent.
-/
def formalDivisorExponent (n : ℕ) : ℕ :=
  (53 * n ^ 2 + 2) / 3 - 4 * n

theorem formalDivisorExponent_eq_paper (n : ℕ) :
    formalDivisorExponent n = (53 * n ^ 2 + 2) / 3 - 4 * n := rfl

def naturalExponent (n p : ℕ) : ℤ :=
  ((3 * mSize n * Nat.log p (numeratorCutoff n) +
      n * Nat.log p (denominatorCutoff n) : ℕ) : ℤ)

def q6FormalCredit (n p : ℕ) : ℤ :=
  if p = 2 then (formalDivisorExponent n : ℤ)
  else if p = 3 then (formalDivisorExponent n : ℤ)
  else if p = 7 then (mSize n : ℤ)
  else 0

def q6ExceptionalExponent (n p : ℕ) : ℤ :=
  naturalExponent n p - q6FormalCredit n p

theorem q6FormalCredit_eq (n : ℕ) :
    q6FormalCredit n 2 = (formalDivisorExponent n : ℤ) ∧
      q6FormalCredit n 3 = (formalDivisorExponent n : ℤ) ∧
      q6FormalCredit n 7 = (mSize n : ℤ) ∧
      (∀ p, p ≠ 2 → p ≠ 3 → p ≠ 7 → q6FormalCredit n p = 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [q6FormalCredit]
  · simp [q6FormalCredit]
  · simp [q6FormalCredit]
  · intro p hp2 hp3 hp7
    simp [q6FormalCredit, hp2, hp3, hp7]

/-! ## p-unit residue blocks (`v-arithmetic.tex:128-287`) -/

structure PUnitData (n p : ℕ) : Prop where
  n_positive : 0 < n
  prime : Nat.Prime p
  not_exceptional : p ∉ exceptionalPrimes
  square_large : max (numeratorCutoff n) (denominatorCutoff n) < p ^ 2

theorem PUnitData.not_two (n p : ℕ) (h : PUnitData n p) : p ≠ 2 := by
  intro hp
  apply h.not_exceptional
  simp [exceptionalPrimes, hp]

theorem PUnitData.not_three (n p : ℕ) (h : PUnitData n p) : p ≠ 3 := by
  intro hp
  apply h.not_exceptional
  simp [exceptionalPrimes, hp]

theorem PUnitData.not_seven (n p : ℕ) (h : PUnitData n p) : p ≠ 7 := by
  intro hp
  apply h.not_exceptional
  simp [exceptionalPrimes, hp]

def rho (n p : ℕ) : ℚ := (p : ℚ) / (mSize n : ℚ)

def xCoordinate (n _p u : ℕ) : ℚ :=
  (u : ℚ) / (mSize n : ℚ)

def kSet (n p u : ℕ) : Finset ℕ :=
  (Finset.range p).filter fun k =>
    (1 / 2 : ℚ) ≤ xCoordinate n p u + (k : ℚ) * rho n p ∧
      xCoordinate n p u + (k : ℚ) * rho n p < (3 / 2 : ℚ)

def lSet (n p u : ℕ) : Finset ℕ :=
  (Finset.range p).filter fun ell =>
    (1 / 4 : ℚ) ≤ xCoordinate n p u + (ell : ℚ) * rho n p ∧
      xCoordinate n p u + (ell : ℚ) * rho n p < (5 / 2 : ℚ)

def wSet (n p u : ℕ) : Finset ℕ :=
  (Finset.range p).filter fun w =>
    1 ≤ w ∧
      0 < (w : ℚ) * rho n p - xCoordinate n p u ∧
      (w : ℚ) * rho n p - xCoordinate n p u ≤ (1 / 4 : ℚ)

def savingProfile (n p u : ℕ) : Prop :=
  kSet n p u = {0} ∧ lSet n p u = {0, 1} ∧ wSet n p u = ∅

noncomputable def profileRank (n p u : ℕ) : ℕ := by
  classical
  exact
  min (2 * (kSet n p u).card + (wSet n p u).card) (lSet n p u).card -
    if savingProfile n p u then 1 else 0

def residueExponent (n p : ℕ) : ℤ :=
  (mSize n : ℤ) + ∑ u ∈ Finset.range p, (profileRank n p u : ℤ)

theorem profileRank_nonneg (n p u : ℕ) : 0 ≤ profileRank n p u := by
  exact Nat.zero_le _

/-
The next structure is the kernel-facing arithmetic contract.  `vp` is supplied
by the eventual coefficientwise Gauss valuation implementation and `G` by the
v13 determinant module.  This keeps the present file honest: constructing the
certificate is the remaining arithmetic proof, while downstream files can
consume one stable proposition.
-/
structure ResidueBlockCertificate (n p : ℕ)
    (vp : Polynomial ℚ → ℤ) : Prop where
  p_unit : PUnitData n p
  coefficientwise_bound : vp (vPolynomial n a) ≥ -residueExponent n p

theorem residueBlock_bound_of_certificate {n p : ℕ}
    {vp : Polynomial ℚ → ℤ}
    (h : ResidueBlockCertificate n p vp) :
    vp (vPolynomial n a) ≥ -residueExponent n p :=
  h.coefficientwise_bound

/-! ## Outer pole assignment (`v-arithmetic.tex:289-351`) -/

def outerRange₁ (n p : ℕ) : Prop := 5 * n < p ∧ p < 6 * n

def outerRange₂ (n p : ℕ) : Prop := 6 * n ≤ p ∧ p < 8 * n

def outerRange₃ (n p : ℕ) : Prop := 8 * n ≤ p ∧ p < 10 * n

def outerRange₄ (n p : ℕ) : Prop := 10 * n ≤ p ∧ p ≤ denominatorCutoff n

def indicator (h : Prop) [Decidable h] : ℕ := if h then 1 else 0

def lambdaB₁ (n p i : ℕ) : ℕ := 1 + indicator (p ≤ i)

def lambdaV₁ (_n _p _ell : ℕ) : ℕ := 1

def chi₁ (n p j : ℕ) : ℕ := indicator (p + 2 * n ≤ j)

def lambdaB₂ (n p i : ℕ) : ℕ := indicator (i + p < 10 * n)

def lambdaV₂ (_n _p _ell : ℕ) : ℕ := 1

def chi₂ (_n p j : ℕ) : ℕ := indicator (p ≤ j)

def lambdaB₃ (_n _p _i : ℕ) : ℕ := 0

def lambdaV₃ (_n _p _ell : ℕ) : ℕ := 1

def chi₃ (_n p j : ℕ) : ℕ := indicator (p ≤ j)

def lambdaB₄ (_n _p _i : ℕ) : ℕ := 0

def lambdaV₄ (n p ell : ℕ) : ℕ :=
  indicator (p - ell ∈ jCols n)

def chi₄ (_n _p _j : ℕ) : ℕ := 0

noncomputable def outerCost (n p : ℕ) : ℤ := by
  classical
  exact if outerRange₁ n p ∨ outerRange₂ n p then
    (19 : ℤ) * n - 2 * p
  else if outerRange₃ n p ∨ outerRange₄ n p then
    (11 : ℤ) * n - p
  else 0

def outerExponent (n p : ℕ) : ℤ := outerCost n p

theorem outer_ranges_disjoint₁₂ {n p : ℕ} :
    outerRange₁ n p → ¬outerRange₂ n p := by
  intro h1 h2
  simp only [outerRange₁, outerRange₂] at h1 h2
  omega

theorem outer_ranges_disjoint₂₃ {n p : ℕ} :
    outerRange₂ n p → ¬outerRange₃ n p := by
  intro h2 h3
  simp only [outerRange₂, outerRange₃] at h2 h3
  omega

theorem outer_ranges_disjoint₃₄ {n p : ℕ} :
    outerRange₃ n p → ¬outerRange₄ n p := by
  intro h3 h4
  simp only [outerRange₃, outerRange₄, denominatorCutoff] at h3 h4
  omega

theorem outer_cost_eq_first {n p : ℕ} (h : outerRange₁ n p) :
    outerCost n p = (19 : ℤ) * n - 2 * p := by
  simp [outerCost, h]

theorem outer_cost_eq_second {n p : ℕ} (h : outerRange₂ n p) :
    outerCost n p = (19 : ℤ) * n - 2 * p := by
  have h₁ : ¬outerRange₁ n p := by
    intro h₁
    simp only [outerRange₁, outerRange₂] at h₁ h
    omega
  simp [outerCost, h, h₁]

theorem outer_cost_eq_third {n p : ℕ} (h : outerRange₃ n p) :
    outerCost n p = (11 : ℤ) * n - p := by
  have h₁ : ¬outerRange₁ n p := by
    intro h₁
    simp only [outerRange₁, outerRange₃] at h₁ h
    omega
  have h₂ : ¬outerRange₂ n p := by
    intro h₂
    simp only [outerRange₂, outerRange₃] at h₂ h
    omega
  simp [outerCost, h, h₁, h₂]

theorem outer_cost_eq_fourth {n p : ℕ} (h : outerRange₄ n p) :
    outerCost n p = (11 : ℤ) * n - p := by
  have h₁ : ¬outerRange₁ n p := by
    intro h₁
    simp only [outerRange₁, outerRange₄, denominatorCutoff] at h₁ h
    omega
  have h₂ : ¬outerRange₂ n p := by
    intro h₂
    simp only [outerRange₂, outerRange₄, denominatorCutoff] at h₂ h
    omega
  have h₃ : ¬outerRange₃ n p := by
    intro h₃
    simp only [outerRange₃, outerRange₄, denominatorCutoff] at h₃ h
    omega
  simp [outerCost, h, h₁, h₂, h₃]

theorem outer_cost_nonneg {n p : ℕ}
    (h : outerRange₁ n p ∨ outerRange₂ n p ∨
      outerRange₃ n p ∨ outerRange₄ n p) :
    0 ≤ outerCost n p := by
  rcases h with h | h | h | h
  · rw [outer_cost_eq_first h]
    simp only [outerRange₁] at h
    omega
  · rw [outer_cost_eq_second h]
    simp only [outerRange₂] at h
    omega
  · rw [outer_cost_eq_third h]
    simp only [outerRange₃] at h
    omega
  · rw [outer_cost_eq_fourth h]
    simp only [outerRange₄, denominatorCutoff] at h
    have hu : p ≤ 11 * n - 1 := h.2
    omega

/-
As with the residue block certificate, this is the explicit outer-pole
contract consumed by integerization.  The four potential families above are
the data to be checked entry by entry; this field is the unresolved
coefficientwise determinant estimate.
-/
structure OuterPoleCertificate (n p : ℕ)
    (vp : Polynomial ℚ → ℤ) : Prop where
  in_outer_range : outerRange₁ n p ∨ outerRange₂ n p ∨
    outerRange₃ n p ∨ outerRange₄ n p
  coefficientwise_bound : vp (vPolynomial n a) ≥ -outerExponent n p

theorem outerPole_bound_of_certificate {n p : ℕ}
    {vp : Polynomial ℚ → ℤ}
    (h : OuterPoleCertificate n p vp) :
    vp (vPolynomial n a) ≥ -outerExponent n p :=
  h.coefficientwise_bound

end
end Q6Arithmetic
end V
end Li2Lean
