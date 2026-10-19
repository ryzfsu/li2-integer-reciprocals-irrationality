/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Mathlib
import Li2Lean.V.VFamily

namespace Li2Lean
namespace V
namespace Q7Arithmetic

/-!
The q=7 specialization of the signed V arithmetic in paper v13.  This is a
certificate interface: residue ranks and pole potentials are executable data,
while the coefficientwise valuation inequalities remain explicit fields until
their proofs are supplied.

Source ledger: `v-arithmetic.tex:128-351` (formal credit, p-unit residue
blocks, rank profile, outer-pole assignment and precedence), with the source
matrix imported from `v-arithmetic.tex:13-35`.
-/

open scoped BigOperators

noncomputable section

def q : Nat := 7

def a : Int := -7

def exceptionalPrimes : Finset Nat := {2, 7}

theorem exceptionalPrimes_eq : exceptionalPrimes = ({2, 7} : Finset Nat) := rfl

theorem mem_exceptionalPrimes_iff {p : Nat} :
    p ∈ exceptionalPrimes ↔ p = 2 ∨ p = 7 := by
  simp [exceptionalPrimes]

theorem prime_not_exceptional_of_gt_seven {p : Nat} (hp : p.Prime)
    (hgt : 7 < p) : p ∉ exceptionalPrimes := by
  intro h
  rcases (mem_exceptionalPrimes_iff.mp h) with rfl | rfl <;> omega

def mSize (n : Nat) : Nat := vM n

def numeratorCutoff (n : Nat) : Nat := vN n

def denominatorCutoff (n : Nat) : Nat := vU n

def formalDivisorExponent (n : Nat) : Nat :=
  (53 * n ^ 2 + 2) / 3 - 4 * n

def naturalExponent (n p : Nat) : Int :=
  ((3 * mSize n * Nat.log p (numeratorCutoff n) +
      n * Nat.log p (denominatorCutoff n) : Nat) : Int)

def q7FormalCredit (n p : Nat) : Int :=
  if p = 7 then (formalDivisorExponent n : Int)
  else if p = 2 then (3 * (mSize n : Int))
  else 0

def q7ExceptionalExponent (n p : Nat) : Int :=
  naturalExponent n p - q7FormalCredit n p

theorem q7FormalCredit_eq (n : Nat) :
    q7FormalCredit n 2 = (3 * (mSize n : Int)) ∧
      q7FormalCredit n 7 = (formalDivisorExponent n : Int) ∧
      (∀ p, p ≠ 2 → p ≠ 7 → q7FormalCredit n p = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [q7FormalCredit]
  · simp [q7FormalCredit]
  · intro p hp2 hp7
    simp [q7FormalCredit, hp2, hp7]

structure PUnitData (n p : Nat) : Prop where
  n_positive : 0 < n
  prime : Nat.Prime p
  not_exceptional : p ∉ exceptionalPrimes
  square_large : max (numeratorCutoff n) (denominatorCutoff n) < p ^ 2

theorem PUnitData.not_two {n p : Nat} (h : PUnitData n p) : p ≠ 2 := by
  intro hp
  apply h.not_exceptional
  simp [exceptionalPrimes, hp]

theorem PUnitData.not_seven {n p : Nat} (h : PUnitData n p) : p ≠ 7 := by
  intro hp
  apply h.not_exceptional
  simp [exceptionalPrimes, hp]

def rho (n p : Nat) : Rat := (p : Rat) / (mSize n : Rat)

def xCoordinate (n _p u : Nat) : Rat := (u : Rat) / (mSize n : Rat)

def kSet (n p u : Nat) : Finset Nat :=
  (Finset.range p).filter fun k =>
    (1 / 2 : Rat) ≤ xCoordinate n p u + (k : Rat) * rho n p ∧
      xCoordinate n p u + (k : Rat) * rho n p < (3 / 2 : Rat)

def lSet (n p u : Nat) : Finset Nat :=
  (Finset.range p).filter fun ell =>
    (1 / 4 : Rat) ≤ xCoordinate n p u + (ell : Rat) * rho n p ∧
      xCoordinate n p u + (ell : Rat) * rho n p < (5 / 2 : Rat)

def wSet (n p u : Nat) : Finset Nat :=
  (Finset.range p).filter fun w =>
    1 ≤ w ∧ 0 < (w : Rat) * rho n p - xCoordinate n p u ∧
      (w : Rat) * rho n p - xCoordinate n p u ≤ (1 / 4 : Rat)

def savingProfile (n p u : Nat) : Prop :=
  kSet n p u = {0} ∧ lSet n p u = {0, 1} ∧ wSet n p u = ∅

noncomputable def profileRank (n p u : Nat) : Nat := by
  classical
  exact min (2 * (kSet n p u).card + (wSet n p u).card) (lSet n p u).card -
    if savingProfile n p u then 1 else 0

def residueExponent (n p : Nat) : Int :=
  (mSize n : Int) + ∑ u ∈ Finset.range p, (profileRank n p u : Int)

structure ResidueBlockCertificate (n p : Nat)
    (vp : Polynomial Rat → Int) : Prop where
  p_unit : PUnitData n p
  coefficientwise_bound : vp (vPolynomial n a) ≥ -residueExponent n p

theorem residueBlock_bound_of_certificate {n p : Nat}
    {vp : Polynomial Rat → Int} (h : ResidueBlockCertificate n p vp) :
    vp (vPolynomial n a) ≥ -residueExponent n p := h.coefficientwise_bound

def outerRange1 (n p : Nat) : Prop := 5 * n < p ∧ p < 6 * n

def outerRange2 (n p : Nat) : Prop := 6 * n ≤ p ∧ p < 8 * n

def outerRange3 (n p : Nat) : Prop := 8 * n ≤ p ∧ p < 10 * n

def outerRange4 (n p : Nat) : Prop := 10 * n ≤ p ∧ p ≤ denominatorCutoff n

def indicator (h : Prop) [Decidable h] : Nat := if h then 1 else 0

def lambdaB1 (n p i : Nat) : Nat := 1 + indicator (p ≤ i)

def lambdaV1 (_n _p _ell : Nat) : Nat := 1

def chi1 (n p j : Nat) : Nat := indicator (p + 2 * n ≤ j)

def lambdaB2 (n p i : Nat) : Nat := indicator (i + p < 10 * n)

def lambdaV2 (_n _p _ell : Nat) : Nat := 1

def chi2 (_n p j : Nat) : Nat := indicator (p ≤ j)

def lambdaB3 (_n _p _i : Nat) : Nat := 0

def lambdaV3 (_n _p _ell : Nat) : Nat := 1

def chi3 (_n p j : Nat) : Nat := indicator (p ≤ j)

def lambdaB4 (_n _p _i : Nat) : Nat := 0

def lambdaV4 (n p ell : Nat) : Nat := indicator (p - ell ∈ Finset.Ico n (10 * n))

def chi4 (_n _p _j : Nat) : Nat := 0

noncomputable def outerCost (n p : Nat) : Int := by
  classical
  exact if outerRange1 n p ∨ outerRange2 n p then
    (19 : Int) * n - 2 * p
  else if outerRange3 n p ∨ outerRange4 n p then
    (11 : Int) * n - p
  else 0

def outerExponent (n p : Nat) : Int := outerCost n p

theorem outer_ranges_disjoint12 {n p : Nat} :
    outerRange1 n p → ¬outerRange2 n p := by
  intro h1 h2
  simp only [outerRange1, outerRange2] at h1 h2
  omega

theorem outer_ranges_disjoint23 {n p : Nat} :
    outerRange2 n p → ¬outerRange3 n p := by
  intro h2 h3
  simp only [outerRange2, outerRange3] at h2 h3
  omega

theorem outer_ranges_disjoint34 {n p : Nat} :
    outerRange3 n p → ¬outerRange4 n p := by
  intro h3 h4
  simp only [outerRange3, outerRange4, denominatorCutoff] at h3 h4
  omega

theorem outer_cost_eq_range1 {n p : Nat} (h : outerRange1 n p) :
    outerCost n p = (19 : Int) * n - 2 * p := by
  simp [outerCost, h]

theorem outer_cost_eq_range2 {n p : Nat} (h : outerRange2 n p) :
    outerCost n p = (19 : Int) * n - 2 * p := by
  have h1 : ¬outerRange1 n p := by
    intro h1
    simp only [outerRange1, outerRange2] at h1 h
    omega
  simp [outerCost, h, h1]

theorem outer_cost_eq_range3 {n p : Nat} (h : outerRange3 n p) :
    outerCost n p = (11 : Int) * n - p := by
  have h1 : ¬outerRange1 n p := by
    intro h1
    simp only [outerRange1, outerRange3] at h1 h
    omega
  have h2 : ¬outerRange2 n p := by
    intro h2
    simp only [outerRange2, outerRange3] at h2 h
    omega
  simp [outerCost, h, h1, h2]

theorem outer_cost_eq_range4 {n p : Nat} (h : outerRange4 n p) :
    outerCost n p = (11 : Int) * n - p := by
  have h1 : ¬outerRange1 n p := by
    intro h1
    simp only [outerRange1, outerRange4, denominatorCutoff] at h1 h
    omega
  have h2 : ¬outerRange2 n p := by
    intro h2
    simp only [outerRange2, outerRange4, denominatorCutoff] at h2 h
    omega
  have h3 : ¬outerRange3 n p := by
    intro h3
    simp only [outerRange3, outerRange4, denominatorCutoff] at h3 h
    omega
  simp [outerCost, h, h1, h2, h3]

structure OuterPoleCertificate (n p : Nat)
    (vp : Polynomial Rat → Int) : Prop where
  in_outer_range : outerRange1 n p ∨ outerRange2 n p ∨
    outerRange3 n p ∨ outerRange4 n p
  coefficientwise_bound : vp (vPolynomial n a) ≥ -outerExponent n p

theorem outerPole_bound_of_certificate {n p : Nat}
    {vp : Polynomial Rat → Int} (h : OuterPoleCertificate n p vp) :
    vp (vPolynomial n a) ≥ -outerExponent n p := h.coefficientwise_bound

end
end Q7Arithmetic
end V
end Li2Lean
