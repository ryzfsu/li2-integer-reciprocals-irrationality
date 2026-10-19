/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Mathlib
import Li2Lean.Kit.ContourKit
import Li2Lean.P0.ConfigFgBound
import Li2Lean.B4.ResidueTailAlgebra

/-!
# Typed negative contour interface for B4

This is a development-only boundary for the negative bases `q = 8, 9, 10`.
The contour argument in paper v13, `hp-tail.tex:258-404`, is deliberately not
reproved here.  The fixed rational height `beta' = 1/5` is a proposed
replacement for the exact saddle height in `hp-tail.tex:258-279`; proving its
boundary maximum and the resulting coefficient estimate remains open.

The eventual proof can reuse the finite-product estimate
`Li2Lean.P0.Config.fgBound` (`P0.ConfigFgBound`) and the ellipse/Joukowski and
rational-interval primitives in `ContourKit`. Construction-bound provider
theorems live in `NegativeContourQSpecificProducers`; they are imported at
their consumers to avoid a cycle through `NegativeContourBoundary`.
-/

namespace Li2Lean.B4.NegativeContour

noncomputable section

open Li2Lean.B4.Residues

/-! `BSequence` is retained as the reusable rectangle-certificate shape.  The
q-specific producers below always instantiate it with `hpBSequence`, the
concrete v13 partial-fraction polynomial. -/
abbrev BSequence := ℕ → ℚ → ℝ

/-! The contour estimate is for the concrete B_n from the Hermite
partial-fraction construction, not for an arbitrary sequence. Keeping the
function type as a small abbreviation lets the rectangle certificate retain
its reusable shape, while all q-specific producers below are specialized to
this definition. This is the B_n polynomial of hp-tail.tex:26. -/
def hpBSequence : BSequence :=
  fun n z => ((Polynomial.eval z (hpBpoly n) : ℚ) : ℝ)

/-!
The exact typed obligation needed for the three exceptional negative bases:

`∃ C k, ∀ n, |B_n(-1/q)| ≤ C * (n+1)^k * 29^n`.

The polynomial factor is represented by a natural exponent `k`; no positivity
assumption on the witnessing constant is hidden in this interface.
-/
def NegContourB (B : BSequence) (q : ℕ) : Prop :=
  ∃ C : ℝ, ∃ k : ℕ, ∀ n : ℕ,
    |B n (-((1 : ℚ) / (q : ℚ)))| ≤
      C * ((n + 1 : ℕ) : ℝ) ^ k * (29 : ℝ) ^ n

def concreteNegContourB (q : ℕ) : Prop := NegContourB hpBSequence q

/-- The all-index coefficient estimate supplies the eventual rate used by
the B4 tail argument at `hp-tail.tex:406-475`. -/
theorem NegContourB.eventually_bound {B : BSequence} {q : ℕ}
    (h : NegContourB B q) :
    ∃ C : ℝ, ∃ k : ℕ, ∀ᶠ n : ℕ in Filter.atTop,
      |B n (-((1 : ℚ) / (q : ℚ)))| ≤
        C * ((n + 1 : ℕ) : ℝ) ^ k * (29 : ℝ) ^ n := by
  obtain ⟨C, k, hbound⟩ := h
  exact ⟨C, k, Filter.Eventually.of_forall hbound⟩

/-- The only negative bases for which the contour cancellation is required. -/
def negativeContourBases : Finset ℕ := {8, 9, 10}

theorem mem_negativeContourBases_iff (q : ℕ) :
    q ∈ negativeContourBases ↔ q = 8 ∨ q = 9 ∨ q = 10 := by
  simp [negativeContourBases]

/-- The exact cast from a negative integer base to the natural denominator
used by both the exceptional contour and the elementary negative tail. -/
theorem negative_int_base {a : ℤ} (ha : a ≤ -8) :
    ∃ q : ℕ, 8 ≤ q ∧ a = -(q : ℤ) ∧
      (1 / (a : ℚ)) = -((1 : ℚ) / (q : ℚ)) := by
  let q : ℕ := (-a).natAbs
  have hnonneg : 0 ≤ -a := by omega
  have hqZ : (q : ℤ) = -a := Int.natAbs_of_nonneg hnonneg
  have hq8 : 8 ≤ q := by
    have hq8Z : (8 : ℤ) ≤ (q : ℤ) := by omega
    exact_mod_cast hq8Z
  have ha_q : a = -(q : ℤ) := by omega
  refine ⟨q, hq8, ha_q, ?_⟩
  have ha_q' : (a : ℚ) = -(q : ℚ) := by exact_mod_cast ha_q
  simp [ha_q']

/-- For the elementary branch `a ≤ -11`, `z = 1/a` lies in the required
negative real interval.  This lemma makes no contour estimate. -/
theorem elementary_negative_z_range {a : ℤ} (ha : a ≤ -11) :
    ∃ q : ℕ, 11 ≤ q ∧ a = -(q : ℤ) ∧
      (1 / (a : ℚ)) = -((1 : ℚ) / (q : ℚ)) ∧
      -(1 / 11 : ℚ) ≤ 1 / (a : ℚ) ∧ 1 / (a : ℚ) < 0 := by
  obtain ⟨q, _, haq, hz⟩ := negative_int_base (by omega : a ≤ -8)
  have hq11 : 11 ≤ q := by
    have hq11Z : (11 : ℤ) ≤ (q : ℤ) := by omega
    exact_mod_cast hq11Z
  have hqpos : (0 : ℚ) < q := by exact_mod_cast (by omega : 0 < q)
  have hq11Q : (11 : ℚ) ≤ q := by exact_mod_cast hq11
  have hrec : (1 : ℚ) / q ≤ 1 / 11 := by
    apply (div_le_div_iff₀ hqpos (by norm_num : (0 : ℚ) < 11)).2
    nlinarith
  have hrecpos : 0 < (1 : ℚ) / q := by positivity
  refine ⟨q, hq11, haq, hz, ?_, ?_⟩
  · rw [hz]
    linarith
  · rw [hz]
    linarith

/-!
A rational rectangle record for the future contour certificate.  `realPart`
and `imagPart` are the rational boxes to be fed to `ContourKit.QInterval`
containment lemmas; `beta'` is the fixed rational height from the tail plan.
-/
structure RationalBetaRectangle where
  realPart : ContourKit.QInterval
  imagPart : ContourKit.QInterval
  beta' : ℚ
  beta'_eq : beta' = (1 / 5 : ℚ)

/-! The unscaled v13 rectangle at index `n`: `hp-tail.tex:268-275`. -/
def rationalBetaRectangle (n : ℕ) : RationalBetaRectangle where
  realPart := ⟨-1 / 2, (n : ℚ) + 1 / 2, by
    have hn : (0 : ℚ) ≤ (n : ℚ) := by exact_mod_cast Nat.zero_le n
    linarith⟩
  imagPart := ⟨-(n : ℚ) / 5, (n : ℚ) / 5, by
    have hn : (0 : ℚ) ≤ (n : ℚ) := by exact_mod_cast Nat.zero_le n
    linarith⟩
  beta' := 1 / 5
  beta'_eq := rfl

/-!
The certificate carries the contour-to-coefficient estimate as a field so that
future consumers can use a typed object without unfolding the analytic proof.
The rectangle field is forced to be the v13 shape with the rational height
`beta' = 1/5`; q-specific provider-input results are declared in
`NegativeContourQSpecificProducers`.
-/
structure NegContourRectangleCertificate (B : BSequence) (q : ℕ) where
  rectangle : ℕ → RationalBetaRectangle
  rectangle_eq : ∀ n, rectangle n = rationalBetaRectangle n
  q_mem : q ∈ negativeContourBases
  contour_bound : NegContourB B q

theorem negContourB_of_rectangle
    {B : BSequence} {q : ℕ}
    (certificate : NegContourRectangleCertificate B q) :
    NegContourB B q := by
  exact certificate.contour_bound

end

end Li2Lean.B4.NegativeContour

/-! Axiom receipt for this development-only interface. -/
#print axioms Li2Lean.B4.NegativeContour.NegContourB.eventually_bound
#print axioms Li2Lean.B4.NegativeContour.negative_int_base
#print axioms Li2Lean.B4.NegativeContour.elementary_negative_z_range
