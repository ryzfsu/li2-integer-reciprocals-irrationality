/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/

import Mathlib
import Li2Lean.Statement
import Li2Lean.V.VFamily
import Li2Lean.V.Q2Arithmetic
import Li2Lean.V.Q4Arithmetic
import Li2Lean.V.Q5Certificate
import Li2Lean.V.Q6Arithmetic
import Li2Lean.V.Q7Arithmetic

/-!
Pinned arithmetic adapters for the signed V construction.

The arithmetic contracts in `Q2Arithmetic`, `Q4Arithmetic`, `Q6Arithmetic`,
and `Q7Arithmetic` intentionally expose a valuation argument.  This file is
the boundary used by the top-down proof: every consumed certificate fixes that
argument to the Gauss valuation of the actual determinant polynomial
`V.vPolynomial n (-q)`.  The q=5 contracts use the same determinant for their
valuation and analytic function.  Thus a certificate cannot be discharged by
choosing `fun _ => 0` or an unrelated determinant function.

The definitions implement v13 `v-arithmetic.tex:13-35,128-351` and
`nonvanishing.tex:146-198`; they reuse the generic determinant family in
`Li2Lean.V.VFamily` (the positive `a = 2` instance is unchanged).
-/

namespace Li2Lean
namespace V

open scoped BigOperators

noncomputable section

/- The generic determinant parameter is retained so the positive `a = 2`
regression is a definitional instance of the same family.  The signed route
uses `a = -q` below (v13 `v-arithmetic.tex:13-35`). -/
def actualDeterminantAt (a : ℤ) (m : ℕ) : Polynomial ℚ :=
  V.vPolynomial (m / 4) a

/-- The determinant polynomial used by the signed V construction. -/
def actualVDeterminant (q m : ℕ) : Polynomial ℚ :=
  actualDeterminantAt (-(q : ℤ)) m

theorem actualDeterminantAt_two (m : ℕ) :
    actualDeterminantAt 2 m = V.vPolynomial (m / 4) (2 : ℤ) := rfl

theorem actualVDeterminant_four_mul (q n : ℕ) :
    actualVDeterminant q (4 * n) = V.vPolynomial n (-(q : ℤ)) := by
  unfold actualVDeterminant actualDeterminantAt
  rw [Nat.mul_div_cancel_left n (by norm_num : (0 : ℕ) < 4)]

/-- Coefficientwise Gauss valuation of a rational polynomial.
The empty support convention is Mathlib's zero valuation convention. -/
def actualGaussValuation (p : ℕ) (P : Polynomial ℚ) : ℤ :=
  if h : P.support.Nonempty then
    P.support.inf' h (fun i => padicValRat p (P.coeff i))
  else 0

theorem actualGaussValuation_coeff {p : ℕ} {P : Polynomial ℚ} {E : ℤ}
    (h : actualGaussValuation p P ≥ -E) :
    ∀ i : ℕ, P.coeff i ≠ 0 → -E ≤ padicValRat p (P.coeff i) := by
  intro i hi
  have hmem : i ∈ P.support := Polynomial.mem_support_iff.mpr hi
  have hne : P.support.Nonempty := ⟨i, hmem⟩
  unfold actualGaussValuation at h
  rw [dif_pos hne] at h
  exact le_trans h (Finset.inf'_le _ hmem)

abbrev Q2ActualResidueBlockCertificate (n p : ℕ) :=
  Q2Arithmetic.ResidueBlockCertificate n p
    (actualGaussValuation p (actualVDeterminant 2 (4 * n)))

abbrev Q2ActualOuterPoleCertificate (n p : ℕ) :=
  Q2Arithmetic.OuterPoleCertificate n p
    (actualGaussValuation p (actualVDeterminant 2 (4 * n)))

abbrev Q4ActualResidueBlockCertificate (n p : ℕ) :=
  Q4Arithmetic.ResidueBlockCertificate n p
    (actualGaussValuation p (actualVDeterminant 4 (4 * n)))

abbrev Q4ActualOuterPoleCertificate (n p : ℕ) :=
  Q4Arithmetic.OuterPoleCertificate n p
    (actualGaussValuation p (actualVDeterminant 4 (4 * n)))

abbrev Q6ActualResidueBlockCertificate (n p : ℕ) :=
  Q6Arithmetic.ResidueBlockCertificate n p
    (actualGaussValuation p (actualVDeterminant 6 (4 * n)))

abbrev Q6ActualOuterPoleCertificate (n p : ℕ) :=
  Q6Arithmetic.OuterPoleCertificate n p
    (actualGaussValuation p (actualVDeterminant 6 (4 * n)))

abbrev Q7ActualResidueBlockCertificate (n p : ℕ) :=
  Q7Arithmetic.ResidueBlockCertificate n p
    (actualGaussValuation p (actualVDeterminant 7 (4 * n)))

abbrev Q7ActualOuterPoleCertificate (n p : ℕ) :=
  Q7Arithmetic.OuterPoleCertificate n p
    (actualGaussValuation p (actualVDeterminant 7 (4 * n)))

/-- The actual q=5 determinant absolute value consumed by the smoothing input. -/
def q5ActualDeterminantAbs (m : ℕ) : ℝ :=
  |(actualVDeterminant 5 m).eval₂ (algebraMap ℚ ℝ) (li2InvValue (-5))|

def Q5ActualAnalyticCertificate : Prop :=
  Q5Certificate.Q5AnalyticBound q5ActualDeterminantAbs

def Q5ActualResidueBlockCertificate : Prop :=
  ∃ c : Q5Certificate.Q5ResidueBlockCertificate,
    c.valuation = fun m p => actualGaussValuation p (actualVDeterminant 5 m)

def Q5ActualOuterPoleCertificate : Prop :=
  ∃ c : Q5Certificate.Q5OuterPoleCertificate,
    c.valuation = fun m p => actualGaussValuation p (actualVDeterminant 5 m)

end
end V
end Li2Lean

#print axioms Li2Lean.V.actualGaussValuation_coeff
