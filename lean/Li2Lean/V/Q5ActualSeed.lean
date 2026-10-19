/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/

import Mathlib
import Li2Lean.Statement
import Li2Lean.V.VFamily
import Li2Lean.V.Q5Certificate
import Li2Lean.B3.ArithmeticPinning

/-!
Typed q=5 seed interface for the signed V determinant.

The determinant is fixed to the v13 family `V.vPolynomial 1 (-5)`; no
determinant, valuation, or residue polynomial is supplied as a free field.
The finite residue and denominator checks remain explicit producer fields so
the seed theorem cannot be proved by choosing an unrelated polynomial.

Source: `nonvanishing.tex:159-198,200-275`; determinant family:
`v-arithmetic.tex:13-35`.
-/

namespace Li2Lean
namespace V
namespace Q5ActualSeed

noncomputable section

def base : ℤ := -5
def index : ℕ := 1
def prime : ℕ := 11

/-- The actual q=5 seed determinant, v13 `v-arithmetic.tex:32`. -/
noncomputable def determinant : Polynomial ℚ :=
  V.vPolynomial index base

theorem determinant_eq_vPolynomial :
    determinant = V.vPolynomial 1 (-5 : ℤ) := by
  rfl

/-- The constant coefficient used by the n=1 seed, v13 `nonvanishing.tex:185-198`. -/
noncomputable def constant : ℚ := determinant.eval 0

/-- Reduction of a rational whose denominator is prime to 11.  The
coprimality condition is carried by `Q5ActualSeedReceipt`. -/
noncomputable def residueOfRat (r : ℚ) : ZMod prime :=
  (r.num : ZMod prime) * ((r.den : ZMod prime)⁻¹)

def constantResidue : ZMod prime := residueOfRat constant

theorem prime_spec : Nat.Prime prime := by
  norm_num [prime]

theorem expected_residue_matches_q5_certificate :
    (5 : ZMod prime) = Q5Certificate.q5SeedConstant := by
  change (5 : ZMod 11) = Q5Certificate.q5SeedConstant
  exact Q5Certificate.q5_seed_constant_residue.symm

/-!
The receipt has only propositions as fields.  Its determinant is the fixed
definition above, so this is a typed proof obligation for the actual v13
object, rather than a structure that can replace it with arbitrary data.
-/
structure Receipt : Prop where
  determinant_is_vPolynomial :
    determinant = V.vPolynomial 1 (-5 : ℤ)
  denominator_coprime : Nat.Coprime constant.den prime
  residue_eq_expected : constantResidue = (5 : ZMod prime)

theorem receipt_determinant_eq (r : Receipt) :
    determinant = V.vPolynomial 1 (-5 : ℤ) :=
  r.determinant_is_vPolynomial

theorem residue_nonzero_of_receipt (r : Receipt) :
    constantResidue ≠ 0 := by
  rw [r.residue_eq_expected]
  decide

theorem residue_matches_q5_seed_constant (r : Receipt) :
    constantResidue = Q5Certificate.q5SeedConstant := by
  rw [r.residue_eq_expected]
  exact expected_residue_matches_q5_certificate

/-! A concrete adapter for the q=5 residue and outer-pole contracts.  The
valuation is the Gauss valuation of the same actual determinant for every
`m`, as required by `v-arithmetic.tex:128-351`. -/
def gaussValuation (m p : ℕ) : ℤ :=
  V.actualGaussValuation p (V.actualVDeterminant 5 m)

def ResidueBlockCertificate : Prop :=
  ∃ c : Q5Certificate.Q5ResidueBlockCertificate,
    c.valuation = fun m p => gaussValuation m p

def OuterPoleCertificate : Prop :=
  ∃ c : Q5Certificate.Q5OuterPoleCertificate,
    c.valuation = fun m p => gaussValuation m p

theorem residue_bound_of_actual_certificate
    {c : Q5Certificate.Q5ResidueBlockCertificate}
    (hc : c.valuation = fun m p => gaussValuation m p) :
    Q5Certificate.Q5ResidueBlockBound (fun m p => gaussValuation m p) := by
  rw [← hc]
  exact c.bound

theorem outer_bound_of_actual_certificate
    {c : Q5Certificate.Q5OuterPoleCertificate}
    (hc : c.valuation = fun m p => gaussValuation m p) :
    Q5Certificate.Q5OuterPoleBound (fun m p => gaussValuation m p) := by
  rw [← hc]
  exact c.bound

theorem actual_gauss_valuation_coeff {m p : ℕ} {E : ℤ}
    (h : gaussValuation m p ≥ -E) :
    ∀ i : ℕ, (V.actualVDeterminant 5 m).coeff i ≠ 0 →
      -E ≤ padicValRat p ((V.actualVDeterminant 5 m).coeff i) := by
  exact V.actualGaussValuation_coeff h

end
end Q5ActualSeed
end V
end Li2Lean

#print axioms Li2Lean.V.Q5ActualSeed.residue_nonzero_of_receipt
#print axioms Li2Lean.V.Q5ActualSeed.actual_gauss_valuation_coeff

