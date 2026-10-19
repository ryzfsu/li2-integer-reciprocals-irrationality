/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Li2Lean.P0.PositiveTower.SeedArgument

/-!
# Seed transport from an explicit nonzero finite-place residue

This is the finite-place part of the v13 seed argument.  A concrete source
residue calculation supplies only `ratResidueOf_ne_zero`; the theorem below
turns that fact into the reduced-rational seed and its eventual prime-square
transport.  The all-level Frobenius field remains a separate obligation.

Source: v13 `nonvanishing.tex:70-145,200-258`.
-/

namespace Li2Lean.P0.PositiveTower

noncomputable section

open Li2Lean
open Li2Lean.P0

/-- The numerator/denominator residue used by the finite q tables. -/
def ratResidueOf (p : ℕ) (x : ℚ) : ZMod p :=
  (x.num : ZMod p) * (x.den : ZMod p)⁻¹

lemma coprime_of_ratResidueOf_ne_zero
    {p : ℕ} [hp : Fact (Nat.Prime p)] {x : ℚ}
    (hx : ratResidueOf p x ≠ 0) :
    Nat.Coprime x.den p := by
  apply Nat.Coprime.symm
  apply (hp.out.coprime_iff_not_dvd).2
  intro hd
  apply hx
  unfold ratResidueOf
  have hzero : (x.den : ZMod p) = 0 := by
    have hzeroInt : ((x.den : ℤ) : ZMod p) = 0 := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd (x.den : ℤ) p).2
      exact_mod_cast hd
    simpa using hzeroInt
  rw [hzero, inv_zero, mul_zero]

/-!
The exact seed fields needed by `P0FrobeniusTowerCertificate`, except for the
all-level Frobenius field.  This theorem is deliberately a boundary lemma:
it does not turn a finite residue table into a Frobenius certificate.
-/
theorem seed_argument_of_ratResidueOf_ne_zero
    {F : P0Family} {M p : ℕ} [hp : Fact (Nat.Prime p)]
    (hM : 4 ∣ M) (hcut : 2 * M + M / 2 < p)
    (hunit : ¬ (p : ℤ) ∣ F.a * (F.a - 1))
    (hres : ratResidueOf p (p0SourceEvalQ F M 0) ≠ 0) :
    ∃ seed : ContourKit.ReducedRational p,
      seed.value = p0SourceEvalQ F M 0 ∧
      seed.residue ≠ 0 ∧
      (∀ r : ℚ, ∃ k₀, ∀ k, k₀ ≤ k →
        ∃ s : ContourKit.ReducedRational p,
          s.value = p0SourceEvalQ F M ((p ^ k : ℕ) ^ 2 * r) ∧
          s.residue = seed.residue) := by
  have hcop : Nat.Coprime (p0SourceEvalQ F M 0).den p :=
    coprime_of_ratResidueOf_ne_zero hres
  let seed := reducedOfP p (p0SourceEvalQ F M 0) hcop
  refine ⟨seed, rfl, ?_, ?_⟩
  · rw [reducedOfP_residue]
    change ((p0SourceEvalQ F M 0).num : ZMod p) *
      ((p0SourceEvalQ F M 0).den : ZMod p)⁻¹ ≠ 0
    exact hres
  · exact seed_argument_of_seed_value hM hcut hunit seed rfl

end
end Li2Lean.P0.PositiveTower

#print axioms Li2Lean.P0.PositiveTower.seed_argument_of_ratResidueOf_ne_zero
