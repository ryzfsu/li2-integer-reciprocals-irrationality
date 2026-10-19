/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.AllN.ProducerAssembly

namespace Li2Lean.AllNAssembly

noncomputable section

open Li2Lean.P0.PositiveBase

/-!
The B0 gate is the only constructor used by the all-n consumer.  Its ten
arguments are the construction-bound producer obligations; in particular,
none of them is an irrationality conclusion, a free endpoint certificate, or
an unconstrained affine-form witness.  Keeping the arguments explicit makes a
missing producer fail at the interface instead of becoming a field with an
unrelated type.
-/

def AllNProducers.ofNamed
    (p0Profile : P0PositiveEnergyProfile)
    (p0Rate : ℕ → ℝ)
    (p0Integerizer : ∀ (q : ℕ) (hq : InRange (q : ℤ)), 3 ≤ q →
      P0IntegerizerBoundAt (family (q : ℤ) hq) (p0Rate q))
    (p0RateMargin : ∀ q : ℕ, 3 ≤ q → q ≤ 11 →
      p0Rate q < p0PositiveChord q)
    (p0Tower : ∀ (q : ℕ) (hq : InRange (q : ℤ)), 3 ≤ q →
      ∃ M p : ℕ,
        Nonempty (P0FrobeniusTowerCertificate (family (q : ℤ) hq) M p))
    (vInputs : ∀ q : ℕ, 2 ≤ q → q ≤ 7 → SignedVEndpointInputs q)
    (hpIntegral : ∀ a : ℤ,
      ((12 : ℤ) ≤ a ∨ a ≤ -8) → HPIntegralForm a)
    (hpDecayPos : ∀ a : ℤ, (12 : ℤ) ≤ a → HPDecay a)
    (hpDecayNeg : ∀ a : ℤ, a ≤ (-8 : ℤ) → HPDecay a)
    (hpNoAdj : ∀ a : ℤ,
      ((12 : ℤ) ≤ a ∨ a ≤ -8) → HPNoAdjacentZero a) :
    AllNProducers :=
  { p0Profile := p0Profile
    p0Rate := p0Rate
    p0Integerizer := p0Integerizer
    p0RateMargin := p0RateMargin
    p0Tower := p0Tower
    vInputs := vInputs
    hpIntegral := hpIntegral
    hpDecayPos := hpDecayPos
    hpDecayNeg := hpDecayNeg
    hpNoAdj := hpNoAdj }

/-- The all-n statement follows only after all ten named producers are supplied. -/
theorem li2_inv_irrational_statement_of_named_producers
    (p0Profile : P0PositiveEnergyProfile)
    (p0Rate : ℕ → ℝ)
    (p0Integerizer : ∀ (q : ℕ) (hq : InRange (q : ℤ)), 3 ≤ q →
      P0IntegerizerBoundAt (family (q : ℤ) hq) (p0Rate q))
    (p0RateMargin : ∀ q : ℕ, 3 ≤ q → q ≤ 11 →
      p0Rate q < p0PositiveChord q)
    (p0Tower : ∀ (q : ℕ) (hq : InRange (q : ℤ)), 3 ≤ q →
      ∃ M p : ℕ,
        Nonempty (P0FrobeniusTowerCertificate (family (q : ℤ) hq) M p))
    (vInputs : ∀ q : ℕ, 2 ≤ q → q ≤ 7 → SignedVEndpointInputs q)
    (hpIntegral : ∀ a : ℤ,
      ((12 : ℤ) ≤ a ∨ a ≤ -8) → HPIntegralForm a)
    (hpDecayPos : ∀ a : ℤ, (12 : ℤ) ≤ a → HPDecay a)
    (hpDecayNeg : ∀ a : ℤ, a ≤ (-8 : ℤ) → HPDecay a)
    (hpNoAdj : ∀ a : ℤ,
      ((12 : ℤ) ≤ a ∨ a ≤ -8) → HPNoAdjacentZero a) :
    li2InvIrrationalStatement :=
  li2_inv_irrational_of_producers
    (AllNProducers.ofNamed p0Profile p0Rate p0Integerizer p0RateMargin
      p0Tower vInputs hpIntegral hpDecayPos hpDecayNeg hpNoAdj)

/-- Pointwise Challenge/Solution-shaped consumer for the same ten producers. -/
theorem li2_inv_irrational_of_named_producers
    (p0Profile : P0PositiveEnergyProfile)
    (p0Rate : ℕ → ℝ)
    (p0Integerizer : ∀ (q : ℕ) (hq : InRange (q : ℤ)), 3 ≤ q →
      P0IntegerizerBoundAt (family (q : ℤ) hq) (p0Rate q))
    (p0RateMargin : ∀ q : ℕ, 3 ≤ q → q ≤ 11 →
      p0Rate q < p0PositiveChord q)
    (p0Tower : ∀ (q : ℕ) (hq : InRange (q : ℤ)), 3 ≤ q →
      ∃ M p : ℕ,
        Nonempty (P0FrobeniusTowerCertificate (family (q : ℤ) hq) M p))
    (vInputs : ∀ q : ℕ, 2 ≤ q → q ≤ 7 → SignedVEndpointInputs q)
    (hpIntegral : ∀ a : ℤ,
      ((12 : ℤ) ≤ a ∨ a ≤ -8) → HPIntegralForm a)
    (hpDecayPos : ∀ a : ℤ, (12 : ℤ) ≤ a → HPDecay a)
    (hpDecayNeg : ∀ a : ℤ, a ≤ (-8 : ℤ) → HPDecay a)
    (hpNoAdj : ∀ a : ℤ,
      ((12 : ℤ) ≤ a ∨ a ≤ -8) → HPNoAdjacentZero a)
    (n : ℤ) (hn : n ≠ 0) :
    Irrational (∑' k : ℕ,
      ((n : ℝ)⁻¹) ^ (k + 1) / ((k : ℝ) + 1) ^ 2) :=
  li2_inv_irrational_of_producers'
    (AllNProducers.ofNamed p0Profile p0Rate p0Integerizer p0RateMargin
      p0Tower vInputs hpIntegral hpDecayPos hpDecayNeg hpNoAdj) n hn

end

end Li2Lean.AllNAssembly
