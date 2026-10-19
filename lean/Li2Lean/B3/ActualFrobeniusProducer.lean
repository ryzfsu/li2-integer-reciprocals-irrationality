/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/

import Mathlib
import Li2Lean.B3.ProducerInterfaces
import Li2Lean.V.NonvanishingPlan

/-!
# Construction-bound signed V Frobenius producer

This is the B3 boundary for the six negative bases.  The auxiliary prime is
fixed to the paper's `vSeedPrime q`; no arbitrary valuation, determinant, or
polynomial may be supplied by a consumer.  The fields below are intentionally
the remaining v13 obligations rather than unconditional claims:

* `nonvanishing.tex:146-198`: seed constant and its p-adic unit;
* `nonvanishing.tex:200-258`: coefficientwise integrality of
  `Q^(13 Q) G_(4 Q,-q)(X / Q^2)` and its constant unit;
* `nonvanishing.tex:262-275`: the strict p-adic tail estimate at each fixed
  rational evaluation point.

The generic arithmetic and evaluation lemmas live in
`Li2Lean.V.NonvanishingPlan`.  This module only pins their parameters to the
actual B3 construction and supplies the prime from `vSeedPrime_spec`.
-/

namespace Li2Lean

noncomputable section

namespace B3

open scoped BigOperators

/-! ## The pinned 9 by 9 seed constants -/

/-- Exact constant coefficients of the six actual 9 by 9 seed determinants.
These values are the rational output of the v13 LU reductions
(`nonvanishing.tex:146-198`); they are data, not a claim that the reductions
have already been proved in Lean. -/
def vSeedConstant : ℕ → ℚ
  | 2 => 158649262379640306631463 / 2333772000000000
  | 3 => 1039022569605470806780631811 / 9604000000000
  | 4 => 62660750921815779182464026763528 / 16747366663125
  | 5 => 40320536130840508931350036296875 / 2788079616
  | 6 => 376202458002139670340998058226513923 / 28000000000
  | 7 => 1824058729423489878071240450876107476590203 / 398580750000000
  | _ => 0

/-- The five coefficient residues printed by the six 9 by 9 LU reductions.
The entries are ascending powers of `T`, and are deliberately represented as
natural numbers so each row can be checked by a small `decide` certificate.
Source: `nonvanishing.tex:179-198`. -/
def vSeedResidueRow : ℕ → Fin 5 → ℕ
  | 2, ⟨0, _⟩ => 4 | 2, ⟨1, _⟩ => 2 | 2, ⟨2, _⟩ => 7
  | 2, ⟨3, _⟩ => 3 | 2, ⟨4, _⟩ => 9
  | 3, ⟨0, _⟩ => 1 | 3, ⟨1, _⟩ => 4 | 3, ⟨2, _⟩ => 6
  | 3, ⟨3, _⟩ => 7 | 3, ⟨4, _⟩ => 1
  | 4, ⟨0, _⟩ => 5 | 4, ⟨1, _⟩ => 8 | 4, ⟨2, _⟩ => 16
  | 4, ⟨3, _⟩ => 21 | 4, ⟨4, _⟩ => 20
  | 5, ⟨0, _⟩ => 5 | 5, ⟨1, _⟩ => 2 | 5, ⟨2, _⟩ => 5
  | 5, ⟨3, _⟩ => 8 | 5, ⟨4, _⟩ => 7
  | 6, ⟨0, _⟩ => 5 | 6, ⟨1, _⟩ => 12 | 6, ⟨2, _⟩ => 4
  | 6, ⟨3, _⟩ => 7 | 6, ⟨4, _⟩ => 4
  | 7, ⟨0, _⟩ => 8 | 7, ⟨1, _⟩ => 0 | 7, ⟨2, _⟩ => 8
  | 7, ⟨3, _⟩ => 16 | 7, ⟨4, _⟩ => 5
  | _, _ => 0

/-- Reduction of a rational coefficient at the paper prime.  The coprimality
of the denominator is an explicit seed-boundary field below. -/
def vSeedCoeffResidue (q i : ℕ) : ZMod (vSeedPrime q) :=
  let r := (V.vPolynomial 1 (-(q : ℤ))).coeff i
  (r.num : ZMod (vSeedPrime q)) * ((r.den : ZMod (vSeedPrime q))⁻¹)

/-- Exact finite seed/LU boundary for the actual determinant.  This is an
interface, not a proved theorem: the `row_residue` and denominator fields are
the six finite Boolean obligations left by the 9 by 9 reductions. -/
structure VActualSeedBoundary (q : ℕ) (hq : SignedVBaseRange q) : Prop where
  denominator_coprime :
    ∀ i : Fin 5,
      Nat.Coprime (vSeedPrime q)
        ((V.vPolynomial 1 (-(q : ℤ))).coeff i).den
  row_residue :
    ∀ i : Fin 5,
      vSeedCoeffResidue q i.val =
        (vSeedResidueRow q i : ZMod (vSeedPrime q))
  constant_eq :
    (V.vPolynomial 1 (-(q : ℤ))).coeff 0 = vSeedConstant q
  constant_ne_zero : vSeedConstant q ≠ 0
  constant_unit : padicValRat (vSeedPrime q) (vSeedConstant q) = 0

/-- Small integer range check for the printed residue rows.  This is the
Boolean part of the finite seed certificate; all entries are represented by
natural integers before their `ZMod` cast. -/
theorem vSeedResidueRow_lt_prime {q : ℕ} (hq : SignedVBaseRange q) :
    ∀ i : Fin 5, vSeedResidueRow q i < vSeedPrime q := by
  intro i
  obtain ⟨hq2, hq7⟩ := hq
  interval_cases q <;> fin_cases i <;> decide

/-! ## The fixed-prime interface -/

/-- The actual Frobenius tower at the paper prime for a signed base.
Source: `nonvanishing.tex:146-275`. -/
abbrev VActualFrobeniusTowerAtSeed (q : ℕ) : Prop :=
  V.VActualFrobeniusTower q (vSeedPrime q)

/-- Explicit producer fields for the construction-bound tower.

All occurrences of the determinant are the actual `V.vPolynomial`; the
scaled polynomial is the v13 object `Q^(13 Q) G_(4Q,-q)(X/Q^2)` from
`vFrobeniusScaledPolynomial`.  The fields are left explicit so a downstream
producer cannot discharge the obligation by choosing a free `vp`, a different
determinant, or a finite seed only. -/
structure VActualFrobeniusTowerProducer
    (q : ℕ) (hq : SignedVBaseRange q) : Prop where
  seed_boundary : VActualSeedBoundary q hq
  /-- The 9 by 9 LU result, tied to the actual determinant coefficient. -/
  scaled_coefficients_integral :
    ∀ k : ℕ, 0 < k → ∀ i : ℕ,
      (V.vFrobeniusScaledPolynomial q (vSeedPrime q) k).coeff i ≠ 0 →
        0 ≤ padicValRat (vSeedPrime q)
          ((V.vFrobeniusScaledPolynomial q (vSeedPrime q) k).coeff i)
  scaled_constant_unit :
    ∀ k : ℕ, 0 < k →
      (V.vFrobeniusScaledPolynomial q (vSeedPrime q) k).coeff 0 ≠ 0 ∧
        padicValRat (vSeedPrime q)
          ((V.vFrobeniusScaledPolynomial q (vSeedPrime q) k).coeff 0) = 0
  strict_tail :
    ∀ r : ℚ, ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      V.VUnitConstantEvaluationInput q (vSeedPrime q) k
        (((vSeedPrime q ^ k : ℕ) : ℚ) ^ 2 * r)

/-- Package the explicit fields into the generic tower used by the
nonvanishing criterion.  The only inferred field is primality of the fixed
paper prime, supplied by `vSeedPrime_spec hq`. -/
theorem VActualFrobeniusTowerProducer.toTower
    {q : ℕ} {hq : SignedVBaseRange q}
    (p : VActualFrobeniusTowerProducer q hq) :
    VActualFrobeniusTowerAtSeed q := by
  have hp : Nat.Prime (vSeedPrime q) := (vSeedPrime_spec hq).1
  have hseed_ne : (V.vPolynomial 1 (-(q : ℤ))).coeff 0 ≠ 0 := by
    rw [p.seed_boundary.constant_eq]
    exact p.seed_boundary.constant_ne_zero
  have hseed_unit :
      padicValRat (vSeedPrime q)
        ((V.vPolynomial 1 (-(q : ℤ))).coeff 0) = 0 := by
    rw [p.seed_boundary.constant_eq]
    exact p.seed_boundary.constant_unit
  exact
    { prime := hp
      seed_constant_ne_zero := hseed_ne
      seed_constant_unit := hseed_unit
      scaled_coefficients_integral := p.scaled_coefficients_integral
      scaled_constant_unit := p.scaled_constant_unit
      unit_input := p.strict_tail }

/-- The construction-bound producer gives eventual nonvanishing at the exact
indices `vSeedPrime q ^ k`, hence at `m = 4 * vSeedPrime q ^ k` in the real
endpoint interface.  Source: `nonvanishing.tex:262-275`. -/
theorem eventualNonvanishing_of_VActualFrobeniusTowerProducer
    {q : ℕ} {hq : SignedVBaseRange q}
    (p : VActualFrobeniusTowerProducer q hq) :
    VEventualNonvanishing q (vSeedPrime q) := by
  apply vEventualNonvanishing_of_rat
  intro r
  exact V.vActualEventualNonvanishing_of_frobenius_tower p.toTower r

/-! The regression target remains the unchanged `a = 2` family.  This is a
parameter pinning theorem only; it does not assert a new nonvanishing result.
-/
theorem VActualFrobeniusTowerProducer.two_regression
    {hq : SignedVBaseRange 2}
    (p : VActualFrobeniusTowerProducer 2 hq) :
    V.VActualFrobeniusTower 2 (vSeedPrime 2) :=
  p.toTower

end B3

end

end Li2Lean

#print axioms Li2Lean.B3.VActualFrobeniusTowerProducer.toTower
#print axioms Li2Lean.B3.eventualNonvanishing_of_VActualFrobeniusTowerProducer
