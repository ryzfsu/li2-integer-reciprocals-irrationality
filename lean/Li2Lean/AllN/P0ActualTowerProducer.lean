/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/

import Li2Lean.P0.Nonvanishing
import Li2Lean.P0.PositiveBaseParam
import Li2Lean.P0.Q11TowerArithmetic

/-!
# Construction-bound P0 Frobenius tower interface

This file fixes the actual positive-base family and the auxiliary primes printed
for the v13 interpolation.  It does not claim the seed or Frobenius congruence:
those are the finite arithmetic obligations in `P0ActualTowerProducer.tower`.
The wrapper prevents a consumer from choosing an unrelated family, index, or
prime while the q-specific seed calculations are completed.

Sources: v13 `nonvanishing.tex:82-145` (seed and auxiliary primes) and
`nonvanishing.tex:200-258` (scaled Frobenius pencil).  The existing `a = 2`
route remains in `P0.NonvanishingScaledLucas` with `M = 32`, `p = 83`.
-/

namespace Li2Lean
namespace AllNAssembly

open Li2Lean.P0.PositiveBase

noncomputable section

/-! ## The fixed v13 auxiliary-prime table -/

/-- Auxiliary primes from v13 `nonvanishing.tex:128-145`, for q = 3,...,11.
The q=2 entry is retained as the frozen a=2 regression prime. -/
def p0ActualTowerPrime : ℕ → ℕ
  | 2 => 83
  | 3 => 17
  | 4 => 53
  | 5 => 11
  | 6 => 13
  | 7 => 11
  | 8 => 247229
  | 9 => 41
  | 10 => 59
  | 11 => 197
  | _ => 0

theorem p0ActualTowerPrime_spec {q : ℕ}
    (hq2 : 3 ≤ q) (hq11 : q ≤ 11) :
    Nat.Prime (p0ActualTowerPrime q) ∧
      2 * 4 + 4 / 2 < p0ActualTowerPrime q := by
  interval_cases q <;> norm_num [p0ActualTowerPrime]

/-- Every q>=3 tower uses the v13 seed index M=4. -/
def p0ActualTowerIndex : ℕ := 4

theorem p0ActualTowerIndex_spec :
    0 < p0ActualTowerIndex ∧ 4 ∣ p0ActualTowerIndex := by
  norm_num [p0ActualTowerIndex]

/-! ## The actual-family certificate boundary -/

/-- The q-specific certificate is tied to the actual `family q hq`, M=4, and
the printed `p0ActualTowerPrime q`.  All seed/Frobenius fields below are the
remaining v13 obligations; no arbitrary valuation or determinant is exposed.
Sources: `nonvanishing.tex:82-145,200-258`. -/
structure P0ActualTowerProducer
    (q : ℕ) (hq : InRange (q : ℤ)) (hq3 : 3 ≤ q) (hq11 : q ≤ 11) : Type where
  tower : P0FrobeniusTowerCertificate
    (family (q : ℤ) hq) p0ActualTowerIndex (p0ActualTowerPrime q)

/-- The fixed producer supplies the original existential p0Tower obligation.
This is pure packaging; it does not discharge the certificate fields. -/
theorem P0ActualTowerProducer.to_p0Tower
    {q : ℕ} {hq : InRange (q : ℤ)} {hq3 : 3 ≤ q} {hq11 : q ≤ 11}
    (P : P0ActualTowerProducer q hq hq3 hq11) :
    ∃ M p : ℕ,
      Nonempty (P0FrobeniusTowerCertificate (family (q : ℤ) hq) M p) := by
  exact ⟨p0ActualTowerIndex, p0ActualTowerPrime q, ⟨P.tower⟩⟩

/-- Universal input package needed to replace `AllNAssembly.p0Tower_producer`.
Each field remains construction-bound to the v13 family and prime table. -/
def P0ActualTowerInputs : Prop :=
  ∀ (q : ℕ) (hq : InRange (q : ℤ))
    (hq3 : 3 ≤ q) (hq11 : q ≤ 11),
    Nonempty (P0ActualTowerProducer q hq hq3 hq11)

theorem p0Tower_of_actual_inputs (H : P0ActualTowerInputs) :
    ∀ (q : ℕ) (hq : InRange (q : ℤ)), 3 ≤ q →
      ∃ M p : ℕ,
        Nonempty (P0FrobeniusTowerCertificate (family (q : ℤ) hq) M p) := by
  intro q hq hq3
  have hq11 : q ≤ 11 := by
    exact_mod_cast hq.2
  obtain ⟨P⟩ := H q hq hq3 hq11
  exact P.to_p0Tower

/-! The unchanged q=2 route remains the regression target.  Its frozen
certificate uses M=32, p=83 in `P0A2FrobeniusTowerCertificate`; the generalized
q>=3 interface above intentionally does not overwrite that route. -/
theorem p0ActualTowerPrime_two_regression :
    p0ActualTowerPrime 2 = 83 := by
  rfl

end
end AllNAssembly
end Li2Lean

#print axioms Li2Lean.AllNAssembly.P0ActualTowerProducer.to_p0Tower
#print axioms Li2Lean.AllNAssembly.p0Tower_of_actual_inputs
