/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/

import Li2Lean.AllN.P0ActualTowerProducer

/-!
# Honest q-case assembly for the positive P0 tower

This module contains only the finite case split.  Each input is an actual
`P0FrobeniusTowerCertificate` for the fixed v13 family, index, and auxiliary
prime.  The module does not create those certificates from finite residue
tables; the seed transport and all-level Frobenius proofs remain explicit
inputs.
-/

namespace Li2Lean.AllNAssembly

open Li2Lean.P0.PositiveBase

noncomputable section

structure P0TowerCaseInputs : Prop where
  q3 : ∀ hq : InRange (3 : ℤ),
    Nonempty (P0FrobeniusTowerCertificate (family (3 : ℤ) hq) 4 17)
  q4 : ∀ hq : InRange (4 : ℤ),
    Nonempty (P0FrobeniusTowerCertificate (family (4 : ℤ) hq) 4 53)
  q5 : ∀ hq : InRange (5 : ℤ),
    Nonempty (P0FrobeniusTowerCertificate (family (5 : ℤ) hq) 4 11)
  q6 : ∀ hq : InRange (6 : ℤ),
    Nonempty (P0FrobeniusTowerCertificate (family (6 : ℤ) hq) 4 13)
  q7 : ∀ hq : InRange (7 : ℤ),
    Nonempty (P0FrobeniusTowerCertificate (family (7 : ℤ) hq) 4 11)
  q8 : ∀ hq : InRange (8 : ℤ),
    Nonempty (P0FrobeniusTowerCertificate (family (8 : ℤ) hq) 4 247229)
  q9 : ∀ hq : InRange (9 : ℤ),
    Nonempty (P0FrobeniusTowerCertificate (family (9 : ℤ) hq) 4 41)
  q10 : ∀ hq : InRange (10 : ℤ),
    Nonempty (P0FrobeniusTowerCertificate (family (10 : ℤ) hq) 4 59)
  q11 : ∀ hq : InRange (11 : ℤ),
    Nonempty (P0FrobeniusTowerCertificate (family (11 : ℤ) hq) 4 197)

theorem p0Tower_producer_of_case_inputs (H : P0TowerCaseInputs) :
    ∀ (q : ℕ) (hq : InRange (q : ℤ)), 3 ≤ q →
      ∃ M p : ℕ,
        Nonempty (P0FrobeniusTowerCertificate (family (q : ℤ) hq) M p) := by
  intro q hq hq3
  have hq11 : q ≤ 11 := by
    have hrange := hq
    simp [InRange] at hrange
    omega
  interval_cases q
  · exact ⟨4, 17, H.q3 hq⟩
  · exact ⟨4, 53, H.q4 hq⟩
  · exact ⟨4, 11, H.q5 hq⟩
  · exact ⟨4, 13, H.q6 hq⟩
  · exact ⟨4, 11, H.q7 hq⟩
  · exact ⟨4, 247229, H.q8 hq⟩
  · exact ⟨4, 41, H.q9 hq⟩
  · exact ⟨4, 59, H.q10 hq⟩
  · exact ⟨4, 197, H.q11 hq⟩

end
end Li2Lean.AllNAssembly

#print axioms Li2Lean.AllNAssembly.p0Tower_producer_of_case_inputs
