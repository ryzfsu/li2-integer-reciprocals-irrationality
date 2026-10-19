/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B3.NonvanishingProducerWiring
import Li2Lean.B3.VActualFrobeniusAssembly

/-!
# Named source-bound Frobenius carriers

The six declarations below are the per-base obligations needed by the
construction-bound range adapter. They are deliberately stronger than finite
seed residue checks. For q = 2, `VActualFrobeniusTowerQ2Inputs` includes the
actual source-matrix and determinant representatives, the seed boundary, and
the scaled-coefficient, scaled-constant, and strict-tail fields. For q = 3..7,
`VActualFrobeniusTowerProducer` ties the seed boundary and every Frobenius
field to the actual `V.vPolynomial` and `V.vFrobeniusScaledPolynomial`.

In particular, `vSeedResidueRow_lt_prime` and any finite modular check can
discharge only part of `seed_boundary`; neither implies the source determinant
identity or any of the infinite scaled-polynomial and tail obligations.
Sources: v13 `nonvanishing.tex:146-275`.
-/

namespace Li2Lean.B3

noncomputable section

/-! ## Unified construction-bound carrier

The actual source determinant, all scaled-polynomial coefficient fields, the
constant-unit fields, and the eventual tail are one common construction
obligation. Keeping that obligation in one named proposition avoids six
independent obligations while retaining q = 2's residue interface inside
`VActualFrobeniusTowerRangeInputs`. The theorem below is the common carrier
entry point; its projections wire the six concrete fields.
-/

/-- The generic actual-source carrier for all six signed bases.

This is intentionally a `Prop`-valued theorem: its fields are the actual
`V.vPolynomial`/`V.vFrobeniusScaledPolynomial` statements and the q = 2
`Q2ActualSeedResidueInterface`, not free replacement data. Source: v13
`nonvanishing.tex:146-275`.
-/
theorem vActualFrobeniusTowerCarrier_generic :
    VActualFrobeniusTowerRangeInputs := by
  exact vActualFrobeniusTowerCarrier_assembled

/-- q = 2 source-bound carrier, including its LU/source determinant bridge. -/
theorem vActualFrobeniusTowerCarrier_q2 :
    VActualFrobeniusTowerQ2Inputs := by
  exact vActualFrobeniusTowerCarrier_generic.q2

/-- q = 3 source-bound carrier for the actual determinant and Frobenius data. -/
theorem vActualFrobeniusTowerCarrier_q3 :
    VActualFrobeniusTowerProducerQ3 := by
  exact vActualFrobeniusTowerCarrier_generic.q3

/-- q = 4 source-bound carrier for the actual determinant and Frobenius data. -/
theorem vActualFrobeniusTowerCarrier_q4 :
    VActualFrobeniusTowerProducerQ4 := by
  exact vActualFrobeniusTowerCarrier_generic.q4

/-! The finite printed seed constants are independent of the actual seed
polynomial and of the Frobenius transport.  These checks close only the
nonzero/unit leaves for q = 5, 6, 7; the equality to the actual determinant,
coefficientwise scaled integrality, and strict tail remain separate fields
of the corresponding construction-bound carriers below. -/

theorem vActualFrobeniusTowerCarrier_q5_constant_ne_zero :
    vSeedConstant 5 ≠ 0 := by
  norm_num [vSeedConstant]

theorem vActualFrobeniusTowerCarrier_q5_constant_unit :
    padicValRat (vSeedPrime 5) (vSeedConstant 5) = 0 := by
  norm_num [vSeedPrime, vSeedConstant, padicValRat]
  have hn :
      ¬(11 : ℤ) ∣ 40320536130840508931350036296875 := by
    norm_num
  have hd : ¬11 ∣ 2788079616 := by
    norm_num
  rw [padicValInt.eq_zero_of_not_dvd hn,
    padicValNat.eq_zero_of_not_dvd hd]
  norm_num

theorem vActualFrobeniusTowerCarrier_q6_constant_ne_zero :
    vSeedConstant 6 ≠ 0 := by
  norm_num [vSeedConstant]

theorem vActualFrobeniusTowerCarrier_q6_constant_unit :
    padicValRat (vSeedPrime 6) (vSeedConstant 6) = 0 := by
  norm_num [vSeedPrime, vSeedConstant, padicValRat]
  have hn :
      ¬(17 : ℤ) ∣ 376202458002139670340998058226513923 := by
    norm_num
  have hd : ¬17 ∣ 28000000000 := by
    norm_num
  rw [padicValInt.eq_zero_of_not_dvd hn,
    padicValNat.eq_zero_of_not_dvd hd]
  norm_num

theorem vActualFrobeniusTowerCarrier_q7_constant_ne_zero :
    vSeedConstant 7 ≠ 0 := by
  norm_num [vSeedConstant]

theorem vActualFrobeniusTowerCarrier_q7_constant_unit :
    padicValRat (vSeedPrime 7) (vSeedConstant 7) = 0 := by
  norm_num [vSeedPrime, vSeedConstant, padicValRat]
  have hn :
      ¬(17 : ℤ) ∣ 1824058729423489878071240450876107476590203 := by
    norm_num
  have hd : ¬17 ∣ 398580750000000 := by
    norm_num
  rw [padicValInt.eq_zero_of_not_dvd hn,
    padicValNat.eq_zero_of_not_dvd hd]
  norm_num

/-- q = 5 source-bound carrier for the actual determinant and Frobenius data. -/
theorem vActualFrobeniusTowerCarrier_q5 :
    VActualFrobeniusTowerProducerQ5 := by
  exact vActualFrobeniusTowerCarrier_generic.q5

/-- q = 6 source-bound carrier for the actual determinant and Frobenius data. -/
theorem vActualFrobeniusTowerCarrier_q6 :
    VActualFrobeniusTowerProducerQ6 := by
  exact vActualFrobeniusTowerCarrier_generic.q6

/-- q = 7 source-bound carrier for the actual determinant and Frobenius data. -/
theorem vActualFrobeniusTowerCarrier_q7 :
    VActualFrobeniusTowerProducerQ7 := by
  exact vActualFrobeniusTowerCarrier_generic.q7

/-- Assemble the six named source-bound carriers without weakening any field. -/
theorem vActualFrobeniusTowerRangeCarrier :
    VActualFrobeniusTowerRangeInputs :=
  { q2 := vActualFrobeniusTowerCarrier_q2
    q3 := vActualFrobeniusTowerCarrier_q3
    q4 := vActualFrobeniusTowerCarrier_q4
    q5 := vActualFrobeniusTowerCarrier_q5
    q6 := vActualFrobeniusTowerCarrier_q6
    q7 := vActualFrobeniusTowerCarrier_q7 }

/-- Expose the fixed-prime producer bundle consumed by the range theorem. -/
theorem vActualFrobeniusTowerProducers_of_carriers :
    VActualFrobeniusTowerProducers :=
  vActualFrobeniusTowerRangeCarrier.toProducers

end
end Li2Lean.B3

#print axioms Li2Lean.B3.vActualFrobeniusTowerRangeCarrier
#print axioms Li2Lean.B3.vActualFrobeniusTowerProducers_of_carriers
