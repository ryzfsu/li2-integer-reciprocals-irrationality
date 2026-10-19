/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B3.ActualFrobeniusProducer

/-!
# q = 2, 3, 4 seed constant leaves

These are the finite constant-nezero and p-adic-unit leaves for the actual
`vSeedConstant` data.  They reuse the definitions in
`B3/ActualFrobeniusProducer.lean`; they do not assert the determinant or
coefficient identities needed by the full Frobenius carrier.
Source: v13 `nonvanishing.tex:146-198`.
-/

namespace Li2Lean.B3

noncomputable section

theorem vActualFrobeniusTowerCarrier_q2_constant_ne_zero :
    vSeedConstant 2 ≠ 0 := by
  norm_num [vSeedConstant]

theorem vActualFrobeniusTowerCarrier_q2_constant_unit :
    padicValRat (vSeedPrime 2) (vSeedConstant 2) = 0 := by
  norm_num [vSeedPrime, vSeedConstant, padicValRat]
  have hn : ¬(11 : ℤ) ∣ 158649262379640306631463 := by
    norm_num
  have hd : ¬11 ∣ 2333772000000000 := by
    norm_num
  rw [padicValInt.eq_zero_of_not_dvd hn,
    padicValNat.eq_zero_of_not_dvd hd]
  norm_num

theorem vActualFrobeniusTowerCarrier_q3_constant_ne_zero :
    vSeedConstant 3 ≠ 0 := by
  norm_num [vSeedConstant]

theorem vActualFrobeniusTowerCarrier_q3_constant_unit :
    padicValRat (vSeedPrime 3) (vSeedConstant 3) = 0 := by
  norm_num [vSeedPrime, vSeedConstant, padicValRat]
  have hn : ¬(11 : ℤ) ∣ 1039022569605470806780631811 := by
    norm_num
  have hd : ¬11 ∣ 9604000000000 := by
    norm_num
  rw [padicValInt.eq_zero_of_not_dvd hn,
    padicValNat.eq_zero_of_not_dvd hd]
  norm_num

theorem vActualFrobeniusTowerCarrier_q4_constant_ne_zero :
    vSeedConstant 4 ≠ 0 := by
  norm_num [vSeedConstant]

theorem vActualFrobeniusTowerCarrier_q4_constant_unit :
    padicValRat (vSeedPrime 4) (vSeedConstant 4) = 0 := by
  norm_num [vSeedPrime, vSeedConstant, padicValRat]
  have hn : ¬(23 : ℤ) ∣ 62660750921815779182464026763528 := by
    norm_num
  have hd : ¬23 ∣ 16747366663125 := by
    norm_num
  rw [padicValInt.eq_zero_of_not_dvd hn,
    padicValNat.eq_zero_of_not_dvd hd]
  norm_num

end
end Li2Lean.B3

#print axioms Li2Lean.B3.vActualFrobeniusTowerCarrier_q2_constant_unit
#print axioms Li2Lean.B3.vActualFrobeniusTowerCarrier_q3_constant_unit
#print axioms Li2Lean.B3.vActualFrobeniusTowerCarrier_q4_constant_unit
