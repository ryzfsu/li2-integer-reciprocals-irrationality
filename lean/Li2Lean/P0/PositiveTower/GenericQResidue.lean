/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Li2Lean.P0.PositiveTower.EntryGoodness

namespace Li2Lean.P0.PositiveTower

noncomputable section

open Li2Lean

variable {p : ℕ} [Fact (Nat.Prime p)]

/-!
The base-dependent `Q_s(a)` residue is the generic form of the already
proved q = 2 residue formula.  The unit hypothesis is exactly the finite-place
condition from v13 nonvanishing.tex:11-145; denominator reduction is handled
by the existing `GoodP` subring and residue homomorphism.
-/
theorem p0Q_residue_formula (a : ℤ) (s : ℕ)
    (hunit : ¬ (p : ℤ) ∣ a * (a - 1)) :
    ((p0Q (a : ℚ) s : ℚ) : ZMod p) =
      ((a : ZMod p) * (((a - 1 : ℤ) : ZMod p)⁻¹)) ^ s - 1 := by
  have hA : (a : ℚ) ∈ GoodP p := by
    exact EntryGoodness.intRat_good a
  have hAm1 : ((a - 1 : ℤ) : ℚ) ∈ GoodP p := by
    exact EntryGoodness.intRat_good (a - 1)
  have hunitA : ¬ (p : ℤ) ∣ a := by
    intro hpA
    apply hunit
    exact dvd_mul_of_dvd_left hpA (a - 1)
  have hunitAm1 : ¬ (p : ℤ) ∣ a - 1 := by
    intro hpA
    apply hunit
    exact dvd_mul_of_dvd_right hpA a
  have hAm1ne : ((a - 1 : ℤ) : ZMod p) ≠ 0 := by
    intro hz
    apply hunitAm1
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (a - 1) p).mp hz
  have hInv : (((a - 1 : ℤ) : ℚ)⁻¹) ∈ GoodP p := by
    change Nat.Coprime (((a - 1 : ℤ) : ℚ)⁻¹).den p
    rw [Rat.inv_intCast_den]
    split_ifs
    · simp
    · apply Nat.Coprime.symm
      apply (Fact.out : Nat.Prime p).coprime_iff_not_dvd.2
      intro hdiv
      apply hunitAm1
      apply Int.dvd_natAbs.mp
      exact_mod_cast hdiv
  have hdiv : (a : ℚ) / ((a - 1 : ℤ) : ℚ) ∈ GoodP p := by
    simpa [div_eq_mul_inv] using (GoodP p).mul_mem hA hInv
  let R : GoodP p := ⟨(a : ℚ) / ((a - 1 : ℤ) : ℚ), hdiv⟩
  have hcast : residueHomP p R =
      (a : ZMod p) * (((a - 1 : ℤ) : ZMod p)⁻¹) := by
    have hR : R =
        (⟨(a : ℚ), hA⟩ : GoodP p) *
          (⟨((a - 1 : ℤ) : ℚ)⁻¹, hInv⟩ : GoodP p) := by
      ext
      rfl
    rw [hR, map_mul]
    change ((a : ℚ) : ZMod p) * ((((a - 1 : ℤ) : ℚ)⁻¹ : ℚ) : ZMod p) = _
    rw [Rat.cast_intCast]
    have hcastinv : ((((a - 1 : ℤ) : ℚ)⁻¹ : ℚ) : ZMod p) =
        (((a - 1 : ℤ) : ZMod p)⁻¹) := by
      have hzQ : ((a - 1 : ℤ) : ℚ) ≠ 0 := by
        apply Int.cast_ne_zero.mpr
        intro hz
        apply hunitAm1
        simp [hz]
      have h1 := congrArg (fun x : ℚ => (x : ZMod p))
        (inv_mul_cancel₀ hzQ)
      rw [Rat.cast_mul_of_ne_zero
        (natCast_ne_zero_of_coprime hInv)
        (natCast_ne_zero_of_coprime hAm1), Rat.cast_intCast,
        Rat.cast_one] at h1
      exact eq_inv_of_mul_eq_one_left h1
    rw [hcastinv]
  have hq : p0Q (a : ℚ) s ∈ GoodP p := by
    have hdiv' : (a : ℚ) / ((a : ℚ) - 1) ∈ GoodP p := by
      simpa [Int.cast_sub, Int.cast_one] using hdiv
    exact (GoodP p).sub_mem ((GoodP p).pow_mem hdiv' s) (GoodP p).one_mem
  change residueHomP p ⟨p0Q (a : ℚ) s, hq⟩ = _
  have hqeq : (⟨p0Q (a : ℚ) s, hq⟩ : GoodP p) = R ^ s - 1 := by
    ext
    simp [p0Q, R, div_eq_mul_inv, Int.cast_sub, Int.cast_one]
  rw [hqeq, map_sub, map_pow, hcast]
  simp

end
end Li2Lean.P0.PositiveTower

#print axioms Li2Lean.P0.PositiveTower.p0Q_residue_formula
