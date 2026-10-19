/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.Kit.ReducedRational

/-!
# Prime-parametric local rational ring and reduced rational certificates

Reuse ControlledResidue and NonvanishingTower with arbitrary prime p,
following v13 chapters/nonvanishing.tex:200-258. This supplies no source
Frobenius or seed nonvanishing theorem by itself.
-/
namespace Li2Lean.P0.PositiveTower

noncomputable section

open Matrix

/-! ## 1. The `p`-integral subring and its residue map (port of `ControlledResidue:1-100`) -/

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

/-- Rationals whose reduced denominator is prime to `p`. -/
def GoodP : Subring ℚ where
  carrier := {x | Nat.Coprime x.den p}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := by
    intro x y hx hy
    exact Nat.Coprime.of_dvd_left (Rat.add_den_dvd x y) (Nat.Coprime.mul_left hx hy)
  neg_mem' := by
    intro x hx
    simpa using hx
  mul_mem' := by
    intro x y hx hy
    exact Nat.Coprime.of_dvd_left (Rat.mul_den_dvd x y) (Nat.Coprime.mul_left hx hy)

variable {p}

theorem natCast_ne_zero_of_coprime {d : ℕ} (hcop : Nat.Coprime d p) :
    (d : ZMod p) ≠ 0 := by
  intro hz
  have hdvd : p ∣ d := (by
    have hzI : ((d : ℤ) : ZMod p) = 0 := by simpa using hz
    have hdvdI := (ZMod.intCast_zmod_eq_zero_iff_dvd (d : ℤ) p).mp hzI
    exact_mod_cast hdvdI)
  have h1 : p = 1 := hcop.symm.eq_one_of_dvd hdvd
  exact hp.out.ne_one h1

variable (p)

/-- Reduction modulo `p` on `GoodP p`; it is the ordinary rational cast. -/
def residueHomP : GoodP p →+* ZMod p where
  toFun x := (x.1 : ZMod p)
  map_zero' := by simp
  map_one' := by simp
  map_add' := by
    intro x y
    change ((x.1 + y.1 : ℚ) : ZMod p) = (x.1 : ZMod p) + (y.1 : ZMod p)
    exact Rat.cast_add_of_ne_zero (natCast_ne_zero_of_coprime x.2)
      (natCast_ne_zero_of_coprime y.2)
  map_mul' := by
    intro x y
    change ((x.1 * y.1 : ℚ) : ZMod p) = (x.1 : ZMod p) * (y.1 : ZMod p)
    exact Rat.cast_mul_of_ne_zero (natCast_ne_zero_of_coprime x.2)
      (natCast_ne_zero_of_coprime y.2)

/-- The certificate form of a `p`-integral rational. -/
def reducedOfP (x : ℚ) (hcop : Nat.Coprime x.den p) : ContourKit.ReducedRational p :=
  { value := x
    numerator := x.num
    denominator := (x.den : ℤ)
    denominator_ne_zero := by exact_mod_cast x.den_nz
    denominator_residue_ne_zero := by exact_mod_cast natCast_ne_zero_of_coprime hcop
    value_eq := by simpa using (Rat.num_div_den x).symm
    residue := (x.num : ZMod p) * (x.den : ZMod p)⁻¹
    residue_eq := by push_cast; rfl }

theorem reducedOfP_residue (x : ℚ) (hcop : Nat.Coprime x.den p) :
    (reducedOfP p x hcop).residue = (x : ZMod p) := by
  change (x.num : ZMod p) * (x.den : ZMod p)⁻¹ = (x : ZMod p)
  rw [Rat.cast_def]
  simp [div_eq_mul_inv]

/-- Two certificates with the same value have the same residue
(verbatim port of `NonvanishingTower.reducedRational_residue_eq_of_value_eq_tower`). -/
theorem residue_eq_of_value_eq {x y : ContourKit.ReducedRational p}
    (hvalue : x.value = y.value) : x.residue = y.residue := by
  have hxdenQ : (x.denominator : ℚ) ≠ 0 := by exact_mod_cast x.denominator_ne_zero
  have hydenQ : (y.denominator : ℚ) ≠ 0 := by exact_mod_cast y.denominator_ne_zero
  have hquot : (x.numerator : ℚ) / (x.denominator : ℚ) =
      (y.numerator : ℚ) / (y.denominator : ℚ) := by
    rw [← x.value_eq, ← y.value_eq, hvalue]
  have hcrossQ : (x.numerator : ℚ) * (y.denominator : ℚ) =
      (y.numerator : ℚ) * (x.denominator : ℚ) := by
    field_simp [hxdenQ, hydenQ] at hquot
    simpa [mul_comm, mul_left_comm, mul_assoc] using hquot
  have hcrossZ : x.numerator * y.denominator = y.numerator * x.denominator := by
    exact_mod_cast hcrossQ
  have hcross : (x.numerator : ZMod p) * (y.denominator : ZMod p) =
      (y.numerator : ZMod p) * (x.denominator : ZMod p) := by
    simpa only [Int.cast_mul] using congrArg (fun z : ℤ => (z : ZMod p)) hcrossZ
  rw [x.residue_eq, y.residue_eq]
  field_simp [x.denominator_residue_ne_zero, y.denominator_residue_ne_zero]
  simpa [mul_comm] using hcross


/-- Every finite-place certificate represents an element of the local ring. -/
theorem reducedRational_value_good (s : ContourKit.ReducedRational p) :
    s.value ∈ GoodP p := by
  change Nat.Coprime s.value.den p
  apply Nat.Coprime.symm
  apply (hp.out.coprime_iff_not_dvd).2
  intro hd
  have hden : (s.value.den : ℤ) ∣ s.denominator := by
    rw [s.value_eq, Rat.intCast_div_eq_divInt]
    exact Rat.den_dvd s.numerator s.denominator
  have hdiv : (p : ℤ) ∣ s.denominator :=
    (by exact_mod_cast hd : (p : ℤ) ∣ (s.value.den : ℤ)).trans hden
  exact s.denominator_residue_ne_zero
    ((ZMod.intCast_zmod_eq_zero_iff_dvd s.denominator p).2 hdiv)

end
end Li2Lean.P0.PositiveTower
