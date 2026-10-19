/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Mathlib

/-!
# Prime-parametric denominator absorption for the P0 Frobenius tower

This ports `P0.NonvanishingLocalResidue` from the fixed prime 83 to an
arbitrary prime, keeping the same rational values and denominator bound.
Source: v13 `chapters/nonvanishing.tex:200-258` (scaled pencil and Lucas
reduction). This module proves the local arithmetic input, independently
of the seed residue and full matrix Frobenius congruence.
-/
namespace Li2Lean.P0.PositiveTower
variable {P : ℕ} [Fact (Nat.Prime P)]

private theorem powP_dvd_mul_of_not_dvd_left {n a b : ℕ}
    (ha : ¬ P ∣ a) (h : P ^ n ∣ a * b) : P ^ n ∣ b := by
  induction n generalizing b with
  | zero => simp
  | succ n ih =>
      have hlow : P ^ n ∣ a * b := (pow_dvd_pow P (Nat.le_succ n)).trans h
      have hbLow : P ^ n ∣ b := ih hlow
      obtain ⟨c, rfl⟩ := hbLow
      have hcancel : P ∣ a * c := by
        have hdiv : P ^ n * P ∣ P ^ n * (a * c) := by
          simpa [pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h
        exact (Nat.mul_dvd_mul_iff_left
          (show 0 < (P : ℕ) ^ n from pow_pos (Fact.out : Nat.Prime P).pos _)).mp hdiv
      have hpc : P ∣ c := ((Fact.out : Nat.Prime P).dvd_mul.mp hcancel).resolve_left ha
      rw [pow_succ]
      exact Nat.mul_dvd_mul_left _ hpc

/-- A prime-power numerator absorbs every P-factor in a smaller denominator. -/
theorem powP_div_den_coprime (k d : ℕ) (hd : 0 < d)
    (hbound : d < P * P ^ k) :
    Nat.Coprime (((P ^ k : ℕ) : ℚ) / (d : ℚ)).den P := by
  let z : ℚ := ((P ^ k : ℕ) : ℚ) / (d : ℚ)
  have hzpos : 0 < z := by
    dsimp [z]
    exact div_pos (by exact_mod_cast pow_pos (Fact.out : Nat.Prime P).pos k) (by exact_mod_cast hd)
  have hnumPos : 0 < z.num := Rat.num_pos.mpr hzpos
  have hnumAbsCast : (z.num.natAbs : ℤ) = z.num :=
    Int.natAbs_of_nonneg hnumPos.le
  have hrepr : (z.num : ℚ) / (z.den : ℚ) = z := by
    calc
      (z.num : ℚ) / (z.den : ℚ) =
          (z.num : ℚ) / ((z.den : ℤ) : ℚ) := by norm_num
      _ = Rat.divInt z.num (z.den : ℤ) := Rat.intCast_div_eq_divInt _ _
      _ = z := Rat.num_divInt_den z
  have hcrossQ : ((P ^ k : ℕ) : ℚ) * (z.den : ℚ) =
      (d : ℚ) * (z.num : ℚ) := by
    have hrat : ((P ^ k : ℕ) : ℚ) / (d : ℚ) =
        (z.num : ℚ) / (z.den : ℚ) := by
      calc
        _ = z := rfl
        _ = _ := hrepr.symm
    have hrat' := hrat
    field_simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd), Rat.den_nz z] at hrat'
    nlinarith [hrat']
  have hcrossZ : (P ^ k : ℤ) * (z.den : ℤ) =
      (d : ℤ) * z.num := by
    exact_mod_cast hcrossQ
  have hcrossN : P ^ k * z.den = d * z.num.natAbs := by
    rw [← hnumAbsCast] at hcrossZ
    exact_mod_cast hcrossZ
  have hdenCop : Nat.Coprime P z.den := ((Fact.out : Nat.Prime P).coprime_iff_not_dvd).2 (by
    intro hpden
    have hcopred : Nat.Coprime z.num.natAbs z.den := z.reduced
    have hpnum : ¬ P ∣ z.num.natAbs := by
      intro h
      have hg : P ∣ Nat.gcd z.num.natAbs z.den := Nat.dvd_gcd h hpden
      rw [hcopred.gcd_eq_one] at hg
      exact (Fact.out : Nat.Prime P).not_dvd_one hg
    have hpowdiv : P ^ (k + 1) ∣ P ^ k * z.den := by
      rw [pow_succ]
      exact Nat.mul_dvd_mul_left _ hpden
    have hpowdiv' : P ^ (k + 1) ∣ d * z.num.natAbs := by
      rw [hcrossN] at hpowdiv
      exact hpowdiv
    have hdvd : P ^ (k + 1) ∣ d := by
      exact powP_dvd_mul_of_not_dvd_left hpnum
        (by simpa [Nat.mul_comm] using hpowdiv')
    have hle : P ^ (k + 1) ≤ d := Nat.le_of_dvd hd hdvd
    rw [pow_succ] at hle
    exact (not_lt_of_ge hle) (by simpa [Nat.mul_comm] using hbound))
  exact hdenCop.symm

/-- If the denominator is not divisible by the prime-power numerator, its
reduced residue is zero. -/
theorem powP_div_den_residue_eq_zero (k d : ℕ) (hd : 0 < d)
    (_hbound : d < P * P ^ k) (hno : ¬ P ^ k ∣ d) :
    ((((P ^ k : ℕ) : ℚ) / (d : ℚ) : ℚ) : ZMod P) = 0 := by
  let z : ℚ := ((P ^ k : ℕ) : ℚ) / (d : ℚ)
  have hzpos : 0 < z := by
    dsimp [z]
    exact div_pos (by exact_mod_cast pow_pos (Fact.out : Nat.Prime P).pos k) (by exact_mod_cast hd)
  have hnumPos : 0 < z.num := Rat.num_pos.mpr hzpos
  have hnumAbsCast : (z.num.natAbs : ℤ) = z.num :=
    Int.natAbs_of_nonneg hnumPos.le
  have hrepr : (z.num : ℚ) / (z.den : ℚ) = z := by
    calc
      (z.num : ℚ) / (z.den : ℚ) =
          (z.num : ℚ) / ((z.den : ℤ) : ℚ) := by norm_num
      _ = Rat.divInt z.num (z.den : ℤ) := Rat.intCast_div_eq_divInt _ _
      _ = z := Rat.num_divInt_den z
  have hcrossQ : ((P ^ k : ℕ) : ℚ) * (z.den : ℚ) =
      (d : ℚ) * (z.num : ℚ) := by
    have hrat : ((P ^ k : ℕ) : ℚ) / (d : ℚ) =
        (z.num : ℚ) / (z.den : ℚ) := by
      calc
        _ = z := rfl
        _ = _ := hrepr.symm
    have hrat' := hrat
    field_simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd), Rat.den_nz z] at hrat'
    nlinarith [hrat']
  have hcrossZ : (P ^ k : ℤ) * (z.den : ℤ) =
      (d : ℤ) * z.num := by
    exact_mod_cast hcrossQ
  have hcrossN : P ^ k * z.den = d * z.num.natAbs := by
    rw [← hnumAbsCast] at hcrossZ
    exact_mod_cast hcrossZ
  have hpnum : P ∣ z.num.natAbs := by
    by_contra hnot
    have hpowdiv : P ^ k ∣ P ^ k * z.den := dvd_mul_right _ _
    have hpowdiv' : P ^ k ∣ d * z.num.natAbs := by
      rw [hcrossN] at hpowdiv
      exact hpowdiv
    have hdvd : P ^ k ∣ d :=
      powP_dvd_mul_of_not_dvd_left hnot
        (by simpa [Nat.mul_comm] using hpowdiv')
    exact hno hdvd
  have hpnumInt : (P : ℤ) ∣ z.num := by
    apply Int.dvd_natAbs.mp
    exact_mod_cast hpnum
  have hnumZero : (z.num : ZMod P) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd z.num P).2 hpnumInt
  change (z : ZMod P) = 0
  rw [Rat.cast_def]
  rw [hnumZero]
  simp


/-- A product of two denominators is cleared by two copies of the prime power. -/
theorem powP_sq_div_prod_den_coprime (k d₁ d₂ : ℕ)
    (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (hb₁ : d₁ < P * P ^ k) (hb₂ : d₂ < P * P ^ k) :
    Nat.Coprime (((P ^ k : ℕ) : ℚ) ^ 2 /
      ((d₁ * d₂ : ℕ) : ℚ)).den P := by
  have hvalue : (((P ^ k : ℕ) : ℚ) ^ 2 / ((d₁ * d₂ : ℕ) : ℚ)) =
      (((P ^ k : ℕ) : ℚ) / (d₁ : ℚ)) *
        (((P ^ k : ℕ) : ℚ) / (d₂ : ℚ)) := by
    push_cast
    field_simp
  rw [hvalue]
  exact Nat.Coprime.of_dvd_left (Rat.mul_den_dvd _ _)
    (Nat.Coprime.mul_left
      (powP_div_den_coprime k d₁ hd₁ hb₁)
      (powP_div_den_coprime k d₂ hd₂ hb₂))

/-- A sufficiently large prime-square scaling of any rational argument is
p-integral. This is the argument used by the seed transport field. -/
theorem powP_sq_mul_rat_den_coprime (k : ℕ) (r : ℚ)
    (hbound : r.den < P ^ k) :
    Nat.Coprime (((P ^ k : ℕ) : ℚ)^2 * r).den P := by
  have hsize : P ^ k ≤ P * P ^ k := by
    simpa using Nat.mul_le_mul_right (P ^ k) (Fact.out : Nat.Prime P).one_lt.le
  have hleft := powP_div_den_coprime k r.den
    (Nat.pos_of_ne_zero r.den_nz) (lt_of_lt_of_le hbound hsize)
  have hright : Nat.Coprime
      (((P ^ k : ℕ) : ℚ) * (r.num : ℚ)).den P := by
    norm_num [Rat.den_mul]
  have hvalue : ((P ^ k : ℕ) : ℚ)^2 * r =
      (((P ^ k : ℕ) : ℚ) / (r.den : ℚ)) *
        (((P ^ k : ℕ) : ℚ) * (r.num : ℚ)) := by
    have hr : (r.num : ℚ) / (r.den : ℚ) = r := Rat.num_div_den r
    conv_lhs => rw [← hr]
    ring
  rw [hvalue]
  exact Nat.Coprime.of_dvd_left (Rat.mul_den_dvd _ _)
    (Nat.Coprime.mul_left hleft hright)

private theorem pUnit_natCast_ne_zero {d : ℕ} (hd : Nat.Coprime d P) :
    (d : ZMod P) ≠ 0 := by
  intro hzero
  have hzeroInt : ((d : ℤ) : ZMod P) = 0 := by simpa using hzero
  have hdvdInt : (P : ℤ) ∣ (d : ℤ) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (d : ℤ) P).mp hzeroInt
  have hdvd : P ∣ d := by exact_mod_cast hdvdInt
  exact (Fact.out : Nat.Prime P).ne_one (hd.symm.eq_one_of_dvd hdvd)

/-- The scaled argument used by seed transport has zero residue once the
prime power exceeds the argument's denominator. -/
theorem powP_sq_mul_rat_cast_eq_zero (k : ℕ) (r : ℚ)
    (hbound : r.den < P ^ k) :
    ((((P ^ k : ℕ) : ℚ)^2 * r : ℚ) : ZMod P) = 0 := by
  have hd : 0 < r.den := Nat.pos_of_ne_zero r.den_nz
  have hsize : P ^ k ≤ P * P ^ k := by
    simpa using Nat.mul_le_mul_right (P ^ k) (Fact.out : Nat.Prime P).one_lt.le
  have hb : r.den < P * P ^ k := lt_of_lt_of_le hbound hsize
  have hleft := powP_div_den_coprime k r.den hd hb
  have hright : Nat.Coprime
      (((P ^ k : ℕ) : ℚ) * (r.num : ℚ)).den P := by
    norm_num [Rat.den_mul]
  have hvalue : ((P ^ k : ℕ) : ℚ)^2 * r =
      (((P ^ k : ℕ) : ℚ) / (r.den : ℚ)) *
        (((P ^ k : ℕ) : ℚ) * (r.num : ℚ)) := by
    have hr : (r.num : ℚ) / (r.den : ℚ) = r := Rat.num_div_den r
    conv_lhs => rw [← hr]
    ring
  rw [hvalue, Rat.cast_mul_of_ne_zero
    (pUnit_natCast_ne_zero hleft) (pUnit_natCast_ne_zero hright),
    powP_div_den_residue_eq_zero k r.den hd hb
      (Nat.not_dvd_of_pos_of_lt hd hbound), zero_mul]

/-- One prime-power scaling suffices for each rational coefficient. -/
theorem powP_mul_rat_den_coprime (k : ℕ) (r : ℚ)
    (hbound : r.den < P ^ k) :
    Nat.Coprime (((P ^ k : ℕ) : ℚ) * r).den P := by
  have hsize : P ^ k ≤ P * P ^ k := by
    simpa using Nat.mul_le_mul_right (P ^ k) (Fact.out : Nat.Prime P).one_lt.le
  have hleft := powP_div_den_coprime k r.den
    (Nat.pos_of_ne_zero r.den_nz) (lt_of_lt_of_le hbound hsize)
  have hright : Nat.Coprime
      (r.num : ℚ).den P := by
    norm_num [Rat.den_mul]
  have hvalue : ((P ^ k : ℕ) : ℚ) * r =
      (((P ^ k : ℕ) : ℚ) / (r.den : ℚ)) *
        (r.num : ℚ) := by
    have hr : (r.num : ℚ) / (r.den : ℚ) = r := Rat.num_div_den r
    conv_lhs => rw [← hr]
    ring
  rw [hvalue]
  exact Nat.Coprime.of_dvd_left (Rat.mul_den_dvd _ _)
    (Nat.Coprime.mul_left hleft hright)

theorem powP_mul_rat_cast_eq_zero (k : ℕ) (r : ℚ)
    (hbound : r.den < P ^ k) :
    ((((P ^ k : ℕ) : ℚ) * r : ℚ) : ZMod P) = 0 := by
  have hd : 0 < r.den := Nat.pos_of_ne_zero r.den_nz
  have hsize : P ^ k ≤ P * P ^ k := by
    simpa using Nat.mul_le_mul_right (P ^ k) (Fact.out : Nat.Prime P).one_lt.le
  have hb : r.den < P * P ^ k := lt_of_lt_of_le hbound hsize
  have hleft := powP_div_den_coprime k r.den hd hb
  have hright : Nat.Coprime
      (r.num : ℚ).den P := by
    norm_num [Rat.den_mul]
  have hvalue : ((P ^ k : ℕ) : ℚ) * r =
      (((P ^ k : ℕ) : ℚ) / (r.den : ℚ)) *
        (r.num : ℚ) := by
    have hr : (r.num : ℚ) / (r.den : ℚ) = r := Rat.num_div_den r
    conv_lhs => rw [← hr]
    ring
  rw [hvalue, Rat.cast_mul_of_ne_zero
    (pUnit_natCast_ne_zero hleft) (pUnit_natCast_ne_zero hright),
    powP_div_den_residue_eq_zero k r.den hd hb
      (Nat.not_dvd_of_pos_of_lt hd hbound), zero_mul]

/-- A single tower cutoff clears the denominators of a finite family of
rationals, as needed for the support of a seed polynomial. -/
theorem finite_den_lt_prime_pow (s : Finset ℚ) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ x ∈ s, x.den < P ^ k := by
  refine ⟨s.sup Rat.den, ?_⟩
  intro k hk x hx
  have hden : x.den ≤ s.sup Rat.den := Finset.le_sup hx
  exact lt_of_le_of_lt (hden.trans hk)
    (Nat.lt_pow_self (Fact.out : Nat.Prime P).one_lt)

end Li2Lean.P0.PositiveTower
