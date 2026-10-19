/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Mathlib
import Li2Lean.V.VFamily
import Li2Lean.V.SignedVFrobenius

namespace Li2Lean.V.SignedVFrobenius

abbrev GoodAt (p : Nat) : Subring Rat where
  carrier := {x | Nat.Coprime x.den p}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := by
    intro x y hx hy
    exact Nat.Coprime.of_dvd_left (Rat.add_den_dvd x y)
      (Nat.Coprime.mul_left hx hy)
  neg_mem' := by
    intro x hx
    simpa using hx
  mul_mem' := by
    intro x y hx hy
    exact Nat.Coprime.of_dvd_left (Rat.mul_den_dvd x y)
      (Nat.Coprime.mul_left hx hy)

variable {p : Nat} [Fact (Nat.Prime p)]

private theorem natCast_ne_zero_of_coprime {d : Nat} (hd : Nat.Coprime d p) :
    (d : ZMod p) ≠ 0 := by
  intro hz
  have hpd : p ∣ d := (ZMod.natCast_eq_zero_iff d p).mp hz
  have hp1 : p = 1 := hd.symm.eq_one_of_dvd hpd
  have hp : Nat.Prime p := Fact.out
  have hpos := hp.one_lt
  omega

def residueOf (x : Rat) (_hx : Nat.Coprime x.den p) : ZMod p :=
  (x.num : ZMod p) * (x.den : ZMod p)⁻¹

theorem residueOf_eq_cast (x : Rat) (hx : Nat.Coprime x.den p) :
    residueOf x hx = (x : ZMod p) := by
  have hden : (x.den : ZMod p) ≠ 0 := natCast_ne_zero_of_coprime hx
  rw [residueOf, Rat.cast_def]
  simp [div_eq_mul_inv, hden]

private theorem prime_pow_dvd_mul_of_not_dvd_left {n a b : Nat}
    (hp : Nat.Prime p) (ha : ¬ p ∣ a) (h : p ^ n ∣ a * b) : p ^ n ∣ b := by
  induction n generalizing b with
  | zero => simp
  | succ n ih =>
      have hlow : p ^ n ∣ a * b :=
        (Nat.pow_dvd_pow p (Nat.le_succ n)).trans h
      have hbLow : p ^ n ∣ b := ih hlow
      obtain ⟨c, rfl⟩ := hbLow
      have hcancel : p ∣ a * c := by
        have hdiv : p ^ n * p ∣ p ^ n * (a * c) := by
          simpa [pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h
        exact (Nat.mul_dvd_mul_iff_left
          (show 0 < p ^ n by exact Nat.pow_pos hp.pos)).mp hdiv
      have hpc := hp.dvd_mul.mp hcancel
      have hc : p ∣ c := hpc.resolve_left ha
      rw [pow_succ]
      exact Nat.mul_dvd_mul_left _ hc

private theorem prime_pow_div_den_coprime (k d : Nat) (hd : 0 < d)
    (hbound : d < p * p ^ k) :
    Nat.Coprime ((((p ^ k : Nat) : Rat) / (d : Rat)).den) p := by
  let z : Rat := ((p ^ k : Nat) : Rat) / (d : Rat)
  have hp : Nat.Prime p := Fact.out
  have hp_pos : 0 < p := hp.pos
  have hzpos : 0 < z := by
    dsimp [z]
    positivity
  have hnumPos : 0 < z.num := Rat.num_pos.mpr hzpos
  have hnumAbsCast : (z.num.natAbs : Int) = z.num :=
    Int.natAbs_of_nonneg hnumPos.le
  have hrepr : (z.num : Rat) / (z.den : Rat) = z := by
    calc
      (z.num : Rat) / (z.den : Rat) =
          (z.num : Rat) / ((z.den : Int) : Rat) := by norm_num
      _ = Rat.divInt z.num (z.den : Int) := Rat.intCast_div_eq_divInt _ _
      _ = z := Rat.num_divInt_den z
  have hcrossQ : ((p ^ k : Nat) : Rat) * (z.den : Rat) =
      (d : Rat) * (z.num : Rat) := by
    have hrat : ((p ^ k : Nat) : Rat) / (d : Rat) =
        (z.num : Rat) / (z.den : Rat) := by
      calc
        _ = z := rfl
        _ = _ := hrepr.symm
    have hrat' := hrat
    field_simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd), Rat.den_nz z] at hrat'
    nlinarith [hrat']
  have hcrossZ : (p ^ k : Int) * (z.den : Int) =
      (d : Int) * z.num := by
    exact_mod_cast hcrossQ
  have hcrossN : p ^ k * z.den = d * z.num.natAbs := by
    rw [← hnumAbsCast] at hcrossZ
    exact_mod_cast hcrossZ
  have hp : Nat.Prime p := Fact.out
  have hdenCop : Nat.Coprime p z.den := (hp.coprime_iff_not_dvd).2 (by
    intro hpden
    have hcopred : Nat.Coprime z.num.natAbs z.den := z.reduced
    have hpnum : ¬ p ∣ z.num.natAbs := by
      intro hnum
      have hg : p ∣ Nat.gcd z.num.natAbs z.den := Nat.dvd_gcd hnum hpden
      rw [hcopred.gcd_eq_one] at hg
      have hp1 : p = 1 := Nat.dvd_one.mp hg
      exact hp.ne_one hp1
    have hpowdiv : p ^ (k + 1) ∣ p ^ k * z.den := by
      rw [pow_succ]
      exact Nat.mul_dvd_mul_left _ hpden
    have hpowdiv' : p ^ (k + 1) ∣ d * z.num.natAbs := by
      rw [hcrossN] at hpowdiv
      exact hpowdiv
    have hdvd : p ^ (k + 1) ∣ d :=
      prime_pow_dvd_mul_of_not_dvd_left hp hpnum
        (by simpa [Nat.mul_comm] using hpowdiv')
    have hle : p ^ (k + 1) ≤ d := Nat.le_of_dvd hd hdvd
    have hle' : p * p ^ k ≤ d := by
      simpa [pow_succ, Nat.mul_comm] using hle
    exact (Nat.not_lt_of_ge hle') hbound)
  exact hdenCop.symm

theorem prime_pow_div_residue_eq_zero (k d : Nat) (hd : 0 < d)
    (hbound : d < p * p ^ k) (hno : ¬ p ^ k ∣ d) :
    residueOf (((p ^ k : Nat) : Rat) / (d : Rat))
      (prime_pow_div_den_coprime k d hd hbound) = 0 := by
  let z : Rat := ((p ^ k : Nat) : Rat) / (d : Rat)
  have hp : Nat.Prime p := Fact.out
  have hp_pos : 0 < p := hp.pos
  have hzpos : 0 < z := by
    dsimp [z]
    positivity
  have hnumPos : 0 < z.num := Rat.num_pos.mpr hzpos
  have hnumAbsCast : (z.num.natAbs : Int) = z.num :=
    Int.natAbs_of_nonneg hnumPos.le
  have hrepr : (z.num : Rat) / (z.den : Rat) = z := by
    calc
      (z.num : Rat) / (z.den : Rat) =
          (z.num : Rat) / ((z.den : Int) : Rat) := by norm_num
      _ = Rat.divInt z.num (z.den : Int) := Rat.intCast_div_eq_divInt _ _
      _ = z := Rat.num_divInt_den z
  have hcrossQ : ((p ^ k : Nat) : Rat) * (z.den : Rat) =
      (d : Rat) * (z.num : Rat) := by
    have hrat : ((p ^ k : Nat) : Rat) / (d : Rat) =
        (z.num : Rat) / (z.den : Rat) := by
      calc
        _ = z := rfl
        _ = _ := hrepr.symm
    have hrat' := hrat
    field_simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd), Rat.den_nz z] at hrat'
    nlinarith [hrat']
  have hcrossZ : (p ^ k : Int) * (z.den : Int) =
      (d : Int) * z.num := by
    exact_mod_cast hcrossQ
  have hcrossN : p ^ k * z.den = d * z.num.natAbs := by
    rw [← hnumAbsCast] at hcrossZ
    exact_mod_cast hcrossZ
  have hp : Nat.Prime p := Fact.out
  have hpnum : p ∣ z.num.natAbs := by
    by_contra hnot
    have hpowdiv : p ^ k ∣ p ^ k * z.den := dvd_mul_right _ _
    rw [hcrossN] at hpowdiv
    have hdvd : p ^ k ∣ d :=
      prime_pow_dvd_mul_of_not_dvd_left hp hnot
        (by simpa [Nat.mul_comm] using hpowdiv)
    exact hno hdvd
  have hpnumInt : (p : Int) ∣ z.num := by
    apply Int.dvd_natAbs.mp
    exact_mod_cast hpnum
  have hnumZero : (z.num : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd z.num p).2 hpnumInt
  change (z.num : ZMod p) * (z.den : ZMod p)⁻¹ = 0
  rw [hnumZero]
  simp

theorem prime_pow_div_residue_eq_unit (k c : Nat) (hc0 : 0 < c) (hclt : c < p) :
    residueOf (((p ^ k : Nat) : Rat) / ((c * p ^ k : Nat) : Rat))
      (prime_pow_div_den_coprime k (c * p ^ k) (by
        have hp : Nat.Prime p := Fact.out
        exact Nat.mul_pos hc0 (Nat.pow_pos hp.pos)) (by
        have hp : Nat.Prime p := Fact.out
        exact Nat.mul_lt_mul_of_pos_right hclt (Nat.pow_pos hp.pos))) =
      (c : ZMod p)⁻¹ := by
  let hp : Nat.Prime p := Fact.out
  have hcp : Nat.Coprime c p :=
    (Nat.coprime_of_lt_prime (Nat.ne_of_gt hc0) hclt hp).symm
  have hcne : (c : Rat) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hc0)
  have hpowne : ((p ^ k : Nat) : Rat) ≠ 0 := by
    exact_mod_cast pow_ne_zero k hp.ne_zero
  have hpCast : (p : Rat) ≠ 0 := by
    exact_mod_cast hp.ne_zero
  have hrat : ((p ^ k : Nat) : Rat) / ((c * p ^ k : Nat) : Rat) =
      (c : Rat)⁻¹ := by
    rw [Nat.cast_mul]
    push_cast
    field_simp [hcne, hpCast]
  rw [residueOf_eq_cast, hrat, Rat.cast_inv_nat]

/-- The actual V-row entry after the row is scaled by `p^k`. -/
def signedVScaledVEntry (k j ell : Nat) : Rat :=
  (((p ^ k : Nat) : Rat) / ((j + ell : Nat) : Rat))

theorem signedVScaledVEntry_eq (k j ell : Nat) :
    signedVScaledVEntry (p := p) k j ell =
      ((p ^ k : Nat) : Rat) * vVEntry j ell := by
  simp [signedVScaledVEntry, vVEntry, div_eq_mul_inv]

/-- The unique V-row index whose denominator is divisible by the block size. -/
def signedVHitLambda (q u : Nat) : Nat :=
  if u = 0 then q else q - u

theorem signedVHitLambda_spec (q u : Nat) (hq : 0 < q) (hu : u < q) :
    0 < signedVHitLambda q u ∧ signedVHitLambda q u ≤ q ∧
      u + signedVHitLambda q u = q := by
  by_cases hu0 : u = 0
  · subst u
    simp [signedVHitLambda, hq]
  · rw [signedVHitLambda, if_neg hu0]
    omega

theorem signedVHitLambda_unique (q u ell : Nat) (hq : 0 < q)
    (hu : u < q) (hell : 0 < ell) (hellq : ell ≤ q)
    (hhit : u + ell = q) : ell = signedVHitLambda q u := by
  by_cases hu0 : u = 0
  · subst u
    simp [signedVHitLambda] at hhit ⊢
    omega
  · rw [signedVHitLambda, if_neg hu0]
    omega

/-- After scaling by `p^k`, a V entry survives exactly when the column and
row residues sum to one full block.  The surviving value is the seed entry
`1 / (j0 + 1)`; all other residues reduce to zero. -/
theorem signedVScaledVEntry_residue (k j0 u ell : Nat)
    (hp11 : 11 ≤ p) (hj0 : j0 < 10) (hu : u < p ^ k)
    (hell : 0 < ell) (hellq : ell ≤ p ^ k) :
    residueOf (signedVScaledVEntry k (j0 * p ^ k + u) ell)
      (prime_pow_div_den_coprime k (j0 * p ^ k + u + ell)
        (by omega) (by
          have hp : Nat.Prime p := Fact.out
          have hq : 0 < p ^ k := Nat.pow_pos hp.pos
          calc
            j0 * p ^ k + u + ell < (j0 + 2) * p ^ k := by
              have htail : u + ell < p ^ k + p ^ k := by omega
              calc
                j0 * p ^ k + u + ell = j0 * p ^ k + (u + ell) := by omega
                _ < j0 * p ^ k + (p ^ k + p ^ k) := Nat.add_lt_add_left htail _
                _ = (j0 + 2) * p ^ k := by ring
            _ ≤ p * p ^ k := Nat.mul_le_mul_right _ (by omega))) =
      if u + ell = p ^ k then ((j0 + 1 : Nat) : ZMod p)⁻¹ else 0 := by
  let q := p ^ k
  let n := j0 * q + u + ell
  have hp : Nat.Prime p := Fact.out
  have hq : 0 < q := Nat.pow_pos hp.pos
  have hnpos : 0 < n := by
    dsimp [n, q]
    omega
  have hnlt : n < p * q := by
    dsimp [n, q]
    calc
      j0 * p ^ k + u + ell < (j0 + 2) * p ^ k := by
        have htail : u + ell < p ^ k + p ^ k := by omega
        calc
          j0 * p ^ k + u + ell = j0 * p ^ k + (u + ell) := by omega
          _ < j0 * p ^ k + (p ^ k + p ^ k) := Nat.add_lt_add_left htail _
          _ = (j0 + 2) * p ^ k := by ring
      _ ≤ p * p ^ k := Nat.mul_le_mul_right _ (by omega)
  have hscaled : signedVScaledVEntry (p := p) k (j0 * q + u) ell =
      ((p ^ k : Nat) : Rat) / (n : Rat) := by
    rfl
  by_cases hhit : u + ell = q
  · have hhit' : u + ell = p ^ k := by simpa [q] using hhit
    have hc0 : 0 < j0 + 1 := by omega
    have hclt : j0 + 1 < p := by omega
    have hunit := prime_pow_div_residue_eq_unit (p := p) k (j0 + 1) hc0 hclt
    rw [if_pos hhit]
    change residueOf
      (((p ^ k : Nat) : Rat) /
        ((j0 * p ^ k + u + ell : Nat) : Rat)) _ = _
    have hdenEq : j0 * p ^ k + u + ell = (j0 + 1) * p ^ k := by
      calc
        j0 * p ^ k + u + ell = j0 * p ^ k + (u + ell) :=
          Nat.add_assoc _ _ _
        _ = j0 * p ^ k + p ^ k := by rw [hhit']
        _ = (j0 + 1) * p ^ k := by ring
    simpa [hdenEq] using hunit
  · have huell_pos : 0 < u + ell := by omega
    have huell_lt : u + ell < q + q := by omega
    have hnot : ¬ q ∣ u + ell := by
      intro hdiv
      have heq : u + ell = q :=
        Nat.eq_of_dvd_of_lt_two_mul (Nat.ne_of_gt huell_pos) hdiv
          (by simpa [two_mul] using huell_lt)
      exact hhit heq
    have hno : ¬ q ∣ n := by
      intro hdiv
      have hsplit : n = j0 * q + (u + ell) := by
        dsimp [n]
        omega
      rw [hsplit] at hdiv
      have hrem :=
        (Nat.dvd_add_right (Dvd.intro_left j0 rfl)).mp hdiv
      exact hnot hrem
    have hzero := prime_pow_div_residue_eq_zero (p := p) k n hnpos (by
      simpa [q] using hnlt) hno
    rw [if_neg hhit]
    change residueOf
      (((p ^ k : Nat) : Rat) /
        ((j0 * p ^ k + u + ell : Nat) : Rat)) _ = 0
    exact hzero

end Li2Lean.V.SignedVFrobenius

#print axioms Li2Lean.V.SignedVFrobenius.signedVScaledVEntry_residue
#print axioms Li2Lean.V.SignedVFrobenius.prime_pow_div_residue_eq_zero
