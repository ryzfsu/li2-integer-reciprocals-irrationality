/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.PositiveTower.GenericBResidue

namespace Li2Lean.P0.PositiveTower

noncomputable section

open Li2Lean
open EntryGoodness
open Li2Lean.P0.ScaledLucas

variable {p : ℕ} [Fact (Nat.Prime p)]

private lemma genericB2_good (a : ℤ) (g i s : ℕ) :
    genericB2 a g i s ∈ GoodP p := by
  unfold genericB2
  exact (GoodP p).mul_mem
    ((GoodP p).mul_mem
      ((GoodP p).pow_mem (EntryGoodness.intRat_good (p := p) a) i)
      ((GoodP p).pow_mem (EntryGoodness.intRat_good (p := p) (-1)) (s + 1)))
    (EntryGoodness.natRat_good (p := p) _)

private lemma genericBI_good (a : ℤ)
    (hunit : Nat.Coprime (a - 1).natAbs p)
    (k s : ℕ) (hs : s < p * p ^ k) : genericBI p a k s ∈ GoodP p := by
  unfold genericBI
  apply (GoodP p).sum_mem
  intro r hr
  have hr' := Finset.mem_range.mp hr
  exact (GoodP p).mul_mem
    (EntryGoodness.p0Q_good_general (p := p) (a := a) hunit _)
    (EntryGoodness.q_div_good k (r + 1) (by omega) (by omega))

def genericYBB (a : ℤ) (A : ℕ) : ZMod p :=
  (∑ c ∈ Finset.range A,
      ((p0UQ (a : ℚ) 2 (A - (c + 1)) : ℚ) : ZMod p) *
        ((c + 1 : ℕ) : ZMod p)⁻¹ * (((c + 1 : ℕ) : ZMod p)⁻¹)) -
    (a : ZMod p) ^ A * ∑ c ∈ Finset.range 2,
      (-1 : ZMod p) ^ (c + 1) *
        ((Nat.choose (A + 2) (2 - (c + 1)) : ℕ) : ZMod p) *
        (((c + 1 : ℕ) : ZMod p)⁻¹) *
        ∑ d ∈ Finset.range c,
          ((p0Q (a : ℚ) (d + 1) : ℚ) : ZMod p) *
            (((d + 1 : ℕ) : ZMod p)⁻¹)

private lemma odd_prime_pow (hp2 : 2 < p) (k : ℕ) : Odd (p ^ k) := by
  have hpodd : Odd p := by
    exact (Nat.Prime.odd_of_ne_two (Fact.out) (by omega))
  exact Odd.pow hpodd

lemma cast_genericB2_block (a : ℤ) (hp2 : 2 < p)
    (k A v c : ℕ) (hv : v < p ^ k) (hc : c < 2) :
    ((genericB2 a (2 * p ^ k) (A * p ^ k + v)
      (c * p ^ k + (p ^ k - 1)) : ℚ) : ZMod p) =
      (a : ZMod p) ^ v *
        ((a : ZMod p) ^ A * ((-1 : ZMod p) ^ (c + 1) *
          ((Nat.choose (A + 2) (2 - (c + 1)) : ℕ) : ZMod p))) := by
  have hq : 0 < p ^ k := pow_pos (Fact.out : Nat.Prime p).pos _
  unfold genericB2
  have hpowBig : (a : ℚ) ^ (A * p ^ k + v) ∈ GoodP p :=
    (GoodP p).pow_mem (EntryGoodness.intRat_good (p := p) a) _
  have hsignBig : (-1 : ℚ) ^ (c * p ^ k + (p ^ k - 1) + 1) ∈ GoodP p :=
    (GoodP p).pow_mem (EntryGoodness.intRat_good (p := p) (-1)) _
  have hchooseBig :
      ((Nat.choose (A * p ^ k + v + 2 * p ^ k)
        (2 * p ^ k - (c * p ^ k + (p ^ k - 1) + 1)) : ℕ) : ℚ) ∈ GoodP p :=
    EntryGoodness.natRat_good _
  have hprod :
      (a : ℚ) ^ (A * p ^ k + v) *
          (-1 : ℚ) ^ (c * p ^ k + (p ^ k - 1) + 1) *
          (Nat.choose (A * p ^ k + v + 2 * p ^ k)
            (2 * p ^ k - (c * p ^ k + (p ^ k - 1) + 1)) : ℚ) ∈ GoodP p :=
    (GoodP p).mul_mem ((GoodP p).mul_mem hpowBig hsignBig) hchooseBig
  have harg : 2 * p ^ k - (c * p ^ k + (p ^ k - 1) + 1) =
      (2 - (c + 1)) * p ^ k := by
    rw [ar_last c (p ^ k) hq, ← Nat.sub_mul]
  have htop : A * p ^ k + v + 2 * p ^ k =
      (A + 2) * p ^ k + v := by ring
  have hchoose_mod :
      ((Nat.choose (A * p ^ k + v + 2 * p ^ k)
        (2 * p ^ k - (c * p ^ k + (p ^ k - 1) + 1)) : ℕ) : ZMod p) =
      ((Nat.choose (A + 2) (2 - (c + 1)) : ℕ) : ZMod p) := by
    rw [harg, htop]
    exact (ZMod.natCast_eq_natCast_iff _ _ p).mpr
      (choose_pow_add_mul_modEq (p := p) (k := k) (u := A + 2)
        (d := 2 - (c + 1)) (r := v) hv)
  have hpow_cast (n : ℕ) :
      (((a : ℚ) ^ n : ℚ) : ZMod p) = (a : ZMod p) ^ n := by
    rw [show (a : ℚ) ^ n = ((a ^ n : ℤ) : ℚ) by norm_num,
      Rat.cast_intCast]
    norm_num
  have hsign_cast (n : ℕ) :
      (((-1 : ℚ) ^ n : ℚ) : ZMod p) = (-1 : ZMod p) ^ n := by
    rw [show (-1 : ℚ) ^ n = (((-1) ^ n : ℤ) : ℚ) by norm_num,
      Rat.cast_intCast]
    norm_num
  have hsign_mod :
      (-1 : ZMod p) ^ (c * p ^ k + (p ^ k - 1) + 1) =
        (-1 : ZMod p) ^ (c + 1) := by
    rw [ar_last c (p ^ k) hq, Nat.mul_comm (c + 1) (p ^ k), pow_mul,
      Odd.neg_one_pow (odd_prime_pow hp2 k)]
  rw [Rat.cast_mul_of_ne_zero (natCast_ne_zero_of_coprime
        ((GoodP p).mul_mem hpowBig hsignBig))
      (natCast_ne_zero_of_coprime hchooseBig),
    Rat.cast_mul_of_ne_zero (natCast_ne_zero_of_coprime hpowBig)
      (natCast_ne_zero_of_coprime hsignBig),
    hpow_cast, hsign_cast, Rat.cast_natCast, hchoose_mod,
    hsign_mod]
  rw [show (a : ZMod p) ^ (A * p ^ k + v) =
      (a : ZMod p) ^ v * (a : ZMod p) ^ A by
        rw [Nat.add_comm, pow_add, Nat.mul_comm, pow_mul]
        simp]
  ring

lemma cast_genericBI_block (a : ℤ) (hp2 : 2 < p)
    (hunit : Nat.Coprime (a - 1).natAbs p)
    (k c : ℕ) (hc : c < 2) :
    ((genericBI p a k (c * p ^ k + (p ^ k - 1)) : ℚ) : ZMod p) =
      ∑ d ∈ Finset.range c,
        ((p0Q (a : ℚ) (d + 1) : ℚ) : ZMod p) *
          (((d + 1 : ℕ) : ZMod p)⁻¹) := by
  have hq : 0 < p ^ k := pow_pos (Fact.out : Nat.Prime p).pos _
  have h2q : 2 * p ^ k < p * p ^ k :=
    Nat.mul_lt_mul_of_pos_right hp2 hq
  have hcq : c * p ^ k + (p ^ k - 1) < 2 * p ^ k :=
    ar_lt c _ _ 2 hc (by omega)
  have hm : ∀ r ∈ Finset.range (c * p ^ k + (p ^ k - 1)),
      p0Q (a : ℚ) (r + 1) *
        (qRatP p k / ((r + 1 : ℕ) : ℚ)) ∈ GoodP p := by
    intro r hr
    have hr' := Finset.mem_range.mp hr
    exact (GoodP p).mul_mem
      (EntryGoodness.p0Q_good_general (p := p) (a := a) hunit _)
      (EntryGoodness.q_div_good k _ (by omega)
        (by omega))
  unfold genericBI
  rw [EntryGoodness.ratCast_sum_good _ _ hm,
    block_sum (p ^ k) c (p ^ k - 1) (p ^ k - 1) _ (by omega)]
  · apply Finset.sum_congr rfl
    intro d hd
    have hd' := Finset.mem_range.mp hd
    have hlt : d * p ^ k + (p ^ k - 1) < 2 * p ^ k :=
      ar_lt d _ _ 2 (by omega) (by omega)
    have hden : d * p ^ k + (p ^ k - 1) + 1 < p * p ^ k := by
      rw [ar_last d _ hq]
      exact Nat.mul_lt_mul_of_pos_right (by omega) hq
    rw [Rat.cast_mul_of_ne_zero
        (natCast_ne_zero_of_coprime
          (EntryGoodness.p0Q_good_general (p := p) (a := a) hunit _))
        (natCast_ne_zero_of_coprime
          (EntryGoodness.q_div_good k _ (by omega) hden)),
      ar_last d _ hq,
      p0Q_scaled_residue_generic (p := p) a hunit k d,
      EntryGoodness.qdiv_cast_unit_generic k (d + 1) (by omega) (by omega)]
  · intro d hd t ht htt
    have hlt : d * p ^ k + t < 2 * p ^ k :=
      ar_lt d t _ 2 (by omega) ht
    have ht1 : t + 1 < p ^ k := by omega
    have hden : d * p ^ k + t + 1 < p * p ^ k := by
      have hdp : (d + 1) * p ^ k < p * p ^ k :=
        Nat.mul_lt_mul_of_pos_right (by omega) hq
      omega
    rw [Rat.cast_mul_of_ne_zero
        (natCast_ne_zero_of_coprime
          (EntryGoodness.p0Q_good_general (p := p) (a := a) hunit _))
        (natCast_ne_zero_of_coprime
          (EntryGoodness.q_div_good k _ (by omega) hden)),
      EntryGoodness.qdiv_cast_zero_generic k _ (by omega) hden
        (not_dvd_of_rem (m := d) (x := t + 1) (by ring) (by omega) ht1),
      mul_zero]

  · intro t ht
    have ht1 : t + 1 < p ^ k := by omega
    have hden : c * p ^ k + t + 1 < p * p ^ k := by
      have hcp : (c + 1) * p ^ k < p * p ^ k :=
        Nat.mul_lt_mul_of_pos_right (by omega) hq
      omega
    rw [Rat.cast_mul_of_ne_zero
        (natCast_ne_zero_of_coprime
          (EntryGoodness.p0Q_good_general (p := p) (a := a) hunit _))
        (natCast_ne_zero_of_coprime
          (EntryGoodness.q_div_good k _ (by omega) hden)),
      EntryGoodness.qdiv_cast_zero_generic k _ (by omega) hden
        (not_dvd_of_rem (m := c) (x := t + 1) (by ring) (by omega) ht1),
      mul_zero]

lemma cast_generic_qqBB (a : ℤ) (hp2 : 2 < p)
    (hunit : Nat.Coprime (a - 1).natAbs p)
    (k A v : ℕ) (hA : A + 3 ≤ p) (hv : v < p ^ k) :
    (((qRatP p k) ^ 2 * p0BQQ (a : ℚ) (2 * p ^ k)
      (A * p ^ k + v) : ℚ) : ZMod p) =
      (a : ZMod p) ^ v * genericYBB (p := p) a A := by
  have hq : 0 < p ^ k := pow_pos (Fact.out : Nat.Prime p).pos _
  have h2q : 2 * p ^ k < p * p ^ k :=
    Nat.mul_lt_mul_of_pos_right hp2 hq
  have hiq : A * p ^ k + v < p * p ^ k :=
    ar_lt A v _ p (by omega) hv
  rw [generic_qqBB_decomp]
  have hm1 : ∀ r ∈ Finset.range (A * p ^ k + v),
      p0UQ (a : ℚ) (2 * p ^ k) (A * p ^ k + v - (r + 1)) *
        (qRatP p k / ((r + 1 : ℕ) : ℚ)) *
        (qRatP p k / ((r + 1 : ℕ) : ℚ)) ∈ GoodP p := by
    intro r hr
    have hr' := Finset.mem_range.mp hr
    have hd : 0 < r + 1 := by omega
    have hbd : r + 1 < p * p ^ k := by omega
    exact (GoodP p).mul_mem
      ((GoodP p).mul_mem
        (EntryGoodness.p0U_good_general (p := p) (a := a) _ _)
        (EntryGoodness.q_div_good k (r + 1) hd hbd))
      (EntryGoodness.q_div_good k (r + 1) hd hbd)
  have hm2 : ∀ s ∈ Finset.range (2 * p ^ k),
      genericB2 a (2 * p ^ k) (A * p ^ k + v) s *
          (qRatP p k / ((s + 1 : ℕ) : ℚ)) *
          genericBI p a k s ∈ GoodP p := by
    intro s hs
    have hs' := Finset.mem_range.mp hs
    have hden : s + 1 < p * p ^ k := by omega
    exact (GoodP p).mul_mem
      ((GoodP p).mul_mem
        (genericB2_good (p := p) a _ _ _)
        (EntryGoodness.q_div_good k (s + 1) (by omega) hden))
      (genericBI_good (p := p) a hunit k s (by omega))
  rw [Rat.cast_sub_of_ne_zero
      (natCast_ne_zero_of_coprime ((GoodP p).sum_mem hm1))
      (natCast_ne_zero_of_coprime ((GoodP p).sum_mem hm2)),
    EntryGoodness.ratCast_sum_good _ _ hm1,
    EntryGoodness.ratCast_sum_good _ _ hm2]
  have hS1 :
      (∑ r ∈ Finset.range (A * p ^ k + v),
        ((p0UQ (a : ℚ) (2 * p ^ k)
          (A * p ^ k + v - (r + 1)) *
          (qRatP p k / ((r + 1 : ℕ) : ℚ)) *
          (qRatP p k / ((r + 1 : ℕ) : ℚ)) : ℚ) : ZMod p)) =
      (a : ZMod p) ^ v *
        (∑ c ∈ Finset.range A,
          ((p0UQ (a : ℚ) 2 (A - (c + 1)) : ℚ) : ZMod p) *
            (((c + 1 : ℕ) : ZMod p)⁻¹) *
            (((c + 1 : ℕ) : ZMod p)⁻¹)) := by
    rw [block_sum (p ^ k) A v (p ^ k - 1) _ (by omega)]
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c hc
      have hc' := Finset.mem_range.mp hc
      have hlt : c * p ^ k + (p ^ k - 1) < A * p ^ k + v :=
        lt_of_lt_of_le (ar_lt c _ _ A hc' (by omega)) (Nat.le_add_right _ _)
      have hu := EntryGoodness.p0U_good_general (p := p) (a := a)
        (2 * p ^ k) (A * p ^ k + v -
          (c * p ^ k + (p ^ k - 1) + 1))
      have hden : c * p ^ k + (p ^ k - 1) + 1 < p * p ^ k := by
        rw [ar_last c _ hq]
        exact Nat.mul_lt_mul_of_pos_right (by omega) hq
      have hd := EntryGoodness.q_div_good k
        (c * p ^ k + (p ^ k - 1) + 1) (by omega) hden
      rw [Rat.cast_mul_of_ne_zero
          (natCast_ne_zero_of_coprime ((GoodP p).mul_mem hu hd))
          (natCast_ne_zero_of_coprime hd),
        Rat.cast_mul_of_ne_zero
          (natCast_ne_zero_of_coprime
            (EntryGoodness.p0U_good_general (p := p) (a := a) _ _))
          (natCast_ne_zero_of_coprime hd),
        ar_shift A c _ v hc' hq, ar_last c _ hq,
        p0U_residue_lucas_M4 (p := p) a (A - (c + 1)) k v hv,
        EntryGoodness.qdiv_cast_unit_generic k (c + 1) (by omega) (by omega)]
      ring
    · intro c hc t ht htt
      have ht1 : t + 1 < p ^ k := by omega
      have hlt : c * p ^ k + t < A * p ^ k :=
        ar_lt c t _ A (by omega) ht
      have hden : c * p ^ k + t + 1 < p * p ^ k := by
        have hcp : (c + 1) * p ^ k < p * p ^ k :=
          Nat.mul_lt_mul_of_pos_right (by omega) hq
        omega
      have hu := EntryGoodness.p0U_good_general (p := p) (a := a)
        (2 * p ^ k) (A * p ^ k + v - (c * p ^ k + t + 1))
      have hd := EntryGoodness.q_div_good k (c * p ^ k + t + 1)
        (by omega) hden
      rw [Rat.cast_mul_of_ne_zero
          (natCast_ne_zero_of_coprime ((GoodP p).mul_mem hu hd))
          (natCast_ne_zero_of_coprime hd),
        Rat.cast_mul_of_ne_zero
          (natCast_ne_zero_of_coprime
            (EntryGoodness.p0U_good_general (p := p) (a := a) _ _))
          (natCast_ne_zero_of_coprime hd),
        EntryGoodness.qdiv_cast_zero_generic k _ (by omega) hden
          (not_dvd_of_rem (m := c) (x := t + 1) (by ring) (by omega) ht1),
        mul_zero]
    · intro t ht
      have ht1 : t + 1 < p ^ k := by omega
      have hden : A * p ^ k + t + 1 < p * p ^ k := by
        have hAp : (A + 1) * p ^ k < p * p ^ k :=
          Nat.mul_lt_mul_of_pos_right (by omega) hq
        omega
      have hu := EntryGoodness.p0U_good_general (p := p) (a := a)
        (2 * p ^ k) (A * p ^ k + v - (A * p ^ k + t + 1))
      have hd := EntryGoodness.q_div_good k (A * p ^ k + t + 1)
        (by omega) hden
      rw [Rat.cast_mul_of_ne_zero
          (natCast_ne_zero_of_coprime ((GoodP p).mul_mem hu hd))
          (natCast_ne_zero_of_coprime hd),
        Rat.cast_mul_of_ne_zero
          (natCast_ne_zero_of_coprime
            (EntryGoodness.p0U_good_general (p := p) (a := a) _ _))
          (natCast_ne_zero_of_coprime hd),
        EntryGoodness.qdiv_cast_zero_generic k _ (by omega) hden
          (not_dvd_of_rem (m := A) (x := t + 1) (by ring) (by omega) ht1),
        mul_zero]
  have hS2 :
      (∑ s ∈ Finset.range (2 * p ^ k),
        ((genericB2 a (2 * p ^ k) (A * p ^ k + v) s *
          (qRatP p k / ((s + 1 : ℕ) : ℚ)) *
          genericBI p a k s : ℚ) : ZMod p)) =
      (a : ZMod p) ^ v *
        ((a : ZMod p) ^ A * ∑ c ∈ Finset.range 2,
          (-1 : ZMod p) ^ (c + 1) *
            ((Nat.choose (A + 2) (2 - (c + 1)) : ℕ) : ZMod p) *
            (((c + 1 : ℕ) : ZMod p)⁻¹) *
            ∑ d ∈ Finset.range c,
              ((p0Q (a : ℚ) (d + 1) : ℚ) : ZMod p) *
                (((d + 1 : ℕ) : ZMod p)⁻¹)) := by
    rw [block_sum_full (p ^ k) (p ^ k - 1) _ (by omega) 2]
    · rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c hc
      have hc' := Finset.mem_range.mp hc
      have hlt : c * p ^ k + (p ^ k - 1) < 2 * p ^ k :=
        ar_lt c _ _ 2 hc' (by omega)
      have hB := cast_genericB2_block (p := p) a hp2 k A v c hv hc'
      have hBI := cast_genericBI_block (p := p) a hp2 hunit k c hc'
      have hBgood := genericB2_good (p := p) a (2 * p ^ k)
        (A * p ^ k + v) (c * p ^ k + (p ^ k - 1))
      have hBIgood := genericBI_good (p := p) a hunit k
        (c * p ^ k + (p ^ k - 1)) (by omega)
      have hden : c * p ^ k + (p ^ k - 1) + 1 < p * p ^ k := by
        rw [ar_last c _ hq]
        exact Nat.mul_lt_mul_of_pos_right (by omega) hq
      have hd := EntryGoodness.q_div_good k
        (c * p ^ k + (p ^ k - 1) + 1) (by omega) hden
      rw [Rat.cast_mul_of_ne_zero
          (natCast_ne_zero_of_coprime
            ((GoodP p).mul_mem hBgood hd))
          (natCast_ne_zero_of_coprime hBIgood),
        Rat.cast_mul_of_ne_zero
          (natCast_ne_zero_of_coprime hBgood)
          (natCast_ne_zero_of_coprime hd),
        hB, ar_last c _ hq,
        EntryGoodness.qdiv_cast_unit_generic k (c + 1) (by omega) (by omega),
        hBI]
      ring
    · intro c hc t ht htt
      have ht1 : t + 1 < p ^ k := by omega
      have hBgood := genericB2_good (p := p) a (2 * p ^ k)
        (A * p ^ k + v) (c * p ^ k + t)
      have hcp : (c + 1) * p ^ k < p * p ^ k :=
        Nat.mul_lt_mul_of_pos_right (by omega) hq
      have hcs : c * p ^ k + t < p * p ^ k := by
        have hlt : c * p ^ k + t < (c + 1) * p ^ k := by
          calc
            c * p ^ k + t < c * p ^ k + p ^ k :=
              Nat.add_lt_add_left ht _
            _ = (c + 1) * p ^ k := by ring
        exact lt_trans hlt hcp
      have hBIgood := genericBI_good (p := p) a hunit k
        (c * p ^ k + t) hcs
      have hden : c * p ^ k + t + 1 < p * p ^ k := by
        have htle : t + 1 ≤ p ^ k := Nat.succ_le_of_lt ht
        have hle : c * p ^ k + t + 1 ≤ (c + 1) * p ^ k := by
          calc
            c * p ^ k + t + 1 = c * p ^ k + (t + 1) := by omega
            _ ≤ c * p ^ k + p ^ k := Nat.add_le_add_left htle _
            _ = (c + 1) * p ^ k := by ring
        exact lt_of_le_of_lt hle hcp
      have hd := EntryGoodness.q_div_good k (c * p ^ k + t + 1)
        (by omega) hden
      rw [Rat.cast_mul_of_ne_zero
          (natCast_ne_zero_of_coprime
            ((GoodP p).mul_mem hBgood hd))
          (natCast_ne_zero_of_coprime hBIgood),
        Rat.cast_mul_of_ne_zero
          (natCast_ne_zero_of_coprime hBgood)
          (natCast_ne_zero_of_coprime hd),
        EntryGoodness.qdiv_cast_zero_generic k _ (by omega) hden
          (not_dvd_of_rem (m := c) (x := t + 1) (by ring) (by omega) ht1),
        mul_zero, zero_mul]
  rw [hS1, hS2, genericYBB]
  ring

end
end Li2Lean.P0.PositiveTower

#print axioms Li2Lean.P0.PositiveTower.generic_qqBB_decomp
#print axioms Li2Lean.P0.PositiveTower.cast_genericB2_block
#print axioms Li2Lean.P0.PositiveTower.cast_genericBI_block
#print axioms Li2Lean.P0.PositiveTower.cast_generic_qqBB
