/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.PositiveTower.GenericQResidue
import Li2Lean.P0.PositiveTower.GenericUResidue
import Li2Lean.P0.PositiveTower.GenericScaledDenominator

namespace Li2Lean.P0.PositiveTower

noncomputable section

open Li2Lean
open EntryGoodness
open Li2Lean.P0.ScaledLucas

variable {p : ℕ} [Fact (Nat.Prime p)]

private def genericT2 (a : ℤ) (g i s : ℕ) : ℚ :=
  (a : ℚ) ^ i * (-1 : ℚ) ^ s *
    (Nat.choose (i + g) (g - (s + 1)) : ℚ) * p0Q (a : ℚ) (s + 1)

private lemma genericT2_good (a : ℤ) (hunit : Nat.Coprime (a - 1).natAbs p)
    (g i s : ℕ) : genericT2 a g i s ∈ GoodP p := by
  unfold genericT2
  exact (GoodP p).mul_mem
    ((GoodP p).mul_mem
      ((GoodP p).mul_mem
        ((GoodP p).pow_mem (EntryGoodness.intRat_good (p := p) a) i)
        ((GoodP p).pow_mem (EntryGoodness.intRat_good (p := p) (-1)) s))
      (EntryGoodness.natRat_good (p := p) _))
    (EntryGoodness.p0Q_good_general (p := p) (a := a) hunit _)

lemma generic_qT_decomp (a : ℤ) (k g i : ℕ) :
    qRatP p k * p0TQ (a : ℚ) g i =
      (∑ r ∈ Finset.range i,
        p0UQ (a : ℚ) g (i - (r + 1)) *
          (qRatP p k / ((r + 1 : ℕ) : ℚ))) +
      ∑ s ∈ Finset.range g,
        genericT2 a g i s * (qRatP p k / ((s + 1 : ℕ) : ℚ)) := by
  unfold p0TQ
  rw [mul_add]
  congr 1
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    push_cast
    ring
  · rw [← mul_assoc, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    simp only [genericT2]
    push_cast
    ring

private lemma generic_odd_pow (hp10 : 10 < p) (k : ℕ) : Odd (p ^ k) := by
  have hpodd : Odd p := by
    exact (Nat.Prime.odd_of_ne_two (Fact.out) (by omega))
  exact Odd.pow hpodd

lemma choose_pow_add_mul_modEq {p k u d r : ℕ} [Fact (Nat.Prime p)]
    (hr : r < p ^ k) :
    Nat.choose (u * p ^ k + r) (d * p ^ k) ≡
      Nat.choose u d [MOD p] := by
  induction k generalizing u d r with
  | zero =>
      have hr0 : r = 0 := by simpa using hr
      subst r
      simpa using (Nat.ModEq.refl (Nat.choose u d))
  | succ k ih =>
      have hpP : Nat.Prime p := Fact.out
      have hp : 0 < p := hpP.pos
      have hmod : (u * p ^ k.succ + r) % p = r % p := by
        simp [pow_succ, Nat.add_mod, Nat.mul_mod]
      have hkm : (d * p ^ k.succ) % p = 0 := by
        simp [pow_succ, Nat.mul_mod]
      have hdiv : (u * p ^ k.succ + r) / p =
          u * p ^ k + r / p := by
        calc
          (u * p ^ k.succ + r) / p = (r + p * (u * p ^ k)) / p := by
            rw [pow_succ]
            congr 1
            ring
          _ = r / p + u * p ^ k := Nat.add_mul_div_left r (u * p ^ k) hp
          _ = u * p ^ k + r / p := Nat.add_comm _ _
      have hdivk : (d * p ^ k.succ) / p = d * p ^ k := by
        calc
          (d * p ^ k.succ) / p = (p * (d * p ^ k)) / p := by
            rw [pow_succ]
            congr 1
            ring
          _ = d * p ^ k := Nat.mul_div_right _ hp
      have hrdiv : r / p < p ^ k :=
        (Nat.div_lt_iff_lt_mul hp).2 (by
          simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using hr)
      have hLucas := Choose.choose_modEq_choose_mod_mul_choose_div_nat
        (n := u * p ^ k.succ + r) (k := d * p ^ k.succ) (p := p)
      have hLucas' :
          Nat.choose (u * p ^ k.succ + r) (d * p ^ k.succ) ≡
            Nat.choose ((u * p ^ k.succ + r) / p)
              ((d * p ^ k.succ) / p) [MOD p] := by
        rw [hmod, hkm] at hLucas
        simpa using hLucas
      rw [hdiv, hdivk] at hLucas'
      exact hLucas'.trans (ih hrdiv)

lemma p0Q_scaled_residue_generic (a : ℤ)
    (hunit : Nat.Coprime (a - 1).natAbs p)
    (k c : ℕ) :
    ((p0Q (a : ℚ) ((c + 1) * p ^ k) : ℚ) : ZMod p) =
      ((p0Q (a : ℚ) (c + 1) : ℚ) : ZMod p) := by
  have hInv : ((a - 1 : ℤ) : ℚ)⁻¹ ∈ GoodP p := by
    change Nat.Coprime (((((a - 1 : ℤ) : ℚ)⁻¹).den)) p
    rw [Rat.inv_intCast_den]
    split_ifs
    · simp
    · exact hunit
  have hU : (a : ℚ) * ((a - 1 : ℤ) : ℚ)⁻¹ ∈ GoodP p :=
    (GoodP p).mul_mem (EntryGoodness.intRat_good (p := p) a) hInv
  let U : GoodP p := ⟨(a : ℚ) * ((a - 1 : ℤ) : ℚ)⁻¹, hU⟩
  have hQ (s : ℕ) : p0Q (a : ℚ) s ∈ GoodP p :=
    EntryGoodness.p0Q_good_general (p := p) (a := a) hunit s
  have hrep (s : ℕ) :
      (⟨p0Q (a : ℚ) s, hQ s⟩ : GoodP p) = U ^ s - 1 := by
    ext
    simp [U, p0Q, div_eq_mul_inv, Int.cast_sub, Int.cast_one]
  have hpowq (x : ZMod p) : x ^ p ^ k = x := by
    induction k with
    | zero => simp
    | succ k ih =>
        rw [pow_succ, pow_mul, ih]
        exact ZMod.pow_card x
  have hres (s : ℕ) :
      residueHomP p (U ^ (s * p ^ k) - 1) =
        residueHomP p (U ^ s - 1) := by
    rw [map_sub, map_sub, map_pow, map_pow, pow_mul, hpowq]
  change residueHomP p ⟨p0Q (a : ℚ) ((c + 1) * p ^ k), hQ _⟩ =
    residueHomP p ⟨p0Q (a : ℚ) (c + 1), hQ _⟩
  rw [hrep, hrep, hres]

lemma generic_T2_block (a : ℤ) (hp10 : 10 < p)
    (hunit : Nat.Coprime (a - 1).natAbs p)
    (k A v c : ℕ) (hA : A + 2 < p) (hc : c < 2)
    (hv : v < p ^ k) :
    ((genericT2 a (2 * p ^ k) (A * p ^ k + v)
      (c * p ^ k + (p ^ k - 1)) : ℚ) : ZMod p) =
      (a : ZMod p) ^ v *
        ((genericT2 a 2 A c : ℚ) : ZMod p) := by
  have hq : 0 < p ^ k := pow_pos (Fact.out : Nat.Prime p).pos _
  have hbig : c * p ^ k + (p ^ k - 1) + 1 = (c + 1) * p ^ k := by
    simpa using ar_last c (p ^ k) hq
  have harg : 2 * p ^ k - (c * p ^ k + (p ^ k - 1) + 1) =
      (2 - (c + 1)) * p ^ k := by
    rw [hbig, ← Nat.sub_mul]
  unfold genericT2
  have hpowBig : (a : ℚ) ^ (A * p ^ k + v) ∈ GoodP p :=
    (GoodP p).pow_mem (EntryGoodness.intRat_good (p := p) a) _
  have hchooseBig :
      (Nat.choose (A * p ^ k + v + 2 * p ^ k)
        (2 * p ^ k - (c * p ^ k + (p ^ k - 1) + 1)) : ℚ) ∈ GoodP p :=
    EntryGoodness.natRat_good (p := p) _
  have hsignbig : ((-1 : ℚ) ^ (c * p ^ k + (p ^ k - 1))) ∈ GoodP p :=
    (GoodP p).pow_mem (EntryGoodness.intRat_good (p := p) (-1)) _
  have hQbig : p0Q (a : ℚ) (c * p ^ k + (p ^ k - 1) + 1) ∈ GoodP p :=
    EntryGoodness.p0Q_good_general (p := p) (a := a) hunit _
  have hqdiv : qRatP p k /
      ((c * p ^ k + (p ^ k - 1) + 1 : ℕ) : ℚ) ∈ GoodP p := by
    apply EntryGoodness.q_div_good
    · omega
    · rw [hbig]
      have : c + 1 < p := by omega
      exact Nat.mul_lt_mul_of_pos_right this hq
  have hprod :
      (a : ℚ) ^ (A * p ^ k + v) *
          (-1 : ℚ) ^ (c * p ^ k + (p ^ k - 1)) *
          (Nat.choose (A * p ^ k + v + 2 * p ^ k)
            (2 * p ^ k - (c * p ^ k + (p ^ k - 1) + 1)) : ℚ) ∈ GoodP p :=
    (GoodP p).mul_mem
      ((GoodP p).mul_mem hpowBig hsignbig) hchooseBig
  have hpre : (a : ℚ) ^ (A * p ^ k + v) *
          (-1 : ℚ) ^ (c * p ^ k + (p ^ k - 1)) ∈ GoodP p :=
    (GoodP p).mul_mem hpowBig hsignbig
  have hprod2 :
      (a : ℚ) ^ (A * p ^ k + v) *
          (-1 : ℚ) ^ (c * p ^ k + (p ^ k - 1)) *
          (Nat.choose (A * p ^ k + v + 2 * p ^ k)
            (2 * p ^ k - (c * p ^ k + (p ^ k - 1) + 1)) : ℚ) *
          p0Q (a : ℚ) (c * p ^ k + (p ^ k - 1) + 1) ∈ GoodP p :=
    (GoodP p).mul_mem hprod hQbig
  have hcast :=
    Rat.cast_mul_of_ne_zero (natCast_ne_zero_of_coprime hprod)
      (natCast_ne_zero_of_coprime hQbig)
  rw [hcast,
    Rat.cast_mul_of_ne_zero (natCast_ne_zero_of_coprime hpre)
      (natCast_ne_zero_of_coprime hchooseBig)]
  rw [Rat.cast_mul_of_ne_zero (natCast_ne_zero_of_coprime hpowBig)
      (natCast_ne_zero_of_coprime hsignbig), Rat.cast_natCast]
  have hpowSeed : (a : ℚ) ^ A ∈ GoodP p :=
    (GoodP p).pow_mem (EntryGoodness.intRat_good (p := p) a) _
  have hsignSeed : ((-1 : ℚ) ^ c) ∈ GoodP p :=
    (GoodP p).pow_mem (EntryGoodness.intRat_good (p := p) (-1)) _
  have hchooseSeed : ((Nat.choose (A + 2) (2 - (c + 1)) : ℕ) : ℚ) ∈ GoodP p :=
    EntryGoodness.natRat_good (p := p) _
  have hQSeed : p0Q (a : ℚ) (c + 1) ∈ GoodP p :=
    EntryGoodness.p0Q_good_general (p := p) (a := a) hunit _
  have hpreSeed : (a : ℚ) ^ A * (-1 : ℚ) ^ c ∈ GoodP p :=
    (GoodP p).mul_mem hpowSeed hsignSeed
  have hprodSeed : (a : ℚ) ^ A * (-1 : ℚ) ^ c *
      (Nat.choose (A + 2) (2 - (c + 1)) : ℚ) ∈ GoodP p :=
    (GoodP p).mul_mem hpreSeed hchooseSeed
  rw [Rat.cast_mul_of_ne_zero (natCast_ne_zero_of_coprime hprodSeed)
      (natCast_ne_zero_of_coprime hQSeed),
    Rat.cast_mul_of_ne_zero (natCast_ne_zero_of_coprime hpreSeed)
      (natCast_ne_zero_of_coprime hchooseSeed), Rat.cast_natCast]
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
  have hchoose_mod :
      ((Nat.choose (A * p ^ k + v + 2 * p ^ k)
        (2 * p ^ k - (c * p ^ k + (p ^ k - 1) + 1)) : ℕ) : ZMod p) =
      ((Nat.choose (A + 2) (2 - (c + 1)) : ℕ) : ZMod p) := by
    rw [harg]
    have hidx : A * p ^ k + v + 2 * p ^ k =
        (A + 2) * p ^ k + v := by ring
    rw [hidx]
    exact (ZMod.natCast_eq_natCast_iff _ _ p).mpr
      (choose_pow_add_mul_modEq (p := p) (k := k) (u := A + 2)
        (d := 2 - (c + 1)) (r := v) hv)
  have hsign_mod :
      (-1 : ZMod p) ^ (c * p ^ k + (p ^ k - 1)) =
        (-1 : ZMod p) ^ c := by
    rw [pow_add, Nat.mul_comm c (p ^ k), pow_mul,
      Odd.neg_one_pow (generic_odd_pow hp10 k),
      Even.neg_one_pow (Nat.Odd.sub_odd (generic_odd_pow hp10 k) odd_one),
      mul_one]
  have hQ_mod :
      ((p0Q (a : ℚ) (c * p ^ k + (p ^ k - 1) + 1) : ℚ) : ZMod p) =
        ((p0Q (a : ℚ) (c + 1) : ℚ) : ZMod p) := by
    rw [hbig]
    exact p0Q_scaled_residue_generic (p := p) a hunit k c
  rw [hpow_cast, hsign_cast, hchoose_mod, hQ_mod,
    Rat.cast_mul_of_ne_zero (natCast_ne_zero_of_coprime hpowSeed)
      (natCast_ne_zero_of_coprime hsignSeed)]
  rw [hpow_cast A, hsign_cast c]
  rw [show (a : ZMod p) ^ (A * p ^ k + v) =
      (a : ZMod p) ^ v * (a : ZMod p) ^ A by
        rw [Nat.add_comm, pow_add, Nat.mul_comm, pow_mul]
        simp]
  rw [hsign_mod]
  ring

def genericYT (a : ℤ) (A : ℕ) : ZMod p :=
  (∑ c ∈ Finset.range A,
      ((p0UQ (a : ℚ) 2 (A - (c + 1)) : ℚ) : ZMod p) *
        ((c + 1 : ℕ) : ZMod p)⁻¹) +
    (a : ZMod p) ^ A *
      ∑ c ∈ Finset.range 2,
        (-1 : ZMod p) ^ c *
          ((Nat.choose (A + 2) (2 - (c + 1)) : ℕ) : ZMod p) *
          ((p0Q (a : ℚ) (c + 1) : ℚ) : ZMod p) *
          ((c + 1 : ℕ) : ZMod p)⁻¹

lemma generic_T2_seed_cast (a : ℤ)
    (hunit : Nat.Coprime (a - 1).natAbs p) (A c : ℕ) :
    ((genericT2 a 2 A c : ℚ) : ZMod p) =
      (a : ZMod p) ^ A * (-1 : ZMod p) ^ c *
        ((Nat.choose (A + 2) (2 - (c + 1)) : ℕ) : ZMod p) *
        ((p0Q (a : ℚ) (c + 1) : ℚ) : ZMod p) := by
  unfold genericT2
  have hp : (a : ℚ) ^ A ∈ GoodP p :=
    (GoodP p).pow_mem (EntryGoodness.intRat_good (p := p) a) _
  have hs : (-1 : ℚ) ^ c ∈ GoodP p :=
    (GoodP p).pow_mem (EntryGoodness.intRat_good (p := p) (-1)) _
  have hc : ((Nat.choose (A + 2) (2 - (c + 1)) : ℕ) : ℚ) ∈ GoodP p :=
    EntryGoodness.natRat_good (p := p) _
  have hq : p0Q (a : ℚ) (c + 1) ∈ GoodP p :=
    EntryGoodness.p0Q_good_general (p := p) (a := a) hunit _
  have hpS : (a : ℚ) ^ A * (-1 : ℚ) ^ c ∈ GoodP p :=
    (GoodP p).mul_mem hp hs
  have hpC : (a : ℚ) ^ A * (-1 : ℚ) ^ c *
      (Nat.choose (A + 2) (2 - (c + 1)) : ℚ) ∈ GoodP p :=
    (GoodP p).mul_mem hpS hc
  rw [Rat.cast_mul_of_ne_zero (natCast_ne_zero_of_coprime hpC)
      (natCast_ne_zero_of_coprime hq),
    Rat.cast_mul_of_ne_zero (natCast_ne_zero_of_coprime hpS)
      (natCast_ne_zero_of_coprime hc),
    Rat.cast_mul_of_ne_zero (natCast_ne_zero_of_coprime hp)
      (natCast_ne_zero_of_coprime hs),
    show (((a : ℚ) ^ A : ℚ) : ZMod p) = (a : ZMod p) ^ A by
      rw [show (a : ℚ) ^ A = ((a ^ A : ℤ) : ℚ) by norm_num,
        Rat.cast_intCast]; norm_num,
    show (((-1 : ℚ) ^ c : ℚ) : ZMod p) = (-1 : ZMod p) ^ c by
      rw [show (-1 : ℚ) ^ c = (((-1) ^ c : ℤ) : ℚ) by norm_num,
        Rat.cast_intCast]; norm_num,
    Rat.cast_natCast]

lemma generic_qT_residue_M4 (a : ℤ) (hp10 : 10 < p)
    (hunit : Nat.Coprime (a - 1).natAbs p)
    (k A v : ℕ) (hA : A + 2 < p) (hv : v < p ^ k) :
    ((qRatP p k * p0TQ (a : ℚ) (2 * p ^ k)
      (A * p ^ k + v) : ℚ) : ZMod p) =
      (a : ZMod p) ^ v * genericYT (p := p) a A := by
  have hq : 0 < p ^ k := pow_pos (Fact.out : Nat.Prime p).pos _
  have hiq : A * p ^ k + v < p * p ^ k := by
    exact ar_lt A v _ p (by omega) hv
  rw [generic_qT_decomp]
  have hm1 : ∀ r ∈ Finset.range (A * p ^ k + v),
      p0UQ (a : ℚ) (2 * p ^ k) (A * p ^ k + v - (r + 1)) *
        (qRatP p k / ((r + 1 : ℕ) : ℚ)) ∈ GoodP p := by
    intro r hr
    have hr' := Finset.mem_range.mp hr
    have hden : r + 1 < p * p ^ k := by omega
    exact (GoodP p).mul_mem
      (EntryGoodness.p0U_good_general (p := p) (a := a) _ _)
      (EntryGoodness.q_div_good k (r + 1) (by omega) hden)
  have hm2 : ∀ s ∈ Finset.range (2 * p ^ k),
      genericT2 a (2 * p ^ k) (A * p ^ k + v) s *
        (qRatP p k / ((s + 1 : ℕ) : ℚ)) ∈ GoodP p := by
    intro s hs
    have hs' := Finset.mem_range.mp hs
    have hden : s + 1 < p * p ^ k := by
      have h2q : 2 * p ^ k < p * p ^ k :=
        Nat.mul_lt_mul_of_pos_right (by omega) hq
      omega
    exact (GoodP p).mul_mem
      (genericT2_good (p := p) a hunit _ _ _)
      (EntryGoodness.q_div_good k (s + 1) (by omega) hden)
  rw [Rat.cast_add_of_ne_zero
      (natCast_ne_zero_of_coprime ((GoodP p).sum_mem hm1))
      (natCast_ne_zero_of_coprime ((GoodP p).sum_mem hm2)),
    EntryGoodness.ratCast_sum_good (Finset.range (A * p ^ k + v)) _ hm1,
    EntryGoodness.ratCast_sum_good (Finset.range (2 * p ^ k)) _ hm2]
  have hS1 :
      (∑ r ∈ Finset.range (A * p ^ k + v),
        ((p0UQ (a : ℚ) (2 * p ^ k) (A * p ^ k + v - (r + 1)) *
          (qRatP p k / ((r + 1 : ℕ) : ℚ)) : ℚ) : ZMod p)) =
      (a : ZMod p) ^ v *
        (∑ c ∈ Finset.range A,
          ((p0UQ (a : ℚ) 2 (A - (c + 1)) : ℚ) : ZMod p) *
            ((c + 1 : ℕ) : ZMod p)⁻¹) := by
    rw [block_sum (p ^ k) A v (p ^ k - 1) _ (by omega)]
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c hc
      have hc' := Finset.mem_range.mp hc
      have hlt : c * p ^ k + (p ^ k - 1) < A * p ^ k + v :=
        lt_of_lt_of_le (ar_lt c _ _ A hc' (by omega)) (Nat.le_add_right _ _)
      have hu := EntryGoodness.p0U_good_general (p := p) (a := a)
        (2 * p ^ k) (A * p ^ k + v - (c * p ^ k + (p ^ k - 1) + 1))
      have hden : c * p ^ k + (p ^ k - 1) + 1 < p * p ^ k := by
        rw [ar_last c _ hq]
        exact Nat.mul_lt_mul_of_pos_right (by omega) hq
      have hd := EntryGoodness.q_div_good k
        (c * p ^ k + (p ^ k - 1) + 1) (by omega) hden
      rw [Rat.cast_mul_of_ne_zero (natCast_ne_zero_of_coprime hu)
          (natCast_ne_zero_of_coprime hd),
        ar_shift A c _ v hc' hq, ar_last c _ hq,
        p0U_residue_lucas_M4 (p := p) a (A - (c + 1)) k v hv,
        EntryGoodness.qdiv_cast_unit_generic k (c + 1) (by omega) (by omega)]
      ring
    · intro c hc t ht htt
      have hlt : c * p ^ k + t < A * p ^ k := ar_lt c t _ A hc ht
      have ht1 : t + 1 < p ^ k := by omega
      have hu := EntryGoodness.p0U_good_general (p := p) (a := a)
        (2 * p ^ k) (A * p ^ k + v - (c * p ^ k + t + 1))
      have hAp : A * p ^ k < p * p ^ k :=
        Nat.mul_lt_mul_of_pos_right (by omega) hq
      have hden : c * p ^ k + t + 1 < p * p ^ k := by
        have hct : c * p ^ k + t < A * p ^ k := ar_lt c t _ A hc ht
        omega
      have hd := EntryGoodness.q_div_good k (c * p ^ k + t + 1)
        (by omega) hden
      rw [Rat.cast_mul_of_ne_zero (natCast_ne_zero_of_coprime hu)
          (natCast_ne_zero_of_coprime hd),
        EntryGoodness.qdiv_cast_zero_generic k _ (by omega) hden
          (ScaledLucas.not_dvd_of_rem (m := c) (x := t + 1)
            (by ring) (by omega) ht1),
        mul_zero]
    · intro t ht
      have ht1 : t + 1 < p ^ k := by omega
      have hu := EntryGoodness.p0U_good_general (p := p) (a := a)
        (2 * p ^ k) (A * p ^ k + v - (A * p ^ k + t + 1))
      have hden : A * p ^ k + t + 1 < p * p ^ k := by
        have hAp : (A + 1) * p ^ k < p * p ^ k :=
          Nat.mul_lt_mul_of_pos_right (by omega) hq
        have htq : t + 1 < p ^ k := by omega
        have : A * p ^ k + (t + 1) < (A + 1) * p ^ k :=
          ar_lt A (t + 1) _ (A + 1) (by omega) htq
        omega
      have hd := EntryGoodness.q_div_good k (A * p ^ k + t + 1)
        (by omega) hden
      rw [Rat.cast_mul_of_ne_zero (natCast_ne_zero_of_coprime hu)
          (natCast_ne_zero_of_coprime hd),
        EntryGoodness.qdiv_cast_zero_generic k _ (by omega) hden
          (ScaledLucas.not_dvd_of_rem (m := A) (x := t + 1)
            (by ring) (by omega) ht1),
        mul_zero]
  have hS2 :
      (∑ s ∈ Finset.range (2 * p ^ k),
        ((genericT2 a (2 * p ^ k) (A * p ^ k + v) s *
          (qRatP p k / ((s + 1 : ℕ) : ℚ)) : ℚ) : ZMod p)) =
      (a : ZMod p) ^ v *
        ((a : ZMod p) ^ A * ∑ c ∈ Finset.range 2,
          (-1 : ZMod p) ^ c *
            ((Nat.choose (A + 2) (2 - (c + 1)) : ℕ) : ZMod p) *
            ((p0Q (a : ℚ) (c + 1) : ℚ) : ZMod p) *
            ((c + 1 : ℕ) : ZMod p)⁻¹) := by
    rw [block_sum_full (p ^ k) (p ^ k - 1) _ (by omega) 2]
    · rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c hc
      have hc' := Finset.mem_range.mp hc
      have hlt : c * p ^ k + (p ^ k - 1) < 2 * p ^ k :=
        ar_lt c _ _ 2 hc' (by omega)
      have hT := generic_T2_block (p := p) a hp10 hunit k A v c hA hc' hv
      have hseed := generic_T2_seed_cast (p := p) a hunit A c
      have hTgood := genericT2_good (p := p) a hunit
        (2 * p ^ k) (A * p ^ k + v) (c * p ^ k + (p ^ k - 1))
      have hden : c * p ^ k + (p ^ k - 1) + 1 < p * p ^ k := by
        rw [ar_last c _ hq]
        exact Nat.mul_lt_mul_of_pos_right (by omega) hq
      have hd := EntryGoodness.q_div_good k
        (c * p ^ k + (p ^ k - 1) + 1) (by omega) hden
      rw [Rat.cast_mul_of_ne_zero (natCast_ne_zero_of_coprime hTgood)
          (natCast_ne_zero_of_coprime hd), hT, hseed,
        ar_last c _ hq,
        EntryGoodness.qdiv_cast_unit_generic k (c + 1) (by omega) (by omega)]
      ring
    · intro c hc t ht htt
      have ht1 : t + 1 < p ^ k := by omega
      have hTgood := genericT2_good (p := p) a hunit
        (2 * p ^ k) (A * p ^ k + v) (c * p ^ k + t)
      have hden : c * p ^ k + t + 1 < p * p ^ k := by
        have hct : c * p ^ k + t + 1 ≤ (c + 1) * p ^ k := by
          calc
            c * p ^ k + t + 1 = c * p ^ k + (t + 1) := by omega
            _ ≤ c * p ^ k + p ^ k :=
              Nat.add_le_add_left (Nat.le_of_lt ht1) _
            _ = (c + 1) * p ^ k := by ring
        have hcp : (c + 1) * p ^ k < p * p ^ k :=
          Nat.mul_lt_mul_of_pos_right (by omega) hq
        omega
      have hd := EntryGoodness.q_div_good k (c * p ^ k + t + 1)
        (by omega) hden
      rw [Rat.cast_mul_of_ne_zero (natCast_ne_zero_of_coprime hTgood)
          (natCast_ne_zero_of_coprime hd),
        EntryGoodness.qdiv_cast_zero_generic k _ (by omega) hden
          (ScaledLucas.not_dvd_of_rem (m := c) (x := t + 1)
            (by ring) (by omega) ht1),
        mul_zero]
  rw [hS1, hS2, genericYT]
  ring

end
end Li2Lean.P0.PositiveTower
