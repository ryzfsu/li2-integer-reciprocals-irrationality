/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B3.ActualFrobeniusCarrierBlocks
import Li2Lean.P0.PositiveTower.GenericScaledDenominator

namespace Li2Lean.B3

noncomputable section

open scoped BigOperators
open Li2Lean.V.SignedVFrobenius
open Li2Lean.P0.ScaledLucas
open Li2Lean.P0.PositiveTower
open Li2Lean.P0.PositiveTower.EntryGoodness

variable {p : ℕ} [Fact (Nat.Prime p)] (a : ℤ)

theorem qMomentT_decomp (p : ℕ) (a : ℤ) (k N : ℕ) :
    qRatP p k * V.vMomentT a N =
      ∑ r ∈ Finset.range N,
        (a : ℚ) ^ (N - (r + 1)) * (qRatP p k / ((r + 1 : ℕ) : ℚ)) := by
  unfold V.vMomentT
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [div_eq_mul_inv]
  ring

theorem qMomentT_term_good (a : ℤ) (k N r : ℕ)
    (hN : N < p * p ^ k) (hr : r ∈ Finset.range N) :
    (a : ℚ) ^ (N - (r + 1)) *
        (qRatP p k / ((r + 1 : ℕ) : ℚ)) ∈ GoodP p := by
  have hrlt : r < N := Finset.mem_range.mp hr
  exact (GoodP p).mul_mem
    ((GoodP p).pow_mem (intRat_good a) _)
    (q_div_good k (r + 1) (by omega) (by omega))

theorem q_mul_vMomentT_good (a : ℤ) (k N : ℕ)
    (hN : N < p * p ^ k) :
    qRatP p k * V.vMomentT a N ∈ GoodP p := by
  rw [qMomentT_decomp]
  exact (GoodP p).sum_mem
    (fun r hr => qMomentT_term_good a k N r hN hr)

theorem cast_int_pow_frob (p : ℕ) [Fact (Nat.Prime p)]
    (a : ℤ) (k A v : ℕ) :
    (((a : ℚ) ^ (A * p ^ k + v) : ℚ) : ZMod p) =
      (a : ZMod p) ^ v * (a : ZMod p) ^ A := by
  have hInt : ((a : ℚ) ^ (A * p ^ k + v)) =
      ((a ^ (A * p ^ k + v) : ℤ) : ℚ) := by
    push_cast
    rfl
  rw [hInt, Rat.cast_intCast, Int.cast_pow, pow_add,
    Nat.mul_comm A (p ^ k), pow_mul, ZMod.pow_card_pow, mul_comm]

theorem vMomentT_scaled_residue_sum (p : ℕ)
    [Fact (Nat.Prime p)] (a : ℤ) (k B v : ℕ)
    (hB : B < p) (hv : v < p ^ k) :
    ((qRatP p k * V.vMomentT a (B * p ^ k + v) : ℚ) : ZMod p) =
      (a : ZMod p) ^ v *
        ∑ c ∈ Finset.range B,
          (a : ZMod p) ^ (B - (c + 1)) *
            ((c + 1 : ℕ) : ZMod p)⁻¹ := by
  have hq : 0 < p ^ k := pow_pos (Fact.out : Nat.Prime p).pos k
  have hN : B * p ^ k + v < p * p ^ k := by
    calc
      B * p ^ k + v < B * p ^ k + p ^ k := Nat.add_lt_add_left hv _
      _ = (B + 1) * p ^ k := by ring
      _ ≤ p * p ^ k := Nat.mul_le_mul_right _ hB
  have hpow_good : ∀ m : ℕ, (a : ℚ) ^ m ∈ GoodP p :=
    fun m => (GoodP p).pow_mem (intRat_good a) m
  rw [qMomentT_decomp,
    ratCast_sum_good (Finset.range (B * p ^ k + v)) _
      (fun r hr => qMomentT_term_good a k (B * p ^ k + v) r hN hr)]
  rw [Li2Lean.P0.ScaledLucas.block_sum (p ^ k) B v (p ^ k - 1) _ (by omega)]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c hc
    have hc' : c < B := Finset.mem_range.mp hc
    have hlt : c * p ^ k + (p ^ k - 1) < B * p ^ k :=
      Li2Lean.P0.ScaledLucas.ar_lt c (p ^ k - 1) (p ^ k) B hc' (by omega)
    have hqdiv : qRatP p k /
        ((c * p ^ k + (p ^ k - 1) + 1 : ℕ) : ℚ) ∈ GoodP p :=
      q_div_good k _ (by omega) (by omega)
    rw [Rat.cast_mul_of_ne_zero
        (natCast_ne_zero_of_coprime (hpow_good _))
        (natCast_ne_zero_of_coprime hqdiv),
      Li2Lean.P0.ScaledLucas.ar_shift B c (p ^ k) v hc' hq,
      Li2Lean.P0.ScaledLucas.ar_last c (p ^ k) hq,
      cast_int_pow_frob p a k (B - (c + 1)) v,
      qdiv_cast_unit_generic k (c + 1) (by omega) (by omega)]
    ring
  · intro c hc t ht htt
    have hlt : c * p ^ k + t < B * p ^ k :=
      Li2Lean.P0.ScaledLucas.ar_lt c t (p ^ k) B hc ht
    have ht1 : t + 1 < p ^ k := by omega
    have hqdiv : qRatP p k /
        ((c * p ^ k + t + 1 : ℕ) : ℚ) ∈ GoodP p :=
      q_div_good k _ (by omega) (by omega)
    have hnd : ¬ p ^ k ∣ c * p ^ k + t + 1 :=
      Li2Lean.P0.ScaledLucas.not_dvd_of_rem (m := c) (x := t + 1)
        (by ring) (by omega) ht1
    rw [Rat.cast_mul_of_ne_zero
        (natCast_ne_zero_of_coprime (hpow_good _))
        (natCast_ne_zero_of_coprime hqdiv),
      qdiv_cast_zero_generic k (c * p ^ k + t + 1) (by omega) (by omega) hnd,
      mul_zero]
  · intro t ht
    have ht1 : t + 1 < p ^ k := by omega
    have hqdiv : qRatP p k /
        ((B * p ^ k + t + 1 : ℕ) : ℚ) ∈ GoodP p :=
      q_div_good k _ (by omega) (by omega)
    have hnd : ¬ p ^ k ∣ B * p ^ k + t + 1 :=
      Li2Lean.P0.ScaledLucas.not_dvd_of_rem (m := B) (x := t + 1)
        (by ring) (by omega) ht1
    rw [Rat.cast_mul_of_ne_zero
        (natCast_ne_zero_of_coprime (hpow_good _))
        (natCast_ne_zero_of_coprime hqdiv),
      qdiv_cast_zero_generic k (B * p ^ k + t + 1) (by omega) (by omega) hnd,
      mul_zero]

theorem vMomentT_seed_residue_sum (p : ℕ) [Fact (Nat.Prime p)]
    (a : ℤ) (B : ℕ) (hB : B < p) :
    ((V.vMomentT a B : ℚ) : ZMod p) =
      ∑ c ∈ Finset.range B,
        (a : ZMod p) ^ (B - (c + 1)) *
          ((c + 1 : ℕ) : ZMod p)⁻¹ := by
  have h0 := vMomentT_scaled_residue_sum p a 0 B 0 hB (by simp)
  simpa [qRatP] using h0

/-- N1-1 target: scaled signed-V first moment, block Lucas reduction. -/
theorem vMomentT_scaled_residue (k B v : ℕ) (hB : B < p) (hv : v < p ^ k) :
    (((p ^ k : ℕ) : ℚ) * V.vMomentT a (B * p ^ k + v)) ∈ GoodAt p ∧
    ((((p ^ k : ℕ) : ℚ) * V.vMomentT a (B * p ^ k + v) : ℚ) : ZMod p) =
      (a : ZMod p) ^ v * (V.vMomentT a B : ZMod p) := by
  have hN : B * p ^ k + v < p * p ^ k := by
    calc
      B * p ^ k + v < B * p ^ k + p ^ k := Nat.add_lt_add_left hv _
      _ = (B + 1) * p ^ k := by ring
      _ ≤ p * p ^ k := Nat.mul_le_mul_right _ hB
  have hgood : qRatP p k * V.vMomentT a (B * p ^ k + v) ∈ GoodP p :=
    q_mul_vMomentT_good a k (B * p ^ k + v) hN
  constructor
  · exact hgood
  · rw [show (((p ^ k : ℕ) : ℚ) * V.vMomentT a (B * p ^ k + v)) =
      qRatP p k * V.vMomentT a (B * p ^ k + v) from rfl,
    vMomentT_scaled_residue_sum p a k B v hB hv,
    vMomentT_seed_residue_sum p a B hB]

end
end Li2Lean.B3
