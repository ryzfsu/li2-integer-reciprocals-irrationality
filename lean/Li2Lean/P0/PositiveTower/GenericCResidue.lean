/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.PositiveTower.GenericScaledDenominator
import Li2Lean.P0.PositiveTower.GenericUResidue

namespace Li2Lean.P0.PositiveTower

noncomputable section

open Li2Lean
open EntryGoodness

variable {p : ℕ} [Fact (Nat.Prime p)]

private lemma qdiff_cast_zero_generic (k i j : ℕ) (hij : i ≠ j)
    (hmod : i % p ^ k ≠ j % p ^ k)
    (hbound : max i j < p * p ^ k) :
    ((qRatP p k / ((j : ℚ) - (i : ℚ)) : ℚ) : ZMod p) = 0 := by
  rcases Nat.lt_or_gt_of_ne hij with hlt | hlt
  · have hcast : (j : ℚ) - (i : ℚ) = ((j - i : ℕ) : ℚ) := by
      rw [Nat.cast_sub hlt.le]
    rw [hcast]
    apply qdiv_cast_zero_generic k (j - i) (Nat.sub_pos_of_lt hlt)
    · exact lt_of_le_of_lt (Nat.sub_le _ _)
        (lt_of_le_of_lt (Nat.le_max_right _ _) hbound)
    · intro hdvd
      apply hmod
      exact (Nat.modEq_iff_dvd' hlt.le).mpr hdvd
  · have hcast : (j : ℚ) - (i : ℚ) = -((i - j : ℕ) : ℚ) := by
      rw [Nat.cast_sub hlt.le]
      ring
    rw [hcast, div_neg, Rat.cast_neg]
    rw [qdiv_cast_zero_generic k (i - j) (Nat.sub_pos_of_lt hlt)]
    · simp
    · exact lt_of_le_of_lt (Nat.sub_le _ _)
        (lt_of_le_of_lt (Nat.le_max_left _ _) hbound)
    · intro hdvd
      apply hmod
      exact ((Nat.modEq_iff_dvd' hlt.le).mpr hdvd).symm

private lemma qdiff_cast_unit_generic (k i j v : ℕ)
    (hij : i ≠ j) (hi : i < p) (hj : j < p) :
    ((qRatP p k /
      (((j * p ^ k + v : ℕ) : ℚ) - ((i * p ^ k + v : ℕ) : ℚ)) : ℚ) : ZMod p) =
      ((((j : ℤ) - (i : ℤ) : ℤ) : ZMod p))⁻¹ := by
  rcases Nat.lt_or_gt_of_ne hij with hlt | hlt
  · have hcast :
        (((j * p ^ k + v : ℕ) : ℚ) - ((i * p ^ k + v : ℕ) : ℚ)) =
          (((j - i) * p ^ k : ℕ) : ℚ) := by
      push_cast
      rw [Nat.cast_sub hlt.le]
      ring
    rw [hcast, qdiv_cast_unit_generic k (j - i) (by omega) (by omega)]
    congr 1
    simp [Nat.cast_sub hlt.le]
  · have hcast :
        (((j * p ^ k + v : ℕ) : ℚ) - ((i * p ^ k + v : ℕ) : ℚ)) =
          -(((i - j) * p ^ k : ℕ) : ℚ) := by
      push_cast
      rw [Nat.cast_sub hlt.le]
      ring
    rw [hcast, div_neg, Rat.cast_neg,
      qdiv_cast_unit_generic k (i - j) (by omega) (by omega)]
    rw [show ((j : ℤ) - (i : ℤ) : ℤ) = -((i - j : ℕ) : ℤ) by
      rw [Nat.cast_sub hlt.le]
      ring]
    push_cast
    rw [inv_neg]

private lemma cast_source_c_diag (a : ℤ) (A : ℕ)
    (hA : A + 3 < p) :
    ((p0CQ (a : ℚ) 2 A A : ℚ) : ZMod p) =
      -((a : ZMod p) ^ A * (Nat.choose (A + 2) 2 : ZMod p)) *
        ∑ c ∈ Finset.range 2, ((A + c + 1 : ℕ) : ZMod p)⁻¹ := by
  unfold p0CQ
  rw [if_pos rfl]
  have hu : p0UQ (a : ℚ) 2 A ∈ GoodP p :=
    EntryGoodness.p0U_good_general (p := p) (a := a) 2 A
  have hterms : ∀ c ∈ Finset.range 2,
      ((A + c + 1 : ℕ) : ℚ)⁻¹ ∈ GoodP p := by
    intro c hc
    have hc' := Finset.mem_range.mp hc
    change Nat.Coprime (((((A + c + 1 : ℕ) : ℚ)⁻¹).den)) p
    rw [Rat.inv_natCast_den]
    have hpos : 0 < A + c + 1 := by omega
    simp only [if_neg (Nat.ne_of_gt hpos)]
    exact (Nat.coprime_of_lt_prime (Nat.ne_of_gt hpos) (by omega) Fact.out).symm
  have hsumgood : (∑ c ∈ Finset.range 2,
      ((A + c + 1 : ℕ) : ℚ)⁻¹) ∈ GoodP p := by
    apply (GoodP p).sum_mem
    intro c hc
    exact hterms c hc
  have hsum_form :
      (∑ s ∈ Finset.range 2, (A + s + 1 : ℚ)⁻¹) =
        ∑ c ∈ Finset.range 2, ((A + c + 1 : ℕ) : ℚ)⁻¹ := by
    apply Finset.sum_congr rfl
    intro c hc
    norm_num [Nat.cast_add, Nat.cast_one]
  rw [hsum_form]
  have hneg :
      -p0UQ (a : ℚ) 2 A *
          (∑ c ∈ Finset.range 2, ((A + c + 1 : ℕ) : ℚ)⁻¹) =
        -(p0UQ (a : ℚ) 2 A *
          (∑ c ∈ Finset.range 2, ((A + c + 1 : ℕ) : ℚ)⁻¹)) := by ring
  have hu0 :
      ((p0UQ (a : ℚ) 2 A : ℚ) : ZMod p) =
        (a : ZMod p) ^ A * (Nat.choose (A + 2) 2 : ZMod p) := by
    have h := Li2Lean.P0.ScaledLucas.cast_U_generic p a 2 0 A 0 (by simp)
    simpa using h
  rw [hneg, Rat.cast_neg, Rat.cast_mul_of_ne_zero (natCast_ne_zero_of_coprime hu)
    (natCast_ne_zero_of_coprime hsumgood),
    hu0,
    EntryGoodness.ratCast_sum_good (p := p) (Finset.range 2)
      (fun c => ((A + c + 1 : ℕ) : ℚ)⁻¹) hterms]
  have hsum_cast :
      (∑ i ∈ Finset.range 2,
        ((((A + i + 1 : ℕ) : ℚ)⁻¹ : ℚ) : ZMod p)) =
        ∑ c ∈ Finset.range 2, ((A + c + 1 : ℕ) : ZMod p)⁻¹ := by
    apply Finset.sum_congr rfl
    intro c hc
    have hc' := Finset.mem_range.mp hc
    have hcast := qdiff_cast_unit_generic (p := p) 0 0 (A + c + 1) 0
      (by omega) (by omega) (by omega)
    simpa [qRatP] using hcast
  rw [hsum_cast]
  ring

/-! Off-diagonal C entries are the remaining C half of the Lucas block. -/
theorem qC_off_residue_M4 (a : ℤ) (k A b v w : ℕ)
    (hunit : Nat.Coprime (a - 1).natAbs p)
    (hA : A + 1 < p) (hb : b < p) (hAb : A + 1 ≠ b)
    (hv : v < p ^ k) (hw : w < p ^ k) :
    ((qRatP p k * p0CQ (a : ℚ) (2 * p ^ k)
      ((A + 1) * p ^ k + v) (b * p ^ k + w) : ℚ) : ZMod p) =
      if v = w then
        (a : ZMod p) ^ v *
          ((p0CQ (a : ℚ) 2 (A + 1) b : ℚ) : ZMod p)
      else 0 := by
  have hq : 0 < p ^ k := pow_pos (Fact.out : Nat.Prime p).pos _
  have hi : (A + 1) * p ^ k + v < p * p ^ k := by
    calc
      (A + 1) * p ^ k + v < (A + 1) * p ^ k + p ^ k :=
        Nat.add_lt_add_left hv _
      _ = (A + 2) * p ^ k := by ring
      _ ≤ p * p ^ k := Nat.mul_le_mul_right _ (by omega)
  have hj : b * p ^ k + w < p * p ^ k := by
    calc
      b * p ^ k + w < b * p ^ k + p ^ k :=
        Nat.add_lt_add_left hw _
      _ = (b + 1) * p ^ k := by ring
      _ ≤ p * p ^ k := Nat.mul_le_mul_right _ (by omega)
  by_cases hvw : v = w
  · subst w
    have hidx : (A + 1) * p ^ k + v ≠ b * p ^ k + v := by
      intro h
      apply hAb
      exact Nat.eq_of_mul_eq_mul_right hq (by omega)
    rw [if_pos rfl, qC_off_decomp_generic (a := (a : ℚ))
      (k := k) (g := 2 * p ^ k)
      (i := (A + 1) * p ^ k + v) (j := b * p ^ k + v) hidx]
    have hu1 := EntryGoodness.p0U_good_general (p := p) (a := a)
      (2 * p ^ k) ((A + 1) * p ^ k + v)
    have hu2 := EntryGoodness.p0U_good_general (p := p) (a := a)
      (2 * p ^ k) (b * p ^ k + v)
    have hratio := EntryGoodness.q_div_diff_good k
      ((A + 1) * p ^ k + v) (b * p ^ k + v) hidx (max_lt hi hj)
    rw [Rat.cast_mul_of_ne_zero
      (natCast_ne_zero_of_coprime ((GoodP p).sub_mem hu1 hu2))
      (natCast_ne_zero_of_coprime hratio),
      Rat.cast_sub_of_ne_zero (natCast_ne_zero_of_coprime hu1)
        (natCast_ne_zero_of_coprime hu2),
      p0U_residue_lucas_M4 (p := p) a (A + 1) k v hv,
      p0U_residue_lucas_M4 (p := p) a b k v hv,
      qdiff_cast_unit_generic (p := p) k (A + 1) b v hAb hA hb]
    have hsource_cast :
        ((p0CQ (a : ℚ) 2 (A + 1) b : ℚ) : ZMod p) =
          (((p0UQ (a : ℚ) 2 (A + 1) : ℚ) : ZMod p) -
            ((p0UQ (a : ℚ) 2 b : ℚ) : ZMod p)) *
            ((((b : ℤ) - (A + 1 : ℕ) : ℤ) : ZMod p))⁻¹ := by
      unfold p0CQ
      rw [if_neg hAb]
      have hbase1 := EntryGoodness.p0U_good_general (p := p) (a := a) 2 (A + 1)
      have hbase2 := EntryGoodness.p0U_good_general (p := p) (a := a) 2 b
      have hden :
          (((b : ℚ) - ((A + 1 : ℕ) : ℚ))⁻¹) ∈ GoodP p := by
        have hbound : max (A + 1) b < p * p ^ 0 := by
          simpa using (max_lt hA hb)
        have hratio := EntryGoodness.q_div_diff_good (p := p) 0
          (A + 1) b hAb hbound
        simpa [qRatP, one_div] using hratio
      rw [div_eq_mul_inv, Rat.cast_mul_of_ne_zero
        (natCast_ne_zero_of_coprime ((GoodP p).sub_mem hbase1 hbase2))
        (natCast_ne_zero_of_coprime hden),
        Rat.cast_sub_of_ne_zero (natCast_ne_zero_of_coprime hbase1)
          (natCast_ne_zero_of_coprime hbase2)]
      congr 1
      simpa [qRatP] using
        (qdiff_cast_unit_generic (p := p) 0 (A + 1) b 0 hAb hA hb)
    rw [hsource_cast]
    ring
  · rw [if_neg hvw, qC_off_decomp_generic (a := (a : ℚ))
      (k := k) (g := 2 * p ^ k)
      (i := (A + 1) * p ^ k + v) (j := b * p ^ k + w)
      (by
        intro h
        apply hvw
        have hmod := congrArg (fun n : ℕ => n % p ^ k) h
        simpa [ScaledLucas.mod_of_decomp hv,
          ScaledLucas.mod_of_decomp hw] using hmod)]
    have hu1 := EntryGoodness.p0U_good_general (p := p) (a := a)
      (2 * p ^ k) ((A + 1) * p ^ k + v)
    have hu2 := EntryGoodness.p0U_good_general (p := p) (a := a)
      (2 * p ^ k) (b * p ^ k + w)
    have hidx : (A + 1) * p ^ k + v ≠ b * p ^ k + w := by
      intro h
      apply hvw
      have hmod := congrArg (fun n : ℕ => n % p ^ k) h
      simpa [ScaledLucas.mod_of_decomp hv,
        ScaledLucas.mod_of_decomp hw] using hmod
    have hratio := EntryGoodness.q_div_diff_good k
      ((A + 1) * p ^ k + v) (b * p ^ k + w) hidx (max_lt hi hj)
    rw [Rat.cast_mul_of_ne_zero
      (natCast_ne_zero_of_coprime ((GoodP p).sub_mem hu1 hu2))
      (natCast_ne_zero_of_coprime hratio),
      Rat.cast_sub_of_ne_zero (natCast_ne_zero_of_coprime hu1)
        (natCast_ne_zero_of_coprime hu2),
      qdiff_cast_zero_generic (p := p) k
        ((A + 1) * p ^ k + v) (b * p ^ k + w) hidx
        (by
          intro hmod
          apply hvw
          simpa [ScaledLucas.mod_of_decomp hv,
            ScaledLucas.mod_of_decomp hw] using hmod)
        (by omega),
      mul_zero]

end
end Li2Lean.P0.PositiveTower
