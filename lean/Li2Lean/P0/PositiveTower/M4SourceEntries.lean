/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.PositiveTower.ScaledMatrix
import Li2Lean.P0.PositiveTower.BlockDeterminantReduction
import Li2Lean.P0.PositiveTower.GenericCResidue
import Li2Lean.P0.PositiveTower.GenericTResidue
import Li2Lean.P0.PositiveTower.GenericBResidueFull

namespace Li2Lean.P0.PositiveTower

open Li2Lean
open Li2Lean.P0
open Li2Lean.P0.ScaledLucas
open EntryGoodness
open Matrix

noncomputable section

variable {p : ℕ} [Fact (Nat.Prime p)]

/-- The index coercion from the `(A,v)` product to the scaled M=4 matrix.
This is the definitional equality `8 * p^k = 2 * (4 * p^k)` used in
the v13 Lucas block decomposition (`nonvanishing.tex:200-214`). -/
def m4RowEquiv (k : ℕ) :
    Fin (8 * p ^ k) ≃ Fin (2 * (4 * p ^ k)) :=
  finCongr (by ring)

/-- The source M=4 entry residue at `T=0`, in numerator/denominator form. -/
def m4SourceResidue (a : ℤ) (A B : Fin 8) (p : ℕ) : ZMod p :=
  let x := (p0MatrixQ (a : ℚ) 4 A B).eval 0
  (x.num : ZMod p) * (x.den : ZMod p)⁻¹

/-! The `A` correction in a lower M=4 row is killed by the squared
prime-power factor.  The entry indices are arbitrary; this is the reusable
row-level fact used before the diagonal and off-diagonal B calculations. -/
theorem m4_b_row_aq_vanishes
    (a : ℤ) (k : ℕ) (r : ℚ)
    (hbound : r.den < p ^ k) (i j : ℕ) :
    (((qRatP p k)^2 * r * p0AQ (a : ℚ) (2 * p ^ k) i j : ℚ) : ZMod p) = 0 := by
  have hqr0 : (((qRatP p k) ^ 2 * r : ℚ) : ZMod p) = 0 := by
    simpa [qRatP] using (powP_sq_mul_rat_cast_eq_zero (P := p) k r hbound)
  have hqrg : (qRatP p k) ^ 2 * r ∈ GoodP p :=
    EntryGoodness.q_sq_mul_rat_good k r hbound
  have hAg : p0AQ (a : ℚ) (2 * p ^ k) i j ∈ GoodP p :=
    EntryGoodness.p0AQ_good (p := p) (a := a) _ _ _
  rw [show qRatP p k ^ 2 * r * p0AQ (a : ℚ) (2 * p ^ k) i j =
        (qRatP p k ^ 2 * r) * p0AQ (a : ℚ) (2 * p ^ k) i j by ring]
  rw [Rat.cast_mul_of_ne_zero (natCast_ne_zero_of_coprime hqrg)
      (natCast_ne_zero_of_coprime hAg), hqr0, zero_mul]

theorem m4_b_diagonal_source_entry
    (a : ℤ) (hp10 : 10 < p)
    (hunit : Nat.Coprime (a - 1).natAbs p)
    (k : ℕ) (r : ℚ) (hbound : r.den < p ^ k) (hk : 0 < k)
    (A B : Fin 8) (v : Fin (p ^ k))
    (hA : ¬ A.val < 4)
    (hBdiag : A.val - 3 = B.val) :
    (((towerScaledMatrixQ (p := p) (a := a) k r
        (m4RowEquiv (p := p) k ((@finProdFinEquiv 8 (p ^ k)) (A, v)))
        (m4RowEquiv (p := p) k ((@finProdFinEquiv 8 (p ^ k)) (B, v))) : ℚ) : ZMod p)) =
      (a : ZMod p) ^ v.val * m4SourceResidue a A B p := by
  have hA4 : A.val < 8 := A.isLt
  have hB4 : B.val < 8 := B.isLt
  have hqpos : 0 < p ^ k := pow_pos (Fact.out : Nat.Prime p).pos _
  have hv : v.val < p ^ k := v.isLt
  have hA3 : A.val - 3 + 3 ≤ p := by
    have hpge : 11 ≤ p := by omega
    omega
  have hA3' : A.val - 3 + 3 ≤ p := hA3
  have hB_eq : B.val = A.val - 3 := hBdiag.symm
  have hrowA : v.val + p ^ k * A.val ≥ 4 * p ^ k := by
    have hA4' : 4 ≤ A.val := by omega
    nlinarith
  have hvalA :
      (m4RowEquiv (p := p) k ((@finProdFinEquiv 8 (p ^ k)) (A, v))).val =
        A.val * p ^ k + v.val := by
    calc
      _ = v.val + p ^ k * A.val := by rfl
      _ = A.val * p ^ k + v.val := by ac_rfl
  have hvalB :
      (m4RowEquiv (p := p) k ((@finProdFinEquiv 8 (p ^ k)) (B, v))).val =
        B.val * p ^ k + v.val := by
    calc
      _ = v.val + p ^ k * B.val := by rfl
      _ = B.val * p ^ k + v.val := by ac_rfl
  have hi : 1 * p ^ k + (v.val + p ^ k * A.val - 4 * p ^ k) =
      (A.val - 3) * p ^ k + v.val := by
    have hA4' : 4 ≤ A.val := by omega
    have hAeq : A.val = (A.val - 4) + 4 := by omega
    rw [hAeq, Nat.mul_add]
    have hcancel : v.val + (p ^ k * (A.val - 4) + p ^ k * 4) -
        4 * p ^ k = v.val + p ^ k * (A.val - 4) := by
      have hq4 : p ^ k * 4 = 4 * p ^ k := by omega
      rw [hq4]
      omega
    rw [hcancel]
    have hA4sub : A.val - 4 + 4 - 3 = A.val - 3 := by omega
    rw [hA4sub]
    have hAminus : A.val - 3 = (A.val - 4) + 1 := by omega
    rw [hAminus, Nat.add_mul]
    ac_rfl
  have hrowA' : ¬ v.val + p ^ k * A.val < 4 * p ^ k := by omega
  have hrowA2 : ¬ A.val * p ^ k + v.val < 4 * p ^ k := by
    simpa [Nat.mul_comm, Nat.add_comm] using hrowA'
  have hi2 : 1 * p ^ k + (A.val * p ^ k + v.val - 4 * p ^ k) =
      (A.val - 3) * p ^ k + v.val := by
    simpa [Nat.mul_comm, Nat.add_comm] using hi
  unfold towerScaledMatrixQ
  simp only [hvalA, hvalB]
  simp only [if_neg hrowA2]
  rw [hi2]
  have hdiag_index : (A.val - 3) * p ^ k + v.val =
      B.val * p ^ k + v.val := by rw [hB_eq]
  rw [← hdiag_index]
  change (((((qRatP p k) ^ 2 * p0BQ (a : ℚ) (2 * p ^ k)
      ((A.val - 3) * p ^ k + v.val) ((A.val - 3) * p ^ k + v.val)) -
      (qRatP p k) ^ 2 * r * p0AQ (a : ℚ) (2 * p ^ k)
        ((A.val - 3) * p ^ k + v.val) ((A.val - 3) * p ^ k + v.val) : ℚ) : ZMod p)) =
    (a : ZMod p) ^ v.val * m4SourceResidue a A B p
  have hBB := cast_generic_qqBB (p := p) a (by omega) hunit k (A.val - 3) v
    (by omega) hv
  have hAQ :
      (((qRatP p k) ^ 2 * r * p0AQ (a : ℚ) (2 * p ^ k)
        ((A.val - 3) * p ^ k + v.val) (B.val * p ^ k + v.val) : ℚ) : ZMod p) = 0 := by
    rw [hB_eq]
    have hqr0 : (((qRatP p k) ^ 2 * r : ℚ) : ZMod p) = 0 := by
      simpa [qRatP] using (powP_sq_mul_rat_cast_eq_zero (P := p) k r hbound)
    have hqrg : (qRatP p k) ^ 2 * r ∈ GoodP p :=
      EntryGoodness.q_sq_mul_rat_good k r hbound
    have hAg : p0AQ (a : ℚ) (2 * p ^ k)
        ((A.val - 3) * p ^ k + v.val) ((A.val - 3) * p ^ k + v.val) ∈ GoodP p :=
      EntryGoodness.p0AQ_good (p := p) (a := a) _ _ _
    rw [show qRatP p k ^ 2 * r * p0AQ (a : ℚ) (2 * p ^ k)
        ((A.val - 3) * p ^ k + v.val) ((A.val - 3) * p ^ k + v.val) =
        (qRatP p k ^ 2 * r) * p0AQ (a : ℚ) (2 * p ^ k)
          ((A.val - 3) * p ^ k + v.val) ((A.val - 3) * p ^ k + v.val) by ring]
    rw [Rat.cast_mul_of_ne_zero (natCast_ne_zero_of_coprime hqrg)
      (natCast_ne_zero_of_coprime hAg), hqr0, zero_mul]
  rw [show B.val * p ^ k + v.val = (A.val - 3) * p ^ k + v.val by rw [hB_eq]] at hAQ
  have hidx_lt : (A.val - 3) * p ^ k + v.val < p * p ^ k := by
    have hA3one : A.val - 3 + 1 ≤ p := by omega
    calc
      (A.val - 3) * p ^ k + v.val < (A.val - 3) * p ^ k + p ^ k :=
        Nat.add_lt_add_left hv _
      _ = (A.val - 3 + 1) * p ^ k := by ring
      _ ≤ p * p ^ k := Nat.mul_le_mul_right _ hA3one
  have h2q : 2 * p ^ k < p * p ^ k := by
    exact Nat.mul_lt_mul_of_pos_right (by omega) hqpos
  simp only [p0BQ, ite_true]
  rw [Rat.cast_sub_of_ne_zero
    (natCast_ne_zero_of_coprime (EntryGoodness.q_sq_mul_p0BQQ_good (p := p) (a := a)
      hunit k (2 * p ^ k) ((A.val - 3) * p ^ k + v.val)
      hidx_lt h2q))
    (natCast_ne_zero_of_coprime
      ((GoodP p).mul_mem (EntryGoodness.q_sq_mul_rat_good (p := p) k r hbound)
        (EntryGoodness.p0AQ_good (p := p) (a := a) (2 * p ^ k)
          ((A.val - 3) * p ^ k + v.val) ((A.val - 3) * p ^ k + v.val))))]
  rw [hAQ, sub_zero]
  rw [hBB]
  have hsource := cast_generic_qqBB (p := p) a (by omega) hunit 0 (A.val - 3) 0
    (by omega) (by norm_num)
  have hrow : 1 + (A.val - 4) = A.val - 3 := by omega
  have hsource_eq : m4SourceResidue a A B p =
      ((p0BQQ (a : ℚ) 2 (A.val - 3) : ℚ) : ZMod p) := by
    unfold m4SourceResidue p0MatrixQ
    simp [p0BQ, hB_eq, hA, hrow, Rat.cast_def, div_eq_mul_inv]
  have hsource' :
      ((p0BQQ (a : ℚ) 2 (A.val - 3) : ℚ) : ZMod p) =
        genericYBB (p := p) a (A.val - 3) := by
    simpa [qRatP] using hsource
  rw [hsource_eq]
  rw [← hsource']

theorem m4_b_off_res_source_entry
    (a : ℤ) (hp10 : 10 < p)
    (hunit : Nat.Coprime (a - 1).natAbs p)
    (k : ℕ) (r : ℚ) (hbound : r.den < p ^ k)
    (A B : Fin 8) (v w : Fin (p ^ k))
    (hA : ¬ A.val < 4)
    (hvw : v ≠ w) :
    (((towerScaledMatrixQ (p := p) (a := a) k r
        (m4RowEquiv (p := p) k ((@finProdFinEquiv 8 (p ^ k)) (A, v)))
        (m4RowEquiv (p := p) k ((@finProdFinEquiv 8 (p ^ k)) (B, w))) : ℚ) : ZMod p)) = 0 := by
  have hA4 : A.val < 8 := A.isLt
  have hB4 : B.val < 8 := B.isLt
  have hqpos : 0 < p ^ k := pow_pos (Fact.out : Nat.Prime p).pos _
  have hv : v.val < p ^ k := v.isLt
  have hw : w.val < p ^ k := w.isLt
  have hvalA :
      (m4RowEquiv (p := p) k ((@finProdFinEquiv 8 (p ^ k)) (A, v))).val =
        A.val * p ^ k + v.val := by
    calc
      _ = v.val + p ^ k * A.val := by rfl
      _ = A.val * p ^ k + v.val := by ac_rfl
  have hvalB :
      (m4RowEquiv (p := p) k ((@finProdFinEquiv 8 (p ^ k)) (B, w))).val =
        B.val * p ^ k + w.val := by
    calc
      _ = w.val + p ^ k * B.val := by rfl
      _ = B.val * p ^ k + w.val := by ac_rfl
  have hrowA : ¬ A.val * p ^ k + v.val < 4 * p ^ k := by
    have hA4' : 4 ≤ A.val := by omega
    have htmp : 4 * p ^ k ≤ A.val * p ^ k :=
      Nat.mul_le_mul_right _ hA4'
    omega
  have hi0 : 1 * p ^ k + (v.val + p ^ k * A.val - 4 * p ^ k) =
      (A.val - 3) * p ^ k + v.val := by
    have hA4' : 4 ≤ A.val := by omega
    have hAeq : A.val = (A.val - 4) + 4 := by omega
    rw [hAeq, Nat.mul_add]
    have hcancel : v.val + (p ^ k * (A.val - 4) + p ^ k * 4) -
        4 * p ^ k = v.val + p ^ k * (A.val - 4) := by
      have hq4 : p ^ k * 4 = 4 * p ^ k := by omega
      rw [hq4]
      omega
    rw [hcancel]
    have hA4sub : A.val - 4 + 4 - 3 = A.val - 3 := by omega
    rw [hA4sub]
    have hAminus : A.val - 3 = (A.val - 4) + 1 := by omega
    rw [hAminus, Nat.add_mul]
    ac_rfl
  have hi : 1 * p ^ k + (A.val * p ^ k + v.val - 4 * p ^ k) =
      (A.val - 3) * p ^ k + v.val := by
    simpa [Nat.mul_comm, Nat.add_comm] using hi0
  have hi_lt : (A.val - 3) * p ^ k + v.val < p * p ^ k := by
    calc
      (A.val - 3) * p ^ k + v.val < (A.val - 3) * p ^ k + p ^ k :=
        Nat.add_lt_add_left hv _
      _ = (A.val - 3 + 1) * p ^ k := by ring
      _ ≤ p * p ^ k := Nat.mul_le_mul_right _ (by omega)
  have hj_lt : B.val * p ^ k + w.val < p * p ^ k := by
    calc
      B.val * p ^ k + w.val < (B.val + 1) * p ^ k := by
        rw [show (B.val + 1) * p ^ k = B.val * p ^ k + p ^ k by ring]
        omega
      _ ≤ 8 * p ^ k := Nat.mul_le_mul_right _ (by omega)
      _ < p * p ^ k := Nat.mul_lt_mul_of_pos_right (by omega) hqpos
  have hij : (A.val - 3) * p ^ k + v.val ≠ B.val * p ^ k + w.val := by
    exact Li2Lean.P0.ScaledLucas.decomp_ne_of_ne_rem hv hw (Fin.val_ne_of_ne hvw)
  unfold towerScaledMatrixQ
  simp only [hvalA, hvalB]
  simp only [if_neg hrowA]
  rw [hi]
  change (((((qRatP p k) ^ 2 * p0BQ (a : ℚ) (2 * p ^ k)
      ((A.val - 3) * p ^ k + v.val) (B.val * p ^ k + w.val)) -
      (qRatP p k) ^ 2 * r * p0AQ (a : ℚ) (2 * p ^ k)
        ((A.val - 3) * p ^ k + v.val) (B.val * p ^ k + w.val) : ℚ) : ZMod p)) = 0
  have hAQ :
      (((qRatP p k) ^ 2 * r * p0AQ (a : ℚ) (2 * p ^ k)
        ((A.val - 3) * p ^ k + v.val) (B.val * p ^ k + w.val) : ℚ) : ZMod p) = 0 := by
    have hqr0 : (((qRatP p k) ^ 2 * r : ℚ) : ZMod p) = 0 := by
      simpa [qRatP] using (powP_sq_mul_rat_cast_eq_zero (P := p) k r hbound)
    have hqrg : (qRatP p k) ^ 2 * r ∈ GoodP p :=
      EntryGoodness.q_sq_mul_rat_good k r hbound
    have hAg : p0AQ (a : ℚ) (2 * p ^ k)
        ((A.val - 3) * p ^ k + v.val) (B.val * p ^ k + w.val) ∈ GoodP p :=
      EntryGoodness.p0AQ_good (p := p) (a := a) _ _ _
    rw [show qRatP p k ^ 2 * r * p0AQ (a : ℚ) (2 * p ^ k)
        ((A.val - 3) * p ^ k + v.val) (B.val * p ^ k + w.val) =
        (qRatP p k ^ 2 * r) * p0AQ (a : ℚ) (2 * p ^ k)
          ((A.val - 3) * p ^ k + v.val) (B.val * p ^ k + w.val) by ring]
    rw [Rat.cast_mul_of_ne_zero (natCast_ne_zero_of_coprime hqrg)
      (natCast_ne_zero_of_coprime hAg), hqr0, zero_mul]
  have hzero :
      ((qRatP p k / (((B.val * p ^ k + w.val : ℕ) : ℚ) -
          (((A.val - 3) * p ^ k + v.val : ℕ) : ℚ)) : ℚ) : ZMod p) = 0 := by
    rcases Nat.lt_or_gt_of_ne hij with hlt | hlt
    · have hcast :
          (((B.val * p ^ k + w.val : ℕ) : ℚ) -
            (((A.val - 3) * p ^ k + v.val : ℕ) : ℚ)) =
            (((B.val * p ^ k + w.val) - ((A.val - 3) * p ^ k + v.val) : ℕ) : ℚ) := by
        rw [Nat.cast_sub hlt.le]
      rw [hcast]
      apply EntryGoodness.qdiv_cast_zero_generic k _ (Nat.sub_pos_of_lt hlt)
      · exact lt_of_le_of_lt (Nat.sub_le _ _)
          (lt_of_le_of_lt (Nat.le_max_right _ _) (max_lt hi_lt hj_lt))
      · have hmod : ((A.val - 3) * p ^ k + v.val) % p ^ k ≠
            (B.val * p ^ k + w.val) % p ^ k := by
          rw [Li2Lean.P0.ScaledLucas.mod_of_decomp hv,
            Li2Lean.P0.ScaledLucas.mod_of_decomp hw]
          exact Fin.val_ne_of_ne hvw
        intro hdvd
        apply hmod
        exact (Nat.modEq_iff_dvd' hlt.le).mpr hdvd
    · have hcast :
          (((B.val * p ^ k + w.val : ℕ) : ℚ) -
            (((A.val - 3) * p ^ k + v.val : ℕ) : ℚ)) =
            -((((A.val - 3) * p ^ k + v.val) - (B.val * p ^ k + w.val) : ℕ) : ℚ) := by
        rw [Nat.cast_sub hlt.le]
        ring
      rw [hcast, div_neg, Rat.cast_neg]
      rw [EntryGoodness.qdiv_cast_zero_generic k _ (Nat.sub_pos_of_lt hlt)]
      · simp
      · exact lt_of_le_of_lt (Nat.sub_le _ _)
          (lt_of_le_of_lt (Nat.le_max_left _ _) (max_lt hi_lt hj_lt))
      · have hmod : (B.val * p ^ k + w.val) % p ^ k ≠
            ((A.val - 3) * p ^ k + v.val) % p ^ k := by
          rw [Li2Lean.P0.ScaledLucas.mod_of_decomp hw,
            Li2Lean.P0.ScaledLucas.mod_of_decomp hv]
          exact (Fin.val_ne_of_ne hvw).symm
        intro hdvd
        apply hmod
        exact (Nat.modEq_iff_dvd' hlt.le).mpr hdvd
  have hT1 := EntryGoodness.q_mul_p0T_good hunit k (2 * p ^ k)
    ((A.val - 3) * p ^ k + v.val) hi_lt (by
      exact Nat.mul_lt_mul_of_pos_right (by omega) hqpos)
  have hT2 := EntryGoodness.q_mul_p0T_good hunit k (2 * p ^ k)
    (B.val * p ^ k + w.val) hj_lt (by
      exact Nat.mul_lt_mul_of_pos_right (by omega) hqpos)
  have hratio := EntryGoodness.q_div_diff_good k
    ((A.val - 3) * p ^ k + v.val) (B.val * p ^ k + w.val) hij
    (max_lt hi_lt hj_lt)
  have hTdiff : qRatP p k * p0TQ (a : ℚ) (2 * p ^ k)
      ((A.val - 3) * p ^ k + v.val) -
      qRatP p k * p0TQ (a : ℚ) (2 * p ^ k)
        (B.val * p ^ k + w.val) ∈ GoodP p :=
    (GoodP p).sub_mem hT1 hT2
  have hBgood : (qRatP p k) ^ 2 * p0BQ (a : ℚ) (2 * p ^ k)
      ((A.val - 3) * p ^ k + v.val) (B.val * p ^ k + w.val) ∈ GoodP p :=
    EntryGoodness.q_sq_mul_p0BQ_good hunit k (2 * p ^ k)
      ((A.val - 3) * p ^ k + v.val) (B.val * p ^ k + w.val)
      (by exact Nat.mul_lt_mul_of_pos_right (by omega) hqpos) hi_lt hj_lt
  have hAQgood : (qRatP p k) ^ 2 * r * p0AQ (a : ℚ) (2 * p ^ k)
      ((A.val - 3) * p ^ k + v.val) (B.val * p ^ k + w.val) ∈ GoodP p :=
    (GoodP p).mul_mem (EntryGoodness.q_sq_mul_rat_good k r hbound)
      (EntryGoodness.p0AQ_good (p := p) (a := a) _ _ _)
  rw [Rat.cast_sub_of_ne_zero (natCast_ne_zero_of_coprime hBgood)
      (natCast_ne_zero_of_coprime hAQgood)]
  have hBfactor : (qRatP p k) ^ 2 * p0BQ (a : ℚ) (2 * p ^ k)
      ((A.val - 3) * p ^ k + v.val) (B.val * p ^ k + w.val) =
      (qRatP p k / (((B.val * p ^ k + w.val : ℕ) : ℚ) -
          (((A.val - 3) * p ^ k + v.val : ℕ) : ℚ))) *
        (qRatP p k * p0TQ (a : ℚ) (2 * p ^ k) ((A.val - 3) * p ^ k + v.val) -
          qRatP p k * p0TQ (a : ℚ) (2 * p ^ k) (B.val * p ^ k + w.val)) := by
    unfold p0BQ
    rw [if_neg hij]
    field_simp
  rw [hBfactor,
    Rat.cast_mul_of_ne_zero (natCast_ne_zero_of_coprime hratio)
      (natCast_ne_zero_of_coprime hTdiff), hzero, zero_mul, hAQ, sub_zero]

/-! The diagonal C entries in the lower half of the M=4 source block. -/
theorem m4_c_diagonal_source_entry
    (a : ℤ) (hp10 : 10 < p)
    (hunit : Nat.Coprime (a - 1).natAbs p)
    (k : ℕ) (r : ℚ)
    (A B : Fin 8) (v : Fin (p ^ k))
    (hA : A.val < 4)
    (hCdiag : A.val + 1 = B.val) :
    (((towerScaledMatrixQ (p := p) (a := a) k r
        (m4RowEquiv (p := p) k ((@finProdFinEquiv 8 (p ^ k)) (A, v)))
        (m4RowEquiv (p := p) k ((@finProdFinEquiv 8 (p ^ k)) (B, v))) : ℚ) : ZMod p)) =
      (a : ZMod p) ^ v.val * m4SourceResidue a A B p := by
  have hA4 : A.val < 8 := A.isLt
  have hB4 : B.val < 8 := B.isLt
  have hqpos : 0 < p ^ k := pow_pos (Fact.out : Nat.Prime p).pos _
  have hv : v.val < p ^ k := v.isLt
  have hA4p : A.val + 1 + 3 ≤ p := by
    have hpge : 11 ≤ p := by omega
    omega
  have hvalA :
      (m4RowEquiv (p := p) k ((@finProdFinEquiv 8 (p ^ k)) (A, v))).val =
        A.val * p ^ k + v.val := by
    calc
      _ = v.val + p ^ k * A.val := by rfl
      _ = A.val * p ^ k + v.val := by ac_rfl
  have hvalB :
      (m4RowEquiv (p := p) k ((@finProdFinEquiv 8 (p ^ k)) (B, v))).val =
        B.val * p ^ k + v.val := by
    calc
      _ = v.val + p ^ k * B.val := by rfl
      _ = B.val * p ^ k + v.val := by ac_rfl
  have hrowA : A.val * p ^ k + v.val < 4 * p ^ k := by
    nlinarith
  unfold towerScaledMatrixQ
  simp only [hvalA, hvalB]
  simp only [if_pos hrowA]
  have hidx : 1 * p ^ k + (A.val * p ^ k + v.val) =
      (A.val + 1) * p ^ k + v.val := by ring
  rw [hidx]
  have hdiag_index : (A.val + 1) * p ^ k + v.val =
      B.val * p ^ k + v.val := by rw [hCdiag]
  rw [← hdiag_index]
  change ((qRatP p k * p0CQ (a : ℚ) (2 * p ^ k)
      ((A.val + 1) * p ^ k + v.val) ((A.val + 1) * p ^ k + v.val) : ℚ) : ZMod p) =
    (a : ZMod p) ^ v.val * m4SourceResidue a A B p
  have hC := cast_qC_diag_generic (p := p) a hunit k (A.val + 1) v.val
    hA4p hv
  rw [hC]
  have hsource := cast_qC_diag_generic (p := p) a hunit 0 (A.val + 1) 0
    hA4p (by norm_num)
  have hB_eq : B.val = A.val + 1 := hCdiag.symm
  have hsource_eq : m4SourceResidue a A B p =
      ((p0CQ (a : ℚ) 2 (A.val + 1) B.val : ℚ) : ZMod p) := by
    have hx : (p0MatrixQ (a : ℚ) 4 A B).eval 0 =
        p0CQ (a : ℚ) 2 (A.val + 1) B.val := by
      simp [p0MatrixQ, hA, Nat.add_comm]
    unfold m4SourceResidue
    dsimp
    rw [hx]
    simp [Rat.cast_def, div_eq_mul_inv]
  rw [hsource_eq]
  have hsource' :
      ((p0CQ (a : ℚ) 2 (A.val + 1) (A.val + 1) : ℚ) : ZMod p) =
        -((a : ZMod p) ^ (A.val + 1) *
            (Nat.choose (A.val + 1 + 2) 2 : ZMod p)) *
            ∑ c ∈ Finset.range 2, ((A.val + 1 + c + 1 : ℕ) : ZMod p)⁻¹ := by
    simpa [qRatP] using hsource
  rw [hB_eq, hsource']
  ring

theorem m4_c_offdiag_source_entry
    (a : ℤ) (hp10 : 10 < p)
    (hunit : Nat.Coprime (a - 1).natAbs p)
    (k : ℕ) (r : ℚ)
    (A B : Fin 8) (v w : Fin (p ^ k))
    (hA : A.val < 4)
    (hoff : A.val + 1 ≠ B.val ∨ v ≠ w) :
    (((towerScaledMatrixQ (p := p) (a := a) k r
        (m4RowEquiv (p := p) k ((@finProdFinEquiv 8 (p ^ k)) (A, v)))
        (m4RowEquiv (p := p) k ((@finProdFinEquiv 8 (p ^ k)) (B, w))) : ℚ) : ZMod p)) =
      if v = w then (a : ZMod p) ^ v.val * m4SourceResidue a A B p else 0 := by
  have hA8 : A.val < 8 := A.isLt
  have hB8 : B.val < 8 := B.isLt
  have hqpos : 0 < p ^ k := pow_pos (Fact.out : Nat.Prime p).pos _
  have hv : v.val < p ^ k := v.isLt
  have hw : w.val < p ^ k := w.isLt
  have hA1p : A.val + 1 < p := by
    have hpge : 11 ≤ p := by omega
    omega
  have hBp : B.val < p := by
    have hpge : 11 ≤ p := by omega
    omega
  have hvalA :
      (m4RowEquiv (p := p) k ((@finProdFinEquiv 8 (p ^ k)) (A, v))).val =
        A.val * p ^ k + v.val := by
    calc
      _ = v.val + p ^ k * A.val := by rfl
      _ = A.val * p ^ k + v.val := by ac_rfl
  have hvalB :
      (m4RowEquiv (p := p) k ((@finProdFinEquiv 8 (p ^ k)) (B, w))).val =
        B.val * p ^ k + w.val := by
    calc
      _ = w.val + p ^ k * B.val := by rfl
      _ = B.val * p ^ k + w.val := by ac_rfl
  have hrowA : A.val * p ^ k + v.val < 4 * p ^ k := by
    nlinarith
  unfold towerScaledMatrixQ
  simp only [hvalA, hvalB]
  simp only [if_pos hrowA]
  have hidxrow : 1 * p ^ k + (A.val * p ^ k + v.val) =
      (A.val + 1) * p ^ k + v.val := by ring
  rw [hidxrow]
  by_cases hAb : A.val + 1 ≠ B.val
  · have hres := qC_off_residue_M4 (p := p) a k A.val B.val v.val w.val
      hunit hA1p hBp hAb hv hw
    by_cases hvw : v = w
    · subst w
      rw [hres]
      have hsource_eq : m4SourceResidue a A B p =
          ((p0CQ (a : ℚ) 2 (A.val + 1) B.val : ℚ) : ZMod p) := by
        unfold m4SourceResidue p0MatrixQ
        have hAb' : 1 + A.val ≠ B.val := by
          simpa [Nat.add_comm] using hAb
        have hAadd : 1 + A.val = A.val + 1 := by omega
        simp [p0CQ, hA, hAb, hAb', hAadd, Rat.cast_def, div_eq_mul_inv]
      rw [hsource_eq]
      simp
    · have hvw_val : v.val ≠ w.val := by
        intro h
        apply hvw
        exact Fin.ext h
      rw [hres]
      simp [hvw, hvw_val]
  · have hvw : v ≠ w := by
      intro hvw
      rcases hoff with h | h
      · exact (hAb h).elim
      · exact h hvw
    have hvw_val : v.val ≠ w.val := by
      intro h
      apply hvw
      exact Fin.ext h
    have hidx : (A.val + 1) * p ^ k + v.val ≠ B.val * p ^ k + w.val := by
      exact ScaledLucas.decomp_ne_of_ne_rem hv hw hvw_val
    have hi : (A.val + 1) * p ^ k + v.val < p * p ^ k := by
      calc
        (A.val + 1) * p ^ k + v.val < (A.val + 2) * p ^ k := by
          calc
            _ < (A.val + 1) * p ^ k + p ^ k :=
              Nat.add_lt_add_left hv _
            _ = (A.val + 2) * p ^ k := by ring
        _ ≤ p * p ^ k := Nat.mul_le_mul_right _ (by omega)
    have hj : B.val * p ^ k + w.val < p * p ^ k := by
      calc
        B.val * p ^ k + w.val < (B.val + 1) * p ^ k := by
          calc
            _ < B.val * p ^ k + p ^ k :=
              Nat.add_lt_add_left hw _
            _ = (B.val + 1) * p ^ k := by ring
        _ ≤ p * p ^ k := Nat.mul_le_mul_right _ (by omega)
    have hbound : max ((A.val + 1) * p ^ k + v.val)
        (B.val * p ^ k + w.val) < p * p ^ k := max_lt hi hj
    have hmod :
        ((A.val + 1) * p ^ k + v.val) % p ^ k ≠
          (B.val * p ^ k + w.val) % p ^ k := by
      simpa [ScaledLucas.mod_of_decomp hv, ScaledLucas.mod_of_decomp hw] using hvw_val
    have hqdiffzero :
        ((qRatP p k /
          (((B.val * p ^ k + w.val : ℕ) : ℚ) -
            (((A.val + 1) * p ^ k + v.val : ℕ) : ℚ)) : ℚ) : ZMod p) = 0 := by
      rcases Nat.lt_or_gt_of_ne hidx with hlt | hlt
      · have hcast :
            (((B.val * p ^ k + w.val : ℕ) : ℚ) -
              (((A.val + 1) * p ^ k + v.val : ℕ) : ℚ)) =
              (((B.val * p ^ k + w.val) -
                ((A.val + 1) * p ^ k + v.val) : ℕ) : ℚ) := by
          rw [Nat.cast_sub hlt.le]
        rw [hcast]
        apply EntryGoodness.qdiv_cast_zero_generic k _ (Nat.sub_pos_of_lt hlt)
        · exact lt_of_le_of_lt (Nat.sub_le _ _)
            (lt_of_le_of_lt (Nat.le_max_right _ _) hbound)
        · intro hdvd
          apply hmod
          exact (Nat.modEq_iff_dvd' hlt.le).mpr hdvd
      · have hcast :
            (((B.val * p ^ k + w.val : ℕ) : ℚ) -
              (((A.val + 1) * p ^ k + v.val : ℕ) : ℚ)) =
              -(((A.val + 1) * p ^ k + v.val -
                (B.val * p ^ k + w.val) : ℕ) : ℚ) := by
          rw [Nat.cast_sub hlt.le]
          ring
        rw [hcast, div_neg, Rat.cast_neg]
        rw [EntryGoodness.qdiv_cast_zero_generic k _ (Nat.sub_pos_of_lt hlt)]
        · simp
        · exact lt_of_le_of_lt (Nat.sub_le _ _)
            (lt_of_le_of_lt (Nat.le_max_left _ _) hbound)
        · intro hdvd
          apply hmod
          exact ((Nat.modEq_iff_dvd' hlt.le).mpr hdvd).symm
    rw [EntryGoodness.qC_off_decomp_generic (a := (a : ℚ))
      (k := k) (g := 2 * p ^ k)
      (i := (A.val + 1) * p ^ k + v.val)
      (j := B.val * p ^ k + w.val) hidx]
    have hu1 := EntryGoodness.p0U_good_general (p := p) (a := a)
      (2 * p ^ k) ((A.val + 1) * p ^ k + v.val)
    have hu2 := EntryGoodness.p0U_good_general (p := p) (a := a)
      (2 * p ^ k) (B.val * p ^ k + w.val)
    have hratio := EntryGoodness.q_div_diff_good k
      ((A.val + 1) * p ^ k + v.val) (B.val * p ^ k + w.val)
      hidx hbound
    rw [Rat.cast_mul_of_ne_zero
      (natCast_ne_zero_of_coprime ((GoodP p).sub_mem hu1 hu2))
      (natCast_ne_zero_of_coprime hratio),
      Rat.cast_sub_of_ne_zero (natCast_ne_zero_of_coprime hu1)
        (natCast_ne_zero_of_coprime hu2),
      hqdiffzero, mul_zero]
    simp [hvw]

theorem m4_b_offdiag_same_res_source_entry
    (a : ℤ) (hp10 : 10 < p)
    (hunit : Nat.Coprime (a - 1).natAbs p)
    (k : ℕ) (r : ℚ) (hbound : r.den < p ^ k)
    (A B : Fin 8) (v : Fin (p ^ k))
    (hA : ¬ A.val < 4)
    (hBoff : A.val - 3 ≠ B.val) :
    (((towerScaledMatrixQ (p := p) (a := a) k r
        (m4RowEquiv (p := p) k ((@finProdFinEquiv 8 (p ^ k)) (A, v)))
        (m4RowEquiv (p := p) k ((@finProdFinEquiv 8 (p ^ k)) (B, v))) : ℚ) : ZMod p)) =
      (a : ZMod p) ^ v.val * m4SourceResidue a A B p := by
  have hA8 : A.val < 8 := A.isLt
  have hB8 : B.val < 8 := B.isLt
  have hqpos : 0 < p ^ k := pow_pos (Fact.out : Nat.Prime p).pos _
  have hv : v.val < p ^ k := v.isLt
  have hpge : 11 ≤ p := by omega
  have hA4 : 4 ≤ A.val := by omega
  have hA3small : A.val - 3 + 2 < p := by omega
  have hBsmall : B.val + 2 < p := by omega
  have hvalA :
      (m4RowEquiv (p := p) k ((@finProdFinEquiv 8 (p ^ k)) (A, v))).val =
        A.val * p ^ k + v.val := by
    calc
      _ = v.val + p ^ k * A.val := by rfl
      _ = A.val * p ^ k + v.val := by ac_rfl
  have hvalB :
      (m4RowEquiv (p := p) k ((@finProdFinEquiv 8 (p ^ k)) (B, v))).val =
        B.val * p ^ k + v.val := by
    calc
      _ = v.val + p ^ k * B.val := by rfl
      _ = B.val * p ^ k + v.val := by ac_rfl
  have hrowA' : ¬ v.val + p ^ k * A.val < 4 * p ^ k := by
    nlinarith
  have hrowA : ¬ A.val * p ^ k + v.val < 4 * p ^ k := by
    simpa [Nat.mul_comm, Nat.add_comm] using hrowA'
  have hi : 1 * p ^ k + (v.val + p ^ k * A.val - 4 * p ^ k) =
      (A.val - 3) * p ^ k + v.val := by
    have hAeq : A.val = (A.val - 4) + 4 := by omega
    rw [hAeq, Nat.mul_add]
    have hcancel : v.val + (p ^ k * (A.val - 4) + p ^ k * 4) -
        4 * p ^ k = v.val + p ^ k * (A.val - 4) := by
      have hq4 : p ^ k * 4 = 4 * p ^ k := by omega
      rw [hq4]
      omega
    rw [hcancel]
    have hsub : A.val - 4 + 4 - 3 = A.val - 3 := by omega
    rw [hsub]
    have hminus : A.val - 3 = (A.val - 4) + 1 := by omega
    rw [hminus, Nat.add_mul]
    ac_rfl
  have hi2 : 1 * p ^ k + (A.val * p ^ k + v.val - 4 * p ^ k) =
      (A.val - 3) * p ^ k + v.val := by
    simpa [Nat.mul_comm, Nat.add_comm] using hi
  have hidx : (A.val - 3) * p ^ k + v.val ≠ B.val * p ^ k + v.val := by
    intro h
    apply hBoff
    exact Nat.eq_of_mul_eq_mul_right hqpos (by omega)
  unfold towerScaledMatrixQ
  simp only [hvalA, hvalB]
  simp only [if_neg hrowA]
  rw [hi2]
  change (((((qRatP p k) ^ 2 * p0BQ (a : ℚ) (2 * p ^ k)
      ((A.val - 3) * p ^ k + v.val) (B.val * p ^ k + v.val)) -
      (qRatP p k) ^ 2 * r * p0AQ (a : ℚ) (2 * p ^ k)
        ((A.val - 3) * p ^ k + v.val) (B.val * p ^ k + v.val) : ℚ) : ZMod p)) =
    (a : ZMod p) ^ v.val * m4SourceResidue a A B p
  have hAQ :
      (((qRatP p k) ^ 2 * r * p0AQ (a : ℚ) (2 * p ^ k)
        ((A.val - 3) * p ^ k + v.val) (B.val * p ^ k + v.val) : ℚ) : ZMod p) = 0 := by
    rw [show qRatP p k ^ 2 * r * p0AQ (a : ℚ) (2 * p ^ k)
        ((A.val - 3) * p ^ k + v.val) (B.val * p ^ k + v.val) =
        (qRatP p k ^ 2 * r) * p0AQ (a : ℚ) (2 * p ^ k)
          ((A.val - 3) * p ^ k + v.val) (B.val * p ^ k + v.val) by ring]
    have hqr0 : (((qRatP p k) ^ 2 * r : ℚ) : ZMod p) = 0 := by
      simpa [qRatP] using (powP_sq_mul_rat_cast_eq_zero (P := p) k r hbound)
    have hqrg : qRatP p k ^ 2 * r ∈ GoodP p :=
      EntryGoodness.q_sq_mul_rat_good k r hbound
    have hAg : p0AQ (a : ℚ) (2 * p ^ k)
        ((A.val - 3) * p ^ k + v.val) (B.val * p ^ k + v.val) ∈ GoodP p :=
      EntryGoodness.p0AQ_good (p := p) (a := a) _ _ _
    rw [Rat.cast_mul_of_ne_zero (natCast_ne_zero_of_coprime hqrg)
      (natCast_ne_zero_of_coprime hAg), hqr0, zero_mul]
  have hi_lt : (A.val - 3) * p ^ k + v.val < p * p ^ k := by
    exact ar_lt (A.val - 3) v.val _ p (by omega) hv
  have hj_lt : B.val * p ^ k + v.val < p * p ^ k := by
    exact ar_lt B.val v.val _ p (by omega) hv
  have h2q : 2 * p ^ k < p * p ^ k :=
    Nat.mul_lt_mul_of_pos_right (by omega) hqpos
  have hBgood :
      (qRatP p k) ^ 2 * p0BQ (a : ℚ) (2 * p ^ k)
          ((A.val - 3) * p ^ k + v.val) (B.val * p ^ k + v.val) ∈ GoodP p :=
    EntryGoodness.q_sq_mul_p0BQ_good (p := p) (a := a) hunit k
      (2 * p ^ k) ((A.val - 3) * p ^ k + v.val)
      (B.val * p ^ k + v.val) h2q hi_lt hj_lt
  have hAgood :
      (qRatP p k) ^ 2 * r * p0AQ (a : ℚ) (2 * p ^ k)
          ((A.val - 3) * p ^ k + v.val) (B.val * p ^ k + v.val) ∈ GoodP p :=
    (GoodP p).mul_mem (EntryGoodness.q_sq_mul_rat_good k r hbound)
      (EntryGoodness.p0AQ_good (p := p) (a := a) _ _ _)
  rw [Rat.cast_sub_of_ne_zero (natCast_ne_zero_of_coprime hBgood)
      (natCast_ne_zero_of_coprime hAgood), hAQ, sub_zero]
  have hdecomp :
      (qRatP p k) ^ 2 * p0BQ (a : ℚ) (2 * p ^ k)
          ((A.val - 3) * p ^ k + v.val) (B.val * p ^ k + v.val) =
        (qRatP p k * p0TQ (a : ℚ) (2 * p ^ k)
            ((A.val - 3) * p ^ k + v.val) -
          qRatP p k * p0TQ (a : ℚ) (2 * p ^ k)
            (B.val * p ^ k + v.val)) *
          (qRatP p k / (((B.val * p ^ k + v.val : ℕ) : ℚ) -
            ((A.val - 3) * p ^ k + v.val : ℕ) : ℚ)) := by
    unfold p0BQ
    rw [if_neg hidx]
    ring
  rw [hdecomp]
  have hmax : max ((A.val - 3) * p ^ k + v.val) (B.val * p ^ k + v.val) <
      p * p ^ k := max_lt hi_lt hj_lt
  have hqi := EntryGoodness.q_mul_p0T_good (p := p) (a := a) hunit k
    (2 * p ^ k) ((A.val - 3) * p ^ k + v.val) hi_lt h2q
  have hqj := EntryGoodness.q_mul_p0T_good (p := p) (a := a) hunit k
    (2 * p ^ k) (B.val * p ^ k + v.val) hj_lt h2q
  have hratio := EntryGoodness.q_div_diff_good (p := p) k
    ((A.val - 3) * p ^ k + v.val) (B.val * p ^ k + v.val) hidx hmax
  rw [Rat.cast_mul_of_ne_zero
      (natCast_ne_zero_of_coprime ((GoodP p).sub_mem hqi hqj))
      (natCast_ne_zero_of_coprime hratio),
    Rat.cast_sub_of_ne_zero (natCast_ne_zero_of_coprime hqi)
      (natCast_ne_zero_of_coprime hqj)]
  have hunit_diff :
      (((qRatP p k / (((B.val * p ^ k + v.val : ℕ) : ℚ) -
        ((A.val - 3) * p ^ k + v.val : ℕ) : ℚ)) : ℚ) : ZMod p) =
        ((((B.val : ℤ) - (A.val - 3 : ℕ) : ℤ) : ZMod p))⁻¹ := by
    rcases Nat.lt_or_gt_of_ne hBoff with hlt | hlt
    · have hcast :
          (((B.val * p ^ k + v.val : ℕ) : ℚ) -
            ((A.val - 3) * p ^ k + v.val : ℕ) : ℚ) =
            (((B.val - (A.val - 3)) * p ^ k : ℕ) : ℚ) := by
        push_cast
        rw [Nat.cast_sub hlt.le]
        ring
      rw [hcast, qdiv_cast_unit_generic k (B.val - (A.val - 3))
        (by omega) (by omega)]
      congr 1
      simp [Nat.cast_sub hlt.le]
    · have hcast :
          (((B.val * p ^ k + v.val : ℕ) : ℚ) -
            ((A.val - 3) * p ^ k + v.val : ℕ) : ℚ) =
            -(((A.val - 3 - B.val) * p ^ k : ℕ) : ℚ) := by
        push_cast
        rw [Nat.cast_sub hlt.le]
        ring
      rw [hcast, div_neg, Rat.cast_neg,
        qdiv_cast_unit_generic k (A.val - 3 - B.val) (by omega) (by omega)]
      rw [show ((B.val : ℤ) - (A.val - 3 : ℕ) : ℤ) =
          -((A.val - 3 - B.val : ℕ) : ℤ) by
            rw [Nat.cast_sub hlt.le]
            ring]
      push_cast
      rw [inv_neg]
  rw [generic_qT_residue_M4 (p := p) a hp10 hunit k (A.val - 3) v.val
      hA3small hv,
    generic_qT_residue_M4 (p := p) a hp10 hunit k B.val v.val hBsmall hv,
    hunit_diff]
  have hsource_eq :
      m4SourceResidue a A B p =
        ((p0BQ (a : ℚ) 2 (A.val - 3) B.val : ℚ) : ZMod p) := by
    have hrow : 1 + (A.val - 4) = A.val - 3 := by omega
    unfold m4SourceResidue p0MatrixQ
    simp [p0BQ, p0AQ, hA, hBoff, hrow, Rat.cast_def, div_eq_mul_inv]
  have hbaseA :
      ((p0TQ (a : ℚ) 2 (A.val - 3) : ℚ) : ZMod p) =
        genericYT (p := p) a (A.val - 3) := by
    have h := generic_qT_residue_M4 (p := p) a hp10 hunit 0
      (A.val - 3) 0 hA3small (by norm_num)
    simpa [qRatP] using h
  have hbaseB :
      ((p0TQ (a : ℚ) 2 B.val : ℚ) : ZMod p) =
        genericYT (p := p) a B.val := by
    have h := generic_qT_residue_M4 (p := p) a hp10 hunit 0
      B.val 0 hBsmall (by norm_num)
    simpa [qRatP] using h
  have hbase_diff :
      ((((B.val : ℚ) - (A.val - 3 : ℕ) : ℚ)⁻¹ : ℚ) : ZMod p) =
        ((((B.val : ℤ) - (A.val - 3 : ℕ) : ℤ) : ZMod p))⁻¹ := by
    rcases Nat.lt_or_gt_of_ne hBoff with hlt | hlt
    · rw [show ((B.val : ℚ) - (A.val - 3 : ℕ) : ℚ) =
          ((B.val - (A.val - 3) : ℕ) : ℚ) by
            rw [Nat.cast_sub hlt.le]]
      have hq := qdiv_cast_unit_generic (p := p) 0
        (B.val - (A.val - 3)) (by omega) (by omega)
      simpa [qRatP, Nat.cast_sub hlt.le] using hq
    · rw [show ((B.val : ℚ) - (A.val - 3 : ℕ) : ℚ) =
          -((A.val - 3 - B.val : ℕ) : ℚ) by
            rw [Nat.cast_sub hlt.le]; norm_num]
      have hq := qdiv_cast_unit_generic (p := p) 0
        (A.val - 3 - B.val) (by omega) (by omega)
      have hq' :
          (((qRatP p 0 / (((A.val - 3 - B.val) * p ^ 0 : ℕ) : ℚ) : ℚ) : ZMod p)) =
            (((A.val - 3 - B.val : ℕ) : ZMod p))⁻¹ := hq
      have hpos :
          ((((A.val - 3 - B.val : ℕ) : ℚ)⁻¹ : ℚ) : ZMod p) =
            (((A.val - 3 - B.val : ℕ) : ZMod p))⁻¹ := by
        simpa [qRatP, Nat.cast_sub hlt.le] using hq'
      rw [inv_neg, Rat.cast_neg, hpos]
      rw [show ((B.val : ℤ) - (A.val - 3 : ℕ) : ℤ) =
          -((A.val - 3 - B.val : ℕ) : ℤ) by
            rw [Nat.cast_sub hlt.le]
            ring]
      push_cast
      rw [inv_neg]
  have hsource' :
      ((p0BQ (a : ℚ) 2 (A.val - 3) B.val : ℚ) : ZMod p) =
        (genericYT (p := p) a (A.val - 3) - genericYT (p := p) a B.val) *
          ((((B.val : ℤ) - (A.val - 3 : ℕ) : ℤ) : ZMod p))⁻¹ := by
    unfold p0BQ
    rw [if_neg hBoff]
    have hu : p0TQ (a : ℚ) 2 (A.val - 3) ∈ GoodP p := by
      simpa [qRatP] using EntryGoodness.q_mul_p0T_good (p := p) (a := a) hunit 0
        2 (A.val - 3) (by simpa [pow_zero] using show A.val - 3 < p by omega)
          (by simpa [pow_zero] using show 2 < p by omega)
    have hv' : p0TQ (a : ℚ) 2 B.val ∈ GoodP p := by
      simpa [qRatP] using EntryGoodness.q_mul_p0T_good (p := p) (a := a) hunit 0
        2 B.val (by simpa [pow_zero] using show B.val < p by omega)
          (by simpa [pow_zero] using show 2 < p by omega)
    have hd : (((B.val : ℚ) - (A.val - 3 : ℕ))⁻¹) ∈ GoodP p := by
      have hmax0 : max (A.val - 3) B.val < p :=
        max_lt (by omega) (by omega)
      have hh := EntryGoodness.q_div_diff_good (p := p) 0 (A.val - 3) B.val hBoff
        (by simpa [pow_zero] using hmax0)
      simpa [qRatP, one_div] using hh
    rw [div_eq_mul_inv,
      Rat.cast_mul_of_ne_zero (natCast_ne_zero_of_coprime
        ((GoodP p).sub_mem hu hv')) (natCast_ne_zero_of_coprime hd),
      Rat.cast_sub_of_ne_zero (natCast_ne_zero_of_coprime hu)
        (natCast_ne_zero_of_coprime hv'), hbaseA, hbaseB, hbase_diff]
  rw [hsource_eq, hsource']
  ring

/-! Unified M=4 entry dispatcher.  The row split is the C/B half split;
the residue and block diagonal splits then select the corresponding leaf
bridge above. -/
theorem m4_scaled_entry
    (a : ℤ) (hp10 : 10 < p)
    (hunit : Nat.Coprime (a - 1).natAbs p)
    (k : ℕ) (r : ℚ) (hbound : r.den < p ^ k) (hk : 0 < k)
    (A B : Fin 8) (v w : Fin (p ^ k)) :
    (((towerScaledMatrixQ (p := p) (a := a) k r
        (m4RowEquiv (p := p) k ((@finProdFinEquiv 8 (p ^ k)) (A, v)))
        (m4RowEquiv (p := p) k ((@finProdFinEquiv 8 (p ^ k)) (B, w))) : ℚ) : ZMod p)) =
      if v = w then (a : ZMod p) ^ v.val * m4SourceResidue a A B p else 0 := by
  by_cases hA : A.val < 4
  · by_cases hCdiag : A.val + 1 = B.val
    · by_cases hvw : v = w
      · subst w
        simpa using
          (m4_c_diagonal_source_entry (p := p) a hp10 hunit k r A B v hA hCdiag)
      · exact
          m4_c_offdiag_source_entry (p := p) a hp10 hunit k r A B v w hA
            (Or.inr hvw)
    · exact
        m4_c_offdiag_source_entry (p := p) a hp10 hunit k r A B v w hA
          (Or.inl hCdiag)
  · by_cases hvw : v = w
    · subst w
      by_cases hBdiag : A.val - 3 = B.val
      · simpa using
          (m4_b_diagonal_source_entry (p := p) a hp10 hunit k r hbound hk A B v
            hA hBdiag)
      · simpa using
          (m4_b_offdiag_same_res_source_entry (p := p) a hp10 hunit k r hbound A B v
            hA hBdiag)
    · simpa [hvw] using
        (m4_b_off_res_source_entry (p := p) a hp10 hunit k r hbound A B v w hA hvw)

end
end Li2Lean.P0.PositiveTower

#print axioms Li2Lean.P0.PositiveTower.m4_b_off_res_source_entry

#print axioms Li2Lean.P0.PositiveTower.m4_b_diagonal_source_entry
