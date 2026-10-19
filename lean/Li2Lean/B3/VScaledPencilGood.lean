/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B3.VScaledPencil
import Li2Lean.B3.VMomentBGood
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# `GoodP p` lift and coefficient integrality for the scaled signed-V pencil

This module proves coefficient integrality for the scaled pencil
(v13 `chapters/nonvanishing.tex:214-219). Every entry of `vScaledPencilMatrix`
lies in `Polynomial (GoodP p)` for `11 ≤ p`, so the determinant polynomial has
`p`-integral coefficients uniformly in `q` and `k`.
-/

namespace Li2Lean.B3

noncomputable section

open scoped BigOperators
open Matrix
open Li2Lean.P0.PositiveTower Li2Lean.P0.PositiveTower.EntryGoodness

variable {p : ℕ} [Fact (Nat.Prime p)]

theorem q_mul_vCEntry_good (a : ℤ) (k i j : ℕ)
    (hb : max i j < p * p ^ k) :
    qRatP p k * V.vCEntry a i j ∈ GoodP p := by
  unfold V.vCEntry
  by_cases hij : i = j
  · simp [hij, (GoodP p).zero_mem]
  · simp only [if_neg hij]
    rw [show qRatP p k * (((a : ℚ) ^ i - (a : ℚ) ^ j) / ((j : ℚ) - (i : ℚ))) =
        ((a : ℚ) ^ i - (a : ℚ) ^ j) * (qRatP p k / ((j : ℚ) - (i : ℚ))) by ring]
    exact (GoodP p).mul_mem
      ((GoodP p).sub_mem ((GoodP p).pow_mem (intRat_good a) i)
        ((GoodP p).pow_mem (intRat_good a) j))
      (q_div_diff_good k i j hij hb)

theorem q_sq_mul_vBEntry_good (a : ℤ) (k i j : ℕ)
    (hb : max i j < p * p ^ k) :
    qRatP p k ^ 2 * V.vBEntry a i j ∈ GoodP p := by
  have hi : i < p * p ^ k := lt_of_le_of_lt (Nat.le_max_left i j) hb
  have hj : j < p * p ^ k := lt_of_le_of_lt (Nat.le_max_right i j) hb
  unfold V.vBEntry
  by_cases hij : i = j
  · simp only [if_pos hij]
    exact q_sq_mul_vMomentB_good a k i hi
  · simp only [if_neg hij]
    rw [show qRatP p k ^ 2 * ((V.vMomentT a i - V.vMomentT a j) / ((j : ℚ) - (i : ℚ))) =
        (qRatP p k * V.vMomentT a i - qRatP p k * V.vMomentT a j) *
          (qRatP p k / ((j : ℚ) - (i : ℚ))) by ring]
    exact (GoodP p).mul_mem
      ((GoodP p).sub_mem (q_mul_vMomentT_good a k i hi)
        (q_mul_vMomentT_good a k j hj))
      (q_div_diff_good k i j hij hb)

theorem vAEntry_good (a : ℤ) (i j : ℕ) : V.vAEntry a i j ∈ GoodP p := by
  unfold V.vAEntry
  split_ifs
  · exact (GoodP p).pow_mem (intRat_good a) i
  · exact (GoodP p).zero_mem

theorem q_mul_vVEntry_good (k j ell : ℕ) (h0 : 0 < j + ell)
    (hb : j + ell < p * p ^ k) :
    qRatP p k * V.vVEntry j ell ∈ GoodP p := by
  unfold V.vVEntry
  rw [← div_eq_mul_inv]
  exact q_div_good k (j + ell) h0 hb

private theorem vC_index_bound (hp11 : 11 ≤ p) (k : ℕ)
    (r c : Fin (V.vMatrixSize (p ^ k))) (hr : r.val < V.vM (p ^ k)) :
    max (V.vIIndexNat (p ^ k) r.val) (V.vJIndex (p ^ k) c) < p * p ^ k := by
  have hj := (V.vJIndex_mem (p ^ k) c).2
  have hpQ := Nat.mul_le_mul_right (p ^ k) hp11
  simp only [V.vIIndexNat, V.vM] at hr ⊢
  exact max_lt (by omega) (by omega)

private theorem vB_index_bound (hp11 : 11 ≤ p) (k : ℕ)
    (r c : Fin (V.vMatrixSize (p ^ k))) (hr : r.val < 2 * V.vM (p ^ k)) :
    max (2 * p ^ k + (r.val - V.vM (p ^ k))) (V.vJIndex (p ^ k) c) < p * p ^ k := by
  have hj := (V.vJIndex_mem (p ^ k) c).2
  have hpQ := Nat.mul_le_mul_right (p ^ k) hp11
  simp only [V.vM] at hr ⊢
  exact max_lt (by omega) (by omega)

private theorem vV_index_pos (k : ℕ) (r c : Fin (V.vMatrixSize (p ^ k))) :
    0 < V.vJIndex (p ^ k) c + (1 + (r.val - 2 * V.vM (p ^ k))) := by
  omega

private theorem vV_index_bound (hp11 : 11 ≤ p) (k : ℕ)
    (r c : Fin (V.vMatrixSize (p ^ k))) :
    V.vJIndex (p ^ k) c + (1 + (r.val - 2 * V.vM (p ^ k))) < p * p ^ k := by
  have hr := r.isLt
  have hj := (V.vJIndex_mem (p ^ k) c).2
  have hpQ := Nat.mul_le_mul_right (p ^ k) hp11
  simp only [V.vMatrixSize, V.vM, V.vS] at hr ⊢
  omega

def vScaledPencilGood (hp11 : 11 ≤ p) (q k : ℕ) :
    Matrix (Fin (V.vMatrixSize (p ^ k))) (Fin (V.vMatrixSize (p ^ k)))
      (Polynomial (GoodP p)) := fun r c =>
  let a : ℤ := -(q : ℤ)
  let j := V.vJIndex (p ^ k) c
  if h1 : r.val < V.vM (p ^ k) then
    Polynomial.C ⟨qRatP p k * V.vCEntry a (V.vIIndexNat (p ^ k) r.val) j,
      q_mul_vCEntry_good a k _ _ (vC_index_bound hp11 k r c h1)⟩
  else if h2 : r.val < 2 * V.vM (p ^ k) then
    let i := 2 * p ^ k + (r.val - V.vM (p ^ k))
    Polynomial.C ⟨qRatP p k ^ 2 * V.vBEntry a i j,
      q_sq_mul_vBEntry_good a k i j (vB_index_bound hp11 k r c h2)⟩ -
      Polynomial.X * Polynomial.C ⟨V.vAEntry a i j, vAEntry_good a i j⟩
  else
    Polynomial.C ⟨qRatP p k * V.vVEntry j (1 + (r.val - 2 * V.vM (p ^ k))),
      q_mul_vVEntry_good k j _ (vV_index_pos k r c) (vV_index_bound hp11 k r c)⟩

theorem vScaledPencilGood_map (hp11 : 11 ≤ p) (q k : ℕ) :
    (Polynomial.mapRingHom (GoodP p).subtype).mapMatrix
        (vScaledPencilGood hp11 q k) =
      vScaledPencilMatrix q (p ^ k) := by
  ext r c : 1
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Polynomial.coe_mapRingHom]
  unfold vScaledPencilGood vScaledPencilMatrix
  by_cases h1 : r.val < V.vM (p ^ k)
  · simp [h1, qRatP]
  · by_cases h2 : r.val < 2 * V.vM (p ^ k)
    · simp [h1, h2, qRatP]
    · simp [h1, h2, qRatP]

theorem vFrobeniusScaledPolynomial_eq_map_det_good (hp11 : 11 ≤ p) (q k : ℕ) :
    V.vFrobeniusScaledPolynomial q p k =
      ((vScaledPencilGood hp11 q k).det).map (GoodP p).subtype := by
  have hp : 0 < p := (Fact.out : Nat.Prime p).pos
  rw [← vScaledPencilMatrix_det q p k hp, ← vScaledPencilGood_map hp11 q k,
    ← RingHom.map_det]
  rfl

theorem padicValRat_nonneg_of_mem_goodP {x : ℚ} (hx : x ∈ GoodP p) :
    0 ≤ padicValRat p x := by
  have hp : Nat.Prime p := Fact.out
  have hnd : ¬ p ∣ x.den := hp.coprime_iff_not_dvd.mp hx.symm
  have hden0 : padicValNat p x.den = 0 := padicValNat.eq_zero_of_not_dvd hnd
  rw [padicValRat_def, hden0, Nat.cast_zero, sub_zero]
  exact Int.natCast_nonneg _

theorem vFrobeniusScaled_coeff_good (hp11 : 11 ≤ p) (q k i : ℕ) :
    (V.vFrobeniusScaledPolynomial q p k).coeff i ∈ GoodP p := by
  rw [vFrobeniusScaledPolynomial_eq_map_det_good hp11 q k, Polynomial.coeff_map]
  exact (((vScaledPencilGood hp11 q k).det).coeff i).2

theorem vFrobeniusScaled_coeff_integral (hp11 : 11 ≤ p) (q k i : ℕ) :
    (V.vFrobeniusScaledPolynomial q p k).coeff i ≠ 0 →
      0 ≤ padicValRat p ((V.vFrobeniusScaledPolynomial q p k).coeff i) := by
  intro _
  exact padicValRat_nonneg_of_mem_goodP (vFrobeniusScaled_coeff_good hp11 q k i)

end
end Li2Lean.B3
