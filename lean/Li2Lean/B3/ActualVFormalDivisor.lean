/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Mathlib
import Li2Lean.B3.ActualRationalIntegerizerGeneric
import Li2Lean.P0.IntegerizationS08Determinant

section

namespace Li2Lean.P0.Integerization.S08

open Finset

noncomputable section

/-- The diagonal series at `g = 0`, without the positive-`g` restriction
used in the general binomial identity. -/
theorem Ed_zero (x : ℕ) :
    Ed 0 x = co (P2 0 x) + L2 * co (uP 0 x) := by
  unfold Ed
  rw [bs_series]
  simp [Wb, hS]

/-- The off-central coefficient of the zero-shift diagonal series. -/
theorem coeff_B_zero (x k : ℕ) (hk : k ≠ x) :
    PowerSeries.coeff k (Ed 0 x) =
      cw 0 k * (((x : ℚ) - k)⁻¹) ^ 2 := by
  rw [Ed_zero, map_add, coeff_co, coeff_P2, coeff_L2_uP]
  rcases lt_or_gt_of_ne hk with hk | hk
  · have hnot : ¬ x ≤ k := by omega
    simp [hk, hnot]
  · have hnot : ¬ k < x := by omega
    have hle : x ≤ k := hk.le
    simp only [hnot, ite_false, hle, ite_true, zero_add, cw,
      Nat.add_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, one_mul]
    rw [Nat.cast_sub hle]
    rw [show (k : ℚ) - x = -((x : ℚ) - k) by ring, inv_neg]
    ring

/-- The full rank-one coefficient formula for the signed-V zero-shift
specialization. In particular, this covers the diagonal convention. -/
theorem coeff_low_zero (i j k : ℕ) :
    PowerSeries.coeff k (Eser 0 i j) = cw 0 k * lowF 0 i j k := by
  by_cases hij : i = j
  · subst hij
    have hE : Eser 0 i i = Ed 0 i := by
      unfold Eser Ed bP cP aP
      simp only [ite_true, map_mul, map_neg, co_C]
      unfold hS
      ring
    rw [hE]
    by_cases hk : k = i
    · subst hk
      unfold lowF gam eR vR
      simp only [ite_true]
      have := (cw_pos 0 k).ne'
      field_simp
      ring
    · rw [coeff_B_zero i k hk]
      have hik : i ≠ k := Ne.symm hk
      unfold lowF eR vR
      simp only [hik, ite_false]
      ring
  · have hE : Eser 0 i j =
        ((binv ^ 0 * co (tsP 0 i) - L1 * co (uP 0 i)) -
          (binv ^ 0 * co (tsP 0 j) - L1 * co (uP 0 j))) *
          PowerSeries.C (((j : ℚ) - (i : ℚ))⁻¹) := by
      unfold Eser bP cP aP
      simp only [hij, ite_false, map_mul, map_sub, map_zero, co_C,
        mul_zero, add_zero]
      ring
    rw [hE, PowerSeries.coeff_mul_C, map_sub, coeff_T, coeff_T,
      ← tau_divided_difference 0 i j k hij]
    ring

end

end Li2Lean.P0.Integerization.S08

namespace Li2Lean.B3.VFormalADivisor

open Li2Lean.P0.Integerization
open Li2Lean.P0.Integerization.S08

noncomputable section

theorem vFormalMomentT_eq_formalTScaled_zero (j : ℕ) :
    vFormalMomentT j = formalTScaled 0 j := by
  simp [vFormalMomentT, formalTScaled, formalU, formalQNum, aVar, ratConst]

theorem vFormalMomentB_eq_formalBScaled_zero (j : ℕ) :
    vFormalMomentB j = formalBScaled 0 j := by
  simp [vFormalMomentB, formalBScaled, formalU, formalQNum, aVar, ratConst]

theorem vFormalCEntry_eq_formalC_zero (i j : ℕ) :
    vFormalCEntry i j = formalC 0 i j := by
  by_cases hij : i = j
  · simp [vFormalCEntry, formalC, formalU, aVar, ratConst, hij]
  · simp [vFormalCEntry, formalC, formalU, aVar, ratConst, hij]

theorem vFormalBEntry_eq_formalB_zero (i j : ℕ) :
    vFormalBEntry i j = formalB 0 i j := by
  by_cases hij : i = j
  · simp [vFormalBEntry, formalB, vFormalMomentB_eq_formalBScaled_zero, hij]
  · simp [vFormalBEntry, formalB, vFormalMomentT_eq_formalTScaled_zero, hij]

theorem vFormalAEntry_eq_formalA_zero (i j : ℕ) :
    vFormalAEntry i j = formalA 0 i j := by
  by_cases hij : i = j <;>
    simp [vFormalAEntry, formalA, formalU, aVar, ratConst, hij]

theorem iota_vFormalCEntry (i j : ℕ) :
    iota (vFormalCEntry i j) = phiC (co (cP 0 i j)) := by
  rw [vFormalCEntry_eq_formalC_zero, formalC_eq, iota_map]

theorem iota_vFormalBEntry (i j : ℕ) :
    iota (vFormalBEntry i j) = phiC (co (bP 0 i j)) := by
  rw [vFormalBEntry_eq_formalB_zero, formalB_eq, iota_map]

theorem iota_vFormalAEntry (i j : ℕ) :
    iota (vFormalAEntry i j) = phiC (co (aP 0 i j)) := by
  rw [vFormalAEntry_eq_formalA_zero, formalA_eq, iota_map]

theorem iota_vFormalT : iota vFormalT = Tser := by
  unfold vFormalT
  rw [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_C]
  rfl

theorem iota_ratConst (q : ℚ) : iota (ratConst q) = kq q := by
  simp [ratConst, iota, kq, phiC,
    Polynomial.coeToPowerSeries.ringHom_apply]

theorem iota_vFormalVEntry (j ell : ℕ) :
    iota (vFormalVEntry j ell) = kq (V.vVEntry j ell) := by
  rw [vFormalVEntry, iota_ratConst]
  rfl

def rowIdx (n : ℕ) (r : Fin (V.vMatrixSize n)) : ℕ :=
  2 * n + (if r.val < V.vM n then r.val else r.val - V.vM n)

theorem rowIdx_bounds (n : ℕ) (r : Fin (V.vMatrixSize n))
    (hr : r.val < 2 * V.vM n) :
    2 * n ≤ rowIdx n r ∧ rowIdx n r < 6 * n := by
  simp only [V.vM] at hr
  unfold rowIdx V.vM
  split_ifs <;> omega

theorem iota_source (n : ℕ) (r c : Fin (V.vMatrixSize n)) :
    iota (vActualFormalSourceMatrix n r c) =
      if r.val < V.vM n then
        phiC (co (cP 0 (rowIdx n r) (V.vJIndex n c)))
      else if r.val < 2 * V.vM n then
        phiC (co (bP 0 (rowIdx n r) (V.vJIndex n c))) -
          Tser * phiC (co (aP 0 (rowIdx n r) (V.vJIndex n c)))
      else kq (((V.vJIndex n c + 1 +
        (r.val - 2 * V.vM n) : ℕ) : ℚ)⁻¹) := by
  unfold vActualFormalSourceMatrix rowIdx
  by_cases htop : r.val < V.vM n
  · simp only [htop, ite_true, iota_vFormalCEntry, V.vIIndexNat]
  · by_cases hmid : r.val < 2 * V.vM n
    · simp only [htop, hmid, ite_false, ite_true, map_sub, map_mul,
        iota_vFormalBEntry, iota_vFormalAEntry, iota_vFormalT]
    · simp only [htop, hmid, ite_false, iota_vFormalVEntry, V.vVEntry, Nat.add_assoc]

end

end Li2Lean.B3.VFormalADivisor

namespace Li2Lean.B3.VFormalADivisor

open Finset

noncomputable section

def D (n : ℕ) : ℕ := (53 * n ^ 2 + 2) / 3 - 4 * n

def allowed (n : ℕ) (f : ℕ × Fin 3) : Prop :=
  (f.2 = 1 → 2 * n ≤ f.1 ∧ f.1 < 6 * n) ∧
    (f.2 = 2 → n ≤ f.1 ∧ f.1 < 10 * n)

abbrev Feature (n : ℕ) := (Fin (D n) × Fin 3) ⊕ Fin n

open Classical in
def weight (n : ℕ) : Feature n → ℕ :=
  Sum.elim
    (fun f => if allowed n (f.1.val, f.2) then f.1.val else D n)
    (fun _ => 0)

private def lowerAllowed (n : ℕ) (f : ℕ × Fin 3) : Prop :=
  (f.2 = 1 → 2 * n ≤ f.1) ∧ (f.2 = 2 → n ≤ f.1)

private def threshold (n : ℕ) : ℕ := 11 * n / 3
private def remainder (n : ℕ) : ℕ := 11 * n % 3

private def lowestBase (n : ℕ) : Finset (ℕ × Fin 3) :=
  ((range (threshold n) ×ˢ {0}) ∪
    (Ico (2 * n) (threshold n) ×ˢ {1})) ∪
    (Ico n (threshold n) ×ˢ {2})

private def lowestTies (n : ℕ) : Finset (ℕ × Fin 3) :=
  {threshold n} ×ˢ (univ.filter fun t : Fin 3 => t.val < remainder n)

private def lowest (n : ℕ) : Finset (ℕ × Fin 3) :=
  lowestBase n ∪ lowestTies n

private theorem tagged_disjoint (S T : Finset ℕ) (a b : Fin 3) (hab : a ≠ b) :
    Disjoint (S ×ˢ {a}) (T ×ˢ {b}) := by
  apply Finset.disjoint_left.mpr
  intro f hf hg
  have ha := (Finset.mem_product.mp hf).2
  have hb := (Finset.mem_product.mp hg).2
  simp only [mem_singleton] at ha hb
  exact hab (ha.symm.trans hb)

private theorem lowestBase_disjoint₁ (n : ℕ) :
    Disjoint (range (threshold n) ×ˢ ({0} : Finset (Fin 3)))
      (Ico (2 * n) (threshold n) ×ˢ ({1} : Finset (Fin 3))) :=
  tagged_disjoint _ _ _ _ (by decide)

private theorem lowestBase_disjoint₂ (n : ℕ) :
    Disjoint
      ((range (threshold n) ×ˢ ({0} : Finset (Fin 3))) ∪
        (Ico (2 * n) (threshold n) ×ˢ ({1} : Finset (Fin 3))))
      (Ico n (threshold n) ×ˢ ({2} : Finset (Fin 3))) := by
  exact Finset.disjoint_union_left.mpr
    ⟨tagged_disjoint _ _ _ _ (by decide), tagged_disjoint _ _ _ _ (by decide)⟩

private theorem lowestBase_mem_iff (n : ℕ) (f : ℕ × Fin 3) :
    f ∈ lowestBase n ↔ lowerAllowed n f ∧ f.1 < threshold n := by
  rcases f with ⟨k, t⟩
  fin_cases t <;> simp [lowestBase, lowerAllowed] <;> omega

private theorem lowest_disjoint (n : ℕ) :
    Disjoint (lowestBase n) (lowestTies n) := by
  apply Finset.disjoint_left.mpr
  intro f hf hg
  have hlt := (lowestBase_mem_iff n f).mp hf |>.2
  have heq := (Finset.mem_product.mp hg).1
  simp only [mem_singleton] at heq
  omega

private theorem threshold_spec (n : ℕ) :
    3 * threshold n + remainder n = 11 * n ∧ remainder n < 3 ∧
      2 * n ≤ threshold n := by
  dsimp [threshold, remainder]
  omega

private theorem fin3_filter_card (r : ℕ) (hr : r ≤ 3) :
    (univ.filter fun t : Fin 3 => t.val < r).card = r := by
  interval_cases r <;> decide

private theorem lowestBase_card (n : ℕ) :
    (lowestBase n).card + 3 * n = 3 * threshold n := by
  have hb := (threshold_spec n).2.2
  rw [lowestBase, card_union_of_disjoint (lowestBase_disjoint₂ n),
    card_union_of_disjoint (lowestBase_disjoint₁ n)]
  simp
  omega

private theorem lowestTies_card (n : ℕ) :
    (lowestTies n).card = remainder n := by
  rw [lowestTies, card_product, card_singleton, one_mul]
  exact fin3_filter_card _ (Nat.le_of_lt (threshold_spec n).2.1)

private theorem lowest_card (n : ℕ) : (lowest n).card = 8 * n := by
  have hc := lowestBase_card n
  have hb := (threshold_spec n).1
  rw [lowest, card_union_of_disjoint (lowest_disjoint n), lowestTies_card]
  omega

private theorem lowest_weight_le (n : ℕ) (f : ℕ × Fin 3) (hf : f ∈ lowest n) :
    f.1 ≤ threshold n := by
  rcases Finset.mem_union.mp hf with h | h
  · exact ((lowestBase_mem_iff n f).mp h).2.le
  · have heq := (Finset.mem_product.mp h).1
    simp only [mem_singleton] at heq
    exact heq.le

private theorem lower_weight_ge_of_not_mem (n : ℕ) (f : ℕ × Fin 3)
    (ha : lowerAllowed n f) (hf : f ∉ lowest n) : threshold n ≤ f.1 := by
  by_contra h
  exact hf (Finset.mem_union_left _ ((lowestBase_mem_iff n f).mpr
    ⟨ha, Nat.lt_of_not_ge h⟩))

private theorem twice_sum_range (b : ℕ) :
    2 * (∑ k ∈ range b, k) + b = b ^ 2 := by
  have hs := Finset.sum_range_id_mul_two b
  by_cases hb : b = 0
  · simp [hb]
  · have hsub : b - 1 + 1 = b := by omega
    nlinarith

private theorem twice_sum_Ico (l b : ℕ) (hlb : l ≤ b) :
    2 * (∑ k ∈ Ico l b, k) + b + l ^ 2 = b ^ 2 + l := by
  have hsplit := Finset.sum_range_add_sum_Ico (fun k : ℕ => k) hlb
  have hl := twice_sum_range l
  have hb := twice_sum_range b
  nlinarith

private theorem lowestBase_weight (n : ℕ) :
    2 * (∑ f ∈ lowestBase n, f.1) + 3 * threshold n + 5 * n ^ 2 =
      3 * (threshold n) ^ 2 + 3 * n := by
  have hb := (threshold_spec n).2.2
  have h0 := twice_sum_range (threshold n)
  have h1 := twice_sum_Ico (2 * n) (threshold n) hb
  have h2 := twice_sum_Ico n (threshold n) (by omega)
  rw [lowestBase, Finset.sum_union (lowestBase_disjoint₂ n),
    Finset.sum_union (lowestBase_disjoint₁ n)]
  simp only [Finset.sum_product, Finset.sum_singleton]
  nlinarith

private theorem lowestTies_weight (n : ℕ) :
    (∑ f ∈ lowestTies n, f.1) = threshold n * remainder n := by
  simp only [lowestTies, Finset.sum_product, Finset.sum_singleton,
    Finset.sum_const, nsmul_eq_mul]
  rw [fin3_filter_card _ (Nat.le_of_lt (threshold_spec n).2.1)]
  exact Nat.mul_comm _ _

private theorem lowest_weight (n : ℕ) :
    D n ≤ ∑ f ∈ lowest n, f.1 := by
  have hbase := lowestBase_weight n
  have hspec := (threshold_spec n).1
  have hsquare := congrArg (fun k : ℕ => k ^ 2) hspec
  have hrem : remainder n * remainder n ≤ 3 * remainder n := by
    exact Nat.mul_le_mul_right _ (Nat.le_of_lt (threshold_spec n).2.1)
  have htotal : (∑ f ∈ lowest n, f.1) =
      (∑ f ∈ lowestBase n, f.1) + threshold n * remainder n := by
    rw [lowest, Finset.sum_union (lowest_disjoint n), lowestTies_weight]
  have hquad : 53 * n ^ 2 ≤ 3 * (∑ f ∈ lowest n, f.1) + 12 * n := by
    nlinarith
  dsimp [D]
  omega

private def ambientWeight (n : ℕ) : (ℕ × Fin 3) ⊕ Fin n → ℕ :=
  Sum.elim Prod.fst (fun _ => 0)

private theorem ambient_weight_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι] (n : ℕ)
    (hι : Fintype.card ι = 9 * n)
    (p : ι → (ℕ × Fin 3) ⊕ Fin n) (hp : Function.Injective p)
    (ha : ∀ j f, p j = Sum.inl f → lowerAllowed n f) :
    D n ≤ ∑ j, ambientWeight n (p j) := by
  classical
  let S := Finset.univ.image p
  let T := (lowest n).disjSum (Finset.univ : Finset (Fin n))
  have hcard : S.card = T.card := by
    simp only [S, Finset.card_image_of_injective _ hp, Finset.card_univ,
      T, Finset.card_disjSum, lowest_card, Fintype.card_fin]
    omega
  have hle := Li2Lean.P0.Integerization.sum_ge_lowest_of_equal_card S T
    (ambientWeight n) (threshold n) hcard
    (by
      intro x hx
      cases x with
      | inl f =>
          exact lowest_weight_le n f (Finset.inl_mem_disjSum.mp hx)
      | inr t => exact Nat.zero_le _)
    (by
      intro x hx hnot
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
      cases he : p j with
      | inl f =>
          exact lower_weight_ge_of_not_mem n f (ha j f he)
            (fun hf => hnot (by simpa [he, T] using hf))
      | inr t =>
          exact False.elim (hnot (by simp [he, T])))
  have hT : (∑ x ∈ T, ambientWeight n x) = ∑ f ∈ lowest n, f.1 := by
    simp [T, Finset.sum_disjSum, ambientWeight]
  rw [hT] at hle
  have hS : (∑ x ∈ S, ambientWeight n x) = ∑ j, ambientWeight n (p j) := by
    simp only [S, Finset.sum_image (fun _ _ _ _ he => hp he)]
  rw [hS] at hle
  exact (lowest_weight n).trans hle

private def toAmbient (n : ℕ) : Feature n → (ℕ × Fin 3) ⊕ Fin n :=
  Sum.map (fun f => (f.1.val, f.2)) id

private theorem toAmbient_injective (n : ℕ) : Function.Injective (toAmbient n) := by
  unfold toAmbient
  apply Sum.map_injective.mpr
  refine ⟨?_, Function.injective_id⟩
  intro f g hfg
  apply Prod.ext
  · exact Fin.ext (congrArg (fun x : ℕ × Fin 3 => x.1) hfg)
  · exact congrArg (fun x : ℕ × Fin 3 => x.2) hfg

theorem weight_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι] (n : ℕ)
    (hι : Fintype.card ι = 9 * n)
    (p : ι → Feature n) (hp : Function.Injective p) :
    D n ≤ ∑ j, weight n (p j) := by
  classical
  by_cases hall : ∀ j f, p j = Sum.inl f → allowed n (f.1.val, f.2)
  · have hle := ambient_weight_bound n hι (fun j => toAmbient n (p j))
      ((toAmbient_injective n).comp hp) (by
        intro j f he
        cases hj : p j with
        | inl g =>
            have hgf : (g.1.val, g.2) = f := by
              simpa [hj, toAmbient] using he
            rw [← hgf]
            have hallow := hall j g hj
            exact ⟨fun ht => (hallow.1 ht).1, fun ht => (hallow.2 ht).1⟩
        | inr t => simp [hj, toAmbient] at he)
    have hw : ∀ j, ambientWeight n (toAmbient n (p j)) = weight n (p j) := by
      intro j
      cases hj : p j with
      | inl f => simp [toAmbient, ambientWeight, weight, hall j f hj]
      | inr t => rfl
    simpa only [hw] using hle
  · push_neg at hall
    obtain ⟨j, f, hj, hf⟩ := hall
    have hw : weight n (p j) = D n := by simp [hj, weight, hf]
    rw [← hw]
    exact Finset.single_le_sum (f := fun k => weight n (p k))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)

end
end Li2Lean.B3.VFormalADivisor

namespace Li2Lean.B3.VFormalADivisor

open Finset Li2Lean.P0.Integerization Li2Lean.P0.Integerization.S08

noncomputable section

private def ordinaryU (n k : ℕ) (t : Fin 3)
    (r : Fin (V.vMatrixSize n)) : PS :=
  if r.val < V.vM n then kq (cw 0 k * topL 0 t k (rowIdx n r))
  else if r.val < 2 * V.vM n then
    kq (cw 0 k * lowL 0 t k (rowIdx n r)) +
      phiC L1 * kq (cw 0 k * topL 0 t k (rowIdx n r)) -
      (if t = 2 then Yser 0 * kq (cw 0 k * eR (rowIdx n r) k) else 0)
  else 0

private def ordinaryV (n k : ℕ) (t : Fin 3)
    (c : Fin (V.vMatrixSize n)) : PS :=
  kq (rgt t k (V.vJIndex n c))

private def featureU (n : ℕ) : Feature n → Fin (V.vMatrixSize n) → PS
  | Sum.inl f, r => ordinaryU n f.1 f.2 r
  | Sum.inr ell, r => if r.val = 2 * V.vM n + ell.val then 1 else 0

private def featureV (n : ℕ) : Feature n → Fin (V.vMatrixSize n) → PS
  | Sum.inl f, c => ordinaryV n f.1 f.2 c
  | Sum.inr ell, c => kq ((((V.vJIndex n c + (1 + ell.val) : ℕ) : ℚ))⁻¹)

private def featureMatrix (n : ℕ) :
    Matrix (Fin (V.vMatrixSize n)) (Fin (V.vMatrixSize n)) PS :=
  Matrix.of fun r c => ∑ f : Feature n,
    featureU n f r * (PowerSeries.X ^ weight n f * featureV n f c)

private theorem featureMatrix_det_dvd (n : ℕ) :
    PowerSeries.X ^ D n ∣ (featureMatrix n).det := by
  apply pow_dvd_det_weighted_rank_one
  intro p hp
  exact weight_bound n (by simp [V.vMatrixSize_eq]) p hp

private theorem ordinary_forbidden (n k : ℕ) (t : Fin 3)
    (r c : Fin (V.vMatrixSize n)) (hf : ¬ allowed n (k, t)) :
    ordinaryU n k t r * ordinaryV n k t c = 0 := by
  have hc := V.vJIndex_mem n c
  unfold allowed at hf
  simp only [not_and_or, not_imp] at hf
  rcases hf with ⟨ht, hk⟩ | ⟨ht, hk⟩
  · subst ht
    have hz : ordinaryU n k 1 r = 0 := by
      unfold ordinaryU
      by_cases hr : r.val < V.vM n
      · simp [hr, topL]
      · by_cases hr' : r.val < 2 * V.vM n
        · have hi : rowIdx n r ≠ k := by
            have hrb := rowIdx_bounds n r hr'
            omega
          simp [hr, hr', topL, lowL, eR, hi]
        · simp [hr, hr']
    rw [hz, zero_mul]
  · subst ht
    have hj : V.vJIndex n c ≠ k := by
      omega
    have hz : ordinaryV n k 2 c = 0 := by
      simp [ordinaryV, rgt, eR, hj]
    rw [hz, mul_zero]

private theorem ordinary_sum (n : ℕ) (r c : Fin (V.vMatrixSize n)) :
    (∑ f : Fin (D n) × Fin 3,
      featureU n (Sum.inl f) r *
        (PowerSeries.X ^ weight n (Sum.inl f) * featureV n (Sum.inl f) c)) =
      ∑ k ∈ range (D n), ∑ t : Fin 3,
        ordinaryU n k t r * (PowerSeries.X ^ k * ordinaryV n k t c) := by
  classical
  rw [Fintype.sum_prod_type]
  rw [← Fin.sum_univ_eq_sum_range (fun k => ∑ t : Fin 3,
    ordinaryU n k t r * (PowerSeries.X ^ k * ordinaryV n k t c))]
  apply sum_congr rfl
  intro k _
  apply sum_congr rfl
  intro t _
  change ordinaryU n k t r *
      (PowerSeries.X ^ (if allowed n (k.val, t) then k.val else D n) *
        ordinaryV n k t c) = _
  split_ifs with hf
  · rfl
  · have hz := ordinary_forbidden n k t r c hf
    calc
      ordinaryU n k t r *
          (PowerSeries.X ^ D n * ordinaryV n k t c) =
          PowerSeries.X ^ D n * (ordinaryU n k t r * ordinaryV n k t c) := by ring
      _ = 0 := by rw [hz, mul_zero]
      _ = PowerSeries.X ^ (k : ℕ) *
          (ordinaryU n k t r * ordinaryV n k t c) := by rw [hz, mul_zero]
      _ = ordinaryU n k t r *
          (PowerSeries.X ^ (k : ℕ) * ordinaryV n k t c) := by ring

private theorem cauchy_sum (n : ℕ) (r c : Fin (V.vMatrixSize n)) :
    (∑ ell : Fin n, featureU n (Sum.inr ell) r *
      (PowerSeries.X ^ weight n (Sum.inr ell) * featureV n (Sum.inr ell) c)) =
      if r.val < 2 * V.vM n then 0
      else kq ((((V.vJIndex n c + 1 + (r.val - 2 * V.vM n) : ℕ) : ℚ))⁻¹) := by
  classical
  by_cases hr : r.val < 2 * V.vM n
  · rw [if_pos hr]
    apply sum_eq_zero
    intro ell _
    have he : r.val ≠ 2 * V.vM n + ell.val := by omega
    simp [featureU, he]
  · rw [if_neg hr]
    have hrsize : r.val < 2 * V.vM n + n := by
      simpa only [V.vMatrixSize, V.vS] using r.isLt
    let ell0 : Fin n := ⟨r.val - 2 * V.vM n, by omega⟩
    rw [Finset.sum_eq_single ell0]
    · have he : r.val = 2 * V.vM n + ell0.val := by dsimp [ell0]; omega
      simp only [featureU, if_pos he, featureV, weight, Sum.elim_inr,
        pow_zero, one_mul]
      simp only [ell0, Nat.add_assoc]
    · intro ell _ hne
      have he : r.val ≠ 2 * V.vM n + ell.val := by
        intro he
        apply hne
        apply Fin.ext
        dsimp [ell0]
        omega
      simp [featureU, he]
    · simp

private theorem featureMatrix_apply (n : ℕ) (r c : Fin (V.vMatrixSize n)) :
    featureMatrix n r c =
      (∑ k ∈ range (D n), ∑ t : Fin 3,
        ordinaryU n k t r * (PowerSeries.X ^ k * ordinaryV n k t c)) +
      (if r.val < 2 * V.vM n then 0
      else kq ((((V.vJIndex n c + 1 + (r.val - 2 * V.vM n) : ℕ) : ℚ))⁻¹)) := by
  unfold featureMatrix
  rw [Matrix.of_apply, Fintype.sum_sum_type, ordinary_sum, cauchy_sum]

private theorem entry_congr (n : ℕ) (r c : Fin (V.vMatrixSize n)) :
    PowerSeries.X ^ D n ∣
      iota (vActualFormalSourceMatrix n r c) - featureMatrix n r c := by
  let i := rowIdx n r
  let j := V.vJIndex n c
  have dC := X_pow_dvd_sub_trunc (D n) (co (cP 0 i j))
    (fun k => cw 0 k * topF 0 i j k) (fun k _ => coeff_top 0 i j k)
  have dE := X_pow_dvd_sub_trunc (D n) (Eser 0 i j)
    (fun k => cw 0 k * lowF 0 i j k) (fun k _ => coeff_low_zero i j k)
  have dA := X_pow_dvd_sub_trunc (D n) (co (aP 0 i j))
    (fun k => cw 0 k * (eR i k * eR j k)) (fun k _ => coeff_aP 0 i j k)
  have mC := phiC_X_pow_dvd dC
  have mE := phiC_X_pow_dvd dE
  have mA := phiC_X_pow_dvd dA
  simp only [map_sub, phiC_trunc] at mC mE mA
  rw [featureMatrix_apply, iota_source]
  by_cases hr : r.val < V.vM n
  · have hr' : r.val < 2 * V.vM n := by omega
    rw [if_pos hr, if_pos hr', add_zero]
    have hs : (∑ k ∈ range (D n), ∑ t : Fin 3,
        ordinaryU n k t r * (PowerSeries.X ^ k * ordinaryV n k t c)) =
        ∑ k ∈ range (D n), kq (cw 0 k * topF 0 i j k) * PowerSeries.X ^ k := by
      apply sum_congr rfl
      intro k _
      rw [← top_row_sum]
      apply sum_congr rfl
      intro t _
      simp only [ordinaryU, ordinaryV, if_pos hr]
      rfl
    rw [hs]
    exact mC
  · rw [if_neg hr]
    by_cases hr' : r.val < 2 * V.vM n
    · rw [if_pos hr', if_pos hr', add_zero]
      have hs : (∑ k ∈ range (D n), ∑ t : Fin 3,
          ordinaryU n k t r * (PowerSeries.X ^ k * ordinaryV n k t c)) =
          (∑ k ∈ range (D n), kq (cw 0 k * lowF 0 i j k) * PowerSeries.X ^ k) +
          phiC L1 * (∑ k ∈ range (D n), kq (cw 0 k * topF 0 i j k) * PowerSeries.X ^ k) -
          Yser 0 * (∑ k ∈ range (D n),
            kq (cw 0 k * (eR i k * eR j k)) * PowerSeries.X ^ k) := by
        rw [mul_sum (s := range (D n)) (a := phiC L1),
          mul_sum (s := range (D n)) (a := Yser 0),
          ← sum_add_distrib, ← sum_sub_distrib]
        apply sum_congr rfl
        intro k _
        have ht := low_row_sum 0 i j k (1 : PS) (phiC L1) (Yser 0)
        simp only [one_mul] at ht
        rw [← ht]
        apply sum_congr rfl
        intro t _
        simp only [ordinaryU, ordinaryV, if_neg hr, if_pos hr']
        rfl
      rw [hs]
      have hb : phiC (co (bP 0 i j)) =
          phiC (Eser 0 i j) + phiC L1 * phiC (co (cP 0 i j)) -
            phiC L2 * phiC (co (aP 0 i j)) := by
        simp only [Eser, pow_zero, one_mul, map_add, map_sub, map_mul]
        ring
      rw [hb]
      have key :
          phiC (Eser 0 i j) + phiC L1 * phiC (co (cP 0 i j)) -
            phiC L2 * phiC (co (aP 0 i j)) - Tser * phiC (co (aP 0 i j)) -
          ((∑ k ∈ range (D n), kq (cw 0 k * lowF 0 i j k) * PowerSeries.X ^ k) +
            phiC L1 * (∑ k ∈ range (D n), kq (cw 0 k * topF 0 i j k) * PowerSeries.X ^ k) -
            Yser 0 * (∑ k ∈ range (D n),
              kq (cw 0 k * (eR i k * eR j k)) * PowerSeries.X ^ k)) =
          (phiC (Eser 0 i j) -
            ∑ k ∈ range (D n), kq (cw 0 k * lowF 0 i j k) * PowerSeries.X ^ k) +
          phiC L1 * (phiC (co (cP 0 i j)) -
            ∑ k ∈ range (D n), kq (cw 0 k * topF 0 i j k) * PowerSeries.X ^ k) -
          Yser 0 * (phiC (co (aP 0 i j)) -
            ∑ k ∈ range (D n),
              kq (cw 0 k * (eR i k * eR j k)) * PowerSeries.X ^ k) := by
        simp only [Yser, pow_zero, mul_one]
        ring
      rw [key]
      exact dvd_sub (dvd_add mE (dvd_mul_of_dvd_right mC _))
        (dvd_mul_of_dvd_right mA _)
    · rw [if_neg hr', if_neg hr']
      have hs : (∑ k ∈ range (D n), ∑ t : Fin 3,
          ordinaryU n k t r * (PowerSeries.X ^ k * ordinaryV n k t c)) = 0 := by
        simp [ordinaryU, hr, hr']
      rw [hs, zero_add, sub_self]
      exact dvd_zero _

/-- The paper's formal a-divisor on the literal signed-V matrix. -/
theorem formal_a_divisor (n : ℕ) :
    (Polynomial.X : BivPoly) ^ D n ∣ (vActualFormalSourceMatrix n).det := by
  have hdet : PowerSeries.X ^ D n ∣ iota ((vActualFormalSourceMatrix n).det) := by
    rw [RingHom.map_det]
    apply dvd_det_of_entrywise_congr _ _ (featureMatrix n)
    · exact entry_congr n
    · exact featureMatrix_det_dvd n
  rw [Polynomial.X_pow_dvd_iff]
  intro d hd
  have hz := (PowerSeries.X_pow_dvd_iff.mp hdet) d hd
  rwa [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coeff_coe] at hz

end
end Li2Lean.B3.VFormalADivisor

namespace Li2Lean.B3.VFormalADivisor

open Li2Lean.P0.Integerization Li2Lean.P0.Integerization.S08

noncomputable section

/-- Monic descent followed by integral specialization of the formal divisor. -/
theorem coeff_witness (q n : ℕ) (hn : 0 < n) :
    ∃ P : Polynomial ℤ,
      (∀ i, (-(q : ℤ)) ^ D n ∣ P.coeff i) ∧
      P.map (Int.castRingHom ℚ) =
        Polynomial.C (vActualBaselineD n) * V.actualVDeterminant q (4 * n) := by
  classical
  obtain ⟨Z, hZ⟩ := vActualFormalDeterminant_integerized n hn
  have hdivQ : (Polynomial.X : BivPoly) ^ D n ∣ psi (Matrix.det Z) := by
    rw [hZ]
    exact dvd_mul_of_dvd_right (formal_a_divisor n) _
  have hdivZ := int_bivariate_x_pow_dvd_of_rat_map hdivQ
  have hspec := IntegerizationScalarSpecialization.eval_dvd_eval_of_X_pow
    (Matrix.det Z) (Polynomial.C (-(q : ℤ))) (D n) hdivZ
  refine ⟨(Matrix.det Z).eval (Polynomial.C (-(q : ℤ))), ?_, ?_⟩
  · intro i
    have hs : Polynomial.C ((-(q : ℤ)) ^ D n) ∣
        (Matrix.det Z).eval (Polynomial.C (-(q : ℤ))) := by
      simpa only [Polynomial.C_pow] using hspec
    exact (Polynomial.C_dvd_iff_dvd_coeff _ _).mp hs i
  · rw [← Li2Lean.B3.outerEval_psi_int, hZ, map_mul]
    simp only [Int.cast_neg, Int.cast_natCast]
    rw [outerEval_actualVDeterminant]
    congr 1
    simp only [map_prod, outerEval_ratConst]
    rw [← map_prod, vActualFormalRowScale_prod]
    rfl

/-- The formal a-credit for each actual signed-V coefficient. -/
theorem coeff_lower (q n p i : ℕ) (hq : 2 ≤ q) (hn : 0 < n)
    (hp : p.Prime) (hc : (V.actualVDeterminant q (4 * n)).coeff i ≠ 0) :
    (D n : ℤ) * (padicValNat p q : ℤ) -
      ((12 * n * Nat.log p (V.vN n) + n * Nat.log p (V.vU n) : ℕ) : ℤ) ≤
      padicValRat p ((V.actualVDeterminant q (4 * n)).coeff i) := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, hdiv, hP⟩ := coeff_witness q n hn
  have hcoeff := congrArg (fun R : Polynomial ℚ => R.coeff i) hP
  simp only [Polynomial.coeff_map, Polynomial.coeff_C_mul] at hcoeff
  change (P.coeff i : ℚ) =
    vActualBaselineD n * (V.actualVDeterminant q (4 * n)).coeff i at hcoeff
  obtain ⟨z, hz⟩ := hdiv i
  rw [hz] at hcoeff
  push_cast at hcoeff
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have hz0 : (z : ℚ) ≠ 0 := by
    intro hz0
    rw [hz0, mul_zero] at hcoeff
    exact mul_ne_zero (ne_of_gt (vActualBaselineD_pos n)) hc hcoeff.symm
  have hv := congrArg (padicValRat p) hcoeff
  rw [padicValRat.mul (pow_ne_zero _ (neg_ne_zero.mpr hq0)) hz0,
    padicValRat.mul (ne_of_gt (vActualBaselineD_pos n)) hc,
    padicValRat.pow, padicValRat.neg, padicValRat.of_nat,
    padicValRat.of_int, vActualBaselineD_padicVal n p hp] at hv
  have hzval : (0 : ℤ) ≤ padicValInt p z := Int.natCast_nonneg _
  omega

end
end Li2Lean.B3.VFormalADivisor

namespace Li2Lean.B3

/-- The p | q branch with the v13 exponent, including the zero index.
The coefficient-zero alternative respects Mathlib's convention for padicValRat 0. -/
theorem actualV_coefficient_val_of_dvd_q (q n p i : ℕ)
    (hq : SignedVBaseRange q) (hp : p.Prime) (_hpq : p ∣ q) :
    (V.actualVDeterminant q (4 * n)).coeff i = 0 ∨
      -(((12 * n * Nat.log p (V.vN n) + n * Nat.log p (V.vU n) : ℕ) : ℤ) -
          (((53 * n ^ 2 + 2) / 3 - 4 * n : ℕ) : ℤ) * (padicValNat p q : ℤ)) ≤
        padicValRat p ((V.actualVDeterminant q (4 * n)).coeff i) := by
  by_cases hc : (V.actualVDeterminant q (4 * n)).coeff i = 0
  · exact Or.inl hc
  right
  by_cases hn : 0 < n
  · have h := VFormalADivisor.coeff_lower q n p i hq.1 hn hp hc
    simpa only [VFormalADivisor.D, neg_sub] using h
  · have hn0 : n = 0 := by omega
    subst n
    simp only [mul_zero, V.actualVDeterminant_zero_generic] at hc ⊢
    have hi : i = 0 := by
      by_contra hi
      exact hc (by simp only [Polynomial.coeff_one, hi, ite_false])
    subst i
    norm_num

end Li2Lean.B3

open Finset Polynomial

namespace Li2Lean.B3.VFormalADivisor

noncomputable section

lemma polynomial_alternating_eq_zero (P : ℚ[X]) (N : ℕ)
    (hdegree : P.natDegree < N) (x₀ : ℚ)
    (hsign : ∀ k ≤ N, 0 ≤ (-1 : ℚ) ^ k * P.eval (x₀ + k)) :
    ∀ k ≤ N, P.eval (x₀ + k) = 0 := by
  have hfd := congrFun (Polynomial.fwdDiff_iter_eq_zero_of_degree_lt hdegree) x₀
  rw [fwdDiff_iter_eq_sum_shift] at hfd
  have hsum : ∑ k ∈ range (N + 1),
      (-1 : ℚ) ^ (N - k) * (N.choose k : ℚ) * P.eval (x₀ + k) = 0 := by
    simpa only [zsmul_eq_mul, Int.cast_mul, Int.cast_pow, Int.cast_neg,
      Int.cast_one, Int.cast_natCast, nsmul_eq_mul, mul_one, Pi.zero_apply] using hfd
  have hpow (k : ℕ) (hk : k ≤ N) :
      (-1 : ℚ) ^ N * (-1 : ℚ) ^ (N - k) = (-1 : ℚ) ^ k := by
    calc
      (-1 : ℚ) ^ N * (-1 : ℚ) ^ (N - k) =
          ((-1 : ℚ) ^ (N - k) * (-1 : ℚ) ^ k) * (-1 : ℚ) ^ (N - k) := by
        rw [← pow_add (-1 : ℚ) (N - k) k, Nat.sub_add_cancel hk]
      _ =
          ((-1 : ℚ) ^ (N - k) * (-1 : ℚ) ^ (N - k)) * (-1 : ℚ) ^ k := by
        ring
      _ = (-1 : ℚ) ^ k := by rw [← mul_pow]; norm_num
  have hz : ∑ k ∈ range (N + 1),
      (N.choose k : ℚ) * ((-1 : ℚ) ^ k * P.eval (x₀ + k)) = 0 := by
    have hh := congrArg (fun x : ℚ => (-1 : ℚ) ^ N * x) hsum
    simp only [mul_zero, Finset.mul_sum] at hh
    convert hh using 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [show (-1 : ℚ) ^ N *
        ((-1 : ℚ) ^ (N - k) * (N.choose k : ℚ) * P.eval (x₀ + k)) =
        (N.choose k : ℚ) *
          (((-1 : ℚ) ^ N * (-1 : ℚ) ^ (N - k)) * P.eval (x₀ + k)) by ring,
      hpow k (by simpa using mem_range.mp hk)]
  have hnonneg (k : ℕ) (hk : k ∈ range (N + 1)) :
      0 ≤ (N.choose k : ℚ) * ((-1 : ℚ) ^ k * P.eval (x₀ + k)) :=
    mul_nonneg (by positivity) (hsign k (by simpa using mem_range.mp hk))
  have hz' := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hz
  intro k hk
  have hk' : k ∈ range (N + 1) := mem_range.mpr (by omega)
  have hchoose : (N.choose k : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hk).ne'
  have hm := (mul_eq_zero.mp (hz' k hk')).resolve_left hchoose
  exact (mul_eq_zero.mp hm).resolve_left (pow_ne_zero _ (by norm_num))

def negativeRootProduct (n : ℕ) : ℚ[X] :=
  ∏ l : Fin n, (X - C (-((l.val + 1 : ℕ) : ℚ)))

lemma negativeRootProduct_monic (n : ℕ) : (negativeRootProduct n).Monic :=
  monic_prod_X_sub_C _ _

lemma negativeRootProduct_natDegree (n : ℕ) :
    (negativeRootProduct n).natDegree = n := by
  simp only [negativeRootProduct, natDegree_finsetProd_X_sub_C_eq_card,
    Finset.card_univ, Fintype.card_fin]

lemma negativeRootProduct_eval_pos (n : ℕ) (x : ℚ) (hx : 0 ≤ x) :
    0 < (negativeRootProduct n).eval x := by
  simp only [negativeRootProduct, eval_prod, eval_sub, eval_X, eval_C]
  apply Finset.prod_pos
  intro l _
  have : (0 : ℚ) < ((l.val + 1 : ℕ) : ℚ) := by positivity
  linarith

lemma negativeRootProduct_dvd (n : ℕ) (U : ℚ[X])
    (hroot : ∀ l : Fin n, U.eval (-((l.val + 1 : ℕ) : ℚ)) = 0) :
    negativeRootProduct n ∣ U := by
  have hinj : Function.Injective (fun l : Fin n => -((l.val + 1 : ℕ) : ℚ)) := by
    intro l k h
    apply Fin.ext
    have h' : l.val + 1 = k.val + 1 := by exact_mod_cast neg_injective h
    omega
  exact Fintype.prod_dvd_of_coprime (pairwise_coprime_X_sub_C hinj)
    (fun l => dvd_iff_isRoot.mpr (hroot l))

lemma numerator_pair_zero (n : ℕ) (hn : 0 < n) (q : ℚ) (hq : 0 < q)
    (U W : ℚ[X]) (hU : U.natDegree < 5 * n) (hW : W.natDegree < 5 * n)
    (hroot : ∀ l : Fin n, U.eval (-((l.val + 1 : ℕ) : ℚ)) = 0)
    (hvalues : ∀ k : Fin (9 * n),
      W.eval ((n + k.val : ℕ) : ℚ) =
        (-q) ^ (n + k.val) * U.eval ((n + k.val : ℕ) : ℚ)) : U = 0 := by
  by_contra hU0
  obtain ⟨H, hH⟩ := negativeRootProduct_dvd n U hroot
  have hH0 : H ≠ 0 := by
    intro h
    apply hU0
    simp [hH, h]
  have hHd : H.natDegree < 4 * n := by
    rw [hH, natDegree_mul (negativeRootProduct_monic n).ne_zero hH0,
      negativeRootProduct_natDegree] at hU
    omega
  let P : ℚ[X] := C ((-1 : ℚ) ^ n) * (H * W)
  have hPd : P.natDegree < 9 * n - 1 := by
    have hle : P.natDegree ≤ H.natDegree + W.natDegree :=
      (natDegree_C_mul_le _ _).trans natDegree_mul_le
    omega
  have hnonneg : ∀ k ≤ 9 * n - 1,
      0 ≤ (-1 : ℚ) ^ k * P.eval ((n : ℚ) + k) := by
    intro k hk
    have hk' : k < 9 * n := by omega
    have hvalue := hvalues ⟨k, hk'⟩
    simp only [Nat.cast_add] at hvalue
    rw [hH, eval_mul] at hvalue
    have hidentity : (-1 : ℚ) ^ k * P.eval ((n : ℚ) + k) =
        q ^ (n + k) * (negativeRootProduct n).eval ((n : ℚ) + k) *
          (H.eval ((n : ℚ) + k)) ^ 2 := by
      simp only [P, eval_mul, eval_C]
      rw [hvalue]
      have hs : (-1 : ℚ) ^ (n + k) * (-q) ^ (n + k) = q ^ (n + k) := by
        rw [← mul_pow]
        congr 1
        ring
      rw [pow_add] at hs
      calc
        (-1 : ℚ) ^ k *
            ((-1 : ℚ) ^ n * (H.eval ((n : ℚ) + k) *
              ((-q) ^ (n + k) *
                ((negativeRootProduct n).eval ((n : ℚ) + k) *
                  H.eval ((n : ℚ) + k))))) =
            (((-1 : ℚ) ^ n * (-1 : ℚ) ^ k) * (-q) ^ (n + k)) *
              (negativeRootProduct n).eval ((n : ℚ) + k) *
                (H.eval ((n : ℚ) + k)) ^ 2 := by ring
        _ = _ := by rw [hs]
    rw [hidentity]
    exact mul_nonneg (mul_nonneg (pow_nonneg hq.le _)
      (negativeRootProduct_eval_pos n _ (by positivity)).le) (sq_nonneg _)
  have hPeval := polynomial_alternating_eq_zero P (9 * n - 1) hPd (n : ℚ) hnonneg
  have hHeval : ∀ k : Fin (9 * n), H.eval ((n + k.val : ℕ) : ℚ) = 0 := by
    intro k
    have hPk := hPeval k.val (by omega)
    have hvalue := hvalues k
    rw [hH, eval_mul] at hvalue
    simp only [P, eval_mul, eval_C] at hPk
    have hPk' : H.eval ((n + k.val : ℕ) : ℚ) *
        W.eval ((n + k.val : ℕ) : ℚ) = 0 := by
      have hs : (-1 : ℚ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
      apply (mul_eq_zero.mp (show (-1 : ℚ) ^ n *
        (H.eval ((n + k.val : ℕ) : ℚ) * W.eval ((n + k.val : ℕ) : ℚ)) = 0 from ?_)).resolve_left hs
      simpa only [Nat.cast_add] using hPk
    rw [hvalue] at hPk'
    have ha : (-q) ^ (n + k.val) ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr hq.ne')
    have hN : (negativeRootProduct n).eval ((n + k.val : ℕ) : ℚ) ≠ 0 :=
      (negativeRootProduct_eval_pos n _ (by positivity)).ne'
    rcases mul_eq_zero.mp hPk' with hz | hz
    · exact hz
    · exact (mul_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left ha)).resolve_left hN
  have hinj : Function.Injective (fun k : Fin (9 * n) => ((n + k.val : ℕ) : ℚ)) := by
    intro k l h
    change ((n + k.val : ℕ) : ℚ) = ((n + l.val : ℕ) : ℚ) at h
    apply Fin.ext
    have h' : n + k.val = n + l.val := by exact_mod_cast h
    omega
  exact hH0 (eq_zero_of_natDegree_lt_card_of_eval_eq_zero H hinj hHeval (by
    simp only [Fintype.card_fin]
    omega))

def rationalNumerator {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v c : ι → ℚ) : ℚ[X] :=
  ∑ j, C (c j) * ∏ k ∈ univ.erase j, (X - C (v k))

lemma rationalNumerator_natDegree {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v c : ι → ℚ) :
    (rationalNumerator v c).natDegree ≤ Fintype.card ι - 1 := by
  unfold rationalNumerator
  apply natDegree_sum_le_of_forall_le
  intro j _
  calc
    (C (c j) * ∏ k ∈ univ.erase j, (X - C (v k))).natDegree ≤
        (∏ k ∈ univ.erase j, (X - C (v k))).natDegree := natDegree_C_mul_le _ _
    _ = Fintype.card ι - 1 := by simp

lemma rationalNumerator_eval_node {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v c : ι → ℚ) (_hv : Function.Injective v) (j : ι) :
    (rationalNumerator v c).eval (v j) =
      c j * ∏ k ∈ univ.erase j, (v j - v k) := by
  simp only [rationalNumerator, eval_finsetSum, eval_mul, eval_C, eval_prod,
    eval_sub, eval_X]
  apply Finset.sum_eq_single j
  · intro k _ hkj
    have hjk : j ∈ univ.erase k := by simp [Ne.symm hkj]
    have hz : ∏ l ∈ univ.erase k, (v j - v l) = 0 := by
      apply Finset.prod_eq_zero hjk
      simp
    rw [hz, mul_zero]
  · simp

lemma rationalNumerator_eval_away {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v c : ι → ℚ) (x : ℚ) (hx : ∀ j, x ≠ v j) :
    (rationalNumerator v c).eval x =
      (∏ k, (x - v k)) * ∑ j, c j / (x - v j) := by
  simp only [rationalNumerator, eval_finsetSum, eval_mul, eval_C, eval_prod,
    eval_sub, eval_X, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hprod := Finset.mul_prod_erase univ (fun k => x - v k) (mem_univ j)
  rw [← hprod]
  field_simp [sub_ne_zero.mpr (hx j)]

lemma rationalNumerator_eq_zero_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v c : ι → ℚ) (hv : Function.Injective v) :
    rationalNumerator v c = 0 ↔ c = 0 := by
  constructor
  · intro h
    funext j
    have he := rationalNumerator_eval_node v c hv j
    rw [h, eval_zero] at he
    apply (mul_eq_zero.mp he.symm).resolve_right
    apply Finset.prod_ne_zero_iff.mpr
    intro k hk
    apply sub_ne_zero.mpr
    intro h'
    have := hv h'
    exact (mem_erase.mp hk).1 this.symm
  · intro h
    subst c
    simp [rationalNumerator]

end

end Li2Lean.B3.VFormalADivisor

open Finset Polynomial

namespace Li2Lean.B3.VFormalADivisor

noncomputable section

def outsideIdx (n : ℕ) (c : Fin (5 * n)) : ℕ :=
  if c.val < n then n + c.val else 5 * n + c.val

lemma outsideIdx_bounds (n : ℕ) (c : Fin (5 * n)) :
    n ≤ outsideIdx n c ∧ outsideIdx n c < 10 * n ∧
      ¬ (2 * n ≤ outsideIdx n c ∧ outsideIdx n c < 6 * n) := by
  unfold outsideIdx
  split_ifs <;> omega

lemma outsideIdx_injective (n : ℕ) : Function.Injective (outsideIdx n) := by
  intro i j hij
  apply Fin.ext
  unfold outsideIdx at hij
  split_ifs at hij <;> omega

lemma outsideIdx_surjective_on (n k : ℕ) (hk : n ≤ k ∧ k < 10 * n)
    (hI : ¬ (2 * n ≤ k ∧ k < 6 * n)) :
    ∃ c : Fin (5 * n), outsideIdx n c = k := by
  by_cases hlow : k < 2 * n
  · refine ⟨⟨k - n, by omega⟩, ?_⟩
    simp only [outsideIdx, Fin.val_mk, if_pos (show k - n < n by omega)]
    omega
  · refine ⟨⟨k - 5 * n, by omega⟩, ?_⟩
    simp only [outsideIdx, Fin.val_mk, if_neg (show ¬ k - 5 * n < n by omega)]
    omega

def leadingMinor (n : ℕ) (a : ℤ) : Matrix (Fin (5 * n)) (Fin (5 * n)) ℚ :=
  fun r c => if r.val < 4 * n then
    V.vCEntry a (2 * n + r.val) (outsideIdx n c)
  else V.vVEntry (outsideIdx n c) (1 + (r.val - 4 * n))

lemma leadingMinor_kernel (q n : ℕ) (hq : 2 ≤ q) (hn : 0 < n)
    (c : Fin (5 * n) → ℚ)
    (hc : (leadingMinor n (-(q : ℤ))).mulVec c = 0) : c = 0 := by
  let v : Fin (5 * n) → ℚ := fun j => (outsideIdx n j : ℚ)
  let U : ℚ[X] := rationalNumerator v c
  let W : ℚ[X] := rationalNumerator v
    (fun j => c j * (-(q : ℚ)) ^ outsideIdx n j)
  have hv : Function.Injective v := by
    intro i j hij
    apply outsideIdx_injective n
    dsimp [v] at hij
    exact_mod_cast hij
  have hC (k : ℕ) (hk : 2 * n ≤ k ∧ k < 6 * n) :
      ∑ j, V.vCEntry (-(q : ℤ)) k (outsideIdx n j) * c j = 0 := by
    let r : Fin (5 * n) := ⟨k - 2 * n, by omega⟩
    have hr : r.val < 4 * n := by dsimp [r]; omega
    have hi : 2 * n + r.val = k := by dsimp [r]; omega
    have he := congrFun hc r
    simpa [Matrix.mulVec, dotProduct, leadingMinor, hr, hi] using he
  have hV (l : Fin n) :
      ∑ j, V.vVEntry (outsideIdx n j) (l.val + 1) * c j = 0 := by
    let r : Fin (5 * n) := ⟨4 * n + l.val, by omega⟩
    have hr : ¬ r.val < 4 * n := by dsimp [r]; omega
    have hl : 1 + (r.val - 4 * n) = l.val + 1 := by dsimp [r]; omega
    have he := congrFun hc r
    simpa [Matrix.mulVec, dotProduct, leadingMinor, hr, hl] using he
  have hroot (l : Fin n) : U.eval (-((l.val + 1 : ℕ) : ℚ)) = 0 := by
    have hx : ∀ j, -((l.val + 1 : ℕ) : ℚ) ≠ v j := by
      intro j
      dsimp [v]
      have hv0 : (0 : ℚ) ≤ (outsideIdx n j : ℚ) := by positivity
      have hl0 : (0 : ℚ) < ((l.val + 1 : ℕ) : ℚ) := by positivity
      linarith
    rw [rationalNumerator_eval_away v c _ hx]
    have hsum : (∑ j, c j / (-((l.val + 1 : ℕ) : ℚ) - v j)) =
        -(∑ j, V.vVEntry (outsideIdx n j) (l.val + 1) * c j) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j _
      simp only [v, V.vVEntry, Nat.cast_add, Nat.cast_one, div_eq_mul_inv]
      rw [show -((l.val : ℚ) + 1) - (outsideIdx n j : ℚ) =
        -((outsideIdx n j : ℚ) + ((l.val : ℚ) + 1)) by ring, inv_neg]
      ring
    rw [hsum, hV, neg_zero, mul_zero]
  have hvalues (k : Fin (9 * n)) :
      W.eval ((n + k.val : ℕ) : ℚ) =
        (-(q : ℚ)) ^ (n + k.val) * U.eval ((n + k.val : ℕ) : ℚ) := by
    let t : ℕ := n + k.val
    have ht : n ≤ t ∧ t < 10 * n := by dsimp [t]; omega
    change W.eval (t : ℚ) = (-(q : ℚ)) ^ t * U.eval (t : ℚ)
    by_cases hI : 2 * n ≤ t ∧ t < 6 * n
    · have hne (j : Fin (5 * n)) : t ≠ outsideIdx n j := by
        intro h
        exact (outsideIdx_bounds n j).2.2 (h ▸ hI)
      have hxc : ∀ j, (t : ℚ) ≠ v j := by
        intro j
        dsimp [v]
        exact_mod_cast hne j
      rw [rationalNumerator_eval_away v _ _ hxc,
        rationalNumerator_eval_away v _ _ hxc]
      have hsum : (∑ j, c j * (-(q : ℚ)) ^ outsideIdx n j / ((t : ℚ) - v j)) =
          (-(q : ℚ)) ^ t * ∑ j, c j / ((t : ℚ) - v j) := by
        apply sub_eq_zero.mp
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        convert hC t hI using 1
        apply Finset.sum_congr rfl
        intro j _
        simp only [V.vCEntry, hne j, if_false, Int.cast_neg, Int.cast_natCast, v]
        have hden : (t : ℚ) - (outsideIdx n j : ℚ) ≠ 0 := sub_ne_zero.mpr (hxc j)
        have hden' : (outsideIdx n j : ℚ) - (t : ℚ) ≠ 0 := sub_ne_zero.mpr (hxc j).symm
        field_simp
        ring
      rw [hsum]
      ring
    · obtain ⟨j, hj⟩ := outsideIdx_surjective_on n t ht hI
      change W.eval (t : ℚ) = (-(q : ℚ)) ^ t * U.eval (t : ℚ)
      rw [← hj]
      change (rationalNumerator v _).eval (v j) =
        (-(q : ℚ)) ^ outsideIdx n j * (rationalNumerator v c).eval (v j)
      rw [rationalNumerator_eval_node v _ hv, rationalNumerator_eval_node v c hv]
      ring
  have hU0 : U = 0 := numerator_pair_zero n hn (q : ℚ) (by exact_mod_cast (by omega : 0 < q))
    U W (by have := rationalNumerator_natDegree v c; dsimp [U]; simp only [Fintype.card_fin] at this; omega)
    (by have := rationalNumerator_natDegree v (fun j => c j * (-(q : ℚ)) ^ outsideIdx n j)
        dsimp [W]; simp only [Fintype.card_fin] at this; omega)
    hroot hvalues
  exact (rationalNumerator_eq_zero_iff v c hv).mp hU0

lemma leadingMinor_det_ne_zero (q n : ℕ) (hq : 2 ≤ q) :
    (leadingMinor n (-(q : ℤ))).det ≠ 0 := by
  by_cases hn : n = 0
  · subst n
    simp [Matrix.det_isEmpty]
  have hinj : Function.Injective (leadingMinor n (-(q : ℤ))).mulVec := by
    intro c d hcd
    apply sub_eq_zero.mp
    apply leadingMinor_kernel q n hq (by omega)
    rw [Matrix.mulVec_sub, hcd, sub_self]
  exact ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.mulVec_injective_iff_isUnit.mp hinj)).ne_zero

end

end Li2Lean.B3.VFormalADivisor

open scoped BigOperators

namespace Li2Lean.B3.VFormalADivisor

lemma det_ne_zero_of_column_cover {α β γ : Type*}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (M : Matrix α α ℚ) (N : Matrix β β ℚ)
    (inside : γ → α) (outside : β → α) (rows : β → α)
    (hout : Function.Injective outside)
    (hcover : ∀ a, (∃ b, outside b = a) ∨ ∃ g, inside g = a)
    (hinside : ∀ x : α → ℚ, M.mulVec x = 0 → ∀ g, x (inside g) = 0)
    (hminor : ∀ b c, M (rows b) (outside c) = N b c)
    (hN : N.det ≠ 0) : M.det ≠ 0 := by
  classical
  have hker (x : α → ℚ) (hx : M.mulVec x = 0) : x = 0 := by
    have hi := hinside x hx
    have houtker : N.mulVec (fun c => x (outside c)) = 0 := by
      funext b
      change (∑ c : β, N b c * x (outside c)) = 0
      let f : α → ℚ := fun a => M (rows b) a * x a
      have hs : (∑ c : β, f (outside c)) = ∑ a : α, f a := by
        calc
          (∑ c : β, f (outside c)) =
              ∑ a ∈ Finset.univ.image outside, f a := by
            symm
            apply Finset.sum_image
            intro c _ d _ hcd
            exact hout hcd
          _ = ∑ a : α, f a := by
            apply Finset.sum_subset (Finset.subset_univ _)
            intro a _ ha
            rcases hcover a with ⟨b, hb⟩ | ⟨g, hg⟩
            · exact False.elim (ha (Finset.mem_image.mpr ⟨b, Finset.mem_univ _, hb⟩))
            · simp only [f, ← hg, hi, mul_zero]
      calc
        (∑ c : β, N b c * x (outside c)) = ∑ c : β, f (outside c) := by
          apply Finset.sum_congr rfl
          intro c _
          simp only [f, hminor]
        _ = ∑ a : α, f a := hs
        _ = 0 := congrFun hx (rows b)
    have ho := Matrix.eq_zero_of_mulVec_eq_zero hN houtker
    funext a
    rcases hcover a with ⟨b, hb⟩ | ⟨g, hg⟩
    · simpa only [← hb, Pi.zero_apply] using congrFun ho b
    · simpa only [← hg, Pi.zero_apply] using hi g
  have hu : IsUnit M := Matrix.mulVec_injective_iff_isUnit.mp (by
    intro x y hxy
    apply sub_eq_zero.mp
    apply hker
    rw [Matrix.mulVec_sub, hxy, sub_self])
  exact ((Matrix.isUnit_iff_isUnit_det M).mp hu).ne_zero

end Li2Lean.B3.VFormalADivisor

open scoped BigOperators

namespace Li2Lean.B3.VFormalADivisor

lemma coeff_prod_sum_budget {R ι : Type*} [CommRing R]
    (s : Finset ι) (f : ι → Polynomial R) (d : ι → ℕ)
    (h : ∀ i ∈ s, (f i).natDegree ≤ d i) :
    (∏ i ∈ s, f i).coeff (∑ i ∈ s, d i) =
      ∏ i ∈ s, (f i).coeff (d i) := by
  classical
  revert h
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    intro h
    have hs : ∀ i ∈ s, (f i).natDegree ≤ d i :=
      fun i hi => h i (Finset.mem_insert_of_mem hi)
    have hprod : (∏ i ∈ s, f i).natDegree ≤ ∑ i ∈ s, d i :=
      (Polynomial.natDegree_prod_le _ _).trans (Finset.sum_le_sum hs)
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      Finset.prod_insert ha,
      Polynomial.coeff_mul_add_eq_of_natDegree_le
        (h a (Finset.mem_insert_self a s)) hprod,
      ih hs]

lemma coeff_det_sum_row_budget {R ι : Type*} [CommRing R] [Fintype ι]
    [DecidableEq ι] (M : Matrix ι ι (Polynomial R)) (d : ι → ℕ)
    (h : ∀ i j, (M i j).natDegree ≤ d i) :
    M.det.coeff (∑ i, d i) = Matrix.det (fun i j => (M i j).coeff (d i)) := by
  classical
  rw [Matrix.det_apply M, Polynomial.finsetSum_coeff]
  rw [Matrix.det_apply (fun i j => (M i j).coeff (d i))]
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [Polynomial.coeff_smul]
  congr 1
  rw [← Equiv.sum_comp σ d]
  exact coeff_prod_sum_budget Finset.univ (fun i => M (σ i) i)
    (fun i => d (σ i)) (fun i _ => h (σ i) i)

noncomputable section

def leadingMatrix (n : ℕ) (a : ℤ) :
    Matrix (Fin (V.vMatrixSize n)) (Fin (V.vMatrixSize n)) ℚ :=
  fun r c =>
    if r.val < V.vM n then
      V.vCEntry a (V.vIIndexNat n r.val) (V.vJIndex n c)
    else if r.val < 2 * V.vM n then
      -V.vAEntry a (2 * n + (r.val - V.vM n)) (V.vJIndex n c)
    else V.vVEntry (V.vJIndex n c) (1 + (r.val - 2 * V.vM n))

def leadingRowBudget (n : ℕ) (r : Fin (V.vMatrixSize n)) : ℕ :=
  if V.vM n ≤ r.val ∧ r.val < 2 * V.vM n then 1 else 0

lemma leadingRowBudget_sum (n : ℕ) :
    (∑ r : Fin (V.vMatrixSize n), leadingRowBudget n r) = V.vM n := by
  classical
  unfold leadingRowBudget
  change (∑ r : Fin (V.vMatrixSize n),
    (fun k : ℕ => if V.vM n ≤ k ∧ k < 2 * V.vM n then 1 else 0) r.val) = V.vM n
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ =>
    if V.vM n ≤ k ∧ k < 2 * V.vM n then (1 : ℕ) else 0) (V.vMatrixSize n)]
  simp only [Finset.sum_boole]
  have hs : (Finset.range (V.vMatrixSize n)).filter
      (fun r => V.vM n ≤ r ∧ r < 2 * V.vM n) =
      Finset.Ico (V.vM n) (2 * V.vM n) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    dsimp [V.vMatrixSize]
    omega
  simp only [hs, Nat.card_Ico, Nat.cast_id]
  omega

lemma leadingRowBudget_natDegree (n : ℕ) (a : ℤ)
    (r c : Fin (V.vMatrixSize n)) :
    (V.vSourceMatrix n a r c).natDegree ≤ leadingRowBudget n r := by
  by_cases h₁ : r.val < V.vM n
  · have hn : ¬ V.vM n ≤ r.val := by omega
    simp [V.vSourceMatrix, leadingRowBudget, h₁, hn]
  · by_cases h₂ : r.val < 2 * V.vM n
    · have hn : V.vM n ≤ r.val := by omega
      simp only [V.vSourceMatrix, h₁, h₂, ↓reduceIte,
        leadingRowBudget, hn, and_self, ↓reduceIte]
      apply (Polynomial.natDegree_sub_le _ _).trans
      apply max_le
      · simp
      · exact (Polynomial.natDegree_mul_le).trans (by simp)
    · simp [V.vSourceMatrix, leadingRowBudget, h₁, h₂]

lemma leadingRowBudget_coeff (n : ℕ) (a : ℤ)
    (r c : Fin (V.vMatrixSize n)) :
    (V.vSourceMatrix n a r c).coeff (leadingRowBudget n r) = leadingMatrix n a r c := by
  by_cases h₁ : r.val < V.vM n
  · have hn : ¬ V.vM n ≤ r.val := by omega
    simp [V.vSourceMatrix, leadingRowBudget, leadingMatrix, h₁, hn]
  · by_cases h₂ : r.val < 2 * V.vM n
    · have hn : V.vM n ≤ r.val := by omega
      simp [V.vSourceMatrix, leadingRowBudget, leadingMatrix, h₁, h₂, hn]
    · simp [V.vSourceMatrix, leadingRowBudget, leadingMatrix, h₁, h₂]

lemma vPolynomial_coeff_vM (n : ℕ) (a : ℤ) :
    (V.vPolynomial n a).coeff (V.vM n) = Matrix.det (leadingMatrix n a) := by
  have h := coeff_det_sum_row_budget (V.vSourceMatrix n a)
    (leadingRowBudget n) (leadingRowBudget_natDegree n a)
  rw [leadingRowBudget_sum] at h
  simpa only [V.vPolynomial, leadingRowBudget_coeff] using h

end

end Li2Lean.B3.VFormalADivisor

open Finset

namespace Li2Lean.B3.VFormalADivisor

noncomputable section

def insideCol (n : ℕ) (i : Fin (4 * n)) : Fin (V.vMatrixSize n) :=
  ⟨n + i.val, by rw [V.vMatrixSize_eq]; omega⟩

def outsideCol (n : ℕ) (i : Fin (5 * n)) : Fin (V.vMatrixSize n) :=
  ⟨outsideIdx n i - n, by
    rw [V.vMatrixSize_eq]
    have := outsideIdx_bounds n i
    omega⟩

def minorRow (n : ℕ) (r : Fin (5 * n)) : Fin (V.vMatrixSize n) :=
  ⟨if r.val < 4 * n then r.val else 4 * n + r.val, by
    rw [V.vMatrixSize_eq]
    split_ifs <;> omega⟩

lemma outsideCol_j (n : ℕ) (c : Fin (5 * n)) :
    V.vJIndex n (outsideCol n c) = outsideIdx n c := by
  change n + (outsideIdx n c - n) = outsideIdx n c
  exact Nat.add_sub_of_le (outsideIdx_bounds n c).1

lemma outsideCol_injective (n : ℕ) : Function.Injective (outsideCol n) := by
  intro i j hij
  apply outsideIdx_injective n
  have h := congrArg (V.vJIndex n) hij
  simpa only [outsideCol_j] using h

lemma column_cover (n : ℕ) (c : Fin (V.vMatrixSize n)) :
    (∃ b, outsideCol n b = c) ∨ ∃ g, insideCol n g = c := by
  have hc : c.val < 9 * n := by simpa only [V.vMatrixSize_eq] using c.isLt
  by_cases hI : n ≤ c.val ∧ c.val < 5 * n
  · right
    refine ⟨⟨c.val - n, by omega⟩, ?_⟩
    apply Fin.ext
    simp only [insideCol, Fin.val_mk]
    omega
  · left
    obtain ⟨b, hb⟩ := outsideIdx_surjective_on n (n + c.val)
      ⟨by omega, by omega⟩ (by omega)
    refine ⟨b, ?_⟩
    apply Fin.ext
    simp only [outsideCol, Fin.val_mk, hb]
    omega

lemma leadingMatrix_minor (n : ℕ) (a : ℤ) (r c : Fin (5 * n)) :
    leadingMatrix n a (minorRow n r) (outsideCol n c) = leadingMinor n a r c := by
  unfold leadingMatrix
  rw [outsideCol_j]
  by_cases hr : r.val < 4 * n
  · simp [minorRow, hr, V.vM, V.vIIndexNat, leadingMinor]
  · have htop : ¬ (minorRow n r).val < V.vM n := by
      simp only [minorRow, hr, ite_false, Fin.val_mk, V.vM]
      omega
    have hmid : ¬ (minorRow n r).val < 2 * V.vM n := by
      simp only [minorRow, hr, ite_false, Fin.val_mk, V.vM]
      omega
    simp only [htop, hmid, ite_false, leadingMinor, hr]
    congr 1
    simp only [minorRow, hr, ite_false, Fin.val_mk, V.vM]
    omega

lemma leadingMatrix_kernel_inside (q n : ℕ) (hq : 2 ≤ q)
    (x : Fin (V.vMatrixSize n) → ℚ)
    (hx : (leadingMatrix n (-(q : ℤ))).mulVec x = 0)
    (i : Fin (4 * n)) : x (insideCol n i) = 0 := by
  let r : Fin (V.vMatrixSize n) := ⟨4 * n + i.val, by
    rw [V.vMatrixSize_eq]
    omega⟩
  have htop : ¬ r.val < V.vM n := by dsimp [r, V.vM]; omega
  have hmid : r.val < 2 * V.vM n := by dsimp [r, V.vM]; omega
  have hi : 2 * n + (r.val - V.vM n) = 2 * n + i.val := by
    dsimp [r, V.vM]
    omega
  have he := congrFun hx r
  change (∑ c, leadingMatrix n (-(q : ℤ)) r c * x c) = 0 at he
  simp only [leadingMatrix, htop, hmid, ite_false, ite_true, hi] at he
  have hs : (∑ c : Fin (V.vMatrixSize n),
      -V.vAEntry (-(q : ℤ)) (2 * n + i.val) (V.vJIndex n c) * x c) =
      -((-(q : ℚ)) ^ (2 * n + i.val)) * x (insideCol n i) := by
    rw [Finset.sum_eq_single (insideCol n i)]
    · have hj : V.vJIndex n (insideCol n i) = 2 * n + i.val := by
        simp only [V.vJIndex, insideCol, Fin.val_mk]
        omega
      simp [V.vAEntry, hj]
    · intro c _ hci
      have hne : 2 * n + i.val ≠ V.vJIndex n c := by
        intro h
        apply hci
        apply Fin.ext
        simp only [V.vJIndex] at h
        simp only [insideCol, Fin.val_mk]
        omega
      simp [V.vAEntry, hne]
    · simp
  rw [hs] at he
  apply (mul_eq_zero.mp he).resolve_left
  apply neg_ne_zero.mpr
  apply pow_ne_zero
  have : (0 : ℚ) < q := by exact_mod_cast (by omega : 0 < q)
  exact neg_ne_zero.mpr this.ne'

lemma leadingMatrix_det_ne_zero (q n : ℕ) (hq : 2 ≤ q) :
    (leadingMatrix n (-(q : ℤ))).det ≠ 0 := by
  exact det_ne_zero_of_column_cover
    (leadingMatrix n (-(q : ℤ))) (leadingMinor n (-(q : ℤ)))
    (insideCol n) (outsideCol n) (minorRow n)
    (outsideCol_injective n) (column_cover n)
    (leadingMatrix_kernel_inside q n hq) (leadingMatrix_minor n (-(q : ℤ)))
    (leadingMinor_det_ne_zero q n hq)

lemma vPolynomial_neg_ne_zero (q n : ℕ) (hq : 2 ≤ q) :
    V.vPolynomial n (-(q : ℤ)) ≠ 0 := by
  intro h
  apply leadingMatrix_det_ne_zero q n hq
  rw [← vPolynomial_coeff_vM, h]
  simp

lemma actualVDeterminant_four_mul_ne_zero (q n : ℕ) (hq : 2 ≤ q) :
    V.actualVDeterminant q (4 * n) ≠ 0 := by
  rw [V.actualVDeterminant_four_mul]
  exact vPolynomial_neg_ne_zero q n hq

end

end Li2Lean.B3.VFormalADivisor

namespace Li2Lean.B3

/-- The formal a-divisor branch of the v13 actual prime-valuation bound.
The credit includes the full multiplicity of p in q. -/
theorem actualV_coeff_val_of_dvd_q {q : ℕ} (hq : SignedVBaseRange q)
    (n p : ℕ) (hp : p.Prime) (hpq : p ∣ q) :
    V.actualGaussValuation p (V.actualVDeterminant q (4 * n)) ≥
      -(((12 * n * Nat.log p (V.vN n) + n * Nat.log p (V.vU n) : ℕ) : ℤ) -
          (((53 * n ^ 2 + 2) / 3 - 4 * n : ℕ) : ℤ) * (padicValNat p q : ℤ)) := by
  have hsupport := Polynomial.support_nonempty.mpr
    (VFormalADivisor.actualVDeterminant_four_mul_ne_zero q n hq.1)
  unfold V.actualGaussValuation
  rw [dif_pos hsupport]
  apply Finset.le_inf'
  intro i hi
  exact (actualV_coefficient_val_of_dvd_q q n p i hq hp hpq).resolve_left
    (Polynomial.mem_support_iff.mp hi)

end Li2Lean.B3

#print axioms Li2Lean.B3.VFormalADivisor.formal_a_divisor
#print axioms Li2Lean.B3.VFormalADivisor.actualVDeterminant_four_mul_ne_zero
#print axioms Li2Lean.B3.actualV_coeff_val_of_dvd_q
