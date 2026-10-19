/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.LayerInterfaces
import Li2Lean.P0.PositiveTower.LocalRing
import Li2Lean.P0.PositiveTower.LocalResidue

/-! Prime/base-parametric entry goodness, porting NonvanishingTowerProducer.
This proves local integrality, not the Lucas congruence or tower certificate. -/
namespace Li2Lean.P0.PositiveTower.EntryGoodness
noncomputable section
open Li2Lean Li2Lean.P0.PositiveTower
variable (p : ℕ) [hp : Fact (Nat.Prime p)]
def qRatP (k : ℕ) : ℚ := ((p ^ k : ℕ) : ℚ)
variable {p}
lemma natRat_good (n : ℕ) : (n : ℚ) ∈ GoodP p := by
  change Nat.Coprime ((n : ℚ).den) p
  simp
lemma intRat_good (z : ℤ) : (z : ℚ) ∈ GoodP p := by
  change Nat.Coprime ((z : ℚ).den) p
  simp
lemma qRat_good (k : ℕ) : qRatP p k ∈ GoodP p := natRat_good _
lemma q_div_good (k d : ℕ) (hd : 0 < d) (hb : d < p * p^k) :
    qRatP p k / (d : ℚ) ∈ GoodP p := powP_div_den_coprime k d hd hb
lemma q_sq_div_prod_good (k d₁ d₂ : ℕ) (h₁ : 0 < d₁) (h₂ : 0 < d₂)
    (hb₁ : d₁ < p*p^k) (hb₂ : d₂ < p*p^k) :
    (qRatP p k)^2 / ((d₁*d₂ : ℕ) : ℚ) ∈ GoodP p :=
  powP_sq_div_prod_den_coprime k d₁ d₂ h₁ h₂ hb₁ hb₂
lemma q_sq_div_sq_good (k d : ℕ) (hd : 0 < d) (hb : d < p*p^k) :
    (qRatP p k)^2 / (d : ℚ)^2 ∈ GoodP p := by
  rw [show (qRatP p k)^2 / (d : ℚ)^2 =
      (qRatP p k / (d : ℚ)) * (qRatP p k / (d : ℚ)) by field_simp]
  exact (GoodP p).mul_mem (q_div_good k d hd hb) (q_div_good k d hd hb)
lemma q_sq_div_good (k d : ℕ) (hd : 0 < d) (hb : d < p*p^k) :
    (qRatP p k)^2 / (d : ℚ) ∈ GoodP p := by
  rw [show (qRatP p k)^2 / (d : ℚ) =
      qRatP p k * (qRatP p k / (d : ℚ)) by field_simp]
  exact (GoodP p).mul_mem (qRat_good k) (q_div_good k d hd hb)

lemma q_div_diff_good (k i j : ℕ) (hij : i ≠ j)
    (hbound : max i j < p * p ^ k) :
    qRatP p k / ((j : ℚ) - (i : ℚ)) ∈ (GoodP p) := by
  by_cases hji : j < i
  · have hd : 0 < i - j := Nat.sub_pos_of_lt hji
    have hbd : i - j < p * p ^ k := lt_of_le_of_lt (Nat.sub_le _ _)
      (lt_of_le_of_lt (Nat.le_max_left _ _) hbound)
    have hcast : ((i - j : ℕ) : ℚ) = (i : ℚ) - (j : ℚ) := by
      exact_mod_cast Nat.cast_sub hji.le
    rw [show ((j : ℚ) - (i : ℚ)) = -((i - j : ℕ) : ℚ) by rw [hcast]; ring]
    rw [div_neg]
    exact (GoodP p).neg_mem (q_div_good k (i-j) hd hbd)
  · have hij' : i < j := lt_of_le_of_ne (Nat.le_of_not_gt hji) hij
    have hd : 0 < j - i := Nat.sub_pos_of_lt hij'
    have hbd : j - i < p * p ^ k := lt_of_le_of_lt (Nat.sub_le _ _)
      (lt_of_le_of_lt (Nat.le_max_right _ _) hbound)
    have hcast : ((j - i : ℕ) : ℚ) = (j : ℚ) - (i : ℚ) := by
      exact_mod_cast Nat.cast_sub hij'.le
    rw [← hcast]
    exact q_div_good k (j-i) hd hbd

variable {a : ℤ}

lemma p0U_good_general (g i : ℕ) : p0UQ (a : ℚ) g i ∈ GoodP p := by
  unfold p0UQ
  exact (GoodP p).mul_mem ((GoodP p).pow_mem (intRat_good a) i) (natRat_good _)

lemma p0Q_good_general (hunit : Nat.Coprime (a - 1).natAbs p) (s : ℕ) :
    p0Q (a : ℚ) s ∈ GoodP p := by
  have hi : ((a - 1 : ℤ) : ℚ)⁻¹ ∈ GoodP p := by
    change Nat.Coprime (((((a - 1 : ℤ) : ℚ))⁻¹).den) p
    rw [Rat.inv_intCast_den]
    split_ifs
    · simp
    · exact hunit
  change ((a : ℚ) * ((a : ℚ) - 1)⁻¹)^s - 1 ∈ GoodP p
  exact (GoodP p).sub_mem ((GoodP p).pow_mem
    ((GoodP p).mul_mem (intRat_good a) (by simpa only [Int.cast_sub, Int.cast_one] using hi)) s)
    (GoodP p).one_mem

variable (hunit : Nat.Coprime (a - 1).natAbs p)

include hunit in
lemma q_mul_p0T_good (k g i : ℕ) (hi : i < p * p ^ k)
    (hg : g < p * p ^ k) :
    qRatP p k * p0TQ (a : ℚ) g i ∈ (GoodP p) := by
  unfold p0TQ
  have hsum1 : qRatP p k *
      (∑ r ∈ Finset.range i,
        p0UQ (a : ℚ) g (i - (r + 1)) / (r + 1 : ℚ)) ∈ (GoodP p) := by
    rw [Finset.mul_sum]
    apply (GoodP p).sum_mem
    intro r hr
    have hrlt : r < i := Finset.mem_range.mp hr
    have hd : 0 < r + 1 := by omega
    have hbd : r + 1 < p * p ^ k := by omega
    have hterm : qRatP p k *
        (p0UQ (a : ℚ) g (i - (r + 1)) / (r + 1 : ℚ)) ∈ (GoodP p) := by
      rw [show qRatP p k *
          (p0UQ (a : ℚ) g (i - (r + 1)) / (r + 1 : ℚ)) =
          (qRatP p k / (r + 1 : ℚ)) * p0UQ (a : ℚ) g (i - (r + 1)) by
            field_simp]
      exact (GoodP p).mul_mem (by
        simpa only [Nat.cast_add, Nat.cast_one] using
          (q_div_good k (r+1) hd hbd))
        (p0U_good_general g (i - (r+1)))
    exact hterm
  have hsum2 : qRatP p k *
      ((a : ℚ) ^ i *
        ∑ s ∈ Finset.range g,
          (((-1 : ℚ) ^ s / ((s : ℚ) + 1)) *
            (Nat.choose (i + g) (g - (s + 1)) : ℚ) *
            p0Q (a : ℚ) (s + 1))) ∈ (GoodP p) := by
    have hsum_expand : qRatP p k * ((a : ℚ) ^ i *
        ∑ s ∈ Finset.range g,
          (((-1 : ℚ) ^ s / ((s : ℚ) + 1)) *
            (Nat.choose (i + g) (g - (s + 1)) : ℚ) *
            p0Q (a : ℚ) (s + 1))) =
      ∑ s ∈ Finset.range g,
        (qRatP p k * ((a : ℚ) ^ i) *
          (((-1 : ℚ) ^ s / ((s : ℚ) + 1)) *
            (Nat.choose (i + g) (g - (s + 1)) : ℚ) *
            p0Q (a : ℚ) (s + 1))) := by
      calc
        _ = (qRatP p k * (a : ℚ)^i) *
            (∑ s ∈ Finset.range g,
              (((-1 : ℚ) ^ s / ((s : ℚ) + 1)) *
                (Nat.choose (i + g) (g - (s + 1)) : ℚ) *
                p0Q (a : ℚ) (s + 1))) := by ring
        _ = ∑ s ∈ Finset.range g,
            (qRatP p k * (a : ℚ)^i) *
              (((-1 : ℚ) ^ s / ((s : ℚ) + 1)) *
                (Nat.choose (i + g) (g - (s + 1)) : ℚ) *
                p0Q (a : ℚ) (s + 1)) := by rw [Finset.mul_sum]
        _ = _ := by
          apply Finset.sum_congr rfl
          intro s hs
          ring
    rw [hsum_expand]
    apply (GoodP p).sum_mem
    intro s hs
    have hslt : s < g := Finset.mem_range.mp hs
    have hd : 0 < s + 1 := by omega
    have hbd : s + 1 < p * p ^ k := by omega
    rw [show qRatP p k * (a : ℚ)^i *
          (((-1 : ℚ) ^ s / ((s : ℚ) + 1)) *
            (Nat.choose (i + g) (g - (s + 1)) : ℚ) *
            p0Q (a : ℚ) (s + 1)) =
        (qRatP p k / ((s + 1 : ℕ) : ℚ)) *
          (((-1 : ℚ) ^ s) *
            (a : ℚ)^i *
            (Nat.choose (i + g) (g - (s + 1)) : ℚ) *
            p0Q (a : ℚ) (s + 1)) by
      field_simp
      push_cast
      ring]
    apply (GoodP p).mul_mem (q_div_good k (s+1) hd hbd)
    rw [show ((-1 : ℚ) ^ s) * (a : ℚ)^i *
          (Nat.choose (i + g) (g - (s + 1)) : ℚ) * p0Q (a : ℚ) (s + 1) =
        ((-1 : ℚ) ^ s) * ((a : ℚ)^i *
          ((Nat.choose (i + g) (g - (s + 1)) : ℚ) * p0Q (a : ℚ) (s + 1))) by ring]
    exact (GoodP p).mul_mem (by
      change Nat.Coprime ((-1 : ℚ) ^ s).den p
      norm_num [Rat.den_pow])
      ((GoodP p).mul_mem (((GoodP p).pow_mem (intRat_good a) i))
        ((GoodP p).mul_mem (natRat_good _) (p0Q_good_general hunit _)))
  have hadd :
      qRatP p k * (∑ r ∈ Finset.range i,
        p0UQ (a : ℚ) g (i - (r + 1)) / (r + 1 : ℚ)) +
      qRatP p k * ((a : ℚ) ^ i * ∑ s ∈ Finset.range g,
          (((-1 : ℚ) ^ s / ((s : ℚ) + 1)) *
            (Nat.choose (i + g) (g - (s + 1)) : ℚ) *
            p0Q (a : ℚ) (s + 1))) ∈ (GoodP p) :=
    (GoodP p).add_mem hsum1 hsum2
  convert hadd using 1 <;> ring

include hunit in
lemma q_sq_mul_p0BQQ_good (k g i : ℕ)
    (hi : i < p * p ^ k) (hg : g < p * p ^ k) :
    (qRatP p k)^2 * p0BQQ (a : ℚ) g i ∈ (GoodP p) := by
  unfold p0BQQ
  have hsum1 : (qRatP p k)^2 *
      (∑ r ∈ Finset.range i,
        p0UQ (a : ℚ) g (i - (r + 1)) / (r + 1 : ℚ)^2) ∈ (GoodP p) := by
    rw [Finset.mul_sum]
    apply (GoodP p).sum_mem
    intro r hr
    have hrlt : r < i := Finset.mem_range.mp hr
    have hd : 0 < r + 1 := by omega
    have hbd : r + 1 < p * p ^ k := by omega
    rw [show (qRatP p k)^2 *
          (p0UQ (a : ℚ) g (i - (r + 1)) / (r + 1 : ℚ)^2) =
        ((qRatP p k)^2 / ((r + 1 : ℕ) : ℚ)^2) *
          p0UQ (a : ℚ) g (i - (r + 1)) by
      field_simp
      push_cast
      ring]
    exact (GoodP p).mul_mem
      (by simpa only [Nat.cast_add, Nat.cast_one] using
        q_sq_div_sq_good k (r+1) hd hbd)
      (p0U_good_general g (i - (r+1)))
  have hsum2 : (qRatP p k)^2 *
      ((a : ℚ) ^ i *
        ∑ s ∈ Finset.Icc 2 g,
          (((-1 : ℚ)^s / (s : ℚ)) *
            (Nat.choose (i + g) (g - s) : ℚ) *
            (∑ r ∈ Finset.range (s - 1),
              p0Q (a : ℚ) (r + 1) / (r + 1 : ℚ)))) ∈ (GoodP p) := by
    have hdouble : (qRatP p k)^2 *
        ((a : ℚ) ^ i *
          ∑ s ∈ Finset.Icc 2 g,
            (((-1 : ℚ)^s / (s : ℚ)) *
              (Nat.choose (i + g) (g - s) : ℚ) *
              (∑ r ∈ Finset.range (s - 1),
                p0Q (a : ℚ) (r + 1) / (r + 1 : ℚ)))) =
      ∑ s ∈ Finset.Icc 2 g, ∑ r ∈ Finset.range (s - 1),
        (((qRatP p k)^2 / ((s * (r + 1) : ℕ) : ℚ)) *
          (((-1 : ℚ)^s) * (a : ℚ)^i *
            (Nat.choose (i + g) (g - s) : ℚ) *
            p0Q (a : ℚ) (r + 1))) := by
      calc
        _ = ((qRatP p k)^2 * (a : ℚ)^i) *
              (∑ s ∈ Finset.Icc 2 g,
                (-1 : ℚ)^s / (s : ℚ) *
                  (Nat.choose (i + g) (g - s) : ℚ) *
                  (∑ r ∈ Finset.range (s - 1),
                    p0Q (a : ℚ) (r + 1) / (r + 1 : ℚ))) := by ring
        _ = ∑ s ∈ Finset.Icc 2 g,
              ((qRatP p k)^2 * (a : ℚ)^i) *
                ((-1 : ℚ)^s / (s : ℚ) *
                  (Nat.choose (i + g) (g - s) : ℚ) *
                  (∑ r ∈ Finset.range (s - 1),
                    p0Q (a : ℚ) (r + 1) / (r + 1 : ℚ))) := by
          rw [Finset.mul_sum]
        _ = ∑ s ∈ Finset.Icc 2 g, ∑ r ∈ Finset.range (s - 1),
              ((qRatP p k)^2 * (a : ℚ)^i) *
                ((-1 : ℚ)^s / (s : ℚ) *
                  (Nat.choose (i + g) (g - s) : ℚ) *
                  (p0Q (a : ℚ) (r + 1) / (r + 1 : ℚ))) := by
          apply Finset.sum_congr rfl
          intro s hs
          rw [Finset.mul_sum]
          rw [Finset.mul_sum]
        _ = ∑ s ∈ Finset.Icc 2 g, ∑ r ∈ Finset.range (s - 1),
              ((qRatP p k)^2 / ((s * (r + 1) : ℕ) : ℚ)) *
                ((-1 : ℚ)^s * (a : ℚ)^i *
                  (Nat.choose (i + g) (g - s) : ℚ) *
                  p0Q (a : ℚ) (r + 1)) := by
          apply Finset.sum_congr rfl
          intro s hs
          apply Finset.sum_congr rfl
          intro r hr
          have hspos : 0 < s := by
            have := Finset.mem_Icc.mp hs
            omega
          have hrpos : 0 < r + 1 := by omega
          have hcast : ((s * (r + 1) : ℕ) : ℚ) =
              (s : ℚ) * ((r + 1 : ℕ) : ℚ) := by norm_num
          rw [hcast]
          push_cast
          field_simp
    rw [hdouble]
    apply (GoodP p).sum_mem
    intro s hs
    apply (GoodP p).sum_mem
    intro r hr
    have hslo : 2 ≤ s := Finset.mem_Icc.mp hs |>.1
    have hshi : s ≤ g := Finset.mem_Icc.mp hs |>.2
    have hspos : 0 < s := by omega
    have hrlt : r < s - 1 := Finset.mem_range.mp hr
    have hrpos : 0 < r + 1 := by omega
    have hbs : s < p * p ^ k := lt_of_le_of_lt hshi hg
    have hbr : r + 1 < p * p ^ k := by omega
    have hchoose : (Nat.choose (i + g) (g - s) : ℚ) ∈ (GoodP p) :=
      natRat_good (Nat.choose (i + g) (g - s))
    have hp0 : p0Q (a : ℚ) (r + 1) ∈ (GoodP p) :=
      p0Q_good_general hunit (r + 1)
    have hterm := (GoodP p).mul_mem
      (q_sq_div_prod_good k s (r+1) hspos hrpos hbs hbr)
      ((GoodP p).mul_mem
        (by change Nat.Coprime ((-1 : ℚ)^s).den p; norm_num [Rat.den_pow])
        ((GoodP p).mul_mem (((GoodP p).pow_mem (intRat_good a) i))
          ((GoodP p).mul_mem hchoose hp0)))
    convert hterm using 1 <;> ring
  have hsub :
      (qRatP p k)^2 *
        ((∑ r ∈ Finset.range i,
          p0UQ (a : ℚ) g (i - (r + 1)) / (r + 1 : ℚ)^2) -
        (a : ℚ) ^ i * ∑ s ∈ Finset.Icc 2 g,
          (((-1 : ℚ)^s / (s : ℚ)) *
            (Nat.choose (i + g) (g - s) : ℚ) *
            (∑ r ∈ Finset.range (s - 1),
              p0Q (a : ℚ) (r + 1) / (r + 1 : ℚ)))) ∈ (GoodP p) := by
    rw [mul_sub]
    exact (GoodP p).sub_mem hsum1 hsum2
  exact hsub

lemma q_mul_p0CQ_good (k g i j : ℕ)
    (hbound : max i j + g < p * p ^ k) :
    qRatP p k * p0CQ (a : ℚ) g i j ∈ (GoodP p) := by
  unfold p0CQ
  by_cases hij : i = j
  · subst j
    simp only [if_pos rfl]
    have hdiag :
        qRatP p k * (-p0UQ (a : ℚ) g i *
          ∑ s ∈ Finset.range g, ((i + s + 1 : ℚ)⁻¹)) =
        ∑ s ∈ Finset.range g,
          (-p0UQ (a : ℚ) g i) *
            (qRatP p k / ((i + s + 1 : ℕ) : ℚ)) := by
      calc
        _ = (-p0UQ (a : ℚ) g i) *
              (qRatP p k * ∑ s ∈ Finset.range g,
                ((i + s + 1 : ℚ)⁻¹)) := by ring
        _ = (-p0UQ (a : ℚ) g i) *
              (∑ s ∈ Finset.range g,
                qRatP p k * ((i + s + 1 : ℚ)⁻¹)) := by rw [Finset.mul_sum]
        _ = ∑ s ∈ Finset.range g,
              (-p0UQ (a : ℚ) g i) *
                (qRatP p k / ((i + s + 1 : ℕ) : ℚ)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro s hs
          have hcast : ((i + s + 1 : ℕ) : ℚ) =
              (i : ℚ) + (s : ℚ) + 1 := by push_cast; ring
          rw [hcast]
          field_simp
    change qRatP p k * (-p0UQ (a : ℚ) g i *
      ∑ s ∈ Finset.range g, ((i + s + 1 : ℚ)⁻¹)) ∈ (GoodP p)
    rw [hdiag]
    apply (GoodP p).sum_mem
    intro s hs
    have hslt : s < g := Finset.mem_range.mp hs
    have hdpos : 0 < i + s + 1 := by omega
    have hdbound : i + s + 1 < p * p ^ k := by
      have : i ≤ max i i + g := by omega
      omega
    exact (GoodP p).mul_mem ((GoodP p).neg_mem (p0U_good_general g i))
      (q_div_good k (i + s + 1) hdpos hdbound)
  · simp only [if_neg hij]
    have hdiff : max i j < p * p ^ k := by omega
    rw [show qRatP p k *
        ((p0UQ (a : ℚ) g i - p0UQ (a : ℚ) g j) /
          ((j : ℚ) - (i : ℚ))) =
        (qRatP p k / ((j : ℚ) - (i : ℚ))) *
          (p0UQ (a : ℚ) g i - p0UQ (a : ℚ) g j) by field_simp]
    exact (GoodP p).mul_mem (q_div_diff_good k i j hij hdiff)
      ((GoodP p).sub_mem (p0U_good_general g i) (p0U_good_general g j))

lemma q_mul_rat_good (k : ℕ) (r : ℚ)
    (hbound : r.den < p ^ k) : qRatP p k * r ∈ GoodP p :=
  powP_mul_rat_den_coprime k r hbound

lemma q_sq_mul_rat_good (k : ℕ) (r : ℚ)
    (hbound : r.den < p ^ k) : (qRatP p k)^2 * r ∈ GoodP p :=
  powP_sq_mul_rat_den_coprime k r hbound

include hunit in
lemma q_sq_mul_p0BQ_good (k g i j : ℕ)
    (hg : g < p * p ^ k)
    (hi : i < p * p ^ k) (hj : j < p * p ^ k) :
    (qRatP p k)^2 * p0BQ (a : ℚ) g i j ∈ (GoodP p) := by
  unfold p0BQ
  by_cases hij : i = j
  · subst j
    simp only [if_pos rfl]
    exact q_sq_mul_p0BQQ_good hunit k g i hi hg
  · simp only [if_neg hij]
    have hdiff : max i j < p * p ^ k := max_lt_iff.mpr ⟨hi, hj⟩
    rw [show (qRatP p k)^2 *
        ((p0TQ (a : ℚ) g i - p0TQ (a : ℚ) g j) /
          ((j : ℚ) - (i : ℚ))) =
        (qRatP p k / ((j : ℚ) - (i : ℚ))) *
          (qRatP p k * p0TQ (a : ℚ) g i - qRatP p k * p0TQ (a : ℚ) g j) by
            field_simp]
    exact (GoodP p).mul_mem (q_div_diff_good k i j hij hdiff)
      ((GoodP p).sub_mem (q_mul_p0T_good hunit k g i hi hg)
        (q_mul_p0T_good hunit k g j hj hg))

lemma p0AQ_good (g i j : ℕ) : p0AQ (a : ℚ) g i j ∈ (GoodP p) := by
  unfold p0AQ
  split
  · exact p0U_good_general g i
  · exact (GoodP p).zero_mem


end
end Li2Lean.P0.PositiveTower.EntryGoodness
