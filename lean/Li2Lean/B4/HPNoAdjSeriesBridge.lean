/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B4.ResidueCertificateAllN_M0c
import Li2Lean.B4.HPNoAdjacentActual

open Filter Topology Polynomial
open scoped BigOperators

namespace Li2Lean.B4.TailAnalytic

noncomputable section

open Li2Lean.B4.Residues

/- v13 hp-tail.tex:31-45; finite-support and shifted-series scaffolding. -/

lemma hasSum_finset_nat (s : Finset ℕ) (f : ℕ → ℝ) :
    HasSum (fun k => if k ∈ s then f k else 0) (∑ k ∈ s, f k) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℝ)) 0)
  | @insert a s ha ih =>
      have hsingle : HasSum (fun k : ℕ => if k = a then f a else 0) (f a) :=
        hasSum_ite_eq a (f a)
      have hadd := hsingle.add ih
      convert hadd using 1
      · funext k
        by_cases hka : k = a
        · subst k
          simp [ha]
        · by_cases hks : k ∈ s <;> simp [hka, hks, ha]
      · simp [ha]

def hpSeriesTerm (d : ℕ) (z : ℝ) (m : ℕ) : ℝ :=
  z ^ (m + 1) / ((m : ℝ) + 1) ^ d

lemma hpPoly_eval_hasSum (p : ℚ[X]) (q : ℚ) (z : ℝ)
    (hz : (q : ℝ) = z) :
    HasSum (fun k : ℕ => ((p.coeff k : ℚ) : ℝ) * z ^ k)
      (((Polynomial.eval q p : ℚ) : ℝ)) := by
  let s : Finset ℕ := Finset.range (p.natDegree + 1)
  have hfinite := hasSum_finset_nat s
    (fun k : ℕ => ((p.coeff k : ℚ) : ℝ) * z ^ k)
  have hfun : (fun k : ℕ => if k ∈ s then
      ((p.coeff k : ℚ) : ℝ) * z ^ k else 0) =
      (fun k : ℕ => ((p.coeff k : ℚ) : ℝ) * z ^ k) := by
    funext k
    by_cases hk : k ∈ s
    · simp [hk]
    · have hdeg : p.natDegree < k := by
        simpa [s, Finset.mem_range] using hk
      have hc : p.coeff k = 0 := coeff_eq_zero_of_natDegree_lt hdeg
      simp [hk, hc]
  rw [hfun] at hfinite
  convert hfinite using 1
  rw [eval_eq_sum_range]
  simp only [s]
  push_cast
  simp [hz]

lemma hp_eval_inv_hasSum (p : ℚ[X]) (a : ℤ) :
    HasSum (fun k : ℕ => ((p.coeff k : ℚ) : ℝ) * (a : ℝ)⁻¹ ^ k)
      (((Polynomial.eval ((a : ℚ)⁻¹) p : ℚ) : ℝ)) := by
  apply hpPoly_eval_hasSum p ((a : ℚ)⁻¹) ((a : ℝ)⁻¹)
  norm_num

lemma hpBRealAt_eq_sum (a : ℤ) (n : ℕ) :
    hpBRealAt a n =
      ∑ j ∈ Finset.range (n + 1), (hpResidueV n j : ℝ) * (a : ℝ)⁻¹ ^ j := by
  unfold hpBRealAt hpBpoly
  rw [Polynomial.eval_finset_sum]
  push_cast
  simp [Polynomial.eval_monomial]

lemma hpCRealAt_eq_sum (a : ℤ) (n : ℕ) :
    hpCRealAt a n =
      ∑ j ∈ Finset.range (n + 1), (hpResidueU n j : ℝ) * (a : ℝ)⁻¹ ^ j := by
  unfold hpCRealAt hpCpoly
  rw [Polynomial.eval_finset_sum]
  push_cast
  simp [Polynomial.eval_monomial]

lemma li2InvValue_eq_hpSeries (a : ℤ) :
    li2InvValue a = ∑' m : ℕ, hpSeriesTerm 2 ((a : ℝ)⁻¹) m := by
  rfl

lemma hpSeriesTerm_log_hasSum {z : ℝ} (hz : |z| < 1) :
    HasSum (hpSeriesTerm 1 z) (-Real.log (1-z)) := by
  convert (Real.hasSum_pow_div_log_of_abs_lt_one hz) using 1
  funext n
  simp [hpSeriesTerm, div_eq_mul_inv]

lemma hpSeriesTerm_li2_summable {z : ℝ} (hz : |z| < 1) :
    Summable (hpSeriesTerm 2 z) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun m => by positivity)
  · intro m
    change ‖z ^ (m + 1) / ((m : ℝ) + 1) ^ 2‖ ≤ |z| ^ (m + 1)
    simp only [Real.norm_eq_abs, abs_div, abs_pow]
    have hden : (1 : ℝ) ≤ ((m : ℝ) + 1) ^ 2 := by
      have hm : (0 : ℝ) ≤ m := by exact_mod_cast Nat.zero_le m
      nlinarith
    have hden' : (1 : ℝ) ≤ |(m : ℝ) + 1| ^ 2 := by
      rw [abs_of_nonneg (by positivity)]
      exact hden
    exact div_le_self (by positivity) hden'
  · have hzabs : |(|z| : ℝ)| < 1 := by
      simpa [abs_of_nonneg (abs_nonneg z)] using hz
    have hg : Summable (fun m : ℕ => |z| ^ m) :=
      summable_geometric_of_abs_lt_one (r := |z|) hzabs
    have hgm := hg.mul_right (|z| : ℝ)
    simpa [hpSeriesTerm, abs_pow, abs_of_nonneg (by positivity : (0 : ℝ) ≤ |z|),
      pow_succ, mul_comm, mul_left_comm, mul_assoc] using hgm

lemma hpSeriesTerm_li2_hasSum {z : ℝ} (hz : |z| < 1) :
    HasSum (hpSeriesTerm 2 z) (∑' m : ℕ, hpSeriesTerm 2 z m) := by
  exact (hpSeriesTerm_li2_summable hz).hasSum

lemma hpShiftedSeries_hasSum {d : ℕ} {z S : ℝ} (j : ℕ) (c : ℝ)
    (hbase : HasSum (hpSeriesTerm d z) S) :
    HasSum (fun k : ℕ =>
      if j < k then c * z ^ k / ((k - j : ℕ) : ℝ) ^ d else 0)
      (c * z ^ j * S) := by
  let f : ℕ → ℝ := fun k =>
    if j < k then c * z ^ k / ((k - j : ℕ) : ℝ) ^ d else 0
  have hhead : ∑ i ∈ Finset.range (j + 1), f i = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp only [Finset.mem_range] at hi
    simp [f, Nat.not_lt_of_ge (Nat.le_of_lt_succ hi)]
  have hshift : HasSum (fun m : ℕ => f (m + (j + 1)))
      (c * z ^ j * S) := by
    have hmul := (hbase.mul_left (c * z ^ j))
    convert hmul using 1
    funext m
    simp only [f]
    have hj : j < m + (j + 1) := by omega
    rw [if_pos hj]
    have hsub : m + (j + 1) - j = m + 1 := by omega
    rw [hsub]
    rw [show z ^ (m + (j + 1)) = z ^ j * z ^ (m + 1) by
      rw [show m + (j + 1) = j + (m + 1) by omega, pow_add]]
    simp only [hpSeriesTerm, Nat.cast_add, Nat.cast_one]
    ring
  have hleft : HasSum (fun m : ℕ => f (m + (j + 1)))
      ((c * z ^ j * S) - ∑ i ∈ Finset.range (j + 1), f i) := by
    simpa [hhead] using hshift
  have hfull := (hasSum_nat_add_iff' (f := f) (j + 1)).mp hleft
  simpa [f] using hfull

lemma hpBSeries_hasSum (a : ℤ) (n : ℕ) (hz0 : |(a : ℝ)⁻¹| < 1) :
    HasSum
      (fun k : ℕ =>
        ∑ j ∈ Finset.range (n + 1),
          if j < k then
            (hpResidueV n j : ℝ) * (a : ℝ)⁻¹ ^ k /
              ((k - j : ℕ) : ℝ) ^ 1
          else 0)
      (hpBRealAt a n * (-Real.log (1 - (a : ℝ)⁻¹))) := by
  let z : ℝ := (a : ℝ)⁻¹
  have hz : |z| < 1 := by simpa [z] using hz0
  have hbase : HasSum (hpSeriesTerm 1 z) (-Real.log (1 - z)) :=
    hpSeriesTerm_log_hasSum hz
  have heach : ∀ j ∈ Finset.range (n + 1),
      HasSum
        (fun k : ℕ =>
          if j < k then
            (hpResidueV n j : ℝ) * z ^ k /
              ((k - j : ℕ) : ℝ) ^ 1
          else 0)
        ((hpResidueV n j : ℝ) * z ^ j * (-Real.log (1 - z))) := by
    intro j hj
    exact hpShiftedSeries_hasSum j (hpResidueV n j : ℝ) hbase
  have hsum := hasSum_sum (s := Finset.range (n + 1)) heach
  have hright :
      (∑ j ∈ Finset.range (n + 1),
        (hpResidueV n j : ℝ) * z ^ j * (-Real.log (1 - z))) =
        hpBRealAt a n * (-Real.log (1 - z)) := by
    rw [hpBRealAt_eq_sum]
    dsimp [z]
    rw [Finset.sum_mul]
  rw [hright] at hsum
  simpa [z] using hsum

lemma hpCSeries_hasSum (a : ℤ) (n : ℕ) (hz0 : |(a : ℝ)⁻¹| < 1) :
    HasSum
      (fun k : ℕ =>
        ∑ j ∈ Finset.range (n + 1),
          if j < k then
            (hpResidueU n j : ℝ) * (a : ℝ)⁻¹ ^ k /
              ((k - j : ℕ) : ℝ) ^ 2
          else 0)
      (hpCRealAt a n * (∑' m : ℕ, hpSeriesTerm 2 ((a : ℝ)⁻¹) m)) := by
  let z : ℝ := (a : ℝ)⁻¹
  have hz : |z| < 1 := by simpa [z] using hz0
  have hbase : HasSum (hpSeriesTerm 2 z)
      (∑' m : ℕ, hpSeriesTerm 2 z m) := hpSeriesTerm_li2_hasSum hz
  have heach : ∀ j ∈ Finset.range (n + 1),
      HasSum
        (fun k : ℕ =>
          if j < k then
            (hpResidueU n j : ℝ) * z ^ k /
              ((k - j : ℕ) : ℝ) ^ 2
          else 0)
        ((hpResidueU n j : ℝ) * z ^ j *
          (∑' m : ℕ, hpSeriesTerm 2 z m)) := by
    intro j hj
    exact hpShiftedSeries_hasSum j (hpResidueU n j : ℝ) hbase
  have hsum := hasSum_sum (s := Finset.range (n + 1)) heach
  have hright :
      (∑ j ∈ Finset.range (n + 1),
        (hpResidueU n j : ℝ) * z ^ j *
          (∑' m : ℕ, hpSeriesTerm 2 z m)) =
        hpCRealAt a n * (∑' m : ℕ, hpSeriesTerm 2 z m) := by
    rw [hpCRealAt_eq_sum]
    dsimp [z]
    rw [Finset.sum_mul]
  rw [hright] at hsum
  simpa [z] using hsum

lemma hpResidueConvolution_real_eq_sum (a : ℤ) (n k : ℕ) :
    ((hpResidueConvolution n k : ℚ) : ℝ) * (a : ℝ)⁻¹ ^ k =
      ∑ j ∈ Finset.range (n + 1),
        if j < k then
          (hpResidueV n j : ℝ) * (a : ℝ)⁻¹ ^ k /
              ((k - j : ℕ) : ℝ) ^ 1 +
            (hpResidueU n j : ℝ) * (a : ℝ)⁻¹ ^ k /
              ((k - j : ℕ) : ℝ) ^ 2
        else 0 := by
  unfold hpResidueConvolution
  push_cast
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases h : j < k
  · simp only [if_pos h]
    push_cast
    rw [Nat.cast_sub h.le]
    have hsub : (k : ℝ) - (j : ℝ) ≠ 0 := by
      exact sub_ne_zero.mpr (by exact_mod_cast (Nat.ne_of_gt h))
    field_simp [hsub]
  · simp only [if_neg h]
    ring

lemma hpCombinedCoeff_eq_threeCoeff (a : ℤ) (n k : ℕ) :
    (((hpApoly n).coeff k : ℚ) : ℝ) * (a : ℝ)⁻¹ ^ k +
        (∑ j ∈ Finset.range (n + 1),
          if j < k then
            (hpResidueV n j : ℝ) * (a : ℝ)⁻¹ ^ k /
                ((k - j : ℕ) : ℝ) ^ 1
          else 0) +
        (∑ j ∈ Finset.range (n + 1),
          if j < k then
            (hpResidueU n j : ℝ) * (a : ℝ)⁻¹ ^ k /
                ((k - j : ℕ) : ℝ) ^ 2
          else 0) =
      ((hpThreeFormCoeff n k : ℚ) : ℝ) * (a : ℝ)⁻¹ ^ k := by
  rw [hpThreeFormCoeff]
  rw [Rat.cast_add]
  calc
    (((hpApoly n).coeff k : ℚ) : ℝ) * (a : ℝ)⁻¹ ^ k +
          (∑ j ∈ Finset.range (n + 1),
            if j < k then
              (hpResidueV n j : ℝ) * (a : ℝ)⁻¹ ^ k /
                  ((k - j : ℕ) : ℝ) ^ 1
            else 0) +
          (∑ j ∈ Finset.range (n + 1),
            if j < k then
              (hpResidueU n j : ℝ) * (a : ℝ)⁻¹ ^ k /
                  ((k - j : ℕ) : ℝ) ^ 2
            else 0) =
        (((hpApoly n).coeff k : ℚ) : ℝ) * (a : ℝ)⁻¹ ^ k +
          ((∑ j ∈ Finset.range (n + 1),
            if j < k then
              (hpResidueV n j : ℝ) * (a : ℝ)⁻¹ ^ k /
                  ((k - j : ℕ) : ℝ) ^ 1
            else 0) +
            (∑ j ∈ Finset.range (n + 1),
              if j < k then
                (hpResidueU n j : ℝ) * (a : ℝ)⁻¹ ^ k /
                    ((k - j : ℕ) : ℝ) ^ 2
              else 0)) := by ring
    _ = (((hpApoly n).coeff k : ℚ) : ℝ) * (a : ℝ)⁻¹ ^ k +
          ((hpResidueConvolution n k : ℚ) : ℝ) * (a : ℝ)⁻¹ ^ k := by
      rw [hpResidueConvolution_real_eq_sum]
      congr 1
      symm
      calc
        (∑ j ∈ Finset.range (n + 1),
            if j < k then
              (hpResidueV n j : ℝ) * (a : ℝ)⁻¹ ^ k /
                  ((k - j : ℕ) : ℝ) ^ 1 +
                (hpResidueU n j : ℝ) * (a : ℝ)⁻¹ ^ k /
                  ((k - j : ℕ) : ℝ) ^ 2
            else 0) =
          (∑ j ∈ Finset.range (n + 1),
            ((if j < k then
                (hpResidueV n j : ℝ) * (a : ℝ)⁻¹ ^ k /
                    ((k - j : ℕ) : ℝ) ^ 1
              else 0) +
              (if j < k then
                (hpResidueU n j : ℝ) * (a : ℝ)⁻¹ ^ k /
                    ((k - j : ℕ) : ℝ) ^ 2
              else 0))) := by
            apply Finset.sum_congr rfl
            intro j hj
            by_cases h : j < k <;> simp [h]
        _ = (∑ j ∈ Finset.range (n + 1),
              if j < k then
                (hpResidueV n j : ℝ) * (a : ℝ)⁻¹ ^ k /
                    ((k - j : ℕ) : ℝ) ^ 1
              else 0) +
              ∑ j ∈ Finset.range (n + 1),
                if j < k then
                  (hpResidueU n j : ℝ) * (a : ℝ)⁻¹ ^ k /
                      ((k - j : ℕ) : ℝ) ^ 2
                else 0 := Finset.sum_add_distrib
    _ = ((((hpApoly n).coeff k : ℚ) : ℝ) +
          ((hpResidueConvolution n k : ℚ) : ℝ)) * (a : ℝ)⁻¹ ^ k := by ring

lemma hpThreeFormCoeff_hasSum (a : ℤ) (n : ℕ) (hz : |(a : ℝ)⁻¹| < 1) :
    HasSum
      (fun k : ℕ => ((hpThreeFormCoeff n k : ℚ) : ℝ) * (a : ℝ)⁻¹ ^ k)
      (hpTailCombinationAt a n) := by
  have hA0 := hp_eval_inv_hasSum (hpApoly n) a
  have hA : HasSum
      (fun k : ℕ => (((hpApoly n).coeff k : ℚ) : ℝ) * (a : ℝ)⁻¹ ^ k)
      (hpARealAt a n) := by
    simpa [hpARealAt] using hA0
  have hB := hpBSeries_hasSum a n hz
  have hC0 := hpCSeries_hasSum a n hz
  have hC : HasSum
      (fun k : ℕ =>
        ∑ j ∈ Finset.range (n + 1),
          if j < k then
            (hpResidueU n j : ℝ) * (a : ℝ)⁻¹ ^ k /
              ((k - j : ℕ) : ℝ) ^ 2
          else 0)
      (hpCRealAt a n * li2InvValue a) := by
    rw [li2InvValue_eq_hpSeries]
    exact hC0
  have htotal := hA.add (hB.add hC)
  convert htotal using 1
  · funext k
    simpa [add_assoc] using (hpCombinedCoeff_eq_threeCoeff a n k).symm
  · unfold hpTailCombinationAt
    ring

lemma hpThreeFormCoeff_zero_at_zero (n : ℕ) :
    hpThreeFormCoeff n 0 = 0 := by
  simp [hpThreeFormCoeff, hpApoly_coeff, hpResidueConvolution]

lemma hpThreeFormCoeff_prefix_sum_zero (a : ℤ) (n : ℕ)
    (hz : |(a : ℝ)⁻¹| < 1) :
    ∑ k ∈ Finset.range (3 * n + 2),
      ((hpThreeFormCoeff n k : ℚ) : ℝ) * (a : ℝ)⁻¹ ^ k = 0 := by
  apply Finset.sum_eq_zero
  intro k hk
  have hklt : k < 3 * n + 2 := Finset.mem_range.mp hk
  by_cases hk0 : k = 0
  · subst k
    rw [hpThreeFormCoeff_zero_at_zero]
    simp
  · have hk1 : 1 ≤ k := by omega
    by_cases hkn : k ≤ n
    · rw [hpThreeFormCoeff_eq_zero_of_le n k hk1 hkn]
      simp
    · have hhi : k ≤ 3 * n + 1 := by omega
      have hnk : n < k := by omega
      have hmid : hpThreeFormCoeff n k = 0 :=
        hpThreeFormCoeff_eq_zero_of_middle n k hnk hhi
          (Li2Lean.B4.hpartial_for_residueTailAlgebra_all n k (by omega))
      rw [hmid]
      simp

lemma hpTailCombination_eq_hpRR_of_abs_inv_lt_one (a : ℤ) (n : ℕ)
    (hz : |(a : ℝ)⁻¹| < 1) :
    hpTailCombinationAt a n = hpRR n ((a : ℝ)⁻¹) := by
  let z : ℝ := (a : ℝ)⁻¹
  let off : ℕ := 3 * n + 2
  let f : ℕ → ℝ := fun k =>
    ((hpThreeFormCoeff n k : ℚ) : ℝ) * z ^ k
  have hfull : HasSum f (hpTailCombinationAt a n) := by
    simpa [f, z] using hpThreeFormCoeff_hasSum a n hz
  have hprefix : ∑ k ∈ Finset.range off, f k = 0 := by
    simpa [f, off, z] using hpThreeFormCoeff_prefix_sum_zero a n hz
  have hshift : HasSum (fun m : ℕ => f (m + off))
      (hpTailCombinationAt a n - ∑ k ∈ Finset.range off, f k) := by
    exact (hasSum_nat_add_iff' (f := f) off).2 hfull
  have hshift' : HasSum (fun m : ℕ => f (m + off))
      (hpTailCombinationAt a n) := by
    simpa [hprefix] using hshift
  have hphi : HasSum
      (fun m : ℕ =>
        ((hpPhiValue n (m + off) : ℚ) : ℝ) * z ^ (m + off))
      (hpTailCombinationAt a n) := by
    convert hshift' using 1
    · funext m
      dsimp [f]
      have htail := Li2Lean.B4.hpTailCoeff_all n (m + off) (by
        dsimp [off]
        omega)
      rw [htail]
  have hrr := hphi.tsum_eq
  simpa [hpRR, off, z, Nat.add_comm] using hrr.symm

end
end Li2Lean.B4.TailAnalytic
