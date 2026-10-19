/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.PiSquaredIrrational
import Li2Lean.Statement

namespace Li2Lean

theorem li2InvValue_one_eq_pi_sq_div_six :
    li2InvValue (1 : ℤ) = Real.pi ^ 2 / 6 := by
  have hshift : HasSum (fun n : ℕ => (1 : ℝ) / (n + 1 : ℝ) ^ 2)
      (Real.pi ^ 2 / 6) := by
    simpa using (hasSum_nat_add_iff' 1).2 (hasSum_zeta_two)
  rw [li2InvValue]
  simpa [one_div] using hshift.tsum_eq

theorem li2_inv_irrational_one : Irrational (li2InvValue (1 : ℤ)) := by
  rw [li2InvValue_one_eq_pi_sq_div_six]
  exact irrational_pi_sq.div_natCast (by norm_num)

noncomputable section

private def negOneTerm (k : ℕ) : ℝ :=
  (1 : ℝ) / (k + 1 : ℝ) ^ 2

private def negOneAlternating (k : ℕ) : ℝ :=
  (-1 : ℝ) ^ k * negOneTerm k

private lemma negOneTerm_hasSum :
    HasSum negOneTerm (Real.pi ^ 2 / 6) := by
  unfold negOneTerm
  simpa using (hasSum_nat_add_iff' 1).2 (hasSum_zeta_two)

private lemma negOneTerm_summable : Summable negOneTerm :=
  negOneTerm_hasSum.summable

private lemma negOneEven_injective :
    Function.Injective (fun k : ℕ => 2 * k) := by
  intro a b h
  exact Nat.mul_left_cancel (by norm_num) h

private lemma negOneOdd_injective :
    Function.Injective (fun k : ℕ => 2 * k + 1) := by
  intro a b h
  exact Nat.mul_left_cancel (by norm_num) (Nat.add_right_cancel h)

private lemma negOneOdd_sum :
    (∑' k : ℕ, negOneTerm (2 * k + 1)) =
      (1 / 4 : ℝ) * (Real.pi ^ 2 / 6) := by
  have hpoint : (fun k : ℕ => negOneTerm (2 * k + 1)) =
      (fun k : ℕ => (1 / 4 : ℝ) * negOneTerm k) := by
    funext k
    simp [negOneTerm]
    field_simp
    ring
  rw [hpoint, tsum_mul_left, negOneTerm_hasSum.tsum_eq]

private lemma negOneAlternating_sum :
    (∑' k : ℕ, negOneAlternating k) = Real.pi ^ 2 / 12 := by
  have heven : Summable (fun k : ℕ => negOneTerm (2 * k)) :=
    negOneTerm_summable.comp_injective negOneEven_injective
  have hodd : Summable (fun k : ℕ => negOneTerm (2 * k + 1)) :=
    negOneTerm_summable.comp_injective negOneOdd_injective
  have halt : Summable negOneAlternating := by
    exact negOneTerm_summable.alternating
  have heven_alt : Summable (fun k : ℕ => negOneAlternating (2 * k)) :=
    halt.comp_injective negOneEven_injective
  have hodd_alt : Summable (fun k : ℕ => negOneAlternating (2 * k + 1)) :=
    halt.comp_injective negOneOdd_injective
  have htotal :
      (∑' k : ℕ, negOneTerm (2 * k)) +
          (∑' k : ℕ, negOneTerm (2 * k + 1)) = Real.pi ^ 2 / 6 := by
    rw [tsum_even_add_odd heven hodd, negOneTerm_hasSum.tsum_eq]
  have hodd_sum := negOneOdd_sum
  calc
    (∑' k : ℕ, negOneAlternating k) =
        (∑' k : ℕ, negOneAlternating (2 * k)) +
          (∑' k : ℕ, negOneAlternating (2 * k + 1)) :=
      (tsum_even_add_odd heven_alt hodd_alt).symm
    _ = (∑' k : ℕ, negOneTerm (2 * k)) -
          (∑' k : ℕ, negOneTerm (2 * k + 1)) := by
      congr 1
      · apply tsum_congr
        intro k
        simp [negOneAlternating, negOneTerm, pow_mul]
      · rw [show (fun k : ℕ => negOneAlternating (2 * k + 1)) =
            (fun k : ℕ => -negOneTerm (2 * k + 1)) by
              funext k
              simp [negOneAlternating, negOneTerm, pow_mul, pow_add]]
        rw [tsum_neg]
    _ = Real.pi ^ 2 / 12 := by
      linarith [htotal, hodd_sum]

theorem li2_inv_value_neg_one_eq_neg_pi_sq_div_twelve :
    li2InvValue (-1 : ℤ) = -(Real.pi ^ 2 / 12) := by
  rw [li2InvValue]
  have hterm :
      (fun k : ℕ => ((-1 : ℤ) : ℝ)⁻¹ ^ (k + 1) /
        ((k : ℝ) + 1) ^ 2) =
      (fun k : ℕ => -negOneAlternating k) := by
    funext k
    simp [negOneAlternating, negOneTerm, pow_add]
    ring
  rw [hterm, tsum_neg, negOneAlternating_sum]

theorem li2_inv_irrational_neg_one : Irrational (li2InvValue (-1 : ℤ)) := by
  rw [li2_inv_value_neg_one_eq_neg_pi_sq_div_twelve]
  exact (irrational_pi_sq.div_natCast (by norm_num : (12 : ℕ) ≠ 0)).neg

end

end Li2Lean
