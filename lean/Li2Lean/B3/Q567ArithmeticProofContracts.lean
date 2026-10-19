/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license.

Construction-facing arithmetic boundaries for q = 5, 6, 7.  These rows are
kept separate by v13 region (exceptional primes, cutoff tail, outer poles,
p-unit residue blocks, and bulk).  They pin the valuation to the actual
signed determinant and do not restate the final integerizer conclusion.
-/

import Li2Lean.B3.Q567ArithmeticContracts

namespace Li2Lean.B3

noncomputable section

open scoped BigOperators

theorem q5_v13_rate_margin :
    vAlpha 5 - vTau 5 = (14649 : ℝ) / 100000 := by
  norm_num [vAlpha, vTau]

theorem q6_v13_rate_margin :
    vAlpha 6 - vTau 6 = (15631 : ℝ) / 100000 := by
  norm_num [vAlpha, vTau]

theorem q7_v13_rate_margin :
    vAlpha 7 - vTau 7 = (16212 : ℝ) / 100000 := by
  norm_num [vAlpha, vTau]

theorem q5_exceptional_credit_is_v13 (n : ℕ) :
    q5FormalCredit n 2 = (4 * n : ℤ) ∧
      q5FormalCredit n 3 = (4 * n : ℤ) ∧
      q5FormalCredit n 5 = (q567FormalDivisorExponent n : ℤ) := by
  exact q5FormalCredit_at_exceptions n

theorem q6_exceptional_credit_is_v13 (n : ℕ) :
    q6FormalCredit n 2 = (q567FormalDivisorExponent n : ℤ) ∧
      q6FormalCredit n 3 = (q567FormalDivisorExponent n : ℤ) ∧
      q6FormalCredit n 7 = (4 * n : ℤ) := by
  exact q6FormalCredit_at_exceptions n

theorem q7_exceptional_credit_is_v13 (n : ℕ) :
    q7FormalCreditV13 n 2 = (3 * (4 * n) : ℤ) ∧
      q7FormalCreditV13 n 7 = (q567FormalDivisorExponent n : ℤ) := by
  exact q7FormalCreditV13_at_exceptions n

structure Q5ValuationRows : Prop where
  exceptional : ∀ n p : ℕ,
    (p = 2 ∨ p = 3 ∨ p = 5) →
      q5ActualGaussValuation n p ≥
        -(q567NaturalExponent n p - q5FormalCredit n p)
  tail : ∀ {n p : ℕ}, 0 < n → Nat.Prime p →
    q567DenominatorCutoff n < p → 0 ≤ q5ActualGaussValuation n p
  outer : ∀ {n p : ℕ}, 0 < n → Nat.Prime p →
    5 * n < p → p ≤ q567DenominatorCutoff n →
      q5ActualGaussValuation n p ≥ -(V.Q5Certificate.q5OuterCost n p)
  residue : ∀ {n p : ℕ}, 0 < n → Nat.Prime p →
    ¬ p ∣ 5 * (5 + 1) →
    max (q567NumeratorCutoff n) (q567DenominatorCutoff n) < p ^ 2 →
      q5ActualGaussValuation n p ≥
        -(V.Q5Certificate.q5ResidueExponent (4 * n) p)
  bulk : ∀ {n p : ℕ}, 0 < n → Nat.Prime p →
    p ≠ 2 → p ≠ 3 → p ≠ 5 →
    p ≤ q567DenominatorCutoff n → ¬ 5 * n < p →
    ¬ max (q567NumeratorCutoff n) (q567DenominatorCutoff n) < p ^ 2 →
      q5ActualGaussValuation n p ≥ -q567NaturalExponent n p

structure Q6ValuationRows : Prop where
  exceptional : ∀ n p : ℕ,
    (p = 2 ∨ p = 3 ∨ p = 7) →
      q6ActualGaussValuation n p ≥
        -(q567NaturalExponent n p - q6FormalCredit n p)
  tail : ∀ {n p : ℕ}, 0 < n → Nat.Prime p →
    q567DenominatorCutoff n < p → 0 ≤ q6ActualGaussValuation n p
  outer : ∀ {n p : ℕ}, 0 < n → Nat.Prime p →
    5 * n < p → p ≤ q567DenominatorCutoff n →
      q6ActualGaussValuation n p ≥ -(V.Q6Arithmetic.outerExponent n p)
  residue : ∀ {n p : ℕ}, 0 < n → Nat.Prime p →
    ¬ p ∣ 6 * (6 + 1) →
    max (q567NumeratorCutoff n) (q567DenominatorCutoff n) < p ^ 2 →
      q6ActualGaussValuation n p ≥ -(V.Q6Arithmetic.residueExponent n p)
  bulk : ∀ {n p : ℕ}, 0 < n → Nat.Prime p →
    p ≠ 2 → p ≠ 3 → p ≠ 7 →
    p ≤ q567DenominatorCutoff n → ¬ 5 * n < p →
    ¬ max (q567NumeratorCutoff n) (q567DenominatorCutoff n) < p ^ 2 →
      q6ActualGaussValuation n p ≥ -q567NaturalExponent n p

structure Q7ValuationRows : Prop where
  exceptional : ∀ n p : ℕ,
    (p = 2 ∨ p = 7) →
      q7ActualGaussValuation n p ≥
        -(q567NaturalExponent n p - q7FormalCreditV13 n p)
  tail : ∀ {n p : ℕ}, 0 < n → Nat.Prime p →
    q567DenominatorCutoff n < p → 0 ≤ q7ActualGaussValuation n p
  outer : ∀ {n p : ℕ}, 0 < n → Nat.Prime p →
    5 * n < p → p ≤ q567DenominatorCutoff n →
      q7ActualGaussValuation n p ≥ -(V.Q7Arithmetic.outerExponent n p)
  residue : ∀ {n p : ℕ}, 0 < n → Nat.Prime p →
    ¬ p ∣ 7 * (7 + 1) →
    max (q567NumeratorCutoff n) (q567DenominatorCutoff n) < p ^ 2 →
      q7ActualGaussValuation n p ≥ -(V.Q7Arithmetic.residueExponent n p)
  bulk : ∀ {n p : ℕ}, 0 < n → Nat.Prime p →
    p ≠ 2 → p ≠ 7 →
    p ≤ q567DenominatorCutoff n → ¬ 5 * n < p →
    ¬ max (q567NumeratorCutoff n) (q567DenominatorCutoff n) < p ^ 2 →
      q7ActualGaussValuation n p ≥ -q567NaturalExponent n p

/-! A pointwise envelope is stronger than the epsilon definition and carries
the exact positive margin needed by the endpoint comparison. -/

structure Q5PrimeSumEnvelope where
  margin : ℝ
  margin_pos : 0 < margin
  start : ℕ
  bound : ∀ {n : ℕ}, start ≤ n → 0 < n →
    (∑ p ∈ Nat.primesLE (q567DenominatorCutoff n),
      (q5TargetExponent n p : ℝ) * Real.log p) /
        (((4 * n : ℕ) : ℝ) ^ 2) ≤ vTau 5 - margin

structure Q6PrimeSumEnvelope where
  margin : ℝ
  margin_pos : 0 < margin
  start : ℕ
  bound : ∀ {n : ℕ}, start ≤ n → 0 < n →
    (∑ p ∈ Nat.primesLE (q567DenominatorCutoff n),
      (q6TargetExponent n p : ℝ) * Real.log p) /
        (((4 * n : ℕ) : ℝ) ^ 2) ≤ vTau 6 - margin

structure Q7PrimeSumEnvelope where
  margin : ℝ
  margin_pos : 0 < margin
  start : ℕ
  bound : ∀ {n : ℕ}, start ≤ n → 0 < n →
    (∑ p ∈ Nat.primesLE (q567DenominatorCutoff n),
      (q7TargetExponent n p : ℝ) * Real.log p) /
        (((4 * n : ℕ) : ℝ) ^ 2) ≤ vTau 7 - margin

/-! The envelope is an input about the fixed v13 exponent and cutoff above.
It cannot be instantiated by changing either carrier. Once its positive
margin is supplied by the arithmetic proof, the epsilon-form rate used by the
integerizer follows by a single real inequality. -/

theorem q5_prime_sum_rate_of_envelope (h : Q5PrimeSumEnvelope) :
    Q5PrimeSumRateInput (vTau 5) := by
  intro ε hε
  refine ⟨max h.start 1, ?_⟩
  intro n hn hnpos
  have hstart : h.start ≤ n := le_trans (Nat.le_max_left _ _) hn
  calc
    (∑ p ∈ Nat.primesLE (q567DenominatorCutoff n),
        (q5TargetExponent n p : ℝ) * Real.log p) /
        (((4 * n : ℕ) : ℝ) ^ 2)
        ≤ vTau 5 - h.margin := h.bound hstart hnpos
    _ ≤ vTau 5 + ε := by linarith [h.margin_pos]

theorem q6_prime_sum_rate_of_envelope (h : Q6PrimeSumEnvelope) :
    Q6PrimeSumRateInput (vTau 6) := by
  intro ε hε
  refine ⟨max h.start 1, ?_⟩
  intro n hn hnpos
  have hstart : h.start ≤ n := le_trans (Nat.le_max_left _ _) hn
  calc
    (∑ p ∈ Nat.primesLE (q567DenominatorCutoff n),
        (q6TargetExponent n p : ℝ) * Real.log p) /
        (((4 * n : ℕ) : ℝ) ^ 2)
        ≤ vTau 6 - h.margin := h.bound hstart hnpos
    _ ≤ vTau 6 + ε := by linarith [h.margin_pos]

theorem q7_prime_sum_rate_of_envelope (h : Q7PrimeSumEnvelope) :
    Q7PrimeSumRateInput (vTau 7) := by
  intro ε hε
  refine ⟨max h.start 1, ?_⟩
  intro n hn hnpos
  have hstart : h.start ≤ n := le_trans (Nat.le_max_left _ _) hn
  calc
    (∑ p ∈ Nat.primesLE (q567DenominatorCutoff n),
        (q7TargetExponent n p : ℝ) * Real.log p) /
        (((4 * n : ℕ) : ℝ) ^ 2)
        ≤ vTau 7 - h.margin := h.bound hstart hnpos
    _ ≤ vTau 7 + ε := by linarith [h.margin_pos]

end
end Li2Lean.B3

#print axioms Li2Lean.B3.q5_v13_rate_margin
#print axioms Li2Lean.B3.q6_v13_rate_margin
#print axioms Li2Lean.B3.q7_v13_rate_margin
/-
Append this complete section to Li2Lean/B3/Q567ArithmeticProofContracts.lean.
All auxiliary lemmas below are proved from the signed V source entries and Mathlib.
-/

/-! The zero-safe valuation algebra and elementary denominator estimates,
reproved from the supplied `P0/IntegerizationOddPrimeLarge.lean` in a local
namespace, with no dependency on the P0 determinant construction. -/
namespace Li2Lean.B3.Q5ResidueProof

open scoped BigOperators

noncomputable section

set_option linter.style.haveILetI false

theorem denominator_le_one (p d : ℕ) (hp : p.Prime)
    (hd : 0 < d) (hlarge : d < p ^ 2) : padicValNat p d ≤ 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hnot : ¬ p ^ 2 ∣ d := Nat.not_dvd_of_pos_of_lt hd hlarge
  have hlt : ¬ 2 ≤ padicValNat p d := by
    intro h
    exact hnot ((padicValNat_dvd_iff_le (Nat.ne_of_gt hd)).2 h)
  omega

/-- Zero-safe lower valuation bound. This treats a zero coefficient as
having arbitrarily high valuation, unlike `padicValRat`'s default at zero. -/
def ValAtLeast (p : ℕ) (k : ℤ) (q : ℚ) : Prop :=
  q = 0 ∨ k ≤ padicValRat p q

namespace ValAtLeast

variable {p : ℕ} {k l : ℤ} {q r : ℚ}

@[simp] theorem zero (p : ℕ) (k : ℤ) : ValAtLeast p k 0 := Or.inl rfl

theorem mono (h : ValAtLeast p k q) (hl : l ≤ k) :
    ValAtLeast p l q := h.imp id (hl.trans ·)

theorem neg (h : ValAtLeast p k q) : ValAtLeast p k (-q) := by
  rcases h with h | h
  · simp [h]
  · exact Or.inr (by simpa using h)

theorem add [Fact p.Prime] (hq : ValAtLeast p k q)
    (hr : ValAtLeast p k r) : ValAtLeast p k (q + r) := by
  rcases hq with rfl | hq
  · simpa using hr
  rcases hr with rfl | hr
  · simpa [ValAtLeast] using (Or.inr hq : ValAtLeast p k q)
  by_cases hqr : q + r = 0
  · exact Or.inl hqr
  · exact Or.inr ((le_min hq hr).trans (padicValRat.min_le_padicValRat_add hqr))

theorem sub [Fact p.Prime] (hq : ValAtLeast p k q)
    (hr : ValAtLeast p k r) : ValAtLeast p k (q - r) := by
  simpa [sub_eq_add_neg] using hq.add hr.neg

theorem mul [Fact p.Prime] (hq : ValAtLeast p k q)
    (hr : ValAtLeast p l r) : ValAtLeast p (k + l) (q * r) := by
  by_cases hq0 : q = 0
  · simp [hq0]
  by_cases hr0 : r = 0
  · simp [hr0]
  apply Or.inr
  rw [padicValRat.mul hq0 hr0]
  exact add_le_add (hq.resolve_left hq0) (hr.resolve_left hr0)

theorem div [Fact p.Prime] (hq : ValAtLeast p k q) (r : ℚ) :
    ValAtLeast p (k - padicValRat p r) (q / r) := by
  by_cases hq0 : q = 0
  · simp [hq0]
  by_cases hr0 : r = 0
  · simp [hr0]
  apply Or.inr
  rw [padicValRat.div hq0 hr0]
  exact sub_le_sub_right (hq.resolve_left hq0) _

theorem natCast (p n : ℕ) : ValAtLeast p 0 (n : ℚ) :=
  Or.inr (zero_le_padicValRat_of_nat n)

theorem intCast (p : ℕ) (z : ℤ) : ValAtLeast p 0 (z : ℚ) := by
  exact Or.inr (by rw [padicValRat.of_int]; exact Int.natCast_nonneg _)

theorem sum [Fact p.Prime] {α : Type*} (s : Finset α) (f : α → ℚ)
    (h : ∀ x ∈ s, ValAtLeast p k (f x)) :
    ValAtLeast p k (∑ x ∈ s, f x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hx ih =>
      rw [Finset.sum_insert hx]
      exact (h x (Finset.mem_insert_self x s)).add
        (ih (fun y hy => h y (Finset.mem_insert_of_mem hy)))

end ValAtLeast

theorem difference_val_le (p i j : ℕ) (hp : p.Prime)
    (hi : i < p ^ 2) (hj : j < p ^ 2) (hne : i ≠ j) :
    padicValRat p ((j : ℚ) - (i : ℚ)) ≤
      (if i % p = j % p then 1 else 0 : ℤ) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hforward : ∀ a b : ℕ, a < b → b < p ^ 2 →
      padicValRat p ((b : ℚ) - (a : ℚ)) ≤
        (if a % p = b % p then 1 else 0 : ℤ) := by
    intro a b hab hb
    rw [← Nat.cast_sub (by omega : a ≤ b), padicValRat.of_nat]
    by_cases hmod : a % p = b % p
    · rw [ite_eq_left hmod]
      exact_mod_cast denominator_le_one p (b - a) hp
        (by omega) (by omega)
    · have hnot : ¬ p ∣ b - a := by
        intro hdiv
        have hEq : b = (b - a) + a := by omega
        apply hmod
        rw [hEq, Nat.add_mod, Nat.mod_eq_zero_of_dvd hdiv, zero_add,
          Nat.mod_mod]
      rw [ite_eq_right hmod, padicValNat.eq_zero_of_not_dvd hnot]
      simp
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact hforward i j hlt hj
  · have heq : (j : ℚ) - (i : ℚ) = -((i : ℚ) - (j : ℚ)) := by ring
    rw [heq, padicValRat.neg]
    simpa [eq_comm] using hforward j i hlt hi


end
end Li2Lean.B3.Q5ResidueProof

namespace Li2Lean.B3.Q5ResidueProof

open scoped BigOperators

noncomputable section

theorem int_pow_val (p : ℕ) (a : ℤ) (k : ℕ) :
    ValAtLeast p 0 ((a : ℚ) ^ k) := by
  simpa only [Int.cast_pow] using ValAtLeast.intCast p (a ^ k)

theorem momentT_val (p : ℕ) (a : ℤ) (j : ℕ)
    (hp : p.Prime) (hj : j < p ^ 2) :
    ValAtLeast p (-1) (V.vMomentT a j) := by
  letI : Fact p.Prime := ⟨hp⟩
  unfold V.vMomentT
  apply ValAtLeast.sum
  intro r hr
  have hrj : r < j := Finset.mem_range.mp hr
  have hd : padicValRat p (((r + 1 : ℕ) : ℚ)) ≤ 1 := by
    rw [padicValRat.of_nat]
    exact_mod_cast denominator_le_one p (r + 1) hp
      (by omega) (by omega)
  have hv := (int_pow_val p a (j - (r + 1))).div (((r + 1 : ℕ) : ℚ))
  simpa only [div_eq_mul_inv] using hv.mono (by omega : (-1 : ℤ) ≤ 0 -
    padicValRat p (((r + 1 : ℕ) : ℚ)))

theorem momentB_val (p : ℕ) (a : ℤ) (j : ℕ)
    (hp : p.Prime) (hj : j < p ^ 2) :
    ValAtLeast p (-2) (V.vMomentB a j) := by
  letI : Fact p.Prime := ⟨hp⟩
  unfold V.vMomentB
  apply ValAtLeast.sum
  intro r hr
  have hrj : r < j := Finset.mem_range.mp hr
  have hd : padicValRat p (((r + 1 : ℕ) : ℚ)) ≤ 1 := by
    rw [padicValRat.of_nat]
    exact_mod_cast denominator_le_one p (r + 1) hp
      (by omega) (by omega)
  have hd2 : padicValRat p ((((r + 1 : ℕ) : ℚ)) ^ 2) ≤ 2 := by
    rw [padicValRat.pow]
    norm_num at hd ⊢
    omega
  have hv := (int_pow_val p a (j - (r + 1))).div ((((r + 1 : ℕ) : ℚ)) ^ 2)
  simpa only [div_eq_mul_inv] using hv.mono (by omega : (-2 : ℤ) ≤ 0 -
    padicValRat p ((((r + 1 : ℕ) : ℚ)) ^ 2))

theorem momentT_small (p : ℕ) (a : ℤ) (j : ℕ)
    (hp : p.Prime) (hj : j < p) :
    ValAtLeast p 0 (V.vMomentT a j) := by
  letI : Fact p.Prime := ⟨hp⟩
  unfold V.vMomentT
  apply ValAtLeast.sum
  intro r hr
  have hrj : r < j := Finset.mem_range.mp hr
  have hnot : ¬ p ∣ r + 1 := Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  have hd : padicValRat p (((r + 1 : ℕ) : ℚ)) = 0 := by
    rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hnot]
    rfl
  have hv := (int_pow_val p a (j - (r + 1))).div (((r + 1 : ℕ) : ℚ))
  simpa only [hd, sub_zero, div_eq_mul_inv] using hv

theorem momentB_small (p : ℕ) (a : ℤ) (j : ℕ)
    (hp : p.Prime) (hj : j < p) :
    ValAtLeast p 0 (V.vMomentB a j) := by
  letI : Fact p.Prime := ⟨hp⟩
  unfold V.vMomentB
  apply ValAtLeast.sum
  intro r hr
  have hrj : r < j := Finset.mem_range.mp hr
  have hnot : ¬ p ∣ r + 1 := Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  have hd : padicValRat p ((((r + 1 : ℕ) : ℚ)) ^ 2) = 0 := by
    rw [padicValRat.pow, padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hnot]
    simp
  have hv := (int_pow_val p a (j - (r + 1))).div ((((r + 1 : ℕ) : ℚ)) ^ 2)
  simpa only [hd, sub_zero, div_eq_mul_inv] using hv

/-- An additional denominator cost is assigned only to a repeated residue,
except for the diagonal below p, which is already p-integral. -/
def entryExtra (p i j : ℕ) : ℤ :=
  if i % p = j % p ∧ (i ≠ j ∨ p ≤ i) then 1 else 0

theorem entryExtra_nonneg (p i j : ℕ) : 0 ≤ entryExtra p i j := by
  unfold entryExtra
  split <;> omega

theorem entryExtra_le_one (p i j : ℕ) : entryExtra p i j ≤ 1 := by
  unfold entryExtra
  split <;> omega

theorem entryExtra_diag_small {p i : ℕ} (hi : i < p) :
    entryExtra p i i = 0 := by
  simp [entryExtra, Nat.not_le.mpr hi]

theorem C_val (p : ℕ) (a : ℤ) (i j : ℕ)
    (hp : p.Prime) (hi : i < p ^ 2) (hj : j < p ^ 2) :
    ValAtLeast p (-entryExtra p i j) (V.vCEntry a i j) := by
  letI : Fact p.Prime := ⟨hp⟩
  by_cases hij : i = j
  · simp [V.vCEntry, hij]
  rw [V.vCEntry, ite_eq_right hij]
  have hv := ((int_pow_val p a i).sub (int_pow_val p a j)).div
    ((j : ℚ) - (i : ℚ))
  have hd := difference_val_le p i j hp hi hj hij
  apply hv.mono
  by_cases hmod : i % p = j % p <;>
    simp [entryExtra, hij, hmod] at hd ⊢ <;> omega

theorem B_val (p : ℕ) (a : ℤ) (i j : ℕ)
    (hp : p.Prime) (hi : i < p ^ 2) (hj : j < p ^ 2) :
    ValAtLeast p (-1 - entryExtra p i j) (V.vBEntry a i j) := by
  letI : Fact p.Prime := ⟨hp⟩
  by_cases hij : i = j
  · subst j
    by_cases hip : i < p
    · rw [entryExtra_diag_small hip]
      simpa [V.vBEntry] using (momentB_small p a i hp hip).mono (by norm_num : (-1 : ℤ) ≤ 0)
    · have hpi : p ≤ i := Nat.le_of_not_gt hip
      simpa [V.vBEntry, entryExtra, hpi] using momentB_val p a i hp hi
  rw [V.vBEntry, ite_eq_right hij]
  have hv := ((momentT_val p a i hp hi).sub (momentT_val p a j hp hj)).div
    ((j : ℚ) - (i : ℚ))
  have hd := difference_val_le p i j hp hi hj hij
  apply hv.mono
  by_cases hmod : i % p = j % p <;>
    simp [entryExtra, hij, hmod] at hd ⊢ <;> omega

theorem V_val (p j ell : ℕ) (hp : p.Prime)
    (hpos : 0 < j + ell) (hbound : j + ell < p ^ 2) :
    ValAtLeast p (-(if p ∣ j + ell then 1 else 0 : ℤ)) (V.vVEntry j ell) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hv := (ValAtLeast.natCast p 1).div (((j + ell : ℕ) : ℚ))
  have hd : padicValRat p (((j + ell : ℕ) : ℚ)) ≤
      (if p ∣ j + ell then 1 else 0 : ℤ) := by
    rw [padicValRat.of_nat]
    by_cases heq : p ∣ j + ell
    · rw [ite_eq_left heq]
      exact_mod_cast denominator_le_one p (j + ell) hp hpos hbound
    · rw [ite_eq_right heq, padicValNat.eq_zero_of_not_dvd heq]
      simp
  have hh : -(if p ∣ j + ell then 1 else 0 : ℤ) ≤
      0 - padicValRat p (((j + ell : ℕ) : ℚ)) := by omega
  simpa [V.vVEntry] using hv.mono hh

theorem A_val (p : ℕ) (a : ℤ) (i j : ℕ) :
    ValAtLeast p 0 (V.vAEntry a i j) := by
  by_cases hij : i = j
  · simpa [V.vAEntry, hij] using int_pow_val p a j
  · simp [V.vAEntry, hij]

theorem C_polynomial_val (p : ℕ) (a : ℤ) (i j : ℕ)
    (hp : p.Prime) (hi : i < p ^ 2) (hj : j < p ^ 2) (k : ℕ) :
    ValAtLeast p (-entryExtra p i j)
      ((Polynomial.C (V.vCEntry a i j)).coeff k) := by
  rw [Polynomial.coeff_C]
  by_cases hk : k = 0
  · rw [ite_eq_left hk]
    exact C_val p a i j hp hi hj
  · rw [ite_eq_right hk]
    exact ValAtLeast.zero _ _

theorem B_polynomial_val (p : ℕ) (a : ℤ) (i j : ℕ)
    (hp : p.Prime) (hi : i < p ^ 2) (hj : j < p ^ 2) (k : ℕ) :
    ValAtLeast p (-1 - entryExtra p i j)
      ((Polynomial.C (V.vBEntry a i j) -
        Polynomial.X * Polynomial.C (V.vAEntry a i j)).coeff k) := by
  letI : Fact p.Prime := ⟨hp⟩
  rw [Polynomial.coeff_sub]
  apply ValAtLeast.sub
  · rw [Polynomial.coeff_C]
    by_cases hk : k = 0
    · rw [ite_eq_left hk]
      exact B_val p a i j hp hi hj
    · rw [ite_eq_right hk]
      exact ValAtLeast.zero _ _
  · rw [mul_comm, Polynomial.coeff_C_mul, Polynomial.coeff_X]
    by_cases hk : 1 = k
    · rw [ite_eq_left hk, mul_one]
      apply (A_val p a i j).mono
      have := entryExtra_nonneg p i j
      omega
    · rw [ite_eq_right hk, mul_zero]
      exact ValAtLeast.zero _ _

theorem V_polynomial_val (p j ell : ℕ) (hp : p.Prime)
    (hpos : 0 < j + ell) (hbound : j + ell < p ^ 2) (k : ℕ) :
    ValAtLeast p (-(if p ∣ j + ell then 1 else 0 : ℤ))
      ((Polynomial.C (V.vVEntry j ell)).coeff k) := by
  rw [Polynomial.coeff_C]
  by_cases hk : k = 0
  · rw [ite_eq_left hk]
    exact V_val p j ell hp hpos hbound
  · rw [ite_eq_right hk]
    exact ValAtLeast.zero _ _

end
end Li2Lean.B3.Q5ResidueProof

namespace Li2Lean.B3.Q5ResidueProof

open scoped BigOperators
open Li2Lean.V Li2Lean.V.Q5Certificate

set_option maxHeartbeats 800000

def sourceRowIndex (n : ℕ) (r : Fin (vMatrixSize n)) : ℕ :=
  if r.val < vM n then 2 * n + r.val else 2 * n + (r.val - vM n)

def sourceLambda (n : ℕ) (r : Fin (vMatrixSize n)) : ℕ :=
  1 + (r.val - 2 * vM n)

def sourceHit (n p : ℕ) (r c : Fin (vMatrixSize n)) : Prop :=
  if r.val < 2 * vM n then
    sourceRowIndex n r % p = vJIndex n c % p ∧
      (sourceRowIndex n r ≠ vJIndex n c ∨ p ≤ sourceRowIndex n r)
  else p ∣ vJIndex n c + sourceLambda n r

instance (n p : ℕ) (r c : Fin (vMatrixSize n)) :
    Decidable (sourceHit n p r c) := by unfold sourceHit; infer_instance

def entryCost (n p : ℕ) (r c : Fin (vMatrixSize n)) : ℤ :=
  (if vM n ≤ r.val ∧ r.val < 2 * vM n then 1 else 0) +
    (if sourceHit n p r c then 1 else 0)

private theorem rowIndex_mem {n : ℕ} {r : Fin (vMatrixSize n)}
    (hr : r.val < 2 * vM n) :
    2 * n ≤ sourceRowIndex n r ∧ sourceRowIndex n r < 6 * n := by
  by_cases hC : r.val < vM n
  · simp only [sourceRowIndex, ite_eq_left hC]
    simp only [vM] at hC hr ⊢
    omega
  · simp only [sourceRowIndex, ite_eq_right hC]
    simp only [vM] at hC hr ⊢
    omega

private theorem sourceLambda_mem {n : ℕ} {r : Fin (vMatrixSize n)}
    (hr : ¬ r.val < 2 * vM n) :
    0 < sourceLambda n r ∧ sourceLambda n r ≤ n := by
  have := r.isLt
  simp only [sourceLambda, vMatrixSize, vM, vS] at *
  omega

private theorem residue_reconstruct (i p u : ℕ) (h : i % p = u) :
    u + (i / p) * p = i := by
  simpa [h, Nat.mul_comm] using Nat.mod_add_div i p

private theorem quotient_inj {p u : ℕ} {i j : ℕ}
    (hi : i % p = u) (hj : j % p = u) (hq : i / p = j / p) : i = j := by
  have h1 := residue_reconstruct i p u hi
  have h2 := residue_reconstruct j p u hj
  rw [hq] at h1
  omega

private theorem mem_K_of_index {n p u i : ℕ}
    (hi : 2 * n ≤ i ∧ i < 6 * n) (hmod : i % p = u) :
    i / p ∈ q5K (4 * n) p u := by
  have hq := Nat.div_le_self i p
  have heq := residue_reconstruct i p u hmod
  have hx : 2 * u + 2 * (i / p) * p = 2 * i := by
    calc
      _ = 2 * (u + (i / p) * p) := by ring
      _ = 2 * i := by rw [heq]
  simp only [q5K, Finset.mem_filter, Finset.mem_range, hx]
  omega

private theorem mem_L_of_index {n p u j : ℕ}
    (hj : n ≤ j ∧ j < 10 * n) (hmod : j % p = u) :
    j / p ∈ q5L (4 * n) p u := by
  have hq := Nat.div_le_self j p
  have heq := residue_reconstruct j p u hmod
  have hx : 4 * u + 4 * (j / p) * p = 4 * j := by
    calc
      _ = 4 * (u + (j / p) * p) := by ring
      _ = 4 * j := by rw [heq]
  simp only [q5L, Finset.mem_filter, Finset.mem_range, hx]
  omega

private theorem mem_W_of_lambda {n p u ell : ℕ}
    (hp : 0 < p) (hu : u < p) (hell : 0 < ell ∧ ell ≤ n)
    (hdiv : p ∣ u + ell) : (u + ell) / p ∈ q5W (4 * n) p u := by
  have heq : (u + ell) / p * p = u + ell := Nat.div_mul_cancel hdiv
  have hw : 0 < (u + ell) / p := by
    apply Nat.pos_of_ne_zero
    intro hz
    rw [hz, zero_mul] at heq
    omega
  have hbound : (u + ell) / p < 3 * (4 * n) + 2 := by
    apply (Nat.div_lt_iff_lt_mul hp).2
    have hnp : n ≤ n * p := by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left n hp
    calc
      u + ell < p + n := by omega
      _ ≤ p + n * p := Nat.add_le_add_left hnp p
      _ = (n + 1) * p := by ring
      _ ≤ (3 * (4 * n) + 2) * p := Nat.mul_le_mul_right p (by omega)
  simp only [q5W, Finset.mem_filter, Finset.mem_range]
  exact ⟨hbound, hw, by omega, by omega⟩

private def hitColumns (n p : ℕ) (σ : Equiv.Perm (Fin (vMatrixSize n)))
    (u : ℕ) : Finset (Fin (vMatrixSize n)) :=
  Finset.univ.filter (fun c => sourceHit n p (σ c) c ∧ vJIndex n c % p = u)

private theorem hitColumns_spec {n p u : ℕ}
    {σ : Equiv.Perm (Fin (vMatrixSize n))} {c : Fin (vMatrixSize n)}
    (hc : c ∈ hitColumns n p σ u) :
    sourceHit n p (σ c) c ∧ vJIndex n c % p = u := by
  simpa only [hitColumns, Finset.mem_filter, Finset.mem_univ, true_and] using hc

private def rowCode (n p u : ℕ) (r : Fin (vMatrixSize n)) : (Bool × ℕ) ⊕ ℕ :=
  if r.val < vM n then Sum.inl (false, sourceRowIndex n r / p)
  else if r.val < 2 * vM n then Sum.inl (true, sourceRowIndex n r / p)
  else Sum.inr ((u + sourceLambda n r) / p)

private def rowCodeSet (n p u : ℕ) : Finset ((Bool × ℕ) ⊕ ℕ) :=
  ((Finset.univ : Finset Bool).product (q5K (4 * n) p u)).disjSum
    (q5W (4 * n) p u)

private theorem hit_row_residue {n p u : ℕ}
    {r c : Fin (vMatrixSize n)} (hr : r.val < 2 * vM n)
    (hhit : sourceHit n p r c) (hcol : vJIndex n c % p = u) :
    sourceRowIndex n r % p = u := by
  have ht : sourceRowIndex n r % p = vJIndex n c % p ∧
      (sourceRowIndex n r ≠ vJIndex n c ∨ p ≤ sourceRowIndex n r) := by
    simpa only [sourceHit, ite_eq_left hr] using hhit
  exact ht.1.trans hcol

private theorem hit_lambda_div {n p u : ℕ}
    {r c : Fin (vMatrixSize n)} (hr : ¬ r.val < 2 * vM n)
    (hhit : sourceHit n p r c) (hcol : vJIndex n c % p = u) :
    p ∣ u + sourceLambda n r := by
  have hdiv : p ∣ vJIndex n c + sourceLambda n r := by
    simpa only [sourceHit, ite_eq_right hr] using hhit
  have hmod := Nat.mod_eq_zero_of_dvd hdiv
  apply Nat.dvd_of_mod_eq_zero
  simpa only [Nat.add_mod, ← hcol, Nat.mod_mod] using hmod

private theorem rowCode_mem {n p u : ℕ} (hp : 0 < p) (hu : u < p)
    {r c : Fin (vMatrixSize n)} (hhit : sourceHit n p r c)
    (hcol : vJIndex n c % p = u) : rowCode n p u r ∈ rowCodeSet n p u := by
  by_cases hC : r.val < vM n
  · have hCB : r.val < 2 * vM n := by omega
    have hk := mem_K_of_index (rowIndex_mem hCB) (hit_row_residue hCB hhit hcol)
    simp [rowCode, rowCodeSet, hC, hk]
  · by_cases hB : r.val < 2 * vM n
    · have hk := mem_K_of_index (rowIndex_mem hB) (hit_row_residue hB hhit hcol)
      simp [rowCode, rowCodeSet, hC, hB, hk]
    · have hw := mem_W_of_lambda hp hu (sourceLambda_mem hB)
        (hit_lambda_div hB hhit hcol)
      simp [rowCode, rowCodeSet, hC, hB, hw]

private theorem rowCode_inj {n p u : ℕ}
    {r₁ r₂ c₁ c₂ : Fin (vMatrixSize n)}
    (hh₁ : sourceHit n p r₁ c₁) (hc₁ : vJIndex n c₁ % p = u)
    (hh₂ : sourceHit n p r₂ c₂) (hc₂ : vJIndex n c₂ % p = u)
    (he : rowCode n p u r₁ = rowCode n p u r₂) : r₁ = r₂ := by
  by_cases hC₁ : r₁.val < vM n
  · have hCB₁ : r₁.val < 2 * vM n := by omega
    by_cases hC₂ : r₂.val < vM n
    · have hCB₂ : r₂.val < 2 * vM n := by omega
      have hq : sourceRowIndex n r₁ / p = sourceRowIndex n r₂ / p := by
        simpa only [rowCode, ite_eq_left hC₁, ite_eq_left hC₂, Sum.inl.injEq,
          Prod.mk.injEq, true_and] using he
      have hi := quotient_inj (hit_row_residue hCB₁ hh₁ hc₁)
        (hit_row_residue hCB₂ hh₂ hc₂) hq
      apply Fin.ext
      simp only [sourceRowIndex, ite_eq_left hC₁, ite_eq_left hC₂] at hi
      omega
    · by_cases hB₂ : r₂.val < 2 * vM n
      · simp [rowCode, hC₁, hC₂, hB₂] at he
      · simp [rowCode, hC₁, hC₂, hB₂] at he
  · by_cases hB₁ : r₁.val < 2 * vM n
    · by_cases hC₂ : r₂.val < vM n
      · simp [rowCode, hC₁, hB₁, hC₂] at he
      · by_cases hB₂ : r₂.val < 2 * vM n
        · have hq : sourceRowIndex n r₁ / p = sourceRowIndex n r₂ / p := by
            simpa only [rowCode, ite_eq_right hC₁, ite_eq_right hC₂, ite_eq_left hB₁,
              ite_eq_left hB₂, Sum.inl.injEq, Prod.mk.injEq, true_and] using he
          have hi := quotient_inj (hit_row_residue hB₁ hh₁ hc₁)
            (hit_row_residue hB₂ hh₂ hc₂) hq
          apply Fin.ext
          simp only [sourceRowIndex, ite_eq_right hC₁, ite_eq_right hC₂] at hi
          omega
        · simp [rowCode, hC₁, hB₁, hC₂, hB₂] at he
    · by_cases hC₂ : r₂.val < vM n
      · simp [rowCode, hC₁, hB₁, hC₂] at he
      · by_cases hB₂ : r₂.val < 2 * vM n
        · simp [rowCode, hC₁, hB₁, hC₂, hB₂] at he
        · have hq : (u + sourceLambda n r₁) / p = (u + sourceLambda n r₂) / p := by
            simpa only [rowCode, ite_eq_right hC₁, ite_eq_right hC₂, ite_eq_right hB₁,
              ite_eq_right hB₂, Sum.inr.injEq] using he
          have he₁ := Nat.div_mul_cancel (hit_lambda_div hB₁ hh₁ hc₁)
          have he₂ := Nat.div_mul_cancel (hit_lambda_div hB₂ hh₂ hc₂)
          rw [hq] at he₁
          apply Fin.ext
          unfold sourceLambda at he₁ he₂
          omega

private theorem hitColumns_card_rows {n p u : ℕ} (hp : 0 < p) (hu : u < p)
    (σ : Equiv.Perm (Fin (vMatrixSize n))) :
    (hitColumns n p σ u).card ≤
      2 * (q5K (4 * n) p u).card + (q5W (4 * n) p u).card := by
  have hcard := Finset.card_le_card_of_injOn
    (s := hitColumns n p σ u) (t := rowCodeSet n p u)
    (fun c => rowCode n p u (σ c))
    (by
      intro c hc
      obtain ⟨hhit, hcol⟩ := hitColumns_spec hc
      exact rowCode_mem hp hu hhit hcol)
    (by
      intro c₁ hc₁ c₂ hc₂ he
      obtain ⟨hh₁, hcol₁⟩ := hitColumns_spec hc₁
      obtain ⟨hh₂, hcol₂⟩ := hitColumns_spec hc₂
      exact σ.injective (rowCode_inj hh₁ hcol₁ hh₂ hcol₂ he))
  simpa [rowCodeSet] using hcard

private theorem column_quotient_inj {n p u : ℕ} {c₁ c₂ : Fin (vMatrixSize n)}
    (hc₁ : vJIndex n c₁ % p = u) (hc₂ : vJIndex n c₂ % p = u)
    (he : vJIndex n c₁ / p = vJIndex n c₂ / p) : c₁ = c₂ := by
  have hj := quotient_inj hc₁ hc₂ he
  apply Fin.ext
  simp only [vJIndex] at hj
  omega

private theorem hitColumns_card_columns {n p u : ℕ}
    (σ : Equiv.Perm (Fin (vMatrixSize n))) :
    (hitColumns n p σ u).card ≤ (q5L (4 * n) p u).card := by
  apply Finset.card_le_card_of_injOn (fun c => vJIndex n c / p)
  · intro c hc
    exact mem_L_of_index (vJIndex_mem n c) (hitColumns_spec hc).2
  · intro c₁ hc₁ c₂ hc₂ he
    exact column_quotient_inj (hitColumns_spec hc₁).2 (hitColumns_spec hc₂).2 he

private theorem special_column_quotient {n p u : ℕ} (hp : 0 < p) (hu : u < p)
    (hK : q5K (4 * n) p u = {0})
    (hL : q5L (4 * n) p u = {0, 1})
    (hW : q5W (4 * n) p u = ∅)
    {r c : Fin (vMatrixSize n)} (hhit : sourceHit n p r c)
    (hcol : vJIndex n c % p = u) : vJIndex n c / p = 1 := by
  have hqL := mem_L_of_index (vJIndex_mem n c) hcol
  rw [hL] at hqL
  simp only [Finset.mem_insert, Finset.mem_singleton] at hqL
  rcases hqL with hzero | hone
  · have hj := residue_reconstruct (vJIndex n c) p u hcol
    rw [hzero, zero_mul, add_zero] at hj
    by_cases hr : r.val < 2 * vM n
    · have hi_mod := hit_row_residue hr hhit hcol
      have hqK := mem_K_of_index (rowIndex_mem hr) hi_mod
      rw [hK, Finset.mem_singleton] at hqK
      have hi := residue_reconstruct (sourceRowIndex n r) p u hi_mod
      rw [hqK, zero_mul, add_zero] at hi
      have hh : sourceRowIndex n r % p = vJIndex n c % p ∧
          (sourceRowIndex n r ≠ vJIndex n c ∨ p ≤ sourceRowIndex n r) := by
        simpa only [sourceHit, ite_eq_left hr] using hhit
      omega
    · have hw := mem_W_of_lambda hp hu (sourceLambda_mem hr)
        (hit_lambda_div hr hhit hcol)
      rw [hW] at hw
      exact False.elim (Finset.notMem_empty _ hw)
  · exact hone

private theorem hitColumns_card_special {n p u : ℕ} (hp : 0 < p) (hu : u < p)
    (σ : Equiv.Perm (Fin (vMatrixSize n)))
    (hK : q5K (4 * n) p u = {0})
    (hL : q5L (4 * n) p u = {0, 1})
    (hW : q5W (4 * n) p u = ∅) : (hitColumns n p σ u).card ≤ 1 := by
  have hcard := Finset.card_le_card_of_injOn
    (s := hitColumns n p σ u) (t := ({1} : Finset ℕ))
    (fun c => vJIndex n c / p)
    (by
      intro c hc
      obtain ⟨hhit, hcol⟩ := hitColumns_spec hc
      exact Finset.mem_singleton.mpr (special_column_quotient hp hu hK hL hW hhit hcol))
    (by
      intro c₁ hc₁ c₂ hc₂ he
      exact column_quotient_inj (hitColumns_spec hc₁).2 (hitColumns_spec hc₂).2 he)
  simpa using hcard

private theorem hitColumns_card_profile {n p u : ℕ} (hp : 0 < p) (hu : u < p)
    (σ : Equiv.Perm (Fin (vMatrixSize n))) :
    ((hitColumns n p σ u).card : ℤ) ≤ q5RankProfile (4 * n) p u := by
  by_cases hs : q5K (4 * n) p u = {0} ∧
      q5L (4 * n) p u = {0, 1} ∧ q5W (4 * n) p u = ∅
  · rw [q5_rank_profile_special hs.1 hs.2.1 hs.2.2]
    exact_mod_cast hitColumns_card_special hp hu σ hs.1 hs.2.1 hs.2.2
  · have hrow := hitColumns_card_rows hp hu σ
    have hcol := hitColumns_card_columns (n := n) (p := p) (u := u) σ
    have hmin := le_min hrow hcol
    simp only [q5RankProfile, q5RankSaving, ite_eq_right hs, Nat.cast_zero, sub_zero]
    exact_mod_cast hmin

private theorem middleColumns_card_le (n : ℕ)
    (σ : Equiv.Perm (Fin (vMatrixSize n))) :
    (Finset.univ.filter (fun c => vM n ≤ (σ c).val ∧ (σ c).val < 2 * vM n)).card ≤
      vM n := by
  have hcard := Finset.card_le_card_of_injOn
    (s := Finset.univ.filter (fun c => vM n ≤ (σ c).val ∧ (σ c).val < 2 * vM n))
    (t := Finset.range (vM n)) (fun c => (σ c).val - vM n)
    (by
      intro c hc
      have hc' : vM n ≤ (σ c).val ∧ (σ c).val < 2 * vM n :=
        (Finset.mem_filter.mp hc).2
      change (σ c).val - vM n ∈ Finset.range (vM n)
      apply Finset.mem_range.mpr
      change (σ c).val - vM n < vM n
      omega)
    (by
      intro c₁ hc₁ c₂ hc₂ he
      have h₁ : vM n ≤ (σ c₁).val ∧ (σ c₁).val < 2 * vM n :=
        (Finset.mem_filter.mp hc₁).2
      have h₂ : vM n ≤ (σ c₂).val ∧ (σ c₂).val < 2 * vM n :=
        (Finset.mem_filter.mp hc₂).2
      change (σ c₁).val - vM n = (σ c₂).val - vM n at he
      apply σ.injective
      apply Fin.ext
      change (σ c₁).val = (σ c₂).val
      omega)
  simpa only [Finset.card_range] using hcard

/-- Every determinant assignment pays at most the paper's finite residue
profile. The exceptional profile is credited using its zero first column;
no rank hypothesis or unproved residue identity is needed. -/
theorem sum_entryCost_le_residueExponent (n p : ℕ) (hp : 0 < p)
    (σ : Equiv.Perm (Fin (vMatrixSize n))) :
    ∑ c, entryCost n p (σ c) c ≤ q5ResidueExponent (4 * n) p := by
  classical
  have hfiber :
      (Finset.univ.filter (fun c => sourceHit n p (σ c) c)).card =
        ∑ u ∈ Finset.range p, (hitColumns n p σ u).card := by
    have h := Finset.card_eq_sum_card_fiberwise
      (s := Finset.univ.filter (fun c => sourceHit n p (σ c) c))
      (t := Finset.range p) (f := fun c => vJIndex n c % p)
      (fun c _ => Finset.mem_range.mpr (Nat.mod_lt _ hp))
    simpa only [Finset.filter_filter, hitColumns] using h
  have hhits :
      ((Finset.univ.filter (fun c => sourceHit n p (σ c) c)).card : ℤ) ≤
        ∑ u ∈ Finset.range p, q5RankProfile (4 * n) p u := by
    rw [hfiber, Nat.cast_sum]
    apply Finset.sum_le_sum
    intro u hu
    exact hitColumns_card_profile hp (Finset.mem_range.mp hu) σ
  have hmiddle :
      ((Finset.univ.filter
        (fun c => vM n ≤ (σ c).val ∧ (σ c).val < 2 * vM n)).card : ℤ) ≤ vM n := by
    exact_mod_cast middleColumns_card_le n σ
  calc
    ∑ c, entryCost n p (σ c) c =
        ((Finset.univ.filter
          (fun c => vM n ≤ (σ c).val ∧ (σ c).val < 2 * vM n)).card : ℤ) +
          ((Finset.univ.filter (fun c => sourceHit n p (σ c) c)).card : ℤ) := by
      simp only [entryCost, Finset.sum_add_distrib, Finset.natCast_card_filter]
    _ ≤ (vM n : ℤ) + ∑ u ∈ Finset.range p, q5RankProfile (4 * n) p u :=
      add_le_add hmiddle hhits
    _ = q5ResidueExponent (4 * n) p := by rfl

end Li2Lean.B3.Q5ResidueProof

namespace Li2Lean.B3.Q5ResidueProof

open scoped BigOperators
open Li2Lean.V.Q5Certificate

theorem rankProfile_nonneg (m p u : ℕ) :
    0 ≤ q5RankProfile m p u := by
  unfold q5RankProfile q5RankSaving
  split_ifs with h
  · rcases h with ⟨hK, hL, hW⟩
    simp [hK, hL, hW]
  · simp only [Nat.cast_zero, sub_zero]
    exact_mod_cast (Nat.zero_le
      (min (2 * (q5K m p u).card + (q5W m p u).card) (q5L m p u).card))

theorem residueExponent_nonneg (m p : ℕ) :
    0 ≤ q5ResidueExponent m p := by
  unfold q5ResidueExponent
  exact add_nonneg (Int.natCast_nonneg _)
    (Finset.sum_nonneg (fun u _ => rankProfile_nonneg m p u))

end Li2Lean.B3.Q5ResidueProof

namespace Li2Lean.B3.Q5ResidueProof

noncomputable section

open scoped BigOperators

theorem polyVal_mul {p : ℕ} [Fact p.Prime] {a b : ℤ}
    {P Q : Polynomial ℚ}
    (hP : ∀ k, ValAtLeast p a (P.coeff k))
    (hQ : ∀ k, ValAtLeast p b (Q.coeff k)) :
    ∀ k, ValAtLeast p (a + b) ((P * Q).coeff k) := by
  intro k
  rw [Polynomial.coeff_mul]
  exact ValAtLeast.sum _ _ (fun x _ => (hP x.1).mul (hQ x.2))

theorem polyVal_one (p : ℕ) :
    ∀ k, ValAtLeast p 0 ((1 : Polynomial ℚ).coeff k) := by
  intro k
  rw [Polynomial.coeff_one]
  split
  · exact Or.inr (by simp)
  · exact ValAtLeast.zero _ _

theorem polyVal_prod {p : ℕ} [Fact p.Prime] {ι : Type*}
    (s : Finset ι) (f : ι → Polynomial ℚ) (a : ι → ℤ)
    (h : ∀ i ∈ s, ∀ k, ValAtLeast p (a i) ((f i).coeff k)) :
    ∀ k, ValAtLeast p (∑ i ∈ s, a i) ((∏ i ∈ s, f i).coeff k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using polyVal_one p
  | @insert x s hx ih =>
    rw [Finset.prod_insert hx, Finset.sum_insert hx]
    exact polyVal_mul (h x (Finset.mem_insert_self x s))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

theorem det_coeff_valAtLeast {p d : ℕ} [Fact p.Prime]
    (M : Matrix (Fin d) (Fin d) (Polynomial ℚ))
    (lower : Fin d → Fin d → ℤ) (L : ℤ)
    (hM : ∀ r c k, ValAtLeast p (lower r c) ((M r c).coeff k))
    (hL : ∀ σ : Equiv.Perm (Fin d), L ≤ ∑ i, lower (σ i) i) :
    ∀ k, ValAtLeast p L (M.det.coeff k) := by
  intro k
  rw [Matrix.det_apply, Polynomial.finsetSum_coeff]
  apply ValAtLeast.sum
  intro σ _
  have hprod := polyVal_prod Finset.univ (fun i => M (σ i) i)
    (fun i => lower (σ i) i) (fun i _ k => hM _ _ k) k
  have hprod' := hprod.mono (hL σ)
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
  · rw [hs, one_smul]
    exact hprod'
  · rw [hs, Units.neg_smul, one_smul, Polynomial.coeff_neg]
    exact hprod'.neg

end

end Li2Lean.B3.Q5ResidueProof

namespace Li2Lean.B3.Q5ResidueProof

open scoped BigOperators

noncomputable section

theorem sourceMatrix_coeff_val (n p : ℕ) (a : ℤ)
    (hn : 0 < n) (hp : p.Prime)
    (hlarge : max (V.vN n) (V.vU n) < p ^ 2)
    (r c : Fin (V.vMatrixSize n)) (k : ℕ) :
    ValAtLeast p (-entryCost n p r c)
      ((V.vSourceMatrix n a r c).coeff k) := by
  have hN : 10 * n - 1 < p ^ 2 :=
    lt_of_le_of_lt (le_max_left _ _) hlarge
  have hU : 11 * n - 1 < p ^ 2 :=
    lt_of_le_of_lt (le_max_right _ _) hlarge
  have hj := V.vJIndex_mem n c
  have hjp : V.vJIndex n c < p ^ 2 := by omega
  have hr := r.isLt
  simp only [V.vMatrixSize, V.vM, V.vS] at hr
  by_cases hC : r.val < V.vM n
  · have hCB : r.val < 2 * V.vM n := by omega
    have hnotB : ¬ V.vM n ≤ r.val := by omega
    have hi : 2 * n + r.val < p ^ 2 := by
      simp only [V.vM] at hC
      omega
    simpa [V.vSourceMatrix, V.vIIndexNat, entryCost, sourceHit,
      sourceRowIndex, entryExtra, hC, hCB, hnotB] using
      C_polynomial_val p a (2 * n + r.val) (V.vJIndex n c) hp hi hjp k
  · by_cases hB : r.val < 2 * V.vM n
    · have hge : V.vM n ≤ r.val := by omega
      have hi : 2 * n + (r.val - V.vM n) < p ^ 2 := by
        simp only [V.vM] at hC hB ⊢
        omega
      have hw : -entryCost n p r c =
          -1 - entryExtra p (2 * n + (r.val - V.vM n)) (V.vJIndex n c) := by
        simp [entryCost, sourceHit, sourceRowIndex, entryExtra, hC, hB, hge]
        <;> omega
      rw [hw]
      simpa only [V.vSourceMatrix, ite_eq_right hC, ite_eq_left hB] using
        B_polynomial_val p a (2 * n + (r.val - V.vM n))
          (V.vJIndex n c) hp hi hjp k
    · have hell : 0 < sourceLambda n r ∧ sourceLambda n r ≤ n := by
        simp only [sourceLambda, V.vM] at hB ⊢
        omega
      have hpos : 0 < V.vJIndex n c + sourceLambda n r := by omega
      have hbound : V.vJIndex n c + sourceLambda n r < p ^ 2 := by omega
      by_cases hd : p ∣ V.vJIndex n c + (1 + (r.val - 2 * V.vM n))
      all_goals
        simpa [V.vSourceMatrix, entryCost, sourceHit, sourceLambda, hC, hB, hd] using
          V_polynomial_val p (V.vJIndex n c) (sourceLambda n r)
            hp hpos hbound k

theorem sourceDeterminant_coeff_val (n p : ℕ) (a : ℤ)
    (hn : 0 < n) (hp : p.Prime)
    (hlarge : max (V.vN n) (V.vU n) < p ^ 2) (k : ℕ) :
    ValAtLeast p (-(V.Q5Certificate.q5ResidueExponent (4 * n) p))
      ((V.vPolynomial n a).coeff k) := by
  letI : Fact p.Prime := ⟨hp⟩
  apply det_coeff_valAtLeast (V.vSourceMatrix n a)
    (fun r c => -entryCost n p r c)
  · exact sourceMatrix_coeff_val n p a hn hp hlarge
  · intro σ
    simpa only [Finset.sum_neg_distrib] using
      neg_le_neg (sum_entryCost_le_residueExponent n p hp.pos σ)

end

end Li2Lean.B3.Q5ResidueProof

namespace Li2Lean.B3.Q5ResidueProof


theorem sourceDeterminant_gauss_bound (n p : ℕ) (a : ℤ)
    (hn : 0 < n) (hp : p.Prime)
    (hlarge : max (V.vN n) (V.vU n) < p ^ 2) :
    V.actualGaussValuation p (V.vPolynomial n a) ≥
      -(V.Q5Certificate.q5ResidueExponent (4 * n) p) := by
  classical
  unfold V.actualGaussValuation
  split_ifs with hsupport
  · apply Finset.le_inf'
    intro k hk
    exact (sourceDeterminant_coeff_val n p a hn hp hlarge k).resolve_left
      (Polynomial.mem_support_iff.mp hk)
  · have hnonneg := residueExponent_nonneg (4 * n) p
    omega

end Li2Lean.B3.Q5ResidueProof

namespace Li2Lean.B3

theorem q5_residue_bound_from_punit
    {n p : ℕ} (hn : 0 < n) (hp : Nat.Prime p)
    (hnotdiv : ¬ p ∣ 5 * (5 + 1))
    (hlarge : max (q567NumeratorCutoff n) (q567DenominatorCutoff n) < p ^ 2) :
    q5ActualGaussValuation n p ≥
      -(V.Q5Certificate.q5ResidueExponent (4 * n) p) := by
  clear hnotdiv
  have h := Q5ResidueProof.sourceDeterminant_gauss_bound n p (-5) hn hp hlarge
  simpa only [q5ActualGaussValuation, V.actualVDeterminant_four_mul,
    Nat.cast_ofNat] using h

end Li2Lean.B3

#print axioms Li2Lean.B3.q5_residue_bound_from_punit
