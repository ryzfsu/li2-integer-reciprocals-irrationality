/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.IntegerizationDeterminant
import Li2Lean.P0.ActualRationalIntegerizerProducer
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace Li2Lean.P0.Integerization

noncomputable section

open Filter Topology

/-!
# The actual P0 squarefull-prime error

The paper v13 cutoff is `p^2 ≤ U+g`, with `U=2m-1` and `g=m/2`.
This module bounds the small-prime contribution to the reduced denominator
of every coefficient of the literal `a=2` determinant.  Its input is the
proved row integerization, not an abstract valuation certificate.  The
remaining large-prime valuation profile is a separate obligation.
-/

/-- The actual upper-index cutoff used in the v13 Kummer split. -/
def p0SquarefullCutoff (m : ℕ) : ℕ := p0DenominatorU m + m / 2

/-- All primes in the paper's squarefull range, including `2`.  Including
`2` is harmless for an upper error bound and avoids an exceptional omission. -/
def p0SquarefullPrimes (m : ℕ) : Finset ℕ :=
  (Finset.range (Nat.sqrt (p0SquarefullCutoff m) + 1)).filter Nat.Prime

theorem mem_p0SquarefullPrimes {m p : ℕ} :
    p ∈ p0SquarefullPrimes m ↔ p.Prime ∧ p ^ 2 ≤ p0SquarefullCutoff m := by
  simp only [p0SquarefullPrimes, Finset.mem_filter, Finset.mem_range,
    Nat.lt_succ_iff, Nat.le_sqrt']
  exact and_comm

theorem p0SquarefullCutoff_le (m : ℕ) : p0SquarefullCutoff m ≤ 3 * m := by
  unfold p0SquarefullCutoff p0DenominatorU
  have hm2 := Nat.div_le_self m 2
  omega

private theorem lcm_factorization_le_log (s : Finset ℕ) (p U : ℕ)
    (hp : p.Prime) (hs : ∀ n ∈ s, n ≠ 0 ∧ n ≤ U) :
    (s.lcm id).factorization p ≤ Nat.log p U := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have has := hs a (Finset.mem_insert_self a s)
    have hss : ∀ n ∈ s, n ≠ 0 ∧ n ≤ U := fun n hn =>
      hs n (Finset.mem_insert_of_mem hn)
    have hs0 : s.lcm id ≠ 0 := by
      rw [Finset.lcm_ne_zero_iff]
      exact fun n hn => (hss n hn).1
    rw [Finset.lcm_insert]
    change (a.lcm (s.lcm id)).factorization p ≤ _
    rw [Nat.factorization_lcm has.1 hs0]
    change max (a.factorization p) ((s.lcm id).factorization p) ≤ _
    refine max_le ?_ (ih hss)
    rw [Nat.factorization_def a hp]
    exact (padicValNat_le_nat_log a).trans (Nat.log_mono_right has.2)

/-- The prime valuation of the actual common denominator is at most the
number of admissible prime-power layers. -/
theorem p0DenominatorLcm_factorization_le_log (m p : ℕ) (hp : p.Prime) :
    (p0DenominatorLcm m).factorization p ≤ Nat.log p (p0DenominatorU m) := by
  apply lcm_factorization_le_log (Finset.Icc 1 (p0DenominatorU m)) p
    (p0DenominatorU m) hp
  intro n hn
  have h := Finset.mem_Icc.mp hn
  exact ⟨by omega, h.2⟩

private theorem rat_den_dvd_of_int_multiple {q : ℚ} {d : ℕ}
    (hd : d ≠ 0) (hq : ∃ z : ℤ, (d : ℚ) * q = z) : q.den ∣ d := by
  obtain ⟨z, hz⟩ := hq
  have hdQ : (d : ℚ) ≠ 0 := by exact_mod_cast hd
  have heq : q = (z : ℚ) / (d : ℚ) := by
    apply (eq_div_iff hdQ).2
    simpa [mul_comm] using hz
  rw [heq]
  have hden : (((z : ℚ) / (d : ℚ)).den : ℤ) ∣ (d : ℤ) := by
    simpa [Rat.divInt_eq_div] using Rat.den_dvd z (d : ℤ)
  exact Int.natCast_dvd_natCast.mp hden

/-- A primewise lower bound on a rational coefficient controls the matching
prime in its reduced denominator. The positive part is needed because a
coefficient may already be divisible by `p`. -/
theorem rat_den_factorization_le_toNat_max_of_padic_lower {q : ℚ} {p : ℕ}
    (hp : p.Prime) (credit : ℤ)
    (hcredit : q = 0 ∨ -credit ≤ padicValRat p q) :
    q.den.factorization p ≤ (max credit 0).toNat := by
  letI : Fact p.Prime := ⟨hp⟩
  by_cases hq : q = 0
  · subst q
    norm_num
  · have hcredit := hcredit.resolve_left hq
    rcases Rat.num_or_den_zero_padicVal q hp with hnum | hden
    · have hval : padicValRat p q = -((q.den.factorization p : ℕ) : ℤ) := by
        rw [padicValRat_def, hnum, Nat.cast_zero, zero_sub,
          ← Nat.factorization_def q.den hp]
      have hfac : (q.den.factorization p : ℤ) ≤ credit := by
        rw [hval] at hcredit
        omega
      by_cases hc : 0 ≤ credit
      · rw [max_eq_left hc]
        exact (Int.le_toNat hc).2 hfac
      · have hfac0 : q.den.factorization p = 0 := by omega
        simp [max_eq_right (le_of_lt (lt_of_not_ge hc)), hfac0]
    · have hfac0 : q.den.factorization p = 0 := by
        rw [Nat.factorization_def q.den hp]
        exact hden
      simp [hfac0]

def p0FormalCreditSquarefullCost (q m : ℕ) : ℝ :=
  ∑ p ∈ p0SquarefullPrimes m,
    ((Int.toNat (max (Li2Lean.P0.formalDivisorCredit q m p) 0) : ℕ) : ℝ) *
      Real.log (p : ℝ)

def p0FormalExceptionalSquarefullCost (q m : ℕ) : ℝ :=
  ∑ p ∈ p0SquarefullPrimes m,
    (padicValNat p (q - 1) : ℝ) * Real.log (p : ℝ)

theorem p0FormalExceptionalSquarefullCost_le_log (q m : ℕ) (hq : 2 ≤ q) :
    p0FormalExceptionalSquarefullCost q m ≤ Real.log ((q - 1 : ℕ) : ℝ) := by
  let n : ℕ := q - 1
  let s : Finset ℕ := p0SquarefullPrimes m
  let t : Finset ℕ := n.primeFactors
  let f : ℕ → ℝ := fun p => (padicValNat p n : ℝ) * Real.log (p : ℝ)
  have hn : n ≠ 0 := by dsimp [n]; omega
  have hsumFilter : (∑ p ∈ s, f p) = ∑ p ∈ s.filter (fun p => p ∈ t), f p := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p hp
    by_cases hpt : p ∈ t
    · simp [hpt]
    · have hprime := (mem_p0SquarefullPrimes.mp (by simpa [s] using hp)).1
      have hnot : ¬ p ∣ n := by
        intro hdiv
        exact hpt (Nat.mem_primeFactors.mpr ⟨hprime, hdiv, hn⟩)
      have hv : padicValNat p n = 0 := padicValNat.eq_zero_of_not_dvd hnot
      simp [f, hpt, hv]
  have hsub : s.filter (fun p => p ∈ t) ⊆ t := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  have hnonneg : ∀ p ∈ t, p ∉ s.filter (fun p => p ∈ t) → 0 ≤ f p := by
    intro p hp _
    have hprime := (Nat.mem_primeFactors.mp (by simpa [t] using hp)).1
    apply mul_nonneg (Nat.cast_nonneg _)
    apply Real.log_nonneg
    exact_mod_cast hprime.one_lt.le
  have hsumle := Finset.sum_le_sum_of_subset_of_nonneg hsub hnonneg
  have hprodNat : n = ∏ p ∈ t, p ^ padicValNat p n := by
    calc
      n = ∏ p ∈ t, p ^ n.factorization p := Nat.prod_primeFactors_pow_factorization hn
      _ = ∏ p ∈ t, p ^ padicValNat p n := by
        apply Finset.prod_congr rfl
        intro p hp
        rw [Nat.factorization_def n (Nat.prime_of_mem_primeFactors hp)]
  have hprodReal : (n : ℝ) = ∏ p ∈ t, (p : ℝ) ^ padicValNat p n := by
    exact_mod_cast hprodNat
  have hlog : (∑ p ∈ t, f p) = Real.log (n : ℝ) := by
    calc
      (∑ p ∈ t, f p) =
          ∑ p ∈ t, Real.log ((p : ℝ) ^ padicValNat p n) := by
        apply Finset.sum_congr rfl
        intro p hp
        dsimp [f]
        rw [Real.log_pow]
      _ = Real.log (∏ p ∈ t, (p : ℝ) ^ padicValNat p n) := by
        symm
        rw [Real.log_prod]
        · intro p hp
          exact pow_ne_zero _ (by
            have hprime := (Nat.mem_primeFactors.mp (by simpa [t] using hp)).1
            exact_mod_cast hprime.ne_zero)
      _ = Real.log (n : ℝ) := by rw [← hprodReal]
  rw [← hsumFilter] at hsumle
  simpa [p0FormalExceptionalSquarefullCost, n, s, f] using hsumle.trans_eq hlog

private theorem formalDivisorN_nonneg (m : ℕ) :
    0 ≤ Li2Lean.P0.formalDivisorN m := by
  unfold Li2Lean.P0.formalDivisorN
  by_cases h : m / 4 = 0
  · simp [h]
  · have hm : 1 ≤ m / 4 := by omega
    nlinarith

private theorem formalDivisorH_toNat_max_le {m : ℕ} (h4 : 4 ∣ m) :
    (Int.toNat (max (Li2Lean.P0.formalDivisorH m) 0) : ℝ) ≤
      (m : ℝ) ^ 2 / 16 := by
  obtain ⟨h, rfl⟩ := h4
  have hH : Li2Lean.P0.formalDivisorH (4 * h) = (h : ℤ) ^ 2 - 3 * h := by
    simp [Li2Lean.P0.formalDivisorH]
  by_cases hh : h < 3
  · have hh2 : h ≤ 2 := by omega
    interval_cases h <;> norm_num [hH, Li2Lean.P0.formalDivisorH]
  · have hh3 : 3 ≤ h := by omega
    have hHpos : 0 ≤ (h : ℤ) ^ 2 - 3 * h := by nlinarith
    have hHcast :
        ((Int.toNat (max (Li2Lean.P0.formalDivisorH (4 * h)) 0) : ℕ) : ℝ) =
          ((max (Li2Lean.P0.formalDivisorH (4 * h)) 0 : ℤ) : ℝ) := by
      exact_mod_cast (Int.toNat_of_nonneg (le_max_right _ _))
    rw [hH, max_eq_left hHpos] at hHcast
    rw [hH, max_eq_left hHpos]
    rw [hHcast]
    push_cast
    norm_num
    nlinarith [sq_nonneg ((h : ℝ) - 3)]

private theorem formalCredit_toNat_le (q m p : ℕ) (hq : 2 ≤ q) :
    Int.toNat (max (Li2Lean.P0.formalDivisorCredit q m p) 0) ≤
      3 * m * Nat.log p (p0DenominatorU m) +
        Int.toNat (max (Li2Lean.P0.formalDivisorH m) 0) *
          padicValNat p (q - 1) := by
  let b : ℕ := 3 * m * Nat.log p (p0DenominatorU m)
  let v : ℕ := padicValNat p (q - 1)
  let w : ℕ := padicValNat p q
  let H : ℤ := Li2Lean.P0.formalDivisorH m
  let N : ℤ := Li2Lean.P0.formalDivisorN m
  have hb : 0 ≤ (b : ℤ) := Int.natCast_nonneg _
  have hv : 0 ≤ (v : ℤ) := Int.natCast_nonneg _
  have hw : 0 ≤ (w : ℤ) := Int.natCast_nonneg _
  have hN : 0 ≤ N := by
    change (0 : ℤ) ≤ (Li2Lean.P0.formalDivisorN m : ℤ)
    exact_mod_cast formalDivisorN_nonneg m
  have hHpos : 0 ≤ max H 0 := le_max_right _ _
  have hHmul : H * (v : ℤ) ≤ max H 0 * (v : ℤ) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hv
  have hNmul : -(N * (w : ℤ)) ≤ 0 := by
    have hprod : 0 ≤ N * (w : ℤ) := mul_nonneg hN hw
    linarith
  have hcredit : Li2Lean.P0.formalDivisorCredit q m p ≤
      (b : ℤ) + max H 0 * (v : ℤ) := by
    unfold Li2Lean.P0.formalDivisorCredit
    dsimp [b, v, w, H, N]
    have hcut : Li2Lean.P0.formalDivisorCutoff m = p0DenominatorU m := by
      rfl
    rw [hcut]
    linarith [hHmul, hNmul]
  have hbound : 0 ≤ (b : ℤ) + max H 0 * (v : ℤ) := by positivity
  have hmax : max (Li2Lean.P0.formalDivisorCredit q m p) 0 ≤
      (b : ℤ) + max H 0 * (v : ℤ) := max_le hcredit hbound
  have hHcast : ((Int.toNat (max H 0) : ℕ) : ℤ) = max H 0 :=
    Int.toNat_of_nonneg hHpos
  have hEq :
      ((b + Int.toNat (max H 0) * v : ℕ) : ℤ) =
        (b : ℤ) + max H 0 * (v : ℤ) := by
    simp [Nat.cast_mul, hHcast]
  have hNat :
      Int.toNat (max (Li2Lean.P0.formalDivisorCredit q m p) 0) ≤
        b + Int.toNat (max H 0) * v := by
    apply (Int.toNat_le).2
    rw [hEq]
    exact hmax
  simpa [b, v] using hNat

def p0QCoefficientSquarefullDenCost (q : ℕ) (m n : ℕ) : ℝ :=
  ∑ p ∈ p0SquarefullPrimes m,
    ((((p0CanonicalPolynomial (q : ℤ) m).coeff n).den.factorization p : ℕ) : ℝ) *
      Real.log (p : ℝ)

/-- The small-prime denominator contribution for a positive-base determinant
is bounded directly by the actual q-specific formal-divisor credit. The
statement consumes the producer's genuine coefficient estimate, rather
than a free numerator or a q=2-only row denominator. -/
theorem p0QCoefficientSquarefullDenCost_le_formalCredit
    (q m n : ℕ)
    (hformal : ∀ p : ℕ, p.Prime →
      (p0CanonicalPolynomial (q : ℤ) m).coeff n = 0 ∨
        -(Li2Lean.P0.formalDivisorCredit q m p) ≤
          padicValRat p ((p0CanonicalPolynomial (q : ℤ) m).coeff n)) :
    p0QCoefficientSquarefullDenCost q m n ≤
      p0FormalCreditSquarefullCost q m := by
  apply Finset.sum_le_sum
  intro p hp
  have hprime := (mem_p0SquarefullPrimes.mp hp).1
  apply mul_le_mul_of_nonneg_right
  · exact_mod_cast rat_den_factorization_le_toNat_max_of_padic_lower hprime
      (Li2Lean.P0.formalDivisorCredit q m p) (hformal p hprime)
  · apply Real.log_nonneg
    exact_mod_cast hprime.one_lt.le

/-- The generic producer's formal-divisor field supplies the small-prime
denominator bound for its actual q-base determinant. -/
theorem p0QCoefficientSquarefullDenCost_le_producerCredit
    {q : ℕ} {hq : Li2Lean.P0.PositiveBase.InRange (q : ℤ)} {rate : ℝ}
    (P : Li2Lean.P0.ActualRationalIntegerizerProducer q hq rate)
    (m : ℕ) (hm : 0 < m) (h4 : 4 ∣ m) (n : ℕ) :
    p0QCoefficientSquarefullDenCost q m n ≤
      p0FormalCreditSquarefullCost q m := by
  apply p0QCoefficientSquarefullDenCost_le_formalCredit
  intro p hp
  exact P.formal_divisor_coeff m hm h4 p hp n

/-- A literal coefficient's reduced denominator divides the already proved
row-scale product `d_U^(3m)`.  This also covers zero coefficients. -/
theorem p0A2_coeff_den_dvd_baseline {m : ℕ} (h4 : 4 ∣ m) (n : ℕ) :
    ((p0CanonicalPolynomial 2 m).coeff n).den ∣
      (p0DenominatorLcm m) ^ (3 * m) := by
  have hd : p0DenominatorLcm m ≠ 0 := by
    unfold p0DenominatorLcm denominatorLcm
    rw [Finset.lcm_ne_zero_iff]
    intro s hs
    exact Nat.ne_of_gt ((Finset.mem_Icc.mp hs).1)
  apply rat_den_dvd_of_int_multiple (pow_ne_zero _ hd)
  obtain ⟨P, hP⟩ := p0_canonical_integerized_two m h4
  have hc := congrArg (fun Q : Polynomial ℚ => Q.coeff n) hP
  refine ⟨P.coeff n, ?_⟩
  rw [Polynomial.coeff_C_mul] at hc
  simpa using hc.symm

/-! ### Base-parametric denominator interface

The squarefull argument does not use that the source base is `2`.  The only
base-specific input is the row-integerization witness.  Keeping that witness
explicit here makes the q-port honest: a caller supplies the determinant
integerization for `p0CanonicalPolynomial q m`, and all denominator and
valuation consequences are then uniform in `q`.
-/

theorem p0Coeff_den_dvd_baseline_of_integerized (q : ℤ) {m : ℕ}
    (hInt : ∃ P : Polynomial ℤ,
      Polynomial.map (Int.castRingHom ℚ) P =
        Polynomial.C ((p0DenominatorLcm m : ℚ) ^ (3 * m)) *
          p0CanonicalPolynomial q m)
    (n : ℕ) :
    ((p0CanonicalPolynomial q m).coeff n).den ∣
      (p0DenominatorLcm m) ^ (3 * m) := by
  have hd : p0DenominatorLcm m ≠ 0 := by
    unfold p0DenominatorLcm denominatorLcm
    rw [Finset.lcm_ne_zero_iff]
    intro s hs
    exact Nat.ne_of_gt ((Finset.mem_Icc.mp hs).1)
  apply rat_den_dvd_of_int_multiple (pow_ne_zero _ hd)
  obtain ⟨P, hP⟩ := hInt
  have hc := congrArg (fun Q : Polynomial ℚ => Q.coeff n) hP
  refine ⟨P.coeff n, ?_⟩
  rw [Polynomial.coeff_C_mul] at hc
  simpa using hc.symm

theorem p0Coeff_den_factorization_le_of_integerized (q : ℤ) {m p : ℕ}
    (hp : p.Prime)
    (hInt : ∀ n : ℕ, ∃ P : Polynomial ℤ,
      Polynomial.map (Int.castRingHom ℚ) P =
        Polynomial.C ((p0DenominatorLcm m : ℚ) ^ (3 * m)) *
          p0CanonicalPolynomial q m)
    (n : ℕ) :
    ((p0CanonicalPolynomial q m).coeff n).den.factorization p ≤
      (3 * m) * Nat.log p (p0DenominatorU m) := by
  have hd0 : (p0DenominatorLcm m) ^ (3 * m) ≠ 0 := by
    unfold p0DenominatorLcm denominatorLcm
    apply pow_ne_zero
    rw [Finset.lcm_ne_zero_iff]
    intro s hs
    exact Nat.ne_of_gt ((Finset.mem_Icc.mp hs).1)
  calc
    _ ≤ ((p0DenominatorLcm m) ^ (3 * m)).factorization p :=
      Nat.factorization_le_factorization_of_dvd_right
        (p0Coeff_den_dvd_baseline_of_integerized q (hInt n) n)
        (Rat.den_nz _) hd0
    _ = (3 * m) * (p0DenominatorLcm m).factorization p := by
      simp [Nat.factorization_pow, mul_comm]
    _ ≤ _ := Nat.mul_le_mul_left _
      (p0DenominatorLcm_factorization_le_log m p hp)

/-- Actual source-linked small-prime valuation bound for every coefficient. -/
theorem p0A2_coeff_den_factorization_le {m p : ℕ} (h4 : 4 ∣ m)
    (hp : p.Prime) (n : ℕ) :
    ((p0CanonicalPolynomial 2 m).coeff n).den.factorization p ≤
      (3 * m) * Nat.log p (p0DenominatorU m) := by
  have hd0 : (p0DenominatorLcm m) ^ (3 * m) ≠ 0 := by
    unfold p0DenominatorLcm denominatorLcm
    apply pow_ne_zero
    rw [Finset.lcm_ne_zero_iff]
    intro s hs
    exact Nat.ne_of_gt ((Finset.mem_Icc.mp hs).1)
  calc
    _ ≤ ((p0DenominatorLcm m) ^ (3 * m)).factorization p :=
      Nat.factorization_le_factorization_of_dvd_right
        (p0A2_coeff_den_dvd_baseline h4 n) (Rat.den_nz _) hd0
    _ = (3 * m) * (p0DenominatorLcm m).factorization p := by
      simp [Nat.factorization_pow, mul_comm]
    _ ≤ _ := Nat.mul_le_mul_left _ (p0DenominatorLcm_factorization_le_log m p hp)

/-- The full binomial valuation bound required for the squarefull range.
The upper index is the actual source index `i+g`, not a replaced scale. -/
theorem p0_source_choose_padicVal_le_log {m i k p : ℕ}
    (hm : 0 < m) (hi : i < 2 * m) (hp : p.Prime) :
    padicValNat p (Nat.choose (i + m / 2) k) ≤ Nat.log p (p0SquarefullCutoff m) := by
  rw [← Nat.factorization_def _ hp]
  apply Nat.factorization_choose_le_log.trans
  apply Nat.log_mono_right
  unfold p0SquarefullCutoff p0DenominatorU
  omega

/-- Multiplying the prime-power layer count by `log p` costs at most one
copy of `log U`.  This proof needs no prime number theorem. -/
theorem natLog_mul_realLog_le {p U : ℕ} (hp : 0 < p) (hU : 0 < U) :
    (Nat.log p U : ℝ) * Real.log (p : ℝ) ≤ Real.log (U : ℝ) := by
  have hpow := Nat.pow_log_le_self p (Nat.ne_of_gt hU)
  have hpowR : (p : ℝ) ^ Nat.log p U ≤ (U : ℝ) := by exact_mod_cast hpow
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  have hlog := Real.log_le_log (pow_pos hpR _) hpowR
  simpa only [Real.log_pow] using hlog

/-- Log-weighted version for an actual source binomial.  All shifted lower
upper indices are also covered by replacing `i` with their smaller index. -/
theorem p0_source_choose_padicLog_le {m i k p : ℕ}
    (hm : 0 < m) (hi : i < 2 * m) (hp : p.Prime) :
    (padicValNat p (Nat.choose (i + m / 2) k) : ℝ) * Real.log (p : ℝ) ≤
      Real.log (p0SquarefullCutoff m : ℝ) := by
  have hX : 0 < p0SquarefullCutoff m := by
    unfold p0SquarefullCutoff p0DenominatorU
    omega
  have hpLog : 0 ≤ Real.log (p : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast hp.one_lt.le
  calc
    _ ≤ (Nat.log p (p0SquarefullCutoff m) : ℝ) * Real.log (p : ℝ) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast p0_source_choose_padicVal_le_log hm hi hp) hpLog
    _ ≤ _ := natLog_mul_realLog_le hp.pos hX

/-- The generic squarefull exponent budget from v13. -/
def p0SquarefullPrimeLayerCost (m : ℕ) : ℝ :=
  ∑ p ∈ p0SquarefullPrimes m,
    ((3 * m * Nat.log p (p0DenominatorU m) : ℕ) : ℝ) * Real.log (p : ℝ)

theorem p0FormalCreditSquarefullCost_le_baseline_exceptional
    (q m : ℕ) (hq : 2 ≤ q) :
    p0FormalCreditSquarefullCost q m ≤
      p0SquarefullPrimeLayerCost m +
        (Int.toNat (max (Li2Lean.P0.formalDivisorH m) 0) : ℝ) *
          p0FormalExceptionalSquarefullCost q m := by
  unfold p0FormalCreditSquarefullCost p0SquarefullPrimeLayerCost
    p0FormalExceptionalSquarefullCost
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro p hp
  have hlog : 0 ≤ Real.log (p : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast (mem_p0SquarefullPrimes.mp hp).1.one_lt.le
  have hpoint := formalCredit_toNat_le q m p hq
  have hpointR :
      ((Int.toNat (max (Li2Lean.P0.formalDivisorCredit q m p) 0) : ℕ) : ℝ) ≤
        ((3 * m * Nat.log p (p0DenominatorU m) : ℕ) : ℝ) +
          (Int.toNat (max (Li2Lean.P0.formalDivisorH m) 0) : ℝ) *
            (padicValNat p (q - 1) : ℝ) := by
    exact_mod_cast hpoint
  calc
    _ ≤ (((3 * m * Nat.log p (p0DenominatorU m) : ℕ) : ℝ) +
        (Int.toNat (max (Li2Lean.P0.formalDivisorH m) 0) : ℝ) *
          (padicValNat p (q - 1) : ℝ)) * Real.log (p : ℝ) :=
      mul_le_mul_of_nonneg_right hpointR hlog
    _ = _ := by ring

def p0SquarefullCoefficientDenCostQ (q : ℤ) (m n : ℕ) : ℝ :=
  ∑ p ∈ p0SquarefullPrimes m,
    ((((p0CanonicalPolynomial q m).coeff n).den.factorization p : ℕ) : ℝ) *
      Real.log (p : ℝ)

theorem p0SquarefullCoefficientDenCostQ_nonneg (q : ℤ) (m n : ℕ) :
    0 ≤ p0SquarefullCoefficientDenCostQ q m n := by
  apply Finset.sum_nonneg
  intro p hp
  have hprime := (mem_p0SquarefullPrimes.mp hp).1
  apply mul_nonneg (Nat.cast_nonneg _)
  apply Real.log_nonneg
  exact_mod_cast hprime.one_lt.le

theorem p0SquarefullCoefficientDenCostQ_le_layerCost (q : ℤ) {m : ℕ}
    (hInt : ∀ n : ℕ, ∃ P : Polynomial ℤ,
      Polynomial.map (Int.castRingHom ℚ) P =
        Polynomial.C ((p0DenominatorLcm m : ℚ) ^ (3 * m)) *
          p0CanonicalPolynomial q m)
    (n : ℕ) :
    p0SquarefullCoefficientDenCostQ q m n ≤
      p0SquarefullPrimeLayerCost m := by
  apply Finset.sum_le_sum
  intro p hp
  have hprime := (mem_p0SquarefullPrimes.mp hp).1
  apply mul_le_mul_of_nonneg_right
  · exact_mod_cast p0Coeff_den_factorization_le_of_integerized q hprime hInt n
  · apply Real.log_nonneg
    exact_mod_cast hprime.one_lt.le

/-- The squarefull-prime log contribution of an actual coefficient's
reduced denominator.  No valuation of a model polynomial is substituted. -/
def p0SquarefullCoefficientDenCost (m n : ℕ) : ℝ :=
  ∑ p ∈ p0SquarefullPrimes m,
    ((((p0CanonicalPolynomial 2 m).coeff n).den.factorization p : ℕ) : ℝ) *
      Real.log (p : ℝ)

/-- An elementary quantitative envelope, `O(m^(3/2) log m)`. -/
def p0SquarefullErrorBound (x : ℝ) : ℝ :=
  3 * x * (Real.sqrt (3 * x) + 1) * Real.log (2 * x)

theorem p0SquarefullPrimeLayerCost_nonneg (m : ℕ) :
    0 ≤ p0SquarefullPrimeLayerCost m := by
  apply Finset.sum_nonneg
  intro p hp
  have hprime := (mem_p0SquarefullPrimes.mp hp).1
  apply mul_nonneg (Nat.cast_nonneg _)
  apply Real.log_nonneg
  exact_mod_cast hprime.one_lt.le

theorem p0SquarefullCoefficientDenCost_nonneg (m n : ℕ) :
    0 ≤ p0SquarefullCoefficientDenCost m n := by
  apply Finset.sum_nonneg
  intro p hp
  have hprime := (mem_p0SquarefullPrimes.mp hp).1
  apply mul_nonneg (Nat.cast_nonneg _)
  apply Real.log_nonneg
  exact_mod_cast hprime.one_lt.le

theorem p0SquarefullCoefficientDenCost_le_layerCost {m : ℕ}
    (h4 : 4 ∣ m) (n : ℕ) :
    p0SquarefullCoefficientDenCost m n ≤ p0SquarefullPrimeLayerCost m := by
  apply Finset.sum_le_sum
  intro p hp
  have hprime := (mem_p0SquarefullPrimes.mp hp).1
  apply mul_le_mul_of_nonneg_right
  · exact_mod_cast p0A2_coeff_den_factorization_le h4 hprime n
  · apply Real.log_nonneg
    exact_mod_cast hprime.one_lt.le

/-- Quantitative squarefull-prime error with the paper's actual cutoff.
This bound uses only the count of integers below the square root; it needs
neither PNT nor an independently supplied theta bound. -/
theorem p0SquarefullPrimeLayerCost_le_errorBound {m : ℕ} (hm : 0 < m) :
    p0SquarefullPrimeLayerCost m ≤ p0SquarefullErrorBound (m : ℝ) := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hU : 0 < p0DenominatorU m := by unfold p0DenominatorU; omega
  have hUle : (p0DenominatorU m : ℝ) ≤ 2 * (m : ℝ) := by
    have : p0DenominatorU m ≤ 2 * m := by unfold p0DenominatorU; omega
    exact_mod_cast this
  have hlogUle : Real.log (p0DenominatorU m : ℝ) ≤ Real.log (2 * (m : ℝ)) :=
    Real.log_le_log (by exact_mod_cast hU) hUle
  have hlognonneg : 0 ≤ Real.log (2 * (m : ℝ)) := by
    apply Real.log_nonneg
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hterm (p : ℕ) (hp : p ∈ p0SquarefullPrimes m) :
      ((3 * m * Nat.log p (p0DenominatorU m) : ℕ) : ℝ) * Real.log (p : ℝ) ≤
        3 * (m : ℝ) * Real.log (2 * (m : ℝ)) := by
    have hprime := (mem_p0SquarefullPrimes.mp hp).1
    have h := (natLog_mul_realLog_le hprime.pos hU).trans hlogUle
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ 3 * (m : ℝ))]
  have hcard : (p0SquarefullPrimes m).card ≤ Nat.sqrt (p0SquarefullCutoff m) + 1 := by
    unfold p0SquarefullPrimes
    exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)
  have hsqrt : (Nat.sqrt (p0SquarefullCutoff m) : ℝ) ≤ Real.sqrt (3 * (m : ℝ)) := by
    apply Real.le_sqrt_of_sq_le
    have hsq := (Nat.sqrt_le' (p0SquarefullCutoff m)).trans (p0SquarefullCutoff_le m)
    exact_mod_cast hsq
  have hcardR : ((p0SquarefullPrimes m).card : ℝ) ≤ Real.sqrt (3 * (m : ℝ)) + 1 := by
    have hc : ((p0SquarefullPrimes m).card : ℝ) ≤
        (Nat.sqrt (p0SquarefullCutoff m) : ℝ) + 1 := by exact_mod_cast hcard
    linarith
  calc
    p0SquarefullPrimeLayerCost m ≤
        ∑ p ∈ p0SquarefullPrimes m, 3 * (m : ℝ) * Real.log (2 * (m : ℝ)) :=
      Finset.sum_le_sum hterm
    _ = ((p0SquarefullPrimes m).card : ℝ) *
        (3 * (m : ℝ) * Real.log (2 * (m : ℝ))) := by simp
    _ ≤ (Real.sqrt (3 * (m : ℝ)) + 1) *
        (3 * (m : ℝ) * Real.log (2 * (m : ℝ))) :=
      mul_le_mul_of_nonneg_right hcardR (by positivity)
    _ = p0SquarefullErrorBound (m : ℝ) := by unfold p0SquarefullErrorBound; ring

theorem p0FormalCreditSquarefullCost_le_error_plus_q_correction
    (q m : ℕ) (hq : 2 ≤ q) (hm : 0 < m) (h4 : 4 ∣ m) :
    p0FormalCreditSquarefullCost q m ≤
      p0SquarefullErrorBound (m : ℝ) +
        (1 / 16 : ℝ) * (m : ℝ) ^ 2 * Real.log ((q - 1 : ℕ) : ℝ) := by
  have hcredit := p0FormalCreditSquarefullCost_le_baseline_exceptional q m hq
  have hbase := p0SquarefullPrimeLayerCost_le_errorBound hm
  have hexception := p0FormalExceptionalSquarefullCost_le_log q m hq
  have hH := formalDivisorH_toNat_max_le h4
  have hlog : 0 ≤ Real.log ((q - 1 : ℕ) : ℝ) := by
    apply Real.log_nonneg
    have hq' : 1 ≤ q - 1 := by omega
    exact_mod_cast hq'
  have hExcNonneg : 0 ≤ p0FormalExceptionalSquarefullCost q m := by
    apply Finset.sum_nonneg
    intro p hp
    have hprime := (mem_p0SquarefullPrimes.mp hp).1
    apply mul_nonneg (Nat.cast_nonneg _)
    apply Real.log_nonneg
    exact_mod_cast hprime.one_lt.le
  have hprod :
      (Int.toNat (max (Li2Lean.P0.formalDivisorH m) 0) : ℝ) *
          p0FormalExceptionalSquarefullCost q m ≤
        (1 / 16 : ℝ) * (m : ℝ)^2 * Real.log ((q - 1 : ℕ) : ℝ) := by
    calc
      _ ≤ ((m : ℝ)^2 / 16) * p0FormalExceptionalSquarefullCost q m :=
        mul_le_mul_of_nonneg_right hH hExcNonneg
      _ ≤ (1 / 16 : ℝ) * (m : ℝ)^2 * Real.log ((q - 1 : ℕ) : ℝ) := by
        nlinarith [mul_le_mul_of_nonneg_left hexception (by positivity :
          0 ≤ (m : ℝ)^2 / 16)]
  linarith

theorem p0QCoefficientSquarefullDenCost_le_error_plus_q_correction
    (q m n : ℕ) (hq : 2 ≤ q) (hm : 0 < m) (h4 : 4 ∣ m)
    (hformal : ∀ p : ℕ, p.Prime →
      (p0CanonicalPolynomial (q : ℤ) m).coeff n = 0 ∨
        -(Li2Lean.P0.formalDivisorCredit q m p) ≤
          padicValRat p ((p0CanonicalPolynomial (q : ℤ) m).coeff n)) :
    p0QCoefficientSquarefullDenCost q m n ≤
      p0SquarefullErrorBound (m : ℝ) +
        (1 / 16 : ℝ) * (m : ℝ)^2 * Real.log ((q - 1 : ℕ) : ℝ) := by
  exact (p0QCoefficientSquarefullDenCost_le_formalCredit q m n hformal).trans
    (p0FormalCreditSquarefullCost_le_error_plus_q_correction q m
      hq hm h4)

private theorem log_scaled_div_sqrt_tendsto_zero :
    Tendsto (fun x : ℝ => Real.log (2 * x) / Real.sqrt x) atTop (𝓝 0) := by
  have hlog : Tendsto (fun x : ℝ => Real.log x / Real.sqrt x) atTop (𝓝 0) := by
    simpa only [Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  have hinv : Tendsto (fun x : ℝ => (Real.sqrt x)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop
  have hsum : Tendsto (fun x : ℝ => Real.log 2 * (Real.sqrt x)⁻¹ +
      Real.log x / Real.sqrt x) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hinv).add hlog
  apply hsum.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [Real.log_mul (by norm_num) hx.ne', add_div]
  simp [div_eq_mul_inv]

private theorem log_scaled_div_tendsto_zero :
    Tendsto (fun x : ℝ => Real.log (2 * x) / x) atTop (𝓝 0) := by
  have hlog := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hinv : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hsum : Tendsto (fun x : ℝ => Real.log 2 * x⁻¹ + Real.log x / x)
      atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hinv).add hlog
  apply hsum.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [Real.log_mul (by norm_num) hx.ne', add_div]
  simp [div_eq_mul_inv]

/-- The normalized explicit error envelope tends to zero. -/
theorem p0SquarefullErrorBound_div_sq_tendsto_zero :
    Tendsto (fun x : ℝ => p0SquarefullErrorBound x / x ^ 2) atTop (𝓝 0) := by
  have hsum : Tendsto (fun x : ℝ =>
      (3 * Real.sqrt 3) * (Real.log (2 * x) / Real.sqrt x) +
        3 * (Real.log (2 * x) / x)) atTop (𝓝 0) := by
    simpa using
      (tendsto_const_nhds.mul log_scaled_div_sqrt_tendsto_zero).add
        (tendsto_const_nhds.mul log_scaled_div_tendsto_zero)
  apply hsum.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  unfold p0SquarefullErrorBound
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
  have hs : Real.sqrt x ≠ 0 := (Real.sqrt_pos.2 hx).ne'
  have hsq := Real.sq_sqrt hx.le
  field_simp [hx.ne', hs]
  ring_nf
  rw [Real.sq_sqrt hx.le]
  ring

/-- The paper's exact generic small-prime budget is negligible after the
same `m^2` normalization used by the weighted-prime rate. -/
theorem p0SquarefullPrimeLayerCost_div_sq_tendsto_zero :
    Tendsto (fun m : ℕ => p0SquarefullPrimeLayerCost m / (m : ℝ) ^ 2)
      atTop (𝓝 0) := by
  have hlim : Tendsto (fun m : ℕ => p0SquarefullErrorBound (m : ℝ) / (m : ℝ) ^ 2)
      atTop (𝓝 0) :=
    p0SquarefullErrorBound_div_sq_tendsto_zero.comp tendsto_natCast_atTop_atTop
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
  · filter_upwards [] with m
    exact div_nonneg (p0SquarefullPrimeLayerCost_nonneg m) (sq_nonneg _)
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with m hm
    exact div_le_div_of_nonneg_right (p0SquarefullPrimeLayerCost_le_errorBound hm) (sq_nonneg _)

/-- The small-prime part of the actual plan's minimum exponent has the
formal-divisor correction rate, for every moving exponent and prime cutoff.
There is no producer or rate hypothesis: this proves the low-prime part of
`pnt_rate` before constructing the producer (v13 p0-arithmetic.tex:326-421). -/
theorem p0LowPrime_minExponent_rate_bound
    (q : ℕ) (hq : 2 ≤ q) (cutoff : ℕ → ℕ) (W : ℕ → ℕ → ℤ) :
    ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, ∀ m : ℕ, M ≤ m → 0 < m → 4 ∣ m →
      (∑ p ∈ (Nat.primesLE (cutoff m)).filter (fun p => p ∈ p0SquarefullPrimes m),
        ((min (Li2Lean.P0.formalDivisorCredit q m p) (W m p) : ℤ) : ℝ) *
          Real.log (p : ℝ)) / (m : ℝ)^2 ≤
        (1 / 16 : ℝ) * Real.log ((q - 1 : ℕ) : ℝ) + ε := by
  intro ε hε
  have hsmall := (p0SquarefullErrorBound_div_sq_tendsto_zero.comp
    tendsto_natCast_atTop_atTop).eventually_lt_const hε
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp hsmall
  refine ⟨M, ?_⟩
  intro m hmM hm h4
  let s := (Nat.primesLE (cutoff m)).filter (fun p => p ∈ p0SquarefullPrimes m)
  let f : ℕ → ℝ := fun p =>
    ((Int.toNat (max (Li2Lean.P0.formalDivisorCredit q m p) 0) : ℕ) : ℝ) *
      Real.log (p : ℝ)
  have hpart : (∑ p ∈ s,
      ((min (Li2Lean.P0.formalDivisorCredit q m p) (W m p) : ℤ) : ℝ) *
        Real.log (p : ℝ)) ≤ ∑ p ∈ s, f p := by
    apply Finset.sum_le_sum
    intro p hp
    have hprime := (Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).2
    have hlog : 0 ≤ Real.log (p : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hprime.one_lt.le)
    apply mul_le_mul_of_nonneg_right _ hlog
    have hmin : min (Li2Lean.P0.formalDivisorCredit q m p) (W m p) ≤
        max (Li2Lean.P0.formalDivisorCredit q m p) 0 :=
      (min_le_left _ _).trans (le_max_left _ _)
    have hnonneg : 0 ≤ max (Li2Lean.P0.formalDivisorCredit q m p) 0 := le_max_right _ _
    have hcast := Int.toNat_of_nonneg hnonneg
    exact_mod_cast (show min (Li2Lean.P0.formalDivisorCredit q m p) (W m p) ≤
      (Int.toNat (max (Li2Lean.P0.formalDivisorCredit q m p) 0) : ℤ) by
        rw [hcast]; exact hmin)
  have hsub : s ⊆ p0SquarefullPrimes m := fun p hp => (Finset.mem_filter.mp hp).2
  have hcost : (∑ p ∈ s, f p) ≤ p0FormalCreditSquarefullCost q m := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro p hp _
    have hprime := (mem_p0SquarefullPrimes.mp hp).1
    exact mul_nonneg (Nat.cast_nonneg _)
      (Real.log_nonneg (by exact_mod_cast hprime.one_lt.le))
  have hbound := (hpart.trans hcost).trans
    (p0FormalCreditSquarefullCost_le_error_plus_q_correction q m hq hm h4)
  have hden0 : (m : ℝ)^2 ≠ 0 := by positivity
  have hdiv := div_le_div_of_nonneg_right hbound (sq_nonneg (m : ℝ))
  rw [add_div] at hdiv
  have hcancel : ((1 / 16 : ℝ) * (m : ℝ)^2 * Real.log ((q - 1 : ℕ) : ℝ)) /
      (m : ℝ)^2 = (1 / 16 : ℝ) * Real.log ((q - 1 : ℕ) : ℝ) := by
    field_simp
  rw [hcancel] at hdiv
  have htail : p0SquarefullErrorBound (m : ℝ) / (m : ℝ)^2 < ε := by
    simpa [Function.comp_apply] using hM m hmM
  exact hdiv.trans (by linarith)

theorem p0QCoefficientSquarefullDenCost_rate_bound
    {q : ℕ} {hq : Li2Lean.P0.PositiveBase.InRange (q : ℤ)}
    (hformal : ∀ m : ℕ, 0 < m → 4 ∣ m → ∀ n p : ℕ, p.Prime →
      (p0CanonicalPolynomial (q : ℤ) m).coeff n = 0 ∨
        -(Li2Lean.P0.formalDivisorCredit q m p) ≤
          padicValRat p ((p0CanonicalPolynomial (q : ℤ) m).coeff n)) :
    ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, ∀ m n : ℕ, M ≤ m → 0 < m → 4 ∣ m →
      p0QCoefficientSquarefullDenCost q m n / (m : ℝ)^2 ≤
        (1 / 16 : ℝ) * Real.log ((q - 1 : ℕ) : ℝ) + ε := by
  intro ε hε
  have hsmall := (p0SquarefullErrorBound_div_sq_tendsto_zero.comp
    tendsto_natCast_atTop_atTop).eventually_lt_const hε
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp hsmall
  refine ⟨M, ?_⟩
  intro m n hmM hm h4
  have hbound := p0QCoefficientSquarefullDenCost_le_error_plus_q_correction
    q m n (by exact_mod_cast hq.1) hm h4 (hformal m hm h4 n)
  have hden : 0 < (m : ℝ)^2 := by positivity
  have hdiv := div_le_div_of_nonneg_right hbound (sq_nonneg (m : ℝ))
  have hden0 : (m : ℝ)^2 ≠ 0 := ne_of_gt hden
  rw [add_div] at hdiv
  have hcancel :
      ((1 / 16 : ℝ) * (m : ℝ)^2 * Real.log ((q - 1 : ℕ) : ℝ)) /
        (m : ℝ)^2 =
          (1 / 16 : ℝ) * Real.log ((q - 1 : ℕ) : ℝ) := by
    field_simp [hden0]
  rw [hcancel] at hdiv
  have htail := hM m hmM
  have htail' : p0SquarefullErrorBound (m : ℝ) / (m : ℝ)^2 < ε := by
    simpa [Function.comp_apply] using htail
  linarith

/-- Uniform coefficient statement on the actual P0 sequence.  The index
`n` is quantified after the common threshold, so increasing determinant
degree incurs no extra small-prime factor. -/
theorem p0A2_coeff_squarefull_error_uniform (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℕ, ∀ m n : ℕ, M ≤ m → 0 < m → 4 ∣ m →
      p0SquarefullCoefficientDenCost m n / (m : ℝ) ^ 2 < ε := by
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp
    (p0SquarefullPrimeLayerCost_div_sq_tendsto_zero.eventually_lt_const hε)
  refine ⟨M, ?_⟩
  intro m n hm _hpos h4
  exact (div_le_div_of_nonneg_right
    (p0SquarefullCoefficientDenCost_le_layerCost h4 n) (sq_nonneg _)).trans_lt (hM m hm)

/-- A single actual common denominator, formed from the literal polynomial's
finite support.  This definition makes the absence of a degree factor in the
small-prime budget explicit. -/
def p0A2CoefficientDenominator (m : ℕ) : ℕ :=
  (p0CanonicalPolynomial 2 m).support.lcm
    (fun n => ((p0CanonicalPolynomial 2 m).coeff n).den)

theorem p0A2CoefficientDenominator_pos (m : ℕ) :
    0 < p0A2CoefficientDenominator m := by
  apply Nat.pos_of_ne_zero
  unfold p0A2CoefficientDenominator
  rw [Finset.lcm_ne_zero_iff]
  exact fun n _ => Rat.den_nz _

theorem p0A2CoefficientDenominator_dvd_baseline {m : ℕ} (h4 : 4 ∣ m) :
    p0A2CoefficientDenominator m ∣ (p0DenominatorLcm m) ^ (3 * m) := by
  apply Finset.lcm_dvd
  exact fun n _ => p0A2_coeff_den_dvd_baseline h4 n

theorem p0A2CoefficientDenominator_factorization_le {m p : ℕ}
    (h4 : 4 ∣ m) (hp : p.Prime) :
    (p0A2CoefficientDenominator m).factorization p ≤
      (3 * m) * Nat.log p (p0DenominatorU m) := by
  have hd0 : (p0DenominatorLcm m) ^ (3 * m) ≠ 0 := by
    unfold p0DenominatorLcm denominatorLcm
    apply pow_ne_zero
    rw [Finset.lcm_ne_zero_iff]
    intro s hs
    exact Nat.ne_of_gt ((Finset.mem_Icc.mp hs).1)
  calc
    _ ≤ ((p0DenominatorLcm m) ^ (3 * m)).factorization p :=
      Nat.factorization_le_factorization_of_dvd_right
        (p0A2CoefficientDenominator_dvd_baseline h4)
        (Nat.ne_of_gt (p0A2CoefficientDenominator_pos m)) hd0
    _ = (3 * m) * (p0DenominatorLcm m).factorization p := by
      simp [Nat.factorization_pow, mul_comm]
    _ ≤ _ := Nat.mul_le_mul_left _ (p0DenominatorLcm_factorization_le_log m p hp)

def p0SquarefullDenominatorCost (m : ℕ) : ℝ :=
  ∑ p ∈ p0SquarefullPrimes m,
    ((p0A2CoefficientDenominator m).factorization p : ℝ) * Real.log (p : ℝ)

theorem p0SquarefullDenominatorCost_le_layerCost {m : ℕ} (h4 : 4 ∣ m) :
    p0SquarefullDenominatorCost m ≤ p0SquarefullPrimeLayerCost m := by
  apply Finset.sum_le_sum
  intro p hp
  have hprime := (mem_p0SquarefullPrimes.mp hp).1
  apply mul_le_mul_of_nonneg_right
  · exact_mod_cast p0A2CoefficientDenominator_factorization_le h4 hprime
  · apply Real.log_nonneg
    exact_mod_cast hprime.one_lt.le

/-- The actual common denominator obeys the same vanishing error budget.
The finite support is combined by LCM, so no extra factor of `m` is paid. -/
theorem p0A2_denominator_squarefull_error (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℕ, ∀ m : ℕ, M ≤ m → 0 < m → 4 ∣ m →
      p0SquarefullDenominatorCost m / (m : ℝ) ^ 2 < ε := by
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp
    (p0SquarefullPrimeLayerCost_div_sq_tendsto_zero.eventually_lt_const hε)
  refine ⟨M, ?_⟩
  intro m hm _hpos h4
  exact (div_le_div_of_nonneg_right
    (p0SquarefullDenominatorCost_le_layerCost h4) (sq_nonneg _)).trans_lt (hM m hm)

end

end Li2Lean.P0.Integerization

#print axioms Li2Lean.P0.Integerization.p0A2_coeff_den_factorization_le
#print axioms Li2Lean.P0.Integerization.p0_source_choose_padicVal_le_log
#print axioms Li2Lean.P0.Integerization.p0_source_choose_padicLog_le
#print axioms Li2Lean.P0.Integerization.natLog_mul_realLog_le
#print axioms Li2Lean.P0.Integerization.p0SquarefullCoefficientDenCost_le_layerCost
#print axioms Li2Lean.P0.Integerization.p0SquarefullPrimeLayerCost_le_errorBound
#print axioms Li2Lean.P0.Integerization.p0SquarefullErrorBound_div_sq_tendsto_zero
#print axioms Li2Lean.P0.Integerization.p0SquarefullPrimeLayerCost_div_sq_tendsto_zero
#print axioms Li2Lean.P0.Integerization.p0A2_coeff_squarefull_error_uniform
#print axioms Li2Lean.P0.Integerization.p0A2CoefficientDenominator_factorization_le
#print axioms Li2Lean.P0.Integerization.p0A2_denominator_squarefull_error

namespace Li2Lean.P0.Integerization

noncomputable section

open Li2Lean.P0

/-- Pointwise coefficient witness extracted from the actual q-parameterized
integerizer producer.  This is the coefficient-level bridge consumed by the
small-prime tail: it keeps the formal-divisor credit tied to the same actual
polynomial as . -/
theorem p0QCoefficientDenFactorization_le_of_actual_producer
    {q : ℕ} {hq : Li2Lean.P0.PositiveBase.InRange (q : ℤ)} {rate : ℝ}
    (P : Li2Lean.P0.ActualRationalIntegerizerProducer q hq rate)
    (m : ℕ) (hm : 0 < m) (h4 : 4 ∣ m) (n p : ℕ) (hp : p.Prime) :
    ((p0CanonicalPolynomial (q : ℤ) m).coeff n).den.factorization p ≤
      Int.toNat (max (Li2Lean.P0.formalDivisorCredit q m p) 0) := by
  exact rat_den_factorization_le_toNat_max_of_padic_lower hp
    (Li2Lean.P0.formalDivisorCredit q m p)
    (P.formal_divisor_coeff m hm h4 p hp n)

/-- Rate-form coefficient witness for the actual q-parameterized producer.
The squarefull contribution is bounded with the same q-dependent correction as
for the formal-divisor leaf, so this theorem can feed the generic integerizer
rate assembly without reopening the coefficient proof. -/
theorem p0QCoefficientSquarefullDenCost_rate_bound_of_actual_producer
    {q : ℕ} {hq : Li2Lean.P0.PositiveBase.InRange (q : ℤ)} {rate : ℝ}
    (P : Li2Lean.P0.ActualRationalIntegerizerProducer q hq rate) :
    ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, ∀ m n : ℕ, M ≤ m → 0 < m → 4 ∣ m →
      p0QCoefficientSquarefullDenCost q m n / (m : ℝ)^2 ≤
        (1 / 16 : ℝ) * Real.log ((q - 1 : ℕ) : ℝ) + ε := by
  intro ε hε
  exact p0QCoefficientSquarefullDenCost_rate_bound (q := q) (hq := hq) (by
    intro m hm h4 n p hp
    exact P.formal_divisor_coeff m hm h4 p hp n) ε hε

end

end Li2Lean.P0.Integerization

#print axioms Li2Lean.P0.Integerization.p0QCoefficientDenFactorization_le_of_actual_producer
#print axioms Li2Lean.P0.Integerization.p0QCoefficientSquarefullDenCost_rate_bound_of_actual_producer
#print axioms Li2Lean.P0.Integerization.p0LowPrime_minExponent_rate_bound
namespace Li2Lean.P0.Integerization
noncomputable section
open Filter Topology

/-- Exact prime-log reconstruction on a finite prime set containing every
prime divisor of the fixed base. -/
theorem sum_padicValNat_mul_log_eq_log_of_primeFactors_subset
    (q : ℕ) (hq : q ≠ 0) (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime) (hcover : q.primeFactors ⊆ s) :
    (∑ p ∈ s, (padicValNat p q : ℝ) * Real.log (p : ℝ)) =
      Real.log (q : ℝ) := by
  classical
  have he : (∑ p ∈ q.primeFactors, (padicValNat p q : ℝ) * Real.log (p : ℝ)) =
      ∑ p ∈ s, (padicValNat p q : ℝ) * Real.log (p : ℝ) := by
    apply Finset.sum_subset hcover
    intro p hp hpnot
    have hnot : ¬ p ∣ q := by
      intro hdiv
      exact hpnot (Nat.mem_primeFactors.mpr ⟨hs p hp, hdiv, hq⟩)
    simp [padicValNat.eq_zero_of_not_dvd hnot]
  rw [← he]
  have hprod : (q : ℝ) = ∏ p ∈ q.primeFactors, (p : ℝ) ^ padicValNat p q := by
    have hn : q = ∏ p ∈ q.primeFactors, p ^ padicValNat p q := by
      convert Nat.prod_primeFactors_pow_factorization hq using 1
      apply Finset.prod_congr rfl
      intro p hp
      rw [Nat.factorization_def q (Nat.prime_of_mem_primeFactors hp)]
    exact_mod_cast hn
  rw [hprod, Real.log_prod]
  · apply Finset.sum_congr rfl
    intro p hp
    rw [Real.log_pow]
  · intro p hp
    exact pow_ne_zero _ (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero)

/-- The signed low-prime exponent sum retains the entire q-adic credit.
The only extra finite condition is that the selected primes include all
prime divisors of q. This is automatic eventually for the plan cutoff. -/
theorem p0LowPrime_minExponent_le_signed_credit
    (q m : ℕ) (hq : 2 ≤ q) (hm : 0 < m) (h4 : 4 ∣ m)
    (cutoff : ℕ) (W : ℕ → ℤ)
    (hcover : q.primeFactors ⊆
      (Nat.primesLE cutoff).filter (fun p => p ∈ p0SquarefullPrimes m)) :
    (∑ p ∈ (Nat.primesLE cutoff).filter (fun p => p ∈ p0SquarefullPrimes m),
      ((min (Li2Lean.P0.formalDivisorCredit q m p) (W p) : ℤ) : ℝ) * Real.log p) ≤
      p0SquarefullPrimeLayerCost m +
        (Int.toNat (max (Li2Lean.P0.formalDivisorH m) 0) : ℝ) *
          Real.log ((q - 1 : ℕ) : ℝ) -
        (Li2Lean.P0.formalDivisorN m : ℝ) * Real.log (q : ℝ) := by
  classical
  let s := (Nat.primesLE cutoff).filter (fun p => p ∈ p0SquarefullPrimes m)
  let H : ℝ := (Int.toNat (max (Li2Lean.P0.formalDivisorH m) 0) : ℝ)
  have hsub : s ⊆ p0SquarefullPrimes m := fun p hp => (Finset.mem_filter.mp hp).2
  have hpr : ∀ p ∈ s, p.Prime := fun p hp => (mem_p0SquarefullPrimes.mp (hsub hp)).1
  have hH : (Li2Lean.P0.formalDivisorH m : ℝ) ≤ H := by
    dsimp [H]
    have hc := Int.toNat_of_nonneg (le_max_right (Li2Lean.P0.formalDivisorH m) 0)
    exact_mod_cast (show Li2Lean.P0.formalDivisorH m ≤
      (Int.toNat (max (Li2Lean.P0.formalDivisorH m) 0) : ℤ) by
        rw [hc]; exact le_max_left _ _)
  have hpoint : ∀ p ∈ s,
      ((min (Li2Lean.P0.formalDivisorCredit q m p) (W p) : ℤ) : ℝ) * Real.log p ≤
      (((3 * m * Nat.log p (p0DenominatorU m) : ℕ) : ℝ) +
        H * (padicValNat p (q-1) : ℝ) -
        (Li2Lean.P0.formalDivisorN m : ℝ) * (padicValNat p q : ℝ)) * Real.log p := by
    intro p hp
    have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast (hpr p hp).one_lt.le)
    apply mul_le_mul_of_nonneg_right _ hlog
    have hh := mul_le_mul_of_nonneg_right hH (Nat.cast_nonneg (padicValNat p (q-1)))
    have hmin : ((min (Li2Lean.P0.formalDivisorCredit q m p) (W p) : ℤ) : ℝ) ≤
        (Li2Lean.P0.formalDivisorCredit q m p : ℝ) := by exact_mod_cast min_le_left (Li2Lean.P0.formalDivisorCredit q m p) (W p)
    have hcreditR : (Li2Lean.P0.formalDivisorCredit q m p : ℝ) =
        ((3 * m * Nat.log p (p0DenominatorU m) : ℕ) : ℝ) +
        (Li2Lean.P0.formalDivisorH m : ℝ) * (padicValNat p (q-1) : ℝ) -
        (Li2Lean.P0.formalDivisorN m : ℝ) * (padicValNat p q : ℝ) := by
      simp only [Li2Lean.P0.formalDivisorCredit, Int.cast_sub, Int.cast_add,
        Int.cast_mul, Int.cast_natCast]
      rfl
    rw [hcreditR] at hmin
    linarith
  have hbase : (∑ p ∈ s, ((3 * m * Nat.log p (p0DenominatorU m) : ℕ) : ℝ) * Real.log p) ≤
      p0SquarefullPrimeLayerCost m := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro p hp _
    exact mul_nonneg (Nat.cast_nonneg _)
      (Real.log_nonneg (by exact_mod_cast (mem_p0SquarefullPrimes.mp hp).1.one_lt.le))
  have hminus : (∑ p ∈ s, (padicValNat p (q-1) : ℝ) * Real.log p) ≤
      Real.log ((q-1:ℕ) : ℝ) := by
    apply le_trans (b := p0FormalExceptionalSquarefullCost q m)
    · apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro p hp _
      exact mul_nonneg (Nat.cast_nonneg _)
        (Real.log_nonneg (by exact_mod_cast (mem_p0SquarefullPrimes.mp hp).1.one_lt.le))
    · exact p0FormalExceptionalSquarefullCost_le_log q m hq
  have hqsum := sum_padicValNat_mul_log_eq_log_of_primeFactors_subset q (by omega) s hpr hcover
  have hmain := Finset.sum_le_sum hpoint
  simp_rw [sub_mul, add_mul, mul_assoc] at hmain
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, hqsum] at hmain
  have hHmul := mul_le_mul_of_nonneg_left hminus (show 0 ≤ H by dsimp [H]; positivity)
  simp only [← Nat.mul_assoc] at hmain
  dsimp [H] at *
  change (∑ p ∈ s,
    ((min (Li2Lean.P0.formalDivisorCredit q m p) (W p) : ℤ) : ℝ) * Real.log p) ≤ _
  linarith


/-- The fixed exceptional primes of q enter the squarefull range once m ≥ q².
This follows solely from the actual cutoff U=2m−1. -/
theorem p0LowPrime_primeFactors_subset
    (q m cutoff : ℕ) (hm : 0 < m) (hqm : q^2 ≤ m)
    (hcutoff : Li2Lean.P0.formalDivisorCutoff m ≤ cutoff) :
    q.primeFactors ⊆ (Nat.primesLE cutoff).filter
      (fun p => p ∈ p0SquarefullPrimes m) := by
  intro p hp
  have hpf := Nat.mem_primeFactors.mp hp
  have hpq : p ≤ q := Nat.le_of_dvd (Nat.pos_of_ne_zero hpf.2.2) hpf.2.1
  have hq2 : q ≤ q^2 := by simpa [pow_two] using Nat.le_mul_self q
  have hpm : p ≤ m := hpq.trans (hq2.trans hqm)
  have hmU : m ≤ p0DenominatorU m := by unfold p0DenominatorU; omega
  apply Finset.mem_filter.mpr
  constructor
  · apply Nat.mem_primesLE.mpr
    exact ⟨hpm.trans (hmU.trans hcutoff), hpf.1⟩
  · apply mem_p0SquarefullPrimes.mpr
    exact ⟨hpf.1, (Nat.pow_le_pow_left hpq 2).trans
      (hqm.trans (hmU.trans (Nat.le_add_right _ _)))⟩

/-- Exact cast of the signed q-adic credit (v13 p0-arithmetic.tex:13–18). -/
theorem p0FormalDivisorN_cast (m : ℕ) (hm : 0 < m) (h4 : 4 ∣ m) :
    (Li2Lean.P0.formalDivisorN m : ℝ) =
      (13/16 : ℝ) * (m : ℝ)^2 - m := by
  obtain ⟨h, rfl⟩ := h4
  have hh : 0 < h := by omega
  have hn : 4*h ≤ 13*h^2 := by nlinarith [Nat.le_mul_self h]
  simp only [Li2Lean.P0.formalDivisorN,
    Nat.mul_div_cancel_left _ (by decide : 0 < 4)]
  rw [Nat.cast_sub hn]
  push_cast
  ring

/-- Normalized finite estimate retaining the full fixed-base gain. Only the
squarefull error and log(q)/m remain for the asymptotic assembly. -/
theorem p0LowPrime_minExponent_signed_normalized
    (q m : ℕ) (hq : 2 ≤ q) (hm : 0 < m) (h4 : 4 ∣ m)
    (cutoff : ℕ) (W : ℕ → ℤ)
    (hcover : q.primeFactors ⊆
      (Nat.primesLE cutoff).filter (fun p => p ∈ p0SquarefullPrimes m)) :
    (∑ p ∈ (Nat.primesLE cutoff).filter (fun p => p ∈ p0SquarefullPrimes m),
      ((min (Li2Lean.P0.formalDivisorCredit q m p) (W p) : ℤ) : ℝ) * Real.log p) /
        (m : ℝ)^2 ≤ p0SquarefullPrimeLayerCost m / (m : ℝ)^2 +
          (1/16 : ℝ) * Real.log ((q-1:ℕ) : ℝ) -
          (13/16 : ℝ) * Real.log (q : ℝ) + Real.log (q : ℝ) / m := by
  have h := p0LowPrime_minExponent_le_signed_credit q m hq hm h4 cutoff W hcover
  have hlog : 0 ≤ Real.log ((q-1:ℕ) : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ q-1))
  have hH := mul_le_mul_of_nonneg_right (formalDivisorH_toNat_max_le h4) hlog
  rw [p0FormalDivisorN_cast m hm h4] at h
  have hb : (∑ p ∈ (Nat.primesLE cutoff).filter (fun p => p ∈ p0SquarefullPrimes m),
      ((min (Li2Lean.P0.formalDivisorCredit q m p) (W p) : ℤ) : ℝ) * Real.log p) ≤
      p0SquarefullPrimeLayerCost m + (m : ℝ)^2/16 * Real.log ((q-1:ℕ) : ℝ) -
        ((13/16 : ℝ) * (m : ℝ)^2 - m) * Real.log (q : ℝ) := by linarith
  have hd := div_le_div_of_nonneg_right hb (sq_nonneg (m : ℝ))
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have he : (p0SquarefullPrimeLayerCost m + (m : ℝ)^2/16 * Real.log ((q-1:ℕ) : ℝ) -
      ((13/16 : ℝ) * (m : ℝ)^2 - m) * Real.log (q : ℝ)) / (m : ℝ)^2 =
      p0SquarefullPrimeLayerCost m / (m : ℝ)^2 +
        (1/16 : ℝ) * Real.log ((q-1:ℕ) : ℝ) -
        (13/16 : ℝ) * Real.log (q : ℝ) + Real.log (q : ℝ) / m := by
    field_simp
    <;> ring
  exact hd.trans_eq he


/-- The signed low-prime rate in the actual minimum-exponent plan. The
threshold is uniform in all moving exponents and all admissible cutoffs.
Unlike the positive-part estimate, this retains −13 log(q)/16 (v13
p0-arithmetic.tex:326–421). -/
theorem p0LowPrime_minExponent_signed_rate_bound
    (q : ℕ) (hq : 2 ≤ q) (cutoff : ℕ → ℕ)
    (hcutoff : ∀ m, 0 < m → 4 ∣ m →
      Li2Lean.P0.formalDivisorCutoff m ≤ cutoff m)
    (W : ℕ → ℕ → ℤ) :
    ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, ∀ m : ℕ, M ≤ m → 0 < m → 4 ∣ m →
      (∑ p ∈ (Nat.primesLE (cutoff m)).filter (fun p => p ∈ p0SquarefullPrimes m),
        ((min (Li2Lean.P0.formalDivisorCredit q m p) (W m p) : ℤ) : ℝ) * Real.log p) /
          (m : ℝ)^2 ≤ (1/16 : ℝ) * Real.log ((q-1:ℕ) : ℝ) -
          (13/16 : ℝ) * Real.log (q : ℝ) + ε := by
  intro ε hε
  have hi : Tendsto (fun m : ℕ => Real.log (q : ℝ) / (m : ℝ))
      atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_def] using
      (tendsto_const_nhds.mul
        (tendsto_inv_atTop_zero.comp
          (tendsto_natCast_atTop_atTop : Tendsto (fun m : ℕ => (m : ℝ)) atTop atTop)))
  have hv : Tendsto (fun m : ℕ => p0SquarefullPrimeLayerCost m / (m : ℝ)^2 +
      Real.log (q : ℝ) / (m : ℝ)) atTop (𝓝 0) := by
    simpa using p0SquarefullPrimeLayerCost_div_sq_tendsto_zero.add hi
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp (hv.eventually_lt_const hε)
  refine ⟨max M (q^2), ?_⟩
  intro m hmM hm h4
  have hcover := p0LowPrime_primeFactors_subset q m (cutoff m) hm
    ((le_max_right M (q^2)).trans hmM) (hcutoff m hm h4)
  have hb := p0LowPrime_minExponent_signed_normalized q m hq hm h4
    (cutoff m) (W m) hcover
  have he := hM m ((le_max_left M (q^2)).trans hmM)
  linarith

end
end Li2Lean.P0.Integerization
#print axioms Li2Lean.P0.Integerization.p0LowPrime_minExponent_signed_rate_bound
