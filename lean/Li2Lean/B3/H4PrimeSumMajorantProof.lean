/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

H4 leaf L3b: the six-prime-class majorant `v13H4_prime_sum_majorant`, the
`hmajor` input of `qv13PrimeSumRate_of_budget` (H4RateBudgetBridge.lean).

This release module supplies `v13H4_prime_sum_majorant`; the H4 assembly imports
it directly and uses the same statement.

Statement status: the statement pinned in the the L6 statement is TRUE as written and
needs no change.  It holds for every `n ≥ 1` (the proof uses only `0 < n`),
not just eventually.  Exact mirror: the finite-data check.

Classes (first match, `p` prime, `p ≤ vU n = 11n - 1`, `m = 4n`,
`ρ = p / m`, `L = log (11 n)`, `E = v13H4Exponent q n p`):
  0 exceptional  `p ∣ q (q+1)`:
      `Σ E log p ≤ 3·13nL - (53/3) n² log q + (4n+1) log 7`
  1 squarefull   `p² ≤ vU n`:          `Σ ≤ 13nL (√(11n) + 1)`
  2 strip        `10 p ≤ n`:           `Σ ≤ 13n θ(n/10)`
  5 outer        `5n < p`:             `E = q5OuterCost n p = m P(ρ)`
  4 slab         residue regime:       `E = q5ResidueExponent m p ≤ m P(ρ)`
  3 wall         otherwise:            `#class ≤ 413`, `Σ ≤ 413·13nL`
  4 ∪ 5:                               `Σ ≤ m · weightedPrimeSum P m`
The four budgets plus `m · wPS` are exactly `(RHS) · m²`.

Paper: `v-arithmetic.tex:319-421` (ordered assignment, Stieltjes/PNT).
Pattern: `P0/RateFinite.lean` (`p0Rate_finite_profile`, hB/hC/hP blocks).
The module is compiled in the release closure; implementation notes are marked
`-- note:`.
-/

import Li2Lean.B3.H4L5Regimes            -- L5 (merged master module)
import Li2Lean.B3.H4Profile             -- the L2c profile (the H4 profile source)
import Li2Lean.B3.H4PrimeSumMajorant    -- master: partition combinator, `v13H4Err`

namespace Li2Lean.B3

noncomputable section

open scoped BigOperators
open Filter Topology
open Li2Lean.P0.Integerization

/-! ## 0. Elementary facts -/

/-- `(53/48) · 16 = 53/3`: the formal-divisor credit after normalisation. -/
theorem h4_credit_constant : (53 / 48 : ℝ) * 16 = 53 / 3 := by norm_num

/-- `1 + 3 + 413 = 417`: the constant in `v13H4Err`. -/
theorem h4_err_constant : (1 + 3 + 413 : ℕ) = 417 := by norm_num

theorem h4_vN_pos {n : ℕ} (hn : 0 < n) : 0 < V.vN n := by
  dsimp only [V.vN]; omega

theorem h4_vU_pos {n : ℕ} (hn : 0 < n) : 0 < V.vU n := by
  dsimp only [V.vU]; omega

theorem h4_vU_ge_ten {n : ℕ} (hn : 0 < n) : 10 ≤ V.vU n := by
  dsimp only [V.vU]; omega

theorem h4_vN_le {n : ℕ} : V.vN n ≤ 11 * n := by
  dsimp only [V.vN]; omega

theorem h4_vU_le {n : ℕ} : V.vU n ≤ 11 * n := by
  dsimp only [V.vU]; omega

theorem h4_vN_le_vU {n : ℕ} : V.vN n ≤ V.vU n := by
  dsimp only [V.vN, V.vU]; omega

theorem h4_log_prime_nonneg {p : ℕ} (hp : p.Prime) : 0 ≤ Real.log (p : ℝ) :=
  Real.log_nonneg (by exact_mod_cast hp.one_lt.le)

theorem h4_log_eleven_nonneg {n : ℕ} (hn : 0 < n) :
    0 ≤ Real.log (11 * (n : ℝ)) := by
  apply Real.log_nonneg
  have : (1 : ℝ) ≤ n := by exact_mod_cast hn
  linarith

theorem h4_log_natCast_le {n N : ℕ} (hN : 0 < N) (h : N ≤ 11 * n) :
    Real.log (N : ℝ) ≤ Real.log (11 * (n : ℝ)) := by
  apply Real.log_le_log (by exact_mod_cast hN)
  have h' : ((N : ℕ) : ℝ) ≤ ((11 * n : ℕ) : ℝ) := by exact_mod_cast h
  push_cast at h'
  exact h'

/-- `Nat.log p N · log p ≤ log N` (from `p ^ Nat.log p N ≤ N`). -/
theorem h4_natLog_mul_log_le {p N : ℕ} (hp : 1 < p) (hN : N ≠ 0) :
    (Nat.log p N : ℝ) * Real.log p ≤ Real.log N := by
  have h := Nat.pow_log_le_self p hN
  have h' : (p : ℝ) ^ (Nat.log p N) ≤ (N : ℝ) := by exact_mod_cast h
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (lt_trans Nat.zero_lt_one hp)
  rw [← Real.log_pow]
  exact Real.log_le_log (pow_pos hp0 _) h'

/-! ## 1. Baseline and exceptional exponents -/

theorem v13BaselineExponent_cast (n p : ℕ) :
    (v13BaselineExponent n p : ℝ) =
      12 * (n : ℝ) * (Nat.log p (V.vN n) : ℝ) +
        (n : ℝ) * (Nat.log p (V.vU n) : ℝ) := by
  unfold v13BaselineExponent
  push_cast
  ring

/-- Every baseline term costs at most `13 n log (11 n)`. -/
theorem v13Baseline_mul_log_le {n p : ℕ} (hn : 0 < n) (hp : p.Prime) :
    (v13BaselineExponent n p : ℝ) * Real.log p ≤
      13 * (n : ℝ) * Real.log (11 * (n : ℝ)) := by
  have h1 := (h4_natLog_mul_log_le hp.one_lt (Nat.pos_iff_ne_zero.1 (h4_vN_pos hn))).trans
    (h4_log_natCast_le (h4_vN_pos hn) h4_vN_le)
  have h2 := (h4_natLog_mul_log_le hp.one_lt (Nat.pos_iff_ne_zero.1 (h4_vU_pos hn))).trans
    (h4_log_natCast_le (h4_vU_pos hn) h4_vU_le)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [v13BaselineExponent_cast]
  nlinarith [mul_le_mul_of_nonneg_left h1 hn0, mul_le_mul_of_nonneg_left h2 hn0]

/-- Above the square-root cutoff both `Nat.log` terms are `≤ 1`, so the
baseline is at most `13 n`.  (No primality needed.) -/
theorem v13Baseline_le_of_sq_gt {n p : ℕ} (hn : 0 < n) (hsq : V.vU n < p ^ 2) :
    (v13BaselineExponent n p : ℝ) ≤ 13 * (n : ℝ) := by
  have ha : Nat.log p (V.vN n) ≤ 1 := by
    have := Nat.log_lt_of_lt_pow (Nat.pos_iff_ne_zero.1 (h4_vN_pos hn))
      (lt_of_le_of_lt h4_vN_le_vU hsq)
    omega
  have hb : Nat.log p (V.vU n) ≤ 1 := by
    have := Nat.log_lt_of_lt_pow (Nat.pos_iff_ne_zero.1 (h4_vU_pos hn)) hsq
    omega
  have ha' : (Nat.log p (V.vN n) : ℝ) ≤ 1 := by exact_mod_cast ha
  have hb' : (Nat.log p (V.vU n) : ℝ) ≤ 1 := by exact_mod_cast hb
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [v13BaselineExponent_cast]
  nlinarith [mul_le_mul_of_nonneg_left ha' hn0, mul_le_mul_of_nonneg_left hb' hn0]

/-- The q-credit multiplier of `v13ExceptionalExponent` (truncated ℕ). -/
def v13H4Credit (n : ℕ) : ℕ := (53 * n ^ 2 + 2) / 3 - 4 * n

/-- `53 n² ≤ 3 (credit n + 4 n)`; checked for `n ≤ 10^5` in N2. -/
theorem v13H4Credit_lower (n : ℕ) :
    (53 / 3 : ℝ) * (n : ℝ) ^ 2 - 4 * n ≤ (v13H4Credit n : ℝ) := by
  have h : 53 * n ^ 2 ≤ 3 * (v13H4Credit n + 4 * n) := by
    unfold v13H4Credit
    generalize n ^ 2 = t
    omega
  have h' : (53 : ℝ) * (n : ℝ) ^ 2 ≤ 3 * ((v13H4Credit n : ℝ) + 4 * n) := by
    exact_mod_cast h
  linarith

/-- Drop the (nonnegative) `q + 1` credit. -/
theorem v13ExceptionalExponent_cast_le (q n p : ℕ) :
    (v13ExceptionalExponent q n p : ℝ) ≤
      (v13BaselineExponent n p : ℝ) - (padicValNat p q : ℝ) * (v13H4Credit n : ℝ) := by
  have h : v13ExceptionalExponent q n p =
      v13BaselineExponent n p - (padicValNat p q : ℤ) * (v13H4Credit n : ℤ) -
        ((4 * n * padicValNat p (q + 1) : ℕ) : ℤ) := rfl
  rw [h]
  push_cast
  norm_num [padicValRat.of_nat]
  have : (0 : ℝ) ≤ 4 * (n : ℝ) * (padicValNat p (q + 1) : ℝ) := by positivity
  have hrat : (0 : ℝ) ≤ 4 * (n : ℝ) *
      (padicValRat p ((q : ℚ) + 1) : ℝ) := by
    have hq1 : (q : ℚ) + 1 = ((q + 1 : ℕ) : ℚ) := by norm_num
    rw [hq1, padicValRat.of_nat]
    positivity
  linarith

/-- `Σ_{p ∈ S} v_p(q) log p = log q` whenever `S ⊇ primeFactors q` consists of
primes. -/
theorem h4_sum_padicValNat_log {q : ℕ} (hq0 : q ≠ 0) {S : Finset ℕ}
    (hS : q.primeFactors ⊆ S) (hSp : ∀ p ∈ S, p.Prime) :
    ∑ p ∈ S, (padicValNat p q : ℝ) * Real.log p = Real.log q := by
  -- note: `Finsupp.sum` unfolds to `∑ a ∈ f.support, g a (f a)`;
  -- `Nat.support_factorization` is `rfl`-simp.
  rw [Real.log_nat_eq_sum_factorization, Finsupp.sum, Nat.support_factorization]
  calc ∑ p ∈ S, (padicValNat p q : ℝ) * Real.log p
      = ∑ p ∈ q.primeFactors, (padicValNat p q : ℝ) * Real.log p := by
        symm
        refine Finset.sum_subset hS (fun p hpS hpq => ?_)
        have hnd : ¬ p ∣ q := fun hd => hpq (Nat.mem_primeFactors.2 ⟨hSp p hpS, hd, hq0⟩)
        simp [padicValNat.eq_zero_of_not_dvd hnd]
    _ = ∑ p ∈ q.primeFactors, (q.factorization p : ℝ) * Real.log p := by
        refine Finset.sum_congr rfl (fun p hp => ?_)
        rw [Nat.factorization_def q (Nat.prime_of_mem_primeFactors hp)]

/-! ## 2. The exponent on each regime -/

theorem v13H4Exponent_of_dvd {q n p : ℕ} (hn : 0 < n) (hd : p ∣ q * (q + 1)) :
    v13H4Exponent q n p = v13ExceptionalExponent q n p := by
  unfold v13H4Exponent v13ThreeRegimeExponent
  simp only [if_neg (Nat.ne_of_gt hn), if_pos hd]

theorem v13H4Exponent_of_residue {q n p : ℕ} (hn : 0 < n) (hd : ¬ p ∣ q * (q + 1))
    (hr : v13H4ResidueRegime n p) :
    v13H4Exponent q n p = v13H4ResidueExponent n p := by
  unfold v13H4Exponent v13ThreeRegimeExponent
  simp only [if_neg (Nat.ne_of_gt hn), if_neg hd, if_pos hr]

theorem v13H4Exponent_of_outer {q n p : ℕ} (hn : 0 < n) (hd : ¬ p ∣ q * (q + 1))
    (hr : ¬ v13H4ResidueRegime n p) (ho : v13H4OuterRegime n p) :
    v13H4Exponent q n p = v13H4OuterExponent n p := by
  unfold v13H4Exponent v13ThreeRegimeExponent
  simp only [if_neg (Nat.ne_of_gt hn), if_neg hd, if_neg hr, if_pos ho]

theorem v13H4Exponent_of_baseline {q n p : ℕ} (hn : 0 < n) (hd : ¬ p ∣ q * (q + 1))
    (hr : ¬ v13H4ResidueRegime n p) (ho : ¬ v13H4OuterRegime n p) :
    v13H4Exponent q n p = v13BaselineExponent n p := by
  unfold v13H4Exponent v13ThreeRegimeExponent
  simp only [if_neg (Nat.ne_of_gt hn), if_neg hd, if_neg hr, if_neg ho]

/-- What the residue regime forces: `vU < p²`, `p ≤ 5 n`, and `n < 10 p`
(the last from `s.lo ≥ 1/40`). -/
theorem v13H4ResidueRegime_facts {n p : ℕ} (h : v13H4ResidueRegime n p) :
    V.vU n < p ^ 2 ∧ p ≤ 5 * n ∧ n < 10 * p := by
  obtain ⟨hmax, h5, s, hs, hlo, -⟩ := h
  refine ⟨lt_of_le_of_lt (le_max_right _ _) hmax, h5, ?_⟩
  have hlo40 : (1 / 40 : ℚ) ≤ s.lo := (H4Slab.ok_parts (v13SlabData_ok s hs)).1
  have hm : (0 : ℚ) ≤ ((4 * n : ℕ) : ℚ) := Nat.cast_nonneg _
  have h1 : (1 / 40 : ℚ) * ((4 * n : ℕ) : ℚ) < p :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right hlo40 hm) hlo
  have h2 : (n : ℚ) < 10 * p := by
    push_cast at h1
    linarith
  exact_mod_cast h2

/-- Below the square-root cutoff the outer regime is impossible. -/
theorem h4_not_outer_of_sq_le {n p : ℕ} (hsq : p ^ 2 ≤ V.vU n) :
    ¬ v13H4OuterRegime n p := by
  rintro ⟨h5, -⟩
  have hU : V.vU n ≤ 11 * n := h4_vU_le
  have h1 : (5 * n + 1) * (5 * n + 1) ≤ p * p := Nat.mul_le_mul h5 h5
  have h2 : p * p = p ^ 2 := (sq p).symm
  have h3 : n ≤ n * n := Nat.le_mul_self n
  nlinarith [h1, h2, h3, hsq, hU, Nat.zero_le (n * n)]

/-! ## 3. The six classes -/

/-- First-match class index (0 exceptional, 1 squarefull, 2 strip, 3 wall,
4 slab, 5 outer). -/
def v13H4Class (q n p : ℕ) : ℕ := by
  classical
  exact if p ∣ q * (q + 1) then 0
    else if p ^ 2 ≤ V.vU n then 1
    else if 10 * p ≤ n then 2
    else if 5 * n < p then 5
    else if v13H4ResidueRegime n p then 4
    else 3

theorem v13H4Class_le (q n p : ℕ) : v13H4Class q n p ≤ 5 := by
  unfold v13H4Class
  split_ifs <;> norm_num

theorem v13H4Class_eq_zero_iff {q n p : ℕ} :
    v13H4Class q n p = 0 ↔ p ∣ q * (q + 1) := by
  constructor
  · intro h
    by_contra h0
    unfold v13H4Class at h
    rw [if_neg h0] at h
    split_ifs at h <;> omega
  · intro h
    unfold v13H4Class
    rw [if_pos h]

theorem v13H4Class_eq_one {q n p : ℕ} (h : v13H4Class q n p = 1) :
    ¬ p ∣ q * (q + 1) ∧ p ^ 2 ≤ V.vU n := by
  unfold v13H4Class at h
  split_ifs at h <;>
    first
    | (exfalso; omega)
    | exact ⟨by assumption, by assumption⟩

theorem v13H4Class_eq_two {q n p : ℕ} (h : v13H4Class q n p = 2) :
    ¬ p ∣ q * (q + 1) ∧ ¬ p ^ 2 ≤ V.vU n ∧ 10 * p ≤ n := by
  unfold v13H4Class at h
  split_ifs at h <;>
    first
    | (exfalso; omega)
    | exact ⟨by assumption, by assumption, by assumption⟩

theorem v13H4Class_eq_three {q n p : ℕ} (h : v13H4Class q n p = 3) :
    ¬ p ∣ q * (q + 1) ∧ ¬ p ^ 2 ≤ V.vU n ∧ ¬ 10 * p ≤ n ∧ ¬ 5 * n < p ∧
      ¬ v13H4ResidueRegime n p := by
  unfold v13H4Class at h
  split_ifs at h <;>
    first
    | (exfalso; omega)
    | exact ⟨by assumption, by assumption, by assumption, by assumption, by assumption⟩

theorem v13H4Class_eq_four {q n p : ℕ} (h : v13H4Class q n p = 4) :
    ¬ p ∣ q * (q + 1) ∧ ¬ 5 * n < p ∧ v13H4ResidueRegime n p := by
  unfold v13H4Class at h
  split_ifs at h <;>
    first
    | (exfalso; omega)
    | exact ⟨by assumption, by assumption, by assumption⟩

theorem v13H4Class_eq_five {q n p : ℕ} (h : v13H4Class q n p = 5) :
    ¬ p ∣ q * (q + 1) ∧ 5 * n < p := by
  unfold v13H4Class at h
  split_ifs at h <;>
    first
    | (exfalso; omega)
    | exact ⟨by assumption, by assumption⟩

def v13H4ClassSet (q n k : ℕ) : Finset ℕ :=
  (Nat.primesLE (V.vU n)).filter (fun p => v13H4Class q n p = k)

theorem mem_v13H4ClassSet {q n k p : ℕ} :
    p ∈ v13H4ClassSet q n k ↔ p ∈ Nat.primesLE (V.vU n) ∧ v13H4Class q n p = k := by
  unfold v13H4ClassSet
  exact Finset.mem_filter

theorem v13H4ClassSet_prime {q n k p : ℕ} (hp : p ∈ v13H4ClassSet q n k) : p.Prime :=
  (Nat.mem_primesLE.1 (mem_v13H4ClassSet.1 hp).1).2

theorem v13H4ClassSet_le {q n k p : ℕ} (hp : p ∈ v13H4ClassSet q n k) : p ≤ V.vU n :=
  (Nat.mem_primesLE.1 (mem_v13H4ClassSet.1 hp).1).1

theorem v13H4ClassSet_disjoint {q n j k : ℕ} (h : j ≠ k) :
    Disjoint (v13H4ClassSet q n j) (v13H4ClassSet q n k) := by
  rw [Finset.disjoint_left]
  intro x hx hy
  exact h ((mem_v13H4ClassSet.1 hx).2.symm.trans (mem_v13H4ClassSet.1 hy).2)

private theorem v13H4_disjoint_of_lt {q n k : ℕ} {s : Finset ℕ}
    (hs : ∀ x ∈ s, v13H4Class q n x < k) : Disjoint s (v13H4ClassSet q n k) := by
  rw [Finset.disjoint_left]
  intro x hx hy
  have h1 := hs x hx
  rw [(mem_v13H4ClassSet.1 hy).2] at h1
  exact lt_irrefl _ h1

private theorem v13H4_lt_union {q n k : ℕ} {s t : Finset ℕ}
    (hs : ∀ x ∈ s, v13H4Class q n x < k) (ht : ∀ x ∈ t, v13H4Class q n x < k) :
    ∀ x ∈ s ∪ t, v13H4Class q n x < k := by
  intro x hx
  rcases Finset.mem_union.1 hx with h | h
  exacts [hs x h, ht x h]

private theorem v13H4_lt_mem {q n j k : ℕ} (hjk : j < k) :
    ∀ x ∈ v13H4ClassSet q n j, v13H4Class q n x < k := by
  intro x hx
  rw [(mem_v13H4ClassSet.1 hx).2]
  exact hjk

/-- The concrete six-class partition of `primesLE (vU n)`. -/
def v13H4Partition (q n : ℕ) : H4SixClassPartition n (Nat.primesLE (V.vU n)) where
  exceptional := v13H4ClassSet q n 0
  squarefull := v13H4ClassSet q n 1
  strip := v13H4ClassSet q n 2
  wall := v13H4ClassSet q n 3
  slab := v13H4ClassSet q n 4
  outer := v13H4ClassSet q n 5
  exceptional_subset := Finset.filter_subset _ _
  squarefull_subset := Finset.filter_subset _ _
  strip_subset := Finset.filter_subset _ _
  wall_subset := Finset.filter_subset _ _
  slab_subset := Finset.filter_subset _ _
  outer_subset := Finset.filter_subset _ _
  disjoint_exceptional_squarefull := v13H4ClassSet_disjoint (by norm_num)
  disjoint_prefix_strip :=
    v13H4_disjoint_of_lt (v13H4_lt_union (v13H4_lt_mem (by norm_num))
      (v13H4_lt_mem (by norm_num)))
  disjoint_prefix_wall :=
    v13H4_disjoint_of_lt (v13H4_lt_union (v13H4_lt_union (v13H4_lt_mem (by norm_num))
      (v13H4_lt_mem (by norm_num))) (v13H4_lt_mem (by norm_num)))
  disjoint_prefix_slab :=
    v13H4_disjoint_of_lt (v13H4_lt_union (v13H4_lt_union (v13H4_lt_union
      (v13H4_lt_mem (by norm_num)) (v13H4_lt_mem (by norm_num)))
      (v13H4_lt_mem (by norm_num))) (v13H4_lt_mem (by norm_num)))
  disjoint_prefix_outer :=
    v13H4_disjoint_of_lt (v13H4_lt_union (v13H4_lt_union (v13H4_lt_union (v13H4_lt_union
      (v13H4_lt_mem (by norm_num)) (v13H4_lt_mem (by norm_num)))
      (v13H4_lt_mem (by norm_num))) (v13H4_lt_mem (by norm_num)))
      (v13H4_lt_mem (by norm_num)))
  cover := by
    ext x
    simp only [Finset.mem_union, mem_v13H4ClassSet]
    constructor
    · rintro (((((h | h) | h) | h) | h) | h) <;> exact h.1
    · intro hx
      have h5 := v13H4Class_le q n x
      generalize v13H4Class q n x = c at h5 ⊢
      interval_cases c <;> simp [hx]

/-! ## 4. Class 0: exceptional primes -/

theorem h4_exc_prime_le {q p : ℕ} (hq : SignedVBaseRange q) (hp : p.Prime)
    (h : p ∣ q * (q + 1)) : p ≤ q + 1 := by
  rcases hq with ⟨hq2, -⟩
  rcases (Nat.Prime.dvd_mul hp).1 h with h1 | h1
  · exact (Nat.le_of_dvd (by omega) h1).trans (Nat.le_succ q)
  · exact Nat.le_of_dvd (by omega) h1

theorem v13H4_exc_subset {q n : ℕ} (hq : SignedVBaseRange q) :
    v13H4ClassSet q n 0 ⊆
      (Finset.range 9).filter (fun p => p.Prime ∧ p ∣ q * (q + 1)) := by
  intro p hp
  have hpr := v13H4ClassSet_prime hp
  have hd := v13H4Class_eq_zero_iff.1 (mem_v13H4ClassSet.1 hp).2
  have hle := h4_exc_prime_le hq hpr hd
  rcases hq with ⟨-, hq7⟩
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨by omega, hpr, hd⟩

/-- At most three exceptional primes (`q(q+1) ∈ {6,12,20,30,42,56}`; check N3). -/
theorem h4_exc_card_aux {q : ℕ} (hq : SignedVBaseRange q) :
    ((Finset.range 9).filter (fun p => p.Prime ∧ p ∣ q * (q + 1))).card ≤ 3 := by
  rcases hq with ⟨h2, h7⟩
  -- note: kernel evaluation of `Nat.decidablePrime` for `p < 9`
  -- (alternative: `decide +kernel`, or `simp [Finset.filter, Nat.Prime]` per case).
  interval_cases q <;> decide +kernel

theorem h4_primeFactors_subset_exc {q n : ℕ} (hq : SignedVBaseRange q) (hn : 0 < n) :
    q.primeFactors ⊆ v13H4ClassSet q n 0 := by
  intro p hp
  obtain ⟨hpr, hdq, -⟩ := Nat.mem_primeFactors.1 hp
  have hle : p ≤ q := Nat.le_of_dvd (by rcases hq with ⟨h2, -⟩; omega) hdq
  have h10 := h4_vU_ge_ten hn
  refine mem_v13H4ClassSet.2 ⟨Nat.mem_primesLE.2 ⟨?_, hpr⟩,
    v13H4Class_eq_zero_iff.2 (Dvd.dvd.mul_right hdq _)⟩
  rcases hq with ⟨-, h7⟩
  omega

theorem v13H4_exceptional_bound {q n : ℕ} (hq : SignedVBaseRange q) (hn : 0 < n) :
    ∑ p ∈ v13H4ClassSet q n 0, (v13H4Exponent q n p : ℝ) * Real.log p ≤
      3 * (13 * (n : ℝ) * Real.log (11 * (n : ℝ))) -
        (53 / 3) * (n : ℝ) ^ 2 * Real.log q + (4 * (n : ℝ) + 1) * Real.log 7 := by
  have hpt : ∀ p ∈ v13H4ClassSet q n 0, (v13H4Exponent q n p : ℝ) * Real.log p ≤
      13 * (n : ℝ) * Real.log (11 * (n : ℝ)) -
        (v13H4Credit n : ℝ) * ((padicValNat p q : ℝ) * Real.log p) := by
    intro p hp
    have hpr := v13H4ClassSet_prime hp
    have hd := v13H4Class_eq_zero_iff.1 (mem_v13H4ClassSet.1 hp).2
    rw [v13H4Exponent_of_dvd hn hd]
    have h1 := mul_le_mul_of_nonneg_right (v13ExceptionalExponent_cast_le q n p)
      (h4_log_prime_nonneg hpr)
    have h2 := v13Baseline_mul_log_le hn hpr
    nlinarith
  have hsum := Finset.sum_le_sum hpt
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum,
    h4_sum_padicValNat_log (by rcases hq with ⟨h2, -⟩; omega)
      (h4_primeFactors_subset_exc hq hn) (fun p hp => v13H4ClassSet_prime hp)] at hsum
  have hcard : ((v13H4ClassSet q n 0).card : ℝ) ≤ 3 := by
    exact_mod_cast (Finset.card_le_card (v13H4_exc_subset hq)).trans (h4_exc_card_aux hq)
  have hL0 := h4_log_eleven_nonneg hn
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hT0 : 0 ≤ 13 * (n : ℝ) * Real.log (11 * (n : ℝ)) := mul_nonneg (by positivity) hL0
  have hK := v13H4Credit_lower n
  obtain ⟨hq2, hq7⟩ := hq
  have hlogq0 : 0 ≤ Real.log (q : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ q))
  have hlogq7 : Real.log (q : ℝ) ≤ Real.log 7 :=
    Real.log_le_log (by exact_mod_cast (by omega : 0 < q)) (by exact_mod_cast hq7)
  have hlog7 : 0 ≤ Real.log (7 : ℝ) := Real.log_nonneg (by norm_num)
  nlinarith [mul_le_mul_of_nonneg_right hcard hT0,
    mul_le_mul_of_nonneg_right hK hlogq0,
    mul_le_mul_of_nonneg_left hlogq7 (by positivity : (0 : ℝ) ≤ 4 * n)]

/-! ## 5. Class 1: `p² ≤ vU n` -/

theorem v13H4_squarefull_bound {q n : ℕ} (hn : 0 < n) :
    ∑ p ∈ v13H4ClassSet q n 1, (v13H4Exponent q n p : ℝ) * Real.log p ≤
      13 * (n : ℝ) * Real.log (11 * (n : ℝ)) * (Real.sqrt (11 * (n : ℝ)) + 1) := by
  have hpt : ∀ p ∈ v13H4ClassSet q n 1, (v13H4Exponent q n p : ℝ) * Real.log p ≤
      13 * (n : ℝ) * Real.log (11 * (n : ℝ)) := by
    intro p hp
    have hpr := v13H4ClassSet_prime hp
    obtain ⟨hd, hsq⟩ := v13H4Class_eq_one (mem_v13H4ClassSet.1 hp).2
    have hr : ¬ v13H4ResidueRegime n p := fun h =>
      absurd (v13H4ResidueRegime_facts h).1 (not_lt.2 hsq)
    rw [v13H4Exponent_of_baseline hn hd hr (h4_not_outer_of_sq_le hsq)]
    exact v13Baseline_mul_log_le hn hpr
  have hcard : ((v13H4ClassSet q n 1).card : ℝ) ≤ Real.sqrt (11 * (n : ℝ)) + 1 := by
    have hsub : v13H4ClassSet q n 1 ⊆ Finset.range (Nat.sqrt (V.vU n) + 1) := by
      intro p hp
      have hsq := (v13H4Class_eq_one (mem_v13H4ClassSet.1 hp).2).2
      exact Finset.mem_range.2 (Nat.lt_succ_of_le (Nat.le_sqrt'.2 hsq))
    have h1 : ((v13H4ClassSet q n 1).card : ℝ) ≤ (Nat.sqrt (V.vU n) : ℝ) + 1 := by
      have := Finset.card_le_card hsub
      rw [Finset.card_range] at this
      exact_mod_cast this
    have hU : ((V.vU n : ℕ) : ℝ) ≤ 11 * (n : ℝ) := by
      have h' : ((V.vU n : ℕ) : ℝ) ≤ ((11 * n : ℕ) : ℝ) := by exact_mod_cast h4_vU_le
      push_cast at h'
      exact h'
    have h2 : (Nat.sqrt (V.vU n) : ℝ) ≤ Real.sqrt (11 * (n : ℝ)) :=
      Real.nat_sqrt_le_real_sqrt.trans (Real.sqrt_le_sqrt hU)  -- note: explicit/implicit arg
    linarith
  have hT0 : 0 ≤ 13 * (n : ℝ) * Real.log (11 * (n : ℝ)) :=
    mul_nonneg (by positivity) (h4_log_eleven_nonneg hn)
  calc ∑ p ∈ v13H4ClassSet q n 1, (v13H4Exponent q n p : ℝ) * Real.log p
      ≤ (v13H4ClassSet q n 1).card • (13 * (n : ℝ) * Real.log (11 * (n : ℝ))) :=
        Finset.sum_le_card_nsmul _ _ _ hpt
    _ = ((v13H4ClassSet q n 1).card : ℝ) * (13 * (n : ℝ) * Real.log (11 * (n : ℝ))) :=
        nsmul_eq_mul _ _
    _ ≤ (Real.sqrt (11 * (n : ℝ)) + 1) * (13 * (n : ℝ) * Real.log (11 * (n : ℝ))) :=
        mul_le_mul_of_nonneg_right hcard hT0
    _ = 13 * (n : ℝ) * Real.log (11 * (n : ℝ)) * (Real.sqrt (11 * (n : ℝ)) + 1) := by ring

/-! ## 6. Class 2: the strip `10 p ≤ n` (paid by the θ term) -/

theorem v13H4_strip_bound {q n : ℕ} (hn : 0 < n) :
    ∑ p ∈ v13H4ClassSet q n 2, (v13H4Exponent q n p : ℝ) * Real.log p ≤
      13 * (n : ℝ) * Chebyshev.theta ((n : ℝ) / 10) := by
  have hpt : ∀ p ∈ v13H4ClassSet q n 2, (v13H4Exponent q n p : ℝ) * Real.log p ≤
      13 * (n : ℝ) * Real.log p := by
    intro p hp
    have hpr := v13H4ClassSet_prime hp
    obtain ⟨hd, hsq, h10⟩ := v13H4Class_eq_two (mem_v13H4ClassSet.1 hp).2
    have hr : ¬ v13H4ResidueRegime n p := fun h => by
      have := (v13H4ResidueRegime_facts h).2.2
      omega
    have ho : ¬ v13H4OuterRegime n p := fun h => by
      have := h.1
      omega
    rw [v13H4Exponent_of_baseline hn hd hr ho]
    exact mul_le_mul_of_nonneg_right (v13Baseline_le_of_sq_gt hn (not_le.1 hsq))
      (h4_log_prime_nonneg hpr)
  have hsub : v13H4ClassSet q n 2 ⊆ Nat.primesLE ⌊(n : ℝ) / 10⌋₊ := by
    intro p hp
    have hpr := v13H4ClassSet_prime hp
    have h10 := (v13H4Class_eq_two (mem_v13H4ClassSet.1 hp).2).2.2
    refine Nat.mem_primesLE.2 ⟨Nat.le_floor ?_, hpr⟩
    have h' : ((10 * p : ℕ) : ℝ) ≤ n := by exact_mod_cast h10
    push_cast at h'
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 10)]
    linarith
  calc ∑ p ∈ v13H4ClassSet q n 2, (v13H4Exponent q n p : ℝ) * Real.log p
      ≤ ∑ p ∈ v13H4ClassSet q n 2, 13 * (n : ℝ) * Real.log p := Finset.sum_le_sum hpt
    _ = 13 * (n : ℝ) * ∑ p ∈ v13H4ClassSet q n 2, Real.log (p : ℝ) := by
        rw [Finset.mul_sum]
    _ ≤ 13 * (n : ℝ) * ∑ p ∈ Nat.primesLE ⌊(n : ℝ) / 10⌋₊, Real.log (p : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun p hp _ => h4_log_prime_nonneg (Nat.mem_primesLE.1 hp).2)
    _ = 13 * (n : ℝ) * Chebyshev.theta ((n : ℝ) / 10) := by
        rw [Chebyshev.theta_eq_sum_primesLE]

/-! ## 7. Class 3: wall primes (`p / 4n` is a slab end) -/

/-- The 412 right slab ends, plus `5/4` (which is also the last one). -/
def v13H4WallTargets : Finset ℚ := (v13SlabData.map VSlab.hi).toFinset ∪ {5 / 4}

/-- 8 shards of 46 slabs plus one of 44 (spine only, no ℚ arithmetic). -/
theorem v13SlabData_length : v13SlabData.length = 412 := by
  decide +kernel  -- note: alternative `rfl`

theorem v13H4WallTargets_card : v13H4WallTargets.card ≤ 413 := by
  unfold v13H4WallTargets
  calc (((v13SlabData.map VSlab.hi).toFinset ∪ {5 / 4}) : Finset ℚ).card
      ≤ (v13SlabData.map VSlab.hi).toFinset.card + ({5 / 4} : Finset ℚ).card :=
        Finset.card_union_le _ _
    _ ≤ (v13SlabData.map VSlab.hi).length + 1 := by
        rw [Finset.card_singleton]
        exact Nat.add_le_add_right (List.toFinset_card_le _) 1
    _ = 413 := by rw [List.length_map, v13SlabData_length]

/-- A wall prime sits at a slab end: otherwise `vSlabChain_cover` puts it
strictly inside a slab, i.e. in the residue regime. -/
theorem v13H4_wall_maps {q n p : ℕ} (hn : 0 < n) (hp : p ∈ v13H4ClassSet q n 3) :
    (p : ℚ) / ((4 * n : ℕ) : ℚ) ∈ v13H4WallTargets := by
  obtain ⟨hd, hsq, h10, h5, hr⟩ := v13H4Class_eq_three (mem_v13H4ClassSet.1 hp).2
  have hmQ : (0 : ℚ) < ((4 * n : ℕ) : ℚ) := by exact_mod_cast (by omega : 0 < 4 * n)
  have hx1 : (1 : ℚ) / 40 < (p : ℚ) / ((4 * n : ℕ) : ℚ) := by
    rw [lt_div_iff₀ hmQ]
    have h' : (n : ℚ) < 10 * p := by exact_mod_cast (not_le.1 h10)
    push_cast
    linarith
  have hx2 : (p : ℚ) / ((4 * n : ℕ) : ℚ) ≤ 5 / 4 := by
    rw [div_le_iff₀ hmQ]
    have h' : (p : ℚ) ≤ 5 * n := by exact_mod_cast (not_lt.1 h5)
    push_cast
    linarith
  unfold v13H4WallTargets
  rw [Finset.mem_union, Finset.mem_singleton, List.mem_toFinset, List.mem_map]
  by_cases h54 : (p : ℚ) / ((4 * n : ℕ) : ℚ) = 5 / 4
  · exact Or.inr h54
  by_cases hw : ∃ s, s ∈ v13SlabData ∧ s.hi = (p : ℚ) / ((4 * n : ℕ) : ℚ)
  · exact Or.inl hw
  exfalso
  push_neg at hw
  obtain ⟨s, hs, hlo, hhi⟩ := vSlabChain_cover v13SlabData_chain hx1
    (lt_of_le_of_ne hx2 h54) (fun s hs h => hw s hs h.symm)
  apply hr
  refine ⟨max_lt (lt_of_le_of_lt h4_vN_le_vU (not_le.1 hsq)) (not_le.1 hsq),
    not_lt.1 h5, s, hs, ?_, ?_⟩
  · exact (lt_div_iff₀ hmQ).1 hlo
  · exact (div_lt_iff₀ hmQ).1 hhi

theorem v13H4_wall_card {q n : ℕ} (hn : 0 < n) : (v13H4ClassSet q n 3).card ≤ 413 := by
  have hmQ : ((4 * n : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (by omega : 4 * n ≠ 0)
  refine (Finset.card_le_card_of_injOn (fun p : ℕ => (p : ℚ) / ((4 * n : ℕ) : ℚ))
    (by intro p hp; exact v13H4_wall_maps hn hp) ?_).trans v13H4WallTargets_card
  intro a _ b _ hab
  have hab' : (a : ℚ) / ((4 * n : ℕ) : ℚ) = (b : ℚ) / ((4 * n : ℕ) : ℚ) := hab
  exact_mod_cast (div_left_inj' hmQ).1 hab'

theorem v13H4_wall_bound {q n : ℕ} (hn : 0 < n) :
    ∑ p ∈ v13H4ClassSet q n 3, (v13H4Exponent q n p : ℝ) * Real.log p ≤
      413 * (13 * (n : ℝ) * Real.log (11 * (n : ℝ))) := by
  have hpt : ∀ p ∈ v13H4ClassSet q n 3, (v13H4Exponent q n p : ℝ) * Real.log p ≤
      13 * (n : ℝ) * Real.log (11 * (n : ℝ)) := by
    intro p hp
    have hpr := v13H4ClassSet_prime hp
    have hple := v13H4ClassSet_le hp
    obtain ⟨hd, hsq, -, h5, hr⟩ := v13H4Class_eq_three (mem_v13H4ClassSet.1 hp).2
    have ho : ¬ v13H4OuterRegime n p := fun h => h5 h.1
    rw [v13H4Exponent_of_baseline hn hd hr ho]
    have hE := v13Baseline_le_of_sq_gt hn (not_le.1 hsq)
    have hlp : Real.log (p : ℝ) ≤ Real.log (11 * (n : ℝ)) :=
      h4_log_natCast_le hpr.pos (hple.trans h4_vU_le)
    calc (v13BaselineExponent n p : ℝ) * Real.log p ≤ 13 * (n : ℝ) * Real.log p :=
          mul_le_mul_of_nonneg_right hE (h4_log_prime_nonneg hpr)
      _ ≤ 13 * (n : ℝ) * Real.log (11 * (n : ℝ)) :=
          mul_le_mul_of_nonneg_left hlp (by positivity)
  have hcard : ((v13H4ClassSet q n 3).card : ℝ) ≤ 413 := by
    exact_mod_cast v13H4_wall_card hn
  have hT0 : 0 ≤ 13 * (n : ℝ) * Real.log (11 * (n : ℝ)) :=
    mul_nonneg (by positivity) (h4_log_eleven_nonneg hn)
  calc ∑ p ∈ v13H4ClassSet q n 3, (v13H4Exponent q n p : ℝ) * Real.log p
      ≤ (v13H4ClassSet q n 3).card • (13 * (n : ℝ) * Real.log (11 * (n : ℝ))) :=
        Finset.sum_le_card_nsmul _ _ _ hpt
    _ = ((v13H4ClassSet q n 3).card : ℝ) * (13 * (n : ℝ) * Real.log (11 * (n : ℝ))) :=
        nsmul_eq_mul _ _
    _ ≤ 413 * (13 * (n : ℝ) * Real.log (11 * (n : ℝ))) :=
        mul_le_mul_of_nonneg_right hcard hT0

/-! ## 8. Classes 4 and 5: profile pieces -/

/-- Slab class: `E = icpt·4n + slope·p = 4n·(slope ρ + icpt) ≤ 4n·P(ρ)`. -/
theorem v13H4_slab_pointwise {q n p : ℕ} (hn : 0 < n) (hp : p ∈ v13H4ClassSet q n 4) :
    (v13H4Exponent q n p : ℝ) ≤
      4 * (n : ℝ) * v13H4Profile.eval ((p : ℝ) / (4 * (n : ℝ))) := by
  obtain ⟨hd, -, hr⟩ := v13H4Class_eq_four (mem_v13H4ClassSet.1 hp).2
  rw [v13H4Exponent_of_residue hn hd hr]
  obtain ⟨-, -, s, hs, hlo, hhi⟩ := hr
  have hok := v13SlabData_ok s hs
  have heq := VSlab.residueExponent_eq hok hn hlo hhi
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmR : (0 : ℝ) < 4 * (n : ℝ) := by linarith
  have heqR : (v13H4ResidueExponent n p : ℝ) =
      (s.icpt : ℝ) * (4 * (n : ℝ)) + (s.slope : ℝ) * p := by
    unfold v13H4ResidueExponent
    -- note: cast normal form `((z : ℤ) : ℚ) : ℝ` ↦ `(z : ℝ)` under `push_cast`
    have h : (((V.Q5Certificate.q5ResidueExponent (4 * n) p : ℤ) : ℚ) : ℝ) =
        ((s.icpt * ((4 * n : ℕ) : ℚ) + s.slope * p : ℚ) : ℝ) := by rw [heq]
    push_cast at h
    exact h
  have hloR : (s.lo : ℝ) * (4 * (n : ℝ)) < p := by
    have h : ((s.lo * ((4 * n : ℕ) : ℚ) : ℚ) : ℝ) < ((p : ℚ) : ℝ) := Rat.cast_lt.mpr hlo
    push_cast at h
    exact h
  have hhiR : (p : ℝ) < (s.hi : ℝ) * (4 * (n : ℝ)) := by
    have h : ((p : ℚ) : ℝ) < ((s.hi * ((4 * n : ℕ) : ℚ) : ℚ) : ℝ) := Rat.cast_lt.mpr hhi
    push_cast at h
    exact h
  have hρlo : (s.lo : ℝ) ≤ (p : ℝ) / (4 * (n : ℝ)) := le_of_lt ((lt_div_iff₀ hmR).2 hloR)
  have hρhi : (p : ℝ) / (4 * (n : ℝ)) < (s.hi : ℝ) := (div_lt_iff₀ hmR).2 hhiR
  have hmem : vSlabPiece s hok ∈ v13H4Profile.pieces := by
    show vSlabPiece s hok ∈ v13H4SlabPieces ++ [v13H4OuterPiece1, v13H4OuterPiece2]
    -- note: `List.mem_pmap_of_mem` (core, Init/Data/List/Attach.lean:190)
    exact List.mem_append_left _ (List.mem_pmap_of_mem hs)
  have hge : (s.slope : ℝ) * ((p : ℝ) / (4 * (n : ℝ))) + (s.icpt : ℝ) ≤
      v13H4Profile.eval ((p : ℝ) / (4 * (n : ℝ))) :=
    p0Profile_eval_ge v13H4Profile_nonneg hmem hρlo hρhi
  have hn0 : (n : ℝ) ≠ 0 := hnR.ne'
  have hmρ : 4 * (n : ℝ) * ((p : ℝ) / (4 * (n : ℝ))) = p := by
    field_simp
  have hsl : (s.slope : ℝ) * (4 * (n : ℝ) * ((p : ℝ) / (4 * (n : ℝ)))) =
      (s.slope : ℝ) * p := by rw [hmρ]
  rw [heqR]
  have hge4 := mul_le_mul_of_nonneg_left hge hmR.le
  generalize (p : ℝ) / (4 * (n : ℝ)) = x at hge4 hsl ⊢
  nlinarith [hge4, hsl]

/-- Outer class: `E = q5OuterCost n p = 4n·P(ρ)` on the two outer pieces. -/
theorem v13H4_outer_pointwise {q n p : ℕ} (hn : 0 < n) (hp : p ∈ v13H4ClassSet q n 5) :
    (v13H4Exponent q n p : ℝ) ≤
      4 * (n : ℝ) * v13H4Profile.eval ((p : ℝ) / (4 * (n : ℝ))) := by
  have hpU := v13H4ClassSet_le hp
  obtain ⟨hd, h5⟩ := v13H4Class_eq_five (mem_v13H4ClassSet.1 hp).2
  have hr : ¬ v13H4ResidueRegime n p := fun h => by
    have := (v13H4ResidueRegime_facts h).2.1
    omega
  rw [v13H4Exponent_of_outer hn hd hr ⟨h5, hpU⟩]
  unfold v13H4OuterExponent
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmR : (0 : ℝ) < 4 * (n : ℝ) := by linarith
  have hn0 : (n : ℝ) ≠ 0 := hnR.ne'
  have hmρ : 4 * (n : ℝ) * ((p : ℝ) / (4 * (n : ℝ))) = p := by
    field_simp
  have hp11 : p < 11 * n := by
    have := hpU
    dsimp only [V.vU] at this
    omega
  have h5R : 5 * (n : ℝ) < p := by exact_mod_cast h5
  have h11R : (p : ℝ) < 11 * (n : ℝ) := by exact_mod_cast hp11
  by_cases h8 : p < 8 * n
  · rw [V.Q5Certificate.q5_outer_cost_first_band h5 h8]
    have h8R : (p : ℝ) < 8 * (n : ℝ) := by exact_mod_cast h8
    have hmem : v13H4OuterPiece1 ∈ v13H4Profile.pieces := by
      simp [v13H4Profile]
    have hρlo : ((v13H4OuterPiece1.lo : ℚ) : ℝ) ≤ (p : ℝ) / (4 * (n : ℝ)) := by
      show ((5 / 4 : ℚ) : ℝ) ≤ (p : ℝ) / (4 * (n : ℝ))
      rw [le_div_iff₀ hmR]
      push_cast
      linarith
    have hρhi : (p : ℝ) / (4 * (n : ℝ)) < ((v13H4OuterPiece1.hi : ℚ) : ℝ) := by
      show (p : ℝ) / (4 * (n : ℝ)) < ((2 : ℚ) : ℝ)
      rw [div_lt_iff₀ hmR]
      push_cast
      linarith
    have hge : ((-2 : ℚ) : ℝ) * ((p : ℝ) / (4 * (n : ℝ))) + ((19 / 4 : ℚ) : ℝ) ≤
        v13H4Profile.eval ((p : ℝ) / (4 * (n : ℝ))) :=
      p0Profile_eval_ge v13H4Profile_nonneg hmem hρlo hρhi
    push_cast at hge ⊢
    have hge4 := mul_le_mul_of_nonneg_left hge hmR.le
    generalize (p : ℝ) / (4 * (n : ℝ)) = x at hge4 hmρ ⊢
    nlinarith [hge4, hmρ]
  · push_neg at h8
    rw [V.Q5Certificate.q5_outer_cost_second_band h8
      (by simpa [V.Q5Certificate.q5U, V.vU] using hpU)]  -- note: both are `11 * n - 1`
    have hmem : v13H4OuterPiece2 ∈ v13H4Profile.pieces := by
      simp [v13H4Profile]
    have h8R : 8 * (n : ℝ) ≤ p := by exact_mod_cast h8
    have hρlo : ((v13H4OuterPiece2.lo : ℚ) : ℝ) ≤ (p : ℝ) / (4 * (n : ℝ)) := by
      show ((2 : ℚ) : ℝ) ≤ (p : ℝ) / (4 * (n : ℝ))
      rw [le_div_iff₀ hmR]
      push_cast
      linarith
    have hρhi : (p : ℝ) / (4 * (n : ℝ)) < ((v13H4OuterPiece2.hi : ℚ) : ℝ) := by
      show (p : ℝ) / (4 * (n : ℝ)) < ((11 / 4 : ℚ) : ℝ)
      rw [div_lt_iff₀ hmR]
      push_cast
      linarith
    have hge : ((-1 : ℚ) : ℝ) * ((p : ℝ) / (4 * (n : ℝ))) + ((11 / 4 : ℚ) : ℝ) ≤
        v13H4Profile.eval ((p : ℝ) / (4 * (n : ℝ))) :=
      p0Profile_eval_ge v13H4Profile_nonneg hmem hρlo hρhi
    push_cast at hge ⊢
    have hge4 := mul_le_mul_of_nonneg_left hge hmR.le
    generalize (p : ℝ) / (4 * (n : ℝ)) = x at hge4 hmρ ⊢
    nlinarith [hge4, hmρ]

/-- Classes 4 ∪ 5 together: `≤ 4n · weightedPrimeSum P (4n)`
(`p0_partial_le_weightedPrimeSum`, `P ≥ 0`, support in `[1/40, 11/4)`). -/
theorem v13H4_slab_outer_bound {q n : ℕ} (hn : 0 < n) :
    (∑ p ∈ v13H4ClassSet q n 4, (v13H4Exponent q n p : ℝ) * Real.log p) +
      (∑ p ∈ v13H4ClassSet q n 5, (v13H4Exponent q n p : ℝ) * Real.log p) ≤
      4 * (n : ℝ) * weightedPrimeSum v13H4Profile (4 * (n : ℝ)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmR : (0 : ℝ) < 4 * (n : ℝ) := by linarith
  have h4 : ∑ p ∈ v13H4ClassSet q n 4, (v13H4Exponent q n p : ℝ) * Real.log p ≤
      4 * (n : ℝ) * ∑ p ∈ v13H4ClassSet q n 4,
        v13H4Profile.eval ((p : ℝ) / (4 * (n : ℝ))) * Real.log p := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun p hp => ?_)
    have h := mul_le_mul_of_nonneg_right (v13H4_slab_pointwise hn hp)
      (h4_log_prime_nonneg (v13H4ClassSet_prime hp))
    linarith
  have h5 : ∑ p ∈ v13H4ClassSet q n 5, (v13H4Exponent q n p : ℝ) * Real.log p ≤
      4 * (n : ℝ) * ∑ p ∈ v13H4ClassSet q n 5,
        v13H4Profile.eval ((p : ℝ) / (4 * (n : ℝ))) * Real.log p := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun p hp => ?_)
    have h := mul_le_mul_of_nonneg_right (v13H4_outer_pointwise hn hp)
      (h4_log_prime_nonneg (v13H4ClassSet_prime hp))
    linarith
  have hprime : ∀ p ∈ v13H4ClassSet q n 4 ∪ v13H4ClassSet q n 5, p.Prime := by
    intro p hp
    rcases Finset.mem_union.1 hp with h | h
    exacts [v13H4ClassSet_prime h, v13H4ClassSet_prime h]
  have hW := p0_partial_le_weightedPrimeSum v13H4Profile_nonneg (11 / 4)
    v13H4Profile_hi_le hmR (v13H4ClassSet q n 4 ∪ v13H4ClassSet q n 5) hprime
  rw [Finset.sum_union (v13H4ClassSet_disjoint (q := q) (n := n) (j := 4) (k := 5)
    (by norm_num))] at hW
  nlinarith [mul_le_mul_of_nonneg_left hW hmR.le]

/-! ## 9. The majorant -/

/-- Unnormalised six-class bound, valid for every `n ≥ 1`. -/
theorem v13H4_prime_sum_le {q n : ℕ} (hq : SignedVBaseRange q) (hn : 0 < n) :
    ∑ p ∈ Nat.primesLE (V.vU n), (v13H4Exponent q n p : ℝ) * Real.log p ≤
      4 * (n : ℝ) * weightedPrimeSum v13H4Profile (4 * (n : ℝ)) +
        13 * (n : ℝ) * Chebyshev.theta ((n : ℝ) / 10) -
        (53 / 3) * (n : ℝ) ^ 2 * Real.log q +
        (13 * (n : ℝ) * Real.log (11 * (n : ℝ)) *
            (Real.sqrt (11 * (n : ℝ)) + 1 + 3 + 413) +
          (4 * (n : ℝ) + 1) * Real.log 7) := by
  have hsplit :
      ∑ p ∈ Nat.primesLE (V.vU n), (v13H4Exponent q n p : ℝ) * Real.log p ≤
        (3 * (13 * (n : ℝ) * Real.log (11 * (n : ℝ))) -
            (53 / 3) * (n : ℝ) ^ 2 * Real.log q + (4 * (n : ℝ) + 1) * Real.log 7) +
          13 * (n : ℝ) * Real.log (11 * (n : ℝ)) * (Real.sqrt (11 * (n : ℝ)) + 1) +
          13 * (n : ℝ) * Chebyshev.theta ((n : ℝ) / 10) +
          413 * (13 * (n : ℝ) * Real.log (11 * (n : ℝ))) +
          (∑ p ∈ v13H4ClassSet q n 4, (v13H4Exponent q n p : ℝ) * Real.log p) +
          (∑ p ∈ v13H4ClassSet q n 5, (v13H4Exponent q n p : ℝ) * Real.log p) :=
    H4SixClassPartition.sum_le_of_bounds (v13H4Partition q n)
      (f := fun p => (v13H4Exponent q n p : ℝ) * Real.log p)
      (v13H4_exceptional_bound hq hn) (v13H4_squarefull_bound hn)
      (v13H4_strip_bound hn) (v13H4_wall_bound hn) le_rfl le_rfl
  have hso := v13H4_slab_outer_bound (q := q) hn
  nlinarith [hsplit, hso]

theorem v13H4_prime_sum_majorant {q : ℕ} (hq : SignedVBaseRange q) :
    ∀ᶠ n : ℕ in atTop,
      (∑ p ∈ Nat.primesLE (V.vU n), (v13H4Exponent q n p : ℝ) * Real.log p) /
          (((4 * n : ℕ) : ℝ) ^ 2) ≤
        weightedPrimeSum v13H4Profile ((4 * n : ℕ) : ℝ) / ((4 * n : ℕ) : ℝ) +
          13 * (n : ℝ) * Chebyshev.theta ((n : ℝ) / 10) /
            (((4 * n : ℕ) : ℝ) ^ 2) -
          (53 / 48) * Real.log q + v13H4Err n := by
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hcast : ((4 * n : ℕ) : ℝ) = 4 * (n : ℝ) := by push_cast; ring
  rw [hcast]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := hnR.ne'
  have hden : (0 : ℝ) < (4 * (n : ℝ)) ^ 2 := by positivity
  have hS := v13H4_prime_sum_le hq hn
  have hrhs :
      weightedPrimeSum v13H4Profile (4 * (n : ℝ)) / (4 * (n : ℝ)) +
          13 * (n : ℝ) * Chebyshev.theta ((n : ℝ) / 10) / (4 * (n : ℝ)) ^ 2 -
          (53 / 48) * Real.log q + v13H4Err n =
        (4 * (n : ℝ) * weightedPrimeSum v13H4Profile (4 * (n : ℝ)) +
            13 * (n : ℝ) * Chebyshev.theta ((n : ℝ) / 10) -
            (53 / 3) * (n : ℝ) ^ 2 * Real.log q +
            (13 * (n : ℝ) * Real.log (11 * (n : ℝ)) *
                (Real.sqrt (11 * (n : ℝ)) + 1 + 3 + 413) +
              (4 * (n : ℝ) + 1) * Real.log 7)) / (4 * (n : ℝ)) ^ 2 := by
    unfold v13H4Err
    -- note: `field_simp` normal form; the identity is
    -- W/(4n) = 4n W/(4n)^2 and (53/48) log q = (53/3) n^2 log q/(4n)^2.
    field_simp
    ring
  rw [hrhs]
  exact (div_le_div_iff_of_pos_right hden).2 hS

end
end Li2Lean.B3

#print axioms Li2Lean.B3.v13H4_prime_sum_le
#print axioms Li2Lean.B3.v13H4_prime_sum_majorant
