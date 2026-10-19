/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.RateCellCore
import Li2Lean.B3.Q567ArithmeticContracts
import Li2Lean.P0.RateResidueCount

/-!
# H4 slab checker interface

This file freezes the finite arithmetic interface used by the v13 H4
integerizer. The data shards are deliberately kept separate from the
soundness theorem so that each shard can be checked by kernel reduction.

Paper source: `v-arithmetic.tex:222-287`.
-/

namespace Li2Lean.B3

open scoped BigOperators
open Li2Lean.P0.Integerization

structure VSlab where
  lo : ℚ
  hi : ℚ
  A : ℕ
  B : ℕ
  C : ℕ
  D : ℕ
  perm : Fin 5 → Fin 5
  slope : ℚ
  icpt : ℚ
  deriving DecidableEq

namespace VSlab

def thr (s : VSlab) : Fin 5 → RAff :=
  ![⟨1 / 2, -(s.A : ℚ)⟩, ⟨3 / 2, -(s.B : ℚ)⟩,
    ⟨1 / 4, -(s.C : ℚ)⟩, ⟨5 / 2, -(s.D : ℚ)⟩,
    ⟨-1 / 4, (s.C : ℚ) + 1⟩]

def cut (s : VSlab) : Fin 7 → RAff :=
  ![0, s.thr (s.perm 0), s.thr (s.perm 1), s.thr (s.perm 2),
    s.thr (s.perm 3), s.thr (s.perm 4), ⟨0, 1⟩]

def width (s : VSlab) (g : Fin 6) : RAff :=
  s.cut g.succ - s.cut g.castSucc

def above (s : VSlab) (g : Fin 6) (k : Fin 5) : Bool :=
  decide (∃ j : Fin 5, j.val < g.val ∧ s.perm j = k)

def kCnt (s : VSlab) (g : Fin 6) : ℤ :=
  (s.B : ℤ) - s.A +
    (if s.above g 1 then 0 else 1) -
    (if s.above g 0 then 0 else 1)

def lCnt (s : VSlab) (g : Fin 6) : ℤ :=
  (s.D : ℤ) - s.C +
    (if s.above g 3 then 0 else 1) -
    (if s.above g 2 then 0 else 1)

def wCnt (s : VSlab) (g : Fin 6) : ℤ :=
  (s.C : ℤ) + if s.above g 4 then 1 else 0

def sav (s : VSlab) (g : Fin 6) : ℤ :=
  if s.A = 0 ∧ s.above g 0 ∧ s.B = 1 ∧ s.above g 1 ∧
      s.D = 2 ∧ s.above g 3 ∧ s.C = 0 ∧ ¬ s.above g 4 then 1 else 0

def rk (s : VSlab) (g : Fin 6) : ℤ :=
  min (2 * s.kCnt g + s.wCnt g) (s.lCnt g) - s.sav g

def total (s : VSlab) : RAff :=
  ⟨1, 0⟩ + RAff.smul (s.rk 0) (s.width 0) +
    RAff.smul (s.rk 1) (s.width 1) +
    RAff.smul (s.rk 2) (s.width 2) +
    RAff.smul (s.rk 3) (s.width 3) +
    RAff.smul (s.rk 4) (s.width 4) +
    RAff.smul (s.rk 5) (s.width 5)

def ok (s : VSlab) : Bool :=
  decide (1 / 40 ≤ s.lo) && decide (s.lo < s.hi) && decide (s.hi ≤ 5 / 4) &&
  (⟨1 / 2, -(s.A : ℚ)⟩ : RAff).nonnegOn s.lo s.hi &&
  (⟨-1 / 2, (s.A : ℚ) + 1⟩ : RAff).posOpen s.lo s.hi &&
  (⟨3 / 2, -(s.B : ℚ)⟩ : RAff).nonnegOn s.lo s.hi &&
  (⟨-3 / 2, (s.B : ℚ) + 1⟩ : RAff).posOpen s.lo s.hi &&
  (⟨1 / 4, -(s.C : ℚ)⟩ : RAff).nonnegOn s.lo s.hi &&
  (⟨-1 / 4, (s.C : ℚ) + 1⟩ : RAff).posOpen s.lo s.hi &&
  (⟨5 / 2, -(s.D : ℚ)⟩ : RAff).nonnegOn s.lo s.hi &&
  (⟨-5 / 2, (s.D : ℚ) + 1⟩ : RAff).posOpen s.lo s.hi &&
  decide (Function.Injective s.perm) &&
  (List.finRange 6).all (fun g => (s.width g).nonnegOn s.lo s.hi) &&
  decide (s.total = ⟨s.icpt, s.slope⟩) &&
  decide (0 ≤ s.icpt + s.slope * s.lo) &&
  decide (0 ≤ s.icpt + s.slope * s.hi)

end VSlab


/-- `vSlabChain lo hi l`: the slabs of `l` start at `lo`, are consecutive, and end at
`hi`. Strict `s.lo < s.hi` is part of `VSlab.ok`, so it is not repeated here. -/
def vSlabChain : ℚ → ℚ → List VSlab → Bool
  | lo, hi, [] => decide (lo = hi)
  | lo, hi, s :: rest => decide (s.lo = lo) && vSlabChain s.hi hi rest

/- The Boolean chain is only a finite-data predicate; its lemmas below reason
   through `decide_eq_true_eq`, rather than treating a `decide` result as a
   mathematical hypothesis. -/

theorem vSlabChain_append {a b c : ℚ} {l₁ l₂ : List VSlab}
    (h₁ : vSlabChain a b l₁ = true) (h₂ : vSlabChain b c l₂ = true) :
    vSlabChain a c (l₁ ++ l₂) = true := by
  induction l₁ generalizing a with
  | nil =>
    simp only [vSlabChain, decide_eq_true_eq] at h₁
    subst h₁
    simpa using h₂
  | cons s rest ih =>
    simp only [vSlabChain, Bool.and_eq_true, decide_eq_true_eq, List.cons_append] at h₁ ⊢
    exact ⟨h₁.1, ih h₁.2⟩

/-- Coverage: a point strictly inside `(a, b)` that is not a slab end lies strictly
inside some slab. Used by L3b (class B5); the excluded points are the wall class B4. -/
theorem vSlabChain_cover {a b x : ℚ} {l : List VSlab}
    (hc : vSlabChain a b l = true) (hax : a < x) (hxb : x < b)
    (hwall : ∀ s ∈ l, x ≠ s.hi) :
    ∃ s ∈ l, s.lo < x ∧ x < s.hi := by
  induction l generalizing a with
  | nil =>
    simp only [vSlabChain, decide_eq_true_eq] at hc
    subst hc
    exact absurd (hax.trans hxb) (lt_irrefl _)
  | cons s rest ih =>
    simp only [vSlabChain, Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨hs, hr⟩ := hc
    rcases lt_or_ge x s.hi with h | h
    · exact ⟨s, List.mem_cons_self .., by rw [hs]; exact hax, h⟩
    · have h' : s.hi < x :=
        lt_of_le_of_ne h (fun e => hwall s (List.mem_cons_self ..) e.symm)
      obtain ⟨t, ht, h1, h2⟩ :=
        ih hr h' (fun t ht => hwall t (List.mem_cons_of_mem _ ht))
      exact ⟨t, List.mem_cons_of_mem _ ht, h1, h2⟩

open scoped BigOperators
open Finset
open Li2Lean.P0.Integerization

namespace H4Slab

/-! ## Step 6a. Residue counting, independent of the slab -/

/-- Number of `k` with `u + k * p < N` (for `u < p`); equals `p0ResCnt p N u`. -/
def h4Cnt (p N u : ℕ) : ℕ := N / p + if u < N % p then 1 else 0

theorem h4Cnt_eq_p0ResCnt {p N u : ℕ} (hp : 0 < p) (hu : u < p) :
    h4Cnt p N u = p0ResCnt p N u := by
  unfold h4Cnt
  exact (p0ResCnt_eq hp hu).symm

theorem h4Cnt_le (p N u : ℕ) : h4Cnt p N u ≤ N + 1 := by
  unfold h4Cnt
  have := Nat.div_le_self N p
  split_ifs <;> omega

/-- The basic counting equivalence. -/
theorem h4_lt_iff_cnt {p N u k : ℕ} (hp : 0 < p) (hu : u < p) :
    u + k * p < N ↔ k < h4Cnt p N u := by
  have hdm : N / p * p + N % p = N := Nat.div_add_mod' N p
  have hr : N % p < p := Nat.mod_lt N hp
  unfold h4Cnt
  rcases lt_trichotomy k (N / p) with hk | hk | hk
  · have h1 : (k + 1) * p ≤ N / p * p := Nat.mul_le_mul_right p (Nat.succ_le_of_lt hk)
    rw [Nat.add_mul, Nat.one_mul] at h1
    constructor
    · intro _
      split_ifs <;> omega
    · intro _
      omega
  · rw [hk]
    split_ifs with h
    · constructor <;> intro _ <;> omega
    · constructor <;> intro _ <;> omega
  · have h1 : (N / p + 1) * p ≤ k * p := Nat.mul_le_mul_right p (Nat.succ_le_of_lt hk)
    rw [Nat.add_mul, Nat.one_mul] at h1
    constructor
    · intro h
      omega
    · intro h
      split_ifs at h <;> omega
  -- NOTE: omega treats `k * p`, `N / p * p` as atoms; if it refuses a nonlinear atom,
  -- insert `generalize k * p = t at *` and `generalize N / p * p = s at *` first.

theorem h4Cnt_mono {p N N' u : ℕ} (hp : 0 < p) (hu : u < p) (h : N ≤ N') :
    h4Cnt p N u ≤ h4Cnt p N' u := by
  by_contra hc
  push_neg at hc
  have h1 := (h4_lt_iff_cnt (N := N) (k := h4Cnt p N' u) hp hu).mpr hc
  have h2 := (h4_lt_iff_cnt (N := N') (k := h4Cnt p N' u) hp hu).mp (by omega)
  exact lt_irrefl _ h2

theorem h4Cnt_eq_zero_iff {p N u : ℕ} (hp : 0 < p) (hu : u < p) :
    h4Cnt p N u = 0 ↔ N ≤ u := by
  have h0 := h4_lt_iff_cnt (N := N) (k := 0) hp hu
  rw [Nat.zero_mul, Nat.add_zero] at h0
  constructor
  · intro hc
    by_contra hlt
    push_neg at hlt
    have := h0.mp hlt
    omega
  · intro hN
    by_contra hc
    have := h0.mpr (Nat.pos_of_ne_zero hc)
    omega

theorem h4Cnt_eq_one_iff {p N u : ℕ} (hp : 0 < p) (hu : u < p) :
    h4Cnt p N u = 1 ↔ u < N ∧ N ≤ u + p := by
  have h0 := h4_lt_iff_cnt (N := N) (k := 0) hp hu
  have h1 := h4_lt_iff_cnt (N := N) (k := 1) hp hu
  rw [Nat.zero_mul, Nat.add_zero] at h0
  rw [Nat.one_mul] at h1
  constructor
  · intro hc
    refine ⟨h0.mpr (by omega), ?_⟩
    by_contra hlt
    push_neg at hlt
    have := h1.mp hlt
    omega
  · rintro ⟨a, b⟩
    have c0 := h0.mp a
    have c1 : ¬ 1 < h4Cnt p N u := fun hc => by
      have := h1.mpr hc
      omega
    omega

theorem h4Cnt_eq_two_iff {p N u : ℕ} (hp : 0 < p) (hu : u < p) :
    h4Cnt p N u = 2 ↔ u + p < N ∧ N ≤ u + 2 * p := by
  have h1 := h4_lt_iff_cnt (N := N) (k := 1) hp hu
  have h2 := h4_lt_iff_cnt (N := N) (k := 2) hp hu
  rw [Nat.one_mul] at h1
  constructor
  · intro hc
    refine ⟨h1.mpr (by omega), ?_⟩
    by_contra hlt
    push_neg at hlt
    have := h2.mp hlt
    omega
  · rintro ⟨a, b⟩
    have c1 := h1.mp a
    have c2 : ¬ 2 < h4Cnt p N u := fun hc => by
      have := h2.mpr hc
      omega
    omega

theorem h4_ite_lt (u t : ℕ) :
    (if u < t then 1 else 0 : ℕ) = if t ≤ u then 0 else 1 := by
  split_ifs <;> omega

/-! ## Step 6b. Closed forms of the residue blocks for `m = 4n` -/

theorem q5K_four_mul {n p u : ℕ} (hp : 0 < p) (hu : u < p) :
    V.Q5Certificate.q5K (4 * n) p u = Ico (h4Cnt p (2 * n) u) (h4Cnt p (6 * n) u) := by
  ext k
  have h2 := h4_lt_iff_cnt (N := 2 * n) (k := k) hp hu
  have h6 := h4_lt_iff_cnt (N := 6 * n) (k := k) hp hu
  have hle := h4Cnt_le p (6 * n) u
  simp only [V.Q5Certificate.q5K, mem_filter, mem_range, mem_Ico]
  rw [Nat.mul_assoc 2 k p]  -- `2 * k * p = 2 * (k * p)`
  constructor
  · rintro ⟨_, h1, h3⟩
    refine ⟨?_, h6.mp (by omega)⟩
    by_contra hc
    push_neg at hc
    have := h2.mpr hc
    omega
  · rintro ⟨h1, h3⟩
    have a6 := h6.mpr h3
    refine ⟨by omega, ?_, by omega⟩
    by_contra hc
    push_neg at hc
    have := h2.mp (by omega)
    omega

theorem q5L_four_mul {n p u : ℕ} (hp : 0 < p) (hu : u < p) :
    V.Q5Certificate.q5L (4 * n) p u = Ico (h4Cnt p n u) (h4Cnt p (10 * n) u) := by
  ext k
  have h1 := h4_lt_iff_cnt (N := n) (k := k) hp hu
  have h10 := h4_lt_iff_cnt (N := 10 * n) (k := k) hp hu
  have hle := h4Cnt_le p (10 * n) u
  simp only [V.Q5Certificate.q5L, mem_filter, mem_range, mem_Ico]
  rw [Nat.mul_assoc 4 k p]  -- `4 * k * p = 4 * (k * p)`
  constructor
  · rintro ⟨_, a, b⟩
    refine ⟨?_, h10.mp (by omega)⟩
    by_contra hc
    push_neg at hc
    have := h1.mpr hc
    omega
  · rintro ⟨a, b⟩
    have a10 := h10.mpr b
    refine ⟨by omega, ?_, by omega⟩
    by_contra hc
    push_neg at hc
    have := h1.mp (by omega)
    omega

theorem q5W_four_mul {n p u : ℕ} (hp : 0 < p) (hu : u < p) (hp5 : p < 5 * n) :
    V.Q5Certificate.q5W (4 * n) p u = Icc 1 ((u + n) / p) := by
  ext w
  simp only [V.Q5Certificate.q5W, mem_filter, mem_range, mem_Icc]
  rw [Nat.le_div_iff_mul_le hp]
  have hw1 : 1 ≤ w → p ≤ w * p := fun h => Nat.le_mul_of_pos_left p h
  have hw2 : w ≤ w * p := Nat.le_mul_of_pos_right w hp
  constructor
  · rintro ⟨_, a, b, c⟩
    exact ⟨a, by omega⟩
  · rintro ⟨a, b⟩
    have := hw1 a
    exact ⟨by omega, a, by omega, by omega⟩

/-- Card lemmas in terms of the master residue count `p0ResCnt`. -/
theorem q5K_card_four_mul {n p u : ℕ} (hp : 0 < p) (hu : u < p) :
    ((V.Q5Certificate.q5K (4 * n) p u).card : ℤ) =
      (p0ResCnt p (6 * n) u : ℤ) - p0ResCnt p (2 * n) u := by
  rw [q5K_four_mul hp hu, Nat.card_Ico,
    Nat.cast_sub (h4Cnt_mono hp hu (by omega : 2 * n ≤ 6 * n)),
    h4Cnt_eq_p0ResCnt hp hu, h4Cnt_eq_p0ResCnt hp hu]

theorem q5L_card_four_mul {n p u : ℕ} (hp : 0 < p) (hu : u < p) :
    ((V.Q5Certificate.q5L (4 * n) p u).card : ℤ) =
      (p0ResCnt p (10 * n) u : ℤ) - p0ResCnt p n u := by
  rw [q5L_four_mul hp hu, Nat.card_Ico,
    Nat.cast_sub (h4Cnt_mono hp hu (by omega : n ≤ 10 * n)),
    h4Cnt_eq_p0ResCnt hp hu, h4Cnt_eq_p0ResCnt hp hu]

theorem h4_div_add {n p u : ℕ} (hp : 0 < p) (hu : u < p) :
    (u + n) / p = n / p + if p - n % p ≤ u then 1 else 0 := by
  have hdm : n / p * p + n % p = n := Nat.div_add_mod' n p
  have hr : n % p < p := Nat.mod_lt n hp
  have e1 : (n / p + 1) * p = n / p * p + p := by ring
  have e2 : (n / p + 1 + 1) * p = n / p * p + p + p := by ring
  split_ifs with h
  · exact Nat.div_eq_of_lt_le (by rw [e1]; omega) (by rw [e2]; omega)
  · rw [Nat.add_zero]
    exact Nat.div_eq_of_lt_le (by omega) (by rw [e1]; omega)

theorem q5W_card_four_mul {n p u : ℕ} (hp : 0 < p) (hu : u < p) (hp5 : p < 5 * n) :
    (V.Q5Certificate.q5W (4 * n) p u).card = n / p + if p - n % p ≤ u then 1 else 0 := by
  rw [q5W_four_mul hp hu hp5, Nat.card_Icc, Nat.add_sub_cancel, h4_div_add hp hu]

/-! ## Step 7. The rank-one saving in closed form -/

theorem Ico_eq_singleton_zero_iff {a b : ℕ} : Ico a b = {0} ↔ a = 0 ∧ b = 1 := by
  constructor
  · intro h
    have h0 : (0 : ℕ) ∈ Ico a b := by rw [h]; exact mem_singleton_self 0
    have hc : (Ico a b).card = 1 := by rw [h]; rfl
    rw [Nat.card_Ico] at hc
    rw [mem_Ico] at h0
    omega
  · rintro ⟨rfl, rfl⟩
    decide +kernel

theorem Ico_eq_pair_zero_one_iff {a b : ℕ} : Ico a b = {0, 1} ↔ a = 0 ∧ b = 2 := by
  constructor
  · intro h
    have h0 : (0 : ℕ) ∈ Ico a b := by rw [h]; simp
    have hc : (Ico a b).card = 2 := by rw [h]; rfl
    rw [Nat.card_Ico] at hc
    rw [mem_Ico] at h0
    omega
  · rintro ⟨rfl, rfl⟩
    decide +kernel

theorem q5RankSaving_four_mul {n p u : ℕ} (hp : 0 < p) (hu : u < p) (hp5 : p < 5 * n) :
    V.Q5Certificate.q5RankSaving (4 * n) p u =
      if 2 * n ≤ u ∧ 6 * n ≤ u + p ∧ 10 * n ≤ u + 2 * p ∧ u + n < p then 1 else 0 := by
  unfold V.Q5Certificate.q5RankSaving
  rw [q5K_four_mul hp hu, q5L_four_mul hp hu, q5W_four_mul hp hu hp5]
  have key :
      (Ico (h4Cnt p (2 * n) u) (h4Cnt p (6 * n) u) = {0} ∧
        Ico (h4Cnt p n u) (h4Cnt p (10 * n) u) = {0, 1} ∧
        Icc 1 ((u + n) / p) = ∅) ↔
      (2 * n ≤ u ∧ 6 * n ≤ u + p ∧ 10 * n ≤ u + 2 * p ∧ u + n < p) := by
    rw [Ico_eq_singleton_zero_iff, Ico_eq_pair_zero_one_iff, Finset.Icc_eq_empty_iff,
      Nat.le_div_iff_mul_le hp, h4Cnt_eq_zero_iff hp hu, h4Cnt_eq_one_iff hp hu,
      h4Cnt_eq_zero_iff hp hu, h4Cnt_eq_two_iff hp hu]
    constructor
    · rintro ⟨⟨a, -, b⟩, ⟨-, -, c⟩, d⟩
      exact ⟨a, b, c, by omega⟩
    · rintro ⟨a, b, c, d⟩
      exact ⟨⟨a, by omega, b⟩, ⟨by omega, by omega, c⟩, by omega⟩
  by_cases h : 2 * n ≤ u ∧ 6 * n ≤ u + p ∧ 10 * n ≤ u + 2 * p ∧ u + n < p
  · rw [if_pos (key.mpr h), if_pos h]
  · rw [if_neg (fun h' => h (key.mp h')), if_neg h]

/-! ## Floor/bit translations of the four saving conditions -/

theorem h4_le_iff_K1 {n p u A : ℕ} (hp : 0 < p) (hu : u < p) (hA : 2 * n / p = A) :
    2 * n ≤ u ↔ A = 0 ∧ 2 * n % p ≤ u := by
  have hdm : 2 * n / p * p + 2 * n % p = 2 * n := Nat.div_add_mod' (2 * n) p
  constructor
  · intro h
    have h0 : 2 * n / p = 0 := Nat.div_eq_of_lt (by omega)
    refine ⟨by rw [← hA]; exact h0, ?_⟩
    rw [h0] at hdm
    omega
  · rintro ⟨h1, h2⟩
    rw [hA, h1] at hdm
    omega

theorem h4_le_iff_K2 {n p u B : ℕ} (hp : 0 < p) (hu : u < p) (hp6 : p ≤ 6 * n)
    (hB : 6 * n / p = B) :
    6 * n ≤ u + p ↔ B = 1 ∧ 6 * n % p ≤ u := by
  have hdm : 6 * n / p * p + 6 * n % p = 6 * n := Nat.div_add_mod' (6 * n) p
  constructor
  · intro h
    have h1 : 6 * n / p = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
    refine ⟨by rw [← hB]; exact h1, ?_⟩
    rw [h1] at hdm
    omega
  · rintro ⟨h1, h2⟩
    rw [hB, h1] at hdm
    omega

theorem h4_le_iff_L2 {n p u D : ℕ} (hp : 0 < p) (hu : u < p) (hp2 : 2 * p ≤ 10 * n)
    (hD : 10 * n / p = D) :
    10 * n ≤ u + 2 * p ↔ D = 2 ∧ 10 * n % p ≤ u := by
  have hdm : 10 * n / p * p + 10 * n % p = 10 * n := Nat.div_add_mod' (10 * n) p
  constructor
  · intro h
    have h1 : 10 * n / p = 2 := Nat.div_eq_of_lt_le (by omega) (by omega)
    refine ⟨by rw [← hD]; exact h1, ?_⟩
    rw [h1] at hdm
    omega
  · rintro ⟨h1, h2⟩
    rw [hD, h1] at hdm
    omega

theorem h4_lt_iff_W {n p u C : ℕ} (hp : 0 < p) (hu : u < p) (hC : n / p = C) :
    u + n < p ↔ C = 0 ∧ ¬ (p - n % p ≤ u) := by
  have hdm : n / p * p + n % p = n := Nat.div_add_mod' n p
  constructor
  · intro h
    have h0 : n / p = 0 := Nat.div_eq_of_lt (by omega)
    refine ⟨by rw [← hC]; exact h0, ?_⟩
    rw [h0] at hdm
    omega
  · rintro ⟨h1, h2⟩
    rw [hC, h1] at hdm
    omega

/-! ## Steps 1-3. Floors, thresholds, cuts -/

/-- The five actual thresholds, indexed as in `VSlab.thr`
(0 `K1`, 1 `K2`, 2 `L1`, 3 `L2`, 4 `W`). -/
def vThr (n p : ℕ) : Fin 5 → ℕ :=
  ![2 * n % p, 6 * n % p, n % p, 10 * n % p, p - n % p]

/-- Actual sorted cut points `0 ≤ … ≤ p`. -/
def vCutAct (s : VSlab) (n p : ℕ) : Fin 7 → ℕ :=
  ![0, vThr n p (s.perm 0), vThr n p (s.perm 1), vThr n p (s.perm 2),
    vThr n p (s.perm 3), vThr n p (s.perm 4), p]

theorem vCutAct_thr (s : VSlab) (n p : ℕ) (j : Fin 5) :
    vCutAct s n p ⟨j.val + 1, by omega⟩ = vThr n p (s.perm j) := by
  fin_cases j <;> rfl

theorem h4_floor_of_aff {N F : ℕ} {x x' lo hi : ℚ} {m p : ℕ}
    (hm : 0 < (m : ℚ)) (hlo : lo * m < p) (hhi : p < hi * m)
    (hN : (N : ℚ) = x * m) (hx : x' = -x)
    (h1 : (⟨x, -(F : ℚ)⟩ : RAff).nonnegOn lo hi = true)
    (h2 : (⟨x', (F : ℚ) + 1⟩ : RAff).posOpen lo hi = true) :
    N / p = F := by
  subst hx
  exact p0_floor_of_aff hm hlo hhi hN h1 h2

theorem ok_parts {s : VSlab} (hs : s.ok = true) :
    1 / 40 ≤ s.lo ∧ s.lo < s.hi ∧ s.hi ≤ 5 / 4 ∧
    (⟨1 / 2, -(s.A : ℚ)⟩ : RAff).nonnegOn s.lo s.hi = true ∧
    (⟨-1 / 2, (s.A : ℚ) + 1⟩ : RAff).posOpen s.lo s.hi = true ∧
    (⟨3 / 2, -(s.B : ℚ)⟩ : RAff).nonnegOn s.lo s.hi = true ∧
    (⟨-3 / 2, (s.B : ℚ) + 1⟩ : RAff).posOpen s.lo s.hi = true ∧
    (⟨1 / 4, -(s.C : ℚ)⟩ : RAff).nonnegOn s.lo s.hi = true ∧
    (⟨-1 / 4, (s.C : ℚ) + 1⟩ : RAff).posOpen s.lo s.hi = true ∧
    (⟨5 / 2, -(s.D : ℚ)⟩ : RAff).nonnegOn s.lo s.hi = true ∧
    (⟨-5 / 2, (s.D : ℚ) + 1⟩ : RAff).posOpen s.lo s.hi = true ∧
    Function.Injective s.perm ∧
    (∀ g : Fin 6, (s.width g).nonnegOn s.lo s.hi = true) ∧
    s.total = ⟨s.icpt, s.slope⟩ ∧
    0 ≤ s.icpt + s.slope * s.lo ∧ 0 ≤ s.icpt + s.slope * s.hi := by
  simp only [VSlab.ok, Bool.and_eq_true] at hs
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩,
    h14⟩, h15⟩, h16⟩ := hs
  -- `of_decide_eq_true` decodes the corresponding Bool fields of `hs`; it
  -- does not assert any unchecked mathematical fact.
  exact ⟨of_decide_eq_true h1, of_decide_eq_true h2, of_decide_eq_true h3, h4, h5, h6, h7,
    h8, h9, h10, h11, of_decide_eq_true h12,
    fun g => List.all_eq_true.mp h13 g (List.mem_finRange g),
    of_decide_eq_true h14, of_decide_eq_true h15, of_decide_eq_true h16⟩

section Sound

variable {s : VSlab} {n p : ℕ}

theorem floors_of_ok (hs : s.ok = true) (hn : 0 < n)
    (hlo : s.lo * ((4 * n : ℕ) : ℚ) < p) (hhi : (p : ℚ) < s.hi * ((4 * n : ℕ) : ℚ)) :
    2 * n / p = s.A ∧ 6 * n / p = s.B ∧ n / p = s.C ∧ 10 * n / p = s.D := by
  obtain ⟨-, -, -, hA1, hA2, hB1, hB2, hC1, hC2, hD1, hD2, -⟩ := ok_parts hs
  have hmQ : (0 : ℚ) < ((4 * n : ℕ) : ℚ) := by exact_mod_cast (by omega : 0 < 4 * n)
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact h4_floor_of_aff (x := 1 / 2) hmQ hlo hhi (by push_cast; ring) (by norm_num) hA1 hA2
  · exact h4_floor_of_aff (x := 3 / 2) hmQ hlo hhi (by push_cast; ring) (by norm_num) hB1 hB2
  · exact h4_floor_of_aff (x := 1 / 4) hmQ hlo hhi (by push_cast; ring) (by norm_num) hC1 hC2
  · exact h4_floor_of_aff (x := 5 / 2) hmQ hlo hhi (by push_cast; ring) (by norm_num) hD1 hD2

/-- Step 2: actual thresholds are the affine thresholds (copy of `p0Cell_thr_val`). -/
theorem vThr_val (hp : 0 < p)
    (hA : 2 * n / p = s.A) (hB : 6 * n / p = s.B) (hC : n / p = s.C) (hD : 10 * n / p = s.D)
    (k : Fin 5) :
    ((vThr n p k : ℕ) : ℚ) = (s.thr k).val ((4 * n : ℕ) : ℚ) p := by
  have dA := Nat.div_add_mod (2 * n) p
  have dB := Nat.div_add_mod (6 * n) p
  have dC := Nat.div_add_mod n p
  have dD := Nat.div_add_mod (10 * n) p
  rw [hA] at dA
  rw [hB] at dB
  rw [hC] at dC
  rw [hD] at dD
  have qA : ((2 * n % p : ℕ) : ℚ) = 2 * n - s.A * p := by
    have : ((p * s.A + 2 * n % p : ℕ) : ℚ) = ((2 * n : ℕ) : ℚ) := by exact_mod_cast dA
    push_cast at this; linarith
  have qB : ((6 * n % p : ℕ) : ℚ) = 6 * n - s.B * p := by
    have : ((p * s.B + 6 * n % p : ℕ) : ℚ) = ((6 * n : ℕ) : ℚ) := by exact_mod_cast dB
    push_cast at this; linarith
  have qC : ((n % p : ℕ) : ℚ) = n - s.C * p := by
    have : ((p * s.C + n % p : ℕ) : ℚ) = (n : ℚ) := by exact_mod_cast dC
    push_cast at this; linarith
  have qD : ((10 * n % p : ℕ) : ℚ) = 10 * n - s.D * p := by
    have : ((p * s.D + 10 * n % p : ℕ) : ℚ) = ((10 * n : ℕ) : ℚ) := by exact_mod_cast dD
    push_cast at this; linarith
  have qW : ((p - n % p : ℕ) : ℚ) = p - n + s.C * p := by
    rw [Nat.cast_sub (Nat.mod_lt n hp).le, qC]
    ring
  fin_cases k <;> simp [vThr, VSlab.thr, RAff.val, qA, qB, qC, qD, qW] <;> ring

theorem vCut_val (hp : 0 < p)
    (hA : 2 * n / p = s.A) (hB : 6 * n / p = s.B) (hC : n / p = s.C) (hD : 10 * n / p = s.D)
    (g : Fin 7) :
    ((vCutAct s n p g : ℕ) : ℚ) = (s.cut g).val ((4 * n : ℕ) : ℚ) p := by
  have ht := vThr_val (s := s) hp hA hB hC hD
  fin_cases g
  · simp [vCutAct, VSlab.cut]
  · simpa [vCutAct, VSlab.cut] using ht (s.perm 0)
  · simpa [vCutAct, VSlab.cut] using ht (s.perm 1)
  · simpa [vCutAct, VSlab.cut] using ht (s.perm 2)
  · simpa [vCutAct, VSlab.cut] using ht (s.perm 3)
  · simpa [vCutAct, VSlab.cut] using ht (s.perm 4)
  · simp [vCutAct, VSlab.cut, RAff.val]

/-- Step 3: the actual cuts are monotone (only consecutive widths are checked). -/
theorem vCut_mono (hp : 0 < p)
    (hA : 2 * n / p = s.A) (hB : 6 * n / p = s.B) (hC : n / p = s.C) (hD : 10 * n / p = s.D)
    (hmQ : (0 : ℚ) < ((4 * n : ℕ) : ℚ))
    (hlo : s.lo * ((4 * n : ℕ) : ℚ) < p) (hhi : (p : ℚ) < s.hi * ((4 * n : ℕ) : ℚ))
    (hwid : ∀ g : Fin 6, (s.width g).nonnegOn s.lo s.hi = true) :
    Monotone (vCutAct s n p) := by
  rw [Fin.monotone_iff_le_succ]
  intro g
  have hw := RAff.nonneg_of_nonnegOn (s.width g) hmQ hlo.le hhi.le (hwid g)
  simp only [VSlab.width, RAff.val_sub] at hw
  rw [← vCut_val hp hA hB hC hD g.succ, ← vCut_val hp hA hB hC hD g.castSucc] at hw
  have : ((vCutAct s n p g.castSucc : ℕ) : ℚ) ≤ vCutAct s n p g.succ := by linarith
  exact_mod_cast this

/-! ## Step 4. Group decomposition (copy of `p0Cell_group_sum`, six groups) -/

theorem h4_group_sum6 {p : ℕ} (S : Fin 7 → ℕ) (mono : Monotone S) (h0 : S 0 = 0)
    (h6 : S 6 = p) (ψ : ℕ → ℤ) (Ψ : Fin 6 → ℤ)
    (h : ∀ g : Fin 6, ∀ v, S g.castSucc ≤ v → v < S g.succ → ψ v = Ψ g) :
    ∑ v ∈ range p, ψ v = ∑ g : Fin 6, (((S g.succ : ℕ) : ℤ) - S g.castSucc) * Ψ g := by
  have hgroup : ∀ g : Fin 6, ∑ v ∈ Ico (S g.castSucc) (S g.succ), ψ v =
      (((S g.succ : ℕ) : ℤ) - S g.castSucc) * Ψ g := by
    intro g
    rw [Finset.sum_congr rfl (fun v hv => h g v (Finset.mem_Ico.mp hv).1 (Finset.mem_Ico.mp hv).2),
      Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
    have hle : S g.castSucc ≤ S g.succ := mono (Fin.castSucc_le_succ g)
    push_cast [hle]
    ring
  have h01 : S 0 ≤ S 1 := mono (by decide)
  have h12 : S 1 ≤ S 2 := mono (by decide)
  have h23 : S 2 ≤ S 3 := mono (by decide)
  have h34 : S 3 ≤ S 4 := mono (by decide)
  have h45 : S 4 ≤ S 5 := mono (by decide)
  have h56 : S 5 ≤ S 6 := mono (by decide)
  have hr : range p = Ico (S 0) (S 6) := by
    rw [Finset.range_eq_Ico, h0, h6]
  have e0 : ∑ v ∈ Ico (S 0) (S 1), ψ v = (((S 1 : ℕ) : ℤ) - S 0) * Ψ 0 := hgroup 0
  have e1 : ∑ v ∈ Ico (S 1) (S 2), ψ v = (((S 2 : ℕ) : ℤ) - S 1) * Ψ 1 := hgroup 1
  have e2 : ∑ v ∈ Ico (S 2) (S 3), ψ v = (((S 3 : ℕ) : ℤ) - S 2) * Ψ 2 := hgroup 2
  have e3 : ∑ v ∈ Ico (S 3) (S 4), ψ v = (((S 4 : ℕ) : ℤ) - S 3) * Ψ 3 := hgroup 3
  have e4 : ∑ v ∈ Ico (S 4) (S 5), ψ v = (((S 5 : ℕ) : ℤ) - S 4) * Ψ 4 := hgroup 4
  have e5 : ∑ v ∈ Ico (S 5) (S 6), ψ v = (((S 6 : ℕ) : ℤ) - S 5) * Ψ 5 := hgroup 5
  rw [hr,
    ← Finset.sum_Ico_consecutive _ h01 (h12.trans (h23.trans (h34.trans (h45.trans h56)))),
    ← Finset.sum_Ico_consecutive _ h12 (h23.trans (h34.trans (h45.trans h56))),
    ← Finset.sum_Ico_consecutive _ h23 (h34.trans (h45.trans h56)),
    ← Finset.sum_Ico_consecutive _ h34 (h45.trans h56),
    ← Finset.sum_Ico_consecutive _ h45 h56,
    Fin.sum_univ_six, e0, e1, e2, e3, e4, e5]
  show _ = (((S 1 : ℕ) : ℤ) - S 0) * Ψ 0 + (((S 2 : ℕ) : ℤ) - S 1) * Ψ 1 +
    (((S 3 : ℕ) : ℤ) - S 2) * Ψ 2 + (((S 4 : ℕ) : ℤ) - S 3) * Ψ 3 +
    (((S 5 : ℕ) : ℤ) - S 4) * Ψ 4 + (((S 6 : ℕ) : ℤ) - S 5) * Ψ 5
  ring

/-! ## Step 5. Threshold bits (copy of `p0Cell_bits`, five thresholds) -/

theorem vbits (hinj : Function.Injective s.perm) (hmono : Monotone (vCutAct s n p))
    (g : Fin 6) (u : ℕ) (hu1 : vCutAct s n p g.castSucc ≤ u) (hu2 : u < vCutAct s n p g.succ)
    (k : Fin 5) :
    vThr n p k ≤ u ↔ s.above g k = true := by
  have hsurj : Function.Surjective s.perm := Finite.injective_iff_surjective.mp hinj
  obtain ⟨j, hj⟩ := hsurj k
  have hcut : vCutAct s n p ⟨j.val + 1, by omega⟩ = vThr n p k := by
    rw [← hj]; exact vCutAct_thr s n p j
  by_cases hjg : j.val < g.val
  · have hle : (⟨j.val + 1, by omega⟩ : Fin 7) ≤ g.castSucc := by
      simp [Fin.le_def]; omega
    have h1 := hmono hle
    rw [hcut] at h1
    have hab : s.above g k = true := by
      simp only [VSlab.above, decide_eq_true_eq]
      exact ⟨j, hjg, hj⟩
    rw [hab]
    simp only [iff_true]
    omega
  · have hle : g.succ ≤ (⟨j.val + 1, by omega⟩ : Fin 7) := by
      simp [Fin.le_def]; omega
    have h1 := hmono hle
    rw [hcut] at h1
    have hab : s.above g k = false := by
      simp only [VSlab.above, decide_eq_false_iff_not, not_exists, not_and]
      intro j' hj' hj'k
      have : j' = j := hinj (hj'k.trans hj.symm)
      subst this
      exact hjg hj'
    rw [hab]
    simp only [Bool.false_eq_true, iff_false, not_le]
    omega

/-! ## Steps 6-7 on a group: the per-residue rank profile equals `VSlab.rk` -/

theorem rankProfile_eq (hp : 0 < p) (hp5 : p < 5 * n)
    (hA : 2 * n / p = s.A) (hB : 6 * n / p = s.B) (hC : n / p = s.C) (hD : 10 * n / p = s.D)
    (hinj : Function.Injective s.perm) (hmono : Monotone (vCutAct s n p))
    (g : Fin 6) (u : ℕ) (hu1 : vCutAct s n p g.castSucc ≤ u)
    (hu2 : u < vCutAct s n p g.succ) :
    V.Q5Certificate.q5RankProfile (4 * n) p u = s.rk g := by
  have hup : u < p := by
    have := hmono (Fin.le_last g.succ)
    have h6 : vCutAct s n p (Fin.last 6) = p := rfl
    omega
  have b := vbits hinj hmono g u hu1 hu2
  have b0 : 2 * n % p ≤ u ↔ s.above g 0 = true := by simpa [vThr] using b 0
  have b1 : 6 * n % p ≤ u ↔ s.above g 1 = true := by simpa [vThr] using b 1
  have b2 : n % p ≤ u ↔ s.above g 2 = true := by simpa [vThr] using b 2
  have b3 : 10 * n % p ≤ u ↔ s.above g 3 = true := by simpa [vThr] using b 3
  have b4 : p - n % p ≤ u ↔ s.above g 4 = true := by simpa [vThr] using b 4
  -- |K_u|
  have eK : s.kCnt g = (((V.Q5Certificate.q5K (4 * n) p u).card : ℕ) : ℤ) := by
    rw [q5K_four_mul hp hup, Nat.card_Ico,
      Nat.cast_sub (h4Cnt_mono hp hup (by omega : 2 * n ≤ 6 * n))]
    unfold h4Cnt VSlab.kCnt
    rw [hA, hB, h4_ite_lt u (2 * n % p), h4_ite_lt u (6 * n % p)]
    simp only [b0, b1]
    push_cast
    ring
  -- |L_u|
  have eL : s.lCnt g = (((V.Q5Certificate.q5L (4 * n) p u).card : ℕ) : ℤ) := by
    rw [q5L_four_mul hp hup, Nat.card_Ico,
      Nat.cast_sub (h4Cnt_mono hp hup (by omega : n ≤ 10 * n))]
    unfold h4Cnt VSlab.lCnt
    rw [hC, hD, h4_ite_lt u (n % p), h4_ite_lt u (10 * n % p)]
    simp only [b2, b3]
    push_cast
    ring
  -- |W_u|
  have eW : s.wCnt g = (((V.Q5Certificate.q5W (4 * n) p u).card : ℕ) : ℤ) := by
    rw [q5W_card_four_mul hp hup hp5, hC]
    unfold VSlab.wCnt
    simp only [b4]
    push_cast
    try ring
  -- rank-one saving
  have eS : s.sav g = ((V.Q5Certificate.q5RankSaving (4 * n) p u : ℕ) : ℤ) := by
    rw [q5RankSaving_four_mul hp hup hp5]
    unfold VSlab.sav
    have i1 := h4_le_iff_K1 hp hup hA
    have i2 := h4_le_iff_K2 hp hup (by omega) hB
    have i3 := h4_le_iff_L2 hp hup (by omega) hD
    have i4 := h4_lt_iff_W hp hup hC
    rw [b0] at i1
    rw [b1] at i2
    rw [b3] at i3
    rw [b4] at i4
    have hc : (2 * n ≤ u ∧ 6 * n ≤ u + p ∧ 10 * n ≤ u + 2 * p ∧ u + n < p) ↔
        (s.A = 0 ∧ s.above g 0 = true ∧ s.B = 1 ∧ s.above g 1 = true ∧
          s.D = 2 ∧ s.above g 3 = true ∧ s.C = 0 ∧ ¬ s.above g 4 = true) := by
      rw [i1, i2, i3, i4]
      simp only [and_assoc]
    by_cases h : s.A = 0 ∧ s.above g 0 = true ∧ s.B = 1 ∧ s.above g 1 = true ∧
        s.D = 2 ∧ s.above g 3 = true ∧ s.C = 0 ∧ ¬ s.above g 4 = true
    · simp only [if_pos h, if_pos (hc.mpr h), Nat.cast_one]
    · simp only [if_neg h, if_neg (fun h' => h (hc.mp h')), Nat.cast_zero]
  unfold V.Q5Certificate.q5RankProfile VSlab.rk
  rw [eK, eL, eW, eS]

/-! ## Step 8. Assembly -/

theorem total_val (s : VSlab) (M P : ℚ) :
    s.total.val M P = M + ∑ g : Fin 6, (s.rk g : ℚ) * (s.width g).val M P := by
  simp only [VSlab.total, RAff.val_add, RAff.val_smul, RAff.val_mk, Fin.sum_univ_six]
  ring

end Sound

end H4Slab

open H4Slab in
/-- SOUNDNESS of one checked slab: for `ρ = p / (4n)` strictly inside the slab, the
actual residue exponent is the slab's affine form. -/
theorem VSlab.residueExponent_eq {s : VSlab} (hs : s.ok = true)
    {n p : ℕ} (hn : 0 < n)
    (hlo : s.lo * ((4 * n : ℕ) : ℚ) < p)
    (hhi : (p : ℚ) < s.hi * ((4 * n : ℕ) : ℚ)) :
    ((V.Q5Certificate.q5ResidueExponent (4 * n) p : ℤ) : ℚ) =
      s.icpt * ((4 * n : ℕ) : ℚ) + s.slope * p := by
  obtain ⟨hlo40, -, hhi54, -, -, -, -, -, -, -, -, hinj, hwid, htot, -, -⟩ := ok_parts hs
  have hmQ : (0 : ℚ) < ((4 * n : ℕ) : ℚ) := by exact_mod_cast (by omega : 0 < 4 * n)
  have hp : 0 < p := by
    have h1 : (0 : ℚ) < s.lo * ((4 * n : ℕ) : ℚ) := mul_pos (by linarith) hmQ
    exact_mod_cast h1.trans hlo
  have hp5 : p < 5 * n := by
    have h1 : s.hi * ((4 * n : ℕ) : ℚ) ≤ 5 / 4 * ((4 * n : ℕ) : ℚ) :=
      mul_le_mul_of_nonneg_right hhi54 hmQ.le
    have h2 : (p : ℚ) < 5 * n := by
      norm_num at h1
      have h2' := hhi
      norm_num at h2'
      linarith
    exact_mod_cast h2
  obtain ⟨hA, hB, hC, hD⟩ := floors_of_ok hs hn hlo hhi
  have hmono := vCut_mono hp hA hB hC hD hmQ hlo hhi hwid
  have hsum := h4_group_sum6 (p := p) (vCutAct s n p) hmono rfl rfl
    (V.Q5Certificate.q5RankProfile (4 * n) p) s.rk
    (fun g u h1 h2 => rankProfile_eq hp hp5 hA hB hC hD hinj hmono g u h1 h2)
  have hT : s.total.val ((4 * n : ℕ) : ℚ) p = s.icpt * ((4 * n : ℕ) : ℚ) + s.slope * p := by
    rw [htot, RAff.val_mk]
  rw [total_val] at hT
  rw [← hT]
  unfold V.Q5Certificate.q5ResidueExponent
  rw [hsum]
  simp only [Int.cast_add, Int.cast_natCast, Int.cast_sum, Int.cast_mul, Int.cast_sub]
  congr 1
  refine Finset.sum_congr rfl (fun g _ => ?_)
  simp only [VSlab.width, RAff.val_sub]
  rw [← vCut_val hp hA hB hC hD g.succ, ← vCut_val hp hA hB hC hD g.castSucc]
  ring

end Li2Lean.B3

#print axioms Li2Lean.B3.VSlab.residueExponent_eq

