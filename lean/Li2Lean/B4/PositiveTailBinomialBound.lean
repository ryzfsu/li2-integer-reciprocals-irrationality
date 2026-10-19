/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Mathlib
import Li2Lean.B4.PositiveTailStirling

namespace Li2Lean.B4

open Finset

/-!
The positive coefficient majorant follows the four-binomial factorization
of the v13 residue at `hp-tail.tex:20-23`, and the tilted estimate used in
the positive-tail argument at `hp-tail.tex:226-256` (in particular the
saddle equation and rate at `:243-245`).  `PositiveTailStirling` is imported
as the existing 1/2-code generalization: its residue magnitude and its
`ConfigSelfStirling.log_factorial_stirling_upper` adapter remain available,
although the elementary bound below does not need Stirling.
-/

noncomputable section

/-- Four-binomial encoding of the positive residue coefficient.  It is the
factorization of v13 `hp-tail.tex:20-23`. -/
def hpTailBinomialProduct (j k : ℕ) : ℝ :=
  (((2 * j + 3 * k).choose j : ℕ) : ℝ) *
    (((j + 3 * k).choose j : ℕ) : ℝ) *
    (((3 * k).choose k : ℕ) : ℝ) *
    (((2 * k).choose k : ℕ) : ℝ)

/-- Fixed rational point just above the v13 saddle bracket endpoint at
`hp-tail.tex:243-245,436-441`. -/
def hpTailTiltT0 : ℝ := (13683 : ℝ) / 100000

/-- The certified positive exponential rate from the v13 expression
`exp f_q(t)=((3-t)/(1-t))^3` at `hp-tail.tex:245`. -/
def hpTailTiltK : ℝ := ((3 - hpTailTiltT0) / (1 - hpTailTiltT0)) ^ 3

/-- Positivity of the fixed saddle parameter used in v13 `:243-245`. -/
lemma hpTailTiltT0_pos : 0 < hpTailTiltT0 := by
  norm_num [hpTailTiltT0]

/-- The fixed saddle parameter is below one, as required by v13 `:243-245`. -/
lemma hpTailTiltT0_lt_one : hpTailTiltT0 < 1 := by
  norm_num [hpTailTiltT0]

/-- Rational certificate for the v13 saddle inequality at `q = 12`.
Source: v13 `hp-tail.tex:243-245`; the rational endpoint is taken from the
v13 bracket at `:436-441`. -/
lemma hpTailTilt_certificate_12 :
    (1 - hpTailTiltT0) ^ 3 ≤ 12 * hpTailTiltT0 ^ 2 * (3 - hpTailTiltT0) := by
  norm_num [hpTailTiltT0]

/-- The one rational saddle certificate works uniformly for every `q ≥ 12`.
Source: v13 `hp-tail.tex:243-245`. -/
lemma hpTailTilt_certificate (q : ℝ) (hq : 12 ≤ q) :
    (1 - hpTailTiltT0) ^ 3 ≤ q * hpTailTiltT0 ^ 2 * (3 - hpTailTiltT0) := by
  have hc : 0 ≤ hpTailTiltT0 ^ 2 * (3 - hpTailTiltT0) := by
    exact mul_nonneg (sq_nonneg _) (by linarith [hpTailTiltT0_lt_one])
  calc
    (1 - hpTailTiltT0) ^ 3 ≤ 12 * hpTailTiltT0 ^ 2 * (3 - hpTailTiltT0) :=
      hpTailTilt_certificate_12
    _ ≤ q * hpTailTiltT0 ^ 2 * (3 - hpTailTiltT0) := by
      simpa [mul_assoc] using mul_le_mul_of_nonneg_right hq hc

/-- A single nonnegative binomial term is bounded by the full binomial sum.
This is the elementary input to the v13 coefficient bound
`hp-tail.tex:226-256`. -/
theorem hpTail_choose_mul_pow_le_add_pow {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (i r : ℕ) :
    ((i + r).choose r : ℝ) * x ^ r * y ^ i ≤ (x + y) ^ (i + r) := by
  rw [add_pow]
  have hmem : r ∈ range (i + r + 1) := by
    simp only [mem_range]
    omega
  have hsum := Finset.single_le_sum
    (f := fun m => x ^ m * y ^ (i + r - m) * ((i + r).choose m : ℝ))
    (fun m hm => by
      exact mul_nonneg (mul_nonneg (pow_nonneg hx _) (pow_nonneg hy _))
        (Nat.cast_nonneg _)) hmem
  have hsub : i + r - r = i := by omega
  calc
    ((i + r).choose r : ℝ) * x ^ r * y ^ i =
        x ^ r * y ^ (i + r - r) * ((i + r).choose r : ℝ) := by
          rw [hsub]
          ring
    _ ≤ ∑ m ∈ range (i + r + 1),
          x ^ m * y ^ (i + r - m) * ((i + r).choose m : ℝ) := hsum

/-- Exact natural-number factorization of the v13 residue coefficient after
writing `n = j + k`; this avoids truncated subtraction in the main estimate.
Source: v13 `hp-tail.tex:20-23`. -/
theorem hpTail_residue_factor (j k : ℕ) :
    (2 * j + 3 * k + 1).factorial =
      (2 * j + 3 * k + 1) *
        (((2 * j + 3 * k).choose j) * ((j + 3 * k).choose j) *
          ((3 * k).choose k) * ((2 * k).choose k)) *
        (j.factorial ^ 2) * (k.factorial ^ 3) := by
  have h1idx : (j + 3 * k) + j = 2 * j + 3 * k := by omega
  have h2idx : 3 * k + j = j + 3 * k := by omega
  have h3idx : 2 * k + k = 3 * k := by omega
  have h4idx : k + k = 2 * k := by omega
  have h1 : (2 * j + 3 * k).choose j * (j + 3 * k).factorial * j.factorial =
      (2 * j + 3 * k).factorial := by
    simpa only [h1idx] using
      (Nat.add_choose_mul_factorial_mul_factorial (j + 3 * k) j)
  have h2 : (j + 3 * k).choose j * j.factorial * (3 * k).factorial =
      (j + 3 * k).factorial := by
    calc
      _ = (j + 3 * k).choose j * (3 * k).factorial * j.factorial := by ac_rfl
      _ = (3 * k + j).factorial := by
        rw [← h2idx]
        exact Nat.add_choose_mul_factorial_mul_factorial (3 * k) j
      _ = _ := by congr 1 <;> omega
  have h3 : (3 * k).choose k * k.factorial * (2 * k).factorial =
      (3 * k).factorial := by
    calc
      _ = (3 * k).choose k * (2 * k).factorial * k.factorial := by ac_rfl
      _ = (3 * k).factorial := by
        simpa only [h3idx] using
          (Nat.add_choose_mul_factorial_mul_factorial (2 * k) k)
  have h4 : (2 * k).choose k * k.factorial * k.factorial =
      (2 * k).factorial := by
    simpa only [h4idx] using
      (Nat.add_choose_mul_factorial_mul_factorial k k)
  suffices hfac : (2 * j + 3 * k).factorial =
      ((2 * j + 3 * k).choose j * (j + 3 * k).choose j *
        (3 * k).choose k * (2 * k).choose k) *
        j.factorial ^ 2 * k.factorial ^ 3 by
    rw [Nat.factorial_succ, hfac]
    ring
  calc
    (2 * j + 3 * k).factorial =
        (2 * j + 3 * k).choose j * j.factorial * (j + 3 * k).factorial := by
          calc
            _ = (2 * j + 3 * k).choose j * (j + 3 * k).factorial * j.factorial := h1.symm
            _ = _ := by ring
    _ = (2 * j + 3 * k).choose j * j.factorial *
          ((j + 3 * k).choose j * j.factorial * (3 * k).factorial) := by
            rw [← h2]
    _ = (2 * j + 3 * k).choose j * j.factorial *
          ((j + 3 * k).choose j * j.factorial *
            ((3 * k).choose k * k.factorial * (2 * k).factorial)) := by
            rw [← h3]
    _ = (2 * j + 3 * k).choose j * j.factorial *
          ((j + 3 * k).choose j * j.factorial *
            ((3 * k).choose k * k.factorial *
              ((2 * k).choose k * k.factorial * k.factorial))) := by
            rw [← h4]
    _ = _ := by ring

/-- Real form of the v13 residue factorization, after cancellation of the
factorials in its denominator.  Source: `hp-tail.tex:20-23`. -/
lemma hpTail_residue_factor_real (j k : ℕ) :
    hpTailResidueMagnitude (j + k) j =
      ((2 * j + 3 * k + 1 : ℕ) : ℝ) * hpTailBinomialProduct j k := by
  have hnum : 3 * (j + k) + 1 - j = 2 * j + 3 * k + 1 := by omega
  have hden : j + k - j = k := by omega
  rw [hpTailResidueMagnitude, hnum, hden]
  apply (div_eq_iff (by positivity :
    (j.factorial : ℝ) ^ 2 * (k.factorial : ℝ) ^ 3 ≠ 0)).2
  have hfacCast : ((2 * j + 3 * k + 1).factorial : ℝ) =
      ((2 * j + 3 * k + 1 : ℕ) : ℝ) *
        (((2 * j + 3 * k).choose j : ℕ) : ℝ) *
        (((j + 3 * k).choose j : ℕ) : ℝ) *
        (((3 * k).choose k : ℕ) : ℝ) *
        (((2 * k).choose k : ℕ) : ℝ) *
        (j.factorial : ℝ) ^ 2 * (k.factorial : ℝ) ^ 3 := by
    have hnat := hpTail_residue_factor j k
    exact_mod_cast (show (2 * j + 3 * k + 1).factorial =
      (2 * j + 3 * k + 1) * (2 * j + 3 * k).choose j *
        (j + 3 * k).choose j * (3 * k).choose k *
        (2 * k).choose k * j.factorial ^ 2 * k.factorial ^ 3 by
          calc
            _ = (2 * j + 3 * k + 1) *
              ((2 * j + 3 * k).choose j * (j + 3 * k).choose j *
                (3 * k).choose k * (2 * k).choose k) *
              j.factorial ^ 2 * k.factorial ^ 3 := hnat
            _ = _ := by ring)
  have hfac' : ((2 * j + 3 * k + 1).factorial : ℝ) =
      (((2 * j + 3 * k + 1 : ℕ) : ℝ) * hpTailBinomialProduct j k) *
        ((j.factorial : ℝ) ^ 2 * (k.factorial : ℝ) ^ 3) := by
    calc
      _ = ((2 * j + 3 * k + 1 : ℕ) : ℝ) *
          (((2 * j + 3 * k).choose j : ℕ) : ℝ) *
          (((j + 3 * k).choose j : ℕ) : ℝ) *
          (((3 * k).choose k : ℕ) : ℝ) *
          (((2 * k).choose k : ℕ) : ℝ) *
          (j.factorial : ℝ) ^ 2 * (k.factorial : ℝ) ^ 3 := hfacCast
      _ = _ := by dsimp [hpTailBinomialProduct]; ring
  calc
    ((2 * j + 3 * k + 1).factorial : ℝ) =
        (((2 * j + 3 * k + 1 : ℕ) : ℝ) * hpTailBinomialProduct j k) *
          ((j.factorial : ℝ) ^ 2 * (k.factorial : ℝ) ^ 3) := hfac'
    _ = (((2 * j + 3 * k + 1 : ℕ) : ℝ) * hpTailBinomialProduct j k) *
          ((j.factorial : ℝ) ^ 2 * (k.factorial : ℝ) ^ 3) := by ring

/-- Weighted four-binomial bound (W), proved by four applications of the
binomial theorem. Source: v13 `hp-tail.tex:226-256`. -/
theorem hpTail_weighted_binomial_le {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (j k : ℕ) :
    hpTailBinomialProduct j k * a ^ (2 * j) * b ^ (3 * k) ≤
      (2 * a + 3 * b) ^ (2 * j + 3 * k) := by
  let c1 : ℝ := ((2 * j + 3 * k).choose j : ℕ)
  let c2 : ℝ := ((j + 3 * k).choose j : ℕ)
  let c3 : ℝ := ((3 * k).choose k : ℕ)
  let c4 : ℝ := ((2 * k).choose k : ℕ)
  have h1 := hpTail_choose_mul_pow_le_add_pow hb hb k k
  have h1' : c4 * b ^ k * b ^ k ≤ (2 * b) ^ (2 * k) := by
    dsimp [c4]
    simpa [two_mul] using h1
  have h2 := hpTail_choose_mul_pow_le_add_pow hb (by positivity : 0 ≤ 2 * b) (2 * k) k
  have h2' : c3 * b ^ k * (2 * b) ^ (2 * k) ≤ (3 * b) ^ (3 * k) := by
    dsimp [c3]
    convert h2 using 1 <;> ring
  have h3 := hpTail_choose_mul_pow_le_add_pow ha (by positivity : 0 ≤ 3 * b)
    (3 * k) j
  have h3' : c2 * a ^ j * (3 * b) ^ (3 * k) ≤
      (a + 3 * b) ^ (j + 3 * k) := by
    dsimp [c2]
    convert h3 using 1 <;> ring
  have h4 := hpTail_choose_mul_pow_le_add_pow ha
    (by positivity : 0 ≤ a + 3 * b) (j + 3 * k) j
  have h4' : c1 * a ^ j * (a + 3 * b) ^ (j + 3 * k) ≤
      (2 * a + 3 * b) ^ (2 * j + 3 * k) := by
    dsimp [c1]
    convert h4 using 1 <;> ring
  have hbc : c3 * c4 * b ^ (3 * k) ≤ (3 * b) ^ (3 * k) := by
    have he : 3 * k = k + (k + k) := by omega
    calc
      c3 * c4 * b ^ (3 * k) = c3 * b ^ k * (c4 * b ^ k * b ^ k) := by
        rw [he, pow_add, pow_add]
        ring
      _ ≤ c3 * b ^ k * (2 * b) ^ (2 * k) := by
        have hk : 0 ≤ c3 * b ^ k := by positivity
        exact mul_le_mul_of_nonneg_left h1' hk
      _ ≤ (3 * b) ^ (3 * k) := h2'
  have habc : c2 * c3 * c4 * a ^ j * b ^ (3 * k) ≤
      (a + 3 * b) ^ (j + 3 * k) := by
    calc
      c2 * c3 * c4 * a ^ j * b ^ (3 * k) =
          c2 * a ^ j * (c3 * c4 * b ^ (3 * k)) := by ring
      _ ≤ c2 * a ^ j * (3 * b) ^ (3 * k) := by
        have hk : 0 ≤ c2 * a ^ j := by positivity
        exact mul_le_mul_of_nonneg_left hbc hk
      _ ≤ (a + 3 * b) ^ (j + 3 * k) := h3'
  calc
    hpTailBinomialProduct j k * a ^ (2 * j) * b ^ (3 * k) =
        c1 * a ^ j * (c2 * c3 * c4 * a ^ j * b ^ (3 * k)) := by
          dsimp [hpTailBinomialProduct, c1, c2, c3, c4]
          rw [show 2 * j = j + j by omega, pow_add]
          ring
    _ ≤ c1 * a ^ j * (a + 3 * b) ^ (j + 3 * k) := by
      have hk : 0 ≤ c1 * a ^ j := by positivity
      exact mul_le_mul_of_nonneg_left habc hk
    _ ≤ (2 * a + 3 * b) ^ (2 * j + 3 * k) := h4'

/-- A power identity used to convert (W) into the saddle-free rate in (U).
Source: the v13 saddle equation and rate `hp-tail.tex:243-245`. -/
private lemma hpTail_tilt_scale_identity (q : ℝ) (j k : ℕ) :
    hpTailTiltK ^ (j + k) * q ^ j * hpTailTiltT0 ^ (2 * j) *
        (1 - hpTailTiltT0) ^ (3 * k) =
      (3 - hpTailTiltT0) ^ (2 * j + 3 * k) *
        ((q * hpTailTiltT0 ^ 2 * (3 - hpTailTiltT0)) /
          (1 - hpTailTiltT0) ^ 3) ^ j := by
  have hb : 1 - hpTailTiltT0 ≠ 0 := ne_of_gt (by linarith [hpTailTiltT0_lt_one])
  have hd : 3 * (j + k) = (2 * j + 3 * k) + j := by omega
  unfold hpTailTiltK
  rw [← pow_mul, div_pow, hd, pow_add]
  rw [show 2 * j + 3 * k + j = 3 * j + 3 * k by omega, pow_add]
  rw [div_pow, mul_pow, mul_pow, pow_mul, pow_mul]
  field_simp
  simp only [← pow_mul, pow_add]
  ring

/-- Tilted residue bound (U) in the `n=j+k` parametrization.
Source: v13 `hp-tail.tex:226-256`, with its saddle equation at `:243-245`. -/
theorem hpTail_residue_tilted (q : ℝ) (hq : 12 ≤ q) (j k : ℕ) :
    ((2 * j + 3 * k + 1 : ℕ) : ℝ) * hpTailBinomialProduct j k * q⁻¹ ^ j ≤
      ((2 * j + 3 * k + 1 : ℕ) : ℝ) * hpTailTiltK ^ (j + k) := by
  have ht := hpTailTilt_certificate q hq
  have hbpos : 0 < 1 - hpTailTiltT0 := by linarith [hpTailTiltT0_lt_one]
  have hdpos : 0 < 3 - hpTailTiltT0 := by linarith [hpTailTiltT0_lt_one]
  have hqpos : 0 < q := by linarith
  have hratio : 1 ≤
      (q * hpTailTiltT0 ^ 2 * (3 - hpTailTiltT0)) /
        (1 - hpTailTiltT0) ^ 3 := by
    apply (le_div_iff₀ (by positivity : 0 < (1 - hpTailTiltT0) ^ 3)).2
    simpa using ht
  have hratioPow : 1 ≤
      ((q * hpTailTiltT0 ^ 2 * (3 - hpTailTiltT0)) /
          (1 - hpTailTiltT0) ^ 3) ^ j := one_le_pow₀ hratio
  have hscale := hpTail_tilt_scale_identity q j k
  have hW' : hpTailBinomialProduct j k * hpTailTiltT0 ^ (2 * j) *
      (1 - hpTailTiltT0) ^ (3 * k) ≤
      (3 - hpTailTiltT0) ^ (2 * j + 3 * k) := by
    have hW := hpTail_weighted_binomial_le hpTailTiltT0_pos.le hbpos.le j k
    convert hW using 1 <;> ring
  have hmiddle : (3 - hpTailTiltT0) ^ (2 * j + 3 * k) ≤
      hpTailTiltK ^ (j + k) * q ^ j * hpTailTiltT0 ^ (2 * j) *
        (1 - hpTailTiltT0) ^ (3 * k) := by
    rw [hscale]
    calc
      (3 - hpTailTiltT0) ^ (2 * j + 3 * k) =
          (3 - hpTailTiltT0) ^ (2 * j + 3 * k) * 1 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hratioPow (pow_nonneg hdpos.le _)
  have hDpos : 0 < q ^ j * hpTailTiltT0 ^ (2 * j) *
      (1 - hpTailTiltT0) ^ (3 * k) := by
    exact mul_pos (mul_pos (pow_pos hqpos _) (pow_pos hpTailTiltT0_pos _))
      (pow_pos hbpos _)
  have hscaled :
      (hpTailBinomialProduct j k * q⁻¹ ^ j) *
          (q ^ j * hpTailTiltT0 ^ (2 * j) * (1 - hpTailTiltT0) ^ (3 * k)) ≤
        hpTailTiltK ^ (j + k) *
          (q ^ j * hpTailTiltT0 ^ (2 * j) * (1 - hpTailTiltT0) ^ (3 * k)) := by
    calc
      _ = hpTailBinomialProduct j k *
            (hpTailTiltT0 ^ (2 * j) * (1 - hpTailTiltT0) ^ (3 * k)) := by
              simp [← mul_pow, hqpos.ne', mul_assoc, mul_left_comm, mul_comm]
      _ ≤ (3 - hpTailTiltT0) ^ (2 * j + 3 * k) := by
        convert hW' using 1 <;> ring
      _ ≤ _ := by convert hmiddle using 1 <;> ring
  have hbase : hpTailBinomialProduct j k * q⁻¹ ^ j ≤ hpTailTiltK ^ (j + k) :=
    le_of_mul_le_mul_right hscaled hDpos
  have hpref : 0 ≤ ((2 * j + 3 * k + 1 : ℕ) : ℝ) := by positivity
  simpa [mul_assoc] using mul_le_mul_of_nonneg_left hbase hpref

/-- The actual negative `C_n(1/q)` coefficient sum from the v13 residue
formula, using `q⁻¹` for the argument `1/q`. Source: v13
`hp-tail.tex:20-23, 226-256`. -/
def hpTailC (n : ℕ) (q : ℝ) : ℝ :=
  -∑ j ∈ range (n + 1), hpTailResidueMagnitude n j * q⁻¹ ^ j

/-- Saddle-free positive coefficient bound, valid uniformly for all real
`q ≥ 12`. This is the coefficient estimate needed from v13
`hp-tail.tex:226-256`; polynomial prefactors are retained explicitly. -/
theorem hpTail_C_bound (n : ℕ) (q : ℝ) (hq : 12 ≤ q) :
    |hpTailC n q| ≤ ((n + 1 : ℕ) : ℝ) * ((3 * n + 1 : ℕ) : ℝ) *
      hpTailTiltK ^ n := by
  have hqpos : 0 < q := by linarith
  have hterm (j : ℕ) (hj : j ∈ range (n + 1)) :
      hpTailResidueMagnitude n j * q⁻¹ ^ j ≤
        ((3 * n + 1 : ℕ) : ℝ) * hpTailTiltK ^ n := by
    have hjn : j ≤ n := by simp only [mem_range] at hj; omega
    let k := n - j
    have hsum : j + k = n := by dsimp [k]; omega
    have hmag : hpTailResidueMagnitude n j =
        ((2 * j + 3 * k + 1 : ℕ) : ℝ) * hpTailBinomialProduct j k := by
      rw [show n = j + k by omega]
      simpa [k, hpTailBinomialProduct] using
        (hpTail_residue_factor_real j k)
    rw [hmag]
    have htilt := hpTail_residue_tilted q hq j k
    have hcoef : 2 * j + 3 * k + 1 ≤ 3 * n + 1 := by
      dsimp [k]
      omega
    have hKnonneg : 0 ≤ hpTailTiltK ^ n := by
      norm_num [hpTailTiltK, hpTailTiltT0]
    have hcoefR : ((2 * j + 3 * k + 1 : ℕ) : ℝ) ≤
        ((3 * n + 1 : ℕ) : ℝ) := by exact_mod_cast hcoef
    calc
      ((2 * j + 3 * k + 1 : ℕ) : ℝ) * hpTailBinomialProduct j k * q⁻¹ ^ j ≤
          ((2 * j + 3 * k + 1 : ℕ) : ℝ) * hpTailTiltK ^ n := by
            simpa [hsum] using htilt
      _ ≤ ((3 * n + 1 : ℕ) : ℝ) * hpTailTiltK ^ n :=
        mul_le_mul_of_nonneg_right hcoefR hKnonneg
  have hsum_nonneg : 0 ≤
      ∑ j ∈ range (n + 1), hpTailResidueMagnitude n j * q⁻¹ ^ j := by
    apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (hpTailResidueMagnitude_pos n j).le
      (pow_nonneg (inv_nonneg.mpr hqpos.le) j)
  have hsum_bound := Finset.sum_le_sum (s := range (n + 1)) (fun j hj => hterm j hj)
  calc
    |hpTailC n q| = ∑ j ∈ range (n + 1),
        hpTailResidueMagnitude n j * q⁻¹ ^ j := by
          calc
            |hpTailC n q| = |∑ j ∈ range (n + 1),
                hpTailResidueMagnitude n j * q⁻¹ ^ j| := by
                  simp [hpTailC]
            _ = _ := abs_of_nonneg hsum_nonneg
    _ ≤ ∑ _j ∈ range (n + 1),
        ((3 * n + 1 : ℕ) : ℝ) * hpTailTiltK ^ n := hsum_bound
    _ = ((n + 1 : ℕ) : ℝ) * ((3 * n + 1 : ℕ) : ℝ) *
        hpTailTiltK ^ n := by
          simp [Finset.sum_const, Finset.card_range]
          ring

/-- Harmonic number `H_m = sum_{r=1}^m 1/r`, using a zero-based range.
Source: v13 `hp-tail.tex:17-23`. -/
def hpTailHarmonic (m : ℕ) : ℝ :=
  ∑ r ∈ range m, ((r + 1 : ℕ) : ℝ)⁻¹

lemma hpTail_harmonic_nonneg (m : ℕ) : 0 ≤ hpTailHarmonic m := by
  unfold hpTailHarmonic
  apply Finset.sum_nonneg
  intro r hr
  positivity

lemma hpTail_harmonic_le (m : ℕ) : hpTailHarmonic m ≤ (m : ℝ) := by
  induction m with
  | zero => simp [hpTailHarmonic]
  | succ m ih =>
      rw [hpTailHarmonic, Finset.sum_range_succ]
      change hpTailHarmonic m + ((m + 1 : ℕ) : ℝ)⁻¹ ≤ ((m + 1 : ℕ) : ℝ)
      have hden : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by
        have hdenNat : 1 ≤ m + 1 := by omega
        exact_mod_cast hdenNat
      have hterm : ((m + 1 : ℕ) : ℝ)⁻¹ ≤ 1 := by
        have h := one_div_le_one_div_of_le
          (show (0 : ℝ) < 1 by norm_num) hden
        simpa using h
      have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by norm_num
      rw [hcast] at hterm
      rw [hcast]
      nlinarith

/-- The harmonic multiplier in the simple residue `v_{n,j}=u_{n,j}(...)`.
Source: v13 `hp-tail.tex:20-23`. -/
def hpTailHarmonicFactor (n j : ℕ) : ℝ :=
  3 * hpTailHarmonic (n - j) - 2 * hpTailHarmonic j -
    hpTailHarmonic (3 * n + 1 - j)

/-- Coarse uniform bound for the residue's harmonic multiplier.  The constants
are deliberately loose; this is the polynomial factor in v13's positive
coefficient estimate at `hp-tail.tex:294-300`. -/
lemma hpTail_harmonicFactor_abs_le (n j : ℕ) (hj : j ≤ n) :
    |hpTailHarmonicFactor n j| ≤ ((8 * n + 1 : ℕ) : ℝ) := by
  have hA0 := hpTail_harmonic_nonneg (n - j)
  have hB0 := hpTail_harmonic_nonneg j
  have hC0 := hpTail_harmonic_nonneg (3 * n + 1 - j)
  have hA : hpTailHarmonic (n - j) ≤ (n : ℝ) := by
    calc
      hpTailHarmonic (n - j) ≤ ((n - j : ℕ) : ℝ) := hpTail_harmonic_le _
      _ ≤ (n : ℝ) := by exact_mod_cast Nat.sub_le n j
  have hB : hpTailHarmonic j ≤ (n : ℝ) := by
    calc
      hpTailHarmonic j ≤ (j : ℝ) := hpTail_harmonic_le _
      _ ≤ (n : ℝ) := by exact_mod_cast hj
  have hC : hpTailHarmonic (3 * n + 1 - j) ≤ ((3 * n + 1 : ℕ) : ℝ) := by
    calc
      hpTailHarmonic (3 * n + 1 - j) ≤ ((3 * n + 1 - j : ℕ) : ℝ) :=
        hpTail_harmonic_le _
      _ ≤ ((3 * n + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.sub_le (3 * n + 1) j
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hC
  unfold hpTailHarmonicFactor
  rw [abs_le]
  constructor
  · push_cast
    have hlow : -(5 * (n : ℝ) + 1) ≤
        3 * hpTailHarmonic (n - j) - 2 * hpTailHarmonic j -
          hpTailHarmonic (3 * n + 1 - j) := by
      have hAterm : 0 ≤ 3 * hpTailHarmonic (n - j) := by positivity
      have hBterm : -(2 * (n : ℝ)) ≤ -2 * hpTailHarmonic j := by
        have h := neg_le_neg hB
        nlinarith [h]
      have hCterm : -(3 * (n : ℝ) + 1) ≤
          -hpTailHarmonic (3 * n + 1 - j) := by
        simpa using neg_le_neg hC
      nlinarith [hAterm, hBterm, hCterm]
    nlinarith [hlow, hn0]
  · push_cast
    nlinarith [hn0, hA, hB0, hC0]

/-- The positive-base value of `B_n`, obtained by substituting the residue
formula `v_{n,j}=u_{n,j}(3H_{n-j}-2H_j-H_{3n+1-j})` and `z=1/q`.
Source: v13 `hp-tail.tex:20-23, 272-300`. -/
def hpTailB (n : ℕ) (q : ℝ) : ℝ :=
  -∑ j ∈ range (n + 1), hpTailResidueMagnitude n j *
    hpTailHarmonicFactor n j * q⁻¹ ^ j

/-- Polynomially weighted positive coefficient bound for `B_n(1/q)`, the
harmonic-factor counterpart of `hpTail_C_bound`.  Its exponential factor is
the same saddle-free rate from v13 `hp-tail.tex:294-300`. -/
theorem hpTail_B_bound (n : ℕ) (q : ℝ) (hq : 12 ≤ q) :
    |hpTailB n q| ≤ ((n + 1 : ℕ) : ℝ) * ((3 * n + 1 : ℕ) : ℝ) *
      ((8 * n + 1 : ℕ) : ℝ) * hpTailTiltK ^ n := by
  have hqpos : 0 < q := by linarith
  have hterm (j : ℕ) (hj : j ∈ range (n + 1)) :
      |hpTailResidueMagnitude n j * hpTailHarmonicFactor n j * q⁻¹ ^ j| ≤
        ((8 * n + 1 : ℕ) : ℝ) *
          (hpTailResidueMagnitude n j * q⁻¹ ^ j) := by
    have hjn : j ≤ n := by simp only [mem_range] at hj; omega
    have hfactor := hpTail_harmonicFactor_abs_le n j hjn
    have hmag : 0 ≤ hpTailResidueMagnitude n j :=
      (hpTailResidueMagnitude_pos n j).le
    have hpow : 0 ≤ q⁻¹ ^ j := pow_nonneg (inv_nonneg.mpr hqpos.le) j
    calc
      |hpTailResidueMagnitude n j * hpTailHarmonicFactor n j * q⁻¹ ^ j| =
          hpTailResidueMagnitude n j * |hpTailHarmonicFactor n j| * q⁻¹ ^ j := by
            rw [abs_mul, abs_mul, abs_of_nonneg hmag, abs_of_nonneg hpow]
      _ ≤ hpTailResidueMagnitude n j * ((8 * n + 1 : ℕ) : ℝ) * q⁻¹ ^ j := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hfactor hmag) hpow
      _ = ((8 * n + 1 : ℕ) : ℝ) *
          (hpTailResidueMagnitude n j * q⁻¹ ^ j) := by ring
  have htriangle :
      |hpTailB n q| ≤
        ∑ j ∈ range (n + 1),
          |hpTailResidueMagnitude n j * hpTailHarmonicFactor n j * q⁻¹ ^ j| := by
    calc
      |hpTailB n q| =
          |∑ j ∈ range (n + 1),
            hpTailResidueMagnitude n j * hpTailHarmonicFactor n j * q⁻¹ ^ j| := by
              simp [hpTailB]
      _ ≤ _ := Finset.abs_sum_le_sum_abs _ _
  have htermSum := Finset.sum_le_sum (s := range (n + 1)) (fun j hj => hterm j hj)
  have hsum_nonneg : 0 ≤
      ∑ j ∈ range (n + 1), hpTailResidueMagnitude n j * q⁻¹ ^ j := by
    apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (hpTailResidueMagnitude_pos n j).le
      (pow_nonneg (inv_nonneg.mpr hqpos.le) j)
  have hCsum :
      ∑ j ∈ range (n + 1), hpTailResidueMagnitude n j * q⁻¹ ^ j =
        |hpTailC n q| := by
    calc
      _ = |∑ j ∈ range (n + 1), hpTailResidueMagnitude n j * q⁻¹ ^ j| :=
        (abs_of_nonneg hsum_nonneg).symm
      _ = |hpTailC n q| := by simp [hpTailC]
  calc
    |hpTailB n q| ≤
        ∑ j ∈ range (n + 1),
          |hpTailResidueMagnitude n j * hpTailHarmonicFactor n j * q⁻¹ ^ j| :=
            htriangle
    _ ≤ ∑ j ∈ range (n + 1),
          ((8 * n + 1 : ℕ) : ℝ) *
            (hpTailResidueMagnitude n j * q⁻¹ ^ j) := htermSum
    _ = ((8 * n + 1 : ℕ) : ℝ) * |hpTailC n q| := by
      rw [← Finset.mul_sum, hCsum]
    _ ≤ ((8 * n + 1 : ℕ) : ℝ) *
        (((n + 1 : ℕ) : ℝ) * ((3 * n + 1 : ℕ) : ℝ) * hpTailTiltK ^ n) := by
      exact mul_le_mul_of_nonneg_left (hpTail_C_bound n q hq) (by positivity)
    _ = ((n + 1 : ℕ) : ℝ) * ((3 * n + 1 : ℕ) : ℝ) *
        ((8 * n + 1 : ℕ) : ℝ) * hpTailTiltK ^ n := by ring

end

end Li2Lean.B4
