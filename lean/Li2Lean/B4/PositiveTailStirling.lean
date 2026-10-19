/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Tactic
import Li2Lean.P0.ConfigSelfStirling

namespace Li2Lean.B4

noncomputable section

/-- The entropy function in v13 `hp-tail.tex:227-235`, with `log 0 = 0`
implementing its `0 log 0 = 0` endpoint convention. -/
def hpTailEntropy (q x : ℝ) : ℝ :=
  (3 - x) * Real.log (3 - x) - 2 * x * Real.log x -
    3 * (1 - x) * Real.log (1 - x) - x * Real.log q

/-- The factorial main term `m log m - m` used on the residue formula
`hp-tail.tex:20-22` in the estimate at `hp-tail.tex:230-235`. -/
def hpTailMain (m : ℕ) : ℝ :=
  (m : ℝ) * Real.log (m : ℝ) - (m : ℝ)

def hpTailMainReal (x : ℝ) : ℝ := x * Real.log x - x

def hpTailStirlingConstant : ℝ :=
  1 + Real.log (2 * Real.pi) / 2 + 1 / 12

lemma hpTailStirlingConstant_nonneg : 0 ≤ hpTailStirlingConstant := by
  have hpi : (1 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
  have hlog : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg hpi
  unfold hpTailStirlingConstant
  nlinarith

/-- Endpoint-safe weighted scaling. The weight on the left is essential:
the unweighted identity `x*log (N*x) = N*x*log x + N*x*log N` is false. -/
lemma hpTailMainReal_scale (N x : ℝ) (hN : 0 < N) (hx : 0 ≤ x) :
    hpTailMainReal (N * x) = N * hpTailMainReal x + (N * x) * Real.log N := by
  by_cases hx0 : x = 0
  · subst x
    simp [hpTailMainReal]
  · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    rw [hpTailMainReal, hpTailMainReal, Real.log_mul hN.ne' hxpos.ne']
    ring

lemma hpTail_factorialMain_le (m : ℕ) :
    hpTailMain m ≤ Real.log (m.factorial : ℝ) := by
  by_cases hm : m = 0
  · subst m
    norm_num [hpTailMain]
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    have hmR : (1 : ℝ) ≤ (m : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm
    have hlogm : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg hmR
    have hpi : (1 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
    have hlogpi : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg hpi
    have h := Stirling.le_log_factorial_stirling (n := m) hm
    have h' :
        (m : ℝ) * Real.log (m : ℝ) - (m : ℝ) +
          Real.log (m : ℝ) / 2 + Real.log (2 * Real.pi) / 2 ≤
        Real.log (m.factorial : ℝ) := by
      simpa using h
    unfold hpTailMain
    linarith

lemma hpTail_logFactorial_sub_main_le (m : ℕ) :
    Real.log (m.factorial : ℝ) - hpTailMain m ≤
      Real.log ((m + 1 : ℕ) : ℝ) + hpTailStirlingConstant := by
  by_cases hm : m = 0
  · subst m
    simpa [hpTailMain] using hpTailStirlingConstant_nonneg
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    have hmain := Li2Lean.P0.Config.SelfCells.log_factorial_stirling_upper m hmpos
    have hupper :
        Real.log (m.factorial : ℝ) - hpTailMain m ≤
          Real.log (m : ℝ) / 2 + Real.log (2 * Real.pi) / 2 +
            1 / (12 * (m : ℝ)) := by
      unfold hpTailMain
      linarith [hmain]
    have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hmpos
    have hmRle : (m : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_succ m
    have hlogm : 0 ≤ Real.log (m : ℝ) :=
      Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm)
    have hlogle : Real.log (m : ℝ) ≤ Real.log ((m + 1 : ℕ) : ℝ) :=
      Real.log_le_log hmR hmRle
    have hrem : (1 : ℝ) / (12 * (m : ℝ)) ≤ 1 / 12 := by
      have hmge : (1 : ℝ) ≤ (m : ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm
      have h := one_div_le_one_div_of_le
        (show (0 : ℝ) < 12 by norm_num)
        (show (12 : ℝ) ≤ 12 * (m : ℝ) by nlinarith)
      simpa [div_eq_mul_inv] using h
    unfold hpTailStirlingConstant
    linarith

/-- Uniform factorial error, with `m=0` discharged separately. This is the
generic interface needed for v13 `hp-tail.tex:230-236`. -/
lemma hpTail_factorialError_bounds (m : ℕ) :
    0 ≤ Real.log (m.factorial : ℝ) - hpTailMain m ∧
      Real.log (m.factorial : ℝ) - hpTailMain m ≤
        Real.log ((m + 1 : ℕ) : ℝ) + hpTailStirlingConstant := by
  constructor
  · exact sub_nonneg.mpr (hpTail_factorialMain_le m)
  · exact hpTail_logFactorial_sub_main_le m

def hpTailEntropyCore (x : ℝ) : ℝ :=
  (3 - x) * Real.log (3 - x) - 2 * x * Real.log x -
    3 * (1 - x) * Real.log (1 - x)

/-- Exact entropy cancellation from the factorial ratio in v13
`hp-tail.tex:20-22` and phase at `hp-tail.tex:227-235`. -/
lemma hpTail_entropy_identity (n j : ℕ) (hn : 0 < n) (hj : j ≤ n) :
    (n : ℝ) * hpTailEntropyCore ((j : ℝ) / n) =
      hpTailMain (3 * n - j) - 2 * hpTailMain j - 3 * hpTailMain (n - j) := by
  let x : ℝ := (j : ℝ) / n
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hjR : (j : ℝ) ≤ (n : ℝ) := by exact_mod_cast hj
  have hx0 : 0 ≤ x := by
    dsimp [x]
    positivity
  have hx1 : x ≤ 1 := by
    dsimp [x]
    exact (div_le_one hnR).2 hjR
  have h1x0 : 0 ≤ 1 - x := by linarith
  have h3x0 : 0 ≤ 3 - x := by linarith
  have hJ : (n : ℝ) * x = (j : ℝ) := by
    dsimp [x]
    field_simp
  have hK : (n : ℝ) * (1 - x) = (n : ℝ) - (j : ℝ) := by
    dsimp [x]
    field_simp
  have hZ : (n : ℝ) * (3 - x) = 3 * (n : ℝ) - (j : ℝ) := by
    dsimp [x]
    field_simp
  have hj3 : j ≤ 3 * n := by omega
  have hKcast : ((n - j : ℕ) : ℝ) = (n : ℝ) - (j : ℝ) :=
    Nat.cast_sub hj
  have hZcast : ((3 * n - j : ℕ) : ℝ) = 3 * (n : ℝ) - (j : ℝ) := by
    rw [Nat.cast_sub hj3]
    push_cast
    rfl
  have hZscale := hpTailMainReal_scale (n : ℝ) (3 - x) hnR h3x0
  rw [hZ] at hZscale
  have hJscale := hpTailMainReal_scale (n : ℝ) x hnR hx0
  rw [hJ] at hJscale
  have hKscale := hpTailMainReal_scale (n : ℝ) (1 - x) hnR h1x0
  rw [hK] at hKscale
  have hbalance :
      (3 * (n : ℝ) - (j : ℝ)) - 2 * (j : ℝ) -
        3 * ((n : ℝ) - (j : ℝ)) = 0 := by ring
  rw [hpTailMain, hpTailMain, hpTailMain, hZcast, hKcast]
  change (n : ℝ) * hpTailEntropyCore x = _
  unfold hpTailEntropyCore
  unfold hpTailMainReal at hZscale hJscale hKscale
  calc
    (n : ℝ) *
        ((3 - x) * Real.log (3 - x) - 2 * x * Real.log x -
          3 * (1 - x) * Real.log (1 - x)) =
      (n : ℝ) * ((3 - x) * Real.log (3 - x) - (3 - x)) -
        2 * ((n : ℝ) * (x * Real.log x - x)) -
        3 * ((n : ℝ) * ((1 - x) * Real.log (1 - x) - (1 - x))) := by ring
    _ = ((3 * (n : ℝ) - (j : ℝ)) * Real.log (3 * (n : ℝ) - (j : ℝ)) -
          (3 * (n : ℝ) - (j : ℝ))) -
        2 * ((j : ℝ) * Real.log (j : ℝ) - (j : ℝ)) -
        3 * (((n : ℝ) - (j : ℝ)) * Real.log ((n : ℝ) - (j : ℝ)) -
          ((n : ℝ) - (j : ℝ))) := by
      calc
        (n : ℝ) * ((3 - x) * Real.log (3 - x) - (3 - x)) -
              2 * ((n : ℝ) * (x * Real.log x - x)) -
              3 * ((n : ℝ) * ((1 - x) * Real.log (1 - x) - (1 - x))) =
            ((n : ℝ) * ((3 - x) * Real.log (3 - x) - (3 - x)) +
                (3 * (n : ℝ) - (j : ℝ)) * Real.log (n : ℝ)) -
              2 * ((n : ℝ) * (x * Real.log x - x) +
                (j : ℝ) * Real.log (n : ℝ)) -
              3 * ((n : ℝ) * ((1 - x) * Real.log (1 - x) - (1 - x)) +
                ((n : ℝ) - (j : ℝ)) * Real.log (n : ℝ)) := by
          nlinarith [hbalance]
        _ = ((3 * (n : ℝ) - (j : ℝ)) * Real.log (3 * (n : ℝ) - (j : ℝ)) -
              (3 * (n : ℝ) - (j : ℝ))) -
            2 * ((j : ℝ) * Real.log (j : ℝ) - (j : ℝ)) -
            3 * (((n : ℝ) - (j : ℝ)) * Real.log ((n : ℝ) - (j : ℝ)) -
              ((n : ℝ) - (j : ℝ))) := by
          rw [← hZscale, ← hJscale, ← hKscale]
    _ = _ := by ring

/-- The numerator's one-step main-term shift, accounting for the `+1` in
v13's `(3n+1-j)!` at `hp-tail.tex:20-22`. -/
lemma hpTail_main_shift (z : ℕ) :
    -1 ≤ hpTailMain (z + 1) - hpTailMain z ∧
      hpTailMain (z + 1) - hpTailMain z ≤ Real.log ((z + 1 : ℕ) : ℝ) := by
  by_cases hz : z = 0
  · subst z
    norm_num [hpTailMain]
  · have hzpos : 0 < z := Nat.pos_of_ne_zero hz
    have hzR : 0 < (z : ℝ) := Nat.cast_pos.mpr hzpos
    have hsucc : ((z + 1 : ℕ) : ℝ) = (z : ℝ) + 1 := by norm_num
    have hratio :
        1 ≤ ((z + 1 : ℕ) : ℝ) / (z : ℝ) := by
      rw [hsucc]
      apply (le_div_iff₀ hzR).2
      nlinarith
    have hlogratio0 :
        0 ≤ Real.log (((z + 1 : ℕ) : ℝ) / (z : ℝ)) :=
      Real.log_nonneg hratio
    have hlogratio1 :
        Real.log (((z + 1 : ℕ) : ℝ) / (z : ℝ)) ≤ 1 / (z : ℝ) := by
      have h := Real.log_le_sub_one_of_pos
        (x := ((z + 1 : ℕ) : ℝ) / (z : ℝ))
        (div_pos (by positivity) hzR)
      have hdiff : ((z + 1 : ℕ) : ℝ) / (z : ℝ) - 1 = 1 / (z : ℝ) := by
        rw [hsucc]
        field_simp
        ring
      linarith
    have hlogdiv :
        Real.log (((z + 1 : ℕ) : ℝ) / (z : ℝ)) =
          Real.log ((z + 1 : ℕ) : ℝ) - Real.log (z : ℝ) :=
      Real.log_div (by positivity) hzR.ne'
    have hshift : hpTailMain (z + 1) - hpTailMain z =
        Real.log ((z + 1 : ℕ) : ℝ) +
          (z : ℝ) * Real.log (((z + 1 : ℕ) : ℝ) / (z : ℝ)) - 1 := by
      rw [hpTailMain, hpTailMain, hlogdiv, hsucc]
      ring
    have hlogZ : 0 ≤ Real.log ((z + 1 : ℕ) : ℝ) :=
      Real.log_nonneg (by rw [hsucc]; linarith)
    have hproduct0 :
        0 ≤ (z : ℝ) *
          Real.log (((z + 1 : ℕ) : ℝ) / (z : ℝ)) :=
      mul_nonneg (le_of_lt hzR) hlogratio0
    have hproduct1 :
        (z : ℝ) *
          Real.log (((z + 1 : ℕ) : ℝ) / (z : ℝ)) ≤ 1 := by
      have hmul := mul_le_mul_of_nonneg_left hlogratio1 (le_of_lt hzR)
      have hrecip : (z : ℝ) * (1 / (z : ℝ)) = 1 := by field_simp
      linarith
    constructor <;> rw [hshift] <;> linarith

def hpTailResidueMagnitude (n j : ℕ) : ℝ :=
  (Nat.factorial (3 * n + 1 - j) : ℝ) /
    ((Nat.factorial j : ℝ) ^ 2 * (Nat.factorial (n - j) : ℝ) ^ 3)

lemma hpTailResidueMagnitude_pos (n j : ℕ) :
    0 < hpTailResidueMagnitude n j := by
  unfold hpTailResidueMagnitude
  positivity

lemma hpTail_logResidueMagnitude (n j : ℕ) :
    Real.log (hpTailResidueMagnitude n j) =
      Real.log (Nat.factorial (3 * n + 1 - j) : ℝ) -
        2 * Real.log (Nat.factorial j : ℝ) -
        3 * Real.log (Nat.factorial (n - j) : ℝ) := by
  unfold hpTailResidueMagnitude
  rw [Real.log_div (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_pow,
    Real.log_pow]
  ring

/-- Uniform effective Stirling estimate for the positive tail in v13
`hp-tail.tex:217-235`, using the exact residue formula at `:20-22`. -/
theorem hp_positive_tail_stirling_uniform
    (q : ℝ) (hq : 1 < q) (n j : ℕ) (hn : 0 < n) (hj : j ≤ n) :
    |Real.log (hpTailResidueMagnitude n j) - (j : ℝ) * Real.log q -
        (n : ℝ) * hpTailEntropy q ((j : ℝ) / n)| ≤
      6 * (Real.log (4 * ((n + 1 : ℕ) : ℝ)) +
        hpTailStirlingConstant + 1) := by
  let z : ℕ := 3 * n - j
  have hj3 : j ≤ 3 * n := by omega
  have hshift : z + 1 = 3 * n + 1 - j := by
    dsimp [z]
    omega
  have hqcancel :
      (n : ℝ) * hpTailEntropy q ((j : ℝ) / n) =
        (n : ℝ) * hpTailEntropyCore ((j : ℝ) / n) -
          (j : ℝ) * Real.log q := by
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
    have hmul : (n : ℝ) * ((j : ℝ) / n) = (j : ℝ) := by
      field_simp
    change (n : ℝ) *
        (hpTailEntropyCore ((j : ℝ) / n) -
          ((j : ℝ) / n) * Real.log q) = _
    rw [mul_sub]
    calc
      (n : ℝ) * hpTailEntropyCore ((j : ℝ) / n) -
          (n : ℝ) * (((j : ℝ) / n) * Real.log q) =
        (n : ℝ) * hpTailEntropyCore ((j : ℝ) / n) -
          ((n : ℝ) * ((j : ℝ) / n)) * Real.log q := by ring
      _ = _ := by rw [hmul]
  have hentropy := hpTail_entropy_identity n j hn hj
  have hdecomp :
      Real.log (hpTailResidueMagnitude n j) - (j : ℝ) * Real.log q -
          (n : ℝ) * hpTailEntropy q ((j : ℝ) / n) =
        (hpTailMain (z + 1) - hpTailMain z) +
          (Real.log ((z + 1).factorial : ℝ) - hpTailMain (z + 1)) -
          2 * (Real.log (j.factorial : ℝ) - hpTailMain j) -
          3 * (Real.log ((n - j).factorial : ℝ) - hpTailMain (n - j)) := by
    rw [hpTail_logResidueMagnitude, ← hshift, hqcancel, hentropy]
    ring
  have hshiftBounds := hpTail_main_shift z
  have hEN := hpTail_factorialError_bounds (z + 1)
  have hEJ := hpTail_factorialError_bounds j
  have hEK := hpTail_factorialError_bounds (n - j)
  let L : ℝ := Real.log (4 * ((n + 1 : ℕ) : ℝ))
  let B : ℝ := L + hpTailStirlingConstant
  have hL : 0 ≤ L := by
    dsimp [L]
    apply Real.log_nonneg
    have hn1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    have : (1 : ℝ) ≤ 4 * ((n + 1 : ℕ) : ℝ) := by nlinarith
    exact this
  have hC : 0 ≤ hpTailStirlingConstant := hpTailStirlingConstant_nonneg
  have hB : 0 ≤ B := add_nonneg hL hC
  have hzBound : z + 2 ≤ 4 * (n + 1) := by
    dsimp [z]
    omega
  have hJBound : j + 1 ≤ 4 * (n + 1) := by omega
  have hKBound : n - j + 1 ≤ 4 * (n + 1) := by omega
  have hlogZ : Real.log ((z + 2 : ℕ) : ℝ) ≤ L := by
    dsimp [L]
    apply Real.log_le_log (by positivity)
    exact_mod_cast hzBound
  have hlogJ : Real.log ((j + 1 : ℕ) : ℝ) ≤ L := by
    dsimp [L]
    apply Real.log_le_log (by positivity)
    exact_mod_cast hJBound
  have hlogK : Real.log ((n - j + 1 : ℕ) : ℝ) ≤ L := by
    dsimp [L]
    apply Real.log_le_log (by positivity)
    exact_mod_cast hKBound
  have hENB : Real.log ((z + 1).factorial : ℝ) - hpTailMain (z + 1) ≤ B := by
    have h := hEN.2
    have harg : ((z + 1 + 1 : ℕ) : ℝ) = ((z + 2 : ℕ) : ℝ) := by
      ring
    rw [harg] at h
    dsimp [B]
    exact h.trans (add_le_add_left hlogZ _)
  have hEJB : Real.log (j.factorial : ℝ) - hpTailMain j ≤ B := by
    dsimp [B]
    exact hEJ.2.trans (add_le_add_left hlogJ _)
  have hEKB : Real.log ((n - j).factorial : ℝ) - hpTailMain (n - j) ≤ B := by
    dsimp [B]
    exact hEK.2.trans (add_le_add_left hlogK _)
  have hD := hdecomp
  rw [hdecomp]
  have hshiftUpper : hpTailMain (z + 1) - hpTailMain z ≤ L := by
    have h := hshiftBounds.2
    have harg : ((z + 1 : ℕ) : ℝ) ≤ ((z + 2 : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_succ (z + 1)
    have hlog := Real.log_le_log (by positivity) harg
    exact h.trans (hlog.trans hlogZ)
  have hshiftLower : -1 ≤ hpTailMain (z + 1) - hpTailMain z := hshiftBounds.1
  have hEN0 := hEN.1
  have hEJ0 := hEJ.1
  have hEK0 := hEK.1
  have hupper :
      (hpTailMain (z + 1) - hpTailMain z) +
          (Real.log ((z + 1).factorial : ℝ) - hpTailMain (z + 1)) -
          2 * (Real.log (j.factorial : ℝ) - hpTailMain j) -
          3 * (Real.log ((n - j).factorial : ℝ) - hpTailMain (n - j)) ≤
        6 * (L + hpTailStirlingConstant + 1) := by
    have hupper0 :
        (hpTailMain (z + 1) - hpTailMain z) +
            (Real.log ((z + 1).factorial : ℝ) - hpTailMain (z + 1)) -
            2 * (Real.log (j.factorial : ℝ) - hpTailMain j) -
            3 * (Real.log ((n - j).factorial : ℝ) - hpTailMain (n - j)) ≤
          L + B := by linarith
    calc
      _ ≤ L + B := hupper0
      _ ≤ 6 * (L + hpTailStirlingConstant + 1) := by
        dsimp [B]
        nlinarith [hL, hC]
  have hlower :
      -6 * (L + hpTailStirlingConstant + 1) ≤
        (hpTailMain (z + 1) - hpTailMain z) +
          (Real.log ((z + 1).factorial : ℝ) - hpTailMain (z + 1)) -
          2 * (Real.log (j.factorial : ℝ) - hpTailMain j) -
          3 * (Real.log ((n - j).factorial : ℝ) - hpTailMain (n - j)) := by
    have hlower0 :
        -1 - 5 * B ≤
          (hpTailMain (z + 1) - hpTailMain z) +
            (Real.log ((z + 1).factorial : ℝ) - hpTailMain (z + 1)) -
            2 * (Real.log (j.factorial : ℝ) - hpTailMain j) -
            3 * (Real.log ((n - j).factorial : ℝ) - hpTailMain (n - j)) := by
      linarith
    calc
      -6 * (L + hpTailStirlingConstant + 1) ≤ -1 - 5 * B := by
        dsimp [B]
        nlinarith [hL, hC]
      _ ≤ _ := hlower0
  have habs := abs_le.mpr ⟨(by nlinarith [hlower] :
      -(6 * (L + hpTailStirlingConstant + 1)) ≤
        (hpTailMain (z + 1) - hpTailMain z) +
          (Real.log ((z + 1).factorial : ℝ) - hpTailMain (z + 1)) -
          2 * (Real.log (j.factorial : ℝ) - hpTailMain j) -
          3 * (Real.log ((n - j).factorial : ℝ) - hpTailMain (n - j))), hupper⟩
  simpa [L] using habs

end

end Li2Lean.B4
