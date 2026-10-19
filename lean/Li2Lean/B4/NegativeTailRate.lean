/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Mathlib

namespace Li2Lean.B4

noncomputable section

open Filter Topology

/-!
The negative-tail saddle and the fixed-base decay glue from v13
`hp-tail.tex:327-344, 360-374, 430-451`.  The contour estimate itself
supplies the geometric envelope; this file isolates the real algebra needed
after that estimate has been established.
-/

/-- The cubic equation for the positive number `s_-(q)` in the negative tail.
It is the sign-normalized form of `-s^3/q - 3s + 2 = 0`. -/
def hpSMinusCubic (q s : ℝ) : ℝ := s ^ 3 / q + 3 * s - 2

theorem hpSMinus_root_exists (q : ℝ) (hq : 0 < q) :
    ∃ s : ℝ, 0 < s ∧ s < 2 / 3 ∧ hpSMinusCubic q s = 0 := by
  have hcont : ContinuousOn (fun s : ℝ => hpSMinusCubic q s) (Set.Icc 0 (2 / 3)) := by
    unfold hpSMinusCubic
    fun_prop
  have hleft : hpSMinusCubic q 0 < 0 := by
    simp [hpSMinusCubic]
  have hright : 0 < hpSMinusCubic q (2 / 3) := by
    have hqterm : 0 < ((2 / 3 : ℝ) ^ 3) / q := by positivity
    dsimp [hpSMinusCubic]
    norm_num
    linarith
  have hzero : (0 : ℝ) ∈ Set.Icc (hpSMinusCubic q 0)
      (hpSMinusCubic q (2 / 3)) := ⟨le_of_lt hleft, le_of_lt hright⟩
  have himage := intermediate_value_Icc (a := (0 : ℝ)) (b := 2 / 3)
    (by norm_num) hcont hzero
  rcases himage with ⟨s, hs, hroot⟩
  have hsroot : hpSMinusCubic q s = 0 := hroot
  have hspos : 0 < s := by
    by_contra h
    have hsle : s ≤ 0 := le_of_not_gt h
    have hseq : s = 0 := le_antisymm hsle hs.1
    subst s
    simp [hpSMinusCubic] at hsroot
  have hslt : s < 2 / 3 := by
    by_contra h
    have hsge : 2 / 3 ≤ s := le_of_not_gt h
    have hseq : s = 2 / 3 := le_antisymm hs.2 hsge
    subst s
    norm_num [hpSMinusCubic] at hsroot
    exact hq.ne' hsroot
  exact ⟨s, hspos, hslt, hsroot⟩

/-- The selected negative-tail saddle root. -/
noncomputable def hpSMinusRoot (q : ℝ) (hq : 0 < q) : ℝ :=
  Classical.choose (hpSMinus_root_exists q hq)

theorem hpSMinusRoot_spec (q : ℝ) (hq : 0 < q) :
    0 < hpSMinusRoot q hq ∧ hpSMinusRoot q hq < 2 / 3 ∧
      hpSMinusCubic q (hpSMinusRoot q hq) = 0 :=
  Classical.choose_spec (hpSMinus_root_exists q hq)

/-- The explicit lower interval used for the `q=8` endpoint check. -/
theorem hpSMinusRoot_gt_6549_10000 {q : ℝ} (hq : (8 : ℝ) ≤ q) :
    (6549 / 10000 : ℝ) < hpSMinusRoot q (by linarith) := by
  have hqpos : 0 < q := by linarith
  let s := hpSMinusRoot q hqpos
  have hs := hpSMinusRoot_spec q hqpos
  by_contra hnot
  have hsle : s ≤ (6549 / 10000 : ℝ) := le_of_not_gt hnot
  have hdiff : 0 ≤ (6549 / 10000 : ℝ) - s := sub_nonneg.mpr hsle
  have hsnonneg : 0 ≤ s := hs.1.le
  have hsum : 0 ≤ (6549 / 10000 : ℝ) ^ 2 +
      (6549 / 10000 : ℝ) * s + s ^ 2 := by positivity
  have hcube : s ^ 3 ≤ (6549 / 10000 : ℝ) ^ 3 := by
    nlinarith [mul_nonneg hdiff hsum]
  have hdivq : s ^ 3 / q ≤ (6549 / 10000 : ℝ) ^ 3 / q := by
    exact div_le_div_of_nonneg_right hcube (le_of_lt hqpos)
  have hdiv8 : (6549 / 10000 : ℝ) ^ 3 / q ≤
      (6549 / 10000 : ℝ) ^ 3 / 8 := by
    apply (div_le_div_iff₀ hqpos (by norm_num : (0 : ℝ) < 8)).2
    have ha : 0 ≤ (6549 / 10000 : ℝ) ^ 3 := by positivity
    nlinarith
  have hupper : hpSMinusCubic q s ≤
      (6549 / 10000 : ℝ) ^ 3 / 8 + 3 * (6549 / 10000 : ℝ) - 2 := by
    dsimp [hpSMinusCubic]
    nlinarith [hdivq, hdiv8]
  have hnegative : (6549 / 10000 : ℝ) ^ 3 / 8 +
      3 * (6549 / 10000 : ℝ) - 2 < 0 := by norm_num
  have : hpSMinusCubic q s < 0 := lt_of_le_of_lt hupper hnegative
  exact (ne_of_gt this) hs.2.2.symm

/-- Mathlib's certified decimal enclosure for `exp 1` gives the coarse
bound needed by the endpoint rate check. -/
theorem hp_exp_four_lt_56 : Real.exp 4 < 56 := by
  calc
    Real.exp 4 = (Real.exp 1) ^ 4 := by
      norm_num
    _ < (2.7182818286 : ℝ) ^ 4 := by
      gcongr
      exact Real.exp_one_lt_d9
    _ < 56 := by norm_num

/-- The negative-tail rate in v13 equation `eq:hp-negative-coeff-rate`
after the denominator and coefficient factors are combined. -/
def hpRMinus (q : ℝ) (hq : 0 < q) : ℝ :=
  Real.exp 4 * (2 - 3 * hpSMinusRoot q hq) / 2

theorem hpRMinus_pos (q : ℝ) (hq : 0 < q) : 0 < hpRMinus q hq := by
  unfold hpRMinus
  have hs := hpSMinusRoot_spec q hq
  have hd : 0 < 2 - 3 * hpSMinusRoot q hq := by linarith [hs.2.1]
  positivity

/-- The endpoint `q=8` is strict; monotonicity in `q` is not needed here,
because the same root lower bound holds for every real `q ≥ 8`. -/
theorem hpRMinus_lt_one_of_ge_eight {q : ℝ} (hq : (8 : ℝ) ≤ q) :
    hpRMinus q (by linarith) < 1 := by
  have hqpos : 0 < q := by linarith
  let s := hpSMinusRoot q hqpos
  have hs := hpSMinusRoot_spec q hqpos
  have hslow : (6549 / 10000 : ℝ) < s :=
    hpSMinusRoot_gt_6549_10000 hq
  have hdpos : 0 < 2 - 3 * s := by linarith [hs.2.1]
  have hdlt : 2 - 3 * s < (353 / 10000 : ℝ) := by linarith
  have hprod₁ : Real.exp 4 * (2 - 3 * s) <
      56 * (2 - 3 * s) := by
    exact mul_lt_mul_of_pos_right hp_exp_four_lt_56 hdpos
  have hprod₂ : 56 * (2 - 3 * s) <
      56 * (353 / 10000 : ℝ) := by
    exact mul_lt_mul_of_pos_left hdlt (by norm_num)
  unfold hpRMinus
  dsimp [s] at hprod₁ hprod₂ ⊢
  nlinarith

/-- Fixed-base glue: any eventual geometric envelope with ratio below one
implies convergence to zero.  Contour/saddle modules only need to supply the
eventual envelope; this theorem performs the limit step used in `hp-tail.tex`.
-/
theorem hp_tendsto_zero_of_geometric_envelope {L : ℕ → ℝ} {C ρ : ℝ}
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hbound : ∀ᶠ n : ℕ in Filter.atTop, |L n| ≤ C * ρ ^ n) :
    Tendsto L Filter.atTop (𝓝 0) := by
  have hpow : Tendsto (fun n : ℕ => ρ ^ n) Filter.atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hρ hρ1
  have hgeom : Tendsto (fun n : ℕ => C * ρ ^ n) Filter.atTop (𝓝 0) := by
    simpa [mul_comm] using hpow.const_mul C
  have habs : Tendsto (fun n : ℕ => |L n|) Filter.atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall (fun n => abs_nonneg (L n))) hbound hgeom
  exact (tendsto_zero_iff_abs_tendsto_zero _).2 habs

end

end Li2Lean.B4
