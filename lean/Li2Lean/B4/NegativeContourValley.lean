/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B4.NegativeContourBottomLeft     -- hpNegValleyError, cpLog (via ContourSum)

open Complex Real Set MeasureTheory
open scoped BigOperators Interval

namespace Li2Lean.B4.NegContour

noncomputable section

open Li2Lean.P0.Config

/-! The master hypothesis
    `∀ ζ g, 1 ≤ g → (∀ u ∈ Icc 0 g, ζ + u ≠ 0) → -log (8 (g+1)) ≤ hpNegValleyError ζ g`
is FALSE: ζ = -1 + iε, g = 1 gives `hpNegValleyError = log ε - ∫₀¹ log|u-1+iε| du
≈ log ε + 1`, below `-log 16` for ε ≤ 0.02 (checked: ε = 0.02 gives -2.943 < -2.773).
The bottom producer only uses ζ with `ζ.im = n/5 ≥ 6`.  The lemma below needs
only `1 ≤ ζ.im` and gives the stronger bound `-log (g+1)`.

Proof idea (quasi-convexity, no turning-cell estimate needed):
  f(u) = log|ζ+u| satisfies f ≤ max(f k, f (k+1)) on [k, k+1]  (u ↦ (u+Re ζ)² convex),
  so each cell term t_k = f(k+1) - ∫_k^{k+1} f ≥ min(0, f(k+1) - f k).
  The sequence f k decreases then increases (it is monotone in |k + Re ζ|), so
  Σ_{k<g} t_k ≥ f m - f 0 for some m ≤ g, and f 0 - f m ≤ log(1 + m)
  because |ζ| ≤ |ζ+m| + m ≤ |ζ+m| (1+m) when |ζ+m| ≥ Im ζ ≥ 1. -/

theorem hp_neg_cp_norm_pos {ζ : ℂ} (hy : ζ.im ≠ 0) (u : ℝ) :
    0 < ‖ζ + (u : ℂ)‖ := by
  apply norm_pos_iff.2
  intro h
  apply hy
  have := congrArg Complex.im h
  simpa using this

/-- Quasi-convexity of `cpLog ζ` on a unit cell. -/
theorem hp_neg_cp_integral_le_max {ζ : ℂ} (hy : ζ.im ≠ 0) (a : ℝ) :
    (∫ u in a..a + 1, cpLog ζ u) ≤ max (cpLog ζ a) (cpLog ζ (a + 1)) := by
  have hb : ∀ u ∈ Set.Icc a (a + 1),
      cpLog ζ u ≤ max (cpLog ζ a) (cpLog ζ (a + 1)) := by
    intro u hu
    rcases le_total ((a + ζ.re) ^ 2) ((a + 1 + ζ.re) ^ 2) with h | h
    · -- 0 ≤ 2(a+re)+1, so (u+re)^2 ≤ (a+1+re)^2 on the cell
      have h1 : 0 ≤ a + 1 - u := by linarith [hu.2]
      have h2 : 0 ≤ (a + 1 + ζ.re) + (u + ζ.re) := by nlinarith [hu.1]
      have hsq : (u + ζ.re) ^ 2 ≤ (a + 1 + ζ.re) ^ 2 := by
        nlinarith [mul_nonneg h1 h2]
      exact (Real.log_le_log (hp_neg_cp_norm_pos hy u)
        (cp_norm_le ζ hsq)).trans (le_max_right _ _)
    · -- 2(a+re)+1 ≤ 0, so (u+re)^2 ≤ (a+re)^2 on the cell
      have h1 : 0 ≤ u - a := by linarith [hu.1]
      have h2 : (a + ζ.re) + (u + ζ.re) ≤ 0 := by nlinarith [hu.2]
      have hsq : (u + ζ.re) ^ 2 ≤ (a + ζ.re) ^ 2 := by
        nlinarith [mul_nonneg h1 (neg_nonneg.2 h2)]
      exact (Real.log_le_log (hp_neg_cp_norm_pos hy u)
        (cp_norm_le ζ hsq)).trans (le_max_left _ _)
  have h := intervalIntegral.integral_mono_on (f := cpLog ζ)
    (g := fun _ : ℝ => max (cpLog ζ a) (cpLog ζ (a + 1))) (by linarith)
    (cp_integrable ζ a (a + 1)) intervalIntegrable_const hb
  simpa using h

/-- Strict increase of `f` across a cell forces the increasing phase. -/
theorem hp_neg_cp_phase_of_lt {ζ : ℂ} (hy : ζ.im ≠ 0) {a : ℝ}
    (hlt : cpLog ζ a < cpLog ζ (a + 1)) : -(1 / 2 : ℝ) ≤ a + ζ.re := by
  by_contra hneg
  push_neg at hneg
  have hsq : (a + 1 + ζ.re) ^ 2 ≤ (a + ζ.re) ^ 2 := by nlinarith
  have := Real.log_le_log (hp_neg_cp_norm_pos hy (a + 1)) (cp_norm_le ζ hsq)
  unfold cpLog at hlt
  linarith

/-- In the increasing phase the next value is not smaller. -/
theorem hp_neg_cp_le_of_phase {ζ : ℂ} (hy : ζ.im ≠ 0) {a : ℝ}
    (hph : -(1 / 2 : ℝ) ≤ a + ζ.re) : cpLog ζ a ≤ cpLog ζ (a + 1) := by
  have hsq : (a + ζ.re) ^ 2 ≤ (a + 1 + ζ.re) ^ 2 := by nlinarith
  exact Real.log_le_log (hp_neg_cp_norm_pos hy a) (cp_norm_le ζ hsq)

/-- Telescoping invariant (mirror of the `key` induction in
`cp_sum_sub_integral`, P0/ConfigFgBound.lean:193). -/
theorem hp_neg_valley_key {ζ : ℂ} (hy : ζ.im ≠ 0) :
    ∀ N : ℕ,
      (cpLog ζ (N : ℝ) - cpLog ζ 0 ≤
        ∑ k ∈ Finset.range N,
          (cpLog ζ ((k : ℝ) + 1) - ∫ u in (k : ℝ)..(k : ℝ) + 1, cpLog ζ u)) ∨
      ∃ m : ℕ, m ≤ N ∧ -(1 / 2 : ℝ) ≤ (N : ℝ) + ζ.re ∧
        cpLog ζ (m : ℝ) - cpLog ζ 0 ≤
          ∑ k ∈ Finset.range N,
            (cpLog ζ ((k : ℝ) + 1) - ∫ u in (k : ℝ)..(k : ℝ) + 1, cpLog ζ u) := by
  intro N
  induction N with
  | zero => left; simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have hcell := hp_neg_cp_integral_le_max hy (N : ℝ)
    push_cast
    rcases ih with h | ⟨m, hm, hph, h⟩
    · by_cases hd : cpLog ζ ((N : ℝ) + 1) ≤ cpLog ζ (N : ℝ)
      · left
        rw [max_eq_left hd] at hcell
        linarith
      · right
        push_neg at hd
        have hph := hp_neg_cp_phase_of_lt hy hd
        rw [max_eq_right hd.le] at hcell
        exact ⟨N, by omega, by linarith, by linarith⟩
    · right
      have hle := hp_neg_cp_le_of_phase hy hph
      rw [max_eq_right hle] at hcell
      exact ⟨m, by omega, by linarith, by linarith⟩

/-- `f 0 - f m ≤ log (m+1)` once `1 ≤ Im ζ`. -/
theorem hp_neg_cp_drop_le {ζ : ℂ} (hy : 1 ≤ ζ.im) (m : ℕ) :
    cpLog ζ 0 - cpLog ζ (m : ℝ) ≤ Real.log ((m : ℝ) + 1) := by
  have hy0 : ζ.im ≠ 0 := by linarith
  have hpos := hp_neg_cp_norm_pos hy0 (m : ℝ)
  have hpos0 := hp_neg_cp_norm_pos hy0 0
  have hge1 : 1 ≤ ‖ζ + ((m : ℝ) : ℂ)‖ := by
    have h := Complex.abs_im_le_norm (ζ + ((m : ℝ) : ℂ))
    have him : (ζ + ((m : ℝ) : ℂ)).im = ζ.im := by simp
    rw [him, abs_of_pos (by linarith)] at h
    linarith
  have htri : ‖ζ + ((0 : ℝ) : ℂ)‖ ≤ ‖ζ + ((m : ℝ) : ℂ)‖ * ((m : ℝ) + 1) := by
    have hz : ζ + ((0 : ℝ) : ℂ) = (ζ + ((m : ℝ) : ℂ)) - ((m : ℝ) : ℂ) := by
      push_cast; ring
    rw [hz]
    refine (norm_sub_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg m)]
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) m) (sub_nonneg.2 hge1)]
  have hlog := Real.log_le_log hpos0 htri
  rw [Real.log_mul hpos.ne' (by positivity)] at hlog
  unfold cpLog
  linarith

/-- A1.  Restricted valley lower bound (stronger than the master target). -/
theorem hp_neg_valley_lower_of_im {ζ : ℂ} (hy : 1 ≤ ζ.im) (g : ℕ) :
    -Real.log ((g : ℝ) + 1) ≤ hpNegValleyError ζ g := by
  have hy0 : ζ.im ≠ 0 := by linarith
  have hsplit : (∫ u in (0 : ℝ)..(g : ℝ), cpLog ζ u) =
      ∑ k ∈ Finset.range g, ∫ u in (k : ℝ)..(k : ℝ) + 1, cpLog ζ u := by
    have h := intervalIntegral.sum_integral_adjacent_intervals (f := cpLog ζ)
      (μ := volume) (a := fun k : ℕ => (k : ℝ)) (n := g)
      (fun k _ => cp_integrable ζ _ _)
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero] at h
    exact h.symm
  have hE : hpNegValleyError ζ g =
      ∑ k ∈ Finset.range g,
        (cpLog ζ ((k : ℝ) + 1) - ∫ u in (k : ℝ)..(k : ℝ) + 1, cpLog ζ u) := by
    rw [hp_neg_valley_error_eq_sum_sub_integral, hsplit, ← Finset.sum_sub_distrib]
  have hexists : ∃ m : ℕ, m ≤ g ∧
      cpLog ζ (m : ℝ) - cpLog ζ 0 ≤ hpNegValleyError ζ g := by
    rw [hE]
    rcases hp_neg_valley_key hy0 g with h | ⟨m, hm, _, h⟩
    · exact ⟨g, le_rfl, h⟩
    · exact ⟨m, hm, h⟩
  obtain ⟨m, hm, h⟩ := hexists
  have hdrop := hp_neg_cp_drop_le hy m
  have hmono : Real.log ((m : ℝ) + 1) ≤ Real.log ((g : ℝ) + 1) :=
    Real.log_le_log (by positivity) (by exact_mod_cast Nat.add_le_add_right hm 1)
  linarith

/-- The exact shape consumed by the (restricted) bottom producer. -/
theorem hp_neg_valley_lower_restricted :
    ∀ (ζ : ℂ) (g : ℕ), 1 ≤ g → 1 ≤ ζ.im →
      -Real.log (8 * ((g : ℝ) + 1)) ≤ hpNegValleyError ζ g := by
  intro ζ g _ hy
  have h := hp_neg_valley_lower_of_im hy g
  have hmono : Real.log ((g : ℝ) + 1) ≤ Real.log (8 * ((g : ℝ) + 1)) :=
    Real.log_le_log (by positivity) (by nlinarith [Nat.cast_nonneg (α := ℝ) g])
  linarith

end

end Li2Lean.B4.NegContour

#print axioms Li2Lean.B4.NegContour.hp_neg_valley_lower_of_im
#print axioms Li2Lean.B4.NegContour.hp_neg_valley_lower_restricted
