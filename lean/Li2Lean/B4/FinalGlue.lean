/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.Kit.EndpointCriterion

open Filter Topology

namespace Li2Lean.B4

/-!
This is the final integer-smallness closure from the v13 tail argument.
It consumes the actual integer affine form, its decay, and the no-adjacent-zero
statement; it does not assert that those B4 inputs have already been proved.
Source: output/li2-alln-paper-v13/source/chapters/hp-tail.tex:561-566.
-/
theorem irrational_of_integer_affine_forms_tendsto_zero
    {x : ℝ} (X Y : ℕ → ℤ) (L : ℕ → ℝ)
    (hform : ∀ n, L n = (X n : ℝ) + (Y n : ℝ) * x)
    (hsmall : Tendsto L atTop (𝓝 0))
    (hnoadj : ∀ n, ¬ (L n = 0 ∧ L (n + 1) = 0)) :
    Irrational x := by
  by_contra hrat
  obtain ⟨a, b, hb, hx⟩ := ContourKit.endpoint_not_irrational_rep hrat
  have hbR : 0 < (b : ℝ) := by exact_mod_cast hb
  let integerForm (n : ℕ) : ℤ := (b : ℤ) * X n + a * Y n
  have hscale (n : ℕ) : (integerForm n : ℝ) = (b : ℝ) * L n := by
    dsimp [integerForm]
    rw [hform n, hx]
    push_cast
    field_simp
  have hscaled : Tendsto (fun n : ℕ => (b : ℝ) * L n) atTop (𝓝 0) := by
    simpa using hsmall.const_mul (b : ℝ)
  have hintegerForm : Tendsto (fun n : ℕ => (integerForm n : ℝ)) atTop (𝓝 0) := by
    have heq : (fun n : ℕ => (integerForm n : ℝ)) =
        fun n => (b : ℝ) * L n := funext hscale
    rw [heq]
    exact hscaled
  have hsmallEventually : ∀ᶠ n : ℕ in atTop,
      |(integerForm n : ℝ)| < 1 := by
    filter_upwards [hintegerForm.eventually
      (Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0)
        (by norm_num : (0 : ℝ) < 1))] with n hn
    exact abs_lt.mpr hn
  have hzeroEventually : ∀ᶠ n : ℕ in atTop, integerForm n = 0 := by
    filter_upwards [hsmallEventually] with n hn
    by_contra hne
    have hnInt : |integerForm n| < 1 := by exact_mod_cast hn
    exact ContourKit.no_nonzero_integer_abs_lt_one hne hnInt
  have hLzeroEventually : ∀ᶠ n : ℕ in atTop, L n = 0 := by
    filter_upwards [hzeroEventually] with n hn
    have hmul : (b : ℝ) * L n = 0 := by
      rw [← hscale n]
      exact_mod_cast hn
    rcases mul_eq_zero.mp hmul with hb0 | hLn
    · exact False.elim ((ne_of_gt hbR) hb0)
    · exact hLn
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hLzeroEventually
  exact hnoadj N ⟨hN N le_rfl, hN (N + 1) (by omega)⟩

end Li2Lean.B4
