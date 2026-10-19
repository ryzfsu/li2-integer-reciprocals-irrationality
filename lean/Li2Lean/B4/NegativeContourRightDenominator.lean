/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B4.NegativeContourRightProduct

open Complex Real Set
open scoped BigOperators Interval

namespace Li2Lean.B4.NegContour

noncomputable section

private theorem finset_prod_mono_nonneg {ι : Type} {s : Finset ι}
    {f g : ι → ℝ} (hf : ∀ i ∈ s, 0 ≤ f i)
    (hg : ∀ i ∈ s, 0 ≤ g i)
    (hfg : ∀ i ∈ s, f i ≤ g i) :
    s.prod f ≤ s.prod g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hga : 0 ≤ g a := hg a (Finset.mem_insert_self a s)
      have hfS : ∀ i ∈ s, 0 ≤ f i := by
        intro i hi
        exact hf i (Finset.mem_insert_of_mem hi)
      have hgS : ∀ i ∈ s, 0 ≤ g i := by
        intro i hi
        exact hg i (Finset.mem_insert_of_mem hi)
      have hfgS : ∀ i ∈ s, f i ≤ g i := by
        intro i hi
        exact hfg i (Finset.mem_insert_of_mem hi)
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      exact mul_le_mul (hfg a (Finset.mem_insert_self a s))
        (ih hfS hgS hfgS) (Finset.prod_nonneg hfS) hga

/-!
The denominator estimate on the right edge follows from the real-part clearance
in v13 `hp-tail.tex:319-337`.  The product is kept separate from the
logarithmic envelope so that the latter remains an explicit analytic goal.
-/

private lemma factorial_cast_prod_succ (n : ℕ) :
    (∏ k ∈ Finset.range n, ((k + 1 : ℕ) : ℝ)) = (Nat.factorial n : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.prod_range_succ, ih, Nat.factorial_succ]
      norm_num
      ring

private lemma descending_cast_prod (n : ℕ) :
    (∏ j ∈ Finset.range n, (((n - 1 - j : ℕ) : ℝ) + 1)) =
      (Nat.factorial n : ℝ) := by
  have hreflect := Finset.prod_range_reflect
    (fun k : ℕ => ((k : ℝ) + 1)) n
  calc
    (∏ j ∈ Finset.range n, (((n - 1 - j : ℕ) : ℝ) + 1)) =
        ∏ j ∈ Finset.range n, (((n - 1 - j + 1 : ℕ) : ℝ)) := by
          refine Finset.prod_congr (M := ℝ) (s₁ := Finset.range n)
            (s₂ := Finset.range n) rfl ?_
          intro j hj
          norm_num [Nat.cast_add]
    _ = ∏ j ∈ Finset.range n, (((j + 1 : ℕ) : ℝ)) := by
          simpa using (Finset.prod_range_reflect
            (fun k : ℕ => (((k + 1 : ℕ) : ℝ))) n)
    _ = (Nat.factorial n : ℝ) := factorial_cast_prod_succ n

private lemma descending_cast_prod_of_lt (n : ℕ) :
    (∏ j ∈ Finset.range n, ((n - j : ℕ) : ℝ)) =
      (Nat.factorial n : ℝ) := by
  calc
    (∏ j ∈ Finset.range n, ((n - j : ℕ) : ℝ)) =
        ∏ j ∈ Finset.range n, (((n - 1 - j + 1 : ℕ) : ℝ)) := by
          apply Finset.prod_congr rfl
          intro j hj
          have hjn : j < n := Finset.mem_range.mp hj
          have : n - j = n - 1 - j + 1 := by omega
          rw [this]
    _ = ∏ j ∈ Finset.range n, (((n - 1 - j : ℕ) : ℝ) + 1) := by
          refine Finset.prod_congr (M := ℝ) (s₁ := Finset.range n)
            (s₂ := Finset.range n) rfl ?_
          intro j hj
          norm_num [Nat.cast_add]
    _ = (Nat.factorial n : ℝ) := by
          exact descending_cast_prod n

private lemma right_denominator_factor_lower {n j : ℕ} {w : ℂ}
    (hj : j ≤ n) (hw : w ∈ hpNegRightSide n) :
    ((n - j : ℕ) : ℝ) + 1 / 2 ≤ ‖w - (j : ℂ)‖ := by
  have hre := hp_neg_right_re_eq n hw
  have hjR : (j : ℝ) ≤ (n : ℝ) := by exact_mod_cast hj
  have hreal : ((n - j : ℕ) : ℝ) + 1 / 2 =
      |((j : ℂ) - w).re| := by
    have hj_re : ((j : ℂ).re) = (j : ℝ) := by norm_num
    rw [Complex.sub_re, hj_re, hre]
    have hsub : (j : ℝ) ≤ (n : ℝ) := hjR
    have hcast : ((n - j : ℕ) : ℝ) = (n : ℝ) - (j : ℝ) := by
      rw [Nat.cast_sub hj]
    rw [hcast]
    have hnonpos : (j : ℝ) - ((n : ℝ) + 1 / 2) ≤ 0 := by linarith
    rw [abs_of_nonpos hnonpos]
    ring
  calc
    ((n - j : ℕ) : ℝ) + 1 / 2 = |((j : ℂ) - w).re| := hreal
    _ ≤ ‖(j : ℂ) - w‖ := Complex.abs_re_le_norm _
    _ = ‖w - (j : ℂ)‖ := by rw [norm_sub_rev]

private lemma right_denominator_prod_lower {n : ℕ} {w : ℂ}
    (hw : w ∈ hpNegRightSide n) :
    ((Nat.factorial n : ℝ) / 2) ≤
      ∏ j ∈ Finset.range (n + 1), ‖w - (j : ℂ)‖ := by
  rw [Finset.prod_range_succ_comm]
  have hlast : (1 / 2 : ℝ) ≤ ‖w - (n : ℂ)‖ := by
    simpa using right_denominator_factor_lower (n := n) (j := n) (le_rfl) hw
  have hprefix : (Nat.factorial n : ℝ) ≤
      ∏ j ∈ Finset.range n, ‖w - (j : ℂ)‖ := by
    calc
      (Nat.factorial n : ℝ) =
          ∏ j ∈ Finset.range n, ((n - j : ℕ) : ℝ) :=
        (descending_cast_prod_of_lt n).symm
      _ ≤ ∏ j ∈ Finset.range n, ‖w - (j : ℂ)‖ := by
        apply finset_prod_mono_nonneg
        · intro j hj
          positivity
        · intro j hj
          exact norm_nonneg _
        · intro j hj
          have hjn : j < n := Finset.mem_range.mp hj
          have hjle : j ≤ n := Nat.le_of_lt hjn
          have hfac := right_denominator_factor_lower (n := n) (j := j) hjle hw
          have hcast : ((n - j : ℕ) : ℝ) ≤ ((n - j : ℕ) : ℝ) + 1 / 2 := by linarith
          exact hcast.trans hfac
  have hnonneg : 0 ≤ ∏ j ∈ Finset.range n, ‖w - (j : ℂ)‖ :=
    Finset.prod_nonneg (fun j hj => norm_nonneg _)
  have hmul := mul_le_mul hlast hprefix (by positivity : 0 ≤ (Nat.factorial n : ℝ))
    (norm_nonneg (w - (n : ℂ)))
  nlinarith [hmul]

theorem hp_neg_right_denominator_factorial_lower {n : ℕ} {w : ℂ}
    (hw : w ∈ hpNegRightSide n) :
    ((Nat.factorial n : ℝ) ^ 2) / 4 ≤
      ∏ j ∈ Finset.range (n + 1), ‖w - (j : ℂ)‖ ^ 2 := by
  have hprod := right_denominator_prod_lower hw
  have hnonneg : 0 ≤ ∏ j ∈ Finset.range (n + 1), ‖w - (j : ℂ)‖ :=
    Finset.prod_nonneg (fun j hj => norm_nonneg _)
  have hsquare : ((Nat.factorial n : ℝ) / 2) ^ 2 ≤
      (∏ j ∈ Finset.range (n + 1), ‖w - (j : ℂ)‖) ^ 2 := by
    exact (sq_le_sq₀ (by positivity) hnonneg).2 hprod
  have hpow :
      (∏ j ∈ Finset.range (n + 1), ‖w - (j : ℂ)‖) ^ 2 =
        ∏ j ∈ Finset.range (n + 1), ‖w - (j : ℂ)‖ ^ 2 := by
    symm
    exact Finset.prod_pow (Finset.range (n + 1)) 2
      (fun j => ‖w - (j : ℂ)‖)
  calc
    ((Nat.factorial n : ℝ) ^ 2) / 4 =
        ((Nat.factorial n : ℝ) / 2) ^ 2 := by ring
    _ ≤ (∏ j ∈ Finset.range (n + 1), ‖w - (j : ℂ)‖) ^ 2 := hsquare
    _ = ∏ j ∈ Finset.range (n + 1), ‖w - (j : ℂ)‖ ^ 2 := hpow

end

end Li2Lean.B4.NegContour

#print axioms Li2Lean.B4.NegContour.hp_neg_right_denominator_factorial_lower
