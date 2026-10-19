/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B3.ActualRationalIntegerizerProducer
import Li2Lean.Kit.PNTAdapter

namespace Li2Lean.B3

open scoped BigOperators
open Filter Topology

/-! A finite six-class partition records the only combinatorial input needed
for the H4 prime-sum majorant.  The classes are intentionally explicit: the
arithmetic leaf supplies their membership and local bounds, while this module
only combines them. -/
structure H4SixClassPartition (n : ℕ) (u : Finset ℕ) where
  exceptional : Finset ℕ
  squarefull : Finset ℕ
  strip : Finset ℕ
  wall : Finset ℕ
  slab : Finset ℕ
  outer : Finset ℕ
  exceptional_subset : exceptional ⊆ u
  squarefull_subset : squarefull ⊆ u
  strip_subset : strip ⊆ u
  wall_subset : wall ⊆ u
  slab_subset : slab ⊆ u
  outer_subset : outer ⊆ u
  disjoint_exceptional_squarefull : Disjoint exceptional squarefull
  disjoint_prefix_strip : Disjoint (exceptional ∪ squarefull) strip
  disjoint_prefix_wall : Disjoint ((exceptional ∪ squarefull) ∪ strip) wall
  disjoint_prefix_slab :
    Disjoint (((exceptional ∪ squarefull) ∪ strip) ∪ wall) slab
  disjoint_prefix_outer :
    Disjoint ((((exceptional ∪ squarefull) ∪ strip) ∪ wall) ∪ slab) outer
  cover : exceptional ∪ squarefull ∪ strip ∪ wall ∪ slab ∪ outer = u

namespace H4SixClassPartition

private theorem sum_union_six {n : ℕ} {f : ℕ → ℝ} {u : Finset ℕ}
    (p : H4SixClassPartition n u) :
    (∑ x ∈ u, f x) =
      (∑ x ∈ p.exceptional, f x) + (∑ x ∈ p.squarefull, f x) +
      (∑ x ∈ p.strip, f x) + (∑ x ∈ p.wall, f x) +
      (∑ x ∈ p.slab, f x) + (∑ x ∈ p.outer, f x) := by
  have hcover := p.cover
  calc
    (∑ x ∈ u, f x) =
        ∑ x ∈ (((((p.exceptional ∪ p.squarefull) ∪ p.strip) ∪
          p.wall) ∪ p.slab) ∪ p.outer), f x := by
      exact congrArg (fun s : Finset ℕ => ∑ x ∈ s, f x) hcover |>.symm
    _ = (∑ x ∈ p.exceptional, f x) + (∑ x ∈ p.squarefull, f x) +
        (∑ x ∈ p.strip, f x) + (∑ x ∈ p.wall, f x) +
        (∑ x ∈ p.slab, f x) + (∑ x ∈ p.outer, f x) := by
      rw [Finset.sum_union p.disjoint_prefix_outer]
      rw [Finset.sum_union p.disjoint_prefix_slab]
      rw [Finset.sum_union p.disjoint_prefix_wall]
      rw [Finset.sum_union p.disjoint_prefix_strip]
      rw [Finset.sum_union p.disjoint_exceptional_squarefull]

theorem sum_le_of_bounds {n : ℕ} {f : ℕ → ℝ} {u : Finset ℕ}
    (p : H4SixClassPartition n u)
    {b₀ b₁ b₂ b₃ b₄ b₅ : ℝ}
    (h₀ : (∑ x ∈ p.exceptional, f x) ≤ b₀)
    (h₁ : (∑ x ∈ p.squarefull, f x) ≤ b₁)
    (h₂ : (∑ x ∈ p.strip, f x) ≤ b₂)
    (h₃ : (∑ x ∈ p.wall, f x) ≤ b₃)
    (h₄ : (∑ x ∈ p.slab, f x) ≤ b₄)
    (h₅ : (∑ x ∈ p.outer, f x) ≤ b₅) :
    (∑ x ∈ u, f x) ≤ b₀ + b₁ + b₂ + b₃ + b₄ + b₅ := by
  rw [sum_union_six p]
  linarith

end H4SixClassPartition

/-! A pointwise certificate for the six v13 classes.  The class budgets are
kept as arguments: exceptional-prime credits, squarefull costs, wall counts,
and the slab/outer profile are separate arithmetic obligations. -/
def H4SixClassBounds (cutoff : ℕ → ℕ) (E : ℕ → ℕ → ℤ)
    (n : ℕ) (b₀ b₁ b₂ b₃ b₄ b₅ : ℝ) : Prop :=
  ∃ p : H4SixClassPartition n (Nat.primesLE (cutoff n)),
    (∑ x ∈ p.exceptional, (E n x : ℝ) * Real.log x) ≤ b₀ ∧
    (∑ x ∈ p.squarefull, (E n x : ℝ) * Real.log x) ≤ b₁ ∧
    (∑ x ∈ p.strip, (E n x : ℝ) * Real.log x) ≤ b₂ ∧
    (∑ x ∈ p.wall, (E n x : ℝ) * Real.log x) ≤ b₃ ∧
    (∑ x ∈ p.slab, (E n x : ℝ) * Real.log x) ≤ b₄ ∧
    (∑ x ∈ p.outer, (E n x : ℝ) * Real.log x) ≤ b₅

theorem h4_prime_sum_majorant_of_six_class_bounds
    (cutoff : ℕ → ℕ) (E : ℕ → ℕ → ℤ)
    (b₀ b₁ b₂ b₃ b₄ b₅ : ℕ → ℝ)
    (h : ∀ᶠ n : ℕ in atTop,
      H4SixClassBounds cutoff E n (b₀ n) (b₁ n) (b₂ n) (b₃ n) (b₄ n) (b₅ n)) :
    ∀ᶠ n : ℕ in atTop,
      (∑ p ∈ Nat.primesLE (cutoff n), (E n p : ℝ) * Real.log p) ≤
        b₀ n + b₁ n + b₂ n + b₃ n + b₄ n + b₅ n := by
  filter_upwards [h] with n hn
  rcases hn with ⟨p, h₀, h₁, h₂, h₃, h₄, h₅⟩
  exact H4SixClassPartition.sum_le_of_bounds p h₀ h₁ h₂ h₃ h₄ h₅

theorem h4_prime_sum_majorant_normalized
    (cutoff : ℕ → ℕ) (E : ℕ → ℕ → ℤ)
    (b₀ b₁ b₂ b₃ b₄ b₅ : ℕ → ℝ)
    (hpos : ∀ᶠ n : ℕ in atTop, 0 < n)
    (h : ∀ᶠ n : ℕ in atTop,
      H4SixClassBounds cutoff E n (b₀ n) (b₁ n) (b₂ n) (b₃ n) (b₄ n) (b₅ n)) :
    ∀ᶠ n : ℕ in atTop,
      (∑ p ∈ Nat.primesLE (cutoff n), (E n p : ℝ) * Real.log p) /
          (((4 * n : ℕ) : ℝ) ^ 2) ≤
        (b₀ n + b₁ n + b₂ n + b₃ n + b₄ n + b₅ n) /
          (((4 * n : ℕ) : ℝ) ^ 2) := by
  have hsum := h4_prime_sum_majorant_of_six_class_bounds cutoff E b₀ b₁ b₂ b₃ b₄ b₅ h
  filter_upwards [hpos, hsum] with n hnposN hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnposN
  have hnpos : (0 : ℝ) < (((4 * n : ℕ) : ℝ) ^ 2) := by
    positivity
  exact (div_le_div_iff_of_pos_right hnpos).2 hn

/-! This is the exact error expression proposed by the v13 six-class budget.
The convergence proof is intentionally not asserted here: it belongs to the
analytic L3a/error leaf and must be supplied by that leaf with its own source
line audit. -/
noncomputable def v13H4Err (n : ℕ) : ℝ :=
  (13 * (n : ℝ) * Real.log (11 * n) *
      (Real.sqrt (11 * n) + 1 + 3 + 413) +
    (4 * n + 1) * Real.log 7) /
    ((4 * (n : ℝ)) ^ 2)

theorem v13H4Err_nonneg {n : ℕ} (hn : 0 < n) : 0 ≤ v13H4Err n := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.succ_le_iff.mpr hn)
  have hlog11 : 0 ≤ Real.log (11 * (n : ℝ)) := by
    apply Real.log_nonneg
    nlinarith
  have hlog7 : 0 ≤ Real.log (7 : ℝ) := by
    apply Real.log_nonneg
    norm_num
  unfold v13H4Err
  positivity

/-! The six local bounds combine directly with the normalization used by the
H4 rate statement.  The profile and exceptional-prime arithmetic remain
explicit parameters, so this theorem cannot silently turn a missing slab or
formal-divisor estimate into a proof. -/
structure H4SixClassMajorant (n : ℕ) (u : Finset ℕ) where
  partition : H4SixClassPartition n u
  term : ℕ → ℝ
  exceptional_bound :
    (∑ x ∈ partition.exceptional, term x) ≤ 0
  squarefull_bound :
    (∑ x ∈ partition.squarefull, term x) ≤ 0
  strip_bound :
    (∑ x ∈ partition.strip, term x) ≤ 0
  wall_bound :
    (∑ x ∈ partition.wall, term x) ≤ 0
  slab_bound :
    (∑ x ∈ partition.slab, term x) ≤ 0
  outer_bound :
    (∑ x ∈ partition.outer, term x) ≤ 0

theorem H4SixClassMajorant.total_nonpos
    {n : ℕ} {u : Finset ℕ} (h : H4SixClassMajorant n u) :
    (∑ x ∈ u, h.term x) ≤ 0 := by
  have hsum := H4SixClassPartition.sum_le_of_bounds
    (f := h.term) (u := u) h.partition
    (b₀ := 0) (b₁ := 0) (b₂ := 0) (b₃ := 0) (b₄ := 0) (b₅ := 0)
    h.exceptional_bound h.squarefull_bound h.strip_bound h.wall_bound
    h.slab_bound h.outer_bound
  simpa using hsum

end Li2Lean.B3

#print axioms Li2Lean.B3.H4SixClassPartition.sum_le_of_bounds
#print axioms Li2Lean.B3.H4SixClassMajorant.total_nonpos

