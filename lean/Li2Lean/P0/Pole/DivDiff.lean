/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Mathlib

/-!
# Pole lemma, layer 1: divided differences and double forward differences

Paper v13 `lem:p0-pole` (chapters/p0-arithmetic.tex:262-295).  The principal
part of every lower entry, *including the diagonal*, is the value of one
polynomial in `(i, j)` of total degree `≤ g-1-t`; the forward differences of
order `u + v > deg` then vanish.  We encode the polynomial extension of the
divided difference `(π i - π j)/(j - i)` as an explicit monomial sum, so the
degree property is syntactic and the diagonal value is `-π'(i)`.

Generated and compiled in the release build; verification notes are retained for context.
-/

namespace Li2Lean.P0.Pole

open Polynomial Finset

noncomputable section

/-- Polynomial extension of `(π x - π y)/(y - x)`. -/
def dd (π : ℚ[X]) (x y : ℚ) : ℚ :=
  -∑ n ∈ range (π.natDegree + 1),
      π.coeff n * ∑ k ∈ range n, x ^ k * y ^ (n - 1 - k)

theorem dd_of_ne (π : ℚ[X]) {x y : ℚ} (hxy : x ≠ y) :
    dd π x y = (π.eval x - π.eval y) / (y - x) := by
  have hyx : y - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
  rw [eq_div_iff hyx, eval_eq_sum_range, eval_eq_sum_range, ← sum_sub_distrib, dd,
    neg_mul, sum_mul, ← sum_neg_distrib]
  refine sum_congr rfl fun n _ => ?_
  -- `geom_sum₂_mul : (∑ i ∈ range n, x ^ i * y ^ (n - 1 - i)) * (x - y) = x ^ n - y ^ n`
  have hg := geom_sum₂_mul x y n                                 -- [Verified] name/namespace
  linear_combination (π.coeff n) * hg

theorem dd_diag (π : ℚ[X]) (x : ℚ) : dd π x x = -(derivative π).eval x := by
  have hsum : ∀ n : ℕ, ∑ k ∈ range n, x ^ k * x ^ (n - 1 - k) = (n : ℚ) * x ^ (n - 1) := by
    intro n
    rw [sum_congr rfl fun k hk => by
      rw [← pow_add, show k + (n - 1 - k) = n - 1 by have := mem_range.mp hk; omega]]
    simp
  rw [dd, derivative_eval, Polynomial.sum_over_range]            -- [Verified] sum_over_range side goal
  · simp only [hsum]
    congr 1
    refine sum_congr rfl fun n _ => by ring
  · intro n; simp

/-- Signed binomial weights of the `u`-th forward difference:
`Δ^u f (x0) = ∑_{a ≤ u} fdw u a * f (x0 + a)`. -/
def fdw (u a : ℕ) : ℚ := (-1 : ℚ) ^ (u - a) * (u.choose a : ℚ)

theorem fdw_sum_pow_eq_zero {u k : ℕ} (hk : k < u) (x0 : ℚ) :
    ∑ a ∈ range (u + 1), fdw u a * (x0 + a) ^ k = 0 := by
  have h := congrFun (fwdDiff_iter_pow_eq_zero_of_lt (R := ℚ) hk) x0
  rw [fwdDiff_iter_eq_sum_shift] at h
  -- h : ∑ a ∈ range (u+1), ((-1:ℤ)^(u-a) * u.choose a) • (x0 + a • 1) ^ k = 0
  simpa [fdw, zsmul_eq_mul, nsmul_eq_mul, mul_assoc] using h     -- [Verified] cast shape

/-- Double forward difference of the divided difference vanishes above the degree. -/
private theorem four_sums_comm
    (A C N : Finset ℕ)
    (K : ℕ → Finset ℕ)
    (F : ℕ → ℕ → ℕ → ℕ → ℚ) :
    (∑ a ∈ A, ∑ c ∈ C,
       ∑ n ∈ N, ∑ k ∈ K n, F a c n k) =
    ∑ n ∈ N, ∑ k ∈ K n,
      ∑ a ∈ A, ∑ c ∈ C, F a c n k := by
  calc
    _ = ∑ a ∈ A, ∑ n ∈ N,
          ∑ c ∈ C, ∑ k ∈ K n, F a c n k := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_comm]
    _ = ∑ a ∈ A, ∑ n ∈ N,
          ∑ k ∈ K n, ∑ c ∈ C, F a c n k := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.sum_comm]
    _ = ∑ n ∈ N, ∑ a ∈ A,
          ∑ k ∈ K n, ∑ c ∈ C, F a c n k := by
      rw [Finset.sum_comm]
    _ = ∑ n ∈ N, ∑ k ∈ K n,
          ∑ a ∈ A, ∑ c ∈ C, F a c n k := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.sum_comm]

private theorem two_sums_factor
    (A C : Finset ℕ)
    (f g X Y : ℕ → ℚ) :
    (∑ a ∈ A, ∑ c ∈ C,
       f a * g c * (X a * Y c)) =
    (∑ a ∈ A, f a * X a) *
    (∑ c ∈ C, g c * Y c) := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  ring

private theorem weighted_sum_factor
    (A C N : Finset ℕ)
    (K : ℕ → Finset ℕ)
    (p f g : ℕ → ℚ)
    (X : ℕ → ℕ → ℚ)
    (Y : ℕ → ℕ → ℕ → ℚ) :
    (∑ a ∈ A, ∑ c ∈ C,
       f a * g c *
         (-∑ n ∈ N, p n *
           ∑ k ∈ K n, X a k * Y c n k)) =
    -∑ n ∈ N, p n *
       ∑ k ∈ K n,
         (∑ a ∈ A, f a * X a k) *
         (∑ c ∈ C, g c * Y c n k) := by
  have hexpand (a c : ℕ) :
      f a * g c *
        (-∑ n ∈ N, p n *
          ∑ k ∈ K n, X a k * Y c n k) =
      -(∑ n ∈ N, ∑ k ∈ K n,
          p n * (f a * g c * (X a k * Y c n k))) := by
    calc
      _ = -((f a * g c) *
            (∑ n ∈ N, p n *
              ∑ k ∈ K n, X a k * Y c n k)) := by ring
      _ = -(∑ n ∈ N, (f a * g c) *
            (p n * ∑ k ∈ K n, X a k * Y c n k)) := by
        rw [Finset.mul_sum]
      _ = -(∑ n ∈ N, ∑ k ∈ K n,
              p n * (f a * g c * (X a k * Y c n k))) := by
        apply congrArg (fun q : ℚ => -q)
        apply Finset.sum_congr rfl
        intro n hn
        calc
          _ = ((f a * g c) * p n) *
                (∑ k ∈ K n, X a k * Y c n k) := by ring
          _ = ∑ k ∈ K n,
                ((f a * g c) * p n) * (X a k * Y c n k) := by
            rw [Finset.mul_sum]
          _ = ∑ k ∈ K n,
                p n * (f a * g c * (X a k * Y c n k)) := by
            apply Finset.sum_congr rfl
            intro k hk
            ring
  have hfactor (n k : ℕ) :
      (∑ a ∈ A, ∑ c ∈ C,
         p n * (f a * g c * (X a k * Y c n k))) =
      p n * ((∑ a ∈ A, f a * X a k) *
        (∑ c ∈ C, g c * Y c n k)) := by
    calc
      _ = ∑ a ∈ A, p n * (∑ c ∈ C,
            f a * g c * (X a k * Y c n k)) := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [← Finset.mul_sum]
      _ = p n * (∑ a ∈ A, ∑ c ∈ C,
            f a * g c * (X a k * Y c n k)) := by
        rw [← Finset.mul_sum]
      _ = p n * ((∑ a ∈ A, f a * X a k) *
            (∑ c ∈ C, g c * Y c n k)) := by
        rw [two_sums_factor A C f g (fun a => X a k)
          (fun c => Y c n k)]
  calc
    _ = ∑ a ∈ A, ∑ c ∈ C,
          -(∑ n ∈ N, ∑ k ∈ K n,
            p n * (f a * g c * (X a k * Y c n k))) := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro c hc
      exact hexpand a c
    _ = -(∑ a ∈ A, ∑ c ∈ C,
          ∑ n ∈ N, ∑ k ∈ K n,
            p n * (f a * g c * (X a k * Y c n k))) := by
      simp only [Finset.sum_neg_distrib]
    _ = -(∑ n ∈ N, ∑ k ∈ K n,
          ∑ a ∈ A, ∑ c ∈ C,
            p n * (f a * g c * (X a k * Y c n k))) := by
      exact congrArg (fun q : ℚ => -q)
        (four_sums_comm A C N K
          (fun a c n k => p n * (f a * g c * (X a k * Y c n k))))
    _ = -(∑ n ∈ N, p n *
          ∑ k ∈ K n,
            (∑ a ∈ A, f a * X a k) *
            (∑ c ∈ C, g c * Y c n k)) := by
      apply congrArg (fun q : ℚ => -q)
      apply Finset.sum_congr rfl
      intro n hn
      calc
        _ = ∑ k ∈ K n, p n *
              ((∑ a ∈ A, f a * X a k) *
               (∑ c ∈ C, g c * Y c n k)) := by
          apply Finset.sum_congr rfl
          intro k hk
          exact hfactor n k
        _ = p n * ∑ k ∈ K n,
              ((∑ a ∈ A, f a * X a k) *
               (∑ c ∈ C, g c * Y c n k)) := by
          rw [Finset.mul_sum]

theorem fwdDiff2_dd_eq_zero (π : ℚ[X]) (x0 : ℚ) {u v : ℕ}
    (hdeg : π.natDegree ≤ u + v) :
    ∑ a ∈ range (u + 1), ∑ c ∈ range (v + 1),
      fdw u a * fdw v c * dd π (x0 + a) (c : ℚ) = 0 := by
  -- Expand `dd`, pull the finite sums over `n, k` outside, and factor each
  -- monomial term as (∑_a fdw u a (x0+a)^k) * (∑_c fdw v c (0+c)^(n-1-k)).
  have key : ∀ n ∈ range (π.natDegree + 1), ∀ k ∈ range n,
      (∑ a ∈ range (u + 1), fdw u a * (x0 + a) ^ k) *
        (∑ c ∈ range (v + 1), fdw v c * ((0 : ℚ) + c) ^ (n - 1 - k)) = 0 := by
    intro n hn k hk
    have hn' := mem_range.mp hn
    have hk' := mem_range.mp hk
    by_cases hku : k < u
    · rw [fdw_sum_pow_eq_zero hku, zero_mul]
    · have : n - 1 - k < v := by omega
      rw [fdw_sum_pow_eq_zero this, mul_zero]
  calc
    _ = -∑ n ∈ range (π.natDegree + 1), π.coeff n * ∑ k ∈ range n,
          (∑ a ∈ range (u + 1), fdw u a * (x0 + a) ^ k) *
            (∑ c ∈ range (v + 1), fdw v c * (c : ℚ) ^ (n - 1 - k)) := by
        simpa only [dd] using
          (weighted_sum_factor
            (range (u + 1))
            (range (v + 1))
            (range (π.natDegree + 1))
            (fun n => range n)
            π.coeff
            (fdw u)
            (fdw v)
            (fun a k => (x0 + (a : ℚ)) ^ k)
            (fun c n k => (c : ℚ) ^ (n - 1 - k)))
    _ = 0 := by
        have hz :
            (∑ n ∈ range (π.natDegree + 1),
              π.coeff n * ∑ k ∈ range n,
                (∑ a ∈ range (u + 1), fdw u a * (x0 + a) ^ k) *
                (∑ c ∈ range (v + 1), fdw v c *
                  (c : ℚ) ^ (n - 1 - k))) = 0 := by
          apply Finset.sum_eq_zero
          intro n hn
          have hkzero :
              (∑ k ∈ range n,
                (∑ a ∈ range (u + 1), fdw u a * (x0 + a) ^ k) *
                (∑ c ∈ range (v + 1), fdw v c *
                  (c : ℚ) ^ (n - 1 - k))) = 0 := by
            apply Finset.sum_eq_zero
            intro k hk
            simpa only [zero_add] using key n hn k hk
          rw [hkzero, mul_zero]
        rw [hz, neg_zero]

end

end Li2Lean.P0.Pole
