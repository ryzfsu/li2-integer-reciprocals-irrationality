/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Mathlib

/-!
# Binomial polynomials for the uniform pole argument

This is the rational polynomial C(X + N, n) used in the pole coefficient
calculation (v13, p0-arithmetic.tex:104-111, 262-286). Keeping the
normalization explicit lets later coefficient lemmas use polynomial equality
without introducing analytic Laurent expansions.
-/

namespace Li2Lean.P0.Pole

open Polynomial Finset

noncomputable section

/-- The rational binomial polynomial binom(X + N, n). -/
def bp (N : ℤ) (n : ℕ) : ℚ[X] :=
  C ((n.factorial : ℚ)⁻¹) *
    (descPochhammer ℚ n).comp (X + C (N : ℚ))

@[simp] theorem bp_zero (N : ℤ) : bp N 0 = 1 := by
  simp [bp]

theorem bp_natDegree_le (N : ℤ) (n : ℕ) : (bp N n).natDegree ≤ n := by
  unfold bp
  refine (natDegree_C_mul_le _ _).trans ?_
  rw [natDegree_comp, descPochhammer_natDegree, natDegree_X_add_C, mul_one]

/-- Values of bp at natural arguments are the usual natural binomial coefficients. -/
theorem bp_eval_nat (N : ℕ) (n x : ℕ) :
    (bp N n).eval (x : ℚ) = (((x + N).choose n : ℕ) : ℚ) := by
  unfold bp
  rw [eval_mul, eval_C, eval_comp, eval_add, eval_X, eval_C]
  have hx : (x : ℚ) + ((N : ℤ) : ℚ) = ((x + N : ℕ) : ℚ) := by
    push_cast
    ring
  rw [hx, descPochhammer_eval_eq_descFactorial]
  rw [Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  field_simp

/-- Translating the argument by an integer translates the upper binomial parameter. -/
theorem bp_comp_X_add_C (N : ℤ) (n : ℕ) (c : ℤ) :
    (bp N n).comp (X + C (c : ℚ)) = bp (N + c) n := by
  unfold bp
  rw [mul_comp, C_comp, comp_assoc]
  congr 2
  simp only [add_comp, X_comp, C_comp]
  push_cast
  rw [add_assoc, ← C_add, add_comm (c : ℚ)]

private theorem natCast_range_infinite :
    (Set.range (fun n : ℕ => (n : ℚ))).Infinite := by
  apply Set.infinite_range_of_injective
  intro m n h
  change (m : ℚ) = (n : ℚ) at h
  exact_mod_cast h

/-- Pascal's identity, first checked on natural inputs and then transported by shifts. -/
theorem bp_pascal (N : ℤ) (n : ℕ) :
    bp (N + 1) (n + 1) = bp N (n + 1) + bp N n := by
  have hzero : bp 1 (n + 1) = bp 0 (n + 1) + bp 0 n := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply natCast_range_infinite.mono
    intro x hx
    rcases hx with ⟨x, rfl⟩
    change (bp 1 (n + 1)).eval (x : ℚ) =
      ((bp 0 (n + 1) + bp 0 n).eval (x : ℚ))
    rw [eval_add]
    have hL : (bp 1 (n + 1)).eval (x : ℚ) =
        (((x + 1).choose (n + 1) : ℕ) : ℚ) := by
      simpa using bp_eval_nat (1 : ℕ) (n + 1) x
    have hR1 : (bp 0 (n + 1)).eval (x : ℚ) =
        ((x.choose (n + 1) : ℕ) : ℚ) := by
      simpa using bp_eval_nat (0 : ℕ) (n + 1) x
    have hR2 : (bp 0 n).eval (x : ℚ) = ((x.choose n : ℕ) : ℚ) := by
      simpa using bp_eval_nat (0 : ℕ) n x
    rw [hL, hR1, hR2]
    norm_cast
    rw [Nat.choose_succ_succ]
    ring
  have hshift := congrArg (fun p : ℚ[X] => p.comp (X + C (N : ℚ))) hzero
  have hshift' : bp (1 + N) (n + 1) = bp N (n + 1) + bp N n := by
    rw [add_comp] at hshift
    simpa only [bp_comp_X_add_C, Int.zero_add] using hshift
  have hbase : 1 + N = N + 1 := by omega
  rw [hbase] at hshift'
  exact hshift'

/-- A polynomial invariant under a unit translation is constant. -/
theorem eq_C_of_comp_X_add_one (p : ℚ[X]) (hp : p.comp (X + 1) = p) :
    p = C (p.eval 0) := by
  have hval : ∀ n : ℕ, p.eval (n : ℚ) = p.eval 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have h := congrArg (fun f : ℚ[X] => f.eval (n : ℚ)) hp
        have hstep : p.eval ((n : ℚ) + 1) = p.eval (n : ℚ) := by
          simpa [Polynomial.eval_comp] using h
        simpa [Nat.cast_succ] using hstep.trans ih
  apply Polynomial.eq_of_infinite_eval_eq
  apply natCast_range_infinite.mono
  intro x hx
  rcases hx with ⟨n, rfl⟩
  simp [hval n]

private theorem descPochhammer_eval_neg_one (n : ℕ) :
    (descPochhammer ℚ n).eval (-1) = (-1 : ℚ) ^ n * (n.factorial : ℚ) := by
  induction n with
  | zero => simp [descPochhammer]
  | succ n ih =>
      rw [descPochhammer_succ_right, eval_mul, ih]
      simp only [eval_sub, eval_X, eval_natCast]
      rw [Nat.factorial_succ, pow_succ]
      push_cast
      ring

/-- At zero, the derivative is the first nonzero coefficient of the falling product. -/
theorem derivative_bp_zero_eval_zero (n : ℕ) :
    (derivative (bp 0 (n + 1))).eval 0 = (-1 : ℚ) ^ n / (n + 1) := by
  have hrepr : bp 0 (n + 1) =
      C (((n + 1).factorial : ℚ)⁻¹) * X *
        (descPochhammer ℚ n).comp (X - 1) := by
    simp [bp, descPochhammer_succ_left, mul_assoc]
  rw [hrepr, derivative_mul, derivative_mul]
  simp only [eval_add, eval_mul, eval_C, eval_X, eval_one, derivative_X,
    derivative_C, eval_comp, eval_sub, eval_natCast, zero_mul, add_zero, one_mul]
  norm_num
  rw [descPochhammer_eval_neg_one]
  rw [Nat.factorial_succ]
  push_cast
  field_simp

private def formA0 (n : ℕ) : ℚ[X] :=
  ∑ j ∈ Icc 1 n, C ((-1 : ℚ) ^ (j - 1) / j) * bp 0 (n - j)

private theorem formA0_comp (n : ℕ) :
    (formA0 n).comp (X + 1) =
      ∑ j ∈ Icc 1 n, C ((-1 : ℚ) ^ (j - 1) / j) * bp 1 (n - j) := by
  unfold formA0
  rw [Polynomial.sum_comp]
  simp only [Polynomial.mul_comp, Polynomial.C_comp]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  simpa using (bp_comp_X_add_C (0 : ℤ) (n - j) (1 : ℤ))

private theorem formA0_comp_sub (n : ℕ) :
    (formA0 (n + 1)).comp (X + 1) - formA0 (n + 1) = formA0 n := by
  rw [formA0_comp, formA0]
  rw [Finset.sum_Icc_succ_top (a := 1) (b := n) (by omega)]
  rw [Finset.sum_Icc_succ_top (a := 1) (b := n) (by omega)]
  have hmain :
      (∑ j ∈ Icc 1 n,
        C ((-1 : ℚ) ^ (j - 1) / j) * bp 1 (n + 1 - j)) -
      ∑ j ∈ Icc 1 n,
        C ((-1 : ℚ) ^ (j - 1) / j) * bp 0 (n + 1 - j) = formA0 n := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have hjn : j ≤ n := (Finset.mem_Icc.mp hj).2
    have hindex : n + 1 - j = (n - j) + 1 := by omega
    rw [hindex]
    have hp := bp_pascal (0 : ℤ) (n - j)
    have hp' : bp 1 ((n - j) + 1) =
        bp 0 ((n - j) + 1) + bp 0 (n - j) := by
      simpa using hp
    rw [hp']
    ring
  have hend :
      C ((-1 : ℚ) ^ ((n + 1) - 1) / ((n + 1 : ℕ) : ℚ)) *
          bp 1 (n + 1 - (n + 1)) =
      C ((-1 : ℚ) ^ ((n + 1) - 1) / ((n + 1 : ℕ) : ℚ)) *
          bp 0 (n + 1 - (n + 1)) := by
    simp [bp_zero]
  rw [← hmain]
  linear_combination hend

private theorem formA0_eval_zero_succ (n : ℕ) :
    (formA0 (n + 1)).eval 0 = (-1 : ℚ) ^ n / (n + 1) := by
  unfold formA0
  rw [eval_finset_sum, Finset.sum_Icc_succ_top (a := 1) (b := n) (by omega)]
  have hzero :
      (∑ j ∈ Icc 1 n,
        (C ((-1 : ℚ) ^ (j - 1) / j) * bp 0 (n + 1 - j)).eval 0) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hjn : j ≤ n := (Finset.mem_Icc.mp hj).2
    have hjone : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have hjpos : 0 < n + 1 - j := by omega
    have he : (bp 0 (n + 1 - j)).eval 0 =
        (((0 : ℕ).choose (n + 1 - j) : ℕ) : ℚ) := by
      simpa using bp_eval_nat (0 : ℕ) (n + 1 - j) 0
    rw [eval_mul, eval_C, he]
    simp [Nat.choose_eq_zero_of_lt hjpos]
  rw [hzero]
  simp [bp_zero]

private theorem derivative_bp_zero_formA (n : ℕ) :
    derivative (bp 0 n) = formA0 n := by
  induction n with
  | zero => simp [formA0]
  | succ n ih =>
      let e : ℚ[X] := derivative (bp 0 (n + 1)) - formA0 (n + 1)
      have hbp : (bp 0 (n + 1)).comp (X + 1) =
          bp 0 (n + 1) + bp 0 n := by
        change (bp 0 (n + 1)).comp (X + C (1 : ℚ)) = _
        have hs := bp_comp_X_add_C (0 : ℤ) (n + 1) (1 : ℤ)
        convert hs using 1 <;> norm_num
        simpa using (bp_pascal (0 : ℤ) n).symm
      have hder := congrArg derivative hbp
      have hder' : (derivative (bp 0 (n + 1))).comp (X + 1) =
          derivative (bp 0 (n + 1)) + derivative (bp 0 n) := by
        calc
          _ = derivative ((bp 0 (n + 1)).comp (X + 1)) := by
            rw [derivative_comp]
            rw [derivative_add]
            simp
          _ = derivative (bp 0 (n + 1) + bp 0 n) := hder
          _ = _ := by rw [derivative_add]
      have hper : e.comp (X + 1) = e := by
        dsimp [e]
        calc
          _ = (derivative (bp 0 (n + 1))).comp (X + 1) -
              (formA0 (n + 1)).comp (X + 1) := by rw [sub_comp]
          _ = (derivative (bp 0 (n + 1)) + derivative (bp 0 n)) -
              (formA0 (n + 1)).comp (X + 1) := by rw [hder']
          _ = derivative (bp 0 (n + 1)) - formA0 (n + 1) := by
            rw [ih]
            linear_combination -1 * formA0_comp_sub n
      have hc := eq_C_of_comp_X_add_one e hper
      have heval : e.eval 0 = 0 := by
        dsimp [e]
        rw [eval_sub, derivative_bp_zero_eval_zero n]
        rw [formA0_eval_zero_succ n]
        ring
      have hz : e = 0 := by
        rw [hc, heval]
        simp
      exact sub_eq_zero.mp hz

theorem derivative_bp_formA (N : ℤ) (n : ℕ) :
    derivative (bp N n) =
      ∑ j ∈ Icc 1 n, C ((-1 : ℚ) ^ (j - 1) / j) * bp N (n - j) := by
  have h0 := derivative_bp_zero_formA n
  have hshift := congrArg (fun p : ℚ[X] => p.comp (X + C (N : ℚ))) h0
  have hbpN : bp N n = (bp 0 n).comp (X + C (N : ℚ)) := by
    simpa using (bp_comp_X_add_C (0 : ℤ) n N).symm
  rw [hbpN]
  calc
    derivative ((bp 0 n).comp (X + C (N : ℚ))) =
        (derivative (bp 0 n)).comp (X + C (N : ℚ)) := by
          rw [derivative_comp, derivative_add]
          simp
    _ = (formA0 n).comp (X + C (N : ℚ)) := hshift
    _ = ∑ j ∈ Icc 1 n,
        C ((-1 : ℚ) ^ (j - 1) / j) * bp N (n - j) := by
          unfold formA0
          rw [Polynomial.sum_comp]
          simp only [Polynomial.mul_comp, Polynomial.C_comp]
          apply Finset.sum_congr rfl
          intro j hj
          congr 1
          simpa using (bp_comp_X_add_C (0 : ℤ) (n - j) N)

end

end Li2Lean.P0.Pole
