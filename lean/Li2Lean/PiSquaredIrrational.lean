/-
Copyright (c) 2022 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
Adapted from mathlib4@25e572b8074098af3f09d4cb2a4231cbdc584534:
  Mathlib/Analysis/Real/Pi/Irrational.lean
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Mathlib

namespace Li2Lean

noncomputable section

open intervalIntegral MeasureTheory.MeasureSpace Set Polynomial Real
open scoped Nat

private def piNivenI (n : ℕ) (θ : ℝ) : ℝ :=
  ∫ x in (-1)..1, (1 - x ^ 2) ^ n * cos (x * θ)

private lemma piNivenI_zero (θ : ℝ) : piNivenI 0 θ * θ = 2 * sin θ := by
  rw [mul_comm, piNivenI]
  simp [mul_integral_comp_mul_right, two_mul]

private lemma piNivenI_recursion' (n : ℕ) (θ : ℝ) :
    piNivenI (n + 1) θ * θ ^ 2 =
      - (2 * 2 * ((n + 1) * (0 ^ n * cos θ))) +
      2 * (n + 1) * (2 * n + 1) * piNivenI n θ -
      4 * (n + 1) * n * piNivenI (n - 1) θ := by
  rw [piNivenI]
  let f (x : ℝ) : ℝ := 1 - x ^ 2
  let u₁ (x : ℝ) : ℝ := f x ^ (n + 1)
  let u₁' (x : ℝ) : ℝ := - (2 * (n + 1) * x * f x ^ n)
  let v₁ (x : ℝ) : ℝ := sin (x * θ)
  let v₁' (x : ℝ) : ℝ := cos (x * θ) * θ
  let u₂ (x : ℝ) : ℝ := x * (f x) ^ n
  let u₂' (x : ℝ) : ℝ := (f x) ^ n - 2 * n * x ^ 2 * (f x) ^ (n - 1)
  let v₂ (x : ℝ) : ℝ := cos (x * θ)
  let v₂' (x : ℝ) : ℝ := -sin (x * θ) * θ
  have hfd : Continuous f := by fun_prop
  have hu₁d : Continuous u₁' := by fun_prop
  have hv₁d : Continuous v₁' := by fun_prop
  have hu₂d : Continuous u₂' := by fun_prop
  have hv₂d : Continuous v₂' := by fun_prop
  have hu₁_eval_one : u₁ 1 = 0 := by simp only [u₁, f]; simp
  have hu₁_eval_neg_one : u₁ (-1) = 0 := by simp only [u₁, f]; simp
  have t : u₂ 1 * v₂ 1 - u₂ (-1) * v₂ (-1) = 2 * (0 ^ n * cos θ) := by
    simp [u₂, v₂, f, ← two_mul]
  have hf (x) : HasDerivAt f (- 2 * x) x := by
    convert (hasDerivAt_pow 2 x).const_sub 1 using 1
    simp
  have hu₁ (x) : HasDerivAt u₁ (u₁' x) x := by
    convert (hf x).pow _ using 1
    simp only [Nat.add_succ_sub_one, u₁', Nat.cast_add_one]
    ring
  have hv₁ (x) : HasDerivAt v₁ (v₁' x) x := (hasDerivAt_mul_const θ).sin
  have hu₂ (x) : HasDerivAt u₂ (u₂' x) x := by
    convert (hasDerivAt_id' x).fun_mul ((hf x).fun_pow _) using 1
    simp only [u₂']
    ring
  have hv₂ (x) : HasDerivAt v₂ (v₂' x) x := (hasDerivAt_mul_const θ).cos
  convert_to (∫ (x : ℝ) in (-1)..1, u₁ x * v₁' x) * θ = _ using 1
  · simp_rw [u₁, v₁', f, ← intervalIntegral.integral_mul_const, sq θ, mul_assoc]
  rw [integral_mul_deriv_eq_deriv_mul (fun x _ => hu₁ x) (fun x _ => hv₁ x)
    (hu₁d.intervalIntegrable _ _) (hv₁d.intervalIntegrable _ _), hu₁_eval_one,
    hu₁_eval_neg_one, zero_mul, zero_mul, sub_zero, zero_sub, ← integral_neg,
    ← integral_mul_const]
  convert_to ((-2 : ℝ) * (n + 1)) * ∫ (x : ℝ) in (-1)..1, (u₂ x * v₂' x) = _ using 1
  · rw [← integral_const_mul]
    congr 1 with x
    dsimp [u₁', v₁, u₂, v₂']
    ring
  rw [integral_mul_deriv_eq_deriv_mul (fun x _ => hu₂ x) (fun x _ => hv₂ x)
    (hu₂d.intervalIntegrable _ _) (hv₂d.intervalIntegrable _ _), mul_sub, t,
    neg_mul, neg_mul, neg_mul, sub_neg_eq_add]
  have h (x : _) : u₂' x = (2 * n + 1) * f x ^ n - 2 * n * f x ^ (n - 1) := by
    cases n with
    | zero => simp [u₂']
    | succ n => ring!
  simp_rw [h, sub_mul, mul_assoc _ _ (v₂ _)]
  have hv₂c : Continuous v₂ := by fun_prop
  rw [mul_mul_mul_comm, integral_sub, mul_sub, add_sub_assoc]
  · congr 1
    simp_rw [integral_const_mul]
    ring!
  all_goals exact Continuous.intervalIntegrable (by fun_prop) _ _

private lemma piNivenI_recursion (n : ℕ) (θ : ℝ) :
    piNivenI (n + 2) θ * θ ^ 2 =
      2 * (n + 2) * (2 * n + 3) * piNivenI (n + 1) θ -
      4 * (n + 2) * (n + 1) * piNivenI n θ := by
  rw [piNivenI_recursion' (n + 1)]
  push_cast
  ring

private lemma piNivenI_one (θ : ℝ) :
    piNivenI 1 θ * θ ^ 3 = 4 * sin θ - 4 * θ * cos θ := by
  rw [_root_.pow_succ, ← mul_assoc, piNivenI_recursion' 0, sub_mul, add_mul,
    mul_assoc _ (piNivenI 0 θ), piNivenI_zero]
  ring

private def piNivenPoly : ℕ → ℤ[X]
  | 0 => 0
  | 1 => C 4
  | n + 2 => ((2 : ℤ) * (2 * n + 3)) • piNivenPoly (n + 1) +
      monomial 1 (-4) * piNivenPoly n

private lemma piNivenPoly_natDegree_le : ∀ n : ℕ, (piNivenPoly n).natDegree ≤ n
  | 0 => by simp [piNivenPoly]
  | 1 => by simp [piNivenPoly]
  | n + 2 => by
      rw [piNivenPoly]
      refine natDegree_add_le_of_degree_le
        ((natDegree_smul_le _ _).trans ?_) ?_
      · exact (piNivenPoly_natDegree_le (n + 1)).trans (by simp)
      calc
        _ ≤ (monomial 1 (-4 : ℤ)).natDegree + (piNivenPoly n).natDegree := by
          exact natDegree_mul_le
        _ ≤ 1 + n := Nat.add_le_add (by simp) (piNivenPoly_natDegree_le n)
        _ ≤ n + 2 := by omega

private def piNivenR (n : ℕ) : ℝ :=
  (Real.pi ^ 2) ^ n * piNivenI n Real.pi / n !

private lemma piNivenR_zero : piNivenR 0 = 0 := by
  unfold piNivenR
  have h := piNivenI_zero Real.pi
  simp only [Real.sin_pi, mul_zero] at h
  have hp : (Real.pi : ℝ) ≠ 0 := ne_of_gt Real.pi_pos
  have hi : piNivenI 0 Real.pi = 0 := by
    exact (mul_eq_zero.mp h).resolve_right hp
  simp [hi]

private lemma piNivenR_one : piNivenR 1 = 4 := by
  unfold piNivenR
  have h := piNivenI_one Real.pi
  rw [Real.sin_pi, Real.cos_pi] at h
  have hp : (Real.pi : ℝ) ≠ 0 := ne_of_gt Real.pi_pos
  have h' : piNivenI 1 Real.pi * Real.pi ^ 2 = 4 := by
    apply (mul_left_cancel₀ hp)
    calc
      Real.pi * (piNivenI 1 Real.pi * Real.pi ^ 2) =
          piNivenI 1 Real.pi * Real.pi ^ 3 := by ring
      _ = 4 * Real.pi := by nlinarith [h]
      _ = Real.pi * 4 := by ring
  simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using h'

private lemma piNivenR_recursion (n : ℕ) :
    piNivenR (n + 2) =
      (2 * (2 * n + 3) : ℝ) * piNivenR (n + 1) -
      4 * (Real.pi ^ 2) * piNivenR n := by
  unfold piNivenR
  have hp : (Real.pi : ℝ) ≠ 0 := ne_of_gt Real.pi_pos
  have hr := piNivenI_recursion n Real.pi
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_ofNat]
  field_simp [hp, Nat.factorial_ne_zero]
  push_cast
  linear_combination (Real.pi ^ 2) ^ (n + 1) * hr

private lemma piNivenPoly_eval : ∀ n : ℕ,
  (piNivenPoly n).eval₂ (Int.castRingHom ℝ) (Real.pi ^ 2) = piNivenR n
  | 0 => by simpa [piNivenPoly] using piNivenR_zero.symm
  | 1 => by simpa [piNivenPoly] using piNivenR_one.symm
  | n + 2 => by
      rw [piNivenPoly, eval₂_add, eval₂_smul, eval₂_mul, eval₂_monomial,
        piNivenPoly_eval (n + 1), piNivenPoly_eval n, piNivenR_recursion]
      norm_num
      ring

private lemma piNivenI_pos (n : ℕ) (hn : 0 < n) : 0 < piNivenI n Real.pi := by
  let A : ℝ → ℝ := fun x => (1 - x ^ 2) ^ n * Real.cos (x * Real.pi)
  let G : ℝ → ℝ := fun x =>
    ((1 - x ^ 2) ^ n - (1 - (1 - x) ^ 2) ^ n) * Real.cos (Real.pi * x)
  have hAc : Continuous A := by
    dsimp [A]
    fun_prop
  have hGc : Continuous G := by
    dsimp [G]
    fun_prop
  have hneg : (∫ x in (-1 : ℝ)..0, A x) = ∫ x in 0..1, A x := by
    calc
      (∫ x in (-1 : ℝ)..0, A x) = ∫ x in 0..1, A (-x) := by
        simpa using (intervalIntegral.integral_comp_neg A (a := 0) (b := 1)).symm
      _ = ∫ x in 0..1, A x := by
        congr 1 with x
        dsimp [A]
        simp [mul_neg, Real.cos_neg]
  have hsplit : (∫ x in (0 : ℝ)..1, A x) =
      (∫ x in 0..(1 / 2 : ℝ), A x) + (∫ x in (1 / 2 : ℝ)..1, A x) := by
    symm
    exact intervalIntegral.integral_add_adjacent_intervals
      (hAc.intervalIntegrable _ _) (hAc.intervalIntegrable _ _)
  have hsecond : (∫ x in (1 / 2 : ℝ)..1, A x) =
      ∫ x in 0..(1 / 2 : ℝ), A (1 - x) := by
    convert (intervalIntegral.integral_comp_sub_left A (d := 1) (a := 0)
      (b := 1 / 2)).symm using 1 <;> norm_num
  have hpair : piNivenI n Real.pi =
      2 * ∫ x in (0 : ℝ)..(1 / 2 : ℝ), G x := by
    have htotal : piNivenI n Real.pi = 2 * ∫ x in (0 : ℝ)..1, A x := by
      rw [piNivenI]
      change (∫ x in (-1 : ℝ)..1, A x) = _
      rw [← intervalIntegral.integral_add_adjacent_intervals
        (hAc.intervalIntegrable _ _) (hAc.intervalIntegrable _ _), hneg]
      ring
    have hAcomp : Continuous (fun x : ℝ => A (1 - x)) := by
      exact hAc.comp (continuous_const.sub continuous_id)
    rw [htotal, hsplit, hsecond]
    rw [← intervalIntegral.integral_add (hAc.intervalIntegrable 0 (1 / 2))
      (hAcomp.intervalIntegrable 0 (1 / 2))]
    apply congrArg (fun z : ℝ => 2 * z)
    apply intervalIntegral.integral_congr
    intro x hx
    dsimp [A, G]
    rw [show (1 - x) * Real.pi = Real.pi - x * Real.pi by ring, Real.cos_sub]
    simp [Real.sin_pi, Real.cos_pi]
    ring
  have hGnonneg : ∀ x ∈ Set.Ioc (0 : ℝ) (1 / 2), 0 ≤ G x := by
    intro x hx
    have hx0 : 0 ≤ x := le_of_lt hx.1
    have hxhalf : x ≤ (1 / 2 : ℝ) := hx.2
    have hbase0 : 0 ≤ 1 - x ^ 2 := by nlinarith [sq_nonneg x]
    have hbase1 : 0 ≤ 1 - (1 - x) ^ 2 := by nlinarith [sq_nonneg (1 - x)]
    have hbase : 1 - (1 - x) ^ 2 ≤ 1 - x ^ 2 := by nlinarith
    have hpow : (1 - (1 - x) ^ 2) ^ n ≤ (1 - x ^ 2) ^ n :=
      pow_le_pow_left₀ hbase1 hbase n
    have hcos : 0 ≤ Real.cos (Real.pi * x) := by
      apply Real.cos_nonneg_of_neg_pi_div_two_le_of_le <;> nlinarith [Real.pi_pos]
    exact mul_nonneg (sub_nonneg.mpr hpow) hcos
  have hGpos : ∃ c ∈ Set.Icc (0 : ℝ) (1 / 2), 0 < G c := by
    refine ⟨(1 / 4 : ℝ), by constructor <;> norm_num, ?_⟩
    dsimp [G]
    have hbase0 : 0 ≤ 1 - (1 / 4 : ℝ) ^ 2 := by norm_num
    have hbase1 : 0 ≤ 1 - (1 - (1 / 4 : ℝ)) ^ 2 := by norm_num
    have hlt : 1 - (1 - (1 / 4 : ℝ)) ^ 2 < 1 - (1 / 4 : ℝ) ^ 2 := by norm_num
    have hp : (1 - (1 - (1 / 4 : ℝ)) ^ 2) ^ n <
        (1 - (1 / 4 : ℝ) ^ 2) ^ n :=
      pow_lt_pow_left₀ hlt hbase1 (Nat.ne_of_gt hn)
    have hc : 0 < Real.cos (Real.pi * (1 / 4 : ℝ)) := by
      apply Real.cos_pos_of_mem_Ioo
      constructor <;> nlinarith [Real.pi_pos]
    exact mul_pos (sub_pos.mpr hp) hc
  have hpos : 0 < ∫ x in (0 : ℝ)..(1 / 2 : ℝ), G x := by
    apply intervalIntegral.integral_pos (by norm_num) hGc.continuousOn hGnonneg hGpos
  rw [hpair]
  positivity

private lemma piNivenI_le_two (n : ℕ) : piNivenI n Real.pi ≤ 2 := by
  have hbound : ∀ x ∈ Set.uIoc (-1 : ℝ) 1,
      ‖(1 - x ^ 2) ^ n * Real.cos (x * Real.pi)‖ ≤ (1 : ℝ) := by
    intro x hx
    have hx0 : (-1 : ℝ) < x := by simpa using hx.1
    have hx1 : x ≤ (1 : ℝ) := by simpa using hx.2
    have hx' : x ∈ Set.Icc (-1 : ℝ) 1 :=
      ⟨le_of_lt hx0, hx1⟩
    rw [Real.norm_eq_abs, abs_mul, abs_pow]
    have hbase : |1 - x ^ 2| ≤ (1 : ℝ) := by
      rw [abs_le]
      constructor <;> nlinarith [sq_nonneg x, hx'.1, hx'.2]
    have hp : |1 - x ^ 2| ^ n ≤ (1 : ℝ) := pow_le_one₀ (abs_nonneg _) hbase
    exact (mul_le_mul hp (Real.abs_cos_le_one _) (abs_nonneg _) zero_le_one).trans_eq
      (by norm_num)
  have hnorm : ‖piNivenI n Real.pi‖ ≤ 2 := by
    unfold piNivenI
    have hnorm0 := intervalIntegral.norm_integral_le_of_norm_le_const hbound
    norm_num at hnorm0
    simpa [Real.norm_eq_abs] using hnorm0
  exact (le_trans (le_norm_self _) (by simpa using hnorm))

private lemma piSq_not_irrational_exists_rep {x : ℝ} :
    ¬Irrational x → ∃ (a b : ℤ), 0 < b ∧ x = a / b := by
  rw [Irrational, not_not, mem_range]
  rintro ⟨q, rfl⟩
  refine ⟨q.num, q.den, ?_, ?_⟩
  · exact_mod_cast q.pos
  · exact_mod_cast (Rat.num_div_den _).symm

private lemma piNiven_is_integer {p : ℤ[X]} (a b : ℤ) {k : ℕ}
    (hp : p.natDegree ≤ k) :
    ∃ z : ℤ, p.eval₂ (Int.castRingHom ℝ) (a / b) * b ^ k = z := by
  rcases eq_or_ne b 0 with rfl | hb
  · rcases k.eq_zero_or_pos with rfl | hk
    · exact ⟨p.coeff 0, by simp⟩
    · exact ⟨0, by simp [hk.ne']⟩
  refine ⟨∑ i ∈ p.support, p.coeff i * a ^ i * b ^ (k - i), ?_⟩
  conv => lhs; rw [← sum_monomial_eq p]
  rw [eval₂_sum, sum, Finset.sum_mul, Int.cast_sum]
  simp only [eval₂_monomial, eq_intCast, div_pow, Int.cast_mul, Int.cast_pow]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have ik := (le_natDegree_of_mem_supp i hi).trans hp
  rw [mul_assoc, div_mul_comm, ← Int.cast_pow, ← Int.cast_pow, ← Int.cast_pow,
    ← pow_sub_mul_pow b ik, ← Int.cast_div_charZero, Int.mul_ediv_cancel _ (pow_ne_zero _ hb),
    ← mul_assoc, mul_right_comm, ← Int.cast_pow]
  exact dvd_mul_left _ _

open Filter

theorem irrational_pi_sq : Irrational (Real.pi ^ 2) := by
  by_contra hrat
  obtain ⟨a, b, hb, h⟩ := piSq_not_irrational_exists_rep hrat
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have haR : (0 : ℝ) < a := by
    have hpos : (0 : ℝ) < (a : ℝ) / b := by
      rw [← h]
      positivity
    simpa using (lt_div_iff₀ hbR).mp hpos
  have hsmall : ∀ᶠ n : ℕ in atTop,
      (a : ℝ) ^ n / n ! * piNivenI n Real.pi < 1 := by
    have hp := (FloorSemiring.tendsto_pow_div_factorial_atTop (a : ℝ)).eventually_lt_const
      (show (0 : ℝ) < 1 / 2 by norm_num)
    filter_upwards [hp] with n hn
    have hi := piNivenI_le_two n
    have hnonneg : 0 ≤ (a : ℝ) ^ n / n ! := by positivity
    calc
      (a : ℝ) ^ n / n ! * piNivenI n Real.pi ≤
          (a : ℝ) ^ n / n ! * 2 := mul_le_mul_of_nonneg_left hi hnonneg
      _ < 1 := by nlinarith
  have hindex : ∀ᶠ n : ℕ in atTop, 0 < n := eventually_gt_atTop 0
  obtain ⟨n, hnsmall, hnpos⟩ := (hsmall.and hindex).exists
  have hIpos : 0 < piNivenI n Real.pi := piNivenI_pos n hnpos
  have hprodpos : 0 < (a : ℝ) ^ n / n ! * piNivenI n Real.pi := by positivity
  obtain ⟨z, hz⟩ := piNiven_is_integer (p := piNivenPoly n) a b
    (piNivenPoly_natDegree_le n)
  have hrel : piNivenR n * (b : ℝ) ^ n =
      (a : ℝ) ^ n / n ! * piNivenI n Real.pi := by
    unfold piNivenR
    rw [h]
    rw [div_pow]
    field_simp [ne_of_gt hbR, Nat.factorial_ne_zero]
  have hzreal : (z : ℝ) =
      (a : ℝ) ^ n / n ! * piNivenI n Real.pi := by
    calc
      (z : ℝ) = (piNivenPoly n).eval₂ (Int.castRingHom ℝ) ((a : ℝ) / b) *
          (b : ℝ) ^ n := by exact_mod_cast hz.symm
      _ = piNivenR n * (b : ℝ) ^ n := by rw [← h, piNivenPoly_eval]
      _ = _ := hrel
  have hzpos : (0 : ℝ) < z := by simpa [hzreal] using hprodpos
  have hzlt : (z : ℝ) < 1 := by simpa [hzreal] using hnsmall
  have hzpos' : (0 : ℤ) < z := by exact_mod_cast hzpos
  have hzlt' : z < 1 := by exact_mod_cast hzlt
  omega

end
end Li2Lean
