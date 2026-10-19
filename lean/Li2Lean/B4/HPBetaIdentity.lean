/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
/-
  B4 item C1/C2: the beta identity for `hpRR`
  (v13 hp-tail.tex eq:hp-beta, lines 198-205) and its two consumers
  (beta remainder bound `hR`, `remainder_ne_zero`).

  The beta identity and its consumers are compiled in this release closure.

  Key fact used throughout: in the release `hpRR n z` is DEFINED as
      ∑' m, (hpPhiValue n (3n+2+m) : ℝ) * z^(3n+2+m)      (HPIntegralForm.lean:39)
  so the identity needs NO residue / M0 input.  Per coefficient it is the finite
  factorial identity
      Φ_n(3n+2+m) = (2n+1+m)!^3 / (m! (3n+2+m)!^2)
                  = (2n+1)!/(n!)^2 * C(m+2n+1, 2n+1) * B(2n+2+m, n+1)^2,
  exact-checked for n ≤ 10, m ≤ 40 (the finite-data source).

  Names that are already used in the release (so known to exist at Mathlib 25e572b8):
    intervalIntegral.hasSum_integral_of_dominated_convergence  (P0/ConfigFejerLog.lean:82)
    hasSum_choose_mul_geometric_of_norm_lt_one                  (P0/FrequencyGenerating.lean:46)
    intervalIntegral.norm_integral_le_of_norm_le_const          (B4/NegativeContourBranchValueBound.lean:280)
    integral_pow, intervalIntegral.integral_const_mul, intervalIntegral.integral_sub,
    intervalIntegrable_const, Nat.choose_le_two_pow, Nat.add_choose_mul_factorial_mul_factorial,
    Finset.prod_Ico_eq_prod_range, Finset.prod_range_reflect, pow_le_pow_left₀
    ResidueTailBridge.prod_shift_factorial, ResidueTailBridge.m0_Icc_eq_Ico_succ
      (B4/ResidueCertificateFactorialHarmonic.lean:39/45)
  Everything else is marked -- [Verified].
-/
import Mathlib
import Li2Lean.B4.HPIntegralForm
import Li2Lean.B4.ResidueCertificateFactorialHarmonic  -- prod_shift_factorial (:45)
import Li2Lean.B4.PositiveTailBeta                     -- hp_positive_beta_denom_lower (:70)
import Li2Lean.B4.NegativeTailElementary                -- negative-axis bracket certificates
-- [Verified] import cycle: none of these imports Li2Lean.AllN.Producers (Main does not either).

open MeasureTheory Set Filter Topology
open scoped BigOperators Interval

namespace Li2Lean.B4.TailAnalytic

noncomputable section

open Li2Lean.B4.Residues

/-- The real beta kernel from v13 `hp-tail.tex:198-204`.  It is repeated
here because `TailAnalyticSkeleton` and `HPIntegralForm` intentionally expose
different interface records with the same historical name. -/
def betaKernel (n : ℕ) (z t u : ℝ) : ℝ :=
  t * u / (1 - z * t * u) ^ 2 *
    (t ^ 2 * u ^ 2 * (1 - t) * (1 - u) /
      (1 - z * t * u) ^ 2) ^ n

lemma hp_mem_Icc_of_uIoc {x : ℝ} (hx : x ∈ Ι (0 : ℝ) 1) :
    x ∈ Icc (0 : ℝ) 1 := by
  rw [Set.uIoc_of_le zero_le_one] at hx
  exact ⟨hx.1.le, hx.2⟩

/-! ## Part 1.  Natural beta integral (no IBP, no Gamma).
Recursion `t^a(1-t)^(b+1) = t^a(1-t)^b - t^(a+1)(1-t)^b`, i.e.
`B(a+1,b+2) = B(a+1,b+1) - B(a+2,b+1)`; base case `integral_pow`. ~35 lines. -/

theorem hp_beta_nat (a b : ℕ) :
    ∫ t in (0 : ℝ)..1, t ^ a * (1 - t) ^ b =
      ((a.factorial : ℝ) * (b.factorial : ℝ)) / ((a + b + 1).factorial : ℝ) := by
  induction b generalizing a with
  | zero =>
    simp only [pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one, add_zero]
    rw [integral_pow, Nat.factorial_succ]
    push_cast
    field_simp
    simp            -- [Verified] closes (1^(a+1) - 0^(a+1)) bookkeeping
  | succ b ih =>
    have hsplit : (fun t : ℝ => t ^ a * (1 - t) ^ (b + 1)) =
        fun t => t ^ a * (1 - t) ^ b - t ^ (a + 1) * (1 - t) ^ b := by
      funext t; ring
    rw [hsplit, intervalIntegral.integral_sub
        (Continuous.intervalIntegrable (by fun_prop) _ _)
        (Continuous.intervalIntegrable (by fun_prop) _ _),
      ih a, ih (a + 1)]
    rw [show a + 1 + b + 1 = (a + b + 1) + 1 by ring,
      show a + (b + 1) + 1 = (a + b + 1) + 1 by ring,
      Nat.factorial_succ (a + b + 1), Nat.factorial_succ a, Nat.factorial_succ b]
    push_cast
    field_simp
    ring             -- a!b!(a+b+2) - (a+1)a!b! = a!b!(b+1)

/-! ## Part 2.  Closed form of Φ_n on the tail (v13 :13-15).  ~75 lines.
Reuses the division-free `prod_shift_factorial a c : a! * ∏_{t<c}(a+t+1) = (a+c)!`. -/

theorem hpNumerator_eval_tail (n m : ℕ) :
    (m.factorial : ℚ) * (hpNumerator n).eval ((3 * n + 2 + m : ℕ) : ℚ) =
      ((2 * n + 1 + m).factorial : ℚ) := by
  unfold hpNumerator
  simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  rw [ResidueTailBridge.m0_Icc_eq_Ico_succ, Finset.prod_Ico_eq_prod_range,
    show 3 * n + 1 + 1 - (n + 1) = 2 * n + 1 by omega]
  have hterm : ∀ t ∈ Finset.range (2 * n + 1),
      ((3 * n + 2 + m : ℕ) : ℚ) - ((n + 1 + t : ℕ) : ℚ) =
        (fun s : ℕ => (((m + s + 1 : ℕ)) : ℚ)) (2 * n + 1 - 1 - t) := by
    intro t ht
    have := Finset.mem_range.mp ht
    simp only
    rw [show m + (2 * n + 1 - 1 - t) + 1 = (3 * n + 2 + m) - (n + 1 + t) by omega,
      Nat.cast_sub (by omega)]
  rw [Finset.prod_congr rfl hterm,
    Finset.prod_range_reflect (fun s : ℕ => (((m + s + 1 : ℕ)) : ℚ)) (2 * n + 1)]
  have h := ResidueTailBridge.prod_shift_factorial m (2 * n + 1)
  rw [show m + (2 * n + 1) = 2 * n + 1 + m by omega] at h
  exact h

theorem hpPoleProd_eval_tail (n m : ℕ) :
    ((2 * n + 1 + m).factorial : ℚ) *
        ∏ j ∈ Finset.range (n + 1), (((3 * n + 2 + m : ℕ) : ℚ) - (j : ℚ)) =
      ((3 * n + 2 + m).factorial : ℚ) := by
  have hterm : ∀ j ∈ Finset.range (n + 1),
      ((3 * n + 2 + m : ℕ) : ℚ) - (j : ℚ) =
        (fun s : ℕ => ((((2 * n + 1 + m) + s + 1 : ℕ)) : ℚ)) (n + 1 - 1 - j) := by
    intro j hj
    have := Finset.mem_range.mp hj
    simp only
    rw [show (2 * n + 1 + m) + (n + 1 - 1 - j) + 1 = (3 * n + 2 + m) - j by omega,
      Nat.cast_sub (by omega)]
  rw [Finset.prod_congr rfl hterm,
    Finset.prod_range_reflect (fun s : ℕ => ((((2 * n + 1 + m) + s + 1 : ℕ)) : ℚ)) (n + 1)]
  have h := ResidueTailBridge.prod_shift_factorial (2 * n + 1 + m) (n + 1)
  rw [show 2 * n + 1 + m + (n + 1) = 3 * n + 2 + m by omega] at h
  exact h

theorem hpPhiValue_tail_closed (n m : ℕ) :
    hpPhiValue n (3 * n + 2 + m) =
      ((2 * n + 1 + m).factorial : ℚ) ^ 3 /
        ((m.factorial : ℚ) * ((3 * n + 2 + m).factorial : ℚ) ^ 2) := by
  have hN := hpNumerator_eval_tail n m
  have hD := hpPoleProd_eval_tail n m
  set P := ∏ j ∈ Finset.range (n + 1), (((3 * n + 2 + m : ℕ) : ℚ) - (j : ℚ)) with hPdef
  set A : ℚ := ((2 * n + 1 + m).factorial : ℚ)
  set N : ℚ := (hpNumerator n).eval ((3 * n + 2 + m : ℕ) : ℚ)
  have hP : P ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hD
    exact (by positivity : ((3 * n + 2 + m).factorial : ℚ) ≠ 0) hD.symm
  unfold hpPhiValue
  rw [Finset.prod_pow]            -- ∏ (x_j)^2 = (∏ x_j)^2
  rw [div_eq_div_iff (pow_ne_zero 2 hP) (by positivity), ← hD]
  linear_combination (A ^ 2 * P ^ 2) * hN

/-! ## Part 3.  Coefficient identity (the whole "beta identity" content).  ~30 lines. -/

/-- `β_m := ∫ u^(2n+1+m) (1-u)^n`, kept as an integral until the very end. -/
abbrev hpBetaMoment (n m : ℕ) : ℝ :=
  ∫ u in (0 : ℝ)..1, u ^ (2 * n + 1 + m) * (1 - u) ^ n

/-- `c_m := C(m+2n+1, 2n+1)`, the geometric-series coefficient of `(1-x)^-(2n+2)`. -/
abbrev hpBetaCoeff (n m : ℕ) : ℝ := (((m + (2 * n + 1)).choose (2 * n + 1) : ℕ) : ℝ)

theorem hpPhiValue_tail_eq_beta (n m : ℕ) :
    ((hpPhiValue n (3 * n + 2 + m) : ℚ) : ℝ) =
      ((2 * n + 1).factorial : ℝ) / (n.factorial : ℝ) ^ 2 *
        hpBetaCoeff n m * hpBetaMoment n m ^ 2 := by
  have hc := Nat.add_choose_mul_factorial_mul_factorial m (2 * n + 1)
  -- (m + (2n+1)).choose (2n+1) * m! * (2n+1)! = (m + (2n+1))!
  have hc' : hpBetaCoeff n m * (m.factorial : ℝ) * ((2 * n + 1).factorial : ℝ) =
      ((2 * n + 1 + m).factorial : ℝ) := by
    rw [show 2 * n + 1 + m = m + (2 * n + 1) by omega]
    exact_mod_cast hc
  rw [hpBetaMoment, hp_beta_nat, show 2 * n + 1 + m + n + 1 = 3 * n + 2 + m by omega,
    hpPhiValue_tail_closed]
  push_cast
  field_simp
  calc
    ((2 * n + 1 + m).factorial : ℝ) =
        hpBetaCoeff n m * (m.factorial : ℝ) *
          ((2 * n + 1).factorial : ℝ) := hc'.symm
    _ = (m.factorial : ℝ) * ((2 * n + 1).factorial : ℝ) *
          hpBetaCoeff n m := by ring

/-! ## Part 4.  Pointwise geometric expansion of the kernel.  ~35 lines. -/

lemma hp_unit_pow_bound (a b : ℕ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    0 ≤ x ^ a * (1 - x) ^ b ∧ x ^ a * (1 - x) ^ b ≤ 1 := by
  have h0 : 0 ≤ 1 - x := sub_nonneg.2 hx.2
  have h1 : 1 - x ≤ 1 := by linarith [hx.1]
  have ha : x ^ a ≤ 1 := pow_le_one₀ hx.1 hx.2
  have hb : (1 - x) ^ b ≤ 1 := pow_le_one₀ h0 h1
  have hb0 : 0 ≤ (1 - x) ^ b := pow_nonneg h0 _
  constructor
  · exact mul_nonneg (pow_nonneg hx.1 _) (pow_nonneg h0 _)
  · calc
      x ^ a * (1 - x) ^ b ≤ 1 * (1 - x) ^ b :=
        mul_le_mul_of_nonneg_right ha hb0
      _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hb (by norm_num)
      _ = 1 := by ring

lemma hp_den_pos {z t u : ℝ} (hz : |z| < 1)
    (ht : t ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (0 : ℝ) 1) : 0 < 1 - z * t * u := by
  have htu0 : 0 ≤ t * u := mul_nonneg ht.1 hu.1
  have htu1 : t * u ≤ 1 := mul_le_one₀ ht.2 hu.1 hu.2
  have : z * t * u ≤ |z| := by
    calc z * t * u = z * (t * u) := by ring
      _ ≤ |z| * (t * u) := mul_le_mul_of_nonneg_right (le_abs_self z) htu0
      _ ≤ |z| * 1 := mul_le_mul_of_nonneg_left htu1 (abs_nonneg z)
      _ = |z| := mul_one _
  linarith

theorem betaKernel_hasSum (n : ℕ) {z t u : ℝ} (hz : |z| < 1)
    (ht : t ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (0 : ℝ) 1) :
    HasSum (fun m : ℕ => hpBetaCoeff n m * z ^ m *
        ((t ^ (2 * n + 1 + m) * (1 - t) ^ n) * (u ^ (2 * n + 1 + m) * (1 - u) ^ n)))
      (betaKernel n z t u) := by
  have htu0 : 0 ≤ t * u := mul_nonneg ht.1 hu.1
  have htu1 : t * u ≤ 1 := mul_le_one₀ ht.2 hu.1 hu.2
  have hr : ‖z * t * u‖ < 1 := by
    rw [Real.norm_eq_abs, mul_assoc, abs_mul, abs_of_nonneg htu0]
    calc |z| * (t * u) ≤ |z| * 1 := mul_le_mul_of_nonneg_left htu1 (abs_nonneg z)
      _ < 1 := by linarith
  have hden : 1 - z * t * u ≠ 0 := (hp_den_pos hz ht hu).ne'
  have h := (hasSum_choose_mul_geometric_of_norm_lt_one (2 * n + 1) hr).mul_left
    ((t * u) ^ (2 * n + 1) * ((1 - t) * (1 - u)) ^ n)
  convert h using 1
  · funext m
    simp only [hpBetaCoeff]
    have htPow : t ^ (2 * n + 1 + m) =
        t ^ (2 * n + 1) * t ^ m := by
      rw [show 2 * n + 1 + m = (2 * n + 1) + m by omega, pow_add]
    have huPow : u ^ (2 * n + 1 + m) =
        u ^ (2 * n + 1) * u ^ m := by
      rw [show 2 * n + 1 + m = (2 * n + 1) + m by omega, pow_add]
    rw [htPow, huPow, mul_pow, mul_pow]
    rw [mul_pow]
    ring
  · unfold betaKernel
    rw [div_pow, show 2 * n + 1 + 1 = 2 * n + 2 by omega]
    field_simp [hden]
    rw [show 2 * n + 1 = 1 + 2 * n by omega, pow_add,
      show 2 * n + 2 = 2 + 2 * n by omega, pow_add,
      ← pow_mul]
    simp only [mul_pow]
    rw [← pow_mul, ← pow_mul]
    ring

/-! ## Part 5.  Termwise integration: two applications of
`intervalIntegral.hasSum_integral_of_dominated_convergence` with the CONSTANT
majorant `c_m |z|^m` (summable by the same geometric lemma).  ~90 lines. -/

lemma hpBetaCoeff_summable (n : ℕ) {z : ℝ} (hz : |z| < 1) :
    Summable (fun m : ℕ => hpBetaCoeff n m * |z| ^ m) :=
  (hasSum_choose_mul_geometric_of_norm_lt_one (2 * n + 1)
    (r := |z|) (by simpa [Real.norm_eq_abs, abs_abs] using hz)).summable

lemma hpBetaMoment_abs_le_one (n m : ℕ) : |hpBetaMoment n m| ≤ 1 := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
    (C := 1) (f := fun u : ℝ => u ^ (2 * n + 1 + m) * (1 - u) ^ n)
    (fun u hu => by
      have hb := hp_unit_pow_bound (2 * n + 1 + m) n (hp_mem_Icc_of_uIoc hu)
      rw [Real.norm_eq_abs, abs_of_nonneg hb.1]
      exact hb.2)
  simpa [hpBetaMoment, Real.norm_eq_abs] using h

/-- Inner integral (in `u`) for a fixed `t ∈ [0,1]`. -/
theorem hp_inner_hasSum (n : ℕ) {z t : ℝ} (hz : |z| < 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    HasSum (fun m : ℕ => hpBetaCoeff n m * z ^ m *
        (t ^ (2 * n + 1 + m) * (1 - t) ^ n) * hpBetaMoment n m)
      (∫ u in (0 : ℝ)..1, betaKernel n z t u) := by
  have hdom := intervalIntegral.hasSum_integral_of_dominated_convergence
    (μ := volume) (a := (0 : ℝ)) (b := 1)
    (F := fun m u => hpBetaCoeff n m * z ^ m *
      ((t ^ (2 * n + 1 + m) * (1 - t) ^ n) * (u ^ (2 * n + 1 + m) * (1 - u) ^ n)))
    (f := fun u => betaKernel n z t u)
    (fun m (_ : ℝ) => hpBetaCoeff n m * |z| ^ m)
    (fun m => (by fun_prop : Continuous _).aestronglyMeasurable)
    (fun m => ae_of_all _ fun u hu => by
      obtain ⟨ht0, ht1⟩ := hp_unit_pow_bound (2 * n + 1 + m) n ht
      obtain ⟨hu0, hu1⟩ := hp_unit_pow_bound (2 * n + 1 + m) n (hp_mem_Icc_of_uIoc hu)
      have hprod1 : (t ^ (2 * n + 1 + m) * (1 - t) ^ n) *
          (u ^ (2 * n + 1 + m) * (1 - u) ^ n) ≤ 1 := mul_le_one₀ ht1 hu0 hu1
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ hpBetaCoeff n m),
        abs_of_nonneg (mul_nonneg ht0 hu0)]
      calc hpBetaCoeff n m * |z| ^ m * ((t ^ (2 * n + 1 + m) * (1 - t) ^ n) *
            (u ^ (2 * n + 1 + m) * (1 - u) ^ n))
          ≤ hpBetaCoeff n m * |z| ^ m * 1 :=
            mul_le_mul_of_nonneg_left hprod1 (by positivity)
        _ = hpBetaCoeff n m * |z| ^ m := mul_one _)
    (ae_of_all _ fun _ _ => hpBetaCoeff_summable n hz)
    intervalIntegrable_const
    (ae_of_all _ fun u hu => betaKernel_hasSum n hz ht (hp_mem_Icc_of_uIoc hu))
  convert hdom using 1
  funext m
  -- ∫ u, K_m * U_m(u) = K_m * β_m; only association differs.
  rw [hpBetaMoment]
  calc
    hpBetaCoeff n m * z ^ m *
        (t ^ (2 * n + 1 + m) * (1 - t) ^ n) *
        (∫ u in (0 : ℝ)..1, u ^ (2 * n + 1 + m) * (1 - u) ^ n) =
      (hpBetaCoeff n m * z ^ m *
        (t ^ (2 * n + 1 + m) * (1 - t) ^ n)) *
        (∫ u in (0 : ℝ)..1, u ^ (2 * n + 1 + m) * (1 - u) ^ n) := by ring
    _ = ∫ x in (0 : ℝ)..1,
        (hpBetaCoeff n m * z ^ m *
          (t ^ (2 * n + 1 + m) * (1 - t) ^ n)) *
          (x ^ (2 * n + 1 + m) * (1 - x) ^ n) := by
      exact (intervalIntegral.integral_const_mul _ _).symm
    _ = ∫ x in (0 : ℝ)..1,
        hpBetaCoeff n m * z ^ m *
          (t ^ (2 * n + 1 + m) * (1 - t) ^ n *
            (x ^ (2 * n + 1 + m) * (1 - x) ^ n)) := by
      apply intervalIntegral.integral_congr
      intro x hx
      ring

/-- Outer integral (in `t`): the full double-integral series. -/
theorem hp_double_hasSum (n : ℕ) {z : ℝ} (hz : |z| < 1) :
    HasSum (fun m : ℕ => hpBetaCoeff n m * z ^ m * hpBetaMoment n m ^ 2)
      (∫ t in (0 : ℝ)..1, ∫ u in (0 : ℝ)..1, betaKernel n z t u) := by
  have hdom := intervalIntegral.hasSum_integral_of_dominated_convergence
    (μ := volume) (a := (0 : ℝ)) (b := 1)
    (F := fun m t => hpBetaCoeff n m * z ^ m *
      (t ^ (2 * n + 1 + m) * (1 - t) ^ n) * hpBetaMoment n m)
    (f := fun t => ∫ u in (0 : ℝ)..1, betaKernel n z t u)
    (fun m (_ : ℝ) => hpBetaCoeff n m * |z| ^ m)
    (fun m => (by fun_prop : Continuous _).aestronglyMeasurable)
    (fun m => ae_of_all _ fun t ht => by
      obtain ⟨ht0, ht1⟩ := hp_unit_pow_bound (2 * n + 1 + m) n (hp_mem_Icc_of_uIoc ht)
      have hβ := hpBetaMoment_abs_le_one n m
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_pow,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ hpBetaCoeff n m), abs_of_nonneg ht0]
      calc hpBetaCoeff n m * |z| ^ m * (t ^ (2 * n + 1 + m) * (1 - t) ^ n) *
            |hpBetaMoment n m|
          ≤ hpBetaCoeff n m * |z| ^ m * 1 * 1 := by gcongr
        _ = hpBetaCoeff n m * |z| ^ m := by ring)
    (ae_of_all _ fun _ _ => hpBetaCoeff_summable n hz)
    intervalIntegrable_const
    (ae_of_all _ fun t ht => hp_inner_hasSum n hz (hp_mem_Icc_of_uIoc ht))
  convert hdom using 1
  funext m
  have hc : (fun t : ℝ => hpBetaCoeff n m * z ^ m *
      (t ^ (2 * n + 1 + m) * (1 - t) ^ n) * hpBetaMoment n m) =
      fun t => (hpBetaCoeff n m * z ^ m * hpBetaMoment n m) *
        (t ^ (2 * n + 1 + m) * (1 - t) ^ n) := by
    funext t; ring
  rw [hc, intervalIntegral.integral_const_mul]
  simp only [hpBetaMoment]
  ring

/-! ## Part 6.  THE BETA IDENTITY (v13 eq:hp-beta, hp-tail.tex:201-205).  ~25 lines. -/

theorem hpRR_hasSum_beta (n : ℕ) {z : ℝ} (hz : |z| < 1) :
    HasSum (fun m : ℕ => ((hpPhiValue n (3 * n + 2 + m) : ℚ) : ℝ) * z ^ (3 * n + 2 + m))
      (((2 * n + 1).factorial : ℝ) / (n.factorial : ℝ) ^ 2 * z ^ (3 * n + 2) *
        ∫ t in (0 : ℝ)..1, ∫ u in (0 : ℝ)..1, betaKernel n z t u) := by
  have h := (hp_double_hasSum n hz).mul_left
    (((2 * n + 1).factorial : ℝ) / (n.factorial : ℝ) ^ 2 * z ^ (3 * n + 2))
  convert h using 1
  funext m
  rw [hpPhiValue_tail_eq_beta, pow_add]
  ring

theorem hpRR_beta_identity (n : ℕ) {z : ℝ} (hz : |z| < 1) :
    hpRR n z = ((2 * n + 1).factorial : ℝ) / (n.factorial : ℝ) ^ 2 * z ^ (3 * n + 2) *
      ∫ t in (0 : ℝ)..1, ∫ u in (0 : ℝ)..1, betaKernel n z t u := by
  unfold hpRR
  exact (hpRR_hasSum_beta n hz).tsum_eq

/-! ## Part 7.  Consumer (a): remainder bound.  ~90 lines. -/

theorem hp_double_integral_abs_le (n : ℕ) {z Cz M2 : ℝ}
    (hpref : ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1, |t * u / (1 - z * t * u) ^ 2| ≤ Cz)
    (hbr : ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
      |t ^ 2 * u ^ 2 * (1 - t) * (1 - u) / (1 - z * t * u) ^ 2| ≤ M2) :
    |∫ t in (0 : ℝ)..1, ∫ u in (0 : ℝ)..1, betaKernel n z t u| ≤ Cz * M2 ^ n := by
  have hK : ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
      |betaKernel n z t u| ≤ Cz * M2 ^ n := by
    intro t ht u hu
    unfold betaKernel
    rw [abs_mul, abs_pow]
    exact mul_le_mul (hpref t ht u hu)
      (pow_le_pow_left₀ (abs_nonneg _) (hbr t ht u hu) n) (by positivity)
      (le_trans (abs_nonneg _) (hpref t ht u hu))
  have hinner : ∀ t ∈ Ι (0 : ℝ) 1,
      ‖∫ u in (0 : ℝ)..1, betaKernel n z t u‖ ≤ Cz * M2 ^ n := by
    intro t ht
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
      (C := Cz * M2 ^ n) (f := fun u => betaKernel n z t u)
      (fun u hu => by
        simpa [Real.norm_eq_abs] using hK t (hp_mem_Icc_of_uIoc ht) u (hp_mem_Icc_of_uIoc hu))
    simpa using h
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
    (C := Cz * M2 ^ n) hinner
  simpa [Real.norm_eq_abs] using h

/-- `(2n+1)!/(n!)^2 = (2n+1)·C(2n,n) ≤ (2n+1)·4^n` (exact check n < 300). -/
theorem hp_beta_prefactor_le (n : ℕ) :
    ((2 * n + 1).factorial : ℝ) / (n.factorial : ℝ) ^ 2 ≤ (2 * n + 1 : ℝ) * 4 ^ n := by
  have h1 := Nat.add_choose_mul_factorial_mul_factorial n n   -- C(n+n,n) n! n! = (n+n)!
  have h2 := Nat.choose_le_two_pow (n + n) n                  -- C(n+n,n) ≤ 2^(n+n)
  have h4 : ((n + n).choose n : ℝ) ≤ 4 ^ n := by
    have : (2 : ℝ) ^ (n + n) = 4 ^ n := by
      rw [← two_mul, pow_mul]; norm_num
    rw [← this]; exact_mod_cast h2
  have hfs : ((2 * n + 1).factorial : ℝ) =
      (2 * n + 1 : ℝ) * ((n + n).choose n : ℝ) * (n.factorial : ℝ) ^ 2 := by
    rw [show 2 * n + 1 = (n + n) + 1 by ring, Nat.factorial_succ, ← h1]
    push_cast; ring
  rw [hfs, div_le_iff₀ (by positivity)]
  have : (0 : ℝ) ≤ (2 * n + 1 : ℝ) * (n.factorial : ℝ) ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h4 this]

/-- General remainder bound from a pointwise prefactor and bracket bound.  No
integrability of the kernel is needed (norm_integral_le_of_norm_le_const). -/
theorem hpRR_abs_le_of_bracket (n : ℕ) {z Cz M2 : ℝ} (hz : |z| < 1)
    (hCz : 0 ≤ Cz) (hM2 : 0 ≤ M2)
    (hpref : ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1, |t * u / (1 - z * t * u) ^ 2| ≤ Cz)
    (hbr : ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
      |t ^ 2 * u ^ 2 * (1 - t) * (1 - u) / (1 - z * t * u) ^ 2| ≤ M2) :
    |hpRR n z| ≤ (2 * n + 1 : ℝ) * 4 ^ n * |z| ^ (3 * n + 2) * (Cz * M2 ^ n) := by
  rw [hpRR_beta_identity n hz, abs_mul, abs_mul, abs_pow,
    abs_of_nonneg (by positivity :
      (0 : ℝ) ≤ ((2 * n + 1).factorial : ℝ) / (n.factorial : ℝ) ^ 2)]
  have hI := hp_double_integral_abs_le n hpref hbr
  have hP := hp_beta_prefactor_le n
  gcongr                           -- [Verified] P*|z|^k*|I| ≤ (2n+1)4^n*|z|^k*(Cz M2^n)

/-- Negative bases `a = -q` (z = -1/q ≤ 0): the prefactor is ≤ 1, so `Cz = 1`.
Output is EXACTLY the `hR` shape of `hpDecayNeg_exceptional_of_contour_beta_bound`
(NegativeTailContourDecay.lean:466) and `hpLR_tendsto_zero_of_contour_beta_bounds` (:377). -/
theorem hpRR_abs_le_neg {q : ℕ} (hq : 2 ≤ q) {M2 : ℝ} (hM2 : 0 ≤ M2)
    (hbr : ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
      t ^ 2 * u ^ 2 * ((1 - t) * (1 - u)) / (1 - (-(q : ℝ)⁻¹) * t * u) ^ 2 ≤ M2)
    (n : ℕ) :
    |hpRR n ((-(q : ℤ) : ℝ)⁻¹)| ≤
      (2 * n + 1 : ℝ) * 4 ^ n * (q : ℝ)⁻¹ ^ (3 * n + 2) * M2 ^ n := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hz : ((-(q : ℤ) : ℝ)⁻¹) = -(q : ℝ)⁻¹ := by push_cast; rw [inv_neg]
  have habs : |(-(q : ℝ)⁻¹)| = (q : ℝ)⁻¹ := by
    rw [abs_neg, abs_of_pos (inv_pos.2 hq0)]
  have hlt : |(-(q : ℝ)⁻¹)| < 1 := by
    rw [habs]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (by omega : 1 < q))
  have h := hpRR_abs_le_of_bracket n (z := -(q : ℝ)⁻¹) (Cz := 1) (M2 := M2) hlt
    zero_le_one hM2
    (fun t ht u hu => by
      have htu0 : 0 ≤ t * u := mul_nonneg ht.1 hu.1
      have htu1 : t * u ≤ 1 := mul_le_one₀ ht.2 hu.1 hu.2
      have hd : 1 ≤ 1 - (-(q : ℝ)⁻¹) * t * u := by
        have hqi : 0 ≤ (q : ℝ)⁻¹ := by positivity
        have : 0 ≤ (q : ℝ)⁻¹ * t * u :=
          mul_nonneg (mul_nonneg hqi ht.1) hu.1
        nlinarith
      have hd2 : 1 ≤ (1 - (-(q : ℝ)⁻¹) * t * u) ^ 2 := one_le_pow₀ hd
      rw [abs_of_nonneg (by positivity), div_le_one (by positivity)]
      linarith)
    (fun t ht u hu => by
      have hb := hbr t ht u hu
      rw [abs_of_nonneg (by
        have := sub_nonneg.2 ht.2; have := sub_nonneg.2 hu.2
        have := ht.1; have := hu.1; positivity)]
      calc t ^ 2 * u ^ 2 * (1 - t) * (1 - u) / (1 - -(q : ℝ)⁻¹ * t * u) ^ 2
          = t ^ 2 * u ^ 2 * ((1 - t) * (1 - u)) / (1 - -(q : ℝ)⁻¹ * t * u) ^ 2 := by ring
        _ ≤ M2 := hb)
  rw [hz, ← habs]
  simpa using h

/-- q = 9, 10 and every q ≥ 12 (and also q = 8, 11 with weaker rates) with the
uniform (4/27)^2 bracket `hp_negative_bracket_div_four27` (NegativeTailElementary.lean:136). -/
theorem hpRR_abs_le_neg_four27 {q : ℕ} (hq : 2 ≤ q) (n : ℕ) :
    |hpRR n ((-(q : ℤ) : ℝ)⁻¹)| ≤
      (2 * n + 1 : ℝ) * 4 ^ n * (q : ℝ)⁻¹ ^ (3 * n + 2) * ((4 / 27 : ℝ) ^ 2) ^ n :=
  hpRR_abs_le_neg hq (by norm_num) (fun t ht u hu =>
    Li2Lean.B4.hp_negative_bracket_div_four27 ht hu
      (by have : (0 : ℝ) ≤ (q : ℝ)⁻¹ := by positivity
          linarith)) n

/-- q = 11 instance with `hp_negative_bracket_div_q11` (NegativeTailElementary.lean:261). -/
theorem hpRR_abs_le_q11 (n : ℕ) :
    |hpRR n ((-((11 : ℕ) : ℤ) : ℝ)⁻¹)| ≤
      (2 * n + 1 : ℝ) * 4 ^ n * ((11 : ℕ) : ℝ)⁻¹ ^ (3 * n + 2) *
        (Li2Lean.B4.hpNegativeQ11M ^ 2) ^ n :=
  hpRR_abs_le_neg (q := 11) (by norm_num) (by positivity) (fun t ht u hu => by
    have hb := Li2Lean.B4.hp_negative_bracket_div_q11 ht hu
    have e : (1 - (-((11 : ℕ) : ℝ)⁻¹) * t * u) = 1 + t * u / 11 := by push_cast; ring
    rw [e]; exact hb) n

/-- Positive bases `a ≥ 12` (z = 1/a): prefactor ≤ (12/11)^2.  Output is EXACTLY
the `hR` shape of `hpLR_tendsto_zero_of_tail_bounds` (NegativeTailContourDecay.lean:205)
with `q := (a:ℝ)`, `Cz := (12/11)^2`.  The bracket input `hbr` is the refined
certificate M = 154/1000 (plan C3a; sup at z=1/12 is 0.0236921 ≤ M^2 = 0.023716). -/
theorem hpRR_abs_le_pos {a : ℤ} (ha : (12 : ℤ) ≤ a) {M2 : ℝ} (hM2 : 0 ≤ M2)
    (hbr : ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
      t ^ 2 * u ^ 2 * (1 - t) * (1 - u) / (1 - (a : ℝ)⁻¹ * t * u) ^ 2 ≤ M2)
    (n : ℕ) :
    |hpRR n ((a : ℝ)⁻¹)| ≤
      (2 * n + 1 : ℝ) * 4 ^ n * (a : ℝ)⁻¹ ^ (3 * n + 2) * ((12 / 11 : ℝ) ^ 2 * M2 ^ n) := by
  have ha' : (12 : ℝ) ≤ a := by exact_mod_cast ha
  have hapos : (0 : ℝ) < a := by linarith
  have hlt : |(a : ℝ)⁻¹| < 1 := by
    rw [abs_inv, abs_of_pos hapos]
    exact (inv_lt_one₀ hapos).2 (by linarith)
  have habs : |(a : ℝ)⁻¹| = (a : ℝ)⁻¹ := abs_of_pos (inv_pos.2 hapos)
  have h := hpRR_abs_le_of_bracket n (Cz := (12 / 11 : ℝ) ^ 2)
    hlt (by positivity) hM2
    (fun t ht u hu => by
      -- copy of the `hpref` block of hp_positive_beta_kernel_le (PositiveTailBeta.lean:114)
      have hden := Li2Lean.B4.hp_positive_beta_denom_lower ha' ht hu  -- 11/12 ≤ 1 - a⁻¹ t u (verified in the release)
      have htu0 : 0 ≤ t * u := mul_nonneg ht.1 hu.1
      have htu1 : t * u ≤ 1 := mul_le_one₀ ht.2 hu.1 hu.2
      have hdp : 0 < (1 - (a : ℝ)⁻¹ * t * u) ^ 2 := by
        have : 0 < 1 - (a : ℝ)⁻¹ * t * u := by linarith
        positivity
      rw [abs_of_nonneg (by positivity), div_le_iff₀ hdp]
      have hsq : (11 / 12 : ℝ) ^ 2 ≤ (1 - (a : ℝ)⁻¹ * t * u) ^ 2 := by
        nlinarith [sq_nonneg ((1 - (a : ℝ)⁻¹ * t * u) - 11 / 12)]
      nlinarith)
    (fun t ht u hu => by
      rw [abs_of_nonneg (by
        have := sub_nonneg.2 ht.2; have := sub_nonneg.2 hu.2
        have := ht.1; have := hu.1; positivity)]
      exact hbr t ht u hu)
  rwa [habs] at h

/-! ## Part 8.  Consumer (b): nonvanishing (v13 :552).  ~70 lines.
The outer integrand needs integrability for `intervalIntegral_pos_of_pos_on`; it is
obtained from continuity of the CLAMPED kernel (projIcc), which is globally
continuous because `1 - z·p·q ≥ 1 - |z| > 0` on the clamped range. -/

def hpClamp (x : ℝ) : ℝ := (Set.projIcc (0 : ℝ) 1 zero_le_one x : ℝ)

lemma hpClamp_mem (x : ℝ) : hpClamp x ∈ Icc (0 : ℝ) 1 :=
  (Set.projIcc (0 : ℝ) 1 zero_le_one x).2

lemma hpClamp_of_mem {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : hpClamp x = x := by
  simp [hpClamp, Set.projIcc_of_mem zero_le_one hx]

lemma continuous_hpClamp : Continuous hpClamp :=
  continuous_subtype_val.comp continuous_projIcc

lemma hp_clamped_kernel_continuous (n : ℕ) {z : ℝ} (hz : |z| < 1) :
    Continuous (Function.uncurry fun t u : ℝ => betaKernel n z (hpClamp t) (hpClamp u)) := by
  have hd : ∀ p : ℝ × ℝ, (1 - z * hpClamp p.1 * hpClamp p.2) ^ 2 ≠ 0 := fun p =>
    pow_ne_zero 2 (hp_den_pos hz (hpClamp_mem _) (hpClamp_mem _)).ne'
  have hc := continuous_hpClamp
  have h1 : Continuous fun p : ℝ × ℝ => hpClamp p.1 := hc.comp continuous_fst
  have h2 : Continuous fun p : ℝ × ℝ => hpClamp p.2 := hc.comp continuous_snd
  have hden : Continuous fun p : ℝ × ℝ => (1 - z * hpClamp p.1 * hpClamp p.2) ^ 2 := by
    fun_prop
  show Continuous fun p : ℝ × ℝ => betaKernel n z (hpClamp p.1) (hpClamp p.2)
  unfold betaKernel
  exact ((h1.mul h2).div hden hd).mul
    ((((((h1.pow 2).mul (h2.pow 2)).mul (continuous_const.sub h1)).mul
      (continuous_const.sub h2)).div hden hd).pow n)

theorem hp_double_integral_pos (n : ℕ) {z : ℝ} (hz : |z| < 1) :
    0 < ∫ t in (0 : ℝ)..1, ∫ u in (0 : ℝ)..1, betaKernel n z t u := by
  set Kc : ℝ → ℝ → ℝ := fun t u => betaKernel n z (hpClamp t) (hpClamp u) with hKc
  have hcont := hp_clamped_kernel_continuous n hz
  have hg : Continuous fun t => ∫ u in (0 : ℝ)..1, Kc t u :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hcont 0 1

    --  with (hf : Continuous fun p : ℝ × ℝ => Kc p.1 p.2) and continuous_const]
  have hEq : EqOn (fun t => ∫ u in (0 : ℝ)..1, betaKernel n z t u)
      (fun t => ∫ u in (0 : ℝ)..1, Kc t u) (uIcc (0 : ℝ) 1) := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le zero_le_one] at hu
    simp [hKc, hpClamp_of_mem ht, hpClamp_of_mem hu]
  rw [intervalIntegral.integral_congr hEq]
  refine intervalIntegral.intervalIntegral_pos_of_pos_on (hg.intervalIntegrable 0 1) ?_ zero_lt_one
  intro t ht
  have hrow : Continuous fun u => Kc t u :=
    hcont.comp (continuous_const.prodMk continuous_id)
  refine intervalIntegral.intervalIntegral_pos_of_pos_on (hrow.intervalIntegrable 0 1) ?_ zero_lt_one
  intro u hu
  have ht' : t ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self ht
  have hu' : u ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hu
  simp only [hKc, hpClamp_of_mem ht', hpClamp_of_mem hu']
  have hd := hp_den_pos hz ht' hu'
  have h1t : 0 < 1 - t := by linarith [ht.2]
  have h1u : 0 < 1 - u := by linarith [hu.2]
  have h0t := ht.1
  have h0u := hu.1
  unfold betaKernel
  positivity

theorem hpRR_ne_zero_of_real (n : ℕ) {z : ℝ} (hz0 : z ≠ 0) (hz : |z| < 1) :
    hpRR n z ≠ 0 := by
  rw [hpRR_beta_identity n hz]
  have hP : 0 < ((2 * n + 1).factorial : ℝ) / (n.factorial : ℝ) ^ 2 := by positivity
  exact mul_ne_zero (mul_ne_zero hP.ne' (pow_ne_zero _ hz0)) (hp_double_integral_pos n hz).ne'

/-- The `remainder_ne_zero` field of `HPNoAdjacentV13Input` (HPNoAdjacentActual.lean:54). -/
theorem hpRR_inv_ne_zero {a : ℤ} (ha : (12 : ℤ) ≤ a ∨ a ≤ -8) (n : ℕ) :
    hpRR n ((a : ℝ)⁻¹) ≠ 0 :=
  hpRR_ne_zero_of_real n
    (inv_ne_zero (by exact_mod_cast (show a ≠ 0 by omega)))
    (by
      rcases ha with ha | ha
      · have ha' : (12 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
        have hpos : (0 : ℝ) < a := by linarith
        rw [abs_inv, abs_of_pos hpos]
        exact (inv_lt_one₀ hpos).2 (by linarith)
      · have ha' : (a : ℝ) ≤ -8 := by exact_mod_cast ha
        have haneg : (a : ℝ) < 0 := by linarith
        have hpos : 0 < -(a : ℝ) := by linarith
        rw [abs_inv, abs_of_neg haneg]
        exact (inv_lt_one₀ hpos).2 (by linarith))

/-! ## Part 9.  Wiring (statements only; bodies are one-liners once B2 lands).

* `hpNoAdjInput_producer` (AllN/Producers.lean:158):
    fun a ha => hpNoAdjacentV13Input_of_producers ha (hpRR_inv_ne_zero ha) (B2 delta)
* q = 8 decay (given a rectangle certificate and `I`):
    hpDecayNeg_q8_of_beta_producer cert I hpRR_q8_beta_bound
* q = 9, 10:  hpDecayNeg_exceptional_of_contour_beta_bound (q := 9) _ cert I
      (by positivity) (hpRR_abs_le_neg_four27 (by norm_num)) hp_q9_rate_lt_one   -- rate 0.97303
* a ≥ 12: hpLR_tendsto_zero_of_tail_bounds (q := a) (Cz := (12/11)^2)
      (M2 := (154/1000)^2) ... (hR := hpRR_abs_le_pos ha _ hp_positive_bracket_refined)
      -- rate gamma_repo*K*4M^2/12 = 0.99241 (< 1)
  NOTE: `hpLR_tendsto_zero_of_contour_beta_bounds` still takes the full
  `I : HPNoAdjacentV13Input a` (uses only tail_representation); either wait for B2
  (delta) or use the decoupled `hpLR_abs_le_of_range` (plan C5a). -/

end

end Li2Lean.B4.TailAnalytic
