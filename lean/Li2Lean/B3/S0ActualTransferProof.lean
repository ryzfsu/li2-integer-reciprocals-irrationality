/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B3.S0TCoreBound
import Li2Lean.B3.C6SmoothedPairExpansion
import Li2Lean.B3.V13SmoothedDualityCertificate
import Li2Lean.B3.C7FieldsAndOneBody
import Li2Lean.B3.S0StageTwoKernel
import Li2Lean.B3.S0OuterM0Alignment

/-!
# H5 Full Assembly — Core Pointwise Bound, `hSwap`, Determinant Identity, and `v13_s0_transfer_actual_generic_proof` (`H5-assembly`)

This module completes the `H5` S0 analytic transfer chain:

1. **Sub-bridge 4 (`v13_contourWeight_prod_and_prefactor_bound`)**:
   Proves `‖V.Literal.vContourWeight q (piece, t)‖ ≤ (q : ℝ)` on all four contour pieces
   (`t ∈ [0, 1]`, `2 ≤ q`), `‖∏ i, V.Literal.vContourWeight q (p i)‖ ≤ (q : ℝ) ^ (4 * n)`,
   and `(4 : ℝ) ^ (4 * n) ≤ (((4 * n).factorial : ℝ) ^ 2 * ((5 * n).factorial : ℝ))` for
   `64 ≤ 4 * n`, yielding the prefactor/contour-weight envelope bound.
2. **Nonzero Pointwise Bound & Unconditional `h5_v13_s0T_core_bound`**:
   Combines `c5_c6_vContourPhi_self_energy_step`,
   `v13_c6_mixed_and_denominator_smoothed_transfer`,
   `v13_smoothed_duality_comparison_of_reference_unshifted`,
   `v13_c7_fields_and_one_body_transfer`, and
   `v13_contourWeight_prod_and_prefactor_bound` to discharge `hpt_nonzero` in
   `h5_v13_s0T_core_bound_of_pointwise`.
3. **Fubini Integrability (`v13LiteralAndreiefData_actual_hSwap`) and Determinant Identity
   (`v13_vContourActualGValue_eq_prefactor_mul_triple`)**:
   Evaluates the inner contour integral via `V.continuous_andreief_carrier` + `D.halign1`,
   combines it with `v13Literal_stage2_andreiefProduct_eq` on the compact unit-cube product
   to prove `hSwap`, and combines `v13Literal_vContourTripleIntegral_eq_qscale_inv_mul_s1`
   with `v13LiteralAndreiefData_actual_hM0` to prove
   `vContourActualGValue q n = V.Literal.vContourPrefactor q n * V.Literal.vContourTripleIntegral q n`.
4. **`v13_s0_transfer_actual_generic_proof`**:
   Constructs `VContourS0TransferDataActual q (vAlpha q) (vSigma q)` for any
   `hq : SignedVBaseRange q` and `P : VReferencePackage q hq`.
-/

open scoped BigOperators Matrix
open MeasureTheory Set

namespace Li2Lean.B3

noncomputable section

open Li2Lean V

/-! ## 1. Sub-bridge 4: Contour weight product and prefactor bound -/

theorem vContourCoefficient_norm_le {q : ℕ} (hq : 2 ≤ q) :
    ‖V.Literal.vContourCoefficient q‖ ≤ (Real.log (q : ℝ) + Real.pi) / (2 * Real.pi) := by
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (show 1 ≤ q by omega)
  have hlog : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hq1
  have hpi : 0 < Real.pi := Real.pi_pos
  unfold V.Literal.vContourCoefficient
  rw [norm_div, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real,
    Complex.norm_I, mul_one, Real.norm_eq_abs, abs_of_pos hpi]
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc
    ‖Complex.ofReal (Real.log (q : ℝ)) + Complex.I * Complex.ofReal Real.pi‖ ≤
        ‖Complex.ofReal (Real.log (q : ℝ))‖ + ‖Complex.I * Complex.ofReal Real.pi‖ :=
      norm_add_le _ _
    _ = Real.log (q : ℝ) + Real.pi := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog,
        norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpi]

theorem vContourCoefficient_sub_one_norm_le {q : ℕ} (hq : 2 ≤ q) :
    ‖V.Literal.vContourCoefficient q - 1‖ ≤ (Real.log (q : ℝ) + Real.pi) / (2 * Real.pi) := by
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (show 1 ≤ q by omega)
  have hlog : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hq1
  have hpi : 0 < Real.pi := Real.pi_pos
  have hpi_ne : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hpi.ne'
  have hden_ne : (2 : ℂ) * Complex.ofReal Real.pi * Complex.I ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero hpi_ne) Complex.I_ne_zero
  have hsub : V.Literal.vContourCoefficient q - 1 =
      (Complex.ofReal (Real.log (q : ℝ)) - Complex.I * Complex.ofReal Real.pi) /
        (2 * Complex.ofReal Real.pi * Complex.I) := by
    unfold V.Literal.vContourCoefficient
    rw [div_sub_one hden_ne]
    congr 1
    ring
  rw [hsub, norm_div, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real,
    Complex.norm_I, mul_one, Real.norm_eq_abs, abs_of_pos hpi]
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc
    ‖Complex.ofReal (Real.log (q : ℝ)) - Complex.I * Complex.ofReal Real.pi‖ ≤
        ‖Complex.ofReal (Real.log (q : ℝ))‖ + ‖Complex.I * Complex.ofReal Real.pi‖ :=
      norm_sub_le _ _
    _ = Real.log (q : ℝ) + Real.pi := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog,
        norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpi]

/-- Every piece of `V.Literal.vContourWeight q` has norm at most `(q : ℝ)` on `[0, 1]`. -/
theorem v13_contourWeight_norm_le_q {q : ℕ} (hq : 2 ≤ q)
    (piece : Fin 4) {t : ℝ} (_ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖V.Literal.vContourWeight q (piece, t)‖ ≤ (q : ℝ) := by
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < (q : ℝ) := by linarith
  have hpi : 0 < Real.pi := Real.pi_pos
  have hpi4 : Real.pi < 4 := Real.pi_lt_four
  have hlog_le : Real.log (q : ℝ) ≤ (q : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos hqpos
  unfold V.Literal.vContourWeight V.Literal.vContourComponentWeight V.Literal.vContourDerivative
  fin_cases piece
  · simp only [Fin.zero_eta, Fin.isValue, Fin.val_zero, Nat.ofNat_pos, ↓reduceIte, one_mul]
    have heq : Complex.ofReal (q : ℝ) - Complex.ofReal V.vContourRadius =
        Complex.ofReal ((q : ℝ) - V.vContourRadius) := by push_cast; ring
    rw [heq, Complex.norm_real, Real.norm_eq_abs, V.vContourRadius,
      abs_of_nonneg (by linarith)]
    linarith
  · simp only [Fin.mk_one, Fin.isValue, Fin.val_one, Nat.one_lt_ofNat, ↓reduceIte,
      one_ne_zero, one_mul]
    have heq : (1 : ℂ) - Complex.ofReal V.vContourRadius =
        Complex.ofReal (1 - V.vContourRadius) := by push_cast; ring
    rw [heq, Complex.norm_real, Real.norm_eq_abs, V.vContourRadius,
      abs_of_nonneg (by norm_num)]
    linarith
  · simp only [Fin.reduceFinMk, Fin.isValue, Nat.lt_irrefl, ↓reduceIte,
       (by decide : ¬ (2 : ℕ) = 0), (by decide : ¬ (2 : ℕ) = 1)]
    have hpt_norm : ‖V.Literal.vContourPoint q 2 t‖ = 3 / 5 := by
      rw [V.literal_piece_two_eq_vUpperArc, V.vUpperArc, ContourKit.p0CirclePoint_eq_circleMap]
      have hmem := circleMap_mem_sphere (0 : ℂ) (by norm_num [V.vContourRadius] : (0 : ℝ) ≤ V.vContourRadius) (Real.pi * t)
      simpa [Metric.mem_sphere, dist_zero_right, V.vContourRadius] using hmem
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hpi, hpt_norm]
    have hcoeff := vContourCoefficient_sub_one_norm_le hq
    calc
      ‖V.Literal.vContourCoefficient q - 1‖ * (Real.pi * (3 / 5)) ≤
          ((Real.log (q : ℝ) + Real.pi) / (2 * Real.pi)) * (Real.pi * (3 / 5)) :=
        mul_le_mul_of_nonneg_right hcoeff (by positivity)
      _ = (3 / 10 : ℝ) * (Real.log (q : ℝ) + Real.pi) := by
        field_simp [hpi.ne']
        ring
      _ ≤ (q : ℝ) := by linarith
  · simp only [Fin.reduceFinMk, Fin.isValue, (by decide : ¬ (3 : ℕ) < 2),
      (by decide : ¬ (3 : ℕ) = 2), (by decide : ¬ (3 : ℕ) = 0),
      (by decide : ¬ (3 : ℕ) = 1), ↓reduceIte]
    have hpt_norm : ‖V.Literal.vContourPoint q 3 t‖ = 3 / 5 := by
      rw [V.literal_piece_three_eq_vLowerArc, V.vLowerArc, ContourKit.p0CirclePoint_eq_circleMap]
      have hmem := circleMap_mem_sphere (0 : ℂ) (by norm_num [V.vContourRadius] : (0 : ℝ) ≤ V.vContourRadius) (Real.pi + Real.pi * t)
      simpa [Metric.mem_sphere, dist_zero_right, V.vContourRadius] using hmem
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hpi, hpt_norm]
    have hcoeff := vContourCoefficient_norm_le hq
    calc
      ‖V.Literal.vContourCoefficient q‖ * (Real.pi * (3 / 5)) ≤
          ((Real.log (q : ℝ) + Real.pi) / (2 * Real.pi)) * (Real.pi * (3 / 5)) :=
        mul_le_mul_of_nonneg_right hcoeff (by positivity)
      _ = (3 / 10 : ℝ) * (Real.log (q : ℝ) + Real.pi) := by
        field_simp [hpi.ne']
        ring
      _ ≤ (q : ℝ) := by linarith

theorem v13_contourWeight_prod_norm_le_q_pow {q d : ℕ} (hq : 2 ≤ q)
    (p : Fin d → Fin 4 × ℝ) (hp : ∀ i, (p i).2 ∈ Set.Icc (0 : ℝ) 1) :
    ‖∏ i : Fin d, V.Literal.vContourWeight q (p i)‖ ≤ (q : ℝ) ^ d := by
  rw [norm_prod]
  calc
    (∏ i : Fin d, ‖V.Literal.vContourWeight q (p i)‖) ≤ ∏ _ : Fin d, (q : ℝ) := by
      apply Finset.prod_le_prod₀
      · intro i _
        exact norm_nonneg _
      · intro i _
        exact v13_contourWeight_norm_le_q hq (p i).1 (hp i)
    _ = (q : ℝ) ^ d := by simp

theorem two_pow_le_factorial {m : ℕ} (hm : 4 ≤ m) : 2 ^ m ≤ m.factorial := by
  induction m, hm using Nat.le_induction with
  | base => decide
  | succ m _ ih =>
      rw [pow_succ', Nat.factorial_succ]
      exact Nat.mul_le_mul (by omega) ih

theorem four_pow_le_factorial_sq_mul_factorial {n : ℕ} (hn : 64 ≤ 4 * n) :
    (4 : ℝ) ^ (4 * n) ≤
      (((Nat.factorial (4 * n) : ℕ) : ℝ) ^ 2 * ((Nat.factorial (5 * n) : ℕ) : ℝ)) := by
  have hm4 : 4 ≤ 4 * n := by omega
  have h2 := two_pow_le_factorial hm4
  have h4_nat : 4 ^ (4 * n) ≤ (Nat.factorial (4 * n)) ^ 2 * Nat.factorial (5 * n) := by
    have hsq : 4 ^ (4 * n) = (2 ^ (4 * n)) ^ 2 := by
      rw [show (4 : ℕ) = 2 ^ 2 by rfl, ← pow_mul, mul_comm, pow_mul]
    rw [hsq]
    have hsq_le : (2 ^ (4 * n)) ^ 2 ≤ (Nat.factorial (4 * n)) ^ 2 :=
      Nat.pow_le_pow_left h2 2
    exact le_trans hsq_le (Nat.le_mul_of_pos_right _ (Nat.factorial_pos (5 * n)))
  exact_mod_cast h4_nat

/-- Sub-bridge 4: contour weight product and prefactor bound. -/
theorem v13_contourWeight_prod_and_prefactor_bound
    {q n : ℕ} (hq : SignedVBaseRange q) (hn : 64 ≤ 4 * n)
    (p : Fin (4 * n) → Fin 4 × ℝ)
    (hp : ∀ i, (p i).2 ∈ Set.Icc (0 : ℝ) 1) :
    ‖∏ i : Fin (4 * n), V.Literal.vContourWeight q (p i)‖ ≤
      Real.exp ((3 / 2 : ℝ) * Real.log (q : ℝ) * ((4 * n : ℕ) : ℝ) ^ 2 +
        ((4 * n : ℕ) : ℝ) - Real.log (s0TransferPrefactor q n)) /
        (4 : ℝ) ^ (4 * n) := by
  have hq_nat : 0 < q := lt_of_lt_of_le (by norm_num) hq.1
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq_nat
  have hpref_pos : 0 < s0TransferPrefactor q n := s0TransferPrefactor_pos hq.1
  have hfac_pos : 0 < (((Nat.factorial (4 * n) : ℕ) : ℝ) ^ 2 *
      ((Nat.factorial (5 * n) : ℕ) : ℝ)) := by positivity
  have hw := v13_contourWeight_prod_norm_le_q_pow hq.1 p hp
  have h4 := four_pow_le_factorial_sq_mul_factorial hn
  have hn_one : 1 ≤ n := by omega
  have hexp_le : 4 * n ≤ 24 * n ^ 2 := by
    calc
      4 * n = (4 * n) * 1 := by simp
      _ ≤ (4 * n) * n := Nat.mul_le_mul_left (4 * n) hn_one
      _ ≤ 24 * (n * n) := by
        simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
          (Nat.mul_le_mul_right (n * n) (show 4 ≤ 24 by omega))
      _ = 24 * n ^ 2 := by ring
  have hq_pow_eq : (q : ℝ) ^ (4 * n) * (q : ℝ) ^ s0Exponent (4 * n) =
      (q : ℝ) ^ (24 * n ^ 2) := by
    rw [s0Exponent_four_mul, ← pow_add, Nat.add_sub_of_le hexp_le]
  have hprod_le : (4 : ℝ) ^ (4 * n) * (q : ℝ) ^ (4 * n) * s0TransferPrefactor q n ≤
      Real.exp ((3 / 2 : ℝ) * Real.log (q : ℝ) * ((4 * n : ℕ) : ℝ) ^ 2 +
        ((4 * n : ℕ) : ℝ)) := by
    unfold s0TransferPrefactor
    calc
      (4 : ℝ) ^ (4 * n) * (q : ℝ) ^ (4 * n) *
          ((q : ℝ) ^ s0Exponent (4 * n) /
            (((Nat.factorial (4 * n) : ℕ) : ℝ) ^ 2 * ((Nat.factorial (5 * n) : ℕ) : ℝ))) =
        ((4 : ℝ) ^ (4 * n) /
          (((Nat.factorial (4 * n) : ℕ) : ℝ) ^ 2 * ((Nat.factorial (5 * n) : ℕ) : ℝ))) *
          ((q : ℝ) ^ (4 * n) * (q : ℝ) ^ s0Exponent (4 * n)) := by ring
      _ ≤ 1 * (q : ℝ) ^ (24 * n ^ 2) := by
        rw [hq_pow_eq]
        exact mul_le_mul_of_nonneg_right ((div_le_one hfac_pos).mpr h4) (by positivity)
      _ = Real.exp ((24 * n ^ 2 : ℕ) * Real.log (q : ℝ)) := by
        rw [one_mul, ← Real.rpow_natCast, Real.rpow_def_of_pos hqpos, mul_comm]
      _ = Real.exp ((3 / 2 : ℝ) * Real.log (q : ℝ) * ((4 * n : ℕ) : ℝ) ^ 2) := by
        congr 1
        push_cast
        ring
      _ ≤ Real.exp ((3 / 2 : ℝ) * Real.log (q : ℝ) * ((4 * n : ℕ) : ℝ) ^ 2 +
          ((4 * n : ℕ) : ℝ)) := by
        apply Real.exp_le_exp.mpr
        have hm_nonneg : (0 : ℝ) ≤ ((4 * n : ℕ) : ℝ) := by positivity
        linarith
  have hq_le_exp : (q : ℝ) ^ (4 * n) ≤
      Real.exp ((3 / 2 : ℝ) * Real.log (q : ℝ) * ((4 * n : ℕ) : ℝ) ^ 2 +
        ((4 * n : ℕ) : ℝ) - Real.log (s0TransferPrefactor q n)) /
        (4 : ℝ) ^ (4 * n) := by
    rw [Real.exp_sub, Real.exp_log hpref_pos, le_div_iff₀ (by positivity)]
    rw [le_div_iff₀ hpref_pos]
    linarith
  exact hw.trans hq_le_exp

/-! ## 2. Nonzero pointwise integrand bound and unconditional `h5_v13_s0T_core_bound` -/

theorem v13_vContourPhi_log_norm_le_of_ne_zero
    {q n : ℕ} {hq : SignedVBaseRange q} (P : VReferencePackage q hq)
    (hn : 64 ≤ 4 * n)
    (x : Fin (4 * n) → ℝ) (v : Fin (5 * n) → ℝ)
    (p : Fin (4 * n) → Fin 4 × ℝ)
    (hx : ∀ i, x i ∈ Set.Icc (0 : ℝ) 1)
    (hv : ∀ b, v b ∈ Set.Icc (0 : ℝ) 1)
    (hp : ∀ i, (p i).2 ∈ Set.Icc (0 : ℝ) 1)
    (hphi : V.Literal.vContourPhi q n x v
      (fun i => V.Literal.vContourPoint q (p i).1 (p i).2) ≠ 0) :
    Real.log ‖V.Literal.vContourPhi q n x v
        (fun i => V.Literal.vContourPoint q (p i).1 (p i).2)‖ ≤
      -(((vQlow q : ℚ) : ℝ) - (vKx q : ℝ) - (5 / 4 : ℝ) * (vKv q : ℝ) - (vKz q : ℝ)) *
        ((4 * n : ℕ) : ℝ) ^ 2 +
      (13 / 2 : ℝ) * ((4 * n : ℕ) : ℝ) * Real.log ((4 * n : ℕ) : ℝ) +
      3 * sigmaBudget P.Ax P.Av P.Az *
        (1 + Real.log (((4 * n : ℕ) : ℝ) ^ 2 / 3)) +
      (2 * denominatorTransferCost q + 7 + 130) := by
  let z : Fin (4 * n) → ℂ := fun i => V.Literal.vContourPoint q (p i).1 (p i).2
  have hz : ∀ i, z i ∈ V.vContourTrace q := fun i =>
    vContourPoint_mem_vContourTrace q (p i).1 (hp i)
  have hzv := vContourPhi_ne_zero_hxv hphi
  have hx0 := vContourPhi_ne_zero_hx0 (by omega) hphi
  have hv0 := vContourPhi_ne_zero_hv0 (by omega) hphi
  have hself := c5_c6_vContourPhi_self_energy_step (by omega) x v z hphi
  rw [p4C6SmoothedSelf_eq_vLogInteraction,
    p4C6SmoothedSelf_eq_vLogInteraction,
    p4C6SmoothedSelf_eq_vLogInteraction] at hself
  have hmix := v13_c6_mixed_and_denominator_smoothed_transfer hq (by omega) x v z hx hv hzv
  have hdual := v13_smoothed_duality_comparison_of_reference_unshifted P hn x v z hx hv
  have hc7 := v13_c7_fields_and_one_body_transfer hq P hn x v z hx hv hz hx0 hv0
  let μ := v13SmoothedEmpiricalMeasures hq (by omega)
    (fun i => (x i : ℂ)) (fun b => (v b : ℂ)) z
  let ν := P.measure
  have hquad : V.signedVQuadratic μ =
      V.vLogInteraction μ.μx μ.μx +
        V.vLogInteraction μ.μv μ.μv +
        V.vLogInteraction μ.μz μ.μz +
        V.vLogInteraction μ.μv μ.μz -
        V.vCrossInteraction μ.q μ.μx μ.μv := rfl
  have hm2_nonneg : 0 ≤ ((4 * n : ℕ) : ℝ) ^ 2 := sq_nonneg _
  have hdual_mul := mul_le_mul_of_nonneg_left hdual hm2_nonneg
  dsimp [μ, ν] at hmix hdual hc7 hquad hdual_mul
  simp only [v13SmoothedEmpiricalMeasures] at hmix hdual hc7 hquad hdual_mul
  change Real.log ‖V.Literal.vContourPhi q n x v z‖ ≤ _
  nlinarith [hself, hmix, hquad, hdual_mul, hc7]

theorem v13_pointwise_nonzero_integrand_bound
    {q : ℕ} (hq : SignedVBaseRange q) (P : VReferencePackage q hq)
    (n : ℕ) (hn : 64 ≤ 4 * n)
    (x : Fin (4 * n) → ℝ) (v : Fin (5 * n) → ℝ)
    (p : Fin (4 * n) → Fin 4 × ℝ)
    (hx : ∀ i, x i ∈ Set.Icc (0 : ℝ) 1)
    (hv : ∀ b, v b ∈ Set.Icc (0 : ℝ) 1)
    (hp : ∀ i, (p i).2 ∈ Set.Icc (0 : ℝ) 1)
    (hphi : V.Literal.vContourPhi q n x v
      (fun i => V.Literal.vContourPoint q (p i).1 (p i).2) ≠ 0) :
    ‖∏ i : Fin (4 * n), V.Literal.vContourWeight q (p i)‖ *
      ‖V.Literal.vContourPhi q n x v
        (fun i => V.Literal.vContourPoint q (p i).1 (p i).2)‖ ≤
      Real.exp (h5CoreBudgetRhs P n) / (4 : ℝ) ^ (4 * n) := by
  let Bphi : ℝ :=
    -(((vQlow q : ℚ) : ℝ) - (vKx q : ℝ) - (5 / 4 : ℝ) * (vKv q : ℝ) - (vKz q : ℝ)) *
      ((4 * n : ℕ) : ℝ) ^ 2 +
    (13 / 2 : ℝ) * ((4 * n : ℕ) : ℝ) * Real.log ((4 * n : ℕ) : ℝ) +
    3 * sigmaBudget P.Ax P.Av P.Az *
      (1 + Real.log (((4 * n : ℕ) : ℝ) ^ 2 / 3)) +
    (2 * denominatorTransferCost q + 7 + 130)
  let Bw : ℝ :=
    (3 / 2 : ℝ) * Real.log (q : ℝ) * ((4 * n : ℕ) : ℝ) ^ 2 +
      ((4 * n : ℕ) : ℝ) - Real.log (s0TransferPrefactor q n)
  have hw := v13_contourWeight_prod_and_prefactor_bound hq hn p hp
  have hphi_log := v13_vContourPhi_log_norm_le_of_ne_zero P hn x v p hx hv hp hphi
  have hpos : 0 < ‖V.Literal.vContourPhi q n x v
      (fun i => V.Literal.vContourPoint q (p i).1 (p i).2)‖ := norm_pos_iff.mpr hphi
  have hphi_le : ‖V.Literal.vContourPhi q n x v
      (fun i => V.Literal.vContourPoint q (p i).1 (p i).2)‖ ≤ Real.exp Bphi := by
    rw [← Real.exp_log hpos]
    exact Real.exp_le_exp.mpr hphi_log
  have hsum : Bw + Bphi = h5CoreBudgetRhs P n := by
    dsimp [Bw, Bphi, h5CoreBudgetRhs]
    ring
  rw [← hsum, Real.exp_add, mul_div_right_comm]
  exact mul_le_mul hw hphi_le (norm_nonneg _) (by positivity)

/-- Unconditional C5–C7 triple-integral core bound (`hcore`) for any reference package `P`. -/
theorem h5_v13_s0T_core_bound
    {q : ℕ} (hq : SignedVBaseRange q) (P : VReferencePackage q hq) :
    ∀ n : ℕ, 64 ≤ 4 * n →
      V.Literal.vContourTripleIntegral q n ≠ 0 →
      Real.log ‖V.Literal.vContourTripleIntegral q n‖ ≤
        -(((vQlow q : ℚ) : ℝ) - (3 / 2 : ℝ) * Real.log (q : ℝ) -
          (vKx q : ℝ) - (5 / 4 : ℝ) * (vKv q : ℝ) - (vKz q : ℝ)) *
          ((4 * n : ℕ) : ℝ) ^ 2 +
        (13 / 2 : ℝ) * ((4 * n : ℕ) : ℝ) *
          Real.log ((4 * n : ℕ) : ℝ) +
        3 * sigmaBudget P.Ax P.Av P.Az *
          (1 + Real.log (((4 * n : ℕ) : ℝ) ^ 2 / 3)) +
        (2 * denominatorTransferCost q + 7 + 130) +
          ((4 * n : ℕ) : ℝ) - Real.log (s0TransferPrefactor q n) :=
  h5_v13_s0T_core_bound_of_pointwise hq P (v13_pointwise_nonzero_integrand_bound hq P)

/-! ## 3. Fubini integrability `hSwap` and the determinant identity -/

private def h5Clamp01 (x : ℝ) : ℝ := min 1 (max 0 x)

private theorem h5Clamp01_mem (x : ℝ) : h5Clamp01 x ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨le_min (by positivity) (le_max_left _ _), min_le_left _ _⟩

private theorem h5Clamp01_eq_of_mem {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    h5Clamp01 x = x := by
  unfold h5Clamp01
  rw [max_eq_right hx.1, min_eq_right hx.2]

private theorem continuous_h5Clamp01 : Continuous h5Clamp01 := by
  unfold h5Clamp01
  exact continuous_const.min (continuous_const.max continuous_id)

private theorem continuous_vContourVandermonde_ofReal {d : ℕ} :
    Continuous (fun u : Fin d → ℝ => V.Literal.vContourVandermonde (fun i => (u i : ℂ))) := by
  unfold V.Literal.vContourVandermonde
  refine continuous_finset_prod _ (fun i _ => continuous_finset_prod _ (fun j _ => ?_))
  by_cases hij : i < j
  · simp only [if_pos hij]
    exact (Complex.continuous_ofReal.comp (continuous_apply j)).sub
      (Complex.continuous_ofReal.comp (continuous_apply i))
  · simp only [if_neg hij]
    exact continuous_const

private theorem continuous_rowRepl_M0_det (q n : ℕ) :
    Continuous (fun v : Fin (5 * n) → ℝ =>
      (P0.Env.rowRepl (V.vLiteralOuterM0 q n) (fun l => V.vLiteralOuterB0 n (v l))).det) := by
  classical
  have hentry : ∀ r c : Fin (5 * n) ⊕ Fin (4 * n),
      Continuous (fun v : Fin (5 * n) → ℝ =>
        P0.Env.rowRepl (V.vLiteralOuterM0 q n) (fun l => V.vLiteralOuterB0 n (v l)) r c) := by
    intro r c
    rcases r with l | k
    · simp only [P0.Env.rowRepl, V.vLiteralOuterB0]
      exact (Complex.continuous_ofReal.comp (continuous_apply l)).pow _
    · simp only [P0.Env.rowRepl]
      exact continuous_const
  apply Continuous.matrix_det
  exact continuous_matrix (fun r c => hentry r c)

/-- Fubini product-integrability `hSwap` for `V.v13LiteralAndreiefData_actual q n hq`. -/
theorem v13LiteralAndreiefData_actual_hSwap (q n : ℕ) (hq : 2 ≤ q) :
    let D := V.v13LiteralAndreiefData_actual q n hq
    Integrable
      (fun y : (Fin (4 * n) → ℝ) × (Fin (5 * n) → ℝ) =>
        V.andreiefProduct (D.M2 y.2) (D.a2 y.2) (D.b2 y.2) y.1 *
          ∫ p : Fin (4 * n) → Fin 4 × ℝ,
            V.andreiefProduct (D.M1 y.2) (D.a1 y.2) (D.b1 y.2) p
              ∂(Measure.pi fun _ : Fin (4 * n) => V.Literal.vContourParameterMeasure))
      ((Measure.pi fun _ : Fin (4 * n) => V.Literal.vContourUnitIntervalMeasure).prod
        (Measure.pi fun _ : Fin (5 * n) => V.Literal.vContourUnitIntervalMeasure)) := by
  classical
  intro D
  let μx := Measure.pi (fun _ : Fin (4 * n) => V.Literal.vContourUnitIntervalMeasure)
  let μv := Measure.pi (fun _ : Fin (5 * n) => V.Literal.vContourUnitIntervalMeasure)
  let μz := Measure.pi (fun _ : Fin (4 * n) => V.Literal.vContourParameterMeasure)
  letI : SigmaFinite V.Literal.vContourParameterMeasure := D.sigma_z
  let F2 : ((Fin (4 * n) → ℝ) × (Fin (5 * n) → ℝ)) → ℂ := fun y =>
    (-(q : ℂ)) ^ (Nat.choose (4 * n) 2) *
      (V.Literal.vContourVandermonde (fun i => (y.1 i : ℂ))) ^ 2 *
      V.Literal.vContourVandermonde (fun b => (y.2 b : ℂ)) *
      (∏ i : Fin (4 * n), (y.1 i : ℂ) ^ (3 * n)) /
      (∏ i : Fin (4 * n), ∏ b : Fin (5 * n),
        ((q : ℂ) + (h5Clamp01 (y.1 i) : ℂ) * (h5Clamp01 (y.2 b) : ℂ)))
  let F1 : ((Fin (4 * n) → ℝ) × (Fin (5 * n) → ℝ)) → ℂ := fun y =>
    (((4 * n).factorial : ℕ) : ℂ) *
      (P0.Env.rowRepl (V.vLiteralOuterM0 q n) (fun l => V.vLiteralOuterB0 n (y.2 l))).det
  have hden_ne : ∀ y : (Fin (4 * n) → ℝ) × (Fin (5 * n) → ℝ),
      (∏ i : Fin (4 * n), ∏ b : Fin (5 * n),
        ((q : ℂ) + (h5Clamp01 (y.1 i) : ℂ) * (h5Clamp01 (y.2 b) : ℂ))) ≠ 0 := by
    intro y
    exact v13Literal_stage2_denominator_ne_zero q n hq
      (fun i => h5Clamp01 (y.1 i)) (fun b => h5Clamp01 (y.2 b))
      (fun i => h5Clamp01_mem (y.1 i)) (fun b => h5Clamp01_mem (y.2 b))
  have hF2_cont : Continuous F2 := by
    have hnum : Continuous (fun y : (Fin (4 * n) → ℝ) × (Fin (5 * n) → ℝ) =>
        (-(q : ℂ)) ^ (Nat.choose (4 * n) 2) *
          (V.Literal.vContourVandermonde (fun i => (y.1 i : ℂ))) ^ 2 *
          V.Literal.vContourVandermonde (fun b => (y.2 b : ℂ)) *
          (∏ i : Fin (4 * n), (y.1 i : ℂ) ^ (3 * n))) := by
      refine (((continuous_const.mul
        ((continuous_vContourVandermonde_ofReal.comp continuous_fst).pow 2)).mul
        (continuous_vContourVandermonde_ofReal.comp continuous_snd)).mul ?_)
      exact continuous_finset_prod _ (fun i _ =>
        (Complex.continuous_ofReal.comp ((continuous_apply i).comp continuous_fst)).pow (3 * n))
    have hden : Continuous (fun y : (Fin (4 * n) → ℝ) × (Fin (5 * n) → ℝ) =>
        ∏ i : Fin (4 * n), ∏ b : Fin (5 * n),
          ((q : ℂ) + (h5Clamp01 (y.1 i) : ℂ) * (h5Clamp01 (y.2 b) : ℂ))) := by
      refine continuous_finset_prod _ (fun i _ => continuous_finset_prod _ (fun b _ => ?_))
      exact continuous_const.add
        ((Complex.continuous_ofReal.comp (continuous_h5Clamp01.comp ((continuous_apply i).comp continuous_fst))).mul
          (Complex.continuous_ofReal.comp (continuous_h5Clamp01.comp ((continuous_apply b).comp continuous_snd))))
    exact hnum.div hden hden_ne
  have hF1_cont : Continuous F1 :=
    continuous_const.mul ((continuous_rowRepl_M0_det q n).comp continuous_snd)
  have hG_cont : Continuous (fun y => F2 y * F1 y) := hF2_cont.mul hF1_cont
  let K : Set ((Fin (4 * n) → ℝ) × (Fin (5 * n) → ℝ)) :=
    (Set.univ.pi fun _ : Fin (4 * n) => Set.Icc (0 : ℝ) 1) ×ˢ
      (Set.univ.pi fun _ : Fin (5 * n) => Set.Icc (0 : ℝ) 1)
  have hK_compact : IsCompact K :=
    (isCompact_univ_pi (fun _ => isCompact_Icc)).prod
      (isCompact_univ_pi (fun _ => isCompact_Icc))
  obtain ⟨C, hC⟩ := hK_compact.exists_bound_of_continuousOn hG_cont.continuousOn
  have hK_ae : ∀ᵐ y ∂(μx.prod μv),
      (∀ i, y.1 i ∈ Set.Icc (0 : ℝ) 1) ∧ (∀ b, y.2 b ∈ Set.Icc (0 : ℝ) 1) :=
    (Measure.quasiMeasurePreserving_fst.ae
      (ae_mem_Icc_vContourUnitIntervalMeasure_pi (4 * n))).and
      (Measure.quasiMeasurePreserving_snd.ae
        (ae_mem_Icc_vContourUnitIntervalMeasure_pi (5 * n)))
  have hG_int : Integrable (fun y => F2 y * F1 y) (μx.prod μv) := by
    refine Integrable.of_bound hG_cont.aestronglyMeasurable C ?_
    filter_upwards [hK_ae] with y ⟨hx, hv⟩
    apply hC y
    refine ⟨Set.mem_univ_pi.mpr hx, Set.mem_univ_pi.mpr hv⟩
  refine hG_int.congr ?_
  filter_upwards [hK_ae] with y ⟨hx, hv⟩
  have hstage2 := v13Literal_stage2_andreiefProduct_eq q n hq y.1 y.2 hx hv
  have hF2_eq : F2 y = V.andreiefProduct (D.M2 y.2) (D.a2 y.2) (D.b2 y.2) y.1 := by
    change F2 y = V.andreiefProduct (V.literalXStageM2 q n y.2)
      (V.literalXStageA2 n) (V.literalXStageB2 q n y.2) y.1
    rw [hstage2]
    dsimp [F2]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    apply Finset.prod_congr rfl
    intro b _
    rw [h5Clamp01_eq_of_mem (hx i), h5Clamp01_eq_of_mem (hv b)]
  have hstage1 : (∫ p : Fin (4 * n) → Fin 4 × ℝ,
      V.andreiefProduct (D.M1 y.2) (D.a1 y.2) (D.b1 y.2) p ∂μz) = F1 y := by
    have hand := V.continuous_andreief_carrier V.Literal.vContourParameterMeasure
      (D.M1 y.2) (D.a1 y.2) (D.b1 y.2) (D.hint1 y.2) (D.hmom1 y.2)
    change (∫ p : Fin (4 * n) → Fin 4 × ℝ,
      (Matrix.of fun k l => D.a1 y.2 k (p l)).det *
        (P0.Env.rowRepl (D.M1 y.2) (fun l => D.b1 y.2 (p l))).det ∂μz) = F1 y
    rw [hand, D.halign1 y.2]
    rfl
  rw [hF2_eq, hstage1]

/-- Exact determinant-to-triple-integral identity for `vContourActualGValue q n`. -/
theorem v13_vContourActualGValue_eq_prefactor_mul_triple
    (q n : ℕ) (hq : 2 ≤ q) :
    vContourActualGValue q n =
      V.Literal.vContourPrefactor q n *
        V.Literal.vContourTripleIntegral q n := by
  let D := V.v13LiteralAndreiefData_actual q n hq
  have hqpos : 0 < q := by omega
  have hqpow : vContourQScale q n ≠ 0 := by
    unfold vContourQScale
    exact pow_ne_zero _ (by exact_mod_cast (Nat.ne_of_gt hqpos))
  have hfac :
      (((Nat.factorial (4 * n) : ℕ) : ℂ) ^ 2 *
        ((Nat.factorial (5 * n) : ℕ) : ℂ)) ≠ 0 := by
    exact mul_ne_zero
      (pow_ne_zero _ (by exact_mod_cast Nat.factorial_ne_zero (4 * n)))
      (by exact_mod_cast Nat.factorial_ne_zero (5 * n))
  have htriple := v13Literal_vContourTripleIntegral_eq_qscale_inv_mul_s1
    q n hq (v13LiteralAndreiefData_actual_hSwap q n hq)
  rw [V.v13S1AndreiefIntegral_eq_factorial_det] at htriple
  have hactual : vContourActualGValue q n = D.M0.det := by
    calc
      vContourActualGValue q n = V.Literal.vContourGValue q n :=
        vContourActualGValue_eq_literal q n
      _ = Complex.ofReal ((V.vOuterMomentMatrix q n).det) :=
        (V.vOuterMomentMatrix_det_eq_vContourGValue q n hq).symm
      _ = D.M0.det := (v13LiteralAndreiefData_actual_hM0 q n hq).symm
  rw [hactual, htriple]
  unfold V.Literal.vContourPrefactor
  unfold vContourQScale at hqpow ⊢
  have hfac' :
      (((Nat.factorial (n * 4) : ℕ) : ℂ) *
        ((Nat.factorial (n * 5) : ℕ) : ℂ)) ≠ 0 := by
    exact mul_ne_zero
      (by exact_mod_cast Nat.factorial_ne_zero (n * 4))
      (by exact_mod_cast Nat.factorial_ne_zero (n * 5))
  have hfacExact :
      (((Nat.factorial (4 * n) : ℕ) : ℂ) *
        ((Nat.factorial (5 * n) : ℕ) : ℂ)) ≠ 0 := by
    exact mul_ne_zero
      (by exact_mod_cast Nat.factorial_ne_zero (4 * n))
      (by exact_mod_cast Nat.factorial_ne_zero (5 * n))
  field_simp [hqpow, hfac, hfac', hfacExact]
  symm
  calc
    (↑(4 * n).factorial * ↑(5 * n).factorial) * D.M0.det /
          (↑(4 * n).factorial * ↑(5 * n).factorial) =
        D.M0.det *
          ((↑(4 * n).factorial * ↑(5 * n).factorial) /
            (↑(4 * n).factorial * ↑(5 * n).factorial)) := by ring
    _ = D.M0.det := by rw [div_self hfacExact]; ring

/-! ## 4. Closing `v13_s0_transfer_actual_generic` (`Li2Lean/B3/S0Actual.lean:286`) -/

/-- Complete `VContourS0Data` instance for every `n : ℕ` and `2 ≤ q`. -/
theorem v13_vContourS0Data_actual
    {q : ℕ} (hq : 2 ≤ q) {Tq : ℝ} (hTq : 0 < Tq) (n : ℕ) :
    VContourS0Data q n Tq (v13PhiMaxValue q Tq n) := by
  refine
    { q_ge_two := hq
      determinant_identity := v13_vContourActualGValue_eq_prefactor_mul_triple q n hq
      triple_norm_bound := ?_ }
  calc
    ‖V.Literal.vContourTripleIntegral q n‖ ≤
        Tq ^ (4 * n) * v13PhiMaxValue q Tq n :=
      v13PhiMaxValue_triple_norm hTq n
    _ ≤ Tq ^ (4 * n) * |v13PhiMaxValue q Tq n| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) (pow_nonneg hTq.le _)

/-- Complete, sorry-free construction of `v13_s0_transfer_actual_generic`
    (`Li2Lean/B3/S0Actual.lean:286`). -/
noncomputable def v13_s0_transfer_actual_generic_proof
    {q : ℕ} (hq : SignedVBaseRange q)
    (P : VReferencePackage q hq) :
    VContourS0TransferDataActual q (vAlpha q) (vSigma q) :=
  let Tq : ℝ := (q : ℝ)
  have hTq : 0 < Tq := by
    change (0 : ℝ) < (q : ℝ)
    exact_mod_cast (show 0 < q by linarith [hq.1])
  { q_ge_two := hq.1
    q_le_seven := hq.2
    Tq := Tq
    Tq_pos := hTq
    s0_data := fun n => v13_vContourS0Data_actual hq.1 hTq n
    phi_log_bound :=
      s0T_of_reference_facts hq P Tq hTq (h5_v13_s0T_core_bound hq P) }

end

end Li2Lean.B3

#print axioms Li2Lean.B3.v13_contourWeight_prod_and_prefactor_bound
#print axioms Li2Lean.B3.v13_vContourPhi_log_norm_le_of_ne_zero
#print axioms Li2Lean.B3.h5_v13_s0T_core_bound
#print axioms Li2Lean.B3.v13LiteralAndreiefData_actual_hSwap
#print axioms Li2Lean.B3.v13_vContourActualGValue_eq_prefactor_mul_triple
#print axioms Li2Lean.B3.v13_s0_transfer_actual_generic_proof
