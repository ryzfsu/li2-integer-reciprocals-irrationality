/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.V.VLiteralNestedBridge
import Li2Lean.P0.SourceMellin

namespace Li2Lean.V

noncomputable section

open MeasureTheory

/-- The literal v13 outer moment `M_ij(q)`, with the paper's `[0,1]^2`
integral (`v-analytic.tex:50-55,71-79`). -/
noncomputable def vOuterMoment (q i j : ℕ) : ℝ :=
  ∫ x : ℝ, ∫ y : ℝ,
    x ^ i * y ^ j / ((q : ℝ) + x * y)
      ∂Literal.vContourUnitIntervalMeasure
    ∂Literal.vContourUnitIntervalMeasure

/-- The logarithmic parameter `lambda_q` in the v13 moment identity
(`v-analytic.tex:53-54,66-79`). -/
noncomputable def vOuterLambda (q : ℕ) : ℝ :=
  Real.log (1 + (q : ℝ)⁻¹)

/-- The v13 dilogarithm parameter `beta_q`, using the project's exact real
series definition (`v-analytic.tex:53-54,77-83`; `Statement.lean:8`). -/
noncomputable def vOuterBeta (q : ℕ) : ℝ :=
  li2InvValue (-(q : ℤ))

private theorem vSourceLogTail (a : ℝ) (ha : a ≠ 0)
    (hq : |a⁻¹| < 1) (i : ℕ) :
    sourceT0 a i + a ^ i * sourceLog a =
      -∑' r : ℕ, (a⁻¹) ^ (r + 1) / ((i + r + 1 : ℕ) : ℝ) := by
  let q : ℝ := a⁻¹
  have hlog := Real.hasSum_pow_div_log_of_abs_lt_one hq
  have hsum : Summable (fun r : ℕ => q ^ (r + 1) / ((r + 1 : ℕ) : ℝ)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hlog.summable
  have hlogtsum :
      (∑' r : ℕ, q ^ (r + 1) / ((r + 1 : ℕ) : ℝ)) = -Real.log (1 - q) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hlog.tsum_eq
  have hsplit := hsum.sum_add_tsum_nat_add i
  have hprefix :
      (∑ r ∈ Finset.range i, q ^ (r + 1) / ((r + 1 : ℕ) : ℝ)) =
        q ^ i * sourceT0 a i := by
    simp only [sourceT0]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    rw [Finset.mem_range] at hr
    have hr' : r + 1 ≤ i := by omega
    have hpow : q ^ i * a ^ (i - (r + 1)) = q ^ (r + 1) := by
      rw [show q = a⁻¹ by rfl]
      rw [pow_sub₀ a ha hr']
      rw [inv_pow]
      field_simp [ha]
      simp [ha]
    rw [div_eq_mul_inv, div_eq_mul_inv]
    rw [← hpow]
    rw [Nat.cast_add, Nat.cast_one]
    ring
  have htail :
      (∑' r : ℕ, q ^ (r + i + 1) / ((r + i + 1 : ℕ) : ℝ)) =
        q ^ i * ∑' r : ℕ, q ^ (r + 1) / ((i + r + 1 : ℕ) : ℝ) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro r
    have hpow : q ^ i * q ^ (r + 1) = q ^ (r + i + 1) := by
      rw [← pow_add]
      congr 1
      omega
    rw [div_eq_mul_inv, div_eq_mul_inv, ← hpow]
    norm_num [Nat.cast_add, Nat.cast_one, add_comm, add_left_comm, add_assoc]
    ring
  have hlogval : sourceLog a =
      -∑' r : ℕ, q ^ (r + 1) / ((r + 1 : ℕ) : ℝ) := by
    rw [show sourceLog a = Real.log (1 - q) by rfl]
    linarith [hlogtsum]
  rw [hlogval]
  rw [hprefix, htail] at hsplit
  have hpowi : a ^ i * q ^ i = 1 := by
    rw [show q = a⁻¹ by rfl, ← mul_pow, mul_inv_cancel₀ ha, one_pow]
  have hmul := congrArg (fun z : ℝ => a ^ i * z) hsplit
  simp only [mul_add, ← mul_assoc, hpowi] at hmul
  dsimp [q] at hmul ⊢
  linarith [hmul]

private theorem vSourceBetaTail (a : ℝ) (ha : a ≠ 0)
    (hq : |a⁻¹| < 1) (i : ℕ) :
    sourceB0 a i - a ^ i * sourceBeta a =
      -∑' r : ℕ,
          (a⁻¹) ^ (r + 1) / ((i + r + 1 : ℕ) : ℝ) ^ 2 := by
  let q : ℝ := a⁻¹
  have hgeom : Summable (fun r : ℕ => |q| ^ (r + 1)) := by
    have hq' : |(|q| : ℝ)| < 1 := by
      simpa only [q, abs_abs] using hq
    have hg := (hasSum_geometric_of_abs_lt_one hq').summable
    have hm := hg.mul_left |q|
    convert hm using 1
    ext r
    rw [pow_succ]
    ring
  have hsum : Summable (fun r : ℕ => q ^ (r + 1) /
      ((r + 1 : ℕ) : ℝ) ^ 2) := by
    apply hgeom.of_norm_bounded
    intro r
    have hden : (1 : ℝ) ≤ ((r + 1 : ℕ) : ℝ) ^ 2 := by
      have hr : (1 : ℝ) ≤ ((r + 1 : ℕ) : ℝ) := by
        exact_mod_cast (show 1 ≤ r + 1 by omega)
      nlinarith
    have hden0 : 0 < ((r + 1 : ℕ) : ℝ) ^ 2 := by positivity
    rw [Real.norm_eq_abs, abs_div, abs_pow]
    rw [abs_of_nonneg (sq_nonneg ((r + 1 : ℕ) : ℝ))]
    rw [div_le_iff₀ hden0]
    have hpow : 0 ≤ |q| ^ (r + 1) := pow_nonneg (abs_nonneg q) _
    nlinarith
  have hsplit := hsum.sum_add_tsum_nat_add i
  have hprefix :
      (∑ r ∈ Finset.range i, q ^ (r + 1) / ((r + 1 : ℕ) : ℝ) ^ 2) =
        q ^ i * sourceB0 a i := by
    simp only [sourceB0]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    rw [Finset.mem_range] at hr
    have hr' : r + 1 ≤ i := by omega
    have hpow : q ^ i * a ^ (i - (r + 1)) = q ^ (r + 1) := by
      rw [show q = a⁻¹ by rfl]
      rw [pow_sub₀ a ha hr']
      rw [inv_pow]
      field_simp [ha]
      simp [ha]
    rw [div_eq_mul_inv, div_eq_mul_inv]
    rw [← hpow]
    rw [Nat.cast_add, Nat.cast_one]
    ring
  have htail :
      (∑' r : ℕ, q ^ (r + i + 1) / ((r + i + 1 : ℕ) : ℝ) ^ 2) =
        q ^ i * ∑' r : ℕ, q ^ (r + 1) / ((i + r + 1 : ℕ) : ℝ) ^ 2 := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro r
    have hpow : q ^ i * q ^ (r + 1) = q ^ (r + i + 1) := by
      rw [← pow_add]
      congr 1
      omega
    rw [div_eq_mul_inv, div_eq_mul_inv, ← hpow]
    norm_num [Nat.cast_add, Nat.cast_one, add_comm, add_left_comm, add_assoc]
    ring
  have hbetaval : sourceBeta a =
      ∑' r : ℕ, q ^ (r + 1) / ((r + 1 : ℕ) : ℝ) ^ 2 := by
    simp [sourceBeta, q, Nat.cast_add, Nat.cast_one]
  rw [hbetaval]
  rw [hprefix, htail] at hsplit
  have hpowi : a ^ i * q ^ i = 1 := by
    rw [show q = a⁻¹ by rfl, ← mul_pow, mul_inv_cancel₀ ha, one_pow]
  have hmul := congrArg (fun z : ℝ => a ^ i * z) hsplit
  simp only [mul_add, ← mul_assoc, hpowi] at hmul
  dsimp [q] at hmul ⊢
  linarith [hmul]

theorem vSourceMellinSeries (a : ℝ) (ha : a ≠ 0)
    (hq : |a⁻¹| < 1) (i j : ℕ) :
    sourceM a i j = sourceMSeries a i j := by
  let q : ℝ := a⁻¹
  have hqabs : |q| < 1 := hq
  have hgeom : Summable (fun r : ℕ => |q| ^ (r + 1)) := by
    have hqabsabs : |(|q| : ℝ)| < 1 := by simpa using hqabs
    have hg := (hasSum_geometric_of_abs_lt_one hqabsabs).summable
    have hm := hg.mul_left |q|
    convert hm using 1
    ext r
    rw [pow_succ]
    ring
  have hsum (k : ℕ) :
      Summable (fun r : ℕ => q ^ (r + 1) /
        ((k + r + 1 : ℕ) : ℝ)) := by
    apply hgeom.of_norm_bounded
    intro r
    have hden : (1 : ℝ) ≤ ((k + r + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 1 ≤ k + r + 1 by omega)
    have hden0 : 0 < ((k + r + 1 : ℕ) : ℝ) := by positivity
    rw [Real.norm_eq_abs, abs_div, abs_pow,
      abs_of_nonneg (show (0 : ℝ) ≤ ((k + r + 1 : ℕ) : ℝ) by positivity)]
    exact div_le_self (pow_nonneg (abs_nonneg q) _) hden
  by_cases hij : i = j
  · subst j
    simp [sourceM, sourceB0ij, sourceC0, sourceA0, sourceMSeries]
    rw [mul_comm (sourceBeta a) (a ^ i), vSourceBetaTail a ha hq i]
    apply congrArg Neg.neg
    apply tsum_congr
    intro r
    have hd : ((i + r + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp [hd]
    rw [one_div]
    have hpow : (a⁻¹) ^ (r + 1) * a ^ (r + 1) = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ ha, one_pow]
    rw [hpow]
    norm_num [Nat.cast_add, Nat.cast_one]
  · have hdi : (j : ℝ) - (i : ℝ) ≠ 0 := by
      have hji : j ≠ i := by
        intro h
        exact hij h.symm
      have hcast : (j : ℝ) ≠ (i : ℝ) := by exact_mod_cast hji
      exact sub_ne_zero.mpr hcast
    have hi := vSourceLogTail a ha hq i
    have hj := vSourceLogTail a ha hq j
    rw [sourceM]
    simp only [sourceB0ij, sourceC0, sourceA0, if_neg hij, mul_zero, sub_zero]
    have hfrac :
        (sourceT0 a i - sourceT0 a j) / ((j : ℝ) - (i : ℝ)) +
            sourceLog a * ((a ^ i - a ^ j) / ((j : ℝ) - (i : ℝ))) =
          (sourceT0 a i + a ^ i * sourceLog a -
            (sourceT0 a j + a ^ j * sourceLog a)) /
              ((j : ℝ) - (i : ℝ)) := by
      field_simp [hdi]
      ring
    rw [hfrac, hi, hj]
    let fi : ℕ → ℝ := fun r =>
      (a⁻¹) ^ (r + 1) / ((i + r + 1 : ℕ) : ℝ)
    let fj : ℕ → ℝ := fun r =>
      (a⁻¹) ^ (r + 1) / ((j + r + 1 : ℕ) : ℝ)
    have hfi : Summable fi := by simpa [fi, q] using hsum i
    have hfj : Summable fj := by simpa [fj, q] using hsum j
    have hdiffsum := hfi.tsum_sub hfj
    have hpoint (r : ℕ) :
        (fi r - fj r) / ((j : ℝ) - (i : ℝ)) =
          (a⁻¹) ^ (r + 1) /
            ((i + r + 1 : ℕ) : ℝ) /
            ((j + r + 1 : ℕ) : ℝ) := by
      dsimp [fi, fj]
      have h1 : ((i + r + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      have h2 : ((j + r + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      have hd : ((j + r + 1 : ℕ) : ℝ) - ((i + r + 1 : ℕ) : ℝ) =
          (j : ℝ) - (i : ℝ) := by
        norm_num [Nat.cast_add, Nat.cast_one]
      field_simp [hdi, h1, h2]
      rw [hd]
    calc
      (-∑' r : ℕ, fi r - -∑' r : ℕ, fj r) /
          ((j : ℝ) - (i : ℝ)) =
          -((∑' r : ℕ, fi r - ∑' r : ℕ, fj r) /
            ((j : ℝ) - (i : ℝ))) := by ring
      _ = -∑' r : ℕ, (fi r - fj r) /
          ((j : ℝ) - (i : ℝ)) := by
        rw [← hdiffsum, div_eq_mul_inv, ← tsum_mul_right]
        congr 1
      _ = -∑' r : ℕ, (a⁻¹) ^ (r + 1) /
          ((i + r + 1 : ℕ) : ℝ) /
          ((j + r + 1 : ℕ) : ℝ) := by
        congr 1
        apply tsum_congr
        intro r
        simpa [Nat.cast_add, Nat.cast_one, inv_pow] using hpoint r

private def vSignedSourceUnitInterval : Measure ℝ :=
  volume.restrict (Set.Ioo (0 : ℝ) 1)

private theorem vSignedSourcePowerIntegral (n : ℕ) :
    (∫ x : ℝ, x ^ n ∂vSignedSourceUnitInterval) =
      1 / ((n + 1 : ℕ) : ℝ) := by
  rw [vSignedSourceUnitInterval]
  rw [← integral_Ioc_eq_integral_Ioo]
  rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [integral_pow]
  norm_num

private theorem vSignedSourceIntegrablePow (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n) vSignedSourceUnitInterval := by
  have hbase : IntegrableOn (fun x : ℝ => x ^ n) (Set.Ioo (0 : ℝ) 1) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le
      (by norm_num : (0 : ℝ) ≤ 1)).mp (intervalIntegral.intervalIntegrable_pow n)
  simpa only [IntegrableOn, vSignedSourceUnitInterval] using hbase

private theorem vSignedMellinKernelHasSum (a : ℝ) (ha : a ≠ 0)
    (hq : |a⁻¹| < 1) (i j : ℕ) (x y : ℝ)
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) (hy : y ∈ Set.Ioo (0 : ℝ) 1) :
    HasSum (fun r : ℕ => (a⁻¹) ^ (r + 1) *
        (x ^ (i + r) * y ^ (j + r)))
      (x ^ i * y ^ j / (a - x * y)) := by
  let q : ℝ := a⁻¹
  have hqabs : |q| < 1 := hq
  have hqxy : |q * x * y| < 1 := by
    rw [abs_mul, abs_mul, abs_of_pos hx.1, abs_of_pos hy.1]
    have hxy : |q| * x * y ≤ |q| * x := by
      have h := mul_le_mul_of_nonneg_left hy.2.le
        (mul_nonneg (abs_nonneg q) hx.1.le)
      simpa [mul_assoc] using h
    have hx' : |q| * x ≤ |q| := by
      have h := mul_le_mul_of_nonneg_left hx.2.le (abs_nonneg q)
      simpa using h
    calc
      |q| * x * y ≤ |q| * x := hxy
      _ ≤ |q| := hx'
      _ < 1 := hqabs
  have hgeo := hasSum_geometric_of_abs_lt_one hqxy
  have hmul := hgeo.mul_left (q * x ^ i * y ^ j)
  have hterm (r : ℕ) :
      q * x ^ i * y ^ j * (q * x * y) ^ r =
        q ^ (r + 1) * (x ^ (i + r) * y ^ (j + r)) := by
    rw [mul_pow, mul_pow, pow_succ, pow_add, pow_add]
    ring
  have hqa : q * a = 1 := by
    dsimp [q]
    exact inv_mul_cancel₀ ha
  have hden : a - x * y ≠ 0 := by
    intro h
    have hae : a = x * y := sub_eq_zero.mp h
    have hqxy' : q * x * y = 1 := by
      calc
        q * x * y = q * (x * y) := by ring
        _ = q * a := by rw [← hae]
        _ = 1 := hqa
    have habs : |q * x * y| = 1 := by rw [hqxy', abs_one]
    exact (ne_of_lt hqxy) habs
  have hqden : 1 - q * x * y ≠ 0 := by
    intro h
    have hqxy' : q * x * y = 1 := by linarith
    have habs : |q * x * y| = 1 := by rw [hqxy', abs_one]
    exact (ne_of_lt hqxy) habs
  have hfrac : q / (1 - q * x * y) = 1 / (a - x * y) := by
    field_simp [hqden, hden]
    calc
      q * (a - x * y) = q * a - q * (x * y) := by ring
      _ = 1 - q * x * y := by rw [hqa]; ring
  have hvalue : q * x ^ i * y ^ j * (1 - q * x * y)⁻¹ =
      x ^ i * y ^ j / (a - x * y) := by
    calc
      q * x ^ i * y ^ j * (1 - q * x * y)⁻¹ =
          (x ^ i * y ^ j) * (q / (1 - q * x * y)) := by ring
      _ = (x ^ i * y ^ j) * (1 / (a - x * y)) := by rw [hfrac]
      _ = x ^ i * y ^ j / (a - x * y) := by ring
  convert hmul using 1
  · funext r
    exact (hterm r).symm
  · exact hvalue.symm

private theorem vSignedInnerMellinIntegral (a : ℝ) (ha : a ≠ 0)
    (hq : |a⁻¹| < 1) (i j : ℕ) (x : ℝ)
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    (∫ y : ℝ, x ^ i * y ^ j / (a - x * y)
        ∂vSignedSourceUnitInterval) =
      ∑' r : ℕ, (a⁻¹) ^ (r + 1) * x ^ (i + r) /
        ((j + r + 1 : ℕ) : ℝ) := by
  let μ := vSignedSourceUnitInterval
  let q : ℝ := a⁻¹
  let F : ℕ → ℝ → ℝ := fun r y =>
    q ^ (r + 1) * (x ^ (i + r) * y ^ (j + r))
  have hqabs : |q| < 1 := hq
  have hqsum : Summable (fun r : ℕ => |q| ^ (r + 1)) := by
    have hqabsabs : |(|q| : ℝ)| < 1 := by simpa using hqabs
    have hg := (hasSum_geometric_of_abs_lt_one hqabsabs).summable
    have hm := hg.mul_left |q|
    convert hm using 1
    ext r
    rw [pow_succ]
    ring
  have hF (r : ℕ) : Integrable (F r) μ := by
    have hp := vSignedSourceIntegrablePow (j + r)
    simpa only [μ, F, mul_assoc] using
      hp.const_mul (q ^ (r + 1) * x ^ (i + r))
  have hpowint (k : ℕ) :
      (∫ y : ℝ, y ^ k ∂μ) = 1 / ((k + 1 : ℕ) : ℝ) := by
    simpa [μ] using vSignedSourcePowerIntegral k
  have hnorm (r : ℕ) :
      (∫ y : ℝ, ‖F r y‖ ∂μ) =
        |q| ^ (r + 1) * x ^ (i + r) /
          ((j + r + 1 : ℕ) : ℝ) := by
    calc
      (∫ y : ℝ, ‖F r y‖ ∂μ) =
          ∫ y : ℝ, (|q| ^ (r + 1) * x ^ (i + r)) *
            y ^ (j + r) ∂μ := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
        change |q ^ (r + 1) * (x ^ (i + r) * y ^ (j + r))| = _
        rw [abs_mul, abs_pow, abs_mul,
          abs_of_nonneg (pow_nonneg hx.1.le _),
          abs_of_nonneg (pow_nonneg hy.1.le _)]
        ring
      _ = (|q| ^ (r + 1) * x ^ (i + r)) *
          ∫ y : ℝ, y ^ (j + r) ∂μ := integral_const_mul _ _
      _ = _ := by rw [hpowint]; ring
  have hsum : Summable (fun r : ℕ => ∫ y : ℝ, ‖F r y‖ ∂μ) := by
    apply hqsum.of_norm_bounded
    intro r
    rw [hnorm r]
    rw [Real.norm_of_nonneg
      (div_nonneg (mul_nonneg (pow_nonneg (abs_nonneg q) _)
        (pow_nonneg hx.1.le _)) (by positivity))]
    have hcoeff : 0 ≤ |q| ^ (r + 1) := pow_nonneg (abs_nonneg q) _
    have hxpow : x ^ (i + r) ≤ 1 := pow_le_one₀ hx.1.le hx.2.le
    have hden : (1 : ℝ) ≤ ((j + r + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 1 ≤ j + r + 1 by omega)
    have hden0 : 0 < ((j + r + 1 : ℕ) : ℝ) := by positivity
    apply (div_le_iff₀ hden0).2
    calc
      |q| ^ (r + 1) * x ^ (i + r) ≤ |q| ^ (r + 1) * 1 :=
        mul_le_mul_of_nonneg_left hxpow hcoeff
      _ ≤ |q| ^ (r + 1) * ((j + r + 1 : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hden hcoeff
  have hpoint : (fun y : ℝ => ∑' r : ℕ, F r y) =ᵐ[μ]
      (fun y => x ^ i * y ^ j / (a - x * y)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
    exact (vSignedMellinKernelHasSum a ha hq i j x y hx hy).tsum_eq
  calc
    (∫ y : ℝ, x ^ i * y ^ j / (a - x * y) ∂μ) =
        ∫ y : ℝ, ∑' r : ℕ, F r y ∂μ := integral_congr_ae hpoint.symm
    _ = ∑' r : ℕ, ∫ y : ℝ, F r y ∂μ :=
      (integral_tsum_of_summable_integral_norm hF hsum).symm
    _ = _ := by
      apply tsum_congr
      intro r
      have hterm (y : ℝ) : F r y =
          ((q ^ (r + 1) * x ^ (i + r)) * y ^ (j + r)) := by
        dsimp [F]
        ring
      rw [show (∫ y : ℝ, F r y ∂μ) =
        ∫ y : ℝ, (q ^ (r + 1) * x ^ (i + r)) * y ^ (j + r) ∂μ by
          apply integral_congr_ae
          filter_upwards with y
          exact hterm y]
      rw [integral_const_mul, hpowint]
      ring

private theorem vSignedMellinMeasureIntegral (a : ℝ) (ha : a ≠ 0)
    (hq : |a⁻¹| < 1) (i j : ℕ) :
    (∫ x : ℝ, ∫ y : ℝ, x ^ i * y ^ j / (a - x * y)
        ∂vSignedSourceUnitInterval ∂vSignedSourceUnitInterval) =
      ∑' r : ℕ,
        (a⁻¹) ^ (r + 1) / ((i + r + 1 : ℕ) : ℝ) /
          ((j + r + 1 : ℕ) : ℝ) := by
  let μ := vSignedSourceUnitInterval
  let q : ℝ := a⁻¹
  let F : ℕ → ℝ → ℝ := fun r x =>
    q ^ (r + 1) * x ^ (i + r) / ((j + r + 1 : ℕ) : ℝ)
  have hqabs : |q| < 1 := hq
  have hqsum : Summable (fun r : ℕ => |q| ^ (r + 1)) := by
    have hqabsabs : |(|q| : ℝ)| < 1 := by simpa using hqabs
    have hg := (hasSum_geometric_of_abs_lt_one hqabsabs).summable
    have hm := hg.mul_left |q|
    convert hm using 1
    ext r
    rw [pow_succ]
    ring
  have hpowint (k : ℕ) :
      (∫ x : ℝ, x ^ k ∂μ) = 1 / ((k + 1 : ℕ) : ℝ) := by
    simpa [μ] using vSignedSourcePowerIntegral k
  have hinner :
      (fun x : ℝ => ∫ y : ℝ, x ^ i * y ^ j / (a - x * y) ∂μ) =ᵐ[μ]
        (fun x => ∑' r : ℕ, F r x) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    simpa [μ, F, q] using vSignedInnerMellinIntegral a ha hq i j x hx
  have hF (r : ℕ) : Integrable (F r) μ := by
    have hp := vSignedSourceIntegrablePow (i + r)
    have hden : ((j + r + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have hrepr : F r = fun x =>
        (q ^ (r + 1) / ((j + r + 1 : ℕ) : ℝ)) * x ^ (i + r) := by
      funext x
      dsimp [F]
      ring
    rw [hrepr]
    exact hp.const_mul _
  have hnorm (r : ℕ) :
      (∫ x : ℝ, ‖F r x‖ ∂μ) =
        |q| ^ (r + 1) / ((j + r + 1 : ℕ) : ℝ) /
          ((i + r + 1 : ℕ) : ℝ) := by
    have hdenj : 0 < ((j + r + 1 : ℕ) : ℝ) := by positivity
    calc
      (∫ x : ℝ, ‖F r x‖ ∂μ) =
          ∫ x : ℝ,
            (|q| ^ (r + 1) / ((j + r + 1 : ℕ) : ℝ)) *
              x ^ (i + r) ∂μ := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
        change |q ^ (r + 1) * x ^ (i + r) /
            ((j + r + 1 : ℕ) : ℝ)| = _
        rw [abs_div, abs_mul, abs_pow,
          abs_of_nonneg (pow_nonneg hx.1.le _),
          abs_of_pos hdenj]
        ring
      _ = (|q| ^ (r + 1) / ((j + r + 1 : ℕ) : ℝ)) *
          ∫ x : ℝ, x ^ (i + r) ∂μ := integral_const_mul _ _
      _ = _ := by rw [hpowint]; ring
  have hsum : Summable (fun r : ℕ => ∫ x : ℝ, ‖F r x‖ ∂μ) := by
    apply hqsum.of_norm_bounded
    intro r
    rw [hnorm r]
    rw [Real.norm_of_nonneg (div_nonneg (div_nonneg
      (pow_nonneg (abs_nonneg q) _) (by positivity)) (by positivity))]
    have hcoeff : 0 ≤ |q| ^ (r + 1) := pow_nonneg (abs_nonneg q) _
    have hdeni : (1 : ℝ) ≤ ((i + r + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 1 ≤ i + r + 1 by omega)
    have hdenj : (1 : ℝ) ≤ ((j + r + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 1 ≤ j + r + 1 by omega)
    have hdeni0 : 0 < ((i + r + 1 : ℕ) : ℝ) := by positivity
    have hdenj0 : 0 < ((j + r + 1 : ℕ) : ℝ) := by positivity
    apply (div_le_iff₀ hdeni0).2
    apply (div_le_iff₀ hdenj0).2
    calc
      |q| ^ (r + 1) ≤ |q| ^ (r + 1) * ((i + r + 1 : ℕ) : ℝ) :=
        le_mul_of_one_le_right hcoeff hdeni
      _ ≤ |q| ^ (r + 1) * ((i + r + 1 : ℕ) : ℝ) *
          ((j + r + 1 : ℕ) : ℝ) := by
        apply le_mul_of_one_le_right
        · positivity
        · exact hdenj
  calc
    (∫ x : ℝ, ∫ y : ℝ, x ^ i * y ^ j / (a - x * y) ∂μ ∂μ) =
        ∫ x : ℝ, ∑' r : ℕ, F r x ∂μ := integral_congr_ae hinner
    _ = ∑' r : ℕ, ∫ x : ℝ, F r x ∂μ :=
      (integral_tsum_of_summable_integral_norm hF hsum).symm
    _ = _ := by
      apply tsum_congr
      intro r
      have hrepr : F r = fun x =>
          (q ^ (r + 1) / ((j + r + 1 : ℕ) : ℝ)) * x ^ (i + r) := by
        funext x
        dsimp [F]
        ring
      rw [hrepr, integral_const_mul, hpowint]
      ring

theorem vSignedSourceMellinIntegralSeries (a : ℝ) (ha : a ≠ 0)
    (hq : |a⁻¹| < 1) (i j : ℕ) :
    sourceMIntegral a i j = sourceMSeries a i j := by
  change -(∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1,
      x ^ i * y ^ j / (a - x * y)) =
    -∑' r : ℕ,
      (a⁻¹) ^ (r + 1) / ((i + r + 1 : ℕ) : ℝ) /
        ((j + r + 1 : ℕ) : ℝ)
  have hmeasure := vSignedMellinMeasureIntegral a ha hq i j
  have hinterval :
      (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1,
        x ^ i * y ^ j / (a - x * y)) =
        ∫ x : ℝ, ∫ y : ℝ, x ^ i * y ^ j / (a - x * y)
          ∂vSignedSourceUnitInterval ∂vSignedSourceUnitInterval := by
    simp only [vSignedSourceUnitInterval,
      intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      integral_Ioc_eq_integral_Ioo]
  rw [hinterval, hmeasure]

/-- The actual v13 outer moment is the source Mellin entry at `a = -q`.
This binds the signed Mellin expansion to the `[0,1]^2` moment used in the
determinant construction (`v-analytic.tex:50-83`,
`v-arithmetic.tex:20-32`). -/
theorem vOuterMoment_eq_sourceM (q : ℕ) (hq : 2 ≤ q) (i j : ℕ) :
    vOuterMoment q i j = sourceM (-(q : ℝ)) i j := by
  have hqpos : 0 < (q : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hq)
  have hqgt : (1 : ℝ) < (q : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hq)
  have ha : -(q : ℝ) ≠ 0 := neg_ne_zero.mpr hqpos.ne'
  have hqinv : |(-(q : ℝ))⁻¹| < 1 := by
    have hinv : (q : ℝ)⁻¹ < 1 := by
      rw [inv_eq_one_div]
      exact (div_lt_one hqpos).2 hqgt
    calc
      |(-(q : ℝ))⁻¹| = |-((q : ℝ)⁻¹)| := by rw [neg_inv]
      _ = (q : ℝ)⁻¹ := by
        rw [abs_neg, abs_of_pos (inv_pos.mpr hqpos)]
      _ < 1 := hinv
  have hμ : Literal.vContourUnitIntervalMeasure = vSignedSourceUnitInterval := by
    unfold Literal.vContourUnitIntervalMeasure vSignedSourceUnitInterval
    exact (Measure.restrict_congr_set Ioo_ae_eq_Icc).symm
  have hsourceIntegral :
      sourceMIntegral (-(q : ℝ)) i j =
        -(∫ x : ℝ, ∫ y : ℝ,
          x ^ i * y ^ j / (-(q : ℝ) - x * y)
            ∂vSignedSourceUnitInterval ∂vSignedSourceUnitInterval) := by
    unfold sourceMIntegral
    have hinterval :
        (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1,
          x ^ i * y ^ j / (-(q : ℝ) - x * y)) =
          (∫ x : ℝ, ∫ y : ℝ,
            x ^ i * y ^ j / (-(q : ℝ) - x * y)
              ∂vSignedSourceUnitInterval ∂vSignedSourceUnitInterval) := by
      simp only [vSignedSourceUnitInterval,
        intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
        integral_Ioc_eq_integral_Ioo]
    rw [hinterval]
  have hkernel (x y : ℝ) :
      -(x ^ i * y ^ j / (-(q : ℝ) - x * y)) =
        x ^ i * y ^ j / ((q : ℝ) + x * y) := by
    rw [show -(q : ℝ) - x * y = -((q : ℝ) + x * y) by ring,
      div_neg, neg_neg]
  have hnegIntegral :
      -(∫ x : ℝ, ∫ y : ℝ,
        x ^ i * y ^ j / (-(q : ℝ) - x * y)
          ∂vSignedSourceUnitInterval ∂vSignedSourceUnitInterval) =
        ∫ x : ℝ, ∫ y : ℝ,
          x ^ i * y ^ j / ((q : ℝ) + x * y)
            ∂vSignedSourceUnitInterval ∂vSignedSourceUnitInterval := by
    calc
      _ = ∫ x : ℝ,
          -(∫ y : ℝ,
            x ^ i * y ^ j / (-(q : ℝ) - x * y)
              ∂vSignedSourceUnitInterval)
          ∂vSignedSourceUnitInterval := by rw [← integral_neg]
      _ = ∫ x : ℝ, ∫ y : ℝ,
          x ^ i * y ^ j / ((q : ℝ) + x * y)
            ∂vSignedSourceUnitInterval ∂vSignedSourceUnitInterval := by
          apply integral_congr_ae
          filter_upwards with x
          calc
            _ = ∫ y : ℝ,
                -(x ^ i * y ^ j / (-(q : ℝ) - x * y))
                  ∂vSignedSourceUnitInterval := by rw [← integral_neg]
            _ = _ := by
                apply integral_congr_ae
                filter_upwards with y
                exact hkernel x y
  calc
    vOuterMoment q i j =
        ∫ x : ℝ, ∫ y : ℝ,
          x ^ i * y ^ j / ((q : ℝ) + x * y)
            ∂vSignedSourceUnitInterval ∂vSignedSourceUnitInterval := by
      unfold vOuterMoment
      rw [hμ]
    _ = sourceMIntegral (-(q : ℝ)) i j :=
      hnegIntegral.symm.trans hsourceIntegral.symm
    _ = sourceMSeries (-(q : ℝ)) i j :=
      vSignedSourceMellinIntegralSeries (-(q : ℝ)) ha hqinv i j
    _ = sourceM (-(q : ℝ)) i j :=
      (vSourceMellinSeries (-(q : ℝ)) ha hqinv i j).symm

/-- The entrywise closed-form obligation in v13
`v-analytic.tex:71-83` and `v-arithmetic.tex:20-32`. -/
def vOuterMomentIdentity (q : ℕ) (_hq : 2 ≤ q) : Prop :=
  ∀ i j : ℕ,
    vOuterMoment q i j =
      (vBEntry (-(q : ℤ)) i j : ℝ) +
        vOuterLambda q * (vCEntry (-(q : ℤ)) i j : ℝ) -
        vOuterBeta q * (vAEntry (-(q : ℤ)) i j : ℝ)

private theorem vMomentT_real (q i : ℕ) :
    (vMomentT (-(q : ℤ)) i : ℝ) = sourceT0 (-(q : ℝ)) i := by
  unfold vMomentT sourceT0
  push_cast
  apply Finset.sum_congr rfl
  intro r hr
  simp [Nat.cast_add, Nat.cast_one, div_eq_mul_inv]

private theorem vMomentB_real (q i : ℕ) :
    (vMomentB (-(q : ℤ)) i : ℝ) = sourceB0 (-(q : ℝ)) i := by
  unfold vMomentB sourceB0
  push_cast
  apply Finset.sum_congr rfl
  intro r hr
  simp [Nat.cast_add, Nat.cast_one, div_eq_mul_inv]

private theorem vBEntry_real (q i j : ℕ) :
    (vBEntry (-(q : ℤ)) i j : ℝ) =
      sourceB0ij (-(q : ℝ)) i j := by
  by_cases hij : i = j
  · subst j
    simp [vBEntry, sourceB0ij, vMomentB_real]
  · simp [vBEntry, sourceB0ij, hij, vMomentT_real]

private theorem vCEntry_real (q i j : ℕ) :
    (vCEntry (-(q : ℤ)) i j : ℝ) =
      sourceC0 (-(q : ℝ)) i j := by
  by_cases hij : i = j
  · subst j
    simp [vCEntry, sourceC0]
  · simp [vCEntry, sourceC0, hij]

private theorem vAEntry_real (q i j : ℕ) :
    (vAEntry (-(q : ℤ)) i j : ℝ) =
      sourceA0 (-(q : ℝ)) i j := by
  by_cases hij : i = j
  · subst j
    simp [vAEntry, sourceA0]
  · simp [vAEntry, sourceA0, hij]

private theorem vOuterLambda_eq_sourceLog (q : ℕ) :
    vOuterLambda q = sourceLog (-(q : ℝ)) := by
  simp [vOuterLambda, sourceLog, inv_neg]

private theorem vOuterBeta_eq_sourceBeta (q : ℕ) :
    vOuterBeta q = sourceBeta (-(q : ℝ)) := by
  simp [vOuterBeta, sourceBeta, li2InvValue, inv_neg]

/-- The signed Mellin evaluation gives the literal v13 moment identity
`M = B + lambda C - beta A` entrywise (`v-analytic.tex:71-83`,
`v-arithmetic.tex:20-32`). The `q = 2` instance is the same specialization
used by the frozen Li2(1/2) determinant. -/
theorem vOuterMomentIdentity_of_signedMellin (q : ℕ) (hq : 2 ≤ q) :
    vOuterMomentIdentity q hq := by
  intro i j
  rw [vOuterMoment_eq_sourceM q hq i j]
  rw [vBEntry_real q i j, vCEntry_real q i j, vAEntry_real q i j,
    vOuterLambda_eq_sourceLog q, vOuterBeta_eq_sourceBeta q]
  unfold sourceM
  ring

/-- The elementary row operator adding `lambda_q` times each corresponding
`C` row to the `B-beta A` row (`v-analytic.tex:80-83`). -/
def vOuterRowOperator {m k : ℕ} (lambda : ℝ) :
    Matrix (Fin (2 * m + k)) (Fin (2 * m + k)) ℝ :=
  fun i j =>
    (if i = j then 1 else 0) +
      (if m ≤ i.val ∧ i.val < 2 * m ∧ j.val = i.val - m then lambda else 0)

/-- Applying the v13 row operation to an arbitrary square matrix
(`v-analytic.tex:80-83`). -/
def vOuterRowAdded {m k : ℕ} (lambda : ℝ)
    (A : Matrix (Fin (2 * m + k)) (Fin (2 * m + k)) ℝ) :
    Matrix (Fin (2 * m + k)) (Fin (2 * m + k)) ℝ :=
  fun i j =>
    if hi : m ≤ i.val ∧ i.val < 2 * m then
      A i j + lambda * A ⟨i.val - m, by omega⟩ j
    else A i j

/-- The row operator is lower triangular because it only adds an earlier
`C` row to a later middle row (`v-analytic.tex:80-83`). -/
theorem vOuterRowOperator_lowerTriangular {m k : ℕ} (lambda : ℝ) :
    (vOuterRowOperator (m := m) (k := k) lambda).IsLowerTriangular := by
  intro i j hij
  simp only [OrderDual.toDual_lt_toDual] at hij
  simp only [vOuterRowOperator]
  rw [if_neg (ne_of_lt hij), if_neg]
  · ring
  · intro h
    rcases h with ⟨hm, hu, hsource⟩
    have hji : j.val < i.val := by omega
    exact absurd hij (not_lt.mpr (le_of_lt (Fin.lt_def.mpr hji)))

/-- The row operation matrix has determinant one
(`v-analytic.tex:80-83`). -/
theorem vOuterRowOperator_det {m k : ℕ} (lambda : ℝ) :
    (vOuterRowOperator (m := m) (k := k) lambda).det = 1 := by
  rw [Matrix.det_of_lowerTriangular
    (vOuterRowOperator (m := m) (k := k) lambda)
    (vOuterRowOperator_lowerTriangular lambda)]
  apply Finset.prod_eq_one
  intro i hi
  simp only [vOuterRowOperator, if_true]
  rw [if_neg]
  · ring
  · intro h
    rcases h with ⟨hm, hu, hsource⟩
    omega

/-- The matrix product by the v13 row operator is exactly the simultaneous
middle-row addition (`v-analytic.tex:80-83`). -/
theorem vOuterRowOperator_mul {m k : ℕ} (lambda : ℝ)
    (A : Matrix (Fin (2 * m + k)) (Fin (2 * m + k)) ℝ) :
    vOuterRowOperator (m := m) (k := k) lambda * A = vOuterRowAdded lambda A := by
  classical
  ext i j
  simp only [Matrix.mul_apply, vOuterRowOperator, add_mul, Finset.sum_add_distrib,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  by_cases htop : i.val < m
  · have hzero :
        (∑ l : Fin (2 * m + k),
          (if m ≤ i.val ∧ i.val < 2 * m ∧ l.val = i.val - m then
            lambda * A l j else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro l hl
      rw [if_neg]
      omega
    rw [hzero, add_zero]
    simp [vOuterRowAdded, htop]
  · by_cases hmid : i.val < 2 * m
    · let s : Fin (2 * m + k) := ⟨i.val - m, by omega⟩
      have hsum :
          (∑ l : Fin (2 * m + k),
            (if m ≤ i.val ∧ i.val < 2 * m ∧ l.val = i.val - m then
              lambda * A l j else 0)) = lambda * A s j := by
        rw [Finset.sum_eq_single s]
        · rw [if_pos ⟨by omega, hmid, rfl⟩]
        · intro l hl hls
          rw [if_neg]
          intro h
          exact hls (Fin.ext (by simpa [s] using h.2.2))
        · intro h
          simp at h
      rw [hsum]
      simp [vOuterRowAdded, htop, hmid, s]
    · have hzero :
          (∑ l : Fin (2 * m + k),
            (if m ≤ i.val ∧ i.val < 2 * m ∧ l.val = i.val - m then
              lambda * A l j else 0)) = 0 := by
        apply Finset.sum_eq_zero
        intro l hl
        rw [if_neg]
        omega
      rw [hzero, add_zero]
      simp [vOuterRowAdded, htop, hmid]

/-- Determinant invariance for all simultaneous corresponding row additions
(`v-analytic.tex:80-83`). -/
theorem vOuterRowAdded_det {m k : ℕ} (lambda : ℝ)
    (A : Matrix (Fin (2 * m + k)) (Fin (2 * m + k)) ℝ) :
    (vOuterRowAdded lambda A).det = A.det := by
  rw [← vOuterRowOperator_mul lambda A, Matrix.det_mul,
    vOuterRowOperator_det lambda, one_mul]

/-- The unreduced v13 determinant with middle rows `B(-q)-beta_q A(-q)`;
the top `C` and bottom fixed `V` rows are unchanged
(`v-arithmetic.tex:24-32`, `v-analytic.tex:78-83`). -/
noncomputable def vOuterSourceMatrix (q n : ℕ) :
    Matrix (Fin (2 * vM n + vS n)) (Fin (2 * vM n + vS n)) ℝ :=
  fun r c =>
    if r.val < vM n then
      (vCEntry (-(q : ℤ)) (2 * n + r.val) (n + c.val) : ℝ)
    else if r.val < 2 * vM n then
      let i := 2 * n + (r.val - vM n)
      (vBEntry (-(q : ℤ)) i (n + c.val) : ℝ) -
        vOuterBeta q * (vAEntry (-(q : ℤ)) i (n + c.val) : ℝ)
    else
      (vVEntry (n + c.val) (1 + (r.val - 2 * vM n)) : ℝ)

/-- The first v13 Andreief matrix has literal `M(q)` rows between the
unchanged `C(-q)` and fixed `V` blocks (`v-arithmetic.tex:24-32`,
`v-analytic.tex:50-55,71-83`). -/
noncomputable def vOuterMomentMatrix (q n : ℕ) :
    Matrix (Fin (2 * vM n + vS n)) (Fin (2 * vM n + vS n)) ℝ :=
  fun r c =>
    if r.val < vM n then
      (vCEntry (-(q : ℤ)) (2 * n + r.val) (n + c.val) : ℝ)
    else if r.val < 2 * vM n then
      vOuterMoment q (2 * n + (r.val - vM n)) (n + c.val)
    else
      (vVEntry (n + c.val) (1 + (r.val - 2 * vM n)) : ℝ)

/-- Under the entrywise moment identity, simultaneous v13 row addition
turns the polynomial-source matrix into the literal `M(q)` matrix
(`v-analytic.tex:71-83`). -/
theorem vOuterRowAdded_eq_momentMatrix (q n : ℕ) (hq : 2 ≤ q)
    (hM : vOuterMomentIdentity q hq) :
    vOuterRowAdded (m := vM n) (k := vS n) (vOuterLambda q)
      (vOuterSourceMatrix q n) = vOuterMomentMatrix q n := by
  classical
  ext r c
  by_cases htop : r.val < vM n
  · simp [vOuterRowAdded, vOuterSourceMatrix, vOuterMomentMatrix, htop]
  · by_cases hmid : r.val < 2 * vM n
    · have hlow : vM n ≤ r.val := by omega
      have hsource : r.val - vM n < vM n := by omega
      have hi : 2 * n + (r.val - vM n) < 2 * n + 4 * n := by
        have hm := vM_eq n
        omega
      simp only [vOuterRowAdded, vOuterSourceMatrix, vOuterMomentMatrix,
        dif_pos (And.intro hlow hmid), if_neg htop, if_pos hmid,
        if_pos hsource]
      rw [hM (2 * n + (r.val - vM n)) (n + c.val)]
      ring
    · have hlow : 2 * vM n ≤ r.val := by omega
      simp [vOuterRowAdded, htop, hmid, hlow,
        vOuterSourceMatrix, vOuterMomentMatrix]

/-- The literal `M(q)` determinant equals the v13 determinant after the
`B-beta A` to `M(q)` row addition (`v-analytic.tex:78-83`). -/
theorem vOuterMomentMatrix_det_eq_sourceMatrix_det (q n : ℕ) (hq : 2 ≤ q)
    (hM : vOuterMomentIdentity q hq) :
    (vOuterMomentMatrix q n).det = (vOuterSourceMatrix q n).det := by
  rw [← vOuterRowAdded_eq_momentMatrix q n hq hM]
  exact vOuterRowAdded_det (vOuterLambda q) (vOuterSourceMatrix q n)

/-- The actual signed Mellin entries close the v13 source/moment determinant
adapter without an assumed moment identity (`v-analytic.tex:71-83`). -/
theorem vOuterMomentMatrix_det_eq_sourceMatrix_det_of_signedMellin
    (q n : ℕ) (hq : 2 ≤ q) :
    (vOuterMomentMatrix q n).det = (vOuterSourceMatrix q n).det :=
  vOuterMomentMatrix_det_eq_sourceMatrix_det q n hq
    (vOuterMomentIdentity_of_signedMellin q hq)

/-- Frozen-base regression: the `q=2` row-addition statement is exactly the
same determinant identity specialized to the existing Li2(1/2) base
(`v-analytic.tex:78-83`). -/
theorem vOuterMomentMatrix_det_eq_sourceMatrix_det_q2 (n : ℕ)
    (hM : vOuterMomentIdentity 2 (by norm_num)) :
    (vOuterMomentMatrix 2 n).det = (vOuterSourceMatrix 2 n).det := by
  exact vOuterMomentMatrix_det_eq_sourceMatrix_det 2 n (by norm_num) hM

end

end Li2Lean.V

#print axioms Li2Lean.V.vOuterRowAdded_det
#print axioms Li2Lean.V.vOuterMomentIdentity_of_signedMellin
#print axioms Li2Lean.V.vOuterMomentMatrix_det_eq_sourceMatrix_det_of_signedMellin
