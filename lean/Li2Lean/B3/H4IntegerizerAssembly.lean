/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

H4 leaf L6: final producer for the actual rational integerizer, all bases
q = 2..7 at once.

This release module supplies the H4 assembly and is imported by the producer
boundary.

The L1--L5 dependencies listed in the imports below are the compiled release
modules: the outer-pole bound, slab table, H4 profile and integral, rate bridge,
six-class majorant, and verified regime data.

This file supplies the H4 assembly after the six-class prime-sum majorant.

Paper source: `v-arithmetic.tex:128-421`.
-/

import Li2Lean.B3.H4L5Regimes            -- L5 (merged master module)
import Li2Lean.B3.H4Profile             -- L2c (the H4 profile source); imports L4
import Li2Lean.B3.H4RateBudgetBridge    -- L3a
import Li2Lean.B3.H4PrimeSumMajorant    -- L3b combinator + `v13H4Err`
import Li2Lean.B3.H4PrimeSumMajorantProof -- completed L3b majorant
import Li2Lean.B3.ActualRationalIntegerizerProducer

namespace Li2Lean.B3

noncomputable section

open scoped BigOperators
open Filter Topology
open Li2Lean.P0.Integerization

/-! ## L3b analytic error: `v13H4Err → 0`

`v13H4Err n = (13 n log(11n) (sqrt(11n) + 417) + (4n+1) log 7) / (4n)^2`
`          = (13 sqrt 11 / 16) log(11n)/sqrt n + (13*417/16) log(11n)/n`
`            + (log 7 / 4) / n + (log 7 / 16) / n^2`.
Pattern: `P0/IntegerizationSmallPrimeTail.lean:615-662`. -/

private theorem h4_log_eleven_div_sqrt_tendsto_zero :
    Tendsto (fun x : ℝ => Real.log (11 * x) / Real.sqrt x) atTop (𝓝 0) := by
  have hlog : Tendsto (fun x : ℝ => Real.log x / Real.sqrt x) atTop (𝓝 0) := by
    simpa only [Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  have hinv : Tendsto (fun x : ℝ => (Real.sqrt x)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop
  have hsum : Tendsto (fun x : ℝ => Real.log 11 * (Real.sqrt x)⁻¹ +
      Real.log x / Real.sqrt x) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hinv).add hlog
  apply hsum.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [Real.log_mul (by norm_num) hx.ne', add_div]
  simp [div_eq_mul_inv]

private theorem h4_log_eleven_div_tendsto_zero :
    Tendsto (fun x : ℝ => Real.log (11 * x) / x) atTop (𝓝 0) := by
  have hlog := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hinv : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hsum : Tendsto (fun x : ℝ => Real.log 11 * x⁻¹ + Real.log x / x)
      atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hinv).add hlog
  apply hsum.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [Real.log_mul (by norm_num) hx.ne', add_div]
  simp [div_eq_mul_inv]

theorem v13H4Err_tendsto : Tendsto v13H4Err atTop (𝓝 0) := by
  have hinv : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hinv2 : Tendsto (fun x : ℝ => x⁻¹ * x⁻¹) atTop (𝓝 0) := by
    simpa using hinv.mul hinv
  have hreal : Tendsto (fun x : ℝ =>
      (13 * Real.sqrt 11 / 16) * (Real.log (11 * x) / Real.sqrt x) +
        (13 * 417 / 16) * (Real.log (11 * x) / x) +
        (Real.log 7 / 4) * x⁻¹ + (Real.log 7 / 16) * (x⁻¹ * x⁻¹)) atTop (𝓝 0) := by
    simpa using
      (((tendsto_const_nhds.mul h4_log_eleven_div_sqrt_tendsto_zero).add
        (tendsto_const_nhds.mul h4_log_eleven_div_tendsto_zero)).add
        (tendsto_const_nhds.mul hinv)).add (tendsto_const_nhds.mul hinv2)
  have hnat := hreal.comp tendsto_natCast_atTop_atTop
  apply hnat.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hx : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.2 hx).ne'
  simp only [Function.comp, v13H4Err]
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 11)]
  -- note: same normalisation as `p0SquarefullErrorBound_div_sq_tendsto_zero`
  -- (`field_simp; ring_nf; rw [Real.sq_sqrt]; ring`); the identity is
  -- 13 n L (sqrt 11 sqrt n + 417) + (4n+1) log 7 over 16 n^2.
  field_simp [hx.ne', hs]
  ring_nf
  rw [Real.sq_sqrt hx.le]
  ring

/-! ## L3b majorant (CLOSED LEAF)

Concrete class split of `Nat.primesLE (V.vU n)` for `n ≥ 1200`, first match
(`E := v13H4Exponent q`, `m := 4n`, `P := v13H4Profile`):

* B1 exceptional `p ∣ q (q+1)` (≤ 3 primes, all ≤ 7):
  `Σ E log p ≤ 3·13n·log(11n) − (53/3) n² log q + (4n+1) log 7`
  (`v13ExceptionalExponent`; `Σ_{p ∣ q} padicValNat p q · log p = log q`;
  `(53n²+2)/3 − 4n ≥ (53/3)n² − 4n` as reals; q+1 credit dropped, it is ≥ 0);
* B2 `p² ≤ vU n`: `E = v13BaselineExponent`, `Σ ≤ 13n·log(11n)·(sqrt(11n)+1)`;
* B3 `vU n < p²`, `10 p ≤ n`: `E = 13n`, `Σ ≤ 13n·θ(n/10)`;
* B4 `n < 10 p ≤ 50 n`, `(p:ℚ) = s.hi·4n` for some slab: `E = 13n`,
  `Σ ≤ 413·13n·log(11n)`  (`v13SlabData.length = 412`);
* B5 other `n < 10 p`, `p ≤ 5n`: inside a slab by `vSlabChain_cover`, residue
  regime holds (`p > n/10 ≥ 120 > sqrt(11n)`), `E = 4n·P(p/4n)` by
  `VSlab.residueExponent_eq` (exactly one piece is active, half-open walls);
* B6 `5n < p ≤ 11n−1`: `E = q5OuterCost n p = 4n·P(p/4n)`;
* B5 ∪ B6: `≤ 4n·weightedPrimeSum P (4n)` by `p0_partial_le_weightedPrimeSum`
  with `v13H4Profile_nonneg`, `H := 11/4`, `v13H4Profile_hi_le`.
Summing: exactly the right side below times `(4n)²` (with `(53/48)·16 = 53/3`).
Combinator in the release: `h4_prime_sum_majorant_normalized` /
`H4SixClassBounds` (`H4PrimeSumMajorant.lean`). -/
/-! ## Rate and producer -/

theorem v13H4_prime_sum_rate {q : ℕ} (hq : SignedVBaseRange q) :
    QV13PrimeSumRate V.vU (v13H4Exponent q) (vTau q) :=
  qv13PrimeSumRate_of_budget V.vU (v13H4Exponent q) (vTau q)
    ((53 / 48) * Real.log q) v13H4Profile v13H4Err v13H4Err_tendsto
    (v13H4_rate_hint hq) (v13H4_prime_sum_majorant hq)

/-- The actual rational integerizer for every base `q ∈ [2, 7]`, exactly as in
the H4 assembly skeleton, with the
named rate leaf replaced by `v13H4_prime_sum_rate`. -/
noncomputable def v13ActualRationalIntegerizerH4 {q : ℕ}
    (hq : SignedVBaseRange q) :
    VActualRationalIntegerizerProducer q (vTau q) where
  denominatorCutoff := V.vU
  primeExponent := v13H4Exponent q
  D := fun m =>
    rationalPrimeProduct (Nat.primesLE (V.vU (m / 4)))
      (v13H4Exponent q (m / 4))
  D_eq_primeProduct := by
    intro n
    simp [Nat.mul_div_cancel_left n (by norm_num : (0 : ℕ) < 4)]
  valuation_bound :=
    v13_valuation_bound_of_three_regimes hq
      v13H4ResidueRegime v13H4OuterRegime
      v13H4ResidueExponent v13H4OuterExponent
      (v13H4_regime_data hq)
  exponent_zero_of_gt_cutoff :=
    v13H4Exponent_zero_of_gt_cutoff hq
  prime_sum_rate := v13H4_prime_sum_rate hq

end
end Li2Lean.B3

#print axioms Li2Lean.B3.v13H4Err_tendsto
#print axioms Li2Lean.B3.v13H4_prime_sum_rate
#print axioms Li2Lean.B3.v13ActualRationalIntegerizerH4

/-
## Producer-boundary wiring

  import Li2Lean.B3.H4IntegerizerAssembly

  noncomputable def v13_actual_rational_integerizer_generic
      {q : ℕ} (hq : SignedVBaseRange q) :
      VActualRationalIntegerizerProducer q (vTau q) :=
    v13ActualRationalIntegerizerH4 hq

No import cycle: the H4 modules do not import `Li2Lean.B3.Producers`.

The per-q certificate route is superseded by this generic construction.
-/
