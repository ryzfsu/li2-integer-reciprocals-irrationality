/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.AllN.ProducerGate
import Li2Lean.AllN.Q11EndpointProfileProducer
import Li2Lean.P0.IntegerizationPlanRateBridge
import Li2Lean.AllN.HPProducerAdapters
import Li2Lean.AllN.HPContourProducerAdapters
import Li2Lean.B3.Producers
import Li2Lean.B3.ActualFrobeniusTowerCarriers
import Li2Lean.B4.NegativeContourProducer
import Li2Lean.B4.HPVpolyIntegrality
import Li2Lean.B4.HPDeltaIdentity
import Li2Lean.B4.HPBetaIdentity
import Li2Lean.B4.HPNoAdjV13Producer
import Li2Lean.B4.HPBetaQ8Adapter
import Li2Lean.B4.NegativeContourQ8BetaRate
import Li2Lean.B4.PositiveTailBetaRate
import Li2Lean.B4.P1EdgeParameterization
import Li2Lean.P0.PositiveBaseTau
import Li2Lean.AllN.P0RateMargin
import Li2Lean.AllN.P0TowerProducerProof
import Li2Lean.P0.IntegerizerObligationPlan
import Li2Lean.P0.IntegerizationS08ChainParam
import Li2Lean.P0.Pole.CoefficientSpecialization
import Li2Lean.P0.RateDetValuation

/-!
B4 wiring (the proof plan, 2026-10-14).  None of the imports above imports
`Li2Lean.AllN.Producers`; the only importers of this file are
`Li2Lean/AllN.lean`, `Solution.lean` and `Li2Lean/B4/HPBetaProducerWiring.lean`,
so the new imports introduce no cycle.  `HPBetaProducerWiring` is therefore
NOT imported here; its q = 9, 10 rate proofs are repeated below under new
names (`ProducersAux.*`) so that no public name collides with that file.
-/

/-! ## Auxiliary B4 tail lemmas used by the three B4 producers

Everything below is pinned to the v13 construction (`hpBRealAt`, `hpRR`,
`hpLR`).  Sources: v13 `hp-tail.tex:20-23` (residues), `:198-220` (beta
remainder), `:226-256` (tilted coefficient bound), `:411-476` (rate). -/

namespace Li2Lean.B4.TailAnalytic.ProducersAux

noncomputable section

open Filter Topology
open Li2Lean.B4.Residues

/-- The rational harmonic number `H_m` (`hp-tail.tex:19`) cast to `ℝ` is the
real harmonic number used by the positive-tail coefficient bounds. -/
theorem hpHarmonic_cast_real (m : ℕ) :
    ((hpHarmonic m : ℚ) : ℝ) = hpTailHarmonic m := by
  first
    | (simp [hpHarmonic, hpTailHarmonic]; done)
    | (unfold hpHarmonic hpTailHarmonic; push_cast; try rfl)

/-- The simple-pole residue `v_{n,j} = u_{n,j}(3H_{n-j}-2H_j-H_{3n+1-j})`
(`hp-tail.tex:20-22`) in the magnitude/harmonic-factor form of
`PositiveTailBinomialBound`. -/
theorem hpResidueV_cast_real (n j : ℕ) :
    ((hpResidueV n j : ℚ) : ℝ) =
      -(hpTailResidueMagnitude n j * hpTailHarmonicFactor n j) := by
  simp only [hpTailHarmonicFactor, ← hpHarmonic_cast_real]
  simp only [hpResidueV, hpResidueU, hpTailResidueMagnitude]
  push_cast
  ring

/-- `|a| = q` for `a = -q`, `q : ℕ` (same proof as
`NegativeTailContourDecay.lean:423-426`). -/
theorem hpAbsNegNatCast (q : ℕ) :
    |(((-(q : ℤ)) : ℤ) : ℝ)| = (q : ℝ) := by
  push_cast
  rw [abs_neg]
  exact abs_of_nonneg (by positivity)

/-- Saddle-tilted four-binomial bound for an arbitrary tilt `t`, base `q`
satisfying the v13 saddle inequality `(1-t)^3 ≤ q t^2 (3-t)`
(`hp-tail.tex:243-245`).  For `t = 13683/100000`, `q ≥ 12` this is
`hpTail_residue_tilted`; it is needed here for `q = 11`, `t = 14180/100000`
(the tilt of `hpNegativeQ11CoeffRate`). -/
theorem residue_tilted_of_certificate {q t : ℝ} (hq : 0 < q) (ht0 : 0 < t)
    (ht1 : t < 1) (hcert : (1 - t) ^ 3 ≤ q * t ^ 2 * (3 - t)) (j k : ℕ) :
    ((2 * j + 3 * k + 1 : ℕ) : ℝ) * hpTailBinomialProduct j k * q⁻¹ ^ j ≤
      ((2 * j + 3 * k + 1 : ℕ) : ℝ) * (((3 - t) / (1 - t)) ^ 3) ^ (j + k) := by
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (3 - t) / (1 - t) := ⟨_, rfl⟩
  rw [← hc]
  have hb : 0 < 1 - t := by linarith
  have hd : 0 < 3 - t := by linarith
  have hb' : 1 - t ≠ 0 := hb.ne'
  have hcm : c * (1 - t) = 3 - t := by
    rw [hc]
    first
      | exact div_mul_cancel₀ (3 - t) hb'
      | field_simp
  have hK1 : c ^ 3 * (1 - t) ^ 3 = (3 - t) ^ 3 := by
    rw [← hcm]
    ring
  have hK2 : (3 - t) ^ 2 ≤ c ^ 3 * q * t ^ 2 := by
    have e : (c ^ 3 * q * t ^ 2) * (1 - t) ^ 3 =
        (3 - t) ^ 2 * (q * t ^ 2 * (3 - t)) := by
      calc
        (c ^ 3 * q * t ^ 2) * (1 - t) ^ 3 =
            (c ^ 3 * (1 - t) ^ 3) * q * t ^ 2 := by ring
        _ = (3 - t) ^ 3 * q * t ^ 2 := by rw [hK1]
        _ = (3 - t) ^ 2 * (q * t ^ 2 * (3 - t)) := by ring
    have key : (3 - t) ^ 2 * (1 - t) ^ 3 ≤ (c ^ 3 * q * t ^ 2) * (1 - t) ^ 3 := by
      rw [e]
      exact mul_le_mul_of_nonneg_left hcert (sq_nonneg _)
    exact le_of_mul_le_mul_right key (pow_pos hb 3)
  -- weighted binomial bound (W) at a = t, b = 1 - t; `2t + 3(1-t) = 3 - t`
  have hW := hpTail_weighted_binomial_le ht0.le hb.le j k
  have h23 : 2 * t + 3 * (1 - t) = 3 - t := by ring
  rw [h23] at hW
  have hsplit : (3 - t) ^ (2 * j + 3 * k) = ((3 - t) ^ 2) ^ j * ((3 - t) ^ 3) ^ k := by
    first
      | ring1
      | rw [pow_add, pow_mul, pow_mul]
  have hA : ((3 - t) ^ 2) ^ j ≤ (c ^ 3 * q * t ^ 2) ^ j :=
    pow_le_pow_left₀ (sq_nonneg _) hK2 j
  have hBk : ((3 - t) ^ 3) ^ k = (c ^ 3 * (1 - t) ^ 3) ^ k := by
    rw [hK1]
  have hD : 0 < q ^ j * t ^ (2 * j) * (1 - t) ^ (3 * k) :=
    mul_pos (mul_pos (pow_pos hq j) (pow_pos ht0 _)) (pow_pos hb _)
  have hupper : (3 - t) ^ (2 * j + 3 * k) ≤
      (c ^ 3) ^ (j + k) * (q ^ j * t ^ (2 * j) * (1 - t) ^ (3 * k)) := by
    have hreshape : (c ^ 3) ^ (j + k) * (q ^ j * t ^ (2 * j) * (1 - t) ^ (3 * k)) =
        (c ^ 3 * q * t ^ 2) ^ j * (c ^ 3 * (1 - t) ^ 3) ^ k := by
      first
        | ring1
        | (simp only [mul_pow, pow_add, ← pow_mul]; ring1)
    rw [hreshape, hsplit, ← hBk]
    exact mul_le_mul_of_nonneg_right hA (pow_nonneg (pow_nonneg hd.le 3) k)
  have hbase : hpTailBinomialProduct j k * q⁻¹ ^ j ≤ (c ^ 3) ^ (j + k) := by
    have hqq : q⁻¹ ^ j * q ^ j = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ hq.ne', one_pow]
    have hlhs : (hpTailBinomialProduct j k * q⁻¹ ^ j) *
          (q ^ j * t ^ (2 * j) * (1 - t) ^ (3 * k)) =
        hpTailBinomialProduct j k * t ^ (2 * j) * (1 - t) ^ (3 * k) := by
      calc
        (hpTailBinomialProduct j k * q⁻¹ ^ j) *
              (q ^ j * t ^ (2 * j) * (1 - t) ^ (3 * k)) =
            hpTailBinomialProduct j k * t ^ (2 * j) * (1 - t) ^ (3 * k) *
              (q⁻¹ ^ j * q ^ j) := by ring
        _ = hpTailBinomialProduct j k * t ^ (2 * j) * (1 - t) ^ (3 * k) := by
          rw [hqq, mul_one]
    have hmul : (hpTailBinomialProduct j k * q⁻¹ ^ j) *
          (q ^ j * t ^ (2 * j) * (1 - t) ^ (3 * k)) ≤
        (c ^ 3) ^ (j + k) * (q ^ j * t ^ (2 * j) * (1 - t) ^ (3 * k)) := by
      rw [hlhs]
      exact hW.trans hupper
    exact le_of_mul_le_mul_right hmul hD
  have hN : (0 : ℝ) ≤ ((2 * j + 3 * k + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  calc
    ((2 * j + 3 * k + 1 : ℕ) : ℝ) * hpTailBinomialProduct j k * q⁻¹ ^ j =
        ((2 * j + 3 * k + 1 : ℕ) : ℝ) * (hpTailBinomialProduct j k * q⁻¹ ^ j) := by
      ring
    _ ≤ ((2 * j + 3 * k + 1 : ℕ) : ℝ) * (c ^ 3) ^ (j + k) :=
      mul_le_mul_of_nonneg_left hbase hN

/-- Residue magnitude times `q^{-j}` from a tilted bound, as in the inner
step of `hpTail_C_bound` (`PositiveTailBinomialBound.lean:334-365`). -/
theorem residueMagnitude_mul_inv_pow_le {q K : ℝ} (hK : 0 ≤ K)
    (htilt : ∀ j k : ℕ,
      ((2 * j + 3 * k + 1 : ℕ) : ℝ) * hpTailBinomialProduct j k * q⁻¹ ^ j ≤
        ((2 * j + 3 * k + 1 : ℕ) : ℝ) * K ^ (j + k))
    {m j : ℕ} (hj : j ≤ m) :
    hpTailResidueMagnitude m j * q⁻¹ ^ j ≤ ((3 * m + 1 : ℕ) : ℝ) * K ^ m := by
  obtain ⟨k, rfl⟩ : ∃ k, m = j + k := ⟨m - j, by omega⟩
  rw [hpTail_residue_factor_real j k]
  have hcoef : ((2 * j + 3 * k + 1 : ℕ) : ℝ) ≤ ((3 * (j + k) + 1 : ℕ) : ℝ) :=
    Nat.cast_le.mpr (by omega)
  calc
    ((2 * j + 3 * k + 1 : ℕ) : ℝ) * hpTailBinomialProduct j k * q⁻¹ ^ j ≤
        ((2 * j + 3 * k + 1 : ℕ) : ℝ) * K ^ (j + k) := htilt j k
    _ ≤ ((3 * (j + k) + 1 : ℕ) : ℝ) * K ^ (j + k) :=
      mul_le_mul_of_nonneg_right hcoef (pow_nonneg hK _)

/-- Coefficient bound for the actual `B_n(1/a)` (plan C4): with `|a| = q`
and a tilted residue bound at rate `K`,
`|B_m(1/a)| ≤ (m+1)(3m+1)(8m+1) K^m ≤ 24 (m+1)^3 K^m`.
This is the bridge `hpBRealAt a m` ↔ `hpTailB m a` recorded as missing in
the release note (2026-10-14 17:25), proved here directly from `hpBRealAt_eq_sum`. -/
theorem hpBRealAt_abs_le_of_tilt {a : ℤ} {q K : ℝ} (hq : 0 < q)
    (haq : |(a : ℝ)| = q) (hK : 0 ≤ K)
    (htilt : ∀ j k : ℕ,
      ((2 * j + 3 * k + 1 : ℕ) : ℝ) * hpTailBinomialProduct j k * q⁻¹ ^ j ≤
        ((2 * j + 3 * k + 1 : ℕ) : ℝ) * K ^ (j + k))
    (m : ℕ) :
    |hpBRealAt a m| ≤ 24 * ((m + 1 : ℕ) : ℝ) ^ 3 * K ^ m := by
  rw [hpBRealAt_eq_sum]
  have hterm : ∀ j ∈ Finset.range (m + 1),
      |(hpResidueV m j : ℝ) * (a : ℝ)⁻¹ ^ j| ≤
        ((8 * m + 1 : ℕ) : ℝ) * (((3 * m + 1 : ℕ) : ℝ) * K ^ m) := by
    intro j hj
    have hjm : j ≤ m := by
      have := Finset.mem_range.mp hj
      omega
    have hmag0 : 0 ≤ hpTailResidueMagnitude m j :=
      (hpTailResidueMagnitude_pos m j).le
    have hpow0 : 0 ≤ q⁻¹ ^ j := pow_nonneg (inv_nonneg.mpr hq.le) j
    have hfac := hpTail_harmonicFactor_abs_le m j hjm
    have hmag := residueMagnitude_mul_inv_pow_le hK htilt hjm
    have h8 : (0 : ℝ) ≤ ((8 * m + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    rw [hpResidueV_cast_real, abs_mul, abs_neg, abs_mul, abs_pow, abs_inv, haq,
      abs_of_nonneg hmag0]
    calc
      hpTailResidueMagnitude m j * |hpTailHarmonicFactor m j| * q⁻¹ ^ j ≤
          hpTailResidueMagnitude m j * ((8 * m + 1 : ℕ) : ℝ) * q⁻¹ ^ j :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfac hmag0) hpow0
      _ = ((8 * m + 1 : ℕ) : ℝ) * (hpTailResidueMagnitude m j * q⁻¹ ^ j) := by
        ring
      _ ≤ ((8 * m + 1 : ℕ) : ℝ) * (((3 * m + 1 : ℕ) : ℝ) * K ^ m) :=
        mul_le_mul_of_nonneg_left hmag h8
  have hpoly : ((m + 1 : ℕ) : ℝ) * ((8 * m + 1 : ℕ) : ℝ) * ((3 * m + 1 : ℕ) : ℝ) ≤
      24 * ((m + 1 : ℕ) : ℝ) ^ 3 := by
    push_cast
    have h0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    nlinarith [h0, mul_nonneg h0 h0]
  have hKm : 0 ≤ K ^ m := pow_nonneg hK m
  calc
    |∑ j ∈ Finset.range (m + 1), (hpResidueV m j : ℝ) * (a : ℝ)⁻¹ ^ j| ≤
        ∑ j ∈ Finset.range (m + 1), |(hpResidueV m j : ℝ) * (a : ℝ)⁻¹ ^ j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.range (m + 1),
          ((8 * m + 1 : ℕ) : ℝ) * (((3 * m + 1 : ℕ) : ℝ) * K ^ m) :=
      Finset.sum_le_sum hterm
    _ = ((m + 1 : ℕ) : ℝ) *
          (((8 * m + 1 : ℕ) : ℝ) * (((3 * m + 1 : ℕ) : ℝ) * K ^ m)) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ = (((m + 1 : ℕ) : ℝ) * ((8 * m + 1 : ℕ) : ℝ) * ((3 * m + 1 : ℕ) : ℝ)) *
          K ^ m := by ring
    _ ≤ (24 * ((m + 1 : ℕ) : ℝ) ^ 3) * K ^ m :=
      mul_le_mul_of_nonneg_right hpoly hKm
    _ = 24 * ((m + 1 : ℕ) : ℝ) ^ 3 * K ^ m := by ring

/-! ### Positive tail, `a ≥ 12` -/

/-- `HPDecay a` for `a ≥ 12` from the refined positive beta certificate
(`hpPositiveRefinedM = 154/1000`, rate 0.99241 at `q = 12`). -/
theorem hpDecayPos_of_refined_beta {a : ℤ} (ha : (12 : ℤ) ≤ a)
    (I : HPNoAdjacentV13Input a) :
    Li2Lean.AllNAssembly.HPDecay a := by
  have haR : (12 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hapos : (0 : ℝ) < (a : ℝ) := by linarith
  have hB : ∀ m : ℕ, |hpBRealAt a m| ≤
      24 * ((m + 1 : ℕ) : ℝ) ^ 3 * hpTailTiltK ^ m :=
    hpBRealAt_abs_le_of_tilt hapos (abs_of_pos hapos) hpTailTiltK_nonneg
      (fun j k => hpTail_residue_tilted (a : ℝ) haR j k)
  have hbr : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ u ∈ Set.Icc (0 : ℝ) 1,
      t ^ 2 * u ^ 2 * (1 - t) * (1 - u) / (1 - (a : ℝ)⁻¹ * t * u) ^ 2 ≤
        hpPositiveBetaM := by
    intro t ht u hu
    have h := hp_positive_bracket_le_refined haR ht hu
    unfold hpPositiveBetaBracket at h
    calc
      t ^ 2 * u ^ 2 * (1 - t) * (1 - u) / (1 - (a : ℝ)⁻¹ * t * u) ^ 2 =
          t ^ 2 * u ^ 2 * ((1 - t) * (1 - u)) / (1 - (a : ℝ)⁻¹ * t * u) ^ 2 := by
        ring
      _ ≤ hpPositiveRefinedM ^ 2 := h
      _ = hpPositiveBetaM := rfl
  exact hpDecayPos_of_beta_producer ha I (CB := 24) (k := 3) (by norm_num) hB
    (fun n => hpRR_abs_le_pos ha hpPositiveBetaM_nonneg hbr n)

/-! ### Negative tail, `a ≤ -11` -/

/-- Generic negative-base decay from a tilted coefficient bound and a beta
remainder bound; the same estimate chain as
`hpLR_tendsto_zero_of_contour_beta_bounds`, with the coefficient bound
supplied by `hpBRealAt_abs_le_of_tilt` instead of a contour certificate. -/
theorem hpDecayNeg_of_tilt {q : ℕ} (hq : 0 < q)
    (I : HPNoAdjacentV13Input (-(q : ℤ))) {K M2 : ℝ} (hK : 0 ≤ K) (hM2 : 0 ≤ M2)
    (hB : ∀ m : ℕ, |hpBRealAt (-(q : ℤ)) m| ≤
      24 * ((m + 1 : ℕ) : ℝ) ^ 3 * K ^ m)
    (hR : ∀ n : ℕ, |hpRR n ((-(q : ℤ) : ℝ)⁻¹)| ≤
      (2 * n + 1 : ℝ) * 4 ^ n * (q : ℝ)⁻¹ ^ (3 * n + 2) * M2 ^ n)
    (hρ : hpContourGamma * K * (4 * M2) * (q : ℝ)⁻¹ < 1) :
    Li2Lean.AllNAssembly.HPDecay (-(q : ℤ)) := by
  apply HPDecay_of_hpLR_tendsto_zero
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hD : ∀ᶠ n : ℕ in atTop,
      0 ≤ hpDR n ∧ hpDR n ≤ Real.exp (2 * (1 + 1 / 1000 : ℝ)) *
        (2 * n + 1 : ℝ) ^ 2 * hpContourGamma ^ n := by
    filter_upwards [hpContourDR_upper] with n hn
    refine ⟨?_, hn⟩
    unfold hpDR
    positivity
  have hL : ∀ n : ℕ, |hpLR (-(q : ℤ)) n| ≤
      (q : ℝ) ^ (2 * n + 1) * hpDR n *
        (|hpBRealAt (-(q : ℤ)) (n + 1)| *
            |hpRR n ((((-(q : ℤ)) : ℤ) : ℝ)⁻¹)| +
          |hpBRealAt (-(q : ℤ)) n| *
            |hpRR (n + 1) ((((-(q : ℤ)) : ℤ) : ℝ)⁻¹)|) := by
    intro n
    have h := hpLR_abs_le_of_v13_input I n
    rw [hpAbsNegNatCast q] at h
    exact h
  have hR' : ∀ m : ℕ, |hpRR m ((((-(q : ℤ)) : ℤ) : ℝ)⁻¹)| ≤
      (2 * m + 1 : ℝ) * 4 ^ m * (q : ℝ)⁻¹ ^ (3 * m + 2) * (1 * M2 ^ m) := by
    intro m
    rw [one_mul]
    simpa only [Int.cast_neg] using hR m
  exact hpLR_tendsto_zero_of_tail_bounds (q := (q : ℝ)) (K := K) (M2 := M2)
    (Cz := 1) (CB := 24) (e2 := Real.exp (2 * (1 + 1 / 1000 : ℝ))) (k := 3)
    (Bf := fun m => hpBRealAt (-(q : ℤ)) m)
    (Rf := fun m => hpRR m ((((-(q : ℤ)) : ℤ) : ℝ)⁻¹))
    (D := hpDR) (L := hpLR (-(q : ℤ)))
    hqR hK hM2 (by norm_num) (by norm_num) (Real.exp_pos _).le
    hB hR' hD hL hρ

/-- `a ≤ -12`: tilt `hpTailTiltK` (valid for every real `q ≥ 12`), uniform
`(4/27)^2` beta bracket, enlarged to `hpPositiveBetaM = (154/1000)^2` so that
the already-certified rate `hp_positive_beta_rate_lt_one` applies
(value 0.99241 at `q = 12`). -/
theorem hpDecayNeg_ge_twelve {q : ℕ} (hq : 12 ≤ q)
    (I : HPNoAdjacentV13Input (-(q : ℤ))) :
    Li2Lean.AllNAssembly.HPDecay (-(q : ℤ)) := by
  have hqR : (12 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < (q : ℝ) := by linarith
  have hB := hpBRealAt_abs_le_of_tilt (a := -(q : ℤ)) hqpos (hpAbsNegNatCast q)
    hpTailTiltK_nonneg (fun j k => hpTail_residue_tilted (q : ℝ) hqR j k)
  have hM : (4 / 27 : ℝ) ^ 2 ≤ hpPositiveBetaM := by
    norm_num [hpPositiveBetaM, hpPositiveRefinedM]
  have hR : ∀ n : ℕ, |hpRR n ((-(q : ℤ) : ℝ)⁻¹)| ≤
      (2 * n + 1 : ℝ) * 4 ^ n * (q : ℝ)⁻¹ ^ (3 * n + 2) * hpPositiveBetaM ^ n := by
    intro n
    have h := hpRR_abs_le_neg_four27 (q := q) (by omega) n
    have hpow : ((4 / 27 : ℝ) ^ 2) ^ n ≤ hpPositiveBetaM ^ n :=
      pow_le_pow_left₀ (by positivity) hM n
    have hpre : 0 ≤ (2 * n + 1 : ℝ) * 4 ^ n * (q : ℝ)⁻¹ ^ (3 * n + 2) := by
      positivity
    exact h.trans (mul_le_mul_of_nonneg_left hpow hpre)
  exact hpDecayNeg_of_tilt (q := q) (by omega) I (K := hpTailTiltK)
    (M2 := hpPositiveBetaM) hpTailTiltK_nonneg hpPositiveBetaM_nonneg hB hR
    (hp_positive_beta_rate_lt_one hqR)

/-- The `a = -11` rate with the tilt `t = 14180/100000`
(`hpNegativeQ11CoeffRate`) and the sharpened bracket `hpNegativeQ11M`:
value 0.93789 with the repo bound `exp(4.004) ≤ e_10^4 * 1.008`. -/
theorem rate_eleven_lt_one :
    hpContourGamma * ((3 - (14180 / 100000 : ℝ)) / (1 - (14180 / 100000 : ℝ))) ^ 3 *
      (4 * hpNegativeQ11M ^ 2) * ((11 : ℕ) : ℝ)⁻¹ < 1 := by
  have hgamma := hpContour_exp_4004_le
  unfold hpContourGamma
  have hnonneg : 0 ≤
      ((3 - (14180 / 100000 : ℝ)) / (1 - (14180 / 100000 : ℝ))) ^ 3 *
        (4 * hpNegativeQ11M ^ 2) * ((11 : ℕ) : ℝ)⁻¹ / 16 := by
    norm_num [hpNegativeQ11M]
  have hmul := mul_le_mul_of_nonneg_right hgamma hnonneg
  calc
    Real.exp (4 * (1 + 1 / 1000 : ℝ)) / 16 *
          ((3 - (14180 / 100000 : ℝ)) / (1 - (14180 / 100000 : ℝ))) ^ 3 *
          (4 * hpNegativeQ11M ^ 2) * ((11 : ℕ) : ℝ)⁻¹ =
        Real.exp (4 * (1 + 1 / 1000 : ℝ)) *
          (((3 - (14180 / 100000 : ℝ)) / (1 - (14180 / 100000 : ℝ))) ^ 3 *
            (4 * hpNegativeQ11M ^ 2) * ((11 : ℕ) : ℝ)⁻¹ / 16) := by ring
    _ ≤ ((27182818286 / 10 ^ 10 : ℝ) ^ 4 * (1008 / 1000)) *
          (((3 - (14180 / 100000 : ℝ)) / (1 - (14180 / 100000 : ℝ))) ^ 3 *
            (4 * hpNegativeQ11M ^ 2) * ((11 : ℕ) : ℝ)⁻¹ / 16) := hmul
    _ < 1 := by norm_num [hpNegativeQ11M]

/-- `a = -11`. -/
theorem hpDecayNeg_eleven (I : HPNoAdjacentV13Input (-((11 : ℕ) : ℤ))) :
    Li2Lean.AllNAssembly.HPDecay (-((11 : ℕ) : ℤ)) := by
  have hqpos : (0 : ℝ) < ((11 : ℕ) : ℝ) := by norm_num
  have hK : (0 : ℝ) ≤
      ((3 - (14180 / 100000 : ℝ)) / (1 - (14180 / 100000 : ℝ))) ^ 3 := by
    norm_num
  have hB := hpBRealAt_abs_le_of_tilt (a := -((11 : ℕ) : ℤ)) hqpos
    (hpAbsNegNatCast 11) hK
    (fun j k => residue_tilted_of_certificate (q := ((11 : ℕ) : ℝ))
      (t := 14180 / 100000) hqpos (by norm_num) (by norm_num) (by norm_num) j k)
  exact hpDecayNeg_of_tilt (q := 11) (by norm_num) I
    (K := ((3 - (14180 / 100000 : ℝ)) / (1 - (14180 / 100000 : ℝ))) ^ 3)
    (M2 := hpNegativeQ11M ^ 2) hK (by positivity) hB hpRR_abs_le_q11
    rate_eleven_lt_one

/-- Every `a ≤ -11` (v13 `hp-tail.tex:449-476`, split `a = -11` / `a ≤ -12`
exactly as `hpNegativeBaseRate_cases`). -/
theorem hpDecayNeg_le_eleven {a : ℤ} (ha : a ≤ -11)
    (I : HPNoAdjacentV13Input a) :
    Li2Lean.AllNAssembly.HPDecay a := by
  have h0 : (0 : ℤ) ≤ -a := by omega
  obtain ⟨q, rfl⟩ : ∃ q : ℕ, a = -(q : ℤ) :=
    ⟨(-a).toNat, by rw [Int.toNat_of_nonneg h0]; omega⟩
  by_cases h11 : q = 11
  · subst h11
    exact hpDecayNeg_eleven I
  · exact hpDecayNeg_ge_twelve (by omega) I

/-! ### Exceptional bases `q = 8, 9, 10` (contour certificate + beta)

Same proofs as `Li2Lean/B4/HPBetaProducerWiring.lean:17-90` (which imports
this file and so cannot be imported here), under new names. -/

theorem hpDecayNeg_q8_of_certificate
    (cert : Nonempty (Li2Lean.B4.NegativeContour.NegContourRectangleCertificate
      Li2Lean.B4.NegativeContour.hpBSequence 8))
    (I : HPNoAdjacentV13Input (-8 : ℤ)) :
    Li2Lean.AllNAssembly.HPDecay (-8 : ℤ) :=
  hpDecayNeg_q8_of_beta_producer cert I hpRR_q8_beta_bound

theorem q9_contour_beta_rate_lt_one :
    hpContourGamma * 29 * (4 * ((4 / 27 : ℝ) ^ 2)) * (9 : ℝ)⁻¹ < 1 := by
  have hgamma := hpContour_exp_4004_le
  unfold hpContourGamma at hgamma ⊢
  calc
    Real.exp (4 * (1 + 1 / 1000 : ℝ)) / 16 * 29 *
          (4 * ((4 / 27 : ℝ) ^ 2)) * (9 : ℝ)⁻¹ ≤
        ((27182818286 / 10 ^ 10 : ℝ) ^ 4 * (1008 / 1000)) / 16 *
          29 * (4 * ((4 / 27 : ℝ) ^ 2)) * (9 : ℝ)⁻¹ := by
      have hnonneg :
          0 ≤ 29 * (4 * ((4 / 27 : ℝ) ^ 2)) * (9 : ℝ)⁻¹ / 16 := by
        norm_num
      have hmul := mul_le_mul_of_nonneg_right hgamma hnonneg
      calc
        Real.exp (4 * (1 + 1 / 1000 : ℝ)) / 16 * 29 *
              (4 * ((4 / 27 : ℝ) ^ 2)) * (9 : ℝ)⁻¹ =
            Real.exp (4 * (1 + 1 / 1000 : ℝ)) *
              (29 * (4 * ((4 / 27 : ℝ) ^ 2)) * (9 : ℝ)⁻¹ / 16) := by ring
        _ ≤ ((27182818286 / 10 ^ 10 : ℝ) ^ 4 * (1008 / 1000)) *
              (29 * (4 * ((4 / 27 : ℝ) ^ 2)) * (9 : ℝ)⁻¹ / 16) := hmul
        _ = ((27182818286 / 10 ^ 10 : ℝ) ^ 4 * (1008 / 1000)) / 16 *
              29 * (4 * ((4 / 27 : ℝ) ^ 2)) * (9 : ℝ)⁻¹ := by ring
    _ < 1 := by norm_num

theorem q10_contour_beta_rate_lt_one :
    hpContourGamma * 29 * (4 * ((4 / 27 : ℝ) ^ 2)) * (10 : ℝ)⁻¹ < 1 := by
  have hgamma := hpContour_exp_4004_le
  unfold hpContourGamma at hgamma ⊢
  calc
    Real.exp (4 * (1 + 1 / 1000 : ℝ)) / 16 * 29 *
          (4 * ((4 / 27 : ℝ) ^ 2)) * (10 : ℝ)⁻¹ ≤
        ((27182818286 / 10 ^ 10 : ℝ) ^ 4 * (1008 / 1000)) / 16 *
          29 * (4 * ((4 / 27 : ℝ) ^ 2)) * (10 : ℝ)⁻¹ := by
      have hnonneg :
          0 ≤ 29 * (4 * ((4 / 27 : ℝ) ^ 2)) * (10 : ℝ)⁻¹ / 16 := by
        norm_num
      have hmul := mul_le_mul_of_nonneg_right hgamma hnonneg
      calc
        Real.exp (4 * (1 + 1 / 1000 : ℝ)) / 16 * 29 *
              (4 * ((4 / 27 : ℝ) ^ 2)) * (10 : ℝ)⁻¹ =
            Real.exp (4 * (1 + 1 / 1000 : ℝ)) *
              (29 * (4 * ((4 / 27 : ℝ) ^ 2)) * (10 : ℝ)⁻¹ / 16) := by ring
        _ ≤ ((27182818286 / 10 ^ 10 : ℝ) ^ 4 * (1008 / 1000)) *
              (29 * (4 * ((4 / 27 : ℝ) ^ 2)) * (10 : ℝ)⁻¹ / 16) := hmul
        _ = ((27182818286 / 10 ^ 10 : ℝ) ^ 4 * (1008 / 1000)) / 16 *
              29 * (4 * ((4 / 27 : ℝ) ^ 2)) * (10 : ℝ)⁻¹ := by ring
    _ < 1 := by norm_num

theorem hpDecayNeg_q9_of_certificate
    (cert : Nonempty (Li2Lean.B4.NegativeContour.NegContourRectangleCertificate
      Li2Lean.B4.NegativeContour.hpBSequence 9))
    (I : HPNoAdjacentV13Input (-9 : ℤ)) :
    Li2Lean.AllNAssembly.HPDecay (-9 : ℤ) := by
  refine hpDecayNeg_exceptional_of_contour_beta_bound
    (q := 9) (by norm_num) cert I
    (M2 := (4 / 27 : ℝ) ^ 2) (by positivity) ?_ q9_contour_beta_rate_lt_one
  intro n
  simpa using (hpRR_abs_le_neg_four27 (q := 9) (by norm_num) n)

theorem hpDecayNeg_q10_of_certificate
    (cert : Nonempty (Li2Lean.B4.NegativeContour.NegContourRectangleCertificate
      Li2Lean.B4.NegativeContour.hpBSequence 10))
    (I : HPNoAdjacentV13Input (-10 : ℤ)) :
    Li2Lean.AllNAssembly.HPDecay (-10 : ℤ) := by
  refine hpDecayNeg_exceptional_of_contour_beta_bound
    (q := 10) (by norm_num) cert I
    (M2 := (4 / 27 : ℝ) ^ 2) (by positivity) ?_ q10_contour_beta_rate_lt_one
  intro n
  simpa using (hpRR_abs_le_neg_four27 (q := 10) (by norm_num) n)

end

end Li2Lean.B4.TailAnalytic.ProducersAux

namespace Li2Lean.AllNAssembly

noncomputable section

open Li2Lean.P0.PositiveBase

/-!
The declarations below are the B0 producer inputs.  They are named
separately so each analytic or arithmetic route can replace one obligation
without changing the consumer.  No declaration below states an
irrationality conclusion or stores a free certificate.  The B3/B4 wiring
supplies each producer input as a closed proof term.
-/

noncomputable def p0Rate_producer (q : ℕ) : ℝ :=
  p0RateRelaxed q

/-- The rate field of the actual generic integerizer witness is proved
from the finite moving-profile majorant and signed exceptional-prime credit.
No coefficient or completed-producer hypothesis is needed here. -/
theorem p0Integerizer_plan_generic_rate (q : ℕ) (hq3 : 3 ≤ q) :
    ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, ∀ m : ℕ, M ≤ m → 0 < m → 4 ∣ m →
      (∑ p ∈ Nat.primesLE (Li2Lean.P0.p0IntegerizerCutoff q m),
        (Li2Lean.P0.p0IntegerizerExponent q m p : ℝ) * Real.log p) /
          (m : ℝ)^2 ≤ p0Rate_producer q + ε := by
  simpa only [p0Rate_producer, p0RateRelaxed] using
    Li2Lean.P0.p0IntegerizerExponent_rate q hq3

/-! The q-generic integerizer plan uses the actual denominator and exponent
witnesses. Its exceptional-pole, formal-base, q-adic, moving-prime, degree,
and rate fields are discharged below from the construction-specific bounds.  The finite q cases below are only instantiations of this
one theorem; they do not duplicate the proof. -/
theorem p0Integerizer_plan_generic (q : ℕ) (h3 : 3 ≤ q) (h11 : q ≤ 11) :
    Li2Lean.P0.P0IntegerizerProofPlan q (p0Rate_producer q) := by
  classical
  refine ⟨Li2Lean.P0.p0IntegerizerCutoff q,
    Li2Lean.P0.p0IntegerizerMovingExponent q,
    Li2Lean.P0.p0IntegerizerExponent q,
    Li2Lean.P0.p0IntegerizerDenominator q, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m hm h4
    simp only [Li2Lean.P0.p0IntegerizerCutoff]
    omega
  · intro m p
    rfl
  · intro m p hm h4 hcut
    have hU : Li2Lean.P0.formalDivisorCutoff m < p := by
      dsimp [Li2Lean.P0.p0IntegerizerCutoff] at hcut
      omega
    have hq : q < p := by
      dsimp [Li2Lean.P0.p0IntegerizerCutoff] at hcut
      omega
    have hpq : ¬ p ∣ q := by
      intro hd
      have hp_le : p ≤ q := Nat.le_of_dvd (by omega) hd
      omega
    have hpq1 : ¬ p ∣ q - 1 := by
      intro hd
      have hp_le : p ≤ q - 1 := Nat.le_of_dvd (by omega) hd
      omega
    have hvq : padicValNat p q = 0 :=
      padicValNat.eq_zero_of_not_dvd hpq
    have hvq1 : padicValNat p (q - 1) = 0 :=
      padicValNat.eq_zero_of_not_dvd hpq1
    have hlog : Nat.log p (Li2Lean.P0.formalDivisorCutoff m) = 0 :=
      Nat.log_of_lt hU
    have hcredit : Li2Lean.P0.formalDivisorCredit q m p = 0 := by
      simp [Li2Lean.P0.formalDivisorCredit, hlog, hvq, hvq1]
    have hmoving : Li2Lean.P0.p0IntegerizerMovingExponent q m p = 0 := by
      unfold Li2Lean.P0.p0IntegerizerMovingExponent
      by_cases hex : p ∣ q * (q - 1)
      · simp [hex, hcredit]
      · have hnotU : ¬ p ≤ Li2Lean.P0.formalDivisorCutoff m := Nat.not_le.mpr hU
        simp [hex, hnotU]
    simp [Li2Lean.P0.p0IntegerizerExponent, hcredit, hmoving]
  · intro m hm h4
    rfl
  · intro m p i hm h4 hp hprod
    by_cases hpq : p ∣ q
    · exact Li2Lean.P0.Integerization.S08.canonical_qadic_coeff q m p i
        (by omega) hm h4 hp hpq
    · have hpq1 : p ∣ q - 1 :=
        Li2Lean.P0.p0Prime_dvd_qSubOne_of_dvd_product hp hpq hprod
      exact Li2Lean.P0.Integerization.S08.canonical_formal_coeff_of_qSubOne_dvd
        q m p i (by omega) hm h4 hp hpq1 hpq
  · intro m p i hm h4 hp hfree
    exact Li2Lean.P0.Integerization.S08.canonical_formal_base_coeff
      q m p i (by omega) hm h4 hp hfree
  · intro m p i hm h4 hp hpq
    have hprod : p ∣ q * (q - 1) := dvd_mul_of_dvd_left hpq _
    have h := Li2Lean.P0.Integerization.S08.canonical_qadic_coeff q m p i
      (by omega) hm h4 hp hpq
    have hmoving : Li2Lean.P0.p0IntegerizerMovingExponent q m p =
        Li2Lean.P0.formalDivisorCredit q m p := by
      simp [Li2Lean.P0.p0IntegerizerMovingExponent, hprod]
    change (p0CanonicalPolynomial (q : ℤ) m).coeff i = 0 ∨
      -(Li2Lean.P0.p0IntegerizerMovingExponent q m p) ≤
        padicValRat p ((p0CanonicalPolynomial (q : ℤ) m).coeff i)
    rw [hmoving]
    simpa [Li2Lean.P0.p0FormalDivisorCoeff] using h
  · intro m p i hm h4 hp hpq
    unfold Li2Lean.P0.p0MovingPrimeCoeff Li2Lean.P0.p0MovingCoeff
    by_cases hpq1 : p ∣ q - 1
    · have hprod : p ∣ q * (q - 1) := dvd_mul_of_dvd_right hpq1 _
      have h := Li2Lean.P0.Integerization.S08.canonical_formal_coeff_of_qSubOne_dvd
        q m p i (by omega) hm h4 hp hpq1 hpq
      simpa [Li2Lean.P0.p0IntegerizerMovingExponent,
        Li2Lean.P0.p0FormalDivisorCoeff, hprod] using h
    · have hfree : ¬ p ∣ q * (q - 1) := by
        intro hd
        exact (hp.dvd_mul.mp hd).elim hpq hpq1
      have hbase := Li2Lean.P0.Integerization.S08.canonical_formal_base_coeff
        q m p i (by omega) hm h4 hp hfree
      have hcutU : Li2Lean.P0.formalDivisorCutoff m =
          Li2Lean.P0.Integerization.p0DenominatorU m := rfl
      have hcredit : Li2Lean.P0.formalDivisorCredit q m p =
          (((3 * m * Nat.log p (Li2Lean.P0.Integerization.p0DenominatorU m) : ℕ) : ℤ)) := by
        rw [Li2Lean.P0.formalDivisorCredit_of_not_dvd_q q m p hpq]
        rw [hcutU]
        simp [padicValNat.eq_zero_of_not_dvd hpq1]
      have hbase' :
          (p0CanonicalPolynomial (q : ℤ) m).coeff i = 0 ∨
            -(((3 * m * Nat.log p (Li2Lean.P0.Integerization.p0DenominatorU m) : ℕ) : ℤ)) ≤
              padicValRat p ((p0CanonicalPolynomial (q : ℤ) m).coeff i) := by
        change (p0CanonicalPolynomial (q : ℤ) m).coeff i = 0 ∨
          -Li2Lean.P0.formalDivisorCredit q m p ≤
            padicValRat p ((p0CanonicalPolynomial (q : ℤ) m).coeff i) at hbase
        rw [hcredit] at hbase
        exact hbase
      by_cases hlarge : Li2Lean.P0.Integerization.p0SquarefullCutoff m < p ^ 2
      · have hlarge' : 2 * m - 1 + m / 2 < p ^ 2 := by
          simpa [Li2Lean.P0.Integerization.p0SquarefullCutoff,
            Li2Lean.P0.Integerization.p0DenominatorU] using hlarge
        have hval := Li2Lean.P0.Integerization.p0Rate_canonical_coeff_val_base
          q p m hp hfree (by omega) h4 hlarge' i
        by_cases hpU : p ≤ Li2Lean.P0.formalDivisorCutoff m
        · have hpU' : p ≤ Li2Lean.P0.Integerization.p0DenominatorU m := by
            simpa [hcutU] using hpU
          by_cases hc : Li2Lean.P0.Integerization.p0RateAssignMax p m ≤
              (((3 * m * Nat.log p (Li2Lean.P0.Integerization.p0DenominatorU m) : ℕ) : ℤ))
          · have hmexp : Li2Lean.P0.p0IntegerizerMovingExponent q m p =
                Li2Lean.P0.Integerization.p0RateAssignMax p m := by
              simp [Li2Lean.P0.p0IntegerizerMovingExponent, hfree,
                Li2Lean.P0.Integerization.p0RateW, hlarge, hcutU, hpU']
              exact_mod_cast hc
            rw [hmexp]
            simpa only [Li2Lean.P0.Integerization.p0ValAtLeast] using hval
          · have hmexp : Li2Lean.P0.p0IntegerizerMovingExponent q m p =
                (((3 * m * Nat.log p (Li2Lean.P0.Integerization.p0DenominatorU m) : ℕ) : ℤ)) := by
              simp [Li2Lean.P0.p0IntegerizerMovingExponent, hfree,
                Li2Lean.P0.Integerization.p0RateW, hlarge, hcutU, hpU']
              exact_mod_cast (le_of_not_ge hc)
            rw [hmexp]
            exact hbase'
        · have hpU' : ¬ p ≤ Li2Lean.P0.Integerization.p0DenominatorU m := by
            simpa [hcutU] using hpU
          have hlog : Nat.log p (Li2Lean.P0.Integerization.p0DenominatorU m) = 0 :=
            Nat.log_of_lt (Nat.lt_of_not_ge hpU')
          have hmexp : Li2Lean.P0.p0IntegerizerMovingExponent q m p = 0 := by
            simp [Li2Lean.P0.p0IntegerizerMovingExponent, hfree,
              hcutU, hpU']
          rw [hmexp]
          simpa [hlog] using hbase'
      · by_cases hpU : p ≤ Li2Lean.P0.formalDivisorCutoff m
        · have hpU' : p ≤ Li2Lean.P0.Integerization.p0DenominatorU m := by
            simpa [hcutU] using hpU
          have hmexp : Li2Lean.P0.p0IntegerizerMovingExponent q m p =
              (((3 * m * Nat.log p (Li2Lean.P0.Integerization.p0DenominatorU m) : ℕ) : ℤ)) := by
            simp [Li2Lean.P0.p0IntegerizerMovingExponent, hfree,
              Li2Lean.P0.Integerization.p0RateW, hlarge, hcutU, hpU', min_self]
          rw [hmexp]
          exact hbase'
        · have hpU' : ¬ p ≤ Li2Lean.P0.Integerization.p0DenominatorU m := by
            simpa [hcutU] using hpU
          have hlog : Nat.log p (Li2Lean.P0.Integerization.p0DenominatorU m) = 0 :=
            Nat.log_of_lt (Nat.lt_of_not_ge hpU')
          have hmexp : Li2Lean.P0.p0IntegerizerMovingExponent q m p = 0 := by
            simp [Li2Lean.P0.p0IntegerizerMovingExponent, hfree,
              hcutU, hpU']
          rw [hmexp]
          simpa [hlog] using hbase'
  · intro m hm h4
    exact Li2Lean.p0CanonicalPolynomial_degree_bound (q : ℤ) m h4
  · exact p0Integerizer_plan_generic_rate q h3

/-! Per-base adapters are finite checks only.  The proof content is entirely
in `p0Integerizer_plan_generic`, which is the q-parametric port of the S08
integerization chain. -/
theorem p0Integerizer_plan_q3 :
    Li2Lean.P0.P0IntegerizerProofPlan 3 (p0Rate_producer 3) := by
  exact p0Integerizer_plan_generic 3 (by norm_num) (by norm_num)

theorem p0Integerizer_plan_q4 :
    Li2Lean.P0.P0IntegerizerProofPlan 4 (p0Rate_producer 4) := by
  exact p0Integerizer_plan_generic 4 (by norm_num) (by norm_num)

theorem p0Integerizer_plan_q5 :
    Li2Lean.P0.P0IntegerizerProofPlan 5 (p0Rate_producer 5) := by
  exact p0Integerizer_plan_generic 5 (by norm_num) (by norm_num)

theorem p0Integerizer_plan_q6 :
    Li2Lean.P0.P0IntegerizerProofPlan 6 (p0Rate_producer 6) := by
  exact p0Integerizer_plan_generic 6 (by norm_num) (by norm_num)

theorem p0Integerizer_plan_q7 :
    Li2Lean.P0.P0IntegerizerProofPlan 7 (p0Rate_producer 7) := by
  exact p0Integerizer_plan_generic 7 (by norm_num) (by norm_num)

theorem p0Integerizer_plan_q8 :
    Li2Lean.P0.P0IntegerizerProofPlan 8 (p0Rate_producer 8) := by
  exact p0Integerizer_plan_generic 8 (by norm_num) (by norm_num)

theorem p0Integerizer_plan_q9 :
    Li2Lean.P0.P0IntegerizerProofPlan 9 (p0Rate_producer 9) := by
  exact p0Integerizer_plan_generic 9 (by norm_num) (by norm_num)

theorem p0Integerizer_plan_q10 :
    Li2Lean.P0.P0IntegerizerProofPlan 10 (p0Rate_producer 10) := by
  exact p0Integerizer_plan_generic 10 (by norm_num) (by norm_num)

theorem p0Integerizer_plan_q11 :
    Li2Lean.P0.P0IntegerizerProofPlan 11 (p0Rate_producer 11) := by
  exact p0Integerizer_plan_generic 11 (by norm_num) (by norm_num)

theorem p0Integerizer_producer :
    ∀ (q : ℕ) (hq : InRange (q : ℤ)), 3 ≤ q →
      P0IntegerizerBoundAt (family (q : ℤ) hq) (p0Rate_producer q) := by
  intro q hq hq3
  have hq11 : q ≤ 11 := by
    have hrange := hq
    simp [InRange] at hrange
    omega
  interval_cases q
  · exact Li2Lean.P0.integerizerBoundAt_of_proof_plan
      p0Integerizer_plan_q3
  · exact Li2Lean.P0.integerizerBoundAt_of_proof_plan
      p0Integerizer_plan_q4
  · exact Li2Lean.P0.integerizerBoundAt_of_proof_plan
      p0Integerizer_plan_q5
  · exact Li2Lean.P0.integerizerBoundAt_of_proof_plan
      p0Integerizer_plan_q6
  · exact Li2Lean.P0.integerizerBoundAt_of_proof_plan
      p0Integerizer_plan_q7
  · exact Li2Lean.P0.integerizerBoundAt_of_proof_plan
      p0Integerizer_plan_q8
  · exact Li2Lean.P0.integerizerBoundAt_of_proof_plan
      p0Integerizer_plan_q9
  · exact Li2Lean.P0.integerizerBoundAt_of_proof_plan
      p0Integerizer_plan_q10
  · exact Li2Lean.P0.integerizerBoundAt_of_proof_plan
      p0Integerizer_plan_q11

theorem p0RateMargin_producer :
    ∀ q : ℕ, 3 ≤ q → q ≤ 11 →
      p0Rate_producer q < p0PositiveChord q := by
  intro q hq3 hq11
  simpa [p0Rate_producer, p0PositiveChord, p0PositiveChordFormulaLocal,
    positiveBaseParameter] using
    (p0RateRelaxed_lt_p0PositiveChordFormula q hq3 hq11)

theorem p0Tower_producer :
    ∀ (q : ℕ) (hq : InRange (q : ℤ)), 3 ≤ q →
      ∃ M p : ℕ,
        Nonempty (P0FrobeniusTowerCertificate (family (q : ℤ) hq) M p) := by
  exact p0Tower_producer_proof

/-- Construction-specific signed-V nonvanishing for each base in the range.
The theorem has no carrier argument; its proof is reduced to six explicit
per-base source-bound obligations in `B3.ActualFrobeniusTowerCarriers`. Those
carriers include the source determinant boundary, scaled-polynomial fields,
and strict tail estimate; finite residue checks alone do not discharge them.
Source: v13 nonvanishing.tex:146-275. -/
theorem vNonvanishing_plan_producer :
    ∀ (q : ℕ), 2 ≤ q → q ≤ 7 → B3.NonvanishingPlan q := by
  intro q hq2 hq7
  exact B3.nonvanishing_plan_of_v13_from_range_inputs
    B3.v13_frobenius_range_producer ⟨hq2, hq7⟩

/-- Once the six actual Frobenius carriers are supplied, the same obligation
is discharged by the explicit range adapter. -/
theorem vNonvanishing_plan_of_range_inputs
    (inputs : B3.VActualFrobeniusTowerProducers) :
    ∀ (q : ℕ), 2 ≤ q → q ≤ 7 → B3.NonvanishingPlan q := by
  intro q hq2 hq7
  exact B3.nonvanishing_plan_of_v13_from_range_inputs inputs ⟨hq2, hq7⟩

noncomputable def vInputs_producer :
    ∀ q : ℕ, 2 ≤ q → q ≤ 7 → SignedVEndpointInputs q := by
  intro q hq2 hq7
  let hq : B3.SignedVBaseRange q := ⟨hq2, hq7⟩
  let energy := B3.signed_energy_plan_of_v13 hq
  let prebound := B3.smoothing_prebound_of_v13 hq energy
  let arithmetic := B3.arithmetic_plan_of_v13 hq
  let nonvanishing := vNonvanishing_plan_producer q hq2 hq7
  have hPre : B3PreboundActual q (B3.vAlpha q) (B3.vSigma q) := by
    intro m hm hm4 hmne
    obtain ⟨n, hn⟩ := hm4
    subst m
    have hmne' : (B3.vRealPoly q (4 * n)).eval
        (li2InvValue (-(q : ℤ))) ≠ 0 := by
      simpa [vFamilyG, B3.vRealPoly] using hmne
    obtain ⟨c, hcq, hcm, hcα, hcσ⟩ := prebound n hm hmne'
    exact ⟨c, hcq, hcm, hcα, hcσ⟩
  let D : ℕ → ℚ := Classical.choose arithmetic.integerizer
  have hD := Classical.choose_spec arithmetic.integerizer
  rcases hD with ⟨hDpos, hDpoly, hDrate⟩
  have hdegree : ∀ m, 0 < m → 4 ∣ m → (vFamilyG q m).natDegree ≤ m := by
    intro m hm hm4
    obtain ⟨n, hn⟩ := hm4
    subst m
    have hnpos : 0 < n := by omega
    simpa [vFamilyG, B3.vRealPoly] using arithmetic.degree n hnpos
  have hpos : ∀ m, 0 < m → 4 ∣ m → 0 < D m := by
    intro m hm hm4
    obtain ⟨n, hn⟩ := hm4
    subst m
    have hnpos : 0 < n := by omega
    simpa using hDpos n hnpos
  have hpoly : ∀ m, 0 < m → 4 ∣ m →
      ∃ P : Polynomial ℤ,
        P.map (Int.castRingHom ℝ) = Polynomial.C (D m : ℝ) * vFamilyG q m := by
    intro m hm hm4
    obtain ⟨n, hn⟩ := hm4
    subst m
    have hnpos : 0 < n := by omega
    change ∃ P : Polynomial ℤ,
      P.map (Int.castRingHom ℝ) =
        Polynomial.C (D (4 * n) : ℝ) * B3.vRealPoly q (4 * n)
    exact hDpoly n hnpos
  have hrate : ∀ ε : ℝ, 0 < ε → ∃ M, ∀ m, M ≤ m → 0 < m → 4 ∣ m →
      Real.log (D m : ℝ) / (m : ℝ) ^ 2 ≤ B3.vTau q + ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := hDrate ε hε
    refine ⟨4 * N, ?_⟩
    intro m hm hmpos hm4
    obtain ⟨n, hn⟩ := hm4
    subst m
    have hNn : N ≤ n := by omega
    have hnpos : 0 < n := by omega
    simpa using hN n hNn hnpos
  obtain ⟨hp, _⟩ := B3.vSeedPrime_spec hq
  have hNv : ∀ r : ℚ, ∃ k₀, ∀ k, k₀ ≤ k →
      (vFamilyG q (4 * B3.vSeedPrime q ^ k)).eval (r : ℝ) ≠ 0 := by
    intro r
    simpa [vFamilyG, B3.vRealPoly] using nonvanishing.eventual r
  exact SignedVEndpointInputs.ofParts hPre D hdegree hpos hpoly hrate
    (B3.vTau_lt_vAlpha hq) (B3.vSeedPrime q) hp hNv

/-! The M0 residue consumers establish the coefficient identities used by
`HPIntegralForm`, but the final integer-affine assembly is still a concrete
producer obligation.  Keep that obligation at the actual `hpBpoly` interface
and use the adapter for the AllN field. -/
theorem hpIntegralInput_producer :
    ∀ a : ℤ, ((12 : ℤ) ≤ a ∨ a ≤ -8) →
      Li2Lean.B4.TailAnalytic.HPIntegralForm a := by
  intro a ha
  exact Li2Lean.B4.HPVpolyIntegrality.hpIntegralForm_of_range ha

theorem hpIntegral_producer :
    ∀ a : ℤ, ((12 : ℤ) ≤ a ∨ a ≤ -8) → HPIntegralForm a := by
  intro a ha
  exact producer_hpIntegral_of_integral_form (hpIntegralInput_producer a ha)

/-! The determinant/no-adjacent-zero input is likewise pinned to the actual
three-form sequence.  `producer_hpNoAdj_of_v13_input` performs the scale
normalization and determinant argument, using the concrete v13 input supplied
by the producer wiring above.
(Moved above the decay producers, which consume `hpNoAdjInput_producer` for
its `tail_representation` field.) -/
theorem hpNoAdjInput_producer :
    ∀ a : ℤ, ((12 : ℤ) ≤ a ∨ a ≤ -8) →
      Li2Lean.B4.TailAnalytic.HPNoAdjacentV13Input a := by
  intro a ha
  refine Li2Lean.B4.TailAnalytic.hpNoAdjacentV13Input_of_producers ha ?_ ?_
  · intro n
    exact Li2Lean.B4.TailAnalytic.hpRR_inv_ne_zero ha n
  · intro n
    exact Li2Lean.B4.TailAnalytic.hpDelta_identity_at a n

theorem hpNoAdj_producer :
    ∀ a : ℤ, ((12 : ℤ) ≤ a ∨ a ≤ -8) → HPNoAdjacentZero a := by
  intro a ha
  exact producer_hpNoAdj_of_v13_input ha (hpNoAdjInput_producer a ha)

/-! Positive tail `a ≥ 12`: refined beta certificate (`M = 154/1000`),
tilted coefficient bound `24 (m+1)^3 K^m` for the actual `B_m(1/a)`, and the
denominator rate (v13 `hp-tail.tex:198-256, 411-430`). -/
theorem hpDecayPos_producer :
    ∀ a : ℤ, (12 : ℤ) ≤ a → HPDecay a := by
  intro a ha
  exact Li2Lean.B4.TailAnalytic.ProducersAux.hpDecayPos_of_refined_beta ha
    (hpNoAdjInput_producer a (Or.inl ha))

/-! The raw exceptional contour input is exactly the P1/P2/branch-bound data
for the pinned `hpBpoly` sequence (v13 `hp-tail.tex:256-410`). This is a Prop
producer; it does not store an opaque certificate value.  P1 is the
construction-bound residue provider `HpNegContourResidueProvider.of_q_spec`
(edge parameterization at height `1/5`), P2 the direct v13 border bound
`hpNegBorderBound_of_v13`, P3 `hpNegBranchValueBound_of_v13_contour`. -/
theorem hpNegContourInputs_producer :
    ∀ q : ℕ, (q = 8 ∨ q = 9 ∨ q = 10) →
      Li2Lean.B4.NegativeContour.HpNegContourProducerInput q :=
  hpNegContourInputs_of_v13_p1_p2
    ⟨fun q hq =>
      Li2Lean.B4.NegContourResidueProducer.HpNegContourResidueProvider.of_q_spec
        q hq⟩

/-! The certificate-to-decay step is the bridge from the concrete
negative contour envelope through the denominator and integer-form estimates
to `L_n(a) → 0` (v13 `hp-tail.tex:411-566`). It is kept separate from the
contour inputs so a contour bound alone is not mistaken for `HPDecay`.
`a = -8, -9, -10` use the rectangle certificates; `a ≤ -11` uses the tilted
coefficient bound (`a = -11`: tilt `14180/100000`, bracket `hpNegativeQ11M`;
`a ≤ -12`: tilt `13683/100000`, bracket `(4/27)^2 ≤ (154/1000)^2`). -/
theorem hpDecayNeg_of_contour_rectangles
    (h8 : Nonempty (Li2Lean.B4.NegativeContour.NegContourRectangleCertificate
      Li2Lean.B4.NegativeContour.hpBSequence 8))
    (h9 : Nonempty (Li2Lean.B4.NegativeContour.NegContourRectangleCertificate
      Li2Lean.B4.NegativeContour.hpBSequence 9))
    (h10 : Nonempty (Li2Lean.B4.NegativeContour.NegContourRectangleCertificate
      Li2Lean.B4.NegativeContour.hpBSequence 10)) :
    ∀ a : ℤ, a ≤ (-8 : ℤ) → HPDecay a := by
  intro a ha
  have hI : ∀ b : ℤ, b ≤ -8 → Li2Lean.B4.TailAnalytic.HPNoAdjacentV13Input b :=
    fun b hb => hpNoAdjInput_producer b (Or.inr hb)
  rcases (show a = -8 ∨ a = -9 ∨ a = -10 ∨ a ≤ -11 by omega) with h | h | h | h
  · subst h
    exact Li2Lean.B4.TailAnalytic.ProducersAux.hpDecayNeg_q8_of_certificate h8
      (hI _ (by norm_num))
  · subst h
    exact Li2Lean.B4.TailAnalytic.ProducersAux.hpDecayNeg_q9_of_certificate h9
      (hI _ (by norm_num))
  · subst h
    exact Li2Lean.B4.TailAnalytic.ProducersAux.hpDecayNeg_q10_of_certificate h10
      (hI _ (by norm_num))
  · exact Li2Lean.B4.TailAnalytic.ProducersAux.hpDecayNeg_le_eleven h
      (hI a (by omega))

theorem hpDecayNeg_producer :
    ∀ a : ℤ, a ≤ (-8 : ℤ) → HPDecay a := by
  have h8 := Li2Lean.B4.NegativeContour.negativeContour_rectangle_q8_of_producers
    (hpNegContourInputs_producer 8 (by norm_num))
  have h9 := Li2Lean.B4.NegativeContour.negativeContour_rectangle_q9_of_producers
    (hpNegContourInputs_producer 9 (by norm_num))
  have h10 := Li2Lean.B4.NegativeContour.negativeContour_rectangle_q10_of_producers
    (hpNegContourInputs_producer 10 (by norm_num))
  exact hpDecayNeg_of_contour_rectangles h8 h9 h10

/-- The consumer sees exactly the ten named obligations above. -/
noncomputable def allNProducers : AllNProducers :=
  AllNProducers.ofNamed p0Profile_producer p0Rate_producer
    p0Integerizer_producer p0RateMargin_producer p0Tower_producer
    vInputs_producer hpIntegral_producer hpDecayPos_producer
    hpDecayNeg_producer hpNoAdj_producer

end

end Li2Lean.AllNAssembly

#print axioms Li2Lean.B4.TailAnalytic.ProducersAux.hpBRealAt_abs_le_of_tilt
#print axioms Li2Lean.B4.TailAnalytic.ProducersAux.hpDecayNeg_le_eleven
#print axioms Li2Lean.AllNAssembly.hpDecayPos_producer
#print axioms Li2Lean.AllNAssembly.hpNegContourInputs_producer
#print axioms Li2Lean.AllNAssembly.hpDecayNeg_of_contour_rectangles
#print axioms Li2Lean.AllNAssembly.hpDecayNeg_producer
#print axioms Li2Lean.AllNAssembly.vNonvanishing_plan_producer
