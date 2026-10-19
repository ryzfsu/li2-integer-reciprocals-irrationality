/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
/-
Top-down B3 interfaces for the signed determinant construction in v13.
The four construction-specific producer obligations and their endpoint glue
are in `Li2Lean.B3.Producers`, downstream of the actual S0 and producer
adapters, to avoid an import cycle.
-/

import Li2Lean.V.AllMSmoothing
import Li2Lean.V.SignedEnergy
import Li2Lean.V.VFamily
import Li2Lean.V.VPath
import Li2Lean.V.Q4ReferenceData
import Li2Lean.V.Q5Certificate
import Li2Lean.V.Q7ReferenceData
import Li2Lean.B3.ArithmeticPinning
import Li2Lean.Kit.EndpointCriterion
import Li2Lean.Statement

namespace Li2Lean

noncomputable section

namespace B3

open MeasureTheory Polynomial

/-! ## 0. Unchanged skeleton vocabulary -/

/-- The signed V bases covered by v13 `v-analytic.tex:4-12`. -/
def signedBase (q : ℕ) : ℤ := -(q : ℤ)

def SignedVBaseRange (q : ℕ) : Prop := 2 ≤ q ∧ q ≤ 7

def AdmissibleIndex (m : ℕ) : Prop :=
  (∃ n : ℕ, m = 4 * n) ∧ 64 ≤ m

/-! ## 1. The polynomial family and its real evaluation -/

/-- `G_m(T;-q)` over `ℝ`.  Source: `V.vPolynomial` (v13 `v-arithmetic.tex:24-32`,
`nonvanishing.tex:146-169`).  Only `m = 4 n` is ever consumed. -/
def vRealPoly (q m : ℕ) : Polynomial ℝ :=
  (V.vPolynomial (m / 4) (-(q : ℤ))).map (algebraMap ℚ ℝ)

theorem vRealPoly_four_mul (q n : ℕ) :
    vRealPoly q (4 * n) =
      (V.vPolynomial n (-(q : ℤ))).map (algebraMap ℚ ℝ) := by
  unfold vRealPoly
  rw [Nat.mul_div_cancel_left n (by norm_num : (0 : ℕ) < 4)]

/-- Bridge to the S0 plan's `vGValue` (`B3-S0-representation-lean-the proof plan §3.0). -/
theorem vRealPoly_eval_eq_eval₂ (q n : ℕ) (x : ℝ) :
    (vRealPoly q (4 * n)).eval x =
      (V.vPolynomial n (-(q : ℤ))).eval₂ (algebraMap ℚ ℝ) x := by
  rw [vRealPoly_four_mul, Polynomial.eval_map]

/-- Rational evaluation commutes with the real map. [Verified: rw with `eq_ratCast`
instance path; alternative `simp [vRealPoly_four_mul, Polynomial.eval_map]`] -/
theorem vRealPoly_eval_ratCast (q n : ℕ) (r : ℚ) :
    (vRealPoly q (4 * n)).eval (r : ℝ) =
      (((V.vPolynomial n (-(q : ℤ))).eval r : ℚ) : ℝ) := by
  rw [vRealPoly_four_mul, Polynomial.eval_map, ← eq_ratCast (algebraMap ℚ ℝ) r,
    Polynomial.eval₂_at_apply, eq_ratCast]

/-! ## 2. Named missing inputs (pinned; no free certificate fields) -/

/-- (A) Analytic producer, certificate form.  `g` is pinned to
`log |G_m(Li₂(-1/q))|`, `m` and `q` are pinned, and the `G ≠ 0` premise
removes the `Real.log 0 = 0` trap (v13 `v-analytic.tex:522-530,628-629`). -/
def VAllMPreboundProducer (q : ℕ) (alpha sigma : ℝ) : Prop :=
  ∀ n : ℕ, 64 ≤ 4 * n →
    (vRealPoly q (4 * n)).eval (li2InvValue (-(q : ℤ))) ≠ 0 →
    ∃ c : AllMSmoothingCertificate
        (Real.log |(vRealPoly q (4 * n)).eval (li2InvValue (-(q : ℤ)))|),
      c.q = q ∧ c.m = 4 * n ∧ alpha ≤ c.alpha ∧ c.sigma ≤ sigma

/-- (A') The same input as a raw inequality (what the prebound proof actually
produces, v13 `v-analytic.tex:591-610`). -/
def VRawPrebound (q : ℕ) (alpha sigma : ℝ) : Prop :=
  ∀ n : ℕ, 64 ≤ 4 * n →
    (vRealPoly q (4 * n)).eval (li2InvValue (-(q : ℤ))) ≠ 0 →
    Real.log |(vRealPoly q (4 * n)).eval (li2InvValue (-(q : ℤ)))| ≤
      -alpha * ((4 * n : ℕ) : ℝ) ^ 2 +
        (13 / 2 : ℝ) * ((4 * n : ℕ) : ℝ) * Real.log ((4 * n : ℕ) : ℝ) +
        3 * sigma * (1 + Real.log (((4 * n : ℕ) : ℝ) ^ 2 / 3)) +
        (2 * denominatorTransferCost q + 7 + 130) + ((4 * n : ℕ) : ℝ)

/-- (B1) Degree bound (pure algebra; see md §5.1 for the proof plan). -/
def VDegreeBound (q : ℕ) : Prop :=
  ∀ n : ℕ, 0 < n → (vRealPoly q (4 * n)).natDegree ≤ 4 * n

/-- (B2) Integerizer with rate `tau` (v13 `v-arithmetic.tex:353-421`,
`prop:v-fixed-arithmetic`).  Same shape as `P0IntegerizerBound`. -/
def VIntegerizerBound (q : ℕ) (tau : ℝ) : Prop :=
  ∃ D : ℕ → ℚ,
    (∀ n : ℕ, 0 < n → 0 < D (4 * n)) ∧
    (∀ n : ℕ, 0 < n → ∃ P : Polynomial ℤ,
      P.map (Int.castRingHom ℝ) =
        Polynomial.C (D (4 * n) : ℝ) * vRealPoly q (4 * n)) ∧
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 0 < n →
      Real.log (D (4 * n) : ℝ) / ((4 * n : ℕ) : ℝ) ^ 2 ≤ tau + ε)

/-- (C) Eventual nonvanishing on `m = 4 p^k` (v13 `lem:v-eventual-nonzero`,
`nonvanishing.tex:262-275`). -/
def VEventualNonvanishing (q p : ℕ) : Prop :=
  ∀ r : ℚ, ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
    (vRealPoly q (4 * p ^ k)).eval (r : ℝ) ≠ 0

/-- The full per-base hypothesis bundle consumed by the endpoint criterion.
All four fields are proofs (valid `Prop` structure); every constant is a
parameter, so a per-`q` instance must pin it. -/
structure SignedVHypotheses (q p : ℕ) (alpha tau sigma : ℝ) : Prop where
  analytic : V.signedVSmoothingBound q (vRealPoly q) alpha tau (10 + 3 * sigma) 0 0
  degree : VDegreeBound q
  integerizer : VIntegerizerBound q tau
  nonvanishing : VEventualNonvanishing q p

/-! ## 3. Glue lemmas (sorry-free) -/

/-- (A') ⟹ (A): build the merged certificate with `G := (value : ℂ)`. -/
theorem producer_of_rawPrebound {q : ℕ} {alpha sigma : ℝ}
    (hq2 : 2 ≤ q) (hq7 : q ≤ 7)
    (hσ : ∃ Ax Av Az : ℝ, 0 ≤ Ax ∧ 0 ≤ Av ∧ 0 ≤ Az ∧ sigma = sigmaBudget Ax Av Az)
    (h : VRawPrebound q alpha sigma) :
    VAllMPreboundProducer q alpha sigma := by
  intro n hn hy
  have hσ0 : 0 ≤ sigma := by
    obtain ⟨Ax, Av, Az, hx, hv, hz, rfl⟩ := hσ
    unfold sigmaBudget densityTransferBudget potentialModulusCoefficient
      xMass vMass zMass
    linarith
  refine ⟨{
    G := (((vRealPoly q (4 * n)).eval (li2InvValue (-(q : ℤ))) : ℝ) : ℂ)
    G_ne_zero := Complex.ofReal_ne_zero.mpr hy
    g_eq_log_norm := by rw [Complex.norm_real, Real.norm_eq_abs]
    q := q
    m := 4 * n
    q_ge_two := hq2
    q_le_seven := hq7
    m_eq_four_n := ⟨n, rfl⟩
    m_ge_64 := hn
    alpha := alpha
    tau := alpha - 1
    sigma := sigma
    alpha_gt_tau := by linarith
    sigma_nonneg := hσ0
    sigma_eq_budget := hσ
    prebound := h n hn hy }, rfl, rfl, le_rfl, le_rfl⟩

/-- (A) ⟹ the merged generic signed-V analytic interface
`V.signedVSmoothingBound` with `cLog = 10 + 3σ`, `cLinear = cConst = 0`.
Uses the merged `all_m_log_bound_of_certificate` (v13 `v-analytic.tex:612-627`). -/
theorem signedVSmoothingBound_of_producer {q : ℕ} {alpha tau sigma : ℝ}
    (h : VAllMPreboundProducer q alpha sigma) :
    V.signedVSmoothingBound q (vRealPoly q) alpha tau (10 + 3 * sigma) 0 0 := by
  intro n hn
  by_cases hy0 : (vRealPoly q (4 * n)).eval (li2InvValue (-(q : ℤ))) = 0
  · -- the zero case is the paper's "holds trivially", now with |0| = 0
    rw [hy0, abs_zero]
    exact (Real.exp_pos _).le
  obtain ⟨c, -, hcm, hcα, hcσ⟩ := h n hn hy0
  have hlog := all_m_log_bound_of_certificate c
  rw [hcm] at hlog
  have hcast : ((4 * n : ℕ) : ℝ) = 4 * (n : ℝ) := by norm_num
  rw [hcast] at hlog
  have hM1 : (1 : ℝ) ≤ 4 * (n : ℝ) := by
    have h1 : (1 : ℝ) ≤ ((4 * n : ℕ) : ℝ) := by
      exact_mod_cast (show 1 ≤ 4 * n by omega)
    rwa [hcast] at h1
  have hMlog : 0 ≤ 4 * (n : ℝ) * Real.log (4 * (n : ℝ)) :=
    mul_nonneg (by linarith) (Real.log_nonneg hM1)
  have hα := mul_le_mul_of_nonneg_right hcα (sq_nonneg (4 * (n : ℝ)))
  have hσ := mul_le_mul_of_nonneg_right hcσ hMlog
  have hcmp :
      -c.alpha * (4 * (n : ℝ)) ^ 2 +
          (10 + 3 * c.sigma) * (4 * (n : ℝ)) * Real.log (4 * (n : ℝ)) ≤
        -alpha * (4 * (n : ℝ)) ^ 2 +
          (10 + 3 * sigma) * (4 * (n : ℝ)) * Real.log (4 * (n : ℝ)) +
          0 * (4 * (n : ℝ)) + 0 := by
    nlinarith [hα, hσ]
  exact (Real.log_le_iff_le_exp (abs_pos.mpr hy0)).1 (hlog.trans hcmp)

/-- Cast bridge: `V.signedVSmoothingBound` uses `(4 * n : ℝ) = 4 * ↑n`, the
endpoint certificate uses `↑(4 * n)`. -/
theorem analytic_at_index {q : ℕ} {G : ℕ → Polynomial ℝ} {alpha tau cLog : ℝ}
    (h : V.signedVSmoothingBound q G alpha tau cLog 0 0) {n : ℕ} (hn : 64 ≤ 4 * n) :
    |(G (4 * n)).eval (li2InvValue (-(q : ℤ)))| ≤
      Real.exp (-alpha * ((4 * n : ℕ) : ℝ) ^ 2 +
        cLog * ((4 * n : ℕ) : ℝ) * Real.log ((4 * n : ℕ) : ℝ) +
        0 * ((4 * n : ℕ) : ℝ) + 0) := by
  have hcast : ((4 * n : ℕ) : ℝ) = 4 * (n : ℝ) := by norm_num
  rw [hcast]
  exact h n hn

/-- ℚ-level degree bound ⟹ (B1). -/
theorem vDegreeBound_of_rat {q : ℕ}
    (h : ∀ n : ℕ, 0 < n → (V.vPolynomial n (-(q : ℤ))).natDegree ≤ 4 * n) :
    VDegreeBound q := by
  intro n hn
  rw [vRealPoly_four_mul]
  exact Polynomial.natDegree_map_le.trans (h n hn)

/-- ℚ-level nonvanishing ⟹ (C). -/
theorem vEventualNonvanishing_of_rat {q p : ℕ}
    (h : ∀ r : ℚ, ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      (V.vPolynomial (p ^ k) (-(q : ℤ))).eval r ≠ 0) :
    VEventualNonvanishing q p := by
  intro r
  obtain ⟨k₀, hk⟩ := h r
  refine ⟨k₀, fun k hk' => ?_⟩
  rw [vRealPoly_eval_ratCast]
  exact_mod_cast hk k hk'

/-! ## 4. Endpoint assembly (replaces sorry #5; sorry-free) -/

/-- The signed-V `EndpointCertificate`, index `m_k = 4 p^(k+2)` (the `+2`
shift gives `m ≥ 4·11² = 484 ≥ 64`, so the all-`m` bound applies at every
index).  Template: `P0.PositiveBase.q11EndpointCertificate_of_inputs`. -/
theorem signedV_endpointCertificate_of_hypotheses {q p : ℕ} {alpha tau sigma : ℝ}
    (hp : Nat.Prime p) (hp11 : 11 ≤ p) (hmargin : tau < alpha)
    (H : SignedVHypotheses q p alpha tau sigma) :
    Nonempty (EndpointCertificate (li2InvValue (-(q : ℤ)))) := by
  obtain ⟨D, hDpos, hpoly, hrate⟩ := H.integerizer
  have hpone : 1 < p := hp.one_lt
  have hn_pos : ∀ k : ℕ, 0 < p ^ (k + 2) := fun k => pow_pos hp.pos _
  have hn16 : ∀ k : ℕ, 16 ≤ p ^ (k + 2) := by
    intro k
    have h1 : p ^ 2 ≤ p ^ (k + 2) := Nat.pow_le_pow_right hp.pos (by omega)
    have h2 : 11 ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left hp11 2
    have h3 : (11 : ℕ) ^ 2 = 121 := by norm_num
    omega
  have hidx64 : ∀ k : ℕ, 64 ≤ 4 * p ^ (k + 2) := by
    intro k
    have := hn16 k
    omega
  have hmono : StrictMono (fun k : ℕ => 4 * p ^ (k + 2)) := by
    intro i j hij
    have hpow : p ^ (i + 2) < p ^ (j + 2) := Nat.pow_lt_pow_right hpone (by omega)
    exact (Nat.mul_lt_mul_left (by norm_num : 0 < 4)).2 hpow
  have hrate' : ∀ ε : ℝ, 0 < ε → ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      Real.log (D (4 * p ^ (k + 2)) : ℝ) / ((4 * p ^ (k + 2) : ℕ) : ℝ) ^ 2 ≤
        tau + ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := hrate ε hε
    refine ⟨N, fun k hk => ?_⟩
    have hkpow : k + 2 ≤ p ^ (k + 2) := (Nat.lt_pow_self hpone).le
    exact hN (p ^ (k + 2)) (by omega) (hn_pos k)
  have hnonzero : ∀ r : ℚ, ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      (vRealPoly q (4 * p ^ (k + 2))).eval (r : ℝ) ≠ 0 := by
    intro r
    obtain ⟨K, hK⟩ := H.nonvanishing r
    exact ⟨K, fun k hk => hK (k + 2) (by omega)⟩
  exact ⟨{
    index := fun k => 4 * p ^ (k + 2)
    G := vRealPoly q
    D := D
    alpha := alpha
    tau := tau
    cLog := 10 + 3 * sigma
    cLinear := 0
    cConst := 0
    index_strictMono := hmono
    index_multiple_four := fun k => dvd_mul_right 4 (p ^ (k + 2))
    index_ge_eight := fun k => by
      show 8 ≤ 4 * p ^ (k + 2)
      have := hn16 k
      omega
    alpha_gt_tau := hmargin
    degree_bound := fun k => H.degree (p ^ (k + 2)) (hn_pos k)
    integerizer_pos := fun k => hDpos (p ^ (k + 2)) (hn_pos k)
    integerizer_poly := fun k => hpoly (p ^ (k + 2)) (hn_pos k)
    analytic_bound := fun k => analytic_at_index H.analytic (hidx64 k)
    integerizer_rate := hrate'
    nonzero_at_rationals := hnonzero }⟩

/-- Generic conditional range theorem. -/
theorem signedV_irrational_of_hypotheses {q p : ℕ} {alpha tau sigma : ℝ}
    (hp : Nat.Prime p) (hp11 : 11 ≤ p) (hmargin : tau < alpha)
    (H : SignedVHypotheses q p alpha tau sigma) :
    Irrational (li2InvValue (signedBase q)) := by
  obtain ⟨c⟩ := signedV_endpointCertificate_of_hypotheses hp hp11 hmargin H
  exact ContourKit.endpoint_criterion c

/-! ## 5. Per-base conditional range theorems (usable now, sorry-free)

Constants: v13 `tab:v-certificates`, `tab:v-transfer-constants`,
`nonvanishing.tex` seed table.  `α₆` is the corrected `3.26091`
(the printed `3.26092` does not follow from the printed `Q_{6,-}`). -/

theorem signed_v_range_q2_of_hypotheses
    (H : SignedVHypotheses 2 11 (434875 / 100000) (431765 / 100000) (14092327 / 1000)) :
    Irrational (li2InvValue (signedBase 2)) :=
  signedV_irrational_of_hypotheses (by norm_num) le_rfl (by norm_num) H

theorem signed_v_range_q3_of_hypotheses
    (H : SignedVHypotheses 3 11 (396707 / 100000) (386995 / 100000) (13219499 / 1000)) :
    Irrational (li2InvValue (signedBase 3)) :=
  signedV_irrational_of_hypotheses (by norm_num) le_rfl (by norm_num) H

/-- q = 4, constants pinned to the merged `V.Q4ReferenceData`. -/
theorem signed_v_range_q4_of_hypotheses
    (H : SignedVHypotheses 4 23 (V.Q4ReferenceData.alphaLower : ℝ)
      (V.Q4ReferenceData.tauUpper : ℝ) (12702122 / 1000)) :
    Irrational (li2InvValue (signedBase 4)) :=
  signedV_irrational_of_hypotheses (by norm_num) (by norm_num)
    (by exact_mod_cast V.Q4ReferenceData.alpha_gt_tau) H

/-- q = 5, constants pinned to the merged `V.Q5Certificate`. -/
theorem signed_v_range_q5_of_hypotheses
    (H : SignedVHypotheses 5 11 (V.Q5Certificate.q5AlphaLower : ℝ)
      (V.Q5Certificate.q5TauUpper : ℝ) (V.Q5Certificate.q5SigmaUpper : ℝ)) :
    Irrational (li2InvValue (signedBase 5)) :=
  signedV_irrational_of_hypotheses (by norm_num) le_rfl
    (by exact_mod_cast V.Q5Certificate.q5_alpha_gt_tau) H

theorem signed_v_range_q6_of_hypotheses
    (H : SignedVHypotheses 6 17 (326091 / 100000) (310460 / 100000) (12095881 / 1000)) :
    Irrational (li2InvValue (signedBase 6)) :=
  signedV_irrational_of_hypotheses (by norm_num) (by norm_num) (by norm_num) H

/-- q = 7, constants pinned to the merged `V.Q7Reference`. -/
theorem signed_v_range_q7_of_hypotheses
    (H : SignedVHypotheses 7 17 (V.Q7Reference.q7AlphaLower : ℝ)
      (V.Q7Reference.q7TauUpper : ℝ) (V.Q7Reference.q7SigmaUpper : ℝ)) :
    Irrational (li2InvValue (signedBase 7)) :=
  signedV_irrational_of_hypotheses (by norm_num) (by norm_num)
    (by exact_mod_cast V.Q7Reference.q7Alpha_gt_q7Tau) H

/-- Pins the free `determinantAbs` of the merged `Q5AnalyticInput` to the
actual q = 5 determinant and converts to the generic interface.
[Verified: `simpa only` closes after beta + `abs_abs`] -/
theorem q5_signedVSmoothingBound_of_analyticBound
    (h : V.Q5Certificate.Q5AnalyticBound
      (fun m => |(vRealPoly 5 m).eval (li2InvValue (-((5 : ℕ) : ℤ)))|)) :
    V.signedVSmoothingBound 5 (vRealPoly 5) (V.Q5Certificate.q5AlphaLower : ℝ)
      (V.Q5Certificate.q5TauUpper : ℝ)
      (10 + 3 * (V.Q5Certificate.q5SigmaUpper : ℝ)) 0 0 := by
  intro n hn
  have h' := h n hn
  have hc : ((V.Q5Certificate.q5TransferCoefficient : ℚ) : ℝ) =
      10 + 3 * (V.Q5Certificate.q5SigmaUpper : ℝ) := by
    -- single closing tactic: a trailing `ring` after `push_cast` would fail
    -- with "no goals" if `push_cast` already closes the goal
    norm_num [V.Q5Certificate.q5TransferCoefficient]
  rw [hc] at h'
  simpa only [zero_mul, add_zero, abs_abs] using h'

/-! ## 6. Arithmetic pinning adapter (fixes the free `vp` / `valuation`) -/

/-- Gauss valuation, the intended instantiation of the free `vp` parameter of
`V.Q{2,4,6,7}Arithmetic.{ResidueBlock,OuterPole}Certificate` and of the free
`valuation` of `V.Q5Certificate.Q5{ResidueBlock,OuterPole}Bound`. -/
def vGaussVal (p : ℕ) (P : Polynomial ℚ) : ℤ :=
  if h : P.support.Nonempty then P.support.inf' h (fun i => padicValRat p (P.coeff i))
  else 0

/-- [Verified: `Finset.inf'_le` argument form] -/
theorem coeff_val_of_gauss {p : ℕ} {P : Polynomial ℚ} {E : ℤ}
    (h : vGaussVal p P ≥ -E) :
    ∀ i : ℕ, P.coeff i ≠ 0 → -E ≤ padicValRat p (P.coeff i) := by
  intro i hi
  have hmem : i ∈ P.support := Polynomial.mem_support_iff.mpr hi
  have hne : P.support.Nonempty := ⟨i, hmem⟩
  unfold vGaussVal at h
  rw [dif_pos hne] at h
  exact le_trans h (Finset.inf'_le _ hmem)

/-! ## 7. Per-base constant tables for the uniform skeleton -/

def vSeedPrime : ℕ → ℕ
  | 2 => 11 | 3 => 11 | 4 => 23 | 5 => 11 | 6 => 17 | 7 => 17 | _ => 0

def vAlpha : ℕ → ℝ
  | 2 => 434875 / 100000 | 3 => 396707 / 100000 | 4 => 368211 / 100000
  | 5 => 345240 / 100000 | 6 => 326091 / 100000 | 7 => 309651 / 100000
  | _ => 0

def vTau : ℕ → ℝ
  | 2 => 431765 / 100000 | 3 => 386995 / 100000 | 4 => 355230 / 100000
  | 5 => 330591 / 100000 | 6 => 310460 / 100000 | 7 => 293439 / 100000
  | _ => 0

def vSigma : ℕ → ℝ
  | 2 => 14092327 / 1000 | 3 => 13219499 / 1000 | 4 => 12702122 / 1000
  | 5 => 12351983 / 1000 | 6 => 12095881 / 1000 | 7 => 11898583 / 1000
  | _ => 0

/-- [Verified: `norm_num [vSeedPrime]` unfolds the literal match; alternative
`all_goals (show Nat.Prime _ ∧ _ ; norm_num)` after `interval_cases`] -/
theorem vSeedPrime_spec {q : ℕ} (hq : SignedVBaseRange q) :
    Nat.Prime (vSeedPrime q) ∧ 11 ≤ vSeedPrime q := by
  obtain ⟨h2, h7⟩ := hq
  interval_cases q <;> norm_num [vSeedPrime]

/-- [Verified: as above] -/
theorem vTau_lt_vAlpha {q : ℕ} (hq : SignedVBaseRange q) : vTau q < vAlpha q := by
  obtain ⟨h2, h7⟩ := hq
  interval_cases q <;> norm_num [vTau, vAlpha]

/-! ## 8. Honest plan statements (replace the bare-`Prop`-field structures) -/

/-- Ball bound `ν(B(w,t)) ≤ A t` (v13 `v-analytic.tex:425-434`). -/
def VBallBound (ν : Measure ℂ) (A : ℝ) : Prop :=
  ∀ w : ℂ, ∀ t : ℝ, 0 < t → (ν (Metric.ball w t)).toReal ≤ A * t

/-- Per-base finite energy certificate (v13 `v-analytic.tex:337-347,425-437`).
Field bounds are on `Ioc 0 1`, never `Icc`: at `w = 0` Lean's `log 0 = 0`
makes `F_x(0), F_v(0)` exceed `K_x, K_v` (B3-energy-certificates-plan §0.2).
The integrability ledger that the prebound proof needs is owned by the construction component
(`SignedVDualAdmissible`, positivity plan Step D) and must be added here
before `smoothing_prebound_of_v13` is attempted. -/
def VEnergyCertificate (q : ℕ) (alpha sigma : ℝ) : Prop :=
  ∃ (ν : V.SignedVMeasures) (Qlow Kx Kv Kz Ax Av Az : ℝ),
    ν.q = q ∧
    ν.μx (Complex.ofReal '' Set.Icc (0 : ℝ) 1)ᶜ = 0 ∧
    ν.μv (Complex.ofReal '' Set.Icc (0 : ℝ) 1)ᶜ = 0 ∧
    ν.μz (V.vContourTrace q)ᶜ = 0 ∧
    (∀ z : ℂ, ν.μx {z} = 0) ∧ (∀ z : ℂ, ν.μv {z} = 0) ∧ (∀ z : ℂ, ν.μz {z} = 0) ∧
    0 ≤ Ax ∧ 0 ≤ Av ∧ 0 ≤ Az ∧
    VBallBound ν.μx Ax ∧ VBallBound ν.μv Av ∧ VBallBound ν.μz Az ∧
    sigma = sigmaBudget Ax Av Az ∧
    Qlow ≤ V.signedVQuadratic ν ∧
    (∀ t : ℝ, t ∈ Set.Ioc (0 : ℝ) 1 → V.signedVFullFieldX ν (t : ℂ) < Kx) ∧
    (∀ t : ℝ, t ∈ Set.Ioc (0 : ℝ) 1 → V.signedVFullFieldV ν (t : ℂ) < Kv) ∧
    (∀ w ∈ V.vContourTrace q, V.signedVFullFieldZ ν w < Kz) ∧
    alpha ≤ Qlow - 3 / 2 * Real.log q - Kx - 5 / 4 * Kv - Kz

structure SignedEnergyPlan (q : ℕ) : Prop where
  base_range : SignedVBaseRange q
  certificate : VEnergyCertificate q (vAlpha q) (vSigma q)

structure ArithmeticPlan (q : ℕ) : Prop where
  degree : VDegreeBound q
  integerizer : VIntegerizerBound q (vTau q)

structure NonvanishingPlan (q : ℕ) : Prop where
  eventual : VEventualNonvanishing q (vSeedPrime q)

end B3

end

end Li2Lean

#print axioms Li2Lean.B3.signedV_irrational_of_hypotheses
#print axioms Li2Lean.B3.signed_v_range_q3_of_hypotheses
#print axioms Li2Lean.B3.signedVSmoothingBound_of_producer
#print axioms Li2Lean.B3.producer_of_rawPrebound
