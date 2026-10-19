/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/

import Mathlib
import Li2Lean.Kit.CircleSmoothing

/-!
Conditional interface for the all-`m` smoothing step in the signed V route.

This file records the construction and the finite arithmetic consequences of
`source/chapters/v-analytic.tex:493-631`.  The measure estimates, the
off-diagonal subharmonicity argument, and the determinant integrand estimate
remain certificate fields.  In particular, this module does not turn a
numerical table or a missing analytic bridge into an unconditional theorem.

The circle-average identity is imported from the frozen Li2(1/2) `Kit` as a
generic logarithmic-circle helper.  It is not a source of the signed V proof.
-/

namespace Li2Lean

noncomputable section

namespace B3

open MeasureTheory

/-! ### The literal smoothing geometry -/

/-- The smoothing radius `epsilon = m⁻²`, v13 `v-analytic.tex:532-535`. -/
def smoothingEpsilon (m : ℕ) : ℝ := (m : ℝ)⁻¹ ^ 2

/-- The translated centre `u + 2 i epsilon`, v13 `v-analytic.tex:534-535`. -/
def translatedAtomCenter (u : ℂ) (m : ℕ) : ℂ :=
  u + Complex.ofReal (2 * smoothingEpsilon m) * Complex.I

/-- The circle used to replace one empirical atom, v13 `v-analytic.tex:534-536`.
-/
def translatedAtom (u : ℂ) (m : ℕ) (theta : ℝ) : ℂ :=
  circleMap (translatedAtomCenter u m) (smoothingEpsilon m) theta

theorem smoothingEpsilon_pos {m : ℕ} (hm : 0 < m) :
    0 < smoothingEpsilon m := by
  unfold smoothingEpsilon
  positivity

theorem smoothingEpsilon_le_one_div_4096 {m : ℕ} (hm : 64 ≤ m) :
    smoothingEpsilon m ≤ (1 / 4096 : ℝ) := by
  have hmR : (64 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmRpos : 0 < (m : ℝ) := by linarith
  have hinv : (m : ℝ)⁻¹ ≤ (64 : ℝ)⁻¹ := by
    exact (inv_le_inv₀ hmRpos (by norm_num : (0 : ℝ) < 64)).2 hmR
  unfold smoothingEpsilon
  calc
    (m : ℝ)⁻¹ ^ 2 ≤ (64 : ℝ)⁻¹ ^ 2 := by gcongr
    _ = (1 / 4096 : ℝ) := by norm_num

theorem smoothingEpsilon_le_one_third {m : ℕ} (hm : 64 ≤ m) :
    3 * smoothingEpsilon m ≤ (1 / 3 : ℝ) := by
  have h := smoothingEpsilon_le_one_div_4096 hm
  nlinarith

theorem translatedAtom_eq_explicit (u : ℂ) (m : ℕ) (theta : ℝ) :
    translatedAtom u m theta =
      u + Complex.ofReal (2 * smoothingEpsilon m) * Complex.I +
        Complex.ofReal (smoothingEpsilon m) *
          Complex.exp (Complex.I * Complex.ofReal theta) := by
  simp only [translatedAtom, translatedAtomCenter, circleMap]
  rw [mul_comm (Complex.ofReal theta) Complex.I]

/-- The v13 translated circle stays within `3 epsilon` of its original atom
(`v-analytic.tex:532-539`). -/
theorem translatedAtom_dist_le_threeEpsilon (u : ℂ) (m : ℕ) (theta : ℝ)
    (hm : 0 < m) :
    ‖translatedAtom u m theta - u‖ ≤ 3 * smoothingEpsilon m := by
  have hε : 0 < smoothingEpsilon m := smoothingEpsilon_pos hm
  have h2ε : 0 < 2 * smoothingEpsilon m := by positivity
  have hexp : ‖Complex.exp (Complex.I * Complex.ofReal theta)‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  have hdiff : translatedAtom u m theta - u =
      Complex.ofReal (2 * smoothingEpsilon m) * Complex.I +
        Complex.ofReal (smoothingEpsilon m) *
          Complex.exp (Complex.I * Complex.ofReal theta) := by
    rw [translatedAtom_eq_explicit]
    ring
  rw [hdiff]
  calc
    ‖Complex.ofReal (2 * smoothingEpsilon m) * Complex.I +
        Complex.ofReal (smoothingEpsilon m) *
          Complex.exp (Complex.I * Complex.ofReal theta)‖ ≤
      ‖Complex.ofReal (2 * smoothingEpsilon m) * Complex.I‖ +
        ‖Complex.ofReal (smoothingEpsilon m) *
          Complex.exp (Complex.I * Complex.ofReal theta)‖ := norm_add_le _ _
    _ = 2 * smoothingEpsilon m + smoothingEpsilon m := by
      simp [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos h2ε, abs_of_pos hε, hexp]
    _ = 3 * smoothingEpsilon m := by ring

/-- Points on a v13 smoothing circle remain in the stated complex tube
(`v-analytic.tex:550-552`). -/
theorem translatedAtom_norm_le_one_add_threeEpsilon {u : ℂ} (m : ℕ)
    (theta : ℝ) (hm : 0 < m) (hu : ‖u‖ ≤ 1) :
    ‖translatedAtom u m theta‖ ≤ 1 + 3 * smoothingEpsilon m := by
  calc
    ‖translatedAtom u m theta‖ =
        ‖(translatedAtom u m theta - u) + u‖ := by congr 1; ring
    _ ≤ ‖translatedAtom u m theta - u‖ + ‖u‖ := norm_add_le _ _
    _ ≤ 3 * smoothingEpsilon m + 1 :=
      add_le_add (translatedAtom_dist_le_threeEpsilon u m theta hm) hu
    _ = 1 + 3 * smoothingEpsilon m := by ring

/-- The v13 tube bound used to keep `q + uv` away from zero when `m >= 64`
(`v-analytic.tex:532-552`). -/
theorem translatedAtom_norm_le_one_add_three_div_4096 {u : ℂ} (m : ℕ)
    (theta : ℝ) (hm : 64 ≤ m) (hu : ‖u‖ ≤ 1) :
    ‖translatedAtom u m theta‖ ≤ 1 + (3 / 4096 : ℝ) := by
  have hmpos : 0 < m := by omega
  calc
    ‖translatedAtom u m theta‖ ≤ 1 + 3 * smoothingEpsilon m :=
      translatedAtom_norm_le_one_add_threeEpsilon m theta hmpos hu
    _ ≤ 1 + 3 * (1 / 4096 : ℝ) := by
      gcongr
      exact smoothingEpsilon_le_one_div_4096 hm
    _ = 1 + (3 / 4096 : ℝ) := by ring

/-- The v13 denominator does not vanish on the smoothed `m >= 64` tube
(`v-analytic.tex:550-552`). -/
theorem translatedDenominator_ne_zero {q : ℕ} (u v : ℂ) (m : ℕ)
    (theta phi : ℝ) (hq : 2 ≤ q) (hm : 64 ≤ m)
    (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) :
    (q : ℂ) + translatedAtom u m theta * translatedAtom v m phi ≠ 0 := by
  have hqR : 2 ≤ (q : ℝ) := by exact_mod_cast hq
  have hqnorm : 2 ≤ ‖(q : ℂ)‖ := by simpa using hqR
  have hsmall : (1 + (3 / 4096 : ℝ)) ^ 2 < 2 := by norm_num
  have hprod :
      ‖translatedAtom u m theta * translatedAtom v m phi‖ < 2 := by
    calc
      ‖translatedAtom u m theta * translatedAtom v m phi‖ ≤
          ‖translatedAtom u m theta‖ * ‖translatedAtom v m phi‖ := norm_mul_le _ _
      _ ≤ (1 + (3 / 4096 : ℝ)) * (1 + (3 / 4096 : ℝ)) := by
        gcongr
        · exact translatedAtom_norm_le_one_add_three_div_4096 m theta hm hu
        · exact translatedAtom_norm_le_one_add_three_div_4096 m phi hm hv
      _ < 2 := by nlinarith [hsmall]
  intro hzero
  have hqeq : (q : ℂ) = -(translatedAtom u m theta * translatedAtom v m phi) := by
    calc
      (q : ℂ) = (q : ℂ) +
          translatedAtom u m theta * translatedAtom v m phi -
          translatedAtom u m theta * translatedAtom v m phi := by ring
      _ = 0 - translatedAtom u m theta * translatedAtom v m phi := by rw [hzero]
      _ = -(translatedAtom u m theta * translatedAtom v m phi) := by ring
  have hqnorm' : ‖(q : ℂ)‖ < 2 := by
    rw [hqeq, norm_neg]
    exact hprod
  linarith

/-!
The next statement is the only analytic fact proved in this module.  It is
the generic circle-average theorem from the frozen 1/2 `Kit`, instantiated at
the translated centre.  The signed V proof still has to establish how these
circle averages enter its three-component energy.
-/

theorem translatedAtom_circleAverage (x u : ℂ) {m : ℕ} (hm : 0 < m) :
    (∫ theta in (0 : ℝ)..(2 * Real.pi),
        Real.log ‖x - translatedAtom u m theta‖) /
        (2 * Real.pi) =
      Real.log (max (smoothingEpsilon m)
        ‖x - translatedAtomCenter u m‖) := by
  simpa only [translatedAtom] using
    (ContourKit.intervalAverage_log_norm_sub_const_eq_log_max
      x (translatedAtomCenter u m) (smoothingEpsilon_pos hm))

/-! ### Explicit constants from the v13 transfer calculation -/

/-- The disk-density modulus coefficient `6 A + 2 M`, v13 `v-analytic.tex:498-503`.
-/
def potentialModulusCoefficient (A M : ℝ) : ℝ := 6 * A + 2 * M

/-- The three reference masses `(1,5/4,1)`, v13 `v-analytic.tex:10-12`. -/
def xMass : ℝ := 1
def vMass : ℝ := 5 / 4
def zMass : ℝ := 1

/-- `B_i = 6 A_i + 2 M_i`, v13 `v-analytic.tex:433-436`. -/
def densityTransferBudget (A M : ℝ) : ℝ := potentialModulusCoefficient A M

/-- `Sigma_q`, v13 `v-analytic.tex:435-437`. -/
def sigmaBudget (Ax Av Az : ℝ) : ℝ :=
  2 * densityTransferBudget Ax xMass +
    (7 / 2 : ℝ) * densityTransferBudget Av vMass +
    (13 / 4 : ℝ) * densityTransferBudget Az zMass

/-- The tube derivative coefficient `L_D`, v13 `v-analytic.tex:546-549`. -/
def denominatorLipschitz (q : ℕ) : ℝ :=
  (1 + 3 / 4096 : ℝ) /
    ((q : ℝ) - (1 + 3 / 4096 : ℝ) ^ 2)

/-- The cross-denominator cost `C_D = 8 L_D`, v13 `v-analytic.tex:546-557`. -/
def denominatorTransferCost (q : ℕ) : ℝ := 8 * denominatorLipschitz q

theorem denominatorLipschitz_pos {q : ℕ} (hq : 2 ≤ q) :
    0 < denominatorLipschitz q := by
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hden : 0 < (q : ℝ) - (1 + 3 / 4096 : ℝ) ^ 2 := by
    norm_num
    nlinarith
  unfold denominatorLipschitz
  exact div_pos (by norm_num) hden

theorem denominatorLipschitz_lt_101_100 {q : ℕ} (hq : 2 ≤ q) :
    denominatorLipschitz q < (101 / 100 : ℝ) := by
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hden : 0 < (q : ℝ) - (1 + 3 / 4096 : ℝ) ^ 2 := by
    norm_num
    nlinarith
  apply (div_lt_iff₀ hden).2
  norm_num [denominatorLipschitz]
  nlinarith

theorem denominatorTransferCost_lt_808_100 {q : ℕ} (hq : 2 ≤ q) :
    denominatorTransferCost q < (808 / 100 : ℝ) := by
  have h := denominatorLipschitz_lt_101_100 hq
  unfold denominatorTransferCost
  nlinarith

/-! ### The conditional certificate -/

/-!
The multiplicative S0 target is kept separate from the logarithmic consumer.
It is the bound used in v13 `v-analytic.tex:106-123,522-530` and remains
meaningful at a zero determinant; the later logarithmic statements carry the
explicit nonvanishing field below.
-/

/-- The integer exponent `3 m^2 / 2 - m` in the S0 magnitude estimate. -/
def s0Exponent (m : ℕ) : ℕ := 3 * m ^ 2 / 2 - m

/-- The right hand side of the multiplicative S0 estimate. -/
def s0MagnitudeRhs (q m L : ℕ) (Tq phiMax : ℝ) : ℝ :=
  ((q : ℝ) ^ s0Exponent m /
      (((Nat.factorial m : ℕ) : ℝ) ^ 2 * (Nat.factorial L : ℝ))) *
    Tq ^ m * |phiMax|

/-- The exact multiplicative S0 obligation for the v13 determinant value. -/
def s0MultiplicativeBound (q m L : ℕ) (G : ℂ) (Tq phiMax : ℝ) : Prop :=
  ‖G‖ ≤ s0MagnitudeRhs q m L Tq phiMax

/-- S0 data, including the nonvanishing input needed by any logarithmic form. -/
structure S0MultiplicativeCertificate (q m L : ℕ) where
  G : ℂ
  G_ne_zero : G ≠ 0
  Tq : ℝ
  Tq_nonneg : 0 ≤ Tq
  phiMax : ℝ
  magnitude_bound : s0MultiplicativeBound q m L G Tq phiMax

/--
The unresolved analytic bridge for one fixed signed base.  This is the
pre-final estimate from `v-analytic.tex:591-610`, before the logarithmic
coefficient and constant absorption in `:612-627`.  It keeps the diagonal
term, reference-potential transfer term, denominator and endpoint costs, and
path linear term visible.  Proving this field requires the v13 smoothing,
energy, and integral estimates; this file does not assume the final bound.
-/
structure AllMSmoothingCertificate (g : ℝ) where
  /-- The actual v13 determinant/configuration value whose logarithm is `g`.
  This prevents Lean's `Real.log 0 = 0` convention from silently replacing
  the paper's zero/nonzero split (`v-analytic.tex:522-530`). -/
  G : ℂ
  G_ne_zero : G ≠ 0
  g_eq_log_norm : g = Real.log ‖G‖
  q : ℕ
  m : ℕ
  q_ge_two : 2 ≤ q
  q_le_seven : q ≤ 7
  m_eq_four_n : ∃ n : ℕ, m = 4 * n
  m_ge_64 : 64 ≤ m
  alpha : ℝ
  tau : ℝ
  sigma : ℝ
  alpha_gt_tau : tau < alpha
  sigma_nonneg : 0 ≤ sigma
  sigma_eq_budget : ∃ Ax Av Az : ℝ,
    0 ≤ Ax ∧ 0 ≤ Av ∧ 0 ≤ Az ∧ sigma = sigmaBudget Ax Av Az
  /-- The actual analytic obligation supplied by the v13 smoothing proof. -/
  prebound :
    g ≤ -alpha * (m : ℝ) ^ 2 +
      (13 / 2 : ℝ) * (m : ℝ) * Real.log (m : ℝ) +
      3 * sigma * (1 + Real.log ((m : ℝ) ^ 2 / 3)) +
      (2 * denominatorTransferCost q + 7 + 130) + (m : ℝ)

theorem allMSmoothingCertificate_m_pos
    {g : ℝ} (c : AllMSmoothingCertificate g) : 0 < (c.m : ℝ) := by
  have hm64 : (64 : ℕ) ≤ c.m := c.m_ge_64
  have hm : (0 : ℕ) < c.m := by omega
  exact_mod_cast hm

theorem allMSmoothingCertificate_log_m_pos
    {g : ℝ} (c : AllMSmoothingCertificate g) : 0 < Real.log (c.m : ℝ) := by
  have hm : (1 : ℝ) < (c.m : ℝ) := by
    have hm64 : (64 : ℕ) ≤ c.m := c.m_ge_64
    have hmNat : 1 < c.m := by omega
    exact_mod_cast hmNat
  exact Real.log_pos hm

theorem allMSmoothingCertificate_m_log_m_nonneg
    {g : ℝ} (c : AllMSmoothingCertificate g) :
    0 ≤ (c.m : ℝ) * Real.log (c.m : ℝ) := by
  exact (le_of_lt (mul_pos (allMSmoothingCertificate_m_pos c)
    (allMSmoothingCertificate_log_m_pos c)))

theorem allMSmoothingCertificate_modulus_log_le
    {g : ℝ} (c : AllMSmoothingCertificate g) :
    1 + Real.log ((c.m : ℝ) ^ 2 / 3) ≤
      (c.m : ℝ) * Real.log (c.m : ℝ) := by
  have hm : (64 : ℝ) ≤ (c.m : ℝ) := by exact_mod_cast c.m_ge_64
  have hmpos : 0 < (c.m : ℝ) := allMSmoothingCertificate_m_pos c
  have hlogmpos : 0 < Real.log (c.m : ℝ) :=
    allMSmoothingCertificate_log_m_pos c
  have hlog3 : Real.log (3 : ℝ) ≤ Real.log (c.m : ℝ) := by
    apply Real.log_le_log (by norm_num)
    have hm3 : (3 : ℝ) ≤ (c.m : ℝ) := by nlinarith [hm]
    exact hm3
  have hprod : (64 : ℝ) * Real.log (c.m : ℝ) ≤
      (c.m : ℝ) * Real.log (c.m : ℝ) := by
    exact mul_le_mul_of_nonneg_right hm (le_of_lt hlogmpos)
  rw [Real.log_div (by positivity) (by norm_num)]
  rw [Real.log_pow]
  norm_num
  have hlogm_ge_one : (1 : ℝ) ≤ Real.log (c.m : ℝ) := by
    have hlog64 : Real.log (64 : ℝ) = 6 * Real.log 2 := by
      rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]
      norm_num
    have hlog2 := Real.log_two_gt_d9
    have hlog64_ge : (4 : ℝ) ≤ Real.log (64 : ℝ) := by
      rw [hlog64]
      nlinarith
    have hlogmono := Real.log_le_log (by norm_num : (0 : ℝ) < 64) hm
    linarith
  have hlog3_nonneg : 0 ≤ Real.log (3 : ℝ) :=
    le_of_lt (Real.log_pos (by norm_num))
  nlinarith [hprod, hlogm_ge_one, hlog3_nonneg]

theorem allMSmoothingCertificate_constant_lt_200
    {g : ℝ} (c : AllMSmoothingCertificate g) :
    2 * denominatorTransferCost c.q + 7 + 130 < 200 := by
  have hcost := denominatorTransferCost_lt_808_100 c.q_ge_two
  nlinarith

theorem allMSmoothingCertificate_m_log_m_ge_200
    {g : ℝ} (c : AllMSmoothingCertificate g) :
    200 ≤ (c.m : ℝ) * Real.log (c.m : ℝ) := by
  have hm : (64 : ℝ) ≤ (c.m : ℝ) := by exact_mod_cast c.m_ge_64
  have hlog : Real.log (64 : ℝ) ≤ Real.log (c.m : ℝ) := by
    apply Real.log_le_log (by norm_num)
    exact hm
  have h64 : (200 : ℝ) ≤ 64 * Real.log (64 : ℝ) := by
    have hlog64 : Real.log (64 : ℝ) = 6 * Real.log 2 := by
      rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]
      norm_num
    have hlog2 := Real.log_two_gt_d9
    rw [hlog64]
    nlinarith
  have hmpos : 0 ≤ (c.m : ℝ) := le_of_lt (allMSmoothingCertificate_m_pos c)
  have hlognonneg : 0 ≤ Real.log (64 : ℝ) := Real.log_nonneg (by norm_num)
  nlinarith

theorem allMSmoothingCertificate_m_le_quarter_m_log_m
    {g : ℝ} (c : AllMSmoothingCertificate g) :
    (c.m : ℝ) ≤ (1 / 4 : ℝ) * (c.m : ℝ) * Real.log (c.m : ℝ) := by
  have hmpos := allMSmoothingCertificate_m_pos c
  have hlog : (4 : ℝ) ≤ Real.log (c.m : ℝ) := by
    have hm : (64 : ℝ) ≤ (c.m : ℝ) := by exact_mod_cast c.m_ge_64
    have := Real.log_le_log (by norm_num : (0 : ℝ) < 64) hm
    have hlog64 : Real.log (64 : ℝ) = 6 * Real.log 2 := by
      rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]
      norm_num
    have hlog2 := Real.log_two_gt_d9
    have h64 : (4 : ℝ) ≤ Real.log (64 : ℝ) := by
      rw [hlog64]
      nlinarith
    linarith
  nlinarith

/-- The coefficient comparison in v13 `v-analytic.tex:618-627`. -/
theorem allMSmoothingCertificate_coefficient_le
    {g : ℝ} (c : AllMSmoothingCertificate g) :
    ((13 / 2 : ℝ) + 3 * c.sigma + 1 + 1 / 4) ≤ 10 + 3 * c.sigma := by
  ring_nf
  norm_num

/--
Conditional all-`m` coefficient comparison for the explicit certificate
fields above; no V reference table is silently imported from the 1/2 route.

The algebraic theorem is abstract in `g`.  The current producer bridge
instantiates `g` with the logarithm of the norm of one pointwise
configuration integrand `Phi_q`.  This is not by itself a bound for the
determinant `G_m`; that requires the separate contour integral representation
and its norm estimate.
-/
theorem all_m_log_bound_of_certificate
    {g : ℝ} (c : AllMSmoothingCertificate g) :
    g ≤ -c.alpha * (c.m : ℝ) ^ 2 +
      (10 + 3 * c.sigma) * (c.m : ℝ) * Real.log (c.m : ℝ) := by
  have hraw := c.prebound
  have hmod := allMSmoothingCertificate_modulus_log_le c
  have hcost := allMSmoothingCertificate_constant_lt_200 c
  have h200 := allMSmoothingCertificate_m_log_m_ge_200 c
  have hlinear := allMSmoothingCertificate_m_le_quarter_m_log_m c
  have hmlog := allMSmoothingCertificate_m_log_m_nonneg c
  have hsigma := c.sigma_nonneg
  have hsigmaTerm :
      3 * c.sigma *
          (1 + Real.log ((c.m : ℝ) ^ 2 / 3)) ≤
        3 * c.sigma * (c.m : ℝ) * Real.log (c.m : ℝ) := by
    have hmul : 0 ≤ 3 * c.sigma := by positivity
    simpa [mul_assoc] using mul_le_mul_of_nonneg_left hmod hmul
  have hconst :
      (2 * denominatorTransferCost c.q + 7 + 130) + (c.m : ℝ) ≤
        200 + (1 / 4 : ℝ) * (c.m : ℝ) * Real.log (c.m : ℝ) := by
    have h1 : 2 * denominatorTransferCost c.q + 7 + 130 ≤ 200 := le_of_lt hcost
    linarith
  nlinarith [hraw, hsigmaTerm, hconst, hlinear,
    allMSmoothingCertificate_coefficient_le c]

end B3

end

end Li2Lean

#print axioms Li2Lean.B3.translatedAtom_circleAverage
#print axioms Li2Lean.B3.all_m_log_bound_of_certificate
