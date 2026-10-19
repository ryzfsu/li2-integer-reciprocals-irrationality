/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B4.NegativeTailRate
import Li2Lean.B4.DenominatorRate

namespace Li2Lean.B4

open Filter Topology

noncomputable section

/-!
Elementary real-axis estimates for the negative part of the v13 tail.
The beta-kernel statements implement `hp-tail.tex:200-220`; the tilted
coefficient rate and assembled exponential factor implement `:222-256` and
`:411-430`. The fixed-base parameter bridge is the `z = 1/a` substitution
used in `:200-220` and `:419-476`.

The denominator limit is reused through `Li2Lean.B4.DenominatorRate`; that
module in turn reuses the frozen 1/2 `Li2Lean.Kit.PNTAdapter` and
`Li2Lean.P0.IntegerizationBottom` interfaces through B4 `Integerization`.
The scalar cubic and beta-kernel inequalities need no 1/2 proof module.

For `q = 11` the uniform `4/27` kernel certificate below is valid, but its
combined rate with the negative triangle coefficient bound is not below one.
The `q = 11` decay rate needs the sharper AM-GM certificate recorded in the
the proof plan; the endpoint AM-GM statement is proved below.
-/

/-- The positive real magnitude of a negative integer base. -/
def hpNegativeBaseQ (a : ℤ) : ℝ := -(a : ℝ)

/-- The v13 argument `z = 1/a`, written as `-1/q` for a negative base. -/
def hpNegativeBaseZ (a : ℤ) : ℝ := -(1 / hpNegativeBaseQ a)

/-- Every integer base `a <= -11` gives a real parameter `q >= 11`.
This is the base substitution in v13 `hp-tail.tex:200-220,419-476`. -/
theorem hpNegativeBaseQ_ge_eleven {a : ℤ} (ha : a ≤ -11) :
    (11 : ℝ) ≤ hpNegativeBaseQ a := by
  have ha' : (a : ℝ) ≤ -11 := by exact_mod_cast ha
  dsimp [hpNegativeBaseQ]
  linarith

/-- The `q` parameter is positive for all bases in v13's negative range. -/
theorem hpNegativeBaseQ_pos {a : ℤ} (ha : a ≤ -11) :
    0 < hpNegativeBaseQ a := by
  have hq := hpNegativeBaseQ_ge_eleven ha
  exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 11) hq

/-- The negative argument is nonpositive. -/
theorem hpNegativeBaseZ_nonpos {a : ℤ} (ha : a ≤ -11) :
    hpNegativeBaseZ a ≤ 0 := by
  have hq := hpNegativeBaseQ_pos ha
  dsimp [hpNegativeBaseZ]
  exact neg_nonpos.mpr (by positivity)

/-- The negative argument lies strictly inside the unit interval. -/
theorem hpNegativeBaseZ_abs_lt_one {a : ℤ} (ha : a ≤ -11) :
    |hpNegativeBaseZ a| < 1 := by
  have hq := hpNegativeBaseQ_ge_eleven ha
  have hqpos := hpNegativeBaseQ_pos ha
  rw [hpNegativeBaseZ, abs_neg, abs_div, abs_of_pos hqpos]
  simp only [abs_one]
  rw [div_lt_iff₀ hqpos]
  norm_num
  linarith

/-- The substitution agrees with the paper's original `1/a`. -/
theorem hpNegativeBaseZ_eq_inv {a : ℤ} (ha : a ≤ -11) :
    hpNegativeBaseZ a = (a : ℝ)⁻¹ := by
  have ha' : (a : ℝ) ≤ -11 := by exact_mod_cast ha
  have ha0 : (a : ℝ) ≠ 0 := by linarith
  unfold hpNegativeBaseZ hpNegativeBaseQ
  rw [one_div]
  field_simp [ha0]

/-- The cubic maximum certificate from v13 `hp-tail.tex:205-216`. -/
theorem hp_negative_cubic_four27 {s : ℝ} (hs : 0 ≤ s) :
    s ^ 2 * (1 - s) ≤ (4 / 27 : ℝ) := by
  have hfactor : (4 / 27 : ℝ) - s ^ 2 * (1 - s) =
      (s - 2 / 3) ^ 2 * (s + 1 / 3) := by ring
  have hnonneg : 0 ≤ (s - 2 / 3) ^ 2 * (s + 1 / 3) :=
    mul_nonneg (sq_nonneg _) (by linarith)
  linarith

/-- One-variable negative-axis factor bound used in v13's real beta estimate,
`hp-tail.tex:200-220`. -/
theorem hp_negative_factor_four27 {s z : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (hz : z ≤ 0) :
    s ^ 2 * (1 - s) ≤ (4 / 27 : ℝ) * (1 - z * s ^ 2) := by
  have hcubic := hp_negative_cubic_four27 hs.1
  have hden : 1 ≤ 1 - z * s ^ 2 := by
    have hzs : z * s ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hz (sq_nonneg s)
    linarith
  calc
    s ^ 2 * (1 - s) ≤ (4 / 27 : ℝ) := hcubic
    _ ≤ (4 / 27 : ℝ) * (1 - z * s ^ 2) := by nlinarith

/-- The double beta-kernel numerator bound for every real `z <= 0`,
v13 `hp-tail.tex:200-220`. This is the exact `4/27` certificate consumed by
the negative-tail beta integral. -/
theorem hp_negative_bracket_four27 {z : ℝ} (hz : z ≤ 0) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ u ∈ Set.Icc (0 : ℝ) 1,
      t ^ 2 * u ^ 2 * ((1 - t) * (1 - u)) ≤
        ((4 / 27 : ℝ) ^ 2) * (1 - z * t * u) ^ 2 := by
  intro t ht u hu
  have hft := hp_negative_cubic_four27 ht.1
  have hfu := hp_negative_cubic_four27 hu.1
  have hft0 : 0 ≤ t ^ 2 * (1 - t) :=
    mul_nonneg (sq_nonneg _) (sub_nonneg.mpr ht.2)
  have hfu0 : 0 ≤ u ^ 2 * (1 - u) :=
    mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hu.2)
  have hM : 0 ≤ (4 / 27 : ℝ) := by norm_num
  have hprod :
      (t ^ 2 * (1 - t)) * (u ^ 2 * (1 - u)) ≤ (4 / 27 : ℝ) ^ 2 := by
    calc
      (t ^ 2 * (1 - t)) * (u ^ 2 * (1 - u)) ≤
          (4 / 27 : ℝ) * (u ^ 2 * (1 - u)) :=
        mul_le_mul_of_nonneg_right hft hfu0
      _ ≤ (4 / 27 : ℝ) * (4 / 27 : ℝ) :=
        mul_le_mul_of_nonneg_left hfu hM
      _ = (4 / 27 : ℝ) ^ 2 := by ring
  have htu : 0 ≤ t * u := mul_nonneg ht.1 hu.1
  have hden : 1 ≤ 1 - z * t * u := by
    have hztu : z * (t * u) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hz htu
    nlinarith
  have hdenSq : 1 ≤ (1 - z * t * u) ^ 2 := by nlinarith
  calc
    t ^ 2 * u ^ 2 * ((1 - t) * (1 - u)) =
        (t ^ 2 * (1 - t)) * (u ^ 2 * (1 - u)) := by ring
    _ ≤ (4 / 27 : ℝ) ^ 2 := hprod
    _ ≤ ((4 / 27 : ℝ) ^ 2) * (1 - z * t * u) ^ 2 := by
      have hM2 : 0 ≤ (4 / 27 : ℝ) ^ 2 := sq_nonneg _
      nlinarith [hdenSq]

/-- Divided form of the same kernel bound; the denominator is positive on
the negative real axis. -/
theorem hp_negative_bracket_div_four27 {z t u : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (hu : u ∈ Set.Icc (0 : ℝ) 1)
    (hz : z ≤ 0) :
    t ^ 2 * u ^ 2 * ((1 - t) * (1 - u)) / (1 - z * t * u) ^ 2 ≤
      (4 / 27 : ℝ) ^ 2 := by
  have hden : 0 < (1 - z * t * u) ^ 2 := by
    have htu : 0 ≤ t * u := mul_nonneg ht.1 hu.1
    have hztu : z * (t * u) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hz htu
    have hpos : 0 < 1 - z * t * u := by nlinarith
    exact sq_pos_of_pos hpos
  apply (div_le_iff₀ hden).2
  exact hp_negative_bracket_four27 hz t ht u hu

/-! The q=11 endpoint uses the AM-GM cancellation from v13 rather than the
uniform 4/27 bound. This is still a real beta estimate (`:205-220`), not a
contour argument. -/

/-- Cubic SOS certificate in the form used by the beta-kernel maximization in
v13 `hp-tail.tex:205-216`. -/
theorem hp_negative_cubic_certificate {s M z : ℝ} (hs : 0 ≤ s)
    (hMz : 0 < 1 + M * z)
    (hcert : 4 * (1 + M * z) ^ 3 ≤ 27 * M) :
    s ^ 2 * (1 - s) ≤ M * (1 - z * s ^ 2) := by
  let α : ℝ := 2 * (1 + M * z) / 3
  have hα : 0 ≤ α := by dsimp [α]; positivity
  have hsα : 0 ≤ s + α / 2 := by positivity
  have hsos : 0 ≤ (s - α) ^ 2 * (s + α / 2) :=
    mul_nonneg (sq_nonneg _) hsα
  have hrem : 0 ≤ M - α ^ 3 / 2 := by
    dsimp [α]
    nlinarith
  have hid : M * (1 - z * s ^ 2) - s ^ 2 * (1 - s) =
      (s - α) ^ 2 * (s + α / 2) + (M - α ^ 3 / 2) := by
    dsimp [α]
    ring
  linarith

/-- AM-GM cancellation for the two beta variables, as used in v13
`hp-tail.tex:205-208`. -/
theorem hp_sqrt_amgm {t u : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    (1 - t) * (1 - u) ≤
      (1 - Real.sqrt (t * u)) ^ 2 := by
  have htu0 : 0 ≤ t * u := mul_nonneg ht.1 hu.1
  let s : ℝ := Real.sqrt (t * u)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs_sq : s ^ 2 = t * u := by
    dsimp [s]
    exact Real.sq_sqrt htu0
  have htu_le : t * u ≤ 1 := by
    have h := mul_le_mul ht.2 hu.2 hu.1 (by norm_num : (0 : ℝ) ≤ 1)
    simpa using h
  have hs1 : s ≤ 1 := by
    dsimp [s]
    exact (Real.sqrt_le_iff).2 ⟨by norm_num, by nlinarith [htu_le]⟩
  have hsum : 2 * s ≤ t + u := by
    have hsq : (2 * s) ^ 2 ≤ (t + u) ^ 2 := by
      rw [show (2 * s) ^ 2 = 4 * s ^ 2 by ring, hs_sq]
      nlinarith [sq_nonneg (t - u)]
    nlinarith [hs0, hs1, ht.1, hu.1]
  dsimp [s] at hs_sq hsum hs1 ⊢
  nlinarith [hsum, hs_sq]

/-- The rational q=11 certificate from v13's endpoint table
(`hp-tail.tex:449-460`, used in the beta estimate `:205-220`). -/
def hpNegativeQ11M : ℝ := (65804 / 100000 : ℝ) ^ 3 / 2

theorem hpNegativeQ11M_pos : 0 < hpNegativeQ11M := by
  norm_num [hpNegativeQ11M]

theorem hpNegativeQ11_cubic {s : ℝ} (hs : 0 ≤ s) :
    s ^ 2 * (1 - s) ≤ hpNegativeQ11M * (1 + s ^ 2 / 11) := by
  have hcert : 4 * (1 + hpNegativeQ11M * (-(1 / 11 : ℝ))) ^ 3 ≤
      27 * hpNegativeQ11M := by
    norm_num [hpNegativeQ11M]
  have hMz : 0 < 1 + hpNegativeQ11M * (-(1 / 11 : ℝ)) := by
    norm_num [hpNegativeQ11M]
  have hmain := hp_negative_cubic_certificate hs hMz hcert
  convert hmain using 1 <;> ring

/-- q=11's two-variable bracket bound after the AM-GM cancellation. -/
theorem hp_negative_bracket_q11 {t u : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    t ^ 2 * u ^ 2 * ((1 - t) * (1 - u)) ≤
      hpNegativeQ11M ^ 2 * (1 + t * u / 11) ^ 2 := by
  have htu0 : 0 ≤ t * u := mul_nonneg ht.1 hu.1
  let s : ℝ := Real.sqrt (t * u)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs_sq : s ^ 2 = t * u := by
    dsimp [s]
    exact Real.sq_sqrt htu0
  have htu_le : t * u ≤ 1 := by
    have h := mul_le_mul ht.2 hu.2 hu.1 (by norm_num : (0 : ℝ) ≤ 1)
    simpa using h
  have hs1 : s ≤ 1 := by
    dsimp [s]
    exact (Real.sqrt_le_iff).2 ⟨by norm_num, by nlinarith [htu_le]⟩
  have hamgm := hp_sqrt_amgm ht hu
  have hcubic := hpNegativeQ11_cubic hs0
  have hleft0 : 0 ≤ s ^ 2 * (1 - s) :=
    mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hs1)
  have hright0 : 0 ≤ hpNegativeQ11M * (1 + s ^ 2 / 11) := by
    have hinner : 0 ≤ 1 + s ^ 2 / 11 := by positivity
    exact mul_nonneg (le_of_lt hpNegativeQ11M_pos) hinner
  have hsquare : (s ^ 2 * (1 - s)) ^ 2 ≤
      (hpNegativeQ11M * (1 + s ^ 2 / 11)) ^ 2 :=
    (sq_le_sq₀ hleft0 hright0).2 hcubic
  have hnum : t ^ 2 * u ^ 2 * ((1 - t) * (1 - u)) ≤
      (s ^ 2 * (1 - s)) ^ 2 := by
    calc
      t ^ 2 * u ^ 2 * ((1 - t) * (1 - u)) ≤
          t ^ 2 * u ^ 2 * (1 - s) ^ 2 := by
        exact mul_le_mul_of_nonneg_left hamgm (by positivity)
      _ = (s ^ 2 * (1 - s)) ^ 2 := by
        rw [hs_sq]
        ring
  calc
    t ^ 2 * u ^ 2 * ((1 - t) * (1 - u)) ≤
        (s ^ 2 * (1 - s)) ^ 2 := hnum
    _ ≤ (hpNegativeQ11M * (1 + s ^ 2 / 11)) ^ 2 := hsquare
    _ = hpNegativeQ11M ^ 2 * (1 + t * u / 11) ^ 2 := by
      rw [hs_sq]
      ring

/-- Divided q=11 kernel form for the beta integral. -/
theorem hp_negative_bracket_div_q11 {t u : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    t ^ 2 * u ^ 2 * ((1 - t) * (1 - u)) /
        (1 + t * u / 11) ^ 2 ≤ hpNegativeQ11M ^ 2 := by
  have hden : 0 < (1 + t * u / 11) ^ 2 := by
    have htu0 : 0 ≤ t * u := mul_nonneg ht.1 hu.1
    have hpos : 0 < 1 + t * u / 11 := by positivity
    exact sq_pos_of_pos hpos
  apply (div_le_iff₀ hden).2
  simpa [div_pow] using hp_negative_bracket_q11 ht hu

def hpNegativeQ11CoeffRate : ℝ := ((3 - (14180 / 100000 : ℝ)) /
  (1 - (14180 / 100000 : ℝ))) ^ 3

def hpNegativeQ11RateCore : ℝ :=
  (Real.exp 4 / (16 * 11)) * hpNegativeQ11CoeffRate *
    (4 * hpNegativeQ11M ^ 2)

theorem hpNegativeQ11CoeffRate_lt_38 : hpNegativeQ11CoeffRate < 38 := by
  norm_num [hpNegativeQ11CoeffRate]

theorem hpNegativeQ11RateCore_lt_one : hpNegativeQ11RateCore < 1 := by
  have hdiv : Real.exp 4 / (16 * 11 : ℝ) < 56 / (16 * 11 : ℝ) := by
    gcongr
    exact hp_exp_four_lt_56
  have hK : hpNegativeQ11CoeffRate < 38 := hpNegativeQ11CoeffRate_lt_38
  have hK0 : 0 < hpNegativeQ11CoeffRate := by
    norm_num [hpNegativeQ11CoeffRate]
  have hfirst :
      Real.exp 4 / (16 * 11 : ℝ) * hpNegativeQ11CoeffRate <
        (56 / (16 * 11 : ℝ)) * 38 := by
    calc
      Real.exp 4 / (16 * 11 : ℝ) * hpNegativeQ11CoeffRate <
          (56 / (16 * 11 : ℝ)) * hpNegativeQ11CoeffRate :=
        mul_lt_mul_of_pos_right hdiv hK0
      _ < (56 / (16 * 11 : ℝ)) * 38 :=
        mul_lt_mul_of_pos_left hK (by norm_num)
  have hM : 0 < 4 * hpNegativeQ11M ^ 2 := by
    norm_num [hpNegativeQ11M]
  have hsecond :
      (Real.exp 4 / (16 * 11 : ℝ) * hpNegativeQ11CoeffRate) *
          (4 * hpNegativeQ11M ^ 2) <
        ((56 / (16 * 11 : ℝ)) * 38) * (4 * hpNegativeQ11M ^ 2) :=
    mul_lt_mul_of_pos_right hfirst hM
  dsimp [hpNegativeQ11RateCore]
  calc
    Real.exp 4 / (16 * 11) * hpNegativeQ11CoeffRate *
          (4 * hpNegativeQ11M ^ 2) <
        ((56 / (16 * 11 : ℝ)) * 38) * (4 * hpNegativeQ11M ^ 2) := hsecond
    _ < 1 := by norm_num [hpNegativeQ11M]

/-- Tilted binomial exponential constant from the v13 positive-tail estimate,
used by the negative triangle bound in `hp-tail.tex:222-256`. -/
def hpNegativeTailTilt : ℝ := 13683 / 100000

/-- The coefficient growth constant paired with the `q >= 12` triangle bound. -/
def hpNegativeTailCoeffRate : ℝ :=
  ((3 - hpNegativeTailTilt) / (1 - hpNegativeTailTilt)) ^ 3

theorem hpNegativeTailCoeffRate_lt_37 : hpNegativeTailCoeffRate < 37 := by
  norm_num [hpNegativeTailCoeffRate, hpNegativeTailTilt]

/-- The exponential part of the v13 assembled negative-tail rate, using
`4 M^2 = 64/729` and the denominator limit `exp(4)/16`, as in
`hp-tail.tex:411-430`. The strict cutoff is available for `q >= 12`. -/
def hpNegativeTailRateCore (q : ℝ) : ℝ :=
  (Real.exp 4 / (16 * q)) * hpNegativeTailCoeffRate *
    (4 * (4 / 27 : ℝ) ^ 2)

theorem hpNegativeTailRateCore_lt_one {q : ℝ} (hq : 12 ≤ q) :
    hpNegativeTailRateCore q < 1 := by
  have hqden : (192 : ℝ) ≤ 16 * q := by nlinarith
  have hqpos : 0 < 16 * q := by positivity
  have hdiv : Real.exp 4 / (16 * q) ≤ (56 : ℝ) / 192 := by
    apply (div_le_div_iff₀ hqpos (by norm_num : (0 : ℝ) < 192)).2
    nlinarith [hp_exp_four_lt_56]
  have hK : hpNegativeTailCoeffRate ≤ 37 := le_of_lt hpNegativeTailCoeffRate_lt_37
  have hK0 : 0 ≤ hpNegativeTailCoeffRate := by
    norm_num [hpNegativeTailCoeffRate, hpNegativeTailTilt]
  have hA : 0 ≤ 4 * (4 / 27 : ℝ) ^ 2 := by norm_num
  calc
    hpNegativeTailRateCore q =
        (Real.exp 4 / (16 * q) * hpNegativeTailCoeffRate) *
          (4 * (4 / 27 : ℝ) ^ 2) := by rfl
    _ ≤ ((56 : ℝ) / 192 * 37) * (4 * (4 / 27 : ℝ) ^ 2) := by
      apply mul_le_mul_of_nonneg_right _ hA
      exact mul_le_mul hdiv hK hK0 (by norm_num)
    _ < 1 := by norm_num

/-- Integer negative bases split into the endpoint `a = -11` and the
uniform range `a <= -12`; this is the case split used by the v13 endpoint
checks in `hp-tail.tex:449-476`. -/
theorem hpNegativeBaseRate_cases {a : ℤ} (ha : a ≤ -11) :
    (a = -11 ∧ hpNegativeQ11RateCore < 1) ∨
      (12 ≤ hpNegativeBaseQ a ∧
        hpNegativeTailRateCore (hpNegativeBaseQ a) < 1) := by
  by_cases h11 : a = -11
  · exact Or.inl ⟨h11, hpNegativeQ11RateCore_lt_one⟩
  · right
    have ha12 : a ≤ -12 := by omega
    have hq12 : (12 : ℝ) ≤ hpNegativeBaseQ a := by
      have ha12' : (a : ℝ) ≤ -12 := by exact_mod_cast ha12
      dsimp [hpNegativeBaseQ]
      linarith
    exact ⟨hq12, hpNegativeTailRateCore_lt_one hq12⟩

/-- The eventual denominator slack used in v13's fixed-base rate argument,
from the existing PNT-backed interface for `log d_N / N` (`:411-418`). -/
theorem hp_log_denominator_upper_one_thousandth :
    ∀ᶠ N : ℕ in atTop,
      Real.log (hpDenominator N : ℝ) ≤ (1 + (1 / 1000 : ℝ)) * N := by
  have hlimit := hp_log_denominator_rate
  have heventually : ∀ᶠ N : ℕ in atTop,
      Real.log (hpDenominator N : ℝ) / (N : ℝ) <
        (1 + (1 / 1000 : ℝ)) := by
    have hopen : Set.Iio (1 + (1 / 1000 : ℝ)) ∈ 𝓝 (1 : ℝ) :=
      Iio_mem_nhds (by norm_num)
    have h := hlimit.eventually hopen
    filter_upwards [h] with N hN
    exact hN
  filter_upwards [heventually, eventually_gt_atTop (0 : ℕ)] with N hN hNpos
  have hNposR : 0 < (N : ℝ) := by exact_mod_cast hNpos
  have hmul := (div_lt_iff₀ hNposR).1 hN
  nlinarith

/-- The same PNT slack expressed with the exact `Nat.lcmUpto` denominator
used in the top-down tail interface, v13 `hp-tail.tex:411-418`. -/
theorem hp_lcmUpto_log_upper_one_thousandth :
    ∀ᶠ N : ℕ in atTop,
      Real.log (Nat.lcmUpto N : ℝ) ≤ (1 + (1 / 1000 : ℝ)) * N := by
  filter_upwards [hp_log_denominator_upper_one_thousandth] with N hN
  rw [← hpDenominator_eq_lcmUpto N]
  exact hN

end

end Li2Lean.B4
