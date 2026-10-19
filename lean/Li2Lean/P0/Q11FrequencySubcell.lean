/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.Q11FrequencyTerms
import Li2Lean.P0.Q11EndpointBridge
import Li2Lean.P0.Q11FrequencyLogLower
import Li2Lean.P0.Q11NuHiF
import Li2Lean.P0.CA.Frequency.Checker
import Li2Lean.P0.Q11FrequencyIntCert

open MeasureTheory Set

namespace Li2Lean.P0.Q11Data

noncomputable section

open Li2Lean.F_L8
open Li2Lean.P0.CA.Frequency
open Li2Lean.P0.ConfigContourReference
open Li2Lean.P0.ConfigContourTail
open Li2Lean.P0.CA.Contour.QI
open Li2Lean.P0.ActualReferenceQLogOutsideCheck

theorem q11ContourTailDerivative_nonneg_weighted {t : ℝ} (ht : leftClearance < t) :
    0 ≤ q11ContourTailDerivative t := by
  unfold q11ContourTailDerivative
  apply mul_nonneg (inv_nonneg.mpr (by positivity))
  apply intervalIntegral.integral_nonneg (by positivity)
  intro u _
  exact mul_nonneg (q11ContourDensity_nonneg u) (tailKernelDeriv_nonneg ht u)

theorem q11ContourPotential_neg_monotoneOn_weighted :
    MonotoneOn (fun s : ℝ => q11ContourPotential (-(s : ℂ))) (Set.Ici (1 / 2)) := by
  have hclear (x : ℝ) (hx : 1 / 2 ≤ x) : leftClearance < x := by
    unfold leftClearance
    linarith
  apply monotoneOn_of_deriv_nonneg (convex_Ici _)
  · intro x hx
    exact (q11_hasDerivAt_contourPotential_neg (hclear x hx)).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    exact (q11_hasDerivAt_contourPotential_neg
      (hclear x (le_of_lt hx))).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    rw [(q11_hasDerivAt_contourPotential_neg
      (hclear x (le_of_lt hx))).deriv]
    exact q11ContourTailDerivative_nonneg_weighted (hclear x (le_of_lt hx))

def q11FrequencyTermsIWeighted : List TermI := [
  ((1 : ℤ), 1, (5 : ℤ), 4), ((-1 : ℤ), 1, (1 : ℤ), 4),
  ((1 : ℤ), 1, (2 : ℤ), 1), ((-1 : ℤ), 1, (0 : ℤ), 1),
  ((-1 : ℤ), 1, (0 : ℤ), 1), ((1 : ℤ), 1, (-1 : ℤ), 2),
  ((-4669092505312 : ℤ), 3000000000000, (-1 : ℤ), 2),
  ((4669092505312 : ℤ), 3000000000000, (-3 : ℤ), 2),
  ((-1304157351620 : ℤ), 3000000000000, (-3 : ℤ), 2),
  ((1304157351620 : ℤ), 3000000000000, (-5 : ℤ), 2),
  ((-26750143068 : ℤ), 3000000000000, (-5 : ℤ), 2),
  ((26750143068 : ℤ), 3000000000000, (-7 : ℤ), 2),
  ((0 : ℤ), 3000000000000, (-7 : ℤ), 2),
  ((0 : ℤ), 3000000000000, (-9 : ℤ), 2),
  ((224 : ℤ), 3000000000000, (8 : ℤ), 32),
  ((-224 : ℤ), 3000000000000, (12 : ℤ), 32),
  ((0 : ℤ), 3000000000000, (12 : ℤ), 32),
  ((0 : ℤ), 3000000000000, (16 : ℤ), 32),
  ((861621250600 : ℤ), 3000000000000, (16 : ℤ), 32),
  ((-861621250600 : ℤ), 3000000000000, (20 : ℤ), 32),
  ((1655513076232 : ℤ), 3000000000000, (20 : ℤ), 32),
  ((-1655513076232 : ℤ), 3000000000000, (24 : ℤ), 32),
  ((2086833534800 : ℤ), 3000000000000, (24 : ℤ), 32),
  ((-2086833534800 : ℤ), 3000000000000, (28 : ℤ), 32),
  ((2573270448992 : ℤ), 3000000000000, (28 : ℤ), 32),
  ((-2573270448992 : ℤ), 3000000000000, (32 : ℤ), 32),
  ((2999999999968 : ℤ), 3000000000000, (32 : ℤ), 32),
  ((-2999999999968 : ℤ), 3000000000000, (36 : ℤ), 32),
  ((2999999999968 : ℤ), 3000000000000, (36 : ℤ), 32),
  ((-2999999999968 : ℤ), 3000000000000, (40 : ℤ), 32)]

theorem q11FrequencyTermsIWeighted_toQ :
    q11FrequencyTermsIWeighted.map TermI.toQ = q11FrequencyTerms :=
  termIListToQCheck_sound (by decide +kernel)

theorem q11FrequencyTermsIWeighted_pos :
    q11FrequencyTermsIWeighted.all TermI.pos = true := by
  decide +kernel

/-!
The row-specific checker keeps the exact cell upper endpoint in the Fourier
potential enclosure.  This is required by the q11 margin; the endpoint bound
at `81/10` is too coarse for the first active cell.
-/
def q11RowLowerRealWeightedTight (ln : ℤ) (ld : ℕ) (hn : ℤ) (hd : ℕ) : ℝ :=
  ((termsLowM ln ld hn hd q11FrequencyTermsIWeighted : ℤ) : ℝ) / twoE +
    (-1 / 2 - (l2hi : ℝ) / 2 +
      (ln : ℝ) / ld * (2397895272 / 1000000000 : ℝ) -
      (q11NuHiF ((hn : ℚ) / hd) : ℝ))

theorem q11RowLowerRealWeightedTight_le {ln hn : ℤ} {ld hd : ℕ}
    (hld : 0 < ld) (hhd : 0 < hd)
    (h0 : (1 / 2 : ℝ) ≤ (ln : ℝ) / ld)
    (hend : (hn : ℝ) / hd ≤ (81 / 10 : ℝ)) {x : ℝ}
    (hlo : (ln : ℝ) / ld ≤ x) (hhi : x ≤ (hn : ℝ) / hd) :
    q11RowLowerRealWeightedTight ln ld hn hd ≤ q11Wmu x := by
  have hldR : (0 : ℝ) < ld := by exact_mod_cast hld
  have hhdR : (0 : ℝ) < hd := by exact_mod_cast hhd
  have hxhalf : (1 / 2 : ℝ) ≤ x := h0.trans hlo
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hxhalf
  have hterms := termsLowM_le hld hhd hlo hhi q11FrequencyTermsIWeighted
    q11FrequencyTermsIWeighted_pos
  rw [q11FrequencyTermsIWeighted_toQ] at hterms
  have hhiQ : (1 / 2 : ℚ) ≤ (hn : ℚ) / hd := by
    have h1 : (((1 / 2 : ℚ)) : ℝ) ≤ (((hn : ℚ) / hd : ℚ) : ℝ) := by
      simp only [Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast]
      norm_num
      exact le_trans hxhalf hhi
    exact Rat.cast_le.mp h1
  have hhiR : (((hn : ℚ) / hd : ℚ) : ℝ) = (hn : ℝ) / hd := by
    simp only [Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast]
  have hmono := q11ContourPotential_neg_monotoneOn_weighted
    (show x ∈ Set.Ici (1 / 2) from hxhalf)
    (show ((hn : ℝ) / hd) ∈ Set.Ici (1 / 2) from
      le_trans hxhalf hhi) hhi
  have hnu := q11ContourPotential_neg_le_q11NuHiF hhiQ
  rw [hhiR] at hnu
  have hcont : q11ContourPotential (Complex.ofReal (-x)) ≤
      (q11NuHiF ((hn : ℚ) / hd) : ℝ) := by
    simpa [Complex.ofReal_neg, q11NuHiF] using hmono.trans hnu
  have hlin0 := q11_log_linear_lower_tight
  have hlin : x * (2397895272 / 1000000000 : ℝ) ≤
      x * (Real.log 2 + q11Lambda) :=
    mul_le_mul_of_nonneg_left (le_of_lt hlin0) (le_of_lt hxpos)
  have hl2 : Real.log 2 ≤ (l2hi : ℝ) := le_l2hi
  rw [q11Wmu_eq_frequencyTerms]
  unfold q11RowLowerRealWeightedTight
  linarith

set_option maxHeartbeats 2000000 in
theorem q11_first_frequency_subcell_weighted_tight :
    (27435768107 / 10000000000 : ℝ) ≤
      q11RowLowerRealWeightedTight 20480 40960 20481 40960 := by
  unfold q11RowLowerRealWeightedTight
  have hval : q11NuHiF (((20481 : ℤ) : ℚ) / ((40960 : ℕ) : ℚ)) =
      ((512378417897 : ℤ) : ℚ) / ((1099511627776 : ℕ) : ℚ) :=
    rat_eq_of_ratIntDenCheck (by decide +kernel)
  have hterms :
      termsLowM 20480 40960 20481 40960 q11FrequencyTermsIWeighted =
        3298921213997240590 := by decide +kernel
  rw [hterms]
  rw [hval]
  norm_num [twoE, l2hi]

set_option maxHeartbeats 2000000 in
theorem q11_second_frequency_subcell_weighted_tight :
    (27435768107 / 10000000000 : ℝ) ≤
      q11RowLowerRealWeightedTight 20481 40960 20482 40960 := by
  unfold q11RowLowerRealWeightedTight
  have hval : q11NuHiF (((20482 : ℤ) : ℚ) / ((40960 : ℕ) : ℚ)) =
      ((256191337997 : ℤ) : ℚ) / ((549755813888 : ℕ) : ℚ) :=
    rat_eq_of_ratIntDenCheck (by decide +kernel)
  have hterms :
      termsLowM 20481 40960 20482 40960 q11FrequencyTermsIWeighted =
        3299218769484177587 := by decide +kernel
  rw [hterms]
  rw [hval]
  norm_num [twoE, l2hi]

set_option maxHeartbeats 2000000 in
theorem q11_third_frequency_subcell_weighted_tight :
    (27435768107 / 10000000000 : ℝ) ≤
      q11RowLowerRealWeightedTight 20482 40960 20483 40960 := by
  unfold q11RowLowerRealWeightedTight
  have hval : q11NuHiF (((20483 : ℤ) : ℚ) / ((40960 : ℕ) : ℚ)) =
      ((256193467029 : ℤ) : ℚ) / ((549755813888 : ℕ) : ℚ) :=
    rat_eq_of_ratIntDenCheck (by decide +kernel)
  have hterms :
      termsLowM 20482 40960 20483 40960 q11FrequencyTermsIWeighted =
        3299480109056157354 := by decide +kernel
  rw [hterms]
  rw [hval]
  norm_num [twoE, l2hi]
set_option maxHeartbeats 2000000 in
theorem q11_fourth_frequency_subcell_weighted_tight :
    (27435768107 / 10000000000 : ℝ) ≤
      q11RowLowerRealWeightedTight 20483 40960 20484 40960 := by
  unfold q11RowLowerRealWeightedTight
  have hval : q11NuHiF (((20484 : ℤ) : ℚ) / ((40960 : ℕ) : ℚ)) =
      ((512391192087 : ℤ) : ℚ) / ((1099511627776 : ℕ) : ℚ) :=
    rat_eq_of_ratIntDenCheck (by decide +kernel)
  have hterms :
      termsLowM 20483 40960 20484 40960 q11FrequencyTermsIWeighted =
        3299728087112362583 := by decide +kernel
  rw [hterms]
  rw [hval]
  norm_num [twoE, l2hi]

set_option maxHeartbeats 2000000 in
theorem q11_fifth_frequency_subcell_weighted_tight :
    (27435768107 / 10000000000 : ℝ) ≤
      q11RowLowerRealWeightedTight 20484 40960 20485 40960 := by
  unfold q11RowLowerRealWeightedTight
  have hval : q11NuHiF (((20485 : ℤ) : ℚ) / ((40960 : ℕ) : ℚ)) =
      ((128098862519 : ℤ) : ℚ) / ((274877906944 : ℕ) : ℚ) :=
    rat_eq_of_ratIntDenCheck (by decide +kernel)
  have hterms :
      termsLowM 20484 40960 20485 40960 q11FrequencyTermsIWeighted =
        3299968287695872816 := by decide +kernel
  rw [hterms]
  rw [hval]
  norm_num [twoE, l2hi]

set_option maxHeartbeats 2000000 in
theorem q11_sixth_frequency_subcell_weighted_tight :
    (27435768107 / 10000000000 : ℝ) ≤
      q11RowLowerRealWeightedTight 20485 40960 20486 40960 := by
  unfold q11RowLowerRealWeightedTight
  have hval : q11NuHiF (((20486 : ℤ) : ℚ) / ((40960 : ℕ) : ℚ)) =
      ((4003122719 : ℤ) : ℚ) / ((8589934592 : ℕ) : ℚ) :=
    rat_eq_of_ratIntDenCheck (by decide +kernel)
  have hterms :
      termsLowM 20485 40960 20486 40960 q11FrequencyTermsIWeighted =
        3300203083139344598 := by decide +kernel
  rw [hterms]
  rw [hval]
  norm_num [twoE, l2hi]

set_option maxHeartbeats 2000000 in
theorem q11_seventh_frequency_subcell_weighted_tight :
    (27435768107 / 10000000000 : ℝ) ≤
      q11RowLowerRealWeightedTight 20486 40960 20487 40960 := by
  unfold q11RowLowerRealWeightedTight
  have hval : q11NuHiF (((20487 : ℤ) : ℚ) / ((40960 : ℕ) : ℚ)) =
      ((256201982975 : ℤ) : ℚ) / ((549755813888 : ℕ) : ℚ) :=
    rat_eq_of_ratIntDenCheck (by decide +kernel)
  have hterms :
      termsLowM 20486 40960 20487 40960 q11FrequencyTermsIWeighted =
        3300433767296149611 := by decide +kernel
  rw [hterms]
  rw [hval]
  norm_num [twoE, l2hi]

set_option maxHeartbeats 2000000 in
theorem q11_eighth_frequency_subcell_weighted_tight :
    (27435768107 / 10000000000 : ℝ) ≤
      q11RowLowerRealWeightedTight 20487 40960 20488 40960 := by
  unfold q11RowLowerRealWeightedTight
  have hval : q11NuHiF (((20488 : ℤ) : ℚ) / ((40960 : ℕ) : ℚ)) =
      ((512408223833 : ℤ) : ℚ) / ((1099511627776 : ℕ) : ℚ) :=
    rat_eq_of_ratIntDenCheck (by decide +kernel)
  have hterms :
      termsLowM 20487 40960 20488 40960 q11FrequencyTermsIWeighted =
        3300661147061648843 := by decide +kernel
  rw [hterms]
  rw [hval]
  norm_num [twoE, l2hi]

set_option maxHeartbeats 2000000 in
theorem q11_ninth_frequency_subcell_weighted_tight :
    (27435768107 / 10000000000 : ℝ) ≤
      q11RowLowerRealWeightedTight 20488 40960 20489 40960 := by
  unfold q11RowLowerRealWeightedTight
  have hval : q11NuHiF (((20489 : ℤ) : ℚ) / ((40960 : ℕ) : ℚ)) =
      ((512412481679 : ℤ) : ℚ) / ((1099511627776 : ℕ) : ℚ) :=
    rat_eq_of_ratIntDenCheck (by decide +kernel)
  have hterms :
      termsLowM 20488 40960 20489 40960 q11FrequencyTermsIWeighted =
        3300885771032815469 := by decide +kernel
  rw [hterms]
  rw [hval]
  norm_num [twoE, l2hi]

set_option maxHeartbeats 2000000 in
theorem q11_tenth_frequency_subcell_weighted_tight :
    (27435768107 / 10000000000 : ℝ) ≤
      q11RowLowerRealWeightedTight 20489 40960 20490 40960 := by
  unfold q11RowLowerRealWeightedTight
  have hval : q11NuHiF (((20490 : ℤ) : ℚ) / ((40960 : ℕ) : ℚ)) =
      ((512416739489 : ℤ) : ℚ) / ((1099511627776 : ℕ) : ℚ) :=
    rat_eq_of_ratIntDenCheck (by decide +kernel)
  have hterms :
      termsLowM 20489 40960 20490 40960 q11FrequencyTermsIWeighted =
        3301108034925573965 := by decide +kernel
  rw [hterms]
  rw [hval]
  norm_num [twoE, l2hi]

set_option maxHeartbeats 2000000 in
theorem q11_eleventh_frequency_subcell_weighted_tight :
    (27435768107 / 10000000000 : ℝ) ≤
      q11RowLowerRealWeightedTight 20490 40960 20491 40960 := by
  unfold q11RowLowerRealWeightedTight
  have hval : q11NuHiF (((20491 : ℤ) : ℚ) / ((40960 : ℕ) : ℚ)) =
      ((512420997267 : ℤ) : ℚ) / ((1099511627776 : ℕ) : ℚ) :=
    rat_eq_of_ratIntDenCheck (by decide +kernel)
  have hterms :
      termsLowM 20490 40960 20491 40960 q11FrequencyTermsIWeighted =
        3301328236199002196 := by decide +kernel
  rw [hterms]
  rw [hval]
  norm_num [twoE, l2hi]

set_option maxHeartbeats 2000000 in
theorem q11_twelfth_frequency_subcell_weighted_tight :
    (27435768107 / 10000000000 : ℝ) ≤
      q11RowLowerRealWeightedTight 20491 40960 20492 40960 := by
  unfold q11RowLowerRealWeightedTight
  have hval : q11NuHiF (((20492 : ℤ) : ℚ) / ((40960 : ℕ) : ℚ)) =
      ((512425255007 : ℤ) : ℚ) / ((1099511627776 : ℕ) : ℚ) :=
    rat_eq_of_ratIntDenCheck (by decide +kernel)
  have hterms :
      termsLowM 20491 40960 20492 40960 q11FrequencyTermsIWeighted =
        3301546609288659912 := by decide +kernel
  rw [hterms]
  rw [hval]
  norm_num [twoE, l2hi]

set_option maxHeartbeats 2000000 in
theorem q11_thirteenth_frequency_subcell_weighted_tight :
    (27435768107 / 10000000000 : ℝ) ≤
      q11RowLowerRealWeightedTight 20492 40960 20493 40960 := by
  unfold q11RowLowerRealWeightedTight
  have hval : q11NuHiF (((20493 : ℤ) : ℚ) / ((40960 : ℕ) : ℚ)) =
      ((512429512711 : ℤ) : ℚ) / ((1099511627776 : ℕ) : ℚ) :=
    rat_eq_of_ratIntDenCheck (by decide +kernel)
  have hterms :
      termsLowM 20492 40960 20493 40960 q11FrequencyTermsIWeighted =
        3301763338707679783 := by decide +kernel
  rw [hterms]
  rw [hval]
  norm_num [twoE, l2hi]

set_option maxHeartbeats 2000000 in
theorem q11_fourteenth_frequency_subcell_weighted_tight :
    (27435768107 / 10000000000 : ℝ) ≤
      q11RowLowerRealWeightedTight 20493 40960 20494 40960 := by
  unfold q11RowLowerRealWeightedTight
  have hval : q11NuHiF (((20494 : ℤ) : ℚ) / ((40960 : ℕ) : ℚ)) =
      ((512433770381 : ℤ) : ℚ) / ((1099511627776 : ℕ) : ℚ) :=
    rat_eq_of_ratIntDenCheck (by decide +kernel)
  have hterms :
      termsLowM 20493 40960 20494 40960 q11FrequencyTermsIWeighted =
        3301978576672805293 := by decide +kernel
  rw [hterms]
  rw [hval]
  norm_num [twoE, l2hi]

set_option maxHeartbeats 2000000 in
theorem q11_fifteenth_frequency_subcell_weighted_tight :
    (27435768107 / 10000000000 : ℝ) ≤
      q11RowLowerRealWeightedTight 20494 40960 20495 40960 := by
  unfold q11RowLowerRealWeightedTight
  have hval : q11NuHiF (((20495 : ℤ) : ℚ) / ((40960 : ℕ) : ℚ)) =
      ((128109507003 : ℤ) : ℚ) / ((274877906944 : ℕ) : ℚ) :=
    rat_eq_of_ratIntDenCheck (by decide +kernel)
  have hterms :
      termsLowM 20494 40960 20495 40960 q11FrequencyTermsIWeighted =
        3302192449967166393 := by decide +kernel
  rw [hterms]
  rw [hval]
  norm_num [twoE, l2hi]

set_option maxHeartbeats 2000000 in
theorem q11_sixteenth_frequency_subcell_weighted_tight :
    (27435768107 / 10000000000 : ℝ) ≤
      q11RowLowerRealWeightedTight 20495 40960 20496 40960 := by
  unfold q11RowLowerRealWeightedTight
  have hval : q11NuHiF (((20496 : ℤ) : ℚ) / ((40960 : ℕ) : ℚ)) =
      ((64055285701 : ℤ) : ℚ) / ((137438953472 : ℕ) : ℚ) :=
    rat_eq_of_ratIntDenCheck (by decide +kernel)
  have hterms :
      termsLowM 20495 40960 20496 40960 q11FrequencyTermsIWeighted =
        3302405065631520586 := by decide +kernel
  rw [hterms]
  rw [hval]
  norm_num [twoE, l2hi]

set_option maxHeartbeats 2000000 in
theorem q11_seventeenth_frequency_subcell_weighted_tight :
    (27435768107 / 10000000000 : ℝ) ≤
      q11RowLowerRealWeightedTight 20496 40960 20497 40960 := by
  unfold q11RowLowerRealWeightedTight
  have hval : q11NuHiF (((20497 : ℤ) : ℚ) / ((40960 : ℕ) : ℚ)) =
      ((256223271585 : ℤ) : ℚ) / ((549755813888 : ℕ) : ℚ) :=
    rat_eq_of_ratIntDenCheck (by decide +kernel)
  have hterms :
      termsLowM 20496 40960 20497 40960 q11FrequencyTermsIWeighted =
        3302616515252157112 := by decide +kernel
  rw [hterms]
  rw [hval]
  norm_num [twoE, l2hi]

set_option maxHeartbeats 2000000 in
theorem q11_eighteenth_frequency_subcell_weighted_tight :
    (27435768107 / 10000000000 : ℝ) ≤
      q11RowLowerRealWeightedTight 20497 40960 20498 40960 := by
  unfold q11RowLowerRealWeightedTight
  have hval : q11NuHiF (((20498 : ℤ) : ℚ) / ((40960 : ℕ) : ℚ)) =
      ((64056350087 : ℤ) : ℚ) / ((137438953472 : ℕ) : ℚ) :=
    rat_eq_of_ratIntDenCheck (by decide +kernel)
  have hterms :
      termsLowM 20497 40960 20498 40960 q11FrequencyTermsIWeighted =
        3302826878069755213 := by decide +kernel
  rw [hterms]
  rw [hval]
  norm_num [twoE, l2hi]

set_option maxHeartbeats 2000000 in
theorem q11_nineteenth_frequency_subcell_weighted_tight :
    (27435768107 / 10000000000 : ℝ) ≤
      q11RowLowerRealWeightedTight 20498 40960 20499 40960 := by
  unfold q11RowLowerRealWeightedTight
  have hval : q11NuHiF (((20499 : ℤ) : ℚ) / ((40960 : ℕ) : ℚ)) =
      ((512455058185 : ℤ) : ℚ) / ((1099511627776 : ℕ) : ℚ) :=
    rat_eq_of_ratIntDenCheck (by decide +kernel)
  have hterms :
      termsLowM 20498 40960 20499 40960 q11FrequencyTermsIWeighted =
        3303036223303519355 := by decide +kernel
  rw [hterms]
  rw [hval]
  norm_num [twoE, l2hi]

def q11FirstRefinedFrequencyCells : List Li2Lean.F_L8.ReceiptCell := [
  ⟨1 / 2, 20481 / 40960, 27435768107 / 10000000000⟩,
  ⟨20481 / 40960, 20482 / 40960, 27435768107 / 10000000000⟩,
  ⟨20482 / 40960, 20483 / 40960, 27435768107 / 10000000000⟩,
  ⟨20483 / 40960, 20484 / 40960, 27435768107 / 10000000000⟩,
  ⟨20484 / 40960, 20485 / 40960, 27435768107 / 10000000000⟩,
  ⟨20485 / 40960, 20486 / 40960, 27435768107 / 10000000000⟩,
  ⟨20486 / 40960, 20487 / 40960, 27435768107 / 10000000000⟩,
  ⟨20487 / 40960, 20488 / 40960, 27435768107 / 10000000000⟩,
  ⟨20488 / 40960, 20489 / 40960, 27435768107 / 10000000000⟩,
  ⟨20489 / 40960, 20490 / 40960, 27435768107 / 10000000000⟩,
  ⟨20490 / 40960, 20491 / 40960, 27435768107 / 10000000000⟩,
  ⟨20491 / 40960, 20492 / 40960, 27435768107 / 10000000000⟩,
  ⟨20492 / 40960, 20493 / 40960, 27435768107 / 10000000000⟩,
  ⟨20493 / 40960, 20494 / 40960, 27435768107 / 10000000000⟩,
  ⟨20494 / 40960, 20495 / 40960, 27435768107 / 10000000000⟩,
  ⟨20495 / 40960, 20496 / 40960, 27435768107 / 10000000000⟩,
  ⟨20496 / 40960, 20497 / 40960, 27435768107 / 10000000000⟩,
  ⟨20497 / 40960, 20498 / 40960, 27435768107 / 10000000000⟩,
  ⟨20498 / 40960, 20499 / 40960, 27435768107 / 10000000000⟩]

theorem q11FirstRefinedFrequencyCells_exactChain :
    Li2Lean.F_L8.ExactChain q11FirstRefinedFrequencyCells
      (1 / 2) (20499 / 40960) := by
  apply Li2Lean.F_L8.exactChain_iff_spec.mpr
  norm_num [q11FirstRefinedFrequencyCells, Li2Lean.F_L8.ExactChainSpec]


end
end Li2Lean.P0.Q11Data
