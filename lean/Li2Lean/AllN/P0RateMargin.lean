/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/

import Li2Lean.P0.PositiveBaseParam
import Li2Lean.P0.ConfigLogTaylor

namespace Li2Lean.AllNAssembly

noncomputable section

open Li2Lean.P0.ConfigLogTaylor
open Li2Lean.P0.PositiveBase
/-! ## Finite exact rate-margin check against the v13 endpoint chord -/

private def rateLogMinusOneUpper : ℕ → ℚ
  | 3 => 6932 / 10000
  | 4 => 10987 / 10000
  | 5 => 13863 / 10000
  | 6 => 16095 / 10000
  | 7 => 17918 / 10000
  | 8 => 19460 / 10000
  | 9 => 20795 / 10000
  | 10 => 21973 / 10000
  | 11 => 23026 / 10000
  | _ => 0

private def rateLogNatLower : ℕ → ℚ
  | 3 => 10986 / 10000
  | 4 => 13862 / 10000
  | 5 => 16094 / 10000
  | 6 => 17917 / 10000
  | 7 => 19459 / 10000
  | 8 => 20794 / 10000
  | 9 => 21972 / 10000
  | 10 => 23025 / 10000
  | 11 => 23978 / 10000
  | _ => 0

private def rateLogHalfUpper : ℕ → ℚ
  | 3 => 4055 / 10000
  | 4 => 6932 / 10000
  | 5 => 9163 / 10000
  | 6 => 10987 / 10000
  | 7 => 12528 / 10000
  | 8 => 13863 / 10000
  | 9 => 15041 / 10000
  | 10 => 16095 / 10000
  | 11 => 17048 / 10000
  | _ => 0

private theorem rate_log_qminus1_upper (q : ℕ) (hq3 : 3 ≤ q) (hq11 : q ≤ 11) :
    Real.log ((q - 1 : ℕ) : ℝ) < (rateLogMinusOneUpper q : ℝ) := by
  have hqpos : 0 < ((q - 1 : ℕ) : ℚ) := by
    exact_mod_cast (show 0 < q - 1 by omega)
  have hcheck :
      logPolynomial ((q - 1 : ℕ) : ℚ) 40 +
          logRemainder ((q - 1 : ℕ) : ℚ) 40 < rateLogMinusOneUpper q := by
    interval_cases q <;>
      norm_num [rateLogMinusOneUpper, logPolynomial, logRemainder,
        logCoordinate, Finset.sum_range_succ]
  have hlog := log_lt_of_rational hqpos 40 hcheck
  have hcast : (((q - 1 : ℕ) : ℚ) : ℝ) = ((q - 1 : ℕ) : ℝ) := by norm_cast
  rw [hcast] at hlog
  exact hlog

private theorem rate_log_q_lower (q : ℕ) (hq3 : 3 ≤ q) (hq11 : q ≤ 11) :
    (rateLogNatLower q : ℝ) < Real.log (q : ℝ) := by
  have hpoly : rateLogNatLower q < logPolynomial (q : ℚ) 40 := by
    interval_cases q <;>
      norm_num [rateLogNatLower, logPolynomial, logCoordinate,
        Finset.sum_range_succ]
  have hpolyR : (rateLogNatLower q : ℝ) < (logPolynomial (q : ℚ) 40 : ℝ) :=
    by exact_mod_cast hpoly
  have hseries : (logPolynomial (q : ℚ) 40 : ℝ) ≤ Real.log (q : ℝ) :=
    logPolynomial_le_log (by exact_mod_cast (show 1 ≤ q by omega)) 40
  exact lt_of_lt_of_le hpolyR hseries

private theorem rate_log_qhalf_upper (q : ℕ) (hq3 : 3 ≤ q) (hq11 : q ≤ 11) :
    Real.log ((q : ℝ) / 2) < (rateLogHalfUpper q : ℝ) := by
  have hqpos : 0 < ((q : ℚ) / 2) := by positivity
  have hcheck :
      logPolynomial ((q : ℚ) / 2) 40 +
          logRemainder ((q : ℚ) / 2) 40 < rateLogHalfUpper q := by
    interval_cases q <;>
      norm_num [rateLogHalfUpper, logPolynomial, logRemainder,
        logCoordinate, Finset.sum_range_succ]
  have hlog := log_lt_of_rational hqpos 40 hcheck
  have hcast : (((q : ℚ) / 2 : ℚ) : ℝ) = (q : ℝ) / 2 := by norm_num
  rw [hcast] at hlog
  exact hlog

private theorem rate_log_eleven_half_lower :
    (17047 / 10000 : ℝ) < Real.log ((11 : ℝ) / 2) := by
  have hpoly : (17047 / 10000 : ℚ) < logPolynomial (11 / 2 : ℚ) 40 := by
    norm_num [logPolynomial, logCoordinate, Finset.sum_range_succ]
  have hpolyR : (17047 / 10000 : ℝ) <
      (logPolynomial (11 / 2 : ℚ) 40 : ℝ) := by
    norm_num [logPolynomial, logCoordinate, Finset.sum_range_succ]
  have hseries : (logPolynomial (11 / 2 : ℚ) 40 : ℝ) ≤
      Real.log ((11 : ℝ) / 2) :=
    by
      have h := logPolynomial_le_log (q := (11 / 2 : ℚ)) (by norm_num) 40
      simpa using h
  exact lt_of_lt_of_le hpolyR hseries

/-- The v13 endpoint chord, expanded to the logarithm formula used by the
positive-base producer. -/
def p0PositiveChordFormulaLocal (q : ℕ) : ℝ :=
  (248035 / 125000 : ℝ) +
    (Real.log ((q : ℝ) / 2) / Real.log ((11 : ℝ) / 2)) *
      ((77597 / 100000 : ℝ) - 248035 / 125000)

private def rateUpper (q : ℕ) : ℚ :=
  25421 / 10000 + (1 / 16 : ℚ) * rateLogMinusOneUpper q -
    (13 / 16 : ℚ) * rateLogNatLower q

private def chordLower (q : ℕ) : ℚ :=
  (248035 / 125000 : ℚ) +
    (rateLogHalfUpper q / (17047 / 10000 : ℚ)) *
      ((77597 / 100000 : ℚ) - 248035 / 125000)

private theorem rate_upper_lt_chord_lower (q : ℕ) (hq3 : 3 ≤ q) (hq11 : q ≤ 11) :
    (rateUpper q : ℝ) < (chordLower q : ℝ) := by
  interval_cases q <;>
    norm_num [rateUpper, chordLower, rateLogMinusOneUpper,
      rateLogNatLower, rateLogHalfUpper]

private theorem chord_lower_le_formula (q : ℕ) (hq3 : 3 ≤ q) (hq11 : q ≤ 11) :
    (chordLower q : ℝ) ≤ p0PositiveChordFormulaLocal q := by
  have hshift := rate_log_qhalf_upper q hq3 hq11
  have hupper0 : 0 ≤ (rateLogHalfUpper q : ℝ) := by
    interval_cases q <;> norm_num [rateLogHalfUpper]
  have hbase := rate_log_eleven_half_lower
  have hbase0 : (0 : ℝ) < 17047 / 10000 := by norm_num
  have hbasePos : (0 : ℝ) < Real.log ((11 : ℝ) / 2) :=
    lt_trans hbase0 hbase
  have hratio : Real.log ((q : ℝ) / 2) / Real.log ((11 : ℝ) / 2) ≤
      (rateLogHalfUpper q : ℝ) / (17047 / 10000 : ℝ) := by
    apply (div_le_iff₀ hbasePos).2
    have hmul := mul_le_mul_of_nonneg_left (le_of_lt hbase) hupper0
    have hdiv : (rateLogHalfUpper q : ℝ) ≤
        (rateLogHalfUpper q : ℝ) * Real.log ((11 : ℝ) / 2) /
          (17047 / 10000 : ℝ) :=
      (le_div_iff₀ hbase0).2 (by nlinarith [hmul])
    calc
      Real.log ((q : ℝ) / 2) ≤ (rateLogHalfUpper q : ℝ) := le_of_lt hshift
      _ ≤ (rateLogHalfUpper q : ℝ) * Real.log ((11 : ℝ) / 2) /
          (17047 / 10000 : ℝ) := hdiv
      _ = ((rateLogHalfUpper q : ℝ) / (17047 / 10000 : ℝ)) *
          Real.log ((11 : ℝ) / 2) := by ring
  have hdelta :
      ((77597 / 100000 : ℝ) - 248035 / 125000) ≤ 0 := by norm_num
  have hmul := mul_le_mul_of_nonpos_left hratio hdelta
  unfold chordLower p0PositiveChordFormulaLocal
  push_cast
  nlinarith [hmul]

private theorem tauSharp_lt_rateUpper (q : ℕ) (hq3 : 3 ≤ q) (hq11 : q ≤ 11) :
    p0TauSharp (q : ℤ) < (rateUpper q : ℝ) := by
  have hq0 : 0 ≤ (q : ℤ) := by omega
  have hqm10 : 0 ≤ (q : ℤ) - 1 := by omega
  have hformula :
      p0TauSharp (q : ℤ) = p0K + (1 / 16 : ℝ) *
        Real.log ((q - 1 : ℕ) : ℝ) - (13 / 16 : ℝ) * Real.log (q : ℝ) := by
    simp [p0TauSharp, Int.natAbs_of_nonneg hq0,
      Int.natAbs_of_nonneg hqm10]
    congr 1
    rw [Nat.cast_sub (by omega : 1 ≤ q)]
    norm_num
  have hK : p0K < (25421 / 10000 : ℝ) := by norm_num [p0K]
  have hminus := rate_log_qminus1_upper q hq3 hq11
  have hqlog := rate_log_q_lower q hq3 hq11
  rw [hformula]
  unfold rateUpper
  push_cast
  nlinarith

/-- The finite q=3,...,11 sharp-rate margin required by the B2 producer.
This matches the logarithm formula in `AllNAssembly.p0PositiveChord`. -/
theorem p0TauSharp_lt_p0PositiveChord_formula
    (q : ℕ) (hq3 : 3 ≤ q) (hq11 : q ≤ 11) :
    p0TauSharp (q : ℤ) < p0PositiveChordFormulaLocal q := by
  exact lt_of_lt_of_le
    (lt_trans (tauSharp_lt_rateUpper q hq3 hq11)
      (rate_upper_lt_chord_lower q hq3 hq11))
    (chord_lower_le_formula q hq3 hq11)

theorem p0RateMargin_formula_producer :
    ∀ q : ℕ, 3 ≤ q → q ≤ 11 →
      p0TauSharp (q : ℤ) < p0PositiveChordFormulaLocal q := by
  intro q hq3 hq11
  exact p0TauSharp_lt_p0PositiveChord_formula q hq3 hq11

/-! A reachable relaxed rate for the q>=3 integerizer port. The existing
finite a=2 budget has core constant below `1273/500`; this definition keeps
the q-dependent logarithmic terms while leaving the sharp `p0TauSharp` route
as a separate, stronger target. -/
noncomputable def p0RateRelaxed (q : ℕ) : ℝ :=
  (1273 / 500 : ℝ) + (1 / 16 : ℝ) *
      Real.log ((q - 1 : ℕ) : ℝ) -
    (13 / 16 : ℝ) * Real.log (q : ℝ)

private def relaxedRateUpper (q : ℕ) : ℚ :=
  1273 / 500 + (1 / 16 : ℚ) * rateLogMinusOneUpper q -
    (13 / 16 : ℚ) * rateLogNatLower q

private theorem relaxed_rate_upper_lt_chord_lower (q : ℕ)
    (hq3 : 3 ≤ q) (hq11 : q ≤ 11) :
    (relaxedRateUpper q : ℝ) < (chordLower q : ℝ) := by
  interval_cases q <;>
    norm_num [relaxedRateUpper, chordLower, rateLogMinusOneUpper,
      rateLogNatLower, rateLogHalfUpper]

theorem p0RateRelaxed_lt_p0PositiveChordFormula
    (q : ℕ) (hq3 : 3 ≤ q) (hq11 : q ≤ 11) :
    p0RateRelaxed q < p0PositiveChordFormulaLocal q := by
  have hminus := rate_log_qminus1_upper q hq3 hq11
  have hqlog := rate_log_q_lower q hq3 hq11
  have hup : p0RateRelaxed q < (relaxedRateUpper q : ℝ) := by
    unfold p0RateRelaxed relaxedRateUpper
    push_cast
    nlinarith
  exact lt_of_lt_of_le (lt_trans hup
    (relaxed_rate_upper_lt_chord_lower q hq3 hq11))
    (chord_lower_le_formula q hq3 hq11)


/-- The q-dependent exceptional-prime correction is below the relaxed rate.
This is the comparison needed to feed the generic low-prime estimate into
the rate target; it is proved from the same finite q logarithm certificates
used by the relaxed-rate margin. -/
theorem p0RateRelaxed_lowPrime_correction_le
    (q : ℕ) (hq3 : 3 ≤ q) (hq11 : q ≤ 11) :
    (1 / 16 : ℝ) * Real.log ((q - 1 : ℕ) : ℝ) ≤ p0RateRelaxed q := by
  have hhalf := rate_log_qhalf_upper q hq3 hq11
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    convert Real.log_le_sub_one_of_pos (x := (2 : ℝ)) (by norm_num) using 1 <;> norm_num
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hqhalf : (0 : ℝ) < (q : ℝ) / 2 := by positivity
  have hsplit : Real.log (q : ℝ) = Real.log ((q : ℝ) / 2) + Real.log 2 := by
    rw [← Real.log_mul hqhalf.ne' (by norm_num : (2 : ℝ) ≠ 0)]
    congr 1
    field_simp
  have hupper : Real.log (q : ℝ) < 3 := by
    rw [hsplit]
    have hcell : (rateLogHalfUpper q : ℝ) < 2 := by
      interval_cases q <;> norm_num [rateLogHalfUpper]
    linarith
  unfold p0RateRelaxed
  nlinarith

end

end Li2Lean.AllNAssembly
