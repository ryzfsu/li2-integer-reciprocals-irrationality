/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

The three-regime bridge for the signed V integerizer. This module only
combines the v13 local estimates. The residue-block estimate is supplied by
its finite pivot certificate; no Gaussian elimination is performed here.

Paper source: `v-arithmetic.tex:66-146,149-256,291-318`.
-/

import Li2Lean.B3.ActualRationalIntegerizerGeneric
import Li2Lean.B3.ActualVFormalDivisor
import Li2Lean.B3.H4bQPlusOneValuation

namespace Li2Lean.B3

noncomputable section

open scoped BigOperators

/-! ## The exponent used by the local v13 regimes -/

/-- The literal row-denominator exponent from v13 `v-arithmetic.tex:37-46`.
This is the baseline before the formal divisor or finite residue/pole credit. -/
def v13BaselineExponent (n p : ℕ) : ℤ :=
  ((12 * n * Nat.log p (V.vN n) + n * Nat.log p (V.vU n) : ℕ) : ℤ)

/-- The exceptional-prime exponent after both formal credits are applied.
The q-credit is supplied by `ActualVFormalDivisor`; the q+1 credit by
`H4bQPlusOneValuation` (v13 `v-arithmetic.tex:66-146`). -/
def v13ExceptionalExponent (q n p : ℕ) : ℤ :=
  v13BaselineExponent n p -
      (padicValNat p q : ℤ) *
        (((53 * n ^ 2 + 2) / 3 - 4 * n : ℕ) : ℤ) -
      ((4 * n * padicValNat p (q + 1) : ℕ) : ℤ)

/-- A branch predicate for the residue-block estimate. Its meaning is fixed
by the caller's v13 decoded slab and pivot table. -/
abbrev V13ResidueRegime := ℕ → ℕ → Prop

/-- A branch predicate for the outer-pole estimate. -/
abbrev V13OuterRegime := ℕ → ℕ → Prop

/-- Inputs to the q-uniform three-regime bridge. `residueExponent` is normally
the rank sum `m + sum_u rank(I(...,u))`; the proof of that rank sum belongs to
the finite pivot certificate, not to this logical combiner. -/
def V13ValuationRegimeData (q : ℕ)
    (residueRegime outerRegime : V13ResidueRegime)
    (residueExponent outerExponent : ℕ → ℕ → ℤ) : Prop :=
  (∀ {n p : ℕ}, 0 < n → p.Prime →
      ¬ p ∣ q * (q + 1) → residueRegime n p →
      V.actualGaussValuation p (V.actualVDeterminant q (4 * n)) ≥
        -residueExponent n p) ∧
  (∀ {n p : ℕ}, 0 < n → p.Prime →
      ¬ p ∣ q * (q + 1) → outerRegime n p →
      V.actualGaussValuation p (V.actualVDeterminant q (4 * n)) ≥
        -outerExponent n p)

/-- The q-uniform exponent assembled from the three v13 local regimes.
The alternative is the proved row-denominator baseline. -/
def v13ThreeRegimeExponent (q : ℕ)
    (residueRegime outerRegime : V13ResidueRegime)
    (residueExponent outerExponent : ℕ → ℕ → ℤ)
    (n p : ℕ) : ℤ := by
  classical
  exact if n = 0 then 0
    else if p ∣ q * (q + 1) then v13ExceptionalExponent q n p
    else if residueRegime n p then residueExponent n p
    else if outerRegime n p then outerExponent n p
    else v13BaselineExponent n p

private theorem actualV_gauss_val_of_dvd_q
    {q n p : ℕ} (hq : SignedVBaseRange q) (hn : 0 < n)
    (hp : p.Prime) (hpq : p ∣ q) :
    V.actualGaussValuation p (V.actualVDeterminant q (4 * n)) ≥
      -v13ExceptionalExponent q n p := by
  have hne : V.actualVDeterminant q (4 * n) ≠ 0 :=
    VFormalADivisor.actualVDeterminant_four_mul_ne_zero q n hq.1
  have hpq1 : ¬ p ∣ q + 1 := by
    intro hq1
    have hone : p ∣ 1 := by
      simpa using Nat.dvd_sub hq1 hpq
    exact hp.ne_one (Nat.dvd_one.mp hone)
  unfold V.actualGaussValuation
  rw [dif_pos (Polynomial.support_nonempty.mpr hne)]
  apply Finset.le_inf'
  intro i hi
  have hcoeff := actualV_coefficient_val_of_dvd_q q n p i hq hp hpq
  have hcoeff' := hcoeff.resolve_left (Polynomial.mem_support_iff.mp hi)
  simpa [v13ExceptionalExponent, v13BaselineExponent, hpq1,
    padicValNat.eq_zero_of_not_dvd hpq1, mul_comm] using hcoeff'

private theorem actualV_gauss_val_of_dvd_q_succ_exponent
    {q n p : ℕ} (hq : SignedVBaseRange q) (hn : 0 < n)
    (hp : p.Prime) (hpq1 : p ∣ q + 1) :
    V.actualGaussValuation p (V.actualVDeterminant q (4 * n)) ≥
      -v13ExceptionalExponent q n p := by
  simpa [v13ExceptionalExponent, v13BaselineExponent, mul_comm] using
    (actualV_v13_gauss_val_of_dvd_q_succ q n p hq.2 hp hpq1)

/-! ## The generic bridge -/

/-- Combine the exceptional-prime, residue-block, outer-pole, and baseline
estimates into the valuation field consumed by
`VActualRationalIntegerizerProducer`.

The theorem follows the three regimes in v13 `v-arithmetic.tex:128-318`.
The finite rank/pivot certificate is represented by `hreg.1`; no linear
algebra is hidden in this bridge. -/
theorem v13_valuation_bound_of_three_regimes
    {q : ℕ} (hq : SignedVBaseRange q)
    (residueRegime outerRegime : V13ResidueRegime)
    (residueExponent outerExponent : ℕ → ℕ → ℤ)
    (hreg : V13ValuationRegimeData q residueRegime outerRegime
      residueExponent outerExponent) :
    QActualPrimeValuationBound q
      (v13ThreeRegimeExponent q residueRegime outerRegime
        residueExponent outerExponent) := by
  classical
  intro n p hp
  by_cases hn : 0 < n
  · have hneq : n ≠ 0 := Nat.ne_of_gt hn
    by_cases hdiv : p ∣ q * (q + 1)
    · rcases hp.dvd_mul.mp hdiv with hpq | hpq1
      · have h := actualV_gauss_val_of_dvd_q hq hn hp hpq
        simpa [v13ThreeRegimeExponent, hneq, hdiv] using h
      · have h := actualV_gauss_val_of_dvd_q_succ_exponent hq hn hp hpq1
        simpa [v13ThreeRegimeExponent, hneq, hdiv] using h
    · by_cases hr : residueRegime n p
      · have h := hreg.1 hn hp hdiv hr
        simpa [v13ThreeRegimeExponent, hneq, hdiv, hr] using h
      · by_cases ho : outerRegime n p
        · have h := hreg.2 hn hp hdiv ho
          simpa [v13ThreeRegimeExponent, hneq, hdiv, hr, ho] using h
        · have h := vActualBaseline_gauss_lower q n p hn hp
          simpa [v13ThreeRegimeExponent, hneq, hdiv, hr, ho,
            v13BaselineExponent] using h
  · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    simpa [v13ThreeRegimeExponent,
      V.actualGaussValuation_zero_index] using
      (show V.actualGaussValuation p (V.actualVDeterminant q 0) ≥ 0 by
        rw [V.actualGaussValuation_zero_index]
        norm_num)

end
end Li2Lean.B3

#print axioms Li2Lean.B3.v13_valuation_bound_of_three_regimes
