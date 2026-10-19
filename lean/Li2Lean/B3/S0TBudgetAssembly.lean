/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B3.S0ActualInterface
import Li2Lean.B3.ReferencePackage
import Li2Lean.B3.S0PinnedTransfer
import Li2Lean.B3.F6Alpha

namespace Li2Lean.B3

/-!
S0-T C8 budget assembly (v13 `v-analytic.tex:602-627`).

The preceding C5-C7 estimate is the explicit `hcore` input below. This lemma
only converts that unnormalised triple-integral estimate into the actual
normalised `phi` budget, using the reference package's energy and mass
constants. It does not assert or prove the C5-C7 analytic estimate.

The pinned and actual files use the same prefactor and budget expressions.
Only those expressions are reused here; the old fixed-`phiMax` carrier is not
used for the `n`-dependent actual contour integral.
-/

theorem s0PinnedPrefactor_eq_s0TransferPrefactor (q n : ℕ) :
    s0PinnedPrefactor q n = s0TransferPrefactor q n := rfl

theorem s0PinnedPhiBudget_eq_s0TransferPhiBudget
    (q : ℕ) (alpha sigma Tq phiMax : ℝ) (n : ℕ) :
    s0PinnedPhiBudget q alpha sigma Tq phiMax n =
      s0TransferPhiBudget q alpha sigma Tq phiMax n := rfl

/-! The coefficient comparison uses the exact q = 2,...,7 logarithm
enclosures from `F6Alpha`, rather than treating `alpha_le` as a fresh
arbitrary assumption.  This is the finite numerical boundary of C8. -/

theorem s0T_alpha_le_of_range {q : ℕ} (hq : SignedVBaseRange q) :
    vAlpha q ≤ (vQlow q : ℝ) - (3 / 2 : ℝ) * Real.log (q : ℝ) -
      (vKx q : ℝ) - (5 / 4 : ℝ) * (vKv q : ℝ) - (vKz q : ℝ) := by
  exact v13_alpha_le_of_range hq

theorem s0T_transfer_constant_lt_200_of_range
    {q : ℕ} (hq : SignedVBaseRange q) :
    2 * denominatorTransferCost q + 7 + 130 < (200 : ℝ) := by
  have hcost := denominatorTransferCost_lt_808_100 hq.1
  nlinarith

theorem s0T_budget_of_reference_facts
    {q : ℕ} {hq : SignedVBaseRange q}
    (P : VReferencePackage q hq)
    (n : ℕ) (Tq : ℝ) (hTq : 0 < Tq)
    (hn : 64 ≤ 4 * n)
    (hI : V.Literal.vContourTripleIntegral q n ≠ 0)
    (hcore : 64 ≤ 4 * n →
      Real.log ‖V.Literal.vContourTripleIntegral q n‖ ≤
        - (((vQlow q : ℚ) : ℝ) - (3 / 2 : ℝ) * Real.log q -
          (vKx q : ℝ) - (5 / 4 : ℝ) * (vKv q : ℝ) -
          (vKz q : ℝ)) * ((4 * n : ℕ) : ℝ) ^ 2 +
        (13 / 2 : ℝ) * ((4 * n : ℕ) : ℝ) *
          Real.log ((4 * n : ℕ) : ℝ) +
        3 * sigmaBudget P.Ax P.Av P.Az *
          (1 + Real.log (((4 * n : ℕ) : ℝ) ^ 2 / 3)) +
        (2 * denominatorTransferCost q + 7 + 130) +
          ((4 * n : ℕ) : ℝ) -
        Real.log (s0TransferPrefactor q n)) :
    Real.log |v13PhiMaxValue q Tq n| ≤
      s0TransferPhiBudget q (vAlpha q) (vSigma q) Tq
        (v13PhiMaxValue q Tq n) n := by
  let m : ℝ := ((4 * n : ℕ) : ℝ)
  let energyCoeff : ℝ :=
    ((vQlow q : ℚ) : ℝ) - (3 / 2 : ℝ) * Real.log q -
      (vKx q : ℝ) - (5 / 4 : ℝ) * (vKv q : ℝ) - (vKz q : ℝ)
  have hI_norm_pos :
      0 < ‖V.Literal.vContourTripleIntegral q n‖ := norm_pos_iff.mpr hI
  have hTpow_pos : 0 < Tq ^ (4 * n) := pow_pos hTq _
  have hphi_pos : 0 < v13PhiMaxValue q Tq n := by
    unfold v13PhiMaxValue
    exact div_pos hI_norm_pos hTpow_pos
  have hpref_pos : 0 < s0TransferPrefactor q n :=
    s0TransferPrefactor_pos hq.1
  have hlog_phi :
      Real.log |v13PhiMaxValue q Tq n| =
        Real.log ‖V.Literal.vContourTripleIntegral q n‖ -
          Real.log (Tq ^ (4 * n)) := by
    rw [abs_of_pos hphi_pos]
    unfold v13PhiMaxValue
    rw [Real.log_div hI_norm_pos.ne' hTpow_pos.ne']
  have hcore' := hcore hn
  rw [← P.facts.sigma_eq] at hcore'
  change Real.log ‖V.Literal.vContourTripleIntegral q n‖ ≤
      -energyCoeff * m ^ 2 +
        (13 / 2 : ℝ) * m * Real.log m +
        3 * vSigma q * (1 + Real.log (m ^ 2 / 3)) +
        (2 * denominatorTransferCost q + 7 + 130) + m -
        Real.log (s0TransferPrefactor q n) at hcore'
  have hAlpha : vAlpha q ≤ energyCoeff := by
    simpa [energyCoeff] using s0T_alpha_le_of_range hq
  have henergy : -energyCoeff * m ^ 2 ≤ -vAlpha q * m ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_right hAlpha (sq_nonneg m)
    linarith
  rw [hlog_phi]
  unfold s0TransferPhiBudget
  rw [Real.log_mul hpref_pos.ne' hTpow_pos.ne']
  change Real.log ‖V.Literal.vContourTripleIntegral q n‖ -
      Real.log (Tq ^ (4 * n)) ≤
    -vAlpha q * m ^ 2 +
      (13 / 2 : ℝ) * m * Real.log m +
      3 * vSigma q * (1 + Real.log (m ^ 2 / 3)) +
      (2 * denominatorTransferCost q + 7 + 130) + m -
      (Real.log (s0TransferPrefactor q n) +
        Real.log (Tq ^ (4 * n)))
  linarith

end Li2Lean.B3
