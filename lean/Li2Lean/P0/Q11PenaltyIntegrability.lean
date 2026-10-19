/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.Q11PenaltyRows

/-!
# Integrability reductions for q11 penalty rows

Finite certified row bounds imply integrability of the positive-part
penalties once the actual fields are measurable. These reductions do not
construct the row certificates or prove the q11 endpoint route.
-/

open MeasureTheory Set

namespace Li2Lean.P0.Q11Data

noncomputable section

open Li2Lean.F_L8 Li2Lean.P0.CA.Receipt

theorem q11PinnedPenalty_integrable_of_lower_audit
    (cells : List ReceiptCell) (allowance : ℚ)
    (chain : ExactChain cells (1 / 4) (5 / 4))
    (lower : ∀ c ∈ cells, ∀ x : ℝ,
      (c.lo : ℝ) ≤ x → x ≤ (c.hi : ℝ) →
        ((c.lower : ℝ) - (allowance : ℝ)) ≤ q11Weta (x : ℂ))
    (hW : Measurable q11Weta) :
    IntegrableOn
      (fun x : ℝ => max ((q11EtaFloorQ : ℝ) - q11Weta (x : ℂ)) 0)
      (Icc (1 / 4 : ℝ) (5 / 4 : ℝ)) := by
  apply (stepMajorant_integrableOn q11EtaFloorQ allowance cells
    (Icc (1 / 4 : ℝ) (5 / 4 : ℝ))).mono'
  · exact ((measurable_const.sub (hW.comp Complex.continuous_ofReal.measurable)).max
      measurable_const).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le
      (sub_le_stepMajorant chain q11EtaFloorQ allowance lower
        (by simpa using hx.1) (by simpa using hx.2))
      (stepMajorant_nonneg _ _ _ _)

theorem q11FrequencyPenalty_integrable_of_lower_audit
    (cells : List ReceiptCell) (allowance : ℚ)
    (chain : ExactChain cells (1 / 2) (81 / 10))
    (lower : ∀ c ∈ cells, ∀ t : ℝ,
      (c.lo : ℝ) ≤ t → t ≤ (c.hi : ℝ) →
        ((c.lower : ℝ) - (allowance : ℝ)) ≤ q11Wmu t)
    (hW : Measurable q11Wmu) :
    IntegrableOn
      (fun t : ℝ => max ((q11FrequencyFloorQ : ℝ) - q11Wmu t) 0)
      (Ici (1 / 2 : ℝ)) := by
  apply (stepMajorant_integrableOn q11FrequencyFloorQ allowance cells
    (Ici (1 / 2 : ℝ))).mono'
  · exact ((measurable_const.sub hW).max measurable_const).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    by_cases hle : t ≤ (81 / 10 : ℝ)
    · exact max_le
        (sub_le_stepMajorant chain q11FrequencyFloorQ allowance lower
          (by simpa using ht) (by simpa using hle))
        (stepMajorant_nonneg _ _ _ _)
    · have htail : (q11FrequencyFloorQ : ℝ) ≤ q11Wmu t :=
        q11_frequency_floor_le_tail (le_of_not_ge hle)
      rw [max_eq_right (sub_nonpos.mpr htail)]
      exact stepMajorant_nonneg _ _ _ _

theorem q11FrequencyPenalty_zero_tail_audit {t : ℝ}
    (ht : (81 / 10 : ℝ) ≤ t) :
    max ((q11FrequencyFloorQ : ℝ) - q11Wmu t) 0 = 0 := by
  exact max_eq_right (sub_nonpos.mpr (q11_frequency_floor_le_tail ht))

end

end Li2Lean.P0.Q11Data

#print axioms Li2Lean.P0.Q11Data.q11PinnedPenalty_integrable_of_lower_audit
#print axioms Li2Lean.P0.Q11Data.q11FrequencyPenalty_integrable_of_lower_audit
#print axioms Li2Lean.P0.Q11Data.q11FrequencyPenalty_zero_tail_audit
