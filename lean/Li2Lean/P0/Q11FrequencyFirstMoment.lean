/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.Q11EndpointBridge
import Li2Lean.P0.Q11MeasureDomination

open MeasureTheory Set
open scoped ENNReal

namespace Li2Lean.P0.Q11Data

noncomputable section

theorem q11FrequencyReferenceMeasure_integrable_id :
    Integrable (fun t : ℝ => t) q11FrequencyReferenceMeasure := by
  letI : IsFiniteMeasure q11FrequencyReferenceMeasure :=
    ⟨by rw [q11FrequencyReferenceMeasure_univ]; simp⟩
  apply (integrable_const (μ := q11FrequencyReferenceMeasure) (9 / 2 : ℝ)).mono'
    continuous_id.aestronglyMeasurable
  filter_upwards [q11FrequencyReferenceMeasure_ae_interval] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (by change 0 ≤ t; linarith [ht.1])]
  exact ht.2

end

end Li2Lean.P0.Q11Data

#print axioms Li2Lean.P0.Q11Data.q11FrequencyReferenceMeasure_integrable_id
