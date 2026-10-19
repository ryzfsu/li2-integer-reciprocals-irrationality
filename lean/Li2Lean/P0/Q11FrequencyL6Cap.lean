/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.Mu0Cap
import Li2Lean.P0.Q11MeasureDomination

open MeasureTheory Set
open scoped ENNReal

namespace Li2Lean.P0.Q11Data

noncomputable section

/-!
The q = 11 frequency reference measure inherits the half-line positive-kernel
cap from the same density comparison used in the dual construction.  This is
the frequency part of the cross-energy input in v13 `p0-analytic.tex:244-255`.
-/

theorem q11Frequency_l6PosKernel_bound :
    ∀ z : ℂ,
      (∫⁻ w, L6Variations.l6PosKernel z w ∂
        p0ReflectedFrequencyMeasure q11FrequencyReferenceMeasure) ≤
        ENNReal.ofReal 2 := by
  have hμ : q11FrequencyReferenceMeasure ≤
      volume.restrict (Set.Ici (1 / 2 : ℝ)) := by
    exact q11FrequencyReferenceMeasure_le_restrict.trans
      (Measure.restrict_mono Set.Icc_subset_Ici_self le_rfl)
  exact frequencyReference_l6PosKernel_bound_of_density_le_one
    q11FrequencyReferenceMeasure hμ frequencyHalfLineOneDimensionalCap_proof

end

end Li2Lean.P0.Q11Data

#print axioms Li2Lean.P0.Q11Data.q11Frequency_l6PosKernel_bound
