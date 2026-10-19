/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Concrete q = 11 lower bounds for the three logarithmic-energy components
covered by the rectangular interval certificate.  The bounds are the
outward rational endpoints from v13 p0-analytic.tex:749-826 and are proved
by the `decide +kernel` rectangle checks in `R3Q11QLogRectangles`.
-/

import Li2Lean.AllN.R3Q11QLogRectangles
import Li2Lean.P0.Q11QLogEnvelopeProducer

namespace Li2Lean.P0.Q11Data

noncomputable section

/-! The lower endpoints used in `Q11QLogEnvelopeInputs`.  Keeping these as
named `IntRatio`s lets the producer perform the same integer cross-product
checks as the other q = 11 certificate fields. -/
def q11LowerPinnedPinned : IntRatio :=
  ⟨-573876243, 1000000000⟩

def q11LowerFrequencyFrequency : IntRatio :=
  ⟨-1013277437, 1000000000⟩

def q11LowerPinnedFrequency : IntRatio :=
  ⟨408988084, 1000000000⟩

theorem q11LowerPinnedPinned_den_pos : 0 < q11LowerPinnedPinned.den := by
  decide +kernel

theorem q11LowerFrequencyFrequency_den_pos :
    0 < q11LowerFrequencyFrequency.den := by
  decide +kernel

theorem q11LowerPinnedFrequency_den_pos :
    0 < q11LowerPinnedFrequency.den := by
  decide +kernel

theorem q11LowerPinnedPinned_le :
    ratioToReal q11LowerPinnedPinned ≤ q11Eκκ := by
  simpa [q11LowerPinnedPinned, ratioToReal] using q11Eκκ_bounds.1

theorem q11LowerFrequencyFrequency_le :
    ratioToReal q11LowerFrequencyFrequency ≤ q11Eμμ := by
  simpa [q11LowerFrequencyFrequency, ratioToReal] using q11Eμμ_bounds.1

theorem q11LowerPinnedFrequency_le :
    ratioToReal q11LowerPinnedFrequency ≤ q11Eκμ := by
  simpa [q11LowerPinnedFrequency, ratioToReal] using q11Eκμ_bounds.1

end

end Li2Lean.P0.Q11Data

#print axioms Li2Lean.P0.Q11Data.q11LowerPinnedPinned_le
#print axioms Li2Lean.P0.Q11Data.q11LowerFrequencyFrequency_le
#print axioms Li2Lean.P0.Q11Data.q11LowerPinnedFrequency_le
