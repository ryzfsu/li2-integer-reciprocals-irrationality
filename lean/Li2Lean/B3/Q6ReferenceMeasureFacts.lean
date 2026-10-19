/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Construction-backed q = 6 projections for the signed-V reference measure.
The row data are concrete; normalization remains an explicit construction
input, so these facts cannot manufacture a measure ledger.
-/

import Li2Lean.B3.EnergySoundnessInputs
import Li2Lean.B3.ReferenceMeasureAtomless
import Li2Lean.V.EnergyCertI.Q6Rows

namespace Li2Lean

noncomputable section

namespace B3

open V
open V.EnergyCertI
open V.EnergyCertI.IK

/-- The fixed base-range proof used by the q = 6 projections. -/
theorem q6ReferenceBaseRange : SignedVBaseRange 6 := by
  constructor <;> norm_num

/-- The concrete decoded row source for q = 6. -/
def q6DecodedReferenceRows : V13DecodedRows 6 :=
  { data := q6D
    source := Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))) }

/-- The raw measure triple obtained directly from the q = 6 decoded rows. -/
def q6RawReferenceMeasures : V13RawMeasures 6 :=
  v13RefRaw q6DecodedReferenceRows

/-- Normalization is a construction obligation, never a default value. -/
abbrev q6ReferenceNormalizationGoal : Prop :=
  V13MeasureNormalization q6ReferenceBaseRange q6RawReferenceMeasures

/-- The normalized signed measure, when its explicit normalization is supplied. -/
def q6ReferenceMeasure (N : q6ReferenceNormalizationGoal) : V.SignedVMeasures :=
  v13RefMeasure q6DecodedReferenceRows N

theorem q6DecodedReferenceRows_data : q6DecodedReferenceRows.data = q6D := rfl

theorem q6RawReferenceMeasures_x :
    q6RawReferenceMeasures.μx = v13DecodedChainMeasure q6D.xp := rfl

theorem q6RawReferenceMeasures_v :
    q6RawReferenceMeasures.μv = v13DecodedChainMeasure q6D.vp := rfl

theorem q6RawReferenceMeasures_z :
    q6RawReferenceMeasures.μz =
      v13DecodedChainMeasure q6D.zp + v13PoissonMeasure q6D.full := rfl

/-! The normalized q = 6 measure retains the concrete z decomposition. -/
theorem q6ReferenceMeasure_z_split (N : q6ReferenceNormalizationGoal) :
    (q6ReferenceMeasure N).μz =
      v13DecodedChainMeasure q6D.zp + v13PoissonMeasure q6D.full := by
  rfl

/-! F1 atomlessness is a direct projection of the same concrete measure. -/
theorem q6ReferenceMeasure_atomless (N : q6ReferenceNormalizationGoal) :
    (∀ z : ℂ, (q6ReferenceMeasure N).μx {z} = 0) /\
    (∀ z : ℂ, (q6ReferenceMeasure N).μv {z} = 0) /\
    (∀ z : ℂ, (q6ReferenceMeasure N).μz {z} = 0) := by
  simpa [q6ReferenceMeasure] using
    (v13RefMeasure_atomless q6DecodedReferenceRows N)

end B3

end

end Li2Lean

#print axioms Li2Lean.B3.q6ReferenceMeasure_z_split
#print axioms Li2Lean.B3.q6ReferenceMeasure_atomless
