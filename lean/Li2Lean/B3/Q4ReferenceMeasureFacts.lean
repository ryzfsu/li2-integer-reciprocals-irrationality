/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Construction-bound q = 4 measure projections for the v13 reference data.
This module keeps normalization as an explicit proposition.  It proves the
measure-level F1 atomlessness and source projections once that normalization
is supplied; it does not claim the missing q4 F/E/T ledger.
-/

import Li2Lean.B3.EnergySoundnessInputs
import Li2Lean.B3.ReferenceMeasureAtomless
import Li2Lean.V.EnergyCertI.Q4Rows

namespace Li2Lean

noncomputable section

namespace B3

open V
open V.EnergyCertI
open V.EnergyCertI.IK

/-- The signed base range used by the q = 4 reference construction. -/
theorem q4ReferenceBaseRange : SignedVBaseRange 4 := by
  constructor <;> norm_num

/-- The raw q = 4 measure triple obtained from the decoded v13 rows. -/
def q4RawReferenceMeasures : V13RawMeasures 4 :=
  v13RefRaw q4DecodedRows

/-- Normalization remains an explicit construction obligation. -/
abbrev q4ReferenceNormalizationGoal : Prop :=
  V13MeasureNormalization q4ReferenceBaseRange q4RawReferenceMeasures

/-- The normalized q = 4 measure, when its normalization ledger is supplied. -/
def q4ReferenceMeasure (N : q4ReferenceNormalizationGoal) : V.SignedVMeasures :=
  v13RefMeasure q4DecodedRows N

theorem q4DecodedRows_data : q4DecodedRows.data = q4D := rfl

theorem q4RawReferenceMeasures_x :
    q4RawReferenceMeasures.μx = v13DecodedChainMeasure q4D.xp := rfl

theorem q4RawReferenceMeasures_v :
    q4RawReferenceMeasures.μv = v13DecodedChainMeasure q4D.vp := rfl

theorem q4RawReferenceMeasures_z :
    q4RawReferenceMeasures.μz =
      v13DecodedChainMeasure q4D.zp + v13PoissonMeasure q4D.full := rfl

theorem q4ReferenceMeasure_q (N : q4ReferenceNormalizationGoal) :
    (q4ReferenceMeasure N).q = 4 := by
  rfl

/-! F1 atomlessness is a direct projection of the concrete decoded measure. -/
theorem q4ReferenceMeasure_atomless (N : q4ReferenceNormalizationGoal) :
    (∀ z : ℂ, (q4ReferenceMeasure N).μx {z} = 0) ∧
    (∀ z : ℂ, (q4ReferenceMeasure N).μv {z} = 0) ∧
    (∀ z : ℂ, (q4ReferenceMeasure N).μz {z} = 0) := by
  simpa [q4ReferenceMeasure] using
    (v13RefMeasure_atomless q4DecodedRows N)

/-! F5's z projection keeps the chain and Poisson components on one measure. -/
theorem q4ReferenceMeasure_z_split (N : q4ReferenceNormalizationGoal) :
    (q4ReferenceMeasure N).μz =
      v13DecodedChainMeasure q4D.zp + v13PoissonMeasure q4D.full := by
  rfl

/-! The q4 qlow equality is a finite decoder fact, independent of the ledger. -/
theorem q4ReferenceMeasure_qlow_value :
    IK.val (qlowQ 4) = (vQlow 4 : ℝ) := by
  norm_num [IK.val, qlowQ, vQlow]

end B3

end

end Li2Lean

#print axioms Li2Lean.B3.q4ReferenceMeasure_atomless
#print axioms Li2Lean.B3.q4ReferenceMeasure_z_split
#print axioms Li2Lean.B3.q4ReferenceMeasure_qlow_value
