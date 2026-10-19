/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Construction-backed q = 5 projections for the signed-V reference package.
The decoded rows are fixed to q5D.  Normalization and all analytic evaluator
soundness facts remain explicit inputs; this module only proves projections
of the resulting concrete measure and its already-defined E2/F1 bridges.
-/

import Li2Lean.B3.DEdBridge
import Li2Lean.B3.E1ConcreteInteractions
import Li2Lean.B3.EnergySoundnessFiniteData
import Li2Lean.B3.ReferenceMeasureAtomless
import Li2Lean.V.EnergyCertI.Q5Assembly

namespace Li2Lean

noncomputable section

namespace B3

open V
open V.EnergyCertI
open V.EnergyCertI.IK

/-- The fixed base-range proof used by every q = 5 projection below. -/
theorem q5ReferenceBaseRange : SignedVBaseRange 5 := by
  constructor <;> norm_num

/-- The sole decoded row source for the q = 5 reference measure. -/
def q5DecodedReferenceRows : V13DecodedRows 5 :=
  { data := q5D
    source := Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)) }

/-- The raw measure triple obtained directly from the decoded q = 5 rows. -/
def q5RawReferenceMeasures : V13RawMeasures 5 :=
  v13RefRaw q5DecodedReferenceRows

/-- Normalization is a construction obligation, never a default value. -/
abbrev q5ReferenceNormalizationGoal : Prop :=
  V13MeasureNormalization q5ReferenceBaseRange q5RawReferenceMeasures

/-- The normalized signed measure, when the explicit normalization ledger is
available. -/
def q5ReferenceMeasure (N : q5ReferenceNormalizationGoal) : V.SignedVMeasures :=
  v13RefMeasure q5DecodedReferenceRows N

/-! The concrete normalized measure carries the base index from
`v13RefMeasure`; this is the `q_eq` field of `VReferenceFacts`. -/
theorem q5ReferenceMeasure_q (N : q5ReferenceNormalizationGoal) :
    (q5ReferenceMeasure N).q = 5 := by
  rfl

theorem q5DecodedReferenceRows_data : q5DecodedReferenceRows.data = q5D := rfl

theorem q5RawReferenceMeasures_x :
    q5RawReferenceMeasures.μx = v13DecodedChainMeasure q5D.xp := rfl

theorem q5RawReferenceMeasures_v :
    q5RawReferenceMeasures.μv = v13DecodedChainMeasure q5D.vp := rfl

theorem q5RawReferenceMeasures_z :
    q5RawReferenceMeasures.μz =
      v13DecodedChainMeasure q5D.zp + v13PoissonMeasure q5D.full := rfl

/-! The normalized q = 5 measure keeps the same concrete z decomposition. -/
theorem q5ReferenceMeasure_z_split (N : q5ReferenceNormalizationGoal) :
    (q5ReferenceMeasure N).μz =
      v13DecodedChainMeasure q5D.zp + v13PoissonMeasure q5D.full := by
  rfl

/-! F1 atomlessness is a direct projection of the concrete decoded measure. -/
theorem q5ReferenceMeasure_atomless (N : q5ReferenceNormalizationGoal) :
    (∀ z : ℂ, (q5ReferenceMeasure N).μx {z} = 0) /\
    (∀ z : ℂ, (q5ReferenceMeasure N).μv {z} = 0) /\
    (∀ z : ℂ, (q5ReferenceMeasure N).μz {z} = 0) := by
  simpa [q5ReferenceMeasure] using
    (v13RefMeasure_atomless q5DecodedReferenceRows N)

/-! E2's `.dq` term is tied to this same normalized q = 5 measure. -/
theorem q5ReferenceMeasure_dq_term (N : q5ReferenceNormalizationGoal) :
    vEnergyTerm 5 q5D .dq 0 =
      -V.vCrossInteraction 5 (q5ReferenceMeasure N).μx
        (q5ReferenceMeasure N).μv := by
  rfl

/-! The finite q = 5 decoder identity remains separate from semantic measure
facts, but is available to the package assembly. -/
theorem q5ReferenceMeasure_qlow_value :
    IK.val (qlowQ 5) = (vQlow 5 : ℝ) := by
  exact q5V2Qlow_decodes

end B3

end

end Li2Lean

#print axioms Li2Lean.B3.q5ReferenceMeasure_z_split
#print axioms Li2Lean.B3.q5ReferenceMeasure_atomless
#print axioms Li2Lean.B3.q5ReferenceMeasure_dq_term
