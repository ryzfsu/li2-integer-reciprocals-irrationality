/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Construction-backed q = 3 projections for the signed-V reference measure.
The decoded rows are concrete; normalization remains an explicit construction
input, so these projections do not manufacture a complete reference ledger.
-/

import Li2Lean.B3.DEdBridge
import Li2Lean.B3.E1ConcreteInteractions
import Li2Lean.B3.EnergySoundnessFiniteData
import Li2Lean.B3.ReferenceMeasureAtomless
import Li2Lean.B3.V13ChainEnergy
import Li2Lean.B3.V13ReferenceEnergyTerm
import Li2Lean.V.EnergyCertI.Q3Rows

namespace Li2Lean

noncomputable section

namespace B3

open V
open V.EnergyCertI
open V.EnergyCertI.IK
open MeasureTheory Set
open scoped ENNReal

/-- The fixed base-range proof used by every q = 3 projection below. -/
theorem q3ReferenceBaseRange : SignedVBaseRange 3 := by
  constructor <;> norm_num

/-- The sole decoded row source for the q = 3 reference measure. -/
def q3DecodedReferenceRows : V13DecodedRows 3 :=
  { data := q3D
    source := by
      have h : (3 = 3 ∧ q3D = q3D) := ⟨rfl, rfl⟩
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))) }

/-- The raw measure triple obtained directly from the decoded q = 3 rows. -/
def q3RawReferenceMeasures : V13RawMeasures 3 :=
  v13RefRaw q3DecodedReferenceRows

/-- Normalization is a construction obligation, never a default value. -/
abbrev q3ReferenceNormalizationGoal : Prop :=
  V13MeasureNormalization q3ReferenceBaseRange q3RawReferenceMeasures

/-- The normalized signed measure, when its explicit normalization is supplied. -/
def q3ReferenceMeasure (N : q3ReferenceNormalizationGoal) : V.SignedVMeasures :=
  v13RefMeasure q3DecodedReferenceRows N

theorem q3DecodedReferenceRows_data : q3DecodedReferenceRows.data = q3D := rfl

theorem q3RawReferenceMeasures_x :
    q3RawReferenceMeasures.μx = v13DecodedChainMeasure q3D.xp := rfl

theorem q3RawReferenceMeasures_v :
    q3RawReferenceMeasures.μv = v13DecodedChainMeasure q3D.vp := rfl

theorem q3RawReferenceMeasures_z :
    q3RawReferenceMeasures.μz =
      v13DecodedChainMeasure q3D.zp + v13PoissonMeasure q3D.full := rfl

private theorem q3_chain_measure_univ (cells : List V13ChainCell) :
    v13ChainMeasure cells Set.univ =
      (cells.map (fun c => ENNReal.ofReal c.density *
        ENNReal.ofReal (c.right - c.left))).sum := by
  rw [v13ChainMeasure_eq_list_sum]
  induction cells with
  | nil => simp
  | cons c cs ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [Measure.add_apply]
      rw [Measure.smul_apply, Measure.restrict_apply_univ,
        Real.volume_Ioc]
      simp only [smul_eq_mul]
      rw [ih]

private theorem q3_chain_complex_univ (cells : List V13ChainCell) :
    v13ChainMeasureComplex cells Set.univ =
      (cells.map (fun c => ENNReal.ofReal c.density *
        ENNReal.ofReal (c.right - c.left))).sum := by
  unfold v13ChainMeasureComplex
  rw [Measure.map_apply Complex.measurable_ofReal MeasurableSet.univ]
  rw [Set.preimage_univ, q3_chain_measure_univ]

theorem q3ReferenceRaw_x_mass :
    q3RawReferenceMeasures.μx Set.univ = (1 : ℝ≥0∞) := by
  unfold q3RawReferenceMeasures v13RefRaw v13DecodedChainMeasure
    v13ChainMeasureComplex
  rw [Measure.map_apply Complex.measurable_ofReal MeasurableSet.univ]
  rw [Set.preimage_univ, q3_chain_measure_univ]
  norm_num [v13ChainCells, v13ChainCellsAux, q3DecodedReferenceRows, q3D, mkIData, chainCP,
    chainCoords, chainMassU, densI, jumpsI, q3XHeader,
    q3XEntries, U, Li2Lean.V.Q2Certificate.decodeChain,
    Li2Lean.V.Q2Certificate.decodeChainAux,
    Li2Lean.V.Q2Certificate.scaleMass,
    Li2Lean.V.Q2Certificate.scaleLength,
    Li2Lean.V.Q2Certificate.correctedLength,
    IK.qsub, IK.qadd, IK.qneg, IK.val,
    ENNReal.ofReal_mul]
  try simp (disch := positivity) only [← ENNReal.ofReal_mul]
  try simp (disch := positivity) only [← ENNReal.ofReal_add]
  norm_num

/-! The normalized q = 3 measure retains the concrete z decomposition. -/
theorem q3ReferenceMeasure_z_split (N : q3ReferenceNormalizationGoal) :
    (q3ReferenceMeasure N).μz =
      v13DecodedChainMeasure q3D.zp + v13PoissonMeasure q3D.full := by
  rfl

/-! F1 atomlessness is a direct projection of the same concrete measure. -/
theorem q3ReferenceMeasure_atomless (N : q3ReferenceNormalizationGoal) :
    (∀ z : ℂ, (q3ReferenceMeasure N).μx {z} = 0) /\
    (∀ z : ℂ, (q3ReferenceMeasure N).μv {z} = 0) /\
    (∀ z : ℂ, (q3ReferenceMeasure N).μz {z} = 0) := by
  simpa [q3ReferenceMeasure] using
    (v13RefMeasure_atomless q3DecodedReferenceRows N)

/-! E2's `.dq` term is tied to this same normalized q = 3 measure. -/
theorem q3ReferenceMeasure_dq_term (N : q3ReferenceNormalizationGoal) :
    vEnergyTerm 3 q3D .dq 0 =
      -V.vCrossInteraction 3 (q3ReferenceMeasure N).μx
        (q3ReferenceMeasure N).μv := by
  rfl

/-! The finite q = 3 decoder identity remains separate from semantic measure
facts, but is available to the package assembly. -/
theorem q3ReferenceMeasure_qlow_value :
    IK.val (qlowQ 3) = (vQlow 3 : ℝ) := by
  norm_num [IK.val, qlowQ, vQlow]

end B3

end

end Li2Lean

#print axioms Li2Lean.B3.q3ReferenceMeasure_z_split
#print axioms Li2Lean.B3.q3ReferenceMeasure_atomless
#print axioms Li2Lean.B3.q3ReferenceMeasure_dq_term
