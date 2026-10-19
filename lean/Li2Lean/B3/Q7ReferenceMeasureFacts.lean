/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Semantic facts for the concrete q = 7 reference measure.
-/

import Li2Lean.B3.ReferenceMeasureAtomless
import Li2Lean.B3.ReferenceMeasureSupportCircle
import Li2Lean.B3.Q7ReferenceNormalization
import Li2Lean.B3.ReferencePackageGeneric

namespace Li2Lean.B3

noncomputable section

open MeasureTheory Set
open V.EnergyCertI
open V.EnergyCertI.IK

/-- The normalized signed measure built from the decoded q = 7 rows. -/
def q7ReferenceMeasure (N : q7ReferenceNormalizationGoal) :
    V.SignedVMeasures :=
  v13RefMeasure q7ReferenceRows N

/-! The concrete normalized measure carries the base index from
`v13RefMeasure`; this is the `q_eq` field of `VReferenceFacts`. -/
theorem q7ReferenceMeasure_q (N : q7ReferenceNormalizationGoal) :
    (q7ReferenceMeasure N).q = 7 := by
  rfl

/-- The q = 7 reference measure is atomless in each component. -/
theorem q7ReferenceMeasure_atomless (N : q7ReferenceNormalizationGoal) :
    (∀ z : ℂ, (q7ReferenceMeasure N).μx {z} = 0) ∧
    (∀ z : ℂ, (q7ReferenceMeasure N).μv {z} = 0) ∧
    (∀ z : ℂ, (q7ReferenceMeasure N).μz {z} = 0) := by
  simpa [q7ReferenceMeasure] using
    (v13RefMeasure_atomless q7ReferenceRows N)

/-! The q7 qlow equality is a finite decoder fact, independent of the
measure-attached field and energy ledgers. -/
theorem q7ReferenceMeasure_qlow_value :
    IK.val (qlowQ 7) = (vQlow 7 : ℝ) := by
  norm_num [IK.val, qlowQ, vQlow]

/-! The q7 x-chain starts at its printed lower support endpoint and ends at
one; the generic chain-support theorem turns the checked cells into F1. -/
set_option maxHeartbeats 2000000 in
theorem v13_q7_x_bounds :
    ∀ c ∈ v13ChainCells q7D.xp,
      ((3349364905389 : ℝ) / (5 * 10 ^ 13)) ≤ c.left ∧ c.right ≤ 1 := by
  norm_num [q7D, mkIData, v13ChainCells, v13ChainCellsAux, chainCP,
    chainCoords, chainMassU, densI, jumpsI, q7XHeader, q7XEntries,
    Li2Lean.V.Q2Certificate.decodeChain,
    Li2Lean.V.Q2Certificate.decodeChainAux,
    Li2Lean.V.Q2Certificate.scaleMass,
    Li2Lean.V.Q2Certificate.scaleLength,
    Li2Lean.V.Q2Certificate.correctedLength,
    IK.qsub, IK.qadd, IK.qneg, IK.val, U]

set_option maxHeartbeats 2000000 in
theorem v13_q7_v_bounds :
    ∀ c ∈ v13ChainCells q7D.vp,
      (480367989919 : ℝ) / (5 * 10 ^ 13) ≤ c.left ∧ c.right ≤ 1 := by
  norm_num [q7D, mkIData, v13ChainCells, v13ChainCellsAux, chainCP,
    q7YHeader, q7YEntries, chainCoords, chainMassU, densI, jumpsI,
    Li2Lean.V.Q2Certificate.decodeChain,
    Li2Lean.V.Q2Certificate.decodeChainAux,
    Li2Lean.V.Q2Certificate.scaleMass,
    Li2Lean.V.Q2Certificate.scaleLength,
    Li2Lean.V.Q2Certificate.correctedLength,
    IK.qsub, IK.qadd, IK.qneg, IK.val, U]

/-! The q7 z-chain bounds are the finite endpoint check for the q = 7 row
table in v13 `v-reference-data.tex`; the common support lemma then handles
the associated decoded chain measure. -/
set_option maxHeartbeats 2000000 in
theorem v13_q7_z_source_bounds :
    ∀ c ∈ v13ChainCells q7D.zp,
      (-7 : ℝ) ≤ c.left ∧ c.right ≤ -(3 / 5 : ℝ) := by
  norm_num [q7D, mkIData, v13ChainCells, v13ChainCellsAux, chainCP,
    q7ZHeader, q7ZEntries, chainCoords, chainMassU, densI, jumpsI,
    Li2Lean.V.Q2Certificate.decodeChain,
    Li2Lean.V.Q2Certificate.decodeChainAux,
    Li2Lean.V.Q2Certificate.scaleMass,
    Li2Lean.V.Q2Certificate.scaleLength,
    Li2Lean.V.Q2Certificate.correctedLength,
    IK.qsub, IK.qadd, IK.qneg, IK.val, U]

/-! The row-bound record is a finite consequence of the same q7 decoded
chain bounds used by the support lemmas above. Keeping it here avoids the
heavy all-q leaf module when compiling the q7 adapter. -/
set_option maxHeartbeats 2000000 in
theorem q7_decoded_row_bounds_adapter :
    V13DecodedRowBounds 7 q7ReferenceRows := by
  refine {
    x_low := ?_
    x_full := ?_
    v_low := ?_
    v_full := ?_
    z_source := ?_ }
  · intro c hc
    have hc' : c ∈ v13ChainCells q7D.xp := by
      simpa only [q7ReferenceRows] using hc
    have h := v13_q7_x_bounds c hc'
    simpa [q7ReferenceRows, vXLow] using h
  · intro c hc
    have hc' : c ∈ v13ChainCells q7D.xp := by
      simpa only [q7ReferenceRows] using hc
    have h := v13_q7_x_bounds c hc'
    have hlow : (0 : ℝ) ≤ vXLow 7 := by norm_num [vXLow]
    exact ⟨hlow.trans (by simpa [q7ReferenceRows, vXLow] using h.1), h.2⟩
  · intro c hc
    have hc' : c ∈ v13ChainCells q7D.vp := by
      simpa only [q7ReferenceRows] using hc
    have h := v13_q7_v_bounds c hc'
    simpa [q7ReferenceRows, vVLow] using h
  · intro c hc
    have hc' : c ∈ v13ChainCells q7D.vp := by
      simpa only [q7ReferenceRows] using hc
    have h := v13_q7_v_bounds c hc'
    have hlow : (0 : ℝ) ≤ vVLow 7 := by norm_num [vVLow]
    exact ⟨hlow.trans (by simpa [q7ReferenceRows, vVLow] using h.1), h.2⟩
  · intro c hc
    have hc' : c ∈ v13ChainCells q7D.zp := by
      simpa only [q7ReferenceRows] using hc
    simpa [q7ReferenceRows] using v13_q7_z_source_bounds c hc'

/-- The q7 x component is supported above the printed v13 lower endpoint. -/
theorem q7ReferenceMeasure_x_support_low
    (N : q7ReferenceNormalizationGoal) :
    (q7ReferenceMeasure N).μx
      (Complex.ofReal '' Icc (vXLow 7) 1)ᶜ = 0 := by
  change v13DecodedChainMeasure q7D.xp
    (Complex.ofReal '' Icc (vXLow 7) 1)ᶜ = 0
  apply v13DecodedChainMeasure_outside_of_cells
  intro c hc
  have h := v13_q7_x_bounds c hc
  simpa [vXLow] using h

/-- The q7 v component is supported above the printed v13 lower endpoint. -/
theorem q7ReferenceMeasure_v_support_low
    (N : q7ReferenceNormalizationGoal) :
    (q7ReferenceMeasure N).μv
      (Complex.ofReal '' Icc (vVLow 7) 1)ᶜ = 0 := by
  change v13DecodedChainMeasure q7D.vp
    (Complex.ofReal '' Icc (vVLow 7) 1)ᶜ = 0
  apply v13DecodedChainMeasure_outside_of_cells
  intro c hc
  have h := v13_q7_v_bounds c hc
  simpa [vVLow] using h

/-- The q7 z-chain and Poisson part lie in the v13 source support set. -/
theorem q7ReferenceMeasure_z_support_low
    (N : q7ReferenceNormalizationGoal) :
    (q7ReferenceMeasure N).μz
      ((Complex.ofReal '' Icc (-(7 : ℝ)) (-3 / 5)) ∪
        Metric.sphere 0 (3 / 5))ᶜ = 0 := by
  let hzSourceSet : Set ℂ :=
    (Complex.ofReal '' Icc (-(7 : ℝ)) (-3 / 5)) ∪
      Metric.sphere 0 (3 / 5)
  have hzCells : ∀ c ∈ v13ChainCells q7ReferenceRows.data.zp,
      (-(7 : ℝ)) ≤ c.left ∧ c.right ≤ (-3 / 5 : ℝ) := by
    intro c hc
    have hc' : c ∈ v13ChainCells q7D.zp := by
      simpa only [q7ReferenceRows] using hc
    have h := v13_q7_z_source_bounds c hc'
    exact ⟨h.1, by norm_num at h ⊢; exact h.2⟩
  have hzChain : v13DecodedChainMeasure q7ReferenceRows.data.zp
      (Complex.ofReal '' Icc (-(7 : ℝ)) (-3 / 5))ᶜ = 0 :=
    v13DecodedChainMeasure_outside_of_cells _ _ _ hzCells
  have hzChain' : v13DecodedChainMeasure q7ReferenceRows.data.zp
      hzSourceSetᶜ = 0 :=
    measure_mono_null
      (by
        intro z hzS hzImage
        exact hzS (Or.inl hzImage)) hzChain
  have hpoisson : v13PoissonMeasure q7ReferenceRows.data.full
      (Metric.sphere 0 v13GlobalPoissonRadius)ᶜ = 0 :=
    v13GlobalPoissonMeasure_outside_sphere q7ReferenceRows.data.full
  have hpoisson' : v13PoissonMeasure q7ReferenceRows.data.full
      hzSourceSetᶜ = 0 :=
    measure_mono_null
      (by
        intro z hzS
        change z ∉ Metric.sphere 0 (3 / 5)
        intro hzSphere
        exact hzS (Or.inr hzSphere))
      hpoisson
  have hzRaw : (v13RefRaw q7ReferenceRows).μz hzSourceSetᶜ = 0 := by
    change (v13DecodedChainMeasure q7ReferenceRows.data.zp +
      v13PoissonMeasure q7ReferenceRows.data.full) hzSourceSetᶜ = 0
    rw [Measure.add_apply, hzChain', hpoisson', zero_add]
  have hzMeasure : (q7ReferenceMeasure N).μz hzSourceSetᶜ = 0 := by
    have hraw : (v13RefMeasure q7ReferenceRows N).μz =
        (v13RefRaw q7ReferenceRows).μz := rfl
    rw [q7ReferenceMeasure, hraw]
    exact hzRaw
  simpa [hzSourceSet] using hzMeasure

/-! The six support fields of `VReferenceFacts` for q = 7.  These are all
finite consequences of the q7 row bounds and the common source-to-contour
bridge; they do not supply any ball, energy, field, endpoint, or integrability
input. -/
set_option maxRecDepth 100000 in
theorem q7ReferenceMeasure_supports
    (N : q7ReferenceNormalizationGoal) :
    (q7ReferenceMeasure N).μx (Complex.ofReal '' Icc (vXLow 7) 1)ᶜ = 0 ∧
    (q7ReferenceMeasure N).μv (Complex.ofReal '' Icc (vVLow 7) 1)ᶜ = 0 ∧
    (q7ReferenceMeasure N).μz
      ((Complex.ofReal '' Icc (-(7 : ℝ)) (-3 / 5)) ∪
        Metric.sphere 0 (3 / 5))ᶜ = 0 ∧
    (q7ReferenceMeasure N).μx
      (Complex.ofReal '' Icc (0 : ℝ) 1)ᶜ = 0 ∧
    (q7ReferenceMeasure N).μv
      (Complex.ofReal '' Icc (0 : ℝ) 1)ᶜ = 0 ∧
    (q7ReferenceMeasure N).μz (V.vContourTrace 7)ᶜ = 0 := by
  have hxLow : ∀ c ∈ v13ChainCells q7D.xp,
      vXLow 7 ≤ c.left ∧ c.right ≤ 1 := by
    intro c hc
    have h := v13_q7_x_bounds c hc
    simpa [vXLow] using h
  have hxFull : ∀ c ∈ v13ChainCells q7D.xp,
      (0 : ℝ) ≤ c.left ∧ c.right ≤ 1 := by
    intro c hc
    have h := hxLow c hc
    have hlow : (0 : ℝ) ≤ vXLow 7 := by norm_num [vXLow]
    exact ⟨hlow.trans h.1, h.2⟩
  have hvLow : ∀ c ∈ v13ChainCells q7D.vp,
      vVLow 7 ≤ c.left ∧ c.right ≤ 1 := by
    intro c hc
    have h := v13_q7_v_bounds c hc
    simpa [vVLow] using h
  have hvFull : ∀ c ∈ v13ChainCells q7D.vp,
      (0 : ℝ) ≤ c.left ∧ c.right ≤ 1 := by
    intro c hc
    have h := hvLow c hc
    have hlow : (0 : ℝ) ≤ vVLow 7 := by norm_num [vVLow]
    exact ⟨hlow.trans h.1, h.2⟩
  have hzSource : ∀ c ∈ v13ChainCells q7D.zp,
      (-(7 : ℝ)) ≤ c.left ∧ c.right ≤ -(3 / 5 : ℝ) := by
    intro c hc
    exact v13_q7_z_source_bounds c hc
  have h := v13RefMeasure_supports_of_bounds
      (q := 7) (hq := q7ReferenceBaseRange)
      q7ReferenceRows N (vXLow 7) (vVLow 7)
      hxLow hxFull hvLow hvFull hzSource
  change
    (v13RefMeasure q7ReferenceRows N).μx
        (Complex.ofReal '' Icc (vXLow 7) 1)ᶜ = 0 ∧
      (v13RefMeasure q7ReferenceRows N).μv
        (Complex.ofReal '' Icc (vVLow 7) 1)ᶜ = 0 ∧
      (v13RefMeasure q7ReferenceRows N).μz
        ((Complex.ofReal '' Icc (-(7 : ℝ)) (-3 / 5)) ∪
          Metric.sphere 0 (3 / 5))ᶜ = 0 ∧
      (v13RefMeasure q7ReferenceRows N).μx
        (Complex.ofReal '' Icc (0 : ℝ) 1)ᶜ = 0 ∧
      (v13RefMeasure q7ReferenceRows N).μv
        (Complex.ofReal '' Icc (0 : ℝ) 1)ᶜ = 0 ∧
      (v13RefMeasure q7ReferenceRows N).μz (V.vContourTrace 7)ᶜ = 0
  exact h

end

end Li2Lean.B3

#print axioms Li2Lean.B3.q7ReferenceMeasure_atomless
#print axioms Li2Lean.B3.q7ReferenceMeasure_qlow_value
#print axioms Li2Lean.B3.q7ReferenceMeasure_x_support_low
#print axioms Li2Lean.B3.q7ReferenceMeasure_v_support_low
#print axioms Li2Lean.B3.v13_q7_z_source_bounds
#print axioms Li2Lean.B3.q7ReferenceMeasure_z_support_low
#print axioms Li2Lean.B3.q7ReferenceMeasure_supports
