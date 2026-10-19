/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B3.Q6ReferenceNormalization
import Li2Lean.B3.ReferenceMeasureSupportCircle

namespace Li2Lean.B3

noncomputable section

open MeasureTheory Set
open V.EnergyCertI

/- The q6 x/v-chain cells lie in the exact v13 lower-support intervals,
following the printed q6 row tables in `v-reference-data.tex:1-430`. The
measure support conclusions reuse the generic decoded-cell theorem from
`ReferenceMeasureSupportCircle.lean`, as the q4 support lemmas do. -/
set_option maxHeartbeats 2000000 in
theorem v13_q6_x_bounds :
    ∀ c ∈ v13ChainCells q6D.xp,
      vXLow 6 ≤ c.left ∧ c.right ≤ 1 := by
  norm_num [vXLow, q6D, mkIData, v13ChainCells, v13ChainCellsAux, chainCP,
    chainCoords, chainMassU, densI, jumpsI, q6XHeader, q6XEntries,
    Li2Lean.V.Q2Certificate.decodeChain,
    Li2Lean.V.Q2Certificate.decodeChainAux,
    Li2Lean.V.Q2Certificate.scaleMass,
    Li2Lean.V.Q2Certificate.scaleLength,
    Li2Lean.V.Q2Certificate.correctedLength,
    IK.qsub, IK.qadd, IK.qneg, IK.val, U]

theorem q6ReferenceMeasure_x_support_low
    (N : q6ReferenceNormalizationGoal) :
    (q6ReferenceMeasure N).μx
      (Complex.ofReal '' Icc (vXLow 6) 1)ᶜ = 0 := by
  change v13DecodedChainMeasure q6D.xp
    (Complex.ofReal '' Icc (vXLow 6) 1)ᶜ = 0
  apply v13DecodedChainMeasure_outside_of_cells
  intro c hc
  exact v13_q6_x_bounds c hc

theorem q6ReferenceMeasure_x_support_full
    (N : q6ReferenceNormalizationGoal) :
    (q6ReferenceMeasure N).μx
      (Complex.ofReal '' Icc (0 : ℝ) 1)ᶜ = 0 := by
  have hlow := q6ReferenceMeasure_x_support_low N
  have hnonneg : (0 : ℝ) ≤ vXLow 6 := by
    norm_num [vXLow]
  apply measure_mono_null
    (show (Complex.ofReal '' Icc (0 : ℝ) 1)ᶜ ⊆
        (Complex.ofReal '' Icc (vXLow 6) 1)ᶜ by
      intro z hzfull
      change z ∉ (Complex.ofReal '' Icc (0 : ℝ) 1) at hzfull
      change z ∉ (Complex.ofReal '' Icc (vXLow 6) 1)
      intro hzlow
      rcases hzlow with ⟨x, hx, rfl⟩
      apply hzfull
      refine ⟨x, ?_, rfl⟩
      exact ⟨le_trans hnonneg hx.1, hx.2⟩)
    hlow

set_option maxHeartbeats 2000000 in
theorem v13_q6_v_bounds :
    ∀ c ∈ v13ChainCells q6D.vp,
      vVLow 6 ≤ c.left ∧ c.right ≤ 1 := by
  norm_num [vVLow, q6D, mkIData, v13ChainCells, v13ChainCellsAux, chainCP,
    chainCoords, chainMassU, densI, jumpsI, q6YHeader, q6YEntries,
    Li2Lean.V.Q2Certificate.decodeChain,
    Li2Lean.V.Q2Certificate.decodeChainAux,
    Li2Lean.V.Q2Certificate.scaleMass,
    Li2Lean.V.Q2Certificate.scaleLength,
    Li2Lean.V.Q2Certificate.correctedLength,
    IK.qsub, IK.qadd, IK.qneg, IK.val, U]

theorem q6ReferenceMeasure_v_support_low
    (N : q6ReferenceNormalizationGoal) :
    (q6ReferenceMeasure N).μv
      (Complex.ofReal '' Icc (vVLow 6) 1)ᶜ = 0 := by
  change v13DecodedChainMeasure q6D.vp
    (Complex.ofReal '' Icc (vVLow 6) 1)ᶜ = 0
  apply v13DecodedChainMeasure_outside_of_cells
  intro c hc
  exact v13_q6_v_bounds c hc

theorem q6ReferenceMeasure_v_support_full
    (N : q6ReferenceNormalizationGoal) :
    (q6ReferenceMeasure N).μv
      (Complex.ofReal '' Icc (0 : ℝ) 1)ᶜ = 0 := by
  apply measure_mono_null (t := (Complex.ofReal '' Icc (vVLow 6) 1)ᶜ)
  · intro z hzFull
    change z ∉ Complex.ofReal '' Icc (vVLow 6) 1
    intro hzLow
    apply hzFull
    rcases hzLow with ⟨x, hx, rfl⟩
    refine ⟨x, ?_, rfl⟩
    constructor
    · have hlow : (0 : ℝ) ≤ vVLow 6 := by norm_num [vVLow]
      exact hlow.trans hx.1
    · exact hx.2
  · exact q6ReferenceMeasure_v_support_low N

/-! The q6 z-chain endpoint check is the structural row bound for
the common reference-package constructor.  It is the direct finite check of
the q6 table in `v-reference-data.tex:293-362`. -/
set_option maxHeartbeats 2000000 in
theorem v13_q6_z_source_bounds :
    ∀ c ∈ v13ChainCells q6D.zp,
      (-6 : ℝ) ≤ c.left ∧ c.right ≤ -(3 / 5 : ℝ) := by
  norm_num [q6D, mkIData, v13ChainCells, v13ChainCellsAux, chainCP,
    q6ZHeader, q6ZEntries, chainCoords, chainMassU, densI, jumpsI,
    Li2Lean.V.Q2Certificate.decodeChain,
    Li2Lean.V.Q2Certificate.decodeChainAux,
    Li2Lean.V.Q2Certificate.scaleMass,
    Li2Lean.V.Q2Certificate.scaleLength,
    Li2Lean.V.Q2Certificate.correctedLength,
    IK.qsub, IK.qadd, IK.qneg, IK.val, U]

end

end Li2Lean.B3

#print axioms Li2Lean.B3.v13_q6_x_bounds
#print axioms Li2Lean.B3.q6ReferenceMeasure_x_support_low
#print axioms Li2Lean.B3.q6ReferenceMeasure_x_support_full
#print axioms Li2Lean.B3.v13_q6_v_bounds
#print axioms Li2Lean.B3.q6ReferenceMeasure_v_support_low
#print axioms Li2Lean.B3.q6ReferenceMeasure_v_support_full
#print axioms Li2Lean.B3.v13_q6_z_source_bounds
