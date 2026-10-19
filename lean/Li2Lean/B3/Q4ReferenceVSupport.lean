/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B3.Q4ReferenceSupportLow

namespace Li2Lean.B3

noncomputable section

open MeasureTheory Set
open V.EnergyCertI

set_option maxHeartbeats 2000000 in
theorem v13_q4_v_bounds :
    ∀ c ∈ v13ChainCells q4D.vp,
      vVLow 4 ≤ c.left ∧ c.right ≤ 1 := by
  norm_num [vVLow, q4D, mkIData, v13ChainCells, v13ChainCellsAux, chainCP,
    chainCoords, chainMassU, densI, jumpsI, q4YHeader, q4YEntries,
    Li2Lean.V.Q2Certificate.decodeChain,
    Li2Lean.V.Q2Certificate.decodeChainAux,
    Li2Lean.V.Q2Certificate.scaleMass,
    Li2Lean.V.Q2Certificate.scaleLength,
    Li2Lean.V.Q2Certificate.correctedLength,
    IK.qsub, IK.qadd, IK.qneg, IK.val, U]

theorem q4ReferenceMeasure_v_support_low
    (N : q4ReferenceNormalizationGoal) :
    (q4ReferenceMeasure N).μv
      (Complex.ofReal '' Icc (vVLow 4) 1)ᶜ = 0 := by
  change v13DecodedChainMeasure q4D.vp
    (Complex.ofReal '' Icc (vVLow 4) 1)ᶜ = 0
  apply v13DecodedChainMeasure_outside_of_cells
  intro c hc
  exact v13_q4_v_bounds c hc

/-- The low-support interval is contained in the full unit interval. -/
theorem q4ReferenceMeasure_v_support_full
    (N : q4ReferenceNormalizationGoal) :
    (q4ReferenceMeasure N).μv
      (Complex.ofReal '' Icc (0 : ℝ) 1)ᶜ = 0 := by
  apply measure_mono_null (t := (Complex.ofReal '' Icc (vVLow 4) 1)ᶜ)
  · intro z hzFull
    change z ∉ Complex.ofReal '' Icc (vVLow 4) 1
    intro hzLow
    apply hzFull
    rcases hzLow with ⟨x, hx, rfl⟩
    refine ⟨x, ?_, rfl⟩
    constructor
    · have hlow : (0 : ℝ) ≤ vVLow 4 := by norm_num [vVLow]
      exact hlow.trans hx.1
    · exact hx.2
  · exact q4ReferenceMeasure_v_support_low N

end

end Li2Lean.B3

#print axioms Li2Lean.B3.q4ReferenceMeasure_v_support_low
