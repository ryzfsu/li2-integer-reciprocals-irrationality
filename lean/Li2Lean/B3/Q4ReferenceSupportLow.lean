/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B3.Q4ReferenceMeasureFacts
import Li2Lean.B3.ReferenceMeasureSupportCircle

namespace Li2Lean.B3

noncomputable section

open MeasureTheory Set
open V.EnergyCertI

/-! Every q4 x-chain cell lies in the printed lower-support interval.

The finite expansion is the q4 x row table from `v-reference-data.tex:154-223`.
The scale is the decoder scale `U` used by `Q4Rows`. -/
set_option maxHeartbeats 2000000 in
theorem v13_q4_x_bounds :
    ∀ c ∈ v13ChainCells q4D.xp,
      ((3349364905389 : ℝ) / (5 * 10 ^ 13)) ≤ c.left ∧ c.right ≤ 1 := by
  norm_num [q4D, mkIData, v13ChainCells, v13ChainCellsAux, chainCP,
    chainCoords, chainMassU, densI, jumpsI, q4XHeader, q4XEntries,
    Li2Lean.V.Q2Certificate.decodeChain,
    Li2Lean.V.Q2Certificate.decodeChainAux,
    Li2Lean.V.Q2Certificate.scaleMass,
    Li2Lean.V.Q2Certificate.scaleLength,
    Li2Lean.V.Q2Certificate.correctedLength,
    IK.qsub, IK.qadd, IK.qneg, IK.val, U]

/-- The concrete q4 reference x measure is supported above the v13 lower
endpoint, independently of the other field, energy, and endpoint ledgers. -/
theorem q4ReferenceMeasure_x_support_low
    (N : q4ReferenceNormalizationGoal) :
    (q4ReferenceMeasure N).μx
      (Complex.ofReal '' Icc (vXLow 4) 1)ᶜ = 0 := by
  change v13DecodedChainMeasure q4D.xp
    (Complex.ofReal '' Icc (vXLow 4) 1)ᶜ = 0
  apply v13DecodedChainMeasure_outside_of_cells
  intro c hc
  have h := v13_q4_x_bounds c hc
  simpa [vXLow] using h

end

end Li2Lean.B3
