/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B3.Q4ReferenceMeasureFacts

namespace Li2Lean.B3

noncomputable section

open MeasureTheory Set
open V.EnergyCertI

/-! Every decoded q4 z-chain cell stays in the source interval printed in
`v-reference-data.tex:154-223`.  This is the finite integer-table check used
as the `hzSource` input to `v13RefMeasure_supports_of_bounds`. -/
set_option maxHeartbeats 2000000 in
theorem v13_q4_z_source_bounds :
    ∀ c ∈ v13ChainCells q4D.zp,
      (-4 : ℝ) ≤ c.left ∧ c.right ≤ -(3 / 5 : ℝ) := by
  norm_num [q4D, mkIData, v13ChainCells, v13ChainCellsAux, chainCP,
    chainCoords, chainMassU, densI, jumpsI, q4ZHeader, q4ZEntries,
    Li2Lean.V.Q2Certificate.decodeChain,
    Li2Lean.V.Q2Certificate.decodeChainAux,
    Li2Lean.V.Q2Certificate.scaleMass,
    Li2Lean.V.Q2Certificate.scaleLength,
    Li2Lean.V.Q2Certificate.correctedLength,
    IK.qsub, IK.qadd, IK.qneg, IK.val, U]

end

end Li2Lean.B3

#print axioms Li2Lean.B3.v13_q4_z_source_bounds
