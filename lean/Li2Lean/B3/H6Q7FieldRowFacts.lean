/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B3.V13RowFacts
import Li2Lean.B3.Q7ReferenceMeasureFacts

/-!
  Finite q = 7 row-well-formedness facts for the H6 field ledger.
  These are the decoded-table obligations from v13 `v-reference-data.tex`.
  They feed the q-generic S1 cell proof and do not assert evaluator soundness.
-/

namespace Li2Lean.B3

open V
open V.EnergyCertI
open V.EnergyCertI.IK

set_option maxHeartbeats 2000000 in
theorem q7_field_row_facts : V13FieldRowFacts q7ReferenceRows := by
  refine {
    x_cells := ?_
    v_cells := ?_
    z_cells := ?_
    x_rows := ?_
    v_rows := ?_
    z_rows := ?_
    x_jump := ?_
    v_jump := ?_
    z_jump := ?_
    pre_ok := ?_
    full_ok := ?_ }
  · change ∀ c ∈ v13ChainCells q7D.xp, 0 ≤ c.left ∧ c.left ≤ c.right ∧ 0 ≤ c.density
    norm_num [q7D, mkIData, v13ChainCells, v13ChainCellsAux, chainCP,
      q7XHeader, q7XEntries, chainCoords, chainMassU, densI, jumpsI,
      Li2Lean.V.Q2Certificate.decodeChain,
      Li2Lean.V.Q2Certificate.decodeChainAux,
      Li2Lean.V.Q2Certificate.correctedLength,
      Li2Lean.V.Q2Certificate.scaleLength,
      Li2Lean.V.Q2Certificate.scaleMass, IK.val, qadd, qsub, qneg, qmul, U]
  · change ∀ c ∈ v13ChainCells q7D.vp, 0 ≤ c.left ∧ c.left ≤ c.right ∧ 0 ≤ c.density
    norm_num [q7D, mkIData, v13ChainCells, v13ChainCellsAux, chainCP,
      q7YHeader, q7YEntries, chainCoords, chainMassU, densI, jumpsI,
      Li2Lean.V.Q2Certificate.decodeChain,
      Li2Lean.V.Q2Certificate.decodeChainAux,
      Li2Lean.V.Q2Certificate.correctedLength,
      Li2Lean.V.Q2Certificate.scaleLength,
      Li2Lean.V.Q2Certificate.scaleMass, IK.val, qadd, qsub, qneg, qmul, U]
  · change ∀ c ∈ v13ChainCells q7D.zp, c.left ≤ c.right ∧ 0 ≤ c.density
    norm_num [q7D, mkIData, v13ChainCells, v13ChainCellsAux, chainCP,
      q7ZHeader, q7ZEntries, chainCoords, chainMassU, densI, jumpsI,
      Li2Lean.V.Q2Certificate.decodeChain,
      Li2Lean.V.Q2Certificate.decodeChainAux,
      Li2Lean.V.Q2Certificate.correctedLength,
      Li2Lean.V.Q2Certificate.scaleLength,
      Li2Lean.V.Q2Certificate.scaleMass, IK.val, qadd, qsub, qneg, qmul, U]
  · change ∀ p ∈ q7D.xp, 0 ≤ p.e.1 ∧ 0 < p.e.2 ∧ 0 < p.J.2
    norm_num [q7D, mkIData, chainCP, q7XHeader, q7XEntries,
      chainCoords, chainMassU, densI, jumpsI,
      Li2Lean.V.Q2Certificate.decodeChain,
      Li2Lean.V.Q2Certificate.decodeChainAux,
      Li2Lean.V.Q2Certificate.correctedLength,
      Li2Lean.V.Q2Certificate.scaleLength,
      Li2Lean.V.Q2Certificate.scaleMass, IK.val, qadd, qsub, qneg, qmul, U]
  · change ∀ p ∈ q7D.vp, 0 ≤ p.e.1 ∧ 0 < p.e.2 ∧ 0 < p.J.2
    norm_num [q7D, mkIData, chainCP, q7YHeader, q7YEntries,
      chainCoords, chainMassU, densI, jumpsI,
      Li2Lean.V.Q2Certificate.decodeChain,
      Li2Lean.V.Q2Certificate.decodeChainAux,
      Li2Lean.V.Q2Certificate.correctedLength,
      Li2Lean.V.Q2Certificate.scaleLength,
      Li2Lean.V.Q2Certificate.scaleMass, IK.val, qadd, qsub, qneg, qmul, U]
  · change ∀ p ∈ q7D.zp, 0 < p.e.2 ∧ 0 < p.J.2
    norm_num [q7D, mkIData, chainCP, q7ZHeader, q7ZEntries,
      chainCoords, chainMassU, densI, jumpsI,
      Li2Lean.V.Q2Certificate.decodeChain,
      Li2Lean.V.Q2Certificate.decodeChainAux,
      Li2Lean.V.Q2Certificate.correctedLength,
      Li2Lean.V.Q2Certificate.scaleLength,
      Li2Lean.V.Q2Certificate.scaleMass, IK.val, qadd, qsub, qneg, qmul, U]
  · change (q7D.xp.map fun p => IK.val p.J).sum = 0
    norm_num [q7D, mkIData, chainCP, q7XHeader, q7XEntries,
      chainCoords, chainMassU, densI, jumpsI,
      Li2Lean.V.Q2Certificate.decodeChain,
      Li2Lean.V.Q2Certificate.decodeChainAux,
      Li2Lean.V.Q2Certificate.correctedLength,
      Li2Lean.V.Q2Certificate.scaleLength,
      Li2Lean.V.Q2Certificate.scaleMass, IK.val, qadd, qsub, qneg, qmul, U]
  · change (q7D.vp.map fun p => IK.val p.J).sum = 0
    norm_num [q7D, mkIData, chainCP, q7YHeader, q7YEntries,
      chainCoords, chainMassU, densI, jumpsI,
      Li2Lean.V.Q2Certificate.decodeChain,
      Li2Lean.V.Q2Certificate.decodeChainAux,
      Li2Lean.V.Q2Certificate.correctedLength,
      Li2Lean.V.Q2Certificate.scaleLength,
      Li2Lean.V.Q2Certificate.scaleMass, IK.val, qadd, qsub, qneg, qmul, U]
  · change (q7D.zp.map fun p => IK.val p.J).sum = 0
    norm_num [q7D, mkIData, chainCP, q7ZHeader, q7ZEntries,
      chainCoords, chainMassU, densI, jumpsI,
      Li2Lean.V.Q2Certificate.decodeChain,
      Li2Lean.V.Q2Certificate.decodeChainAux,
      Li2Lean.V.Q2Certificate.correctedLength,
      Li2Lean.V.Q2Certificate.scaleLength,
      Li2Lean.V.Q2Certificate.scaleMass, IK.val, qadd, qsub, qneg, qmul, U]
  · decide +kernel
  · decide +kernel

end Li2Lean.B3

#print axioms Li2Lean.B3.q7_field_row_facts
