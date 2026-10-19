/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B3.V13RowFacts
import Li2Lean.B3.Q3ReferenceMeasureFacts
import Li2Lean.B3.Q4ReferenceMeasureFacts
import Li2Lean.B3.Q6ReferenceNormalization
import Li2Lean.B3.Q7ReferenceMeasureFacts

/-!
  Finite q = 3 row-well-formedness facts for the H6 field ledger.
  These are the decoded-table obligations from v13 `v-reference-data.tex:84-153`.
  They feed the q-generic S1 cell proof and do not assert evaluator soundness.
-/

namespace Li2Lean.B3

open V
open V.EnergyCertI
open V.EnergyCertI.IK

set_option maxHeartbeats 2000000 in
theorem q3_field_row_facts : V13FieldRowFacts q3DecodedRows := by
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
  · change ∀ c ∈ v13ChainCells q3D.xp, 0 ≤ c.left ∧ c.left ≤ c.right ∧ 0 ≤ c.density
    norm_num [q3D, mkIData, v13ChainCells, v13ChainCellsAux, chainCP,
      q3XHeader, q3XEntries, chainCoords, chainMassU, densI, jumpsI,
      Li2Lean.V.Q2Certificate.decodeChain,
      Li2Lean.V.Q2Certificate.decodeChainAux,
      Li2Lean.V.Q2Certificate.correctedLength,
      Li2Lean.V.Q2Certificate.scaleLength,
      Li2Lean.V.Q2Certificate.scaleMass, IK.val, qadd, qsub, qneg, qmul, U]
  · change ∀ c ∈ v13ChainCells q3D.vp, 0 ≤ c.left ∧ c.left ≤ c.right ∧ 0 ≤ c.density
    norm_num [q3D, mkIData, v13ChainCells, v13ChainCellsAux, chainCP,
      q3YHeader, q3YEntries, chainCoords, chainMassU, densI, jumpsI,
      Li2Lean.V.Q2Certificate.decodeChain,
      Li2Lean.V.Q2Certificate.decodeChainAux,
      Li2Lean.V.Q2Certificate.correctedLength,
      Li2Lean.V.Q2Certificate.scaleLength,
      Li2Lean.V.Q2Certificate.scaleMass, IK.val, qadd, qsub, qneg, qmul, U]
  · change ∀ c ∈ v13ChainCells q3D.zp, c.left ≤ c.right ∧ 0 ≤ c.density
    norm_num [q3D, mkIData, v13ChainCells, v13ChainCellsAux, chainCP,
      q3ZHeader, q3ZEntries, chainCoords, chainMassU, densI, jumpsI,
      Li2Lean.V.Q2Certificate.decodeChain,
      Li2Lean.V.Q2Certificate.decodeChainAux,
      Li2Lean.V.Q2Certificate.correctedLength,
      Li2Lean.V.Q2Certificate.scaleLength,
      Li2Lean.V.Q2Certificate.scaleMass, IK.val, qadd, qsub, qneg, qmul, U]
  · change ∀ p ∈ q3D.xp, 0 ≤ p.e.1 ∧ 0 < p.e.2 ∧ 0 < p.J.2
    norm_num [q3D, mkIData, chainCP, q3XHeader, q3XEntries,
      chainCoords, chainMassU, densI, jumpsI,
      Li2Lean.V.Q2Certificate.decodeChain,
      Li2Lean.V.Q2Certificate.decodeChainAux,
      Li2Lean.V.Q2Certificate.correctedLength,
      Li2Lean.V.Q2Certificate.scaleLength,
      Li2Lean.V.Q2Certificate.scaleMass, IK.val, qadd, qsub, qneg, qmul, U]
  · change ∀ p ∈ q3D.vp, 0 ≤ p.e.1 ∧ 0 < p.e.2 ∧ 0 < p.J.2
    norm_num [q3D, mkIData, chainCP, q3YHeader, q3YEntries,
      chainCoords, chainMassU, densI, jumpsI,
      Li2Lean.V.Q2Certificate.decodeChain,
      Li2Lean.V.Q2Certificate.decodeChainAux,
      Li2Lean.V.Q2Certificate.correctedLength,
      Li2Lean.V.Q2Certificate.scaleLength,
      Li2Lean.V.Q2Certificate.scaleMass, IK.val, qadd, qsub, qneg, qmul, U]
  · change ∀ p ∈ q3D.zp, 0 < p.e.2 ∧ 0 < p.J.2
    norm_num [q3D, mkIData, chainCP, q3ZHeader, q3ZEntries,
      chainCoords, chainMassU, densI, jumpsI,
      Li2Lean.V.Q2Certificate.decodeChain,
      Li2Lean.V.Q2Certificate.decodeChainAux,
      Li2Lean.V.Q2Certificate.correctedLength,
      Li2Lean.V.Q2Certificate.scaleLength,
      Li2Lean.V.Q2Certificate.scaleMass, IK.val, qadd, qsub, qneg, qmul, U]
  · change (q3D.xp.map fun p => IK.val p.J).sum = 0
    norm_num [q3D, mkIData, chainCP, q3XHeader, q3XEntries,
      chainCoords, chainMassU, densI, jumpsI,
      Li2Lean.V.Q2Certificate.decodeChain,
      Li2Lean.V.Q2Certificate.decodeChainAux,
      Li2Lean.V.Q2Certificate.correctedLength,
      Li2Lean.V.Q2Certificate.scaleLength,
      Li2Lean.V.Q2Certificate.scaleMass, IK.val, qadd, qsub, qneg, qmul, U]
  · change (q3D.vp.map fun p => IK.val p.J).sum = 0
    norm_num [q3D, mkIData, chainCP, q3YHeader, q3YEntries,
      chainCoords, chainMassU, densI, jumpsI,
      Li2Lean.V.Q2Certificate.decodeChain,
      Li2Lean.V.Q2Certificate.decodeChainAux,
      Li2Lean.V.Q2Certificate.correctedLength,
      Li2Lean.V.Q2Certificate.scaleLength,
      Li2Lean.V.Q2Certificate.scaleMass, IK.val, qadd, qsub, qneg, qmul, U]
  · change (q3D.zp.map fun p => IK.val p.J).sum = 0
    norm_num [q3D, mkIData, chainCP, q3ZHeader, q3ZEntries,
      chainCoords, chainMassU, densI, jumpsI,
      Li2Lean.V.Q2Certificate.decodeChain,
      Li2Lean.V.Q2Certificate.decodeChainAux,
      Li2Lean.V.Q2Certificate.correctedLength,
      Li2Lean.V.Q2Certificate.scaleLength,
      Li2Lean.V.Q2Certificate.scaleMass, IK.val, qadd, qsub, qneg, qmul, U]
  · decide +kernel
  · decide +kernel

end Li2Lean.B3

#print axioms Li2Lean.B3.q3_field_row_facts
