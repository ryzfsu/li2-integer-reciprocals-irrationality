/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.

Finite q = 3 support bounds for the decoded v13 rows.
Source: `v-reference-data.tex:84-153` and the generic decoder in
`B3/ReferencePackageGeneric.lean`.
-/

import Li2Lean.B3.ReferencePackageGeneric

namespace Li2Lean

noncomputable section

namespace B3

open V V.EnergyCertI

set_option maxHeartbeats 2000000 in
theorem q3_decoded_row_bounds :
    V13DecodedRowBounds 3 q3DecodedRows := by
  refine {
    x_low := ?_
    x_full := ?_
    v_low := ?_
    v_full := ?_
    z_source := ?_ }
  · simpa [q3DecodedRows] using (show
      ∀ c ∈ v13ChainCells V.EnergyCertI.q3D.xp,
        (vXLow 3 : ℝ) ≤ c.left ∧ c.right ≤ 1 by
      norm_num [vXLow, V.EnergyCertI.q3D, V.EnergyCertI.mkIData,
        v13ChainCells, v13ChainCellsAux, V.EnergyCertI.chainCP,
        V.EnergyCertI.q3XHeader, V.EnergyCertI.q3XEntries,
        V.EnergyCertI.chainCoords, V.EnergyCertI.chainMassU,
        V.EnergyCertI.densI, V.EnergyCertI.jumpsI,
        V.EnergyCertI.IK.val, V.Q2Certificate.correctedLength,
        V.Q2Certificate.scaleLength, V.Q2Certificate.scaleMass,
        V.EnergyCertI.U, Li2Lean.V.Q2Certificate.decodeChain,
        Li2Lean.V.Q2Certificate.decodeChainAux])
  · simpa [q3DecodedRows] using (show
      ∀ c ∈ v13ChainCells V.EnergyCertI.q3D.xp,
        (0 : ℝ) ≤ c.left ∧ c.right ≤ 1 by
      norm_num [V.EnergyCertI.q3D, V.EnergyCertI.mkIData,
        v13ChainCells, v13ChainCellsAux, V.EnergyCertI.chainCP,
        V.EnergyCertI.q3XHeader, V.EnergyCertI.q3XEntries,
        V.EnergyCertI.chainCoords, V.EnergyCertI.chainMassU,
        V.EnergyCertI.densI, V.EnergyCertI.jumpsI,
        V.EnergyCertI.IK.val, V.Q2Certificate.correctedLength,
        V.Q2Certificate.scaleLength, V.Q2Certificate.scaleMass,
        V.EnergyCertI.U, Li2Lean.V.Q2Certificate.decodeChain,
        Li2Lean.V.Q2Certificate.decodeChainAux])
  · simpa [q3DecodedRows] using (show
      ∀ c ∈ v13ChainCells V.EnergyCertI.q3D.vp,
        (vVLow 3 : ℝ) ≤ c.left ∧ c.right ≤ 1 by
      norm_num [vVLow, V.EnergyCertI.q3D, V.EnergyCertI.mkIData,
        v13ChainCells, v13ChainCellsAux, V.EnergyCertI.chainCP,
        V.EnergyCertI.q3YHeader, V.EnergyCertI.q3YEntries,
        V.EnergyCertI.chainCoords, V.EnergyCertI.chainMassU,
        V.EnergyCertI.densI, V.EnergyCertI.jumpsI,
        V.EnergyCertI.IK.val, V.Q2Certificate.correctedLength,
        V.Q2Certificate.scaleLength, V.Q2Certificate.scaleMass,
        V.EnergyCertI.U, Li2Lean.V.Q2Certificate.decodeChain,
        Li2Lean.V.Q2Certificate.decodeChainAux])
  · simpa [q3DecodedRows] using (show
      ∀ c ∈ v13ChainCells V.EnergyCertI.q3D.vp,
        (0 : ℝ) ≤ c.left ∧ c.right ≤ 1 by
      norm_num [V.EnergyCertI.q3D, V.EnergyCertI.mkIData,
        v13ChainCells, v13ChainCellsAux, V.EnergyCertI.chainCP,
        V.EnergyCertI.q3YHeader, V.EnergyCertI.q3YEntries,
        V.EnergyCertI.chainCoords, V.EnergyCertI.chainMassU,
        V.EnergyCertI.densI, V.EnergyCertI.jumpsI,
        V.EnergyCertI.IK.val, V.Q2Certificate.correctedLength,
        V.Q2Certificate.scaleLength, V.Q2Certificate.scaleMass,
        V.EnergyCertI.U, Li2Lean.V.Q2Certificate.decodeChain,
        Li2Lean.V.Q2Certificate.decodeChainAux])
  · simpa [q3DecodedRows] using (show
      ∀ c ∈ v13ChainCells V.EnergyCertI.q3D.zp,
        (-3 : ℝ) ≤ c.left ∧ c.right ≤ -(3 / 5 : ℝ) by
      norm_num [V.EnergyCertI.q3D, V.EnergyCertI.mkIData,
        v13ChainCells, v13ChainCellsAux, V.EnergyCertI.chainCP,
        V.EnergyCertI.q3ZHeader, V.EnergyCertI.q3ZEntries,
        V.EnergyCertI.chainCoords, V.EnergyCertI.chainMassU,
        V.EnergyCertI.densI, V.EnergyCertI.jumpsI,
        V.EnergyCertI.IK.val, V.Q2Certificate.correctedLength,
        V.Q2Certificate.scaleLength, V.Q2Certificate.scaleMass,
        V.EnergyCertI.U, Li2Lean.V.Q2Certificate.decodeChain,
        Li2Lean.V.Q2Certificate.decodeChainAux])

/-! The q3 instance of the generic v13 constructor.  All analytic and
numeric certificates remain explicit inputs; this wrapper only fixes the
decoded source and supplies the verified row bounds above. -/

noncomputable def q3_reference_package_of_numeric_certificates
    {hq : SignedVBaseRange 3}
    (C : V13NumericCertificates 3 hq q3DecodedRows) :
    VReferencePackage 3 hq :=
  vReferencePackage_of_rows q3DecodedRows C

end B3

end

end Li2Lean

#print axioms Li2Lean.B3.q3_decoded_row_bounds
#print axioms Li2Lean.B3.q3_reference_package_of_numeric_certificates
