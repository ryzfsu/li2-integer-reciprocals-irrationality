/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Cells-compatible q = 3 reference-package adapter.  The adapter fixes the
decoded v13 rows and the generated plan/term boundary; all numerical and
analytic certificates remain explicit inputs.
-/

import Li2Lean.B3.ReferencePackagePinnedAdapter
import Li2Lean.B3.Q3ReferenceMeasureFacts

namespace Li2Lean

noncomputable section

namespace B3

open V
open V.EnergyCertI
open V.EnergyCertI.IK

/-- Bind the q = 3 reference package to the concrete v13 decoder source.

The five field bounds, shard soundness, and total identity are deliberately
arguments.  This theorem only removes the old free-measure/free-plan
interface; it does not manufacture a certificate cell or a conclusion-shaped
bound.
-/
noncomputable def v13_reference_package_input_q3_of_v13_certificates
    {hq : SignedVBaseRange 3}
    (C : V13NumericCertificates 3 hq q3DecodedReferenceRows)
    (lr : IV)
    (lr_sound : IV.mem lr (Real.log (3 / 5 : ℝ)))
    (qlow_value : IK.val (qlowQ 3) = (vQlow 3 : ℝ))
    (field_x : CellSoundnessOn (pieceDomain 3 .x).1 (pieceDomain 3 .x).2
      (fieldUB q3D 3 lr .x)
      (fun t => V.signedVFullFieldX
        (v13RefMeasure q3DecodedReferenceRows C.normalization) (t : ℂ)))
    (field_vlo : CellSoundnessOn (pieceDomain 3 .vlo).1 (pieceDomain 3 .vlo).2
      (fieldUB q3D 3 lr .vlo)
      (fun t => V.signedVFullFieldV
        (v13RefMeasure q3DecodedReferenceRows C.normalization) (t : ℂ)))
    (field_vhi : CellSoundnessOn (pieceDomain 3 .vhi).1 (pieceDomain 3 .vhi).2
      (fieldUB q3D 3 lr .vhi)
      (fun t => V.signedVFullFieldV
        (v13RefMeasure q3DecodedReferenceRows C.normalization) (t : ℂ)))
    (field_zneg : CellSoundnessOn (pieceDomain 3 .zneg).1 (pieceDomain 3 .zneg).2
      (fieldUB q3D 3 lr .zneg)
      (fun t => V.signedVFullFieldZ
        (v13RefMeasure q3DecodedReferenceRows C.normalization) (t : ℂ)))
    (field_zpos : CellSoundnessOn (pieceDomain 3 .zpos).1 (pieceDomain 3 .zpos).2
      (fieldUB q3D 3 lr .zpos)
      (fun t => V.signedVFullFieldZ
        (v13RefMeasure q3DecodedReferenceRows C.normalization) (t : ℂ)))
    (energy : EnergyShardSoundnessFact q3D 3 lr
      (planOf q3D 3) (vEnergyTerm 3 q3D))
    (total : EnergyTotalSoundnessFact
      (v13RefMeasure q3DecodedReferenceRows C.normalization) q3D
      (planOf q3D 3) (vEnergyTerm 3 q3D)) :
    V13ReferencePackageInput 3 hq := by
  exact v13ReferencePackageInput_of_pinned q3DecodedReferenceRows C lr
    lr_sound qlow_value field_x field_vlo field_vhi field_zneg field_zpos
    energy total

end B3

end

end Li2Lean

#print axioms Li2Lean.B3.v13_reference_package_input_q3_of_v13_certificates
