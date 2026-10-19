/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B3.S0ActualInterface
import Li2Lean.B3.S0ActualTransferProof

namespace Li2Lean

noncomputable section

namespace B3

open Li2Lean V

/-! The actual construction carrier is proved in `S0ActualTransferProof`.
This wrapper keeps the public q-specific names in the historical module while
the low-level declarations live in `S0ActualInterface`, avoiding the import
cycle through the S0-T assembly. -/

noncomputable def v13_s0_transfer_actual_generic
    {q : ℕ} (hq : SignedVBaseRange q)
    (P : VReferencePackage q hq) :
    VContourS0TransferDataActual q (vAlpha q) (vSigma q) :=
  v13_s0_transfer_actual_generic_proof hq P

noncomputable def v13_s0_transfer_actual_q2
    (hq : SignedVBaseRange 2) (P : VReferencePackage 2 hq) :
    VContourS0TransferDataActual 2 (vAlpha 2) (vSigma 2) :=
  v13_s0_transfer_actual_generic hq P

noncomputable def v13_s0_transfer_actual_q3
    (hq : SignedVBaseRange 3) (P : VReferencePackage 3 hq) :
    VContourS0TransferDataActual 3 (vAlpha 3) (vSigma 3) :=
  v13_s0_transfer_actual_generic hq P

noncomputable def v13_s0_transfer_actual_q4
    (hq : SignedVBaseRange 4) (P : VReferencePackage 4 hq) :
    VContourS0TransferDataActual 4 (vAlpha 4) (vSigma 4) :=
  v13_s0_transfer_actual_generic hq P

noncomputable def v13_s0_transfer_actual_q5
    (hq : SignedVBaseRange 5) (P : VReferencePackage 5 hq) :
    VContourS0TransferDataActual 5 (vAlpha 5) (vSigma 5) :=
  v13_s0_transfer_actual_generic hq P

noncomputable def v13_s0_transfer_actual_q6
    (hq : SignedVBaseRange 6) (P : VReferencePackage 6 hq) :
    VContourS0TransferDataActual 6 (vAlpha 6) (vSigma 6) :=
  v13_s0_transfer_actual_generic hq P

noncomputable def v13_s0_transfer_actual_q7
    (hq : SignedVBaseRange 7) (P : VReferencePackage 7 hq) :
    VContourS0TransferDataActual 7 (vAlpha 7) (vSigma 7) :=
  v13_s0_transfer_actual_generic hq P

end B3

end

end Li2Lean
