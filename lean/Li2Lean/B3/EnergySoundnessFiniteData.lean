/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Concrete finite facts for the q = 2 and q = 5 v2 evaluator certificates.
These theorems deliberately stop at the checked integer layer: they do not
claim that the row evaluator is already identified with a reference measure.
-/

import Li2Lean.V.EnergyCertI.Q2Assembly
import Li2Lean.V.EnergyCertI.Q5Assembly
import Li2Lean.B3.EnergySoundnessInputs

namespace Li2Lean.B3

open V.EnergyCertI

theorem q2V2Qlow_decodes :
    IK.val (qlowQ 2) = (vQlow 2 : ℝ) := by
  norm_num [IK.val, qlowQ, vQlow]

theorem q5V2Qlow_decodes :
    IK.val (qlowQ 5) = (vQlow 5 : ℝ) := by
  norm_num [IK.val, qlowQ, vQlow]

/-! These finite checks do not produce `VReferencePackage` values.  Therefore
the first unsupplied field when constructing `VReferenceEnergySoundnessLedger`
is its `reference` field: there is no q = 2 or q = 5 concrete measure package
whose measure is proven to have these decoded rows.  After that, G-1 still
needs F-a..F-g cellwise evaluator soundness, and G-3 still needs E-a..E-d
partial-sum soundness plus the real `signedVQuadratic` decomposition. -/

end Li2Lean.B3

