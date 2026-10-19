/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B3.ReferencePackageLeafQ2
import Li2Lean.B3.ReferencePackageLeafQ3
import Li2Lean.B3.ReferencePackageLeafQ4
import Li2Lean.B3.ReferencePackageLeafQ5
import Li2Lean.B3.ReferencePackageLeafQ6
import Li2Lean.B3.ReferencePackageLeafQ7

/-!
Named public leaves for the construction-bound signed-V reference package.
The q-specific closure targets live in separate modules so that certificate
templates and energy bridges do not import this public aggregation module.
-/

namespace Li2Lean.B3

noncomputable section

/-- q = 2 reference-package ledger input. -/
noncomputable def v13_reference_package_input_q2
    (hq : SignedVBaseRange 2) : V13ReferencePackageInput 2 hq :=
  v13_reference_package_input_q2_closed hq

/-- q = 3 reference-package ledger input. -/
noncomputable def v13_reference_package_input_q3
    (hq : SignedVBaseRange 3) : V13ReferencePackageInput 3 hq :=
  v13_reference_package_input_q3_closed hq

/-- q = 4 reference-package ledger input. -/
noncomputable def v13_reference_package_input_q4
    (hq : SignedVBaseRange 4) : V13ReferencePackageInput 4 hq :=
  v13_reference_package_input_q4_closed hq

/-- q = 5 reference-package ledger input. -/
noncomputable def v13_reference_package_input_q5
    (hq : SignedVBaseRange 5) : V13ReferencePackageInput 5 hq :=
  v13_reference_package_input_q5_closed hq

/-- q = 6 reference-package ledger input. -/
noncomputable def v13_reference_package_input_q6
    (hq : SignedVBaseRange 6) : V13ReferencePackageInput 6 hq :=
  v13_reference_package_input_q6_closed hq

/-- q = 7 reference-package ledger input. -/
noncomputable def v13_reference_package_input_q7
    (hq : SignedVBaseRange 7) : V13ReferencePackageInput 7 hq :=
  v13_reference_package_input_q7_closed hq

end

end Li2Lean.B3

#print axioms Li2Lean.B3.v13_reference_package_input_q2
#print axioms Li2Lean.B3.v13_reference_package_input_q3
#print axioms Li2Lean.B3.v13_reference_package_input_q4
#print axioms Li2Lean.B3.v13_reference_package_input_q5
#print axioms Li2Lean.B3.v13_reference_package_input_q6
#print axioms Li2Lean.B3.v13_reference_package_input_q7
