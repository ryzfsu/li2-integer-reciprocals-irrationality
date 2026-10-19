/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

The signed-pairing endpoint of the reusable Li2(1/2) L6 route.
The substantive construction of a `SignedVSquareCertificate` from the
v13 reference measures remains a separate measure-identity obligation.
-/

import Li2Lean.V.SignedEnergy

namespace Li2Lean

namespace B3

open V

/-! If the four L6 certificates and their v13 scalar identities have been
    supplied, the signed quadratic form is nonpositive.  This wrapper does
    not manufacture those certificates; it reuses the already proved L6/SOS
    theorem. -/
theorem s0T_signedPairing_nonpos_of_l6Certificates
    (μ ν : SignedVMeasures) (c : SignedVSquareCertificate μ ν) :
    signedVQuadraticForm c.data ≤ 0 := by
  have h : c.remainder ≤ 0 :=
    signedV_square_remainder_nonpos μ ν c
  rw [← c.remainder_eq]
  exact h

end B3

end Li2Lean

#print axioms Li2Lean.B3.s0T_signedPairing_nonpos_of_l6Certificates
