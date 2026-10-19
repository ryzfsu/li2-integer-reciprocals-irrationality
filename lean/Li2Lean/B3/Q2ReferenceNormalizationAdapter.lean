/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
/-
  q = 2 normalization adapter for the construction-bound reference package.

  The raw mass calculation is proved in Q2ReferencePackageFacts.lean.  This
  wrapper only transports that proof across the arbitrary proof argument
  hq; it introduces no certificate or analytic bound.
-/
import Li2Lean.B3.Q2ReferencePackageFacts

namespace Li2Lean.B3

noncomputable section

theorem q2ReferenceNormalization_of_hq (hq : SignedVBaseRange 2) :
    V13MeasureNormalization hq (v13RefRaw q2ReferenceRows) := by
  exact q2ReferenceNormalization

end

end Li2Lean.B3

#print axioms Li2Lean.B3.q2ReferenceNormalization_of_hq
