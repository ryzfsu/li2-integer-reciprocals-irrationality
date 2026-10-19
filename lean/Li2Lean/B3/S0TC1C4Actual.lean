/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B3.ReferencePackage

namespace Li2Lean
namespace B3

noncomputable section

open MeasureTheory Set

/-! The v13 lower support endpoint is strictly positive.  This is the
construction-side nonvanishing input used by the reflection step in
`paper-v13/source/chapters/v-analytic.tex:220-248`. -/
theorem referenceMeasure_v_ae_ne_zero {q : ℕ} {hq : SignedVBaseRange q}
    (P : VReferencePackage q hq) :
    ∀ᵐ v ∂P.measure.μv, v ≠ 0 := by
  have hlow : (0 : ℝ) < (vVLow q : ℝ) := by
    norm_num [vVLow]
  have hmem : ∀ᵐ v ∂P.measure.μv,
      v ∈ (Complex.ofReal '' Set.Icc (vVLow q) 1) := by
    rw [ae_iff]
    change P.measure.μv (Complex.ofReal '' Set.Icc (vVLow q) 1)ᶜ = 0
    exact P.facts.v_support_low
  filter_upwards [hmem] with v hv
  intro hv0
  rcases hv with ⟨r, hr, rfl⟩
  have hr0 : r = 0 := by
    exact_mod_cast hv0
  linarith [hr.1]

end

end B3
end Li2Lean

#print axioms Li2Lean.B3.referenceMeasure_v_ae_ne_zero
