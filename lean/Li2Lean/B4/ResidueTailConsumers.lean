/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B4.ResidueTailBridge

open Finset Polynomial

namespace Li2Lean.B4.ResidueTailBridge.Consumers

noncomputable section

open Li2Lean.B4.Residues

/-!
  Consumers for the explicit v13 residue certificate.  The certificate is
  kept as an explicit hypothesis here so this file can be compiled before the
  all-`n` producer is merged.  The two conclusions are the coefficient
  identities used in `hp-tail.tex:34-41`.
-/

/--
  Once the concrete finite-product certificate is supplied, the residue
  convolution agrees with `Phi_n` above the pole range.  This is the
  `hpartial` input to the tail algebra, v13 `hp-tail.tex:34-41`.
-/
theorem hpartial_for_residueTailAlgebra_all_of_certificate
    (n : ℕ) (hcert : ExplicitResidueCertificate n) :
    ∀ k, n < k →
      hpResidueConvolution n k = hpPhiValue n k := by
  exact hpartial_for_residueTailAlgebra n hcert

/-- Named consumer used by the all-`n` assembly, with the certificate kept as
    an explicit construction-bound hypothesis. -/
theorem hpartial_for_residueTailAlgebra_all
    (n : ℕ) (hcert : ExplicitResidueCertificate n) :
    ∀ k, n < k →
      hpResidueConvolution n k = hpPhiValue n k := by
  exact hpartial_for_residueTailAlgebra_all_of_certificate n hcert

/--
  The high-tail coefficient identity after the explicit residue certificate
  is supplied.  This is the `A_n/B_n/C_n` tail coefficient statement from
  v13 `hp-tail.tex:34-41`.
-/
theorem hpTailCoeff_all_of_certificate
    (n : ℕ) (hcert : ExplicitResidueCertificate n) :
    ∀ k, 3 * n + 2 ≤ k →
      hpThreeFormCoeff n k = hpPhiValue n k := by
  exact hpTailCoeff_of_certificate n hcert

/-- Named high-tail consumer used by the all-`n` assembly, with the
    certificate kept as an explicit construction-bound hypothesis. -/
theorem hpTailCoeff_all
    (n : ℕ) (hcert : ExplicitResidueCertificate n) :
    ∀ k, 3 * n + 2 ≤ k →
      hpThreeFormCoeff n k = hpPhiValue n k := by
  exact hpTailCoeff_all_of_certificate n hcert

end

end Li2Lean.B4.ResidueTailBridge.Consumers

#print axioms Li2Lean.B4.ResidueTailBridge.Consumers.hpartial_for_residueTailAlgebra_all_of_certificate
#print axioms Li2Lean.B4.ResidueTailBridge.Consumers.hpTailCoeff_all_of_certificate
#print axioms Li2Lean.B4.ResidueTailBridge.Consumers.hpartial_for_residueTailAlgebra_all
#print axioms Li2Lean.B4.ResidueTailBridge.Consumers.hpTailCoeff_all
