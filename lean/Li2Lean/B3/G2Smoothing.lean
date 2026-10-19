/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Construction-bound G2/S1 interface for the signed V family.

The package keeps the literal S1 determinant data and the reference energy
facts attached to one \`VReferencePackage\`.  It does not prove the contour
identity, the S0 norm estimate, or the logarithmic transfer.  Those remain
explicit producer fields in \`ReferencePackageAdapter\`.

Paper sources: \`v-analytic.tex:106-145,220-301,493-631\` and
\`v-reference-data.tex:1-430\`.
-/

import Li2Lean.B3.ReferencePackageAdapter
import Li2Lean.V.VLiteralNestedBridge

namespace Li2Lean

noncomputable section

namespace V

open MeasureTheory

/-! ## Literal S1 integral and the existing nested Andreief identity -/

/- The positive parameter integral is the left hand side of the three nested
   Andreief applications (\`v-analytic.tex:127-153\`). -/
noncomputable def v13S1AndreiefIntegral {q n : ℕ}
    (D : V13LiteralAndreiefData q n) : ℂ :=
  ∫ v : Fin (5 * n) → ℝ,
    (∫ x : Fin (4 * n) → ℝ,
      andreiefProduct (D.M2 v) (D.a2 v) (D.b2 v) x
        ∂(Measure.pi fun _ : Fin (4 * n) => Literal.vContourUnitIntervalMeasure)) *
      (∫ z : Fin (4 * n) → (Fin 4 × ℝ),
        andreiefProduct (D.M1 v) (D.a1 v) (D.b1 v) z
          ∂(Measure.pi fun _ : Fin (4 * n) => Literal.vContourParameterMeasure))
      ∂(Measure.pi fun _ : Fin (5 * n) => Literal.vContourUnitIntervalMeasure)

theorem v13S1AndreiefIntegral_eq_factorial_det {q n : ℕ}
    (D : V13LiteralAndreiefData q n) :
    v13S1AndreiefIntegral D =
      (((4 * n).factorial : ℂ) ^ 2 * ((5 * n).factorial : ℂ)) * D.M0.det := by
  simpa [v13S1AndreiefIntegral] using v13_nested_andreief_of_data D

end V

namespace B3

open MeasureTheory

/-! A construction-bound S1 datum.  The determinant equation is about the
actual \`vContourActualGValue\`; \`g_ne_zero\` is kept next to it for every later
logarithmic statement. -/
structure V13LiteralAndreiefS1Data (q n : ℕ) where
  data : V.V13LiteralAndreiefData q n
  determinant_identity :
    vContourActualGValue q n =
      V.Literal.vContourPrefactor q n *
        V.v13S1AndreiefIntegral data
  g_ne_zero : vContourActualGValue q n ≠ 0

/- The same S1 identity after replacing the nested integral by its factorial
determinant value.  This is a rewrite of the existing Andreief theorem, not
a new determinant claim. -/
theorem V13LiteralAndreiefS1Data.determinant_identity_of_m0
    {q n : ℕ} (D : V13LiteralAndreiefS1Data q n) :
    vContourActualGValue q n =
      V.Literal.vContourPrefactor q n *
        ((((4 * n).factorial : ℂ) ^ 2 * ((5 * n).factorial : ℂ)) *
          D.data.M0.det) := by
  calc
    vContourActualGValue q n =
        V.Literal.vContourPrefactor q n *
          V.v13S1AndreiefIntegral D.data := D.determinant_identity
    _ = V.Literal.vContourPrefactor q n *
          ((((4 * n).factorial : ℂ) ^ 2 * ((5 * n).factorial : ℂ)) *
            D.data.M0.det) := by
      rw [V.v13S1AndreiefIntegral_eq_factorial_det]

/-! ## Shared reference measure package -/

/- The \`reference\` field is the sole carrier of the measure and all energy
facts.  Thus the S1 rows cannot silently use a second measure.  The only
energy scalar exposed by this G2 interface is \`h_sigma\`; field bounds,
support, atomlessness, and integrability remain the explicit fields of
\`VReferenceFacts\`. -/
structure VReferenceS1Package (q : ℕ) (hq : SignedVBaseRange q) where
  reference : VReferencePackage q hq
  s1 : ∀ n : ℕ, V13LiteralAndreiefS1Data q n

def VReferenceS1Package.measure
    {q : ℕ} {hq : SignedVBaseRange q}
    (P : VReferenceS1Package q hq) : V.SignedVMeasures :=
  P.reference.measure

theorem VReferenceS1Package.facts
    {q : ℕ} {hq : SignedVBaseRange q}
    (P : VReferenceS1Package q hq) :
    VReferenceFacts q hq P.reference.measure P.reference.Ax P.reference.Av
      P.reference.Az :=
  P.reference.facts

/- This is the sole sigma input consumed by G2 from the energy package. -/
theorem VReferenceS1Package.h_sigma
    {q : ℕ} {hq : SignedVBaseRange q}
    (P : VReferenceS1Package q hq) :
    vSigma q = sigmaBudget P.reference.Ax P.reference.Av P.reference.Az :=
  P.reference.facts.sigma_eq

theorem VReferenceS1Package.s1_determinant_identity
    {q : ℕ} {hq : SignedVBaseRange q}
    (P : VReferenceS1Package q hq) (n : ℕ) :
    vContourActualGValue q n =
      V.Literal.vContourPrefactor q n *
        ((((4 * n).factorial : ℂ) ^ 2 * ((5 * n).factorial : ℂ)) *
          (P.s1 n).data.M0.det) :=
  (P.s1 n).determinant_identity_of_m0

theorem VReferenceS1Package.s1_g_ne_zero
    {q : ℕ} {hq : SignedVBaseRange q}
    (P : VReferenceS1Package q hq) (n : ℕ) :
    vContourActualGValue q n ≠ 0 :=
  (P.s1 n).g_ne_zero

end B3

end

end Li2Lean

#print axioms Li2Lean.V.v13S1AndreiefIntegral_eq_factorial_det
#print axioms Li2Lean.B3.V13LiteralAndreiefS1Data.determinant_identity_of_m0
#print axioms Li2Lean.B3.VReferenceS1Package.h_sigma
#print axioms Li2Lean.B3.VReferenceS1Package.s1_determinant_identity
