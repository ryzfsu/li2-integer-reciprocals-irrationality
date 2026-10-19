/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B4.NegativeContourConcreteEnvelope
import Li2Lean.B4.NegativeContourProducer

/-!
Construction-bound wiring for the C3 four-side negative-contour envelope.

The C3 envelope is stated for the actual `hpNegPhi` kernel and its full
phase `exp (hpNegLambda q * w)`, as in `hp-tail.tex:258-266,319-371`.
This module only transports that border certificate into the older producer
record.  The transport remains on `hpNegBorder`; it does not extend the
estimate to the solid rectangle.

The residue and branch-norm fields below stay explicit construction inputs.
They are the actual `HpTailResidueRectangleCertificate` and
`hpTailBranchValuePlus` obligations from `hp-tail.tex:256-266`; no arbitrary
`BSequence` or unrelated contour function is introduced.
-/

open Complex Real

namespace Li2Lean.B4.NegContour

noncomputable section

open Li2Lean.B4
open Li2Lean.B4.NegativeContour

/-!
Build the construction-bound producer input from the merged C3 envelope.
The `fixed30_boundary` argument is deliberately explicit.  The C3 envelope
proves its border estimate from `certificate.n0` onward, with only
`30 ≤ certificate.n0`; that fact cannot be reversed to a threshold-30 bound.
Thus this adapter keeps the old `HpNegBorderBound` field honest instead of
silently weakening its quantifier.  The `branch_bound` argument is likewise
explicit: the four-side estimate alone does not prove the Cauchy/residue norm
estimate.
-/
def hpNegContourProducerInputOfConcrete {q : ℕ}
    (sides : HpNegConcreteFourSideInputs q)
    (fixed30_boundary : HpNegBorderBound q)
    (residue : ∀ n : ℕ, 0 < n →
      HpTailResidueRectangleCertificate q n (1 / 5 : ℝ))
    (branch_bound : ∀ n : ℕ, 30 ≤ n →
      ‖hpTailBranchValuePlus q n‖ ≤
        (1 / (2 * Real.pi)) * (3 * ((n + 1 : ℕ) : ℝ)) *
          (Real.exp 18 * ((n + 1 : ℕ) : ℝ) ^ 18 * (29 : ℝ) ^ n)) :
    HpNegContourProducerInput q := by
  let certificate : HpNegBoundaryCertificate q :=
    hpNegBoundaryCertificateOfConcrete sides
  exact
    { q_spec := certificate.q_spec
      residue := residue
      boundary := fixed30_boundary
      branch_bound := branch_bound }

theorem hpNegContourProducerInputOfConcrete_q_spec {q : ℕ}
    (sides : HpNegConcreteFourSideInputs q)
    (fixed30_boundary : HpNegBorderBound q)
    (residue : ∀ n : ℕ, 0 < n →
      HpTailResidueRectangleCertificate q n (1 / 5 : ℝ))
    (branch_bound : ∀ n : ℕ, 30 ≤ n →
      ‖hpTailBranchValuePlus q n‖ ≤
        (1 / (2 * Real.pi)) * (3 * ((n + 1 : ℕ) : ℝ)) *
          (Real.exp 18 * ((n + 1 : ℕ) : ℝ) ^ 18 * (29 : ℝ) ^ n)) :
    (hpNegContourProducerInputOfConcrete sides fixed30_boundary residue branch_bound).q_spec =
      hpNegConcreteFourSideInputs.q_spec sides := by
  rfl

end

end Li2Lean.B4.NegContour

#print axioms Li2Lean.B4.NegContour.hpNegContourProducerInputOfConcrete
