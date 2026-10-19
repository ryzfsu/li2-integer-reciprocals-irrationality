/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B4.HpNegContourResidueProvider
import Li2Lean.B4.NegativeContourConcreteProducer

/-!
Construction-bound q-specific assembly for the exceptional negative contour
in paper v13 `hp-tail.tex:256-316,319-410,403-455`.

The P1 residue provider retains the actual rectangle decomposition and edge
parameterization assumptions. The P2 inputs retain both the fixed-30 border
bound and the branch-value norm estimate. This module only connects those
inputs to the existing concrete `hpBSequence` certificate; it proves no
boundary estimate or residue decomposition by assumption hiding.
-/

open Complex Real

namespace Li2Lean.B4.NegativeContour

noncomputable section

open Li2Lean.B4.NegContour
open Li2Lean.B4.NegContourResidueProducer

/-- The remaining branch-value estimate in the normalization of
`hp-tail.tex:403-410`. It is tied to the actual v13 branch kernel. -/
def HpNegBranchValueBound (q : ℕ) : Prop :=
  ∀ n : ℕ, 30 ≤ n →
    ‖hpTailBranchValuePlus q n‖ ≤
      (1 / (2 * Real.pi)) * (3 * ((n + 1 : ℕ) : ℝ)) *
        (Real.exp 18 * ((n + 1 : ℕ) : ℝ) ^ 18 * (29 : ℝ) ^ n)

/-- Assemble the actual P1 residue provider and concrete four-side inputs
into the producer record. The fixed-30 border bound and branch-value estimate
remain explicit hypotheses because the side envelope alone only starts at
its declared `n0`, and the norm estimate still requires the Cauchy/residue
bound. -/
theorem hpNegContourProducerInputOfV13Providers {q : ℕ}
    (residueProvider : HpNegContourResidueProvider q)
    (sides : HpNegConcreteFourSideInputs q)
    (fixed30Boundary : HpNegBorderBound q)
    (branchBound : HpNegBranchValueBound q) :
    HpNegContourProducerInput q := by
  exact hpNegContourProducerInputOfConcrete sides fixed30Boundary
    residueProvider.residue branchBound

/-- q=8 instance of the v13 rectangle producer. The inputs are bound to the
actual branch kernel, residue provider, and four-side rectangle data. -/
theorem negativeContour_rectangle_q8_of_v13_providers
    (residueProvider : HpNegContourResidueProvider 8)
    (sides : HpNegConcreteFourSideInputs 8)
    (fixed30Boundary : HpNegBorderBound 8)
    (branchBound : HpNegBranchValueBound 8) :
    Nonempty (NegContourRectangleCertificate hpBSequence 8) := by
  exact negativeContour_rectangle_q8_of_producers
    (hpNegContourProducerInputOfV13Providers residueProvider sides
      fixed30Boundary branchBound)

/-- q=9 instance of the v13 rectangle producer. The inputs are bound to the
actual branch kernel, residue provider, and four-side rectangle data. -/
theorem negativeContour_rectangle_q9_of_v13_providers
    (residueProvider : HpNegContourResidueProvider 9)
    (sides : HpNegConcreteFourSideInputs 9)
    (fixed30Boundary : HpNegBorderBound 9)
    (branchBound : HpNegBranchValueBound 9) :
    Nonempty (NegContourRectangleCertificate hpBSequence 9) := by
  exact negativeContour_rectangle_q9_of_producers
    (hpNegContourProducerInputOfV13Providers residueProvider sides
      fixed30Boundary branchBound)

/-- q=10 instance of the v13 rectangle producer. The inputs are bound to the
actual branch kernel, residue provider, and four-side rectangle data. -/
theorem negativeContour_rectangle_q10_of_v13_providers
    (residueProvider : HpNegContourResidueProvider 10)
    (sides : HpNegConcreteFourSideInputs 10)
    (fixed30Boundary : HpNegBorderBound 10)
    (branchBound : HpNegBranchValueBound 10) :
    Nonempty (NegContourRectangleCertificate hpBSequence 10) := by
  exact negativeContour_rectangle_q10_of_producers
    (hpNegContourProducerInputOfV13Providers residueProvider sides
      fixed30Boundary branchBound)

/-- q=8 coefficient estimate for the actual Hermite-Pade sequence. -/
theorem negativeContourB_q8_of_v13_providers
    (residueProvider : HpNegContourResidueProvider 8)
    (sides : HpNegConcreteFourSideInputs 8)
    (fixed30Boundary : HpNegBorderBound 8)
    (branchBound : HpNegBranchValueBound 8) : concreteNegContourB 8 := by
  exact negativeContourB_q8_of_producers
    (hpNegContourProducerInputOfV13Providers residueProvider sides
      fixed30Boundary branchBound)

/-- q=9 coefficient estimate for the actual Hermite-Pade sequence. -/
theorem negativeContourB_q9_of_v13_providers
    (residueProvider : HpNegContourResidueProvider 9)
    (sides : HpNegConcreteFourSideInputs 9)
    (fixed30Boundary : HpNegBorderBound 9)
    (branchBound : HpNegBranchValueBound 9) : concreteNegContourB 9 := by
  exact negativeContourB_q9_of_producers
    (hpNegContourProducerInputOfV13Providers residueProvider sides
      fixed30Boundary branchBound)

/-- q=10 coefficient estimate for the actual Hermite-Pade sequence. -/
theorem negativeContourB_q10_of_v13_providers
    (residueProvider : HpNegContourResidueProvider 10)
    (sides : HpNegConcreteFourSideInputs 10)
    (fixed30Boundary : HpNegBorderBound 10)
    (branchBound : HpNegBranchValueBound 10) : concreteNegContourB 10 := by
  exact negativeContourB_q10_of_producers
    (hpNegContourProducerInputOfV13Providers residueProvider sides
      fixed30Boundary branchBound)

end

end Li2Lean.B4.NegativeContour

#print axioms Li2Lean.B4.NegativeContour.hpNegContourProducerInputOfV13Providers
#print axioms Li2Lean.B4.NegativeContour.negativeContour_rectangle_q8_of_v13_providers
#print axioms Li2Lean.B4.NegativeContour.negativeContour_rectangle_q9_of_v13_providers
#print axioms Li2Lean.B4.NegativeContour.negativeContour_rectangle_q10_of_v13_providers
#print axioms Li2Lean.B4.NegativeContour.negativeContourB_q8_of_v13_providers
#print axioms Li2Lean.B4.NegativeContour.negativeContourB_q9_of_v13_providers
#print axioms Li2Lean.B4.NegativeContour.negativeContourB_q10_of_v13_providers
