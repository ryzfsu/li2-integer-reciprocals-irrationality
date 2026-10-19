/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B4.NegativeContourBranchValueBound
import Li2Lean.B4.HpNegContourResidueProvider
import Li2Lean.B4.NegativeContourProducer
import Li2Lean.B4.NegativeContourBorderV13
import Li2Lean.B4.P1EdgeParameterization

/-!
Construction-bound wiring for the exceptional negative bases in v13
`hp-tail.tex:256-410`. The producer consumes the actual residue provider and
the phase-aware border bound. The branch-value norm estimate is supplied by
the compiled P3 theorem `hpNegBranchValueBound_of_v13_contour`; no arbitrary
sequence or conclusion-shaped certificate is introduced here.
-/

open Li2Lean.B4
open Li2Lean.B4.NegContour
open Li2Lean.B4.NegContourResidueProducer
open Li2Lean.B4.NegativeContour

namespace Li2Lean.AllNAssembly

noncomputable section

/-! The only remaining analytic input is the construction-bound P1 rectangle
decomposition.  The P2 border estimate is the direct v13 theorem
`hpNegBorderBound_of_v13`; retaining a boundary field here would duplicate
the old four-side envelope interface and allow stale data to bypass that
theorem.  P3 remains derived from P1 and the direct P2 result.
-/
structure HPExceptionalContourInput : Prop where
  residue : ∀ q : ℕ, (q = 8 ∨ q = 9 ∨ q = 10) →
    HpNegContourResidueProvider q

/-! Build the full q-specific producer input. P2 is supplied directly by the
v13 four-side proof, and P3 remains tied to `hpTailBranchValuePlus`. -/
theorem hpNegContourInputs_of_v13_p1_p2
    (I : HPExceptionalContourInput) :
    ∀ q : ℕ, (q = 8 ∨ q = 9 ∨ q = 10) →
      HpNegContourProducerInput q := by
  intro q hq
  let R := I.residue q hq
  let B := hpNegBorderBound_of_v13 hq
  have hbranch : HpNegBranchValueBound q :=
    hpNegBranchValueBound_of_v13_contour R B
  exact hpNegContourProducerInput_of_provider R B hbranch

/-! Rectangle certificates for the three exceptional q are direct
construction-bound consumers of the two named analytic inputs. -/
theorem negativeContour_rectangle_q8_of_v13_p1_p2
    (I : HPExceptionalContourInput) :
    Nonempty (NegContourRectangleCertificate hpBSequence 8) := by
  exact negativeContour_rectangle_q8_of_producers
    (hpNegContourInputs_of_v13_p1_p2 I 8 (by norm_num))

theorem negativeContour_rectangle_q9_of_v13_p1_p2
    (I : HPExceptionalContourInput) :
    Nonempty (NegContourRectangleCertificate hpBSequence 9) := by
  exact negativeContour_rectangle_q9_of_producers
    (hpNegContourInputs_of_v13_p1_p2 I 9 (by norm_num))

theorem negativeContour_rectangle_q10_of_v13_p1_p2
    (I : HPExceptionalContourInput) :
    Nonempty (NegContourRectangleCertificate hpBSequence 10) := by
  exact negativeContour_rectangle_q10_of_producers
    (hpNegContourInputs_of_v13_p1_p2 I 10 (by norm_num))

theorem negativeContourB_q8_of_v13_p1_p2
    (I : HPExceptionalContourInput) : concreteNegContourB 8 := by
  exact negativeContourB_q8_of_producers
    (hpNegContourInputs_of_v13_p1_p2 I 8 (by norm_num))

theorem negativeContourB_q9_of_v13_p1_p2
    (I : HPExceptionalContourInput) : concreteNegContourB 9 := by
  exact negativeContourB_q9_of_producers
    (hpNegContourInputs_of_v13_p1_p2 I 9 (by norm_num))

theorem negativeContourB_q10_of_v13_p1_p2
    (I : HPExceptionalContourInput) : concreteNegContourB 10 := by
  exact negativeContourB_q10_of_producers
    (hpNegContourInputs_of_v13_p1_p2 I 10 (by norm_num))

/-! The concrete q = 8 specialization used for the exceptional base
`a = -8`. This follows the v13 residue-provider construction and the
coefficient normalization in `hp-tail.tex:256-410,403-410`; no arbitrary
contour sequence or replacement analytic input is introduced. -/
theorem negativeContourB_a8_v13 : concreteNegContourB 8 := by
  exact negativeContourB_q8_of_v13_p1_p2
    ⟨fun q hq =>
      HpNegContourResidueProvider.of_q_spec q hq⟩

theorem negativeContourRectangle_a8_v13 :
    Nonempty (NegContourRectangleCertificate hpBSequence 8) := by
  exact negativeContour_rectangle_q8_of_v13_p1_p2
    ⟨fun q hq =>
      HpNegContourResidueProvider.of_q_spec q hq⟩

/-! The concrete q = 9 specialization for `a = -9`, using the same
v13 rectangle, border, and residue-provider route as q = 8. -/
theorem negativeContourB_a9_v13 : concreteNegContourB 9 := by
  exact negativeContourB_q9_of_v13_p1_p2
    ⟨fun q hq =>
      HpNegContourResidueProvider.of_q_spec q hq⟩

theorem negativeContourRectangle_a9_v13 :
    Nonempty (NegContourRectangleCertificate hpBSequence 9) := by
  exact negativeContour_rectangle_q9_of_v13_p1_p2
    ⟨fun q hq =>
      HpNegContourResidueProvider.of_q_spec q hq⟩

/-! The q = 10 specialization is the a = -1/10 contour certificate in
v13 `hp-tail.tex:256-410`; it reuses the P1 edge parameterization and the
existing direct P2/P3 bounds. -/
theorem negativeContourB_a10_v13 : concreteNegContourB 10 := by
  exact negativeContourB_q10_of_v13_p1_p2
    ⟨fun q hq => HpNegContourResidueProvider.of_q_spec q hq⟩

/-! The typed rectangle package for the same q = 10 (`a = -1/10`) estimate;
the rectangle shape and q membership are the fixed v13 data. -/
theorem negativeContourRectangle_a10_v13 :
    Nonempty (NegContourRectangleCertificate hpBSequence 10) := by
  exact negativeContour_rectangle_q10_of_v13_p1_p2
    ⟨fun q hq => HpNegContourResidueProvider.of_q_spec q hq⟩

end

end Li2Lean.AllNAssembly

#print axioms Li2Lean.AllNAssembly.hpNegContourInputs_of_v13_p1_p2
#print axioms Li2Lean.AllNAssembly.negativeContour_rectangle_q8_of_v13_p1_p2
#print axioms Li2Lean.AllNAssembly.negativeContour_rectangle_q9_of_v13_p1_p2
#print axioms Li2Lean.AllNAssembly.negativeContour_rectangle_q10_of_v13_p1_p2
#print axioms Li2Lean.AllNAssembly.negativeContourB_q8_of_v13_p1_p2
#print axioms Li2Lean.AllNAssembly.negativeContourB_q9_of_v13_p1_p2
#print axioms Li2Lean.AllNAssembly.negativeContourB_q10_of_v13_p1_p2
#print axioms Li2Lean.AllNAssembly.negativeContourB_a8_v13
#print axioms Li2Lean.AllNAssembly.negativeContourRectangle_a8_v13
#print axioms Li2Lean.AllNAssembly.negativeContourB_a9_v13
#print axioms Li2Lean.AllNAssembly.negativeContourRectangle_a9_v13
#print axioms Li2Lean.AllNAssembly.negativeContourB_a10_v13
#print axioms Li2Lean.AllNAssembly.negativeContourRectangle_a10_v13
