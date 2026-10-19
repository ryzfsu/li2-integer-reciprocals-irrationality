/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B4.NegativeContourTyped

/-!
# Concrete B4 negative-contour producer bridge

This module only packages a quantitative producer for the concrete
Hermite--Pade sequence `hpBSequence`. The analytic estimate itself is the
v13 rectangle argument in `hp-tail.tex:256-410`; it is supplied as a typed
input here and is not replaced by an estimate for an arbitrary sequence.

The `(n + 1)^k` normalization is the one used by the corrected
`NegativeContourTyped` interface, so the `n = 0` coefficient is included.
-/

namespace Li2Lean.B4.NegativeContour

noncomputable section

/-! A concrete producer contract for one of the three exceptional bases. -/
structure ConcreteHpProducer (q : ℕ) : Prop where
  q_mem : q ∈ negativeContourBases
  bound : concreteNegContourB q

/-- Package a concrete `hpBSequence` contour estimate into the rectangle
certificate consumed by the B4 tail. The rectangle is the fixed rational
height `1/5` rectangle from the v13 contour setup. -/
theorem certificate_of_concrete_producer {q : ℕ}
    (producer : ConcreteHpProducer q) :
    Nonempty (NegContourRectangleCertificate hpBSequence q) := by
  refine ⟨⟨rationalBetaRectangle, (fun _ => rfl), producer.q_mem,
    producer.bound⟩⟩

/-- q = 8 bridge. The hypothesis is the unresolved v13 boundary producer,
kept explicit so this theorem does not claim the contour estimate. -/
theorem certificate_q8_of_bound (h8 : concreteNegContourB 8) :
    Nonempty (NegContourRectangleCertificate hpBSequence 8) := by
  apply certificate_of_concrete_producer
  exact { q_mem := by simp [negativeContourBases], bound := h8 }

/-- q = 9 bridge. -/
theorem certificate_q9_of_bound (h9 : concreteNegContourB 9) :
    Nonempty (NegContourRectangleCertificate hpBSequence 9) := by
  apply certificate_of_concrete_producer
  exact { q_mem := by simp [negativeContourBases], bound := h9 }

/-- q = 10 bridge. -/
theorem certificate_q10_of_bound (h10 : concreteNegContourB 10) :
    Nonempty (NegContourRectangleCertificate hpBSequence 10) := by
  apply certificate_of_concrete_producer
  exact { q_mem := by simp [negativeContourBases], bound := h10 }

/-! A compact triple package for the final producer glue. -/
structure ExceptionalHpProducers : Prop where
  q8 : concreteNegContourB 8
  q9 : concreteNegContourB 9
  q10 : concreteNegContourB 10

theorem certificates_of_exceptional_producers
    (producers : ExceptionalHpProducers) :
    Nonempty (NegContourRectangleCertificate hpBSequence 8) ∧
      Nonempty (NegContourRectangleCertificate hpBSequence 9) ∧
      Nonempty (NegContourRectangleCertificate hpBSequence 10) := by
  exact ⟨certificate_q8_of_bound producers.q8,
    certificate_q9_of_bound producers.q9,
    certificate_q10_of_bound producers.q10⟩

end

end Li2Lean.B4.NegativeContour

#print axioms Li2Lean.B4.NegativeContour.certificate_of_concrete_producer
#print axioms Li2Lean.B4.NegativeContour.certificate_q8_of_bound
#print axioms Li2Lean.B4.NegativeContour.certificate_q9_of_bound
#print axioms Li2Lean.B4.NegativeContour.certificate_q10_of_bound
#print axioms Li2Lean.B4.NegativeContour.certificates_of_exceptional_producers
