/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/

import Li2Lean.B3.ArithmeticPinning
import Li2Lean.B3.SignedProducerAdapters
import Li2Lean.B3.ProducerInterfaces
import Li2Lean.V.NonvanishingPlan

/-!
# Construction-bound signed-V integerizer producers

The endpoint layer needs an integerizer for the *actual* signed determinant
`V.vPolynomial n (-q)`.  The producer below extends the existing
`VActualIntegerizerCertificate` with the coefficientwise Gauss valuation used
by the residue-block and outer-pole parts of the v13 argument.  In particular,
there is no free valuation function and no theorem that silently supplies the
valuation/PNT estimates: those estimates remain fields of the producer.

Paper sources: `v-arithmetic.tex:37-421`, especially the local credits at
`:128-133` and the prime-product/rate argument at `:353-421`.  The actual
determinant and Gauss valuation are reused from `B3.ArithmeticPinning`.
-/

namespace Li2Lean
namespace B3

noncomputable section

open scoped BigOperators

/-! ## Actual valuation and producer boundary -/

/-- The coefficientwise Gauss valuation of the signed determinant at the
paper index `m = 4 n`.  This is the valuation used by every q-specific
residue/outer-pole adapter; it is not an arbitrary `vp` field.

v13: `v-arithmetic.tex:128-133,353-421`. -/
def actualVGaussValuation (q n p : ℕ) : ℤ :=
  V.actualGaussValuation p (V.actualVDeterminant q (4 * n))

/-- A construction-bound integerizer producer.  The inherited fields pin the
clearing polynomial to the actual `V.vPolynomial n (-q)` and carry the full
PNT rate.  `primeExponent` and `valuation_bound` are the remaining explicit
residue-block/outer-pole inputs from v13; no proof is supplied here.

v13: `v-arithmetic.tex:128-133,289-421`. -/
structure VActualIntegerizerProducer (q : ℕ) (tau : ℝ) where
  certificate : V.VActualIntegerizerCertificate q tau
  primeExponent : ℕ → ℕ → ℤ
  valuation_bound : ∀ n p : ℕ, p.Prime →
    actualVGaussValuation q n p ≥ -primeExponent n p

/-- q-specific producer aliases.  Their fields remain obligations for the
actual signed determinant; these aliases only pin the base and rate. -/
abbrev VActualIntegerizerProducerQ2 :=
  VActualIntegerizerProducer 2 (vTau 2)

abbrev VActualIntegerizerProducerQ3 :=
  VActualIntegerizerProducer 3 (vTau 3)

abbrev VActualIntegerizerProducerQ4 :=
  VActualIntegerizerProducer 4 (vTau 4)

abbrev VActualIntegerizerProducerQ5 :=
  VActualIntegerizerProducer 5 (vTau 5)

abbrev VActualIntegerizerProducerQ6 :=
  VActualIntegerizerProducer 6 (vTau 6)

abbrev VActualIntegerizerProducerQ7 :=
  VActualIntegerizerProducer 7 (vTau 7)

/-! The underlying certificate aliases expose the exact endpoint input type
`VActualIntegerizerCertificate q (vTau q)` for each fixed base.  They are kept
separate from the producer wrappers so existing adapters can consume the
certificate without importing the valuation side conditions. -/
abbrev VActualIntegerizerCertificateQ2 :=
  V.VActualIntegerizerCertificate 2 (vTau 2)

abbrev VActualIntegerizerCertificateQ3 :=
  V.VActualIntegerizerCertificate 3 (vTau 3)

abbrev VActualIntegerizerCertificateQ4 :=
  V.VActualIntegerizerCertificate 4 (vTau 4)

abbrev VActualIntegerizerCertificateQ5 :=
  V.VActualIntegerizerCertificate 5 (vTau 5)

abbrev VActualIntegerizerCertificateQ6 :=
  V.VActualIntegerizerCertificate 6 (vTau 6)

abbrev VActualIntegerizerCertificateQ7 :=
  V.VActualIntegerizerCertificate 7 (vTau 7)

/-- The six signed bases used by the v13 range. -/
structure VActualIntegerizerProducers where
  q2 : VActualIntegerizerProducerQ2
  q3 : VActualIntegerizerProducerQ3
  q4 : VActualIntegerizerProducerQ4
  q5 : VActualIntegerizerProducerQ5
  q6 : VActualIntegerizerProducerQ6
  q7 : VActualIntegerizerProducerQ7

/-! A compact endpoint-facing bundle of the six actual certificate inputs. -/
structure VActualIntegerizerCertificates where
  q2 : VActualIntegerizerCertificateQ2
  q3 : VActualIntegerizerCertificateQ3
  q4 : VActualIntegerizerCertificateQ4
  q5 : VActualIntegerizerCertificateQ5
  q6 : VActualIntegerizerCertificateQ6
  q7 : VActualIntegerizerCertificateQ7

/-! ## Degree and endpoint adapters -/

/-- Degree is unconditional algebra for the actual determinant family.  The
positive `a = 2` family remains the same `V.vPolynomial` instance, so this
also serves as the regression path requested for the 1/2 formalization.

v13: `v-arithmetic.tex:24-32`; reuse `V.vPolynomial_natDegree_le`. -/
theorem vActualDegreeBound (q : ℕ) : VDegreeBound q := by
  intro n _hn
  rw [vRealPoly_four_mul]
  exact Polynomial.natDegree_map_le.trans (V.vPolynomial_natDegree_le n _)

/-- Select the actual integerizer producer for a base in the signed range.
The interval proof only chooses a field; it does not prove any valuation or
PNT obligation hidden in that field.
-/
def VActualIntegerizerProducers.at
    (P : VActualIntegerizerProducers) {q : ℕ}
    (hq : SignedVBaseRange q) :
    VActualIntegerizerProducer q (vTau q) := by
  obtain ⟨hlo, hhi⟩ := hq
  interval_cases q
  · exact P.q2
  · exact P.q3
  · exact P.q4
  · exact P.q5
  · exact P.q6
  · exact P.q7

/-- A construction-bound producer gives the arithmetic plan after the
unconditional degree lemma. -/
theorem arithmeticPlan_of_actual_integerizer_producer
    {q : ℕ} (P : VActualIntegerizerProducer q (vTau q)) : ArithmeticPlan q :=
  { degree := vActualDegreeBound q
    integerizer :=
      B3.actualIntegerizer_toVIntegerizerBound P.certificate }

/-- q=2 regression: the generalized family still evaluates to the same
positive `a = 2` determinant used by the frozen 1/2 code. -/
theorem actualIntegerizer_a2_regression (n : ℕ) :
    V.actualDeterminantAt 2 (4 * n) = V.vPolynomial n (2 : ℤ) := by
  simpa [V.actualDeterminantAt, Nat.mul_div_cancel_left n
    (by norm_num : (0 : ℕ) < 4)]

end
end B3
end Li2Lean

#print axioms Li2Lean.B3.vActualDegreeBound
#print axioms Li2Lean.B3.arithmeticPlan_of_actual_integerizer_producer
