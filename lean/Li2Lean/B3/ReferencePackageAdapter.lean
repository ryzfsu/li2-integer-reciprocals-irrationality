/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Adapters for the construction-bound signed-V reference package.  The S0
fields below are inputs to the analytic proof; this file only packages them
and never manufactures a determinant identity or a logarithmic estimate.
-/

import Li2Lean.B3.ReferencePackage
import Li2Lean.B3.S0ActualInterface

namespace Li2Lean

noncomputable section

namespace B3

open MeasureTheory

/-! The same literal reference package is carried through the S0 interface.
The package's measure is therefore available to the energy, positivity, and
integrability proof without introducing a second free measure. -/

structure VContourS0TransferInput (q : ℕ)
    (hq : SignedVBaseRange q) where
  reference : VReferencePackage q hq
  Tq : ℝ
  Tq_pos : 0 < Tq
  /-- The single v13 maximum point, shared by every `n`. -/
  phiMax : ℝ
  phiMax_pos : 0 < phiMax
  /-- The determinant identity and triple norm estimate for the fixed v13
  contour.  These are the S0 obligations from `v-analytic.tex:106-145`. -/
  s0_data : ∀ n : ℕ, VContourS0Data q n Tq phiMax
  /-- The explicit v13 fixed-point transfer, before the S0 prefactor. -/
  phi_log_bound : ∀ n : ℕ, 64 ≤ 4 * n →
    Real.log |phiMax| ≤ s0TransferPhiBudget q (vAlpha q) (vSigma q)
      Tq phiMax n

def VContourS0TransferInput.referenceMeasure
    {q : ℕ} {hq : SignedVBaseRange q}
    (H : VContourS0TransferInput q hq) : V.SignedVMeasures :=
  H.reference.measure

theorem VContourS0TransferInput.energy_certificate
    {q : ℕ} {hq : SignedVBaseRange q}
    (H : VContourS0TransferInput q hq) :
    VEnergyCertificate q (vAlpha q) (vSigma q) :=
  H.reference.facts.toEnergyCertificate

def VContourS0TransferInput.toS0TransferData
    {q : ℕ} {hq : SignedVBaseRange q}
    (H : VContourS0TransferInput q hq) :
    VContourS0TransferData q (vAlpha q) (vSigma q) := by
  refine {
    q_ge_two := hq.1
    q_le_seven := hq.2
    Tq := H.Tq
    Tq_pos := H.Tq_pos
    phiMax := H.phiMax
    phiMax_pos := H.phiMax_pos
    s0_data := H.s0_data
    phi_log_bound := H.phi_log_bound }

end B3

end

end Li2Lean

#print axioms Li2Lean.B3.VContourS0TransferInput.energy_certificate
#print axioms Li2Lean.B3.VContourS0TransferInput.toS0TransferData
