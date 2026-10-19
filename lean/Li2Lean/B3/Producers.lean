/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
/-
Construction-specific producer obligations for the signed V route.
This module depends on the top-down interfaces and on the existing actual
S0/producer adapters, so those adapters do not create an import cycle.

This module exposes adapter interfaces; the concrete integerizer,
Frobenius-tower, and positive-HP decay inputs are supplied by the closed
AllN assembly.
-/

import Li2Lean.B3.ProducerInterfaces
import Li2Lean.B3.S0Actual
import Li2Lean.B3.PreboundLeafInterfaces
import Li2Lean.B3.SignedProducerAdapters
import Li2Lean.B3.ActualIntegerizerRange
import Li2Lean.B3.NonvanishingProducerWiring
import Li2Lean.B3.ActualFrobeniusTowerCarriers
import Li2Lean.B3.Q3RationalIntegerizerAdapter
import Li2Lean.B3.Q2Q4RationalIntegerizerAdapters
import Li2Lean.B3.Q567ArithmeticContracts
import Li2Lean.B3.ReferencePackageAdapter
import Li2Lean.B3.ReferencePackageProducer
import Li2Lean.B3.ReferencePackageLeaves
import Li2Lean.B3.H4IntegerizerAssembly

namespace Li2Lean.B3

noncomputable section

/-! ## Construction-bound Frobenius carrier entry point

`ActualFrobeniusTowerCarriers` owns the six source-bound obligations. These
aliases keep the producer boundary in this module, without replacing any
seed, determinant, scaled-integrality, or strict-tail field by a conclusion-
shaped proposition.
-/

theorem v13_frobenius_q2_input :
    VActualFrobeniusTowerQ2Inputs :=
  vActualFrobeniusTowerCarrier_q2

theorem v13_frobenius_q3_producer :
    VActualFrobeniusTowerProducerQ3 :=
  vActualFrobeniusTowerCarrier_q3

theorem v13_frobenius_q4_producer :
    VActualFrobeniusTowerProducerQ4 :=
  vActualFrobeniusTowerCarrier_q4

theorem v13_frobenius_q5_producer :
    VActualFrobeniusTowerProducerQ5 :=
  vActualFrobeniusTowerCarrier_q5

theorem v13_frobenius_q6_producer :
    VActualFrobeniusTowerProducerQ6 :=
  vActualFrobeniusTowerCarrier_q6

theorem v13_frobenius_q7_producer :
    VActualFrobeniusTowerProducerQ7 :=
  vActualFrobeniusTowerCarrier_q7

theorem v13_frobenius_range_producer :
    VActualFrobeniusTowerProducers :=
  { q2 := fun hq => by
      have hq_eq : hq = q2SignedRange := Subsingleton.elim _ _
      exact hq_eq ▸ v13_frobenius_q2_input.toProducer
    q3 := v13_frobenius_q3_producer
    q4 := v13_frobenius_q4_producer
    q5 := v13_frobenius_q5_producer
    q6 := v13_frobenius_q6_producer
    q7 := v13_frobenius_q7_producer }

/-! ## Construction-specific producer obligations -/

/-! ## Construction-bound reference package inputs

The reference package is the construction-bound source for the signed energy
certificate.  Its measure and all analytic fields remain explicit in the
package; this boundary keeps the complete ledger attached to the construction
instead of treating finite shard checks as a measure-level proof.  The input is
the complete ledger from
`B3.ReferencePackageProducer`: qlow, field-cell, energy-shard, and total
quadratic fields stay attached to the same reference measure.
-/

noncomputable def v13_reference_package_input_producer
    {q : ℕ} (hq : SignedVBaseRange q) : V13ReferencePackageInput q hq := by
  have hq2 : 2 ≤ q := hq.1
  have hq7 : q ≤ 7 := hq.2
  interval_cases q
  · exact v13_reference_package_input_q2 hq
  · exact v13_reference_package_input_q3 hq
  · exact v13_reference_package_input_q4 hq
  · exact v13_reference_package_input_q5 hq
  · exact v13_reference_package_input_q6 hq
  · exact v13_reference_package_input_q7 hq

noncomputable def v13_reference_package_producer
    {q : ℕ} (hq : SignedVBaseRange q) : VReferencePackage q hq :=
  v13_reference_package_of_input (v13_reference_package_input_producer hq)

/-! ## Input-to-plan adapters

These constructors are the downstream wiring promised by the top-down
interfaces. Each input is tied to the actual v13 family by its definition;
none of these lemmas invents a measure, valuation, determinant, or Frobenius
tower. The remaining construction obligations are kept explicit in
`AllN/Producers.lean`; this file never manufactures a tower without its
producer input.
-/

/- Per-base energy input -> signed energy plan. Source:
v13 `v-analytic.tex:220-301,337-408`. -/
theorem signed_energy_plan_of_certificate
    {q : ℕ} (hq : SignedVBaseRange q)
    (certificate : VEnergyCertificate q (vAlpha q) (vSigma q)) :
    SignedEnergyPlan q :=
  { base_range := hq
    certificate := certificate }

/- Multiplicative S0 transfer input -> all-m prebound. Source:
v13 `v-analytic.tex:106-145,493-631`; the determinant and `G != 0` guard
are fixed by `VContourS0TransferData`. -/
theorem smoothing_prebound_of_transfer
    {q : ℕ} (hq : SignedVBaseRange q)
    (transfer : VContourS0TransferData q (vAlpha q) (vSigma q))
    (hσ : ∃ Ax Av Az : ℝ,
      0 ≤ Ax ∧ 0 ≤ Av ∧ 0 ≤ Az ∧
        vSigma q = sigmaBudget Ax Av Az) :
    VAllMPreboundProducer q (vAlpha q) (vSigma q) := by
  exact vAllMPreboundProducer_of_s0_transfer transfer hσ

/-! The corrected actual transfer has an n-dependent source.  It therefore
cannot be coerced to the legacy fixed-`phiMax` carrier: the actual source and
its S0 data must stay together through the prebound calculation. -/
theorem vRawPrebound_of_actual_transfer_in_producers
    {q : ℕ} {alpha sigma : ℝ}
    (H : VContourS0TransferDataActual q alpha sigma) :
    VRawPrebound q alpha sigma := by
  intro n hn hreal
  have D := H.s0_data n
  have hcomplex : vContourActualGValue q n ≠ 0 := by
    rw [vContourActualGValue_eq_vRealPoly]
    exact Complex.ofReal_ne_zero.mpr hreal
  have hmag := vContourS0Magnitude_of_data D
  have hlog := Real.log_le_log (norm_pos_iff.mpr hcomplex) hmag
  rw [vContourActualGValue_eq_vRealPoly] at hlog
  rw [Complex.norm_real, Real.norm_eq_abs] at hlog
  have hpref : 0 < s0TransferPrefactor q n :=
    s0TransferPrefactor_pos H.q_ge_two
  have hpow : 0 < H.Tq ^ (4 * n) := pow_pos H.Tq_pos _
  have htriple : V.Literal.vContourTripleIntegral q n ≠ 0 := by
    intro hzero
    rw [D.determinant_identity, hzero, mul_zero] at hcomplex
    exact hcomplex rfl
  have hphi : 0 < |v13PhiMaxValue q H.Tq n| := by
    exact abs_pos.mpr (v13PhiMaxValue_pos H.Tq_pos n htriple).ne'
  have hfirst : s0TransferPrefactor q n * H.Tq ^ (4 * n) ≠ 0 :=
    (mul_pos hpref hpow).ne'
  rw [show s0MagnitudeRhs q (4 * n) (5 * n) H.Tq
      (v13PhiMaxValue q H.Tq n) =
      s0TransferPrefactor q n * H.Tq ^ (4 * n) *
        |v13PhiMaxValue q H.Tq n| by rfl] at hlog
  rw [Real.log_mul hfirst hphi.ne'] at hlog
  have htransfer := H.phi_log_bound n htriple hn
  unfold s0TransferPhiBudget at htransfer
  linarith

theorem smoothing_prebound_of_actual_transfer_in_producers
    {q : ℕ} (hq : SignedVBaseRange q)
    (energy : SignedEnergyPlan q)
    (H : VContourS0TransferDataActual q (vAlpha q) (vSigma q)) :
    VAllMPreboundProducer q (vAlpha q) (vSigma q) := by
  rcases energy.certificate with
    ⟨ν, Qlow, Kx, Kv, Kz, Ax, Av, Az,
      hν, hμx, hμv, hμz, hnx, hnv, hnz,
      hAx, hAv, hAz, hBx, hBv, hBz, hσ, hQ, hFx, hFv, hFz, hα⟩
  exact producer_of_rawPrebound hq.1 hq.2
    ⟨Ax, Av, Az, hAx, hAv, hAz, hσ⟩
    (vRawPrebound_of_actual_transfer_in_producers H)

/-! The remaining S0 calculation is assembled from the six explicit signed
base leaves.  The finite case split only selects the corresponding
construction input; the analytic content remains in the Actual carrier. -/
noncomputable def v13_s0_transfer_producer
    {q : ℕ} (hq : SignedVBaseRange q)
    (energy : SignedEnergyPlan q) :
    VContourS0TransferDataActual q (vAlpha q) (vSigma q) :=
  v13_s0_transfer_actual_generic hq (v13_reference_package_producer hq)

theorem sigma_witness_of_energy
    {q : ℕ} (energy : SignedEnergyPlan q) :
    ∃ Ax Av Az : ℝ,
      0 ≤ Ax ∧ 0 ≤ Av ∧ 0 ≤ Az ∧
        vSigma q = sigmaBudget Ax Av Az := by
  rcases energy.certificate with
    ⟨ν, Qlow, Kx, Kv, Kz, Ax, Av, Az,
      hν, hμx, hμv, hμz, hnx, hnv, hnz,
      hAx, hAv, hAz, hBx, hBv, hBz, hσ, hQ, hFx, hFv, hFz, hα⟩
  exact ⟨Ax, Av, Az, hAx, hAv, hAz, hσ⟩

/- Actual integerizer input -> arithmetic plan. Source:
v13 `v-arithmetic.tex:353-421`; the degree proof is a separate producer. -/
theorem arithmetic_plan_of_actual_certificate
    {q : ℕ} (degree : VDegreeBound q)
    (certificate : V.VActualIntegerizerCertificate q (vTau q)) :
    ArithmeticPlan q :=
  arithmeticPlan_of_actual_integerizer degree certificate

/-- Construction-backed arithmetic adapter for the rational v13 divisor.
The divisor is the explicit prime product carried by `P`; the residue-block
valuation and weighted prime-sum estimate remain fields of that same producer.
This is the downstream replacement for the old free-certificate route.

v13: `v-arithmetic.tex:128-421`; degree and determinant identity at
`:24-32,353-421`. -/
theorem arithmetic_plan_of_v13_from_producer
    {q : ℕ} (P : VActualRationalIntegerizerProducer q (vTau q)) :
    ArithmeticPlan q :=
  arithmeticPlan_of_actual_rational_producer P

/-! The q = 3 bridge is available downstream without changing the
construction obligation. Its valuation and prime-sum fields remain explicit
q = 3 inputs, and this adapter does not manufacture either one. -/
theorem arithmetic_plan_of_q3_actual_inputs
    (h : Li2Lean.V.Q3Integerizer.Q3ActualIntegerizerInputs (vTau 3)) :
    ArithmeticPlan 3 :=
  q3_arithmetic_plan_of_actual_inputs h

/-! ## Generic actual rational integerizer input

One named construction obligation supplies the actual rational producer for
every base in `SignedVBaseRange`. The finite family below only selects this
same q-generic target at the six permitted bases; it does not duplicate the
valuation and rate obligations. This is a completed construction, not a completed
integerizer proof. The generic fields are derived from the
q-uniform p-adic valuation bound for the actual determinant from its source
matrix rows and proving the weighted finite-prime-sum rate bound at `vTau q`;
the producer's `n = 0` exponent clause is handled separately.

v13: `v-arithmetic.tex:128-421`. -/

noncomputable def v13_actual_rational_integerizer_generic
    {q : ℕ} (hq : SignedVBaseRange q) :
    VActualRationalIntegerizerProducer q (vTau q) :=
  v13ActualRationalIntegerizerH4 hq

/-! The family is finite range bookkeeping over the one generic obligation.
No per-base valuation or prime-sum input is manufactured here. -/
noncomputable def v13_rational_integerizer_family :
    VActualRationalIntegerizerProducerFamily :=
  { q2 := v13_actual_rational_integerizer_generic ⟨by norm_num, by norm_num⟩
    q3 := v13_actual_rational_integerizer_generic ⟨by norm_num, by norm_num⟩
    q4 := v13_actual_rational_integerizer_generic ⟨by norm_num, by norm_num⟩
    q5 := v13_actual_rational_integerizer_generic ⟨by norm_num, by norm_num⟩
    q6 := v13_actual_rational_integerizer_generic ⟨by norm_num, by norm_num⟩
    q7 := v13_actual_rational_integerizer_generic ⟨by norm_num, by norm_num⟩ }

/-! The outer producer is now an explicit q = 2,...,7 assembly. -/
noncomputable def v13_rational_integerizer_producer
    {q : ℕ} (hq : SignedVBaseRange q) :
    VActualRationalIntegerizerProducer q (vTau q) :=
  v13_rational_integerizer_family.at hq

/- Actual corrected Frobenius input -> nonvanishing plan. Source:
v13 `nonvanishing.tex:200-275`; this uses the `vPolynomial (p^k)` target. -/
theorem nonvanishing_plan_of_actual_tower
    {q : ℕ}
    (tower : V.VActualFrobeniusTower q (vSeedPrime q)) :
    NonvanishingPlan q := by
  exact nonvanishingPlan_of_actual_tower tower rfl

/-! A package itself already contains all measure-level energy facts.  This
adapter is deliberately independent of the six-base producer, so callers
with a concrete package do not need to depend on the construction leaves. -/
theorem signed_energy_plan_of_package
    {q : ℕ} {hq : SignedVBaseRange q}
    (P : VReferencePackage q hq) : SignedEnergyPlan q := by
  exact { base_range := hq, certificate := P.facts.toEnergyCertificate }

/-! ## Explicit range adapter

The six-base producer is a genuine construction input. In particular, the
finite seed boundary and the coefficientwise p-adic/tail obligations are not
derivable from `SignedVBaseRange q` alone. The selected base is passed to the
existing actual-producer range adapter.
Source: v13 `nonvanishing.tex:146-275`. -/

theorem nonvanishing_plan_of_v13_from_range_inputs
    (inputs : VActualFrobeniusTowerProducers)
    {q : ℕ} (hq : SignedVBaseRange q) : NonvanishingPlan q :=
  nonvanishing_plan_of_actual_frobenius_producers inputs hq

/-- Per-base signed energy certificate. v13: `v-analytic.tex:220-301,337-408`
and `v-reference-data.tex`. -/
theorem signed_energy_plan_of_v13
    {q : ℕ} (hq : SignedVBaseRange q) : SignedEnergyPlan q := by
  exact signed_energy_plan_of_package
    (v13_reference_package_producer hq)

/-! A construction-backed version of the same adapter.  This is the route
used once the q-specific row/evaluator/measure ledger is inhabited; it keeps
the finite EnergyCertI checks and the semantic reference facts distinct. -/
theorem signed_energy_plan_of_reference_input
    {q : ℕ} {hq : SignedVBaseRange q}
    (I : V13ReferencePackageInput q hq) : SignedEnergyPlan q := by
  exact signed_energy_plan_of_package (v13_reference_package_of_input I)

/-- All-m smoothing prebound. v13: `v-analytic.tex:493-631`; it consumes the
actual multiplicative S0 bound and the same signed measure as the energy
certificate. -/
theorem smoothing_prebound_of_v13
    {q : ℕ} (hq : SignedVBaseRange q) (energy : SignedEnergyPlan q) :
    VAllMPreboundProducer q (vAlpha q) (vSigma q) := by
  exact smoothing_prebound_of_actual_transfer_in_producers hq energy
    (v13_s0_transfer_producer hq energy)

/-- Actual degree and integerization producers. v13: `v-arithmetic.tex:37-421`.
-/
theorem arithmetic_plan_of_v13
    {q : ℕ} (hq : SignedVBaseRange q) : ArithmeticPlan q := by
  exact arithmetic_plan_of_v13_from_producer
    (v13_rational_integerizer_producer hq)

/-! ## Endpoint assembly and the six range theorems -/

theorem endpoint_certificate_of_v13_chain
    {q : ℕ} (hq : SignedVBaseRange q)
    (energy : SignedEnergyPlan q)
    (smoothing : VAllMPreboundProducer q (vAlpha q) (vSigma q))
    (arithmetic : ArithmeticPlan q)
    (nonvanishing : NonvanishingPlan q) :
    Nonempty (EndpointCertificate (li2InvValue (signedBase q))) := by
  obtain ⟨hp, hp11⟩ := vSeedPrime_spec hq
  exact signedV_endpointCertificate_of_hypotheses hp hp11 (vTau_lt_vAlpha hq)
    { analytic := signedVSmoothingBound_of_producer smoothing
      degree := arithmetic.degree
      integerizer := arithmetic.integerizer
      nonvanishing := nonvanishing.eventual }

theorem signed_v_range_of_v13 {q : ℕ} (hq : SignedVBaseRange q)
    (energy : SignedEnergyPlan q)
    (smoothing : VAllMPreboundProducer q (vAlpha q) (vSigma q))
    (arithmetic : ArithmeticPlan q)
    (nonvanishing : NonvanishingPlan q) :
    Irrational (li2InvValue (signedBase q)) := by
  obtain ⟨c⟩ := endpoint_certificate_of_v13_chain hq energy smoothing arithmetic
    nonvanishing
  exact ContourKit.endpoint_criterion c

end

end Li2Lean.B3

#print axioms Li2Lean.B3.signed_v_range_of_v13
