/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Construction input for the v13 signed-V reference package.

This file is intentionally an input boundary.  A `VReferencePackage` by
itself is not enough to justify the energy producer: the decoded rows, the
integer evaluator, and the analytic interpretation must all refer to the
same measure.  `VReferenceEnergySoundnessLedger` carries those obligations
as Type-level data plus explicit propositions.  There is no default instance
and no theorem from a base-range hypothesis alone.
-/

import Li2Lean.B3.EnergySoundnessInputs

namespace Li2Lean

noncomputable section

namespace B3

/-!
`V13ReferencePackageInput` is the sole construction-backed input accepted by
the reference-package adapter.  Its `soundness` field contains:

* the concrete measure and its support/atomlessness/integrability facts;
* the exact decoded row source and the `qlow_value` decoder equality;
* the per-cell field obligations (`field_x`, `field_vlo`, `field_vhi`,
  `field_zneg`, `field_zpos`), representing the F-a..F-g ledger;
* the per-shard enclosure and total signed quadratic identity (`energy` and
  `total`), representing the E-a..E-d and T obligations.

The package cannot be inhabited merely by restating the desired field or
energy bound: every one of these fields is supplied by the ledger.
-/
structure V13ReferencePackageInput (q : ℕ) (hq : SignedVBaseRange q) where
  soundness : VReferenceEnergySoundnessLedger q hq

def V13ReferencePackageInput.reference
    {q : ℕ} {hq : SignedVBaseRange q}
    (I : V13ReferencePackageInput q hq) : VReferencePackage q hq :=
  I.soundness.reference

def V13ReferencePackageInput.measure
    {q : ℕ} {hq : SignedVBaseRange q}
    (I : V13ReferencePackageInput q hq) : V.SignedVMeasures :=
  I.reference.measure

theorem V13ReferencePackageInput.reference_facts
    {q : ℕ} {hq : SignedVBaseRange q}
    (I : V13ReferencePackageInput q hq) :
    VReferenceFacts q hq I.measure I.reference.Ax I.reference.Av
      I.reference.Az :=
  I.soundness.reference.facts

def V13ReferencePackageInput.decoded_rows
    {q : ℕ} {hq : SignedVBaseRange q}
    (I : V13ReferencePackageInput q hq) : V13DecodedRows q :=
  I.soundness.source

theorem V13ReferencePackageInput.log_reference_sound
    {q : ℕ} {hq : SignedVBaseRange q}
    (I : V13ReferencePackageInput q hq) :
    V.EnergyCertI.IK.IV.mem I.soundness.lr (Real.log (3 / 5 : ℝ)) :=
  I.soundness.lr_sound

theorem V13ReferencePackageInput.qlow_value
    {q : ℕ} {hq : SignedVBaseRange q}
    (I : V13ReferencePackageInput q hq) :
    V.EnergyCertI.IK.val (V.EnergyCertI.qlowQ q) = (vQlow q : ℝ) :=
  I.soundness.qlow_value

theorem V13ReferencePackageInput.field_inputs
    {q : ℕ} {hq : SignedVBaseRange q}
    (I : V13ReferencePackageInput q hq) :
    CellSoundnessOn (pieceDomain q .x).1 (pieceDomain q .x).2
      (V.EnergyCertI.fieldUB I.soundness.source.data q I.soundness.lr .x)
      (fun t => V.signedVFullFieldX I.measure (t : ℂ)) ∧
    CellSoundnessOn (pieceDomain q .vlo).1 (pieceDomain q .vlo).2
      (V.EnergyCertI.fieldUB I.soundness.source.data q I.soundness.lr .vlo)
      (fun t => V.signedVFullFieldV I.measure (t : ℂ)) ∧
    CellSoundnessOn (pieceDomain q .vhi).1 (pieceDomain q .vhi).2
      (V.EnergyCertI.fieldUB I.soundness.source.data q I.soundness.lr .vhi)
      (fun t => V.signedVFullFieldV I.measure (t : ℂ)) ∧
    CellSoundnessOn (pieceDomain q .zneg).1 (pieceDomain q .zneg).2
      (V.EnergyCertI.fieldUB I.soundness.source.data q I.soundness.lr .zneg)
      (fun t => V.signedVFullFieldZ I.measure (t : ℂ)) ∧
    CellSoundnessOn (pieceDomain q .zpos).1 (pieceDomain q .zpos).2
      (V.EnergyCertI.fieldUB I.soundness.source.data q I.soundness.lr .zpos)
      (fun t => V.signedVFullFieldZ I.measure (t : ℂ)) := by
  exact ⟨I.soundness.field_x, I.soundness.field_vlo, I.soundness.field_vhi,
    I.soundness.field_zneg, I.soundness.field_zpos⟩

theorem V13ReferencePackageInput.energy_inputs
    {q : ℕ} {hq : SignedVBaseRange q}
    (I : V13ReferencePackageInput q hq) :
    EnergyShardSoundnessFact I.soundness.source.data q I.soundness.lr
      I.soundness.plan I.soundness.term :=
  I.soundness.energy

theorem V13ReferencePackageInput.total_input
    {q : ℕ} {hq : SignedVBaseRange q}
    (I : V13ReferencePackageInput q hq) :
    EnergyTotalSoundnessFact I.measure I.soundness.source.data
      I.soundness.plan I.soundness.term :=
  I.soundness.total

/-! The adapter used by `Producers.lean`.  This is a projection, so it cannot
turn an absent ledger into a package. -/
def v13_reference_package_of_input
    {q : ℕ} {hq : SignedVBaseRange q}
    (I : V13ReferencePackageInput q hq) : VReferencePackage q hq :=
  I.reference

def v13_reference_package_of_ledger
    {q : ℕ} {hq : SignedVBaseRange q}
    (L : VReferenceEnergySoundnessLedger q hq) : VReferencePackage q hq :=
  L.reference

theorem v13_reference_energy_certificate_of_input
    {q : ℕ} {hq : SignedVBaseRange q}
    (I : V13ReferencePackageInput q hq) :
    VEnergyCertificate q (vAlpha q) (vSigma q) :=
  I.reference.facts.toEnergyCertificate

theorem v13_reference_energy_certificate_of_ledger
    {q : ℕ} {hq : SignedVBaseRange q}
    (L : VReferenceEnergySoundnessLedger q hq) :
    VEnergyCertificate q (vAlpha q) (vSigma q) :=
  L.reference.facts.toEnergyCertificate

/-!
Named ledger gaps for each base.  These are propositions requiring a real
`V13ReferencePackageInput`; they are not Boolean flags and have no inhabitant
until the corresponding measure, decoded rows, F/E soundness, T identity,
and qlow equality have been supplied.

Base-by-base inventory of the missing construction inputs:

* q = 2: `q2D` exists.  Still required: the concrete reference package
  (measure, support, atomlessness, ball bounds, sigma budget, energy/field
  inequalities, endpoint disks, integrability); a reference log interval;
  the qlow decoder equality; the five field-cell ledgers; the complete energy
  shard plan and E-a..E-d enclosures; and the T signed-quadratic identity.
* q = 3: all of the q = 2 items, plus its missing raw decoded-row declaration.
* q = 4: all of the q = 2 items; q4D is now supplied by Q4Rows, but its
  concrete measure and all F/E/T soundness fields remain to be proved.
* q = 5: `q5D` exists.  Still required: the same concrete package, log
  interval, qlow equality, five field-cell ledgers, complete energy shard
  plan and E-a..E-d enclosures, and T identity as for q = 2.
* q = 6: all of the q = 2 items, plus its missing raw decoded-row declaration.
* q = 7: all of the q = 2 items, plus its missing raw decoded-row declaration.

The `q2D`/`q5D` row tables alone do not supply any measure-level F/E/T fact.
Keeping one gap per base prevents a q = 2 certificate from being silently
reused at another base.
-/
def v13_reference_package_input_gap (q : ℕ) : Prop :=
  ∃ hq : SignedVBaseRange q, Nonempty (V13ReferencePackageInput q hq)

def q2_reference_package_input_gap : Prop :=
  v13_reference_package_input_gap 2

def q3_reference_package_input_gap : Prop :=
  v13_reference_package_input_gap 3

def q4_reference_package_input_gap : Prop :=
  v13_reference_package_input_gap 4

def q5_reference_package_input_gap : Prop :=
  v13_reference_package_input_gap 5

def q6_reference_package_input_gap : Prop :=
  v13_reference_package_input_gap 6

def q7_reference_package_input_gap : Prop :=
  v13_reference_package_input_gap 7

end B3

end

end Li2Lean

#print axioms Li2Lean.B3.v13_reference_package_of_input
#print axioms Li2Lean.B3.v13_reference_energy_certificate_of_input
