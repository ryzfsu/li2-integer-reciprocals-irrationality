/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Construction-backed measure facts for the v2 signed-V evaluator.

The integer rows and Boolean checks do not identify their evaluator with a
measure.  This module records that missing bridge without putting an
unconstrained existential in a certificate: every cell witness is tied to the
same `VReferencePackage.measure`, every shard witness is tied to the same
`term` family, and the total identity is tied to that measure and source.
No q-specific instance is supplied here.
-/

import Li2Lean.B3.EnergySoundnessInputs

namespace Li2Lean

noncomputable section

namespace B3

open V
open V.EnergyCertI

/-! ## F-a .. F-g: cellwise evaluator enclosures -/

/- A witness is data in `Type`, while its three proof fields remain ordinary
  propositions.  This avoids the Prop-elimination trap and makes the chosen
  upper endpoint visible to the construction audit. -/
structure CellUpperBoundWitness (D : IData) (q : ℕ) (lr : IV)
    (piece : FPiece) (f : ℝ → ℝ) (a b : QF) : Type where
  upper : ℝ
  upper_mem : IK.IV.mem (fieldUB D q lr piece a b) upper
  pointwise : ∀ t, IK.val a ≤ t → t ≤ IK.val b → f t ≤ upper

structure CellUpperBoundFamily (D : IData) (q : ℕ) (lr : IV)
    (piece : FPiece) (f : ℝ → ℝ) : Type where
  witness : ∀ (a b : QF), 0 < a.2 → 0 < b.2 → IK.val a < IK.val b →
    CellUpperBoundWitness D q lr piece f a b

def CellUpperBoundFamily.toFact {D : IData} {q : ℕ} {lr : IV}
    {piece : FPiece} {f : ℝ → ℝ}
    (F : CellUpperBoundFamily D q lr piece f) :
    CellSoundnessFact D q lr (fieldUB D q lr piece) (match piece with
      | .x => kxQ q
      | .vlo => kvQ q
      | .vhi => kvQ q
      | .zneg => kzQ q
      | .zpos => kzQ q
      | .arc1 => kzQ q
      | .arc2 => kzQ q) f := by
  intro a b ha hb hab
  let w := F.witness a b ha hb hab
  exact ⟨w.upper, w.upper_mem, w.pointwise⟩

def CellUpperBoundFamily.toOn {D : IData} {q : ℕ} {lr : IV}
    {piece : FPiece} {f : ℝ → ℝ}
    (F : CellUpperBoundFamily D q lr piece f) :
    CellSoundnessOn (pieceDomain q piece).1 (pieceDomain q piece).2
      (fieldUB D q lr piece) f := by
  intro a b ha hb hloa hab hbhi
  let w := F.witness a b ha hb hab
  exact ⟨w.upper, w.upper_mem, w.pointwise⟩

/- The five pieces consumed by G-1/G-2 are kept as separate fields.  In
  particular, a proof for X cannot be reused for V or Z by changing a label. -/
structure VFieldCellSoundness (D : IData) (q : ℕ) (lr : IV)
    (ν : V.SignedVMeasures) : Type where
  x : CellUpperBoundFamily D q lr .x
    (fun t => V.signedVFullFieldX ν (t : ℂ))
  vlo : CellUpperBoundFamily D q lr .vlo
    (fun t => V.signedVFullFieldV ν (t : ℂ))
  vhi : CellUpperBoundFamily D q lr .vhi
    (fun t => V.signedVFullFieldV ν (t : ℂ))
  zneg : CellUpperBoundFamily D q lr .zneg
    (fun t => V.signedVFullFieldZ ν (t : ℂ))
  zpos : CellUpperBoundFamily D q lr .zpos
    (fun t => V.signedVFullFieldZ ν (t : ℂ))

/- The existing soundness ledger uses a uniform family predicate.  This
  projection is only packaging: it does not prove any cell witness. -/
theorem VFieldCellSoundness.toFacts {D : IData} {q : ℕ} {lr : IV}
    {ν : V.SignedVMeasures} (F : VFieldCellSoundness D q lr ν) :
    CellSoundnessOn (pieceDomain q .x).1 (pieceDomain q .x).2
      (fieldUB D q lr .x)
        (fun t => V.signedVFullFieldX ν (t : ℂ)) ∧
    CellSoundnessOn (pieceDomain q .vlo).1 (pieceDomain q .vlo).2
      (fieldUB D q lr .vlo)
        (fun t => V.signedVFullFieldV ν (t : ℂ)) ∧
    CellSoundnessOn (pieceDomain q .vhi).1 (pieceDomain q .vhi).2
      (fieldUB D q lr .vhi)
        (fun t => V.signedVFullFieldV ν (t : ℂ)) ∧
    CellSoundnessOn (pieceDomain q .zneg).1 (pieceDomain q .zneg).2
      (fieldUB D q lr .zneg)
        (fun t => V.signedVFullFieldZ ν (t : ℂ)) ∧
    CellSoundnessOn (pieceDomain q .zpos).1 (pieceDomain q .zpos).2
      (fieldUB D q lr .zpos)
        (fun t => V.signedVFullFieldZ ν (t : ℂ)) := by
  exact ⟨F.x.toOn, F.vlo.toOn, F.vhi.toOn, F.zneg.toOn,
    F.zpos.toOn⟩

/-! The H3 field ledger is consumed through the piece-restricted domains.
This named projection keeps all five field bounds attached to the same decoded
source and reference measure; it does not reintroduce unrestricted
`CellSoundnessFact` quantification. -/
theorem fieldUB_sound_on {D : IData} {q : ℕ} {lr : IV}
    {ν : V.SignedVMeasures} (F : VFieldCellSoundness D q lr ν) :
    CellSoundnessOn (pieceDomain q .x).1 (pieceDomain q .x).2
        (fieldUB D q lr .x)
        (fun t => V.signedVFullFieldX ν (t : ℂ)) ∧
    CellSoundnessOn (pieceDomain q .vlo).1 (pieceDomain q .vlo).2
        (fieldUB D q lr .vlo)
        (fun t => V.signedVFullFieldV ν (t : ℂ)) ∧
    CellSoundnessOn (pieceDomain q .vhi).1 (pieceDomain q .vhi).2
        (fieldUB D q lr .vhi)
        (fun t => V.signedVFullFieldV ν (t : ℂ)) ∧
    CellSoundnessOn (pieceDomain q .zneg).1 (pieceDomain q .zneg).2
        (fieldUB D q lr .zneg)
        (fun t => V.signedVFullFieldZ ν (t : ℂ)) ∧
    CellSoundnessOn (pieceDomain q .zpos).1 (pieceDomain q .zpos).2
        (fieldUB D q lr .zpos)
        (fun t => V.signedVFullFieldZ ν (t : ℂ)) := by
  exact F.toFacts

/-! ## E-a .. E-d: shard enclosures -/

structure EnergyShardWitness (D : IData) (q : ℕ) (lr : IV)
    (e : EKind × ℕ × ℕ × Int) (term : EKind → ℕ → ℝ) : Type where
  check : energyShardOK D q lr e.1 e.2.1 e.2.2.1 e.2.2.2 = true
  enclosure : IK.IV.mem (energyShard D q lr e.1 e.2.1 e.2.2.1)
    (∑ i ∈ Finset.Ico e.2.1 e.2.2.1, term e.1 i)

structure EnergyShardSoundness (D : IData) (q : ℕ) (lr : IV)
    (plan : List (EKind × ℕ × ℕ × Int)) (term : EKind → ℕ → ℝ) : Type where
  witness : ∀ (e : EKind × ℕ × ℕ × Int), e ∈ plan →
    EnergyShardWitness D q lr e term

theorem EnergyShardSoundness.toFact {D : IData} {q : ℕ} {lr : IV}
    {plan : List (EKind × ℕ × ℕ × Int)} {term : EKind → ℕ → ℝ}
    (S : EnergyShardSoundness D q lr plan term) :
    EnergyShardSoundnessFact D q lr plan term := by
  intro e he
  let w := S.witness e he
  exact ⟨w.check, w.enclosure⟩

/-! ## T: signed quadratic decomposition -/

structure SignedQuadraticTotalIdentity (ν : V.SignedVMeasures)
    (D : IData) (plan : List (EKind × ℕ × ℕ × Int))
    (term : EKind → ℕ → ℝ) : Type where
  identity : V.signedVQuadratic ν =
    (allKinds.map fun k =>
      ∑ i ∈ Finset.range (kindCount D k), term k i).sum

theorem SignedQuadraticTotalIdentity.toFact
    {ν : V.SignedVMeasures} {D : IData}
    {plan : List (EKind × ℕ × ℕ × Int)} {term : EKind → ℕ → ℝ}
    (T : SignedQuadraticTotalIdentity ν D plan term) :
    EnergyTotalSoundnessFact ν D plan term :=
  T.identity

/-! ## Complete same-measure input -/

structure VReferenceEnergyMeasureFacts (q : ℕ)
    (hq : SignedVBaseRange q) : Type where
  reference : VReferencePackage q hq
  source : V13DecodedRows q
  lr : IV
  lr_sound : IK.IV.mem lr (Real.log (3 / 5 : ℝ))
  plan : List (EKind × ℕ × ℕ × Int)
  term : EKind → ℕ → ℝ
  qlow_value : IK.val (qlowQ q) = (vQlow q : ℝ)
  fields : VFieldCellSoundness source.data q lr reference.measure
  shards : EnergyShardSoundness source.data q lr plan term
  total : SignedQuadraticTotalIdentity reference.measure source.data plan term

/-! This projection is deliberately the only bridge into the older ledger:
it merely repackages named construction obligations and cannot synthesize any
measure, cell endpoint, shard enclosure, or total identity. -/
def VReferenceEnergyMeasureFacts.toLedger {q : ℕ}
    {hq : SignedVBaseRange q} (F : VReferenceEnergyMeasureFacts q hq) :
    VReferenceEnergySoundnessLedger q hq := by
  rcases F.fields.toFacts with ⟨hx, hvlo, hvhi, hzn, hzp⟩
  exact
    { reference := F.reference
      source := F.source
      lr := F.lr
      lr_sound := F.lr_sound
      plan := F.plan
      term := F.term
      qlow_value := F.qlow_value
      field_x := hx
      field_vlo := hvlo
      field_vhi := hvhi
      field_zneg := hzn
      field_zpos := hzp
      energy := F.shards.toFact
      total := F.total.toFact }

/-! Named obligation predicates for the ledger.  The predicates quantify over
the Type-level carrier, so the q2/q5 finite row tables alone cannot inhabit
them and no q3/q4/q6/q7 data is inferred. -/
def v13_field_cell_obligation (q : ℕ) (hq : SignedVBaseRange q)
    (D : IData) (lr : IV) (ν : V.SignedVMeasures) : Prop :=
  Nonempty (VFieldCellSoundness D q lr ν)

def v13_energy_shard_obligation (q : ℕ) (hq : SignedVBaseRange q)
    (D : IData) (lr : IV) (plan : List (EKind × ℕ × ℕ × Int))
    (term : EKind → ℕ → ℝ) : Prop :=
  Nonempty (EnergyShardSoundness D q lr plan term)

def v13_energy_total_obligation (q : ℕ) (hq : SignedVBaseRange q)
    (ν : V.SignedVMeasures) (D : IData)
    (plan : List (EKind × ℕ × ℕ × Int))
    (term : EKind → ℕ → ℝ) : Prop :=
  Nonempty (SignedQuadraticTotalIdentity ν D plan term)

end B3

end

end Li2Lean

