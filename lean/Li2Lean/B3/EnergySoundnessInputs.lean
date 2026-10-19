/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Construction-bound input ledger for the v2 signed-V energy soundness layer.

The K-1..K-9 lemmas prove arithmetic soundness.  They do not manufacture the
v13 reference rows or identify an integer evaluator with the concrete signed
measure.  This file names that remaining interface explicitly.  In particular,
there is no default instance and no proposition-valued field carrying hidden
data.
-/

import Li2Lean.B3.ReferencePackage
import Li2Lean.V.EnergyCertI.ISoundGlue
import Li2Lean.V.EnergyCertI.Consts
import Li2Lean.V.EnergyCertI.Q2Rows
import Li2Lean.V.EnergyCertI.Q3Rows
import Li2Lean.V.EnergyCertI.Q4Rows
import Li2Lean.V.EnergyCertI.Q5Rows
import Li2Lean.V.EnergyCertI.Q7Rows
import Li2Lean.V.EnergyCertI.Q6Rows

namespace Li2Lean

noncomputable section

namespace B3

open V
open V.EnergyCertI
abbrev QF := V.EnergyCertI.IK.QF
abbrev IV := V.EnergyCertI.IK.IV

def CellSoundnessOn (lo hi : QF) (ub : QF → QF → IV) (f : ℝ → ℝ) : Prop :=
  ∀ a b : QF, 0 < a.2 → 0 < b.2 → IK.val lo ≤ IK.val a →
    IK.val a < IK.val b → IK.val b ≤ IK.val hi →
    ∃ U : ℝ, IK.IV.mem (ub a b) U ∧
      ∀ t, IK.val a ≤ t → t ≤ IK.val b → f t ≤ U

def pieceDomain (q : ℕ) : FPiece → QF × QF
  | .x => ((1, 250), (1, 1))
  | .vlo => ((1, 250), (3, 5))
  | .vhi => ((3, 5), (1, 1))
  | .zneg => ((-(q : ℤ), 1), (-3, 5))
  | .zpos => ((3, 5), (1, 1))
  | .arc1 => ((0, 1), (1, 1))
  | .arc2 => ((0, 1), (1, 1))

/-! A decoded row source is identified by the exact decoder output, rather than
by row counts alone.  The accepted q = 2 through q = 7 cases are backed by raw
rows decoded in the corresponding `EnergyCertI` modules.  Other q values must
add their own raw row declarations before an instance of this interface exists.
-/

structure V13DecodedRows (q : ℕ) where
  data : IData
  source : (q = 2 ∧ data = q2D) ∨
    (q = 4 ∧ data = q4D) ∨
    (q = 5 ∧ data = q5D) ∨
    (q = 7 ∧ data = q7D) ∨
    (q = 6 ∧ data = q6D) ∨
    (q = 3 ∧ data = q3D)

/-- The concrete q = 4 source decoded from the v13 row tables. -/
def q4DecodedRows : V13DecodedRows 4 :=
  { data := q4D
    source := Or.inr (Or.inl ⟨rfl, rfl⟩) }

/-- The q = 3 rows from v13 `v-reference-data.tex:84-153`. -/
def q3DecodedRows : V13DecodedRows 3 :=
  { data := q3D
    source := by
      right
      right
      right
      right
      right
      exact ⟨rfl, rfl⟩ }

/-! Per-cell F-a..F-g and per-shard E-a..E-d are carried as predicates whose
real functions are supplied by the same reference package.  Keeping the
functions explicit prevents a certificate for one measure from being reused
for another measure accidentally.
-/

def CellSoundnessFact (D : IData) (q : ℕ) (lr : IV)
    (ub : QF → QF → IV) (K : QF) (f : ℝ → ℝ) : Prop :=
  ∀ a b : QF, 0 < a.2 → 0 < b.2 → IK.val a < IK.val b →
    ∃ U : ℝ, IK.IV.mem (ub a b) U ∧
      ∀ t, IK.val a ≤ t → t ≤ IK.val b → f t ≤ U

theorem CellSoundnessFact.toOn
    {D : IData} {q : ℕ} {lr : IV} {ub : QF → QF → IV} {K : QF}
    {f : ℝ → ℝ} {lo hi : QF}
    (h : CellSoundnessFact D q lr ub K f) :
    CellSoundnessOn lo hi ub f := by
  intro a b ha hb hloa hab hbhi
  exact h a b ha hb hab

def EnergyShardSoundnessFact (D : IData) (q : ℕ) (lr : IV)
    (plan : List (EKind × ℕ × ℕ × Int)) (term : EKind → ℕ → ℝ) : Prop :=
  ∀ e ∈ plan,
    energyShardOK D q lr e.1 e.2.1 e.2.2.1 e.2.2.2 = true ∧
      IK.IV.mem (energyShard D q lr e.1 e.2.1 e.2.2.1)
        (∑ i ∈ Finset.Ico e.2.1 e.2.2.1, term e.1 i)

def EnergyTotalSoundnessFact (ν : V.SignedVMeasures)
    (D : IData) (plan : List (EKind × ℕ × ℕ × Int))
    (term : EKind → ℕ → ℝ) : Prop :=
  V.signedVQuadratic ν =
    (allKinds.map fun k =>
      ∑ i ∈ Finset.range (kindCount D k), term k i).sum

/-! This ledger is an input for the final producer, not a certificate itself.
Every analytic field is attached to `reference.measure`; the qlow equality is
attached to the integer decoder.  The `source` field is intentionally Type
level so that the decoded data cannot be hidden in a Prop structure.
-/

structure VReferenceEnergySoundnessLedger (q : ℕ)
    (hq : SignedVBaseRange q) where
  reference : VReferencePackage q hq
  source : V13DecodedRows q
  lr : IV
  lr_sound : IK.IV.mem lr (Real.log (3 / 5 : ℝ))
  plan : List (EKind × ℕ × ℕ × Int)
  term : EKind → ℕ → ℝ
  qlow_value : IK.val (V.EnergyCertI.qlowQ q) = (vQlow q : ℝ)
  field_x : CellSoundnessOn (pieceDomain q .x).1 (pieceDomain q .x).2
    (fieldUB source.data q lr .x)
    (fun t => V.signedVFullFieldX reference.measure (t : ℂ))
  field_vlo : CellSoundnessOn (pieceDomain q .vlo).1 (pieceDomain q .vlo).2
    (fieldUB source.data q lr .vlo)
    (fun t => V.signedVFullFieldV reference.measure (t : ℂ))
  field_vhi : CellSoundnessOn (pieceDomain q .vhi).1 (pieceDomain q .vhi).2
    (fieldUB source.data q lr .vhi)
    (fun t => V.signedVFullFieldV reference.measure (t : ℂ))
  field_zneg : CellSoundnessOn (pieceDomain q .zneg).1 (pieceDomain q .zneg).2
    (fieldUB source.data q lr .zneg)
    (fun t => V.signedVFullFieldZ reference.measure (t : ℂ))
  field_zpos : CellSoundnessOn (pieceDomain q .zpos).1 (pieceDomain q .zpos).2
    (fieldUB source.data q lr .zpos)
    (fun t => V.signedVFullFieldZ reference.measure (t : ℂ))
  energy : EnergyShardSoundnessFact source.data q lr plan term
  total : EnergyTotalSoundnessFact reference.measure source.data plan term

/-! Projection used by the G-3 proof.  This only repackages the named ledger
fields; it does not close the missing row, contour, or measure obligations. -/

theorem VReferenceEnergySoundnessLedger.energy_total_eq
    {q : ℕ} {hq : SignedVBaseRange q}
    (L : VReferenceEnergySoundnessLedger q hq) :
    V.signedVQuadratic L.reference.measure =
      (allKinds.map fun k =>
        ∑ i ∈ Finset.range (kindCount L.source.data k), L.term k i).sum :=
  L.total

end B3

end

end Li2Lean

