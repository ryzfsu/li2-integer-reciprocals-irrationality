/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Real row terms for the construction-backed v13 energy certificate.

The integer evaluator in `IEnergyEval` encloses these same expressions.  This
module is the semantic API consumed by the E2 enclosure layer: it is indexed
by the decoded `IData`, so it has no free term function or free measure.
-/

import Li2Lean.B3.V13ReferenceMeasure
import Li2Lean.V.EnergyCertI.IEnergyEval

namespace Li2Lean

noncomputable section

namespace B3

open V
open V.EnergyCertI
open V.EnergyCertI.IK

/-! ## Real counterparts of the integer evaluator kernels -/

/-- Twice-integrated logarithmic kernel, with its continuous value at zero. -/
def vEnergyG (s : ℝ) : ℝ :=
  if s = 0 then 0 else (s ^ 2 / 2) * Real.log |s| - 3 * s ^ 2 / 4

/-- Antiderivative used by the horizontal-chain and Poisson rows. -/
def vEnergyA (s y : ℝ) : ℝ :=
  if y = 0 then
    if s = 0 then 0 else s * Real.log |s| - s
  else
    (s / 2) * Real.log (s ^ 2 + y ^ 2) - s + y * Real.arctan (s / y)

def vEnergyPhiOut (c : PR) (u : QF) : ℝ :=
  vEnergyA (IK.val u - IK.val c.cx) (IK.val c.cy)

def vEnergyPhiIn (c : PR) (u : QF) : ℝ :=
  let x := IK.val c.cx
  let y := IK.val c.cy
  let r2 : ℝ := 9 / 25
  let d := x ^ 2 + y ^ 2
  if x = 0 ∧ y = 0 then
    IK.val u * Real.log (3 / 5 : ℝ)
  else
    IK.val u * ((1 / 2 : ℝ) * Real.log d - Real.log (3 / 5 : ℝ)) +
      vEnergyA (IK.val u - r2 * x / d) (r2 * y / d)

def vEnergyPhiV (c : PR) (u : QF) : ℝ :=
  if qle R u then vEnergyPhiOut c u
  else vEnergyPhiIn c u - vEnergyPhiIn c R + vEnergyPhiOut c R

def vEnergyPpModSq (ci cj : PR) : ℝ :=
  IK.val (modsq ci cj)

def vEnergyPpTerm (ci cj : PR) : ℝ :=
  (1 / 2 : ℝ) * Real.log (vEnergyPpModSq ci cj) - Real.log (3 / 5 : ℝ)

/-! ## Real row contributions -/

def vEnergySelfRow (pts : List CP) (k : ℕ) : ℝ :=
  match pts.drop k with
  | [] => 0
  | p :: rest =>
      (rest.map fun l =>
        -2 * IK.val p.J * IK.val l.J *
          vEnergyG (IK.val l.e - IK.val p.e)).sum

def vEnergyCrossRow (pts1 pts2 : List CP) (k : ℕ) : ℝ :=
  match pts1.drop k with
  | [] => 0
  | p :: _ =>
      (pts2.map fun l =>
        -IK.val p.J * IK.val l.J *
          vEnergyG (IK.val p.e - IK.val l.e)).sum

def vEnergyIntPoiRow (D : IData) (c : PR) : ℝ :=
  -((c.mult : ℝ) * IK.val c.w) *
    (2 * (D.zp.map fun p => IK.val p.J * vEnergyPhiOut c p.e).sum +
      (D.vp.map fun p => IK.val p.J * vEnergyPhiV c p.e).sum)

def vEnergyPpRow (full : List PR) (i : ℕ) : ℝ :=
  match full.drop i with
  | [] => 0
  | ci :: rest =>
      (IK.val ci.w) ^ 2 * vEnergyPpTerm ci ci +
        (rest.map fun cj =>
          2 * IK.val ci.w * IK.val cj.w * vEnergyPpTerm ci cj).sum

/-! The q argument occurs only in the actual cross-interaction row.  The raw
measure constructor is the same chain/Poisson construction used by
`v13RefMeasure`; normalization is a separate fact and is not smuggled into
this row API. -/

/-- The real contribution for one `EnergyCertI` kind and row. -/
def vEnergyTerm (q : ℕ) (D : IData) : EKind → ℕ → ℝ
  | .selfX, i => vEnergySelfRow D.xp i
  | .selfV, i => vEnergySelfRow D.vp i
  | .selfZ, i => vEnergySelfRow D.zp i
  | .crossVZ, i => vEnergyCrossRow D.vp D.zp i
  | .intPoi, i =>
      match D.pre.drop i with
      | [] => 0
      | c :: _ => vEnergyIntPoiRow D c
  | .pp, i => vEnergyPpRow D.full i
  | .dq, 0 =>
      -V.vCrossInteraction q (v13RefRawOfData q D).μx
        (v13RefRawOfData q D).μv
  | .dq, _ => 0

@[simp] theorem vEnergyTerm_dq_zero (q : ℕ) (D : IData) :
    vEnergyTerm q D .dq 0 =
      -V.vCrossInteraction q (v13RefRawOfData q D).μx
        (v13RefRawOfData q D).μv := rfl

@[simp] theorem vEnergyTerm_dq_succ (q i : ℕ) (D : IData) :
    vEnergyTerm q D .dq (i + 1) = 0 := by
  rfl

theorem vEnergyTerm_dq_sum (q : ℕ) (D : IData) :
    ∑ i ∈ Finset.range (kindCount D .dq), vEnergyTerm q D .dq i =
      -V.vCrossInteraction q (v13RefRawOfData q D).μx
        (v13RefRawOfData q D).μv := by
  simp [kindCount, vEnergyTerm]

end B3

end

end Li2Lean

#print axioms Li2Lean.B3.vEnergyTerm
