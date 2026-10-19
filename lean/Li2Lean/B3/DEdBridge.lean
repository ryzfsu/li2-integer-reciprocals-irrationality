/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Primitive bridge for the `.dq` evaluator shard.  The theorem exposes the
v13 analytic remainder as an explicit hypothesis; it does not manufacture a
measure-level identity from the integer evaluator.
-/

import Li2Lean.B3.EnergySoundnessInputs
import Li2Lean.B3.V13ReferenceEnergyTerm

namespace Li2Lean

noncomputable section

namespace B3

open V
open V.EnergyCertI

namespace DEncBridge

open IK

def momentValue (pts : List CP) (k : Nat) : ℝ :=
  (pts.map fun p =>
    val (qmul (qneg (qmul p.J (qpow p.e (k + 1)))) (1, k + 1))).sum

def dSeriesValue (q : Nat) (D : IData) : ℝ :=
  val (qmul D.mx D.mv) * Real.log (val (Int.ofNat q, 1)) +
    ((List.range 50).map (fun i =>
      val ((if i % 2 = 0 then 1 else -1), (i + 1) * q ^ (i + 1)) *
        (momentValue D.xp (i + 1) * momentValue D.vp (i + 1)))).sum

def tailDen (q : Nat) (D : IData) : Nat :=
  51 * q ^ 51 * (qmul D.mx D.mv).2

def tailNumerator (D : IData) : Nat :=
  (qmul D.mx D.mv).1.natAbs

def tailInterval (q : Nat) (D : IData) : IV :=
  (fl (-(Int.ofNat (tailNumerator D) * Int.ofNat S)) (tailDen q D),
    cl (Int.ofNat (tailNumerator D) * Int.ofNat S) (tailDen q D))

def remainderRadius (q : Nat) (D : IData) : ℝ :=
  |val (qmul D.mx D.mv)| / (51 * (q : ℝ) ^ 51)

private theorem qpow_den_pos {a : QF} (ha : 0 < a.2) (k : Nat) :
    0 < (qpow a k).2 := by
  simp [qpow, ha]

private theorem moment_term_mem {pts : List CP} {k : Nat}
    (hden : ∀ p ∈ pts, 0 < p.J.2 ∧ 0 < p.e.2) :
    ∀ p ∈ pts,
      IV.mem (ofQ (qmul (qneg (qmul p.J (qpow p.e (k + 1)))) (1, k + 1)))
        (val (qmul (qneg (qmul p.J (qpow p.e (k + 1)))) (1, k + 1))) := by
  intro p hp
  have hpJ : 0 < p.J.2 := (hden p hp).1
  have hpe : 0 < p.e.2 := (hden p hp).2
  have hpow : 0 < (qpow p.e (k + 1)).2 := qpow_den_pos hpe _
  have hq : 0 < (qmul p.J (qpow p.e (k + 1))).2 :=
    Nat.mul_pos hpJ hpow
  have hfinal : 0 <
      (qmul (qneg (qmul p.J (qpow p.e (k + 1)))) (1, k + 1)).2 := by
    exact Nat.mul_pos hq (by omega)
  exact ofQ_mem hfinal

theorem momentI_mem {pts : List CP} {k : Nat}
    (hden : ∀ p ∈ pts, 0 < p.J.2 ∧ 0 < p.e.2) :
    IV.mem (momentI pts k) (momentValue pts k) := by
  have h := sumI_map_mem
      (l := pts)
      (f := fun p => ofQ (qmul (qneg (qmul p.J (qpow p.e (k + 1)))) (1, k + 1)))
      (g := fun p => val (qmul (qneg (qmul p.J (qpow p.e (k + 1)))) (1, k + 1)))
      (fun p hp => moment_term_mem hden p hp)
  simpa [momentI, momentValue] using h

private theorem coeff_den_pos (q i : Nat) (hq : 0 < q) :
    0 < (i + 1) * q ^ (i + 1) := by
  exact Nat.mul_pos (by omega) (pow_pos hq _)

private theorem dSeries_term_mem {q : Nat} {D : IData} {i : Nat}
    (hq : 0 < q)
    (hx : ∀ p ∈ D.xp, 0 < p.J.2 ∧ 0 < p.e.2)
    (hv : ∀ p ∈ D.vp, 0 < p.J.2 ∧ 0 < p.e.2) :
    IV.mem
      (smulQ ((if i % 2 = 0 then 1 else -1), (i + 1) * q ^ (i + 1))
        (mulI (momentI D.xp (i + 1)) (momentI D.vp (i + 1))))
      (val ((if i % 2 = 0 then 1 else -1), (i + 1) * q ^ (i + 1)) *
        (momentValue D.xp (i + 1) * momentValue D.vp (i + 1))) := by
  apply smulQ_mem (coeff_den_pos q i hq)
  exact mulI_mem (momentI_mem hx) (momentI_mem hv)

private theorem dSeries_mem {q : Nat} {D : IData}
    (hq : 0 < q)
    (hmx : 0 < D.mx.2) (hmv : 0 < D.mv.2)
    (hx : ∀ p ∈ D.xp, 0 < p.J.2 ∧ 0 < p.e.2)
    (hv : ∀ p ∈ D.vp, 0 < p.J.2 ∧ 0 < p.e.2) :
    IV.mem
      (add (smulQ (qmul D.mx D.mv) (logQ energyMode.ntl (Int.ofNat q, 1)))
        (sumI ((List.range 50).map fun i =>
          smulQ ((if i % 2 = 0 then 1 else -1), (i + 1) * q ^ (i + 1))
            (mulI (momentI D.xp (i + 1)) (momentI D.vp (i + 1))))))
      (dSeriesValue q D) := by
  have hqQ : 0 < (Int.ofNat q) := Int.natCast_pos.mpr hq
  have hlog := logQ_mem energyMode.ntl (a := (Int.ofNat q, 1)) hqQ (by norm_num)
  have hmass := smulQ_mem (c := qmul D.mx D.mv)
      (Nat.mul_pos hmx hmv) hlog
  have hsum := sumI_map_mem (l := List.range 50)
      (f := fun i => smulQ ((if i % 2 = 0 then 1 else -1), (i + 1) * q ^ (i + 1))
        (mulI (momentI D.xp (i + 1)) (momentI D.vp (i + 1))))
      (g := fun i => val ((if i % 2 = 0 then 1 else -1), (i + 1) * q ^ (i + 1)) *
        (momentValue D.xp (i + 1) * momentValue D.vp (i + 1)))
      (fun i hi => dSeries_term_mem (q := q) (D := D) hq hx hv)
  simpa [dSeriesValue] using add_mem hmass hsum

/-! The integer evaluator has exactly the finite series followed by the
explicit interval for the analytic remainder.  Keeping the remainder as an
input is deliberate: the evaluator cannot identify a concrete measure with
its moment expansion by reduction. -/

theorem dEnc_mem_of_remainder {q : Nat} {D : IData} {Dq rho : ℝ}
    (hq : 0 < q)
    (hmx : 0 < D.mx.2) (hmv : 0 < D.mv.2)
    (hx : ∀ p ∈ D.xp, 0 < p.J.2 ∧ 0 < p.e.2)
    (hv : ∀ p ∈ D.vp, 0 < p.J.2 ∧ 0 < p.e.2)
    (hDq : Dq = dSeriesValue q D + rho)
    (htail : IV.mem (tailInterval q D) rho) :
    IV.mem (dEnc energyMode q D) Dq := by
  have hseries := dSeries_mem (q := q) (D := D) hq hmx hmv hx hv
  have hadd : IV.mem
      (add (add (smulQ (qmul D.mx D.mv)
          (logQ energyMode.ntl (Int.ofNat q, 1)))
        (sumI ((List.range 50).map fun i =>
          smulQ ((if i % 2 = 0 then 1 else -1), (i + 1) * q ^ (i + 1))
            (mulI (momentI D.xp (i + 1)) (momentI D.vp (i + 1))))))
        (tailInterval q D)) Dq := by
    apply mem_of_eq (add_mem hseries htail)
    exact hDq.symm
  simpa [dEnc, tailInterval, tailNumerator, tailDen] using hadd

theorem v13_dEnc_mem {q : Nat} {D : IData} {Dq rho : ℝ}
    (M : V.SignedVMeasures)
    (hq : 0 < q)
    (hmx : 0 < D.mx.2) (hmv : 0 < D.mv.2)
    (hx : ∀ p ∈ D.xp, 0 < p.J.2 ∧ 0 < p.e.2)
    (hv : ∀ p ∈ D.vp, 0 < p.J.2 ∧ 0 < p.e.2)
    (hactual : V.vCrossInteraction q M.μx M.μv = Dq)
    (hDq : Dq = dSeriesValue q D + rho)
    (htail : IV.mem (tailInterval q D) rho) :
    IV.mem (dEnc energyMode q D)
      (V.vCrossInteraction q M.μx M.μv) := by
  exact mem_of_eq (dEnc_mem_of_remainder hq hmx hmv hx hv hDq htail)
    hactual.symm

theorem v13_dq_shard_mem {q : Nat} {D : IData} {Dq rho : ℝ}
    (M : V.SignedVMeasures) (lr : IV)
    (hq : 0 < q)
    (hmx : 0 < D.mx.2) (hmv : 0 < D.mv.2)
    (hx : ∀ p ∈ D.xp, 0 < p.J.2 ∧ 0 < p.e.2)
    (hv : ∀ p ∈ D.vp, 0 < p.J.2 ∧ 0 < p.e.2)
    (hactual : V.vCrossInteraction q M.μx M.μv = Dq)
    (hDq : Dq = dSeriesValue q D + rho)
    (htail : IV.mem (tailInterval q D) rho) :
    IV.mem (energyShard D q lr EKind.dq 0 1)
      (-(V.vCrossInteraction q M.μx M.μv)) := by
  have h := v13_dEnc_mem (q := q) (D := D) M hq hmx hmv hx hv
    hactual hDq htail
  simpa [energyShard] using (neg_mem h)

/-! The measure-pinned form uses the same decoded rows that define the real
`vEnergyTerm`.  The normalization witness is explicit so the signed measure
cannot be replaced by an unrelated object; the raw measure in the `.dq` term
is definitionally the underlying `μx`/`μv` pair of `v13RefMeasure`. -/
theorem v13_dq_shard_mem_ref
    {q : Nat} {hq : SignedVBaseRange q}
    (R : V13DecodedRows q)
    (N : V13MeasureNormalization hq (v13RefRaw R))
    (lr : IV) {Dq rho : ℝ}
    (hqpos : 0 < q)
    (hmx : 0 < R.data.mx.2) (hmv : 0 < R.data.mv.2)
    (hx : ∀ p ∈ R.data.xp, 0 < p.J.2 ∧ 0 < p.e.2)
    (hv : ∀ p ∈ R.data.vp, 0 < p.J.2 ∧ 0 < p.e.2)
    (hactual :
      V.vCrossInteraction q (v13RefMeasure R N).μx
        (v13RefMeasure R N).μv = Dq)
    (hDq : Dq = dSeriesValue q R.data + rho)
    (htail : IV.mem (tailInterval q R.data) rho) :
    IV.mem (energyShard R.data q lr EKind.dq 0 1)
      (vEnergyTerm q R.data EKind.dq 0) := by
  have h := v13_dq_shard_mem (q := q) (D := R.data) (Dq := Dq)
    (rho := rho) (v13RefMeasure R N) lr hqpos hmx hmv hx hv hactual hDq htail
  simpa [vEnergyTerm, v13RefMeasure, V13RawMeasures.toSigned,
    v13RefRawOfData, v13RefRaw, energyShard] using h

/-- The evaluator's `.dq` shard is the negation of its `dEnc` interval.
This generic bridge is the E-d field consumed by the q-specific ledgers. -/
theorem dq_shard_mem_of_dEnc_mem {D : IData} {q : Nat} {lr : IV} {Dq : ℝ}
    (hDq : IK.IV.mem (dEnc energyMode q D) Dq) :
    IK.IV.mem (energyShard D q lr EKind.dq 0 1) (-Dq) := by
  simpa [energyShard] using IK.neg_mem hDq

end DEncBridge

end B3

end

end Li2Lean
