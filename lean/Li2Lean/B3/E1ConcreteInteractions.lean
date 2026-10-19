/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Concrete interaction bookkeeping for the signed-V reference measure.  The
theorem in this file is deliberately below the evaluator boundary: it proves
the exact finite decomposition of the analytic quadratic energy, while the
separate E-a..E-d work still has to identify each evaluator row with one of
these integrals.
-/

import Li2Lean.B3.V13ReferenceMeasure
import Li2Lean.B3.V13ReferenceEnergyTerm
import Li2Lean.P0.DualL6Variations

namespace Li2Lean

noncomputable section

namespace B3

open MeasureTheory Set
open V
open V.EnergyCertI
open V.EnergyCertI.IK

/-! The decoder includes a terminal jump in `jumpsI`.  This elementary
    telescoping lemma is the structural closed-jump fact needed before the
    piecewise-density integration-by-parts bridge can be applied. -/

theorem val_jumpsI_sum (prev : QF) (hs : List QF)
    (hprev : 0 < prev.2)
    (hspos : ∀ h ∈ hs, 0 < h.2) :
    ((V.EnergyCertI.jumpsI prev hs).map IK.val).sum = -IK.val prev := by
  induction hs generalizing prev with
  | nil =>
      simp [V.EnergyCertI.jumpsI, IK.val_qneg]
  | cons h hs ih =>
      have hh : 0 < h.2 := hspos h (by simp)
      have htail : ∀ x ∈ hs, 0 < x.2 := by
        intro x hx
        exact hspos x (by simp [hx])
      simp only [V.EnergyCertI.jumpsI, List.map_cons, List.sum_cons]
      rw [IK.val_qsub hh hprev, ih h hh htail]
      ring

theorem val_jumpsI_zero_sum (hs : List QF)
    (hspos : ∀ h ∈ hs, 0 < h.2) :
    ((V.EnergyCertI.jumpsI (0, 1) hs).map IK.val).sum = 0 := by
  simpa [IK.val, IK.qneg] using
    (val_jumpsI_sum (0, 1) hs (by norm_num) hspos)

/-! The two pieces of the z reference measure are named once, so the
    multiplicity of the mixed z interaction is visible in the theorem below. -/

def v13ZChain {q : ℕ} (R : V13DecodedRows q) : Measure ℂ :=
  v13DecodedChainMeasure R.data.zp

def v13ZPoisson {q : ℕ} (R : V13DecodedRows q) : Measure ℂ :=
  v13PoissonMeasure R.data.full

def v13InteractionKernel : ℂ × ℂ → ℝ :=
  fun p => li2LogKernel p.1 p.2

/-! Integrability is explicit because additivity of logarithmic interaction is
    only valid after the four expanded z products are known integrable. -/

structure V13InteractionIntegrability (M : V.SignedVMeasures)
    (zc zp : Measure ℂ) : Prop where
  sx : SFinite M.μx
  sv : SFinite M.μv
  szc : SFinite zc
  szp : SFinite zp
  xx : Integrable v13InteractionKernel (M.μx.prod M.μx)
  vv : Integrable v13InteractionKernel (M.μv.prod M.μv)
  zcc : Integrable v13InteractionKernel (zc.prod zc)
  zcp : Integrable v13InteractionKernel (zc.prod zp)
  zpp : Integrable v13InteractionKernel (zp.prod zp)
  vzc : Integrable v13InteractionKernel (M.μv.prod zc)
  vzp : Integrable v13InteractionKernel (M.μv.prod zp)

inductive V13InteractionKind where
  | selfX
  | selfV
  | zChainSelf
  | zChainPoisson
  | zPoissonSelf
  | vZChain
  | vZPoisson
  | crossXV
  deriving DecidableEq

/-! Each term is an actual integral of the same concrete measures.  The factor
    two is part of the mixed z term, rather than hidden in a free coefficient. -/

def v13InteractionTerm (M : V.SignedVMeasures)
    (zc zp : Measure ℂ) : V13InteractionKind → ℝ
  | .selfX => vLogInteraction M.μx M.μx
  | .selfV => vLogInteraction M.μv M.μv
  | .zChainSelf => vLogInteraction zc zc
  | .zChainPoisson => 2 * vLogInteraction zc zp
  | .zPoissonSelf => vLogInteraction zp zp
  | .vZChain => vLogInteraction M.μv zc
  | .vZPoisson => vLogInteraction M.μv zp
  | .crossXV => -vCrossInteraction M.q M.μx M.μv

def v13InteractionPlan : List V13InteractionKind :=
  [.selfX, .selfV, .zChainSelf, .zChainPoisson, .zPoissonSelf,
    .vZChain, .vZPoisson, .crossXV]

def v13InteractionPlanSum (M : V.SignedVMeasures)
    (zc zp : Measure ℂ) : ℝ :=
  (v13InteractionPlan.map (v13InteractionTerm M zc zp)).sum

theorem vLogInteraction_add_left
    {a b c : Measure ℂ} [SFinite a] [SFinite b] [SFinite c]
    (hac : Integrable v13InteractionKernel (a.prod c))
    (hbc : Integrable v13InteractionKernel (b.prod c)) :
    vLogInteraction (a + b) c = vLogInteraction a c + vLogInteraction b c := by
  unfold vLogInteraction
  rw [P0.L6Variations.li2LogInteraction_add_left hac hbc]
  ring

theorem vLogInteraction_add_right
    {a b c : Measure ℂ} [SFinite a] [SFinite b] [SFinite c]
    (hab : Integrable v13InteractionKernel (a.prod b))
    (hac : Integrable v13InteractionKernel (a.prod c)) :
    vLogInteraction a (b + c) = vLogInteraction a b + vLogInteraction a c := by
  unfold vLogInteraction
  rw [P0.L6Variations.li2LogInteraction_add_right hab hac]
  ring

/-! The exact analytic identity.  `hz` is the construction equation for the
    concrete q reference measure; no arbitrary term or conclusion-shaped plan
    occurs in the statement. -/

theorem signedVQuadratic_eq_v13InteractionPlanSum
    (M : V.SignedVMeasures) (zc zp : Measure ℂ)
    (hz : M.μz = zc + zp)
    (H : V13InteractionIntegrability M zc zp) :
    V.signedVQuadratic M = v13InteractionPlanSum M zc zp := by
  letI := H.sx
  letI := H.sv
  letI := H.szc
  letI := H.szp
  have hzcp : Integrable v13InteractionKernel (zp.prod zc) := by
    exact P0.L6Variations.integrable_kernel_swap H.zcp
  have hvzc : Integrable v13InteractionKernel ((M.μv).prod zc) := H.vzc
  have hvzp : Integrable v13InteractionKernel ((M.μv).prod zp) := H.vzp
  have hzcsum : Integrable v13InteractionKernel (zc.prod (zc + zp)) := by
    exact P0.L6Variations.integrable_kernel_add_right H.zcc H.zcp
  have hzpsum : Integrable v13InteractionKernel (zp.prod (zc + zp)) := by
    exact P0.L6Variations.integrable_kernel_add_right hzcp H.zpp
  have hzz :
      vLogInteraction M.μz M.μz =
        vLogInteraction zc zc + 2 * vLogInteraction zc zp +
          vLogInteraction zp zp := by
    rw [hz]
    rw [vLogInteraction_add_left hzcsum hzpsum]
    rw [vLogInteraction_add_right H.zcc H.zcp]
    rw [vLogInteraction_add_right hzcp H.zpp]
    rw [show vLogInteraction zp zc = vLogInteraction zc zp by
      unfold vLogInteraction
      rw [P0.L6Variations.li2LogInteraction_comm]]
    ring
  have hvz :
      vLogInteraction M.μv M.μz =
        vLogInteraction M.μv zc + vLogInteraction M.μv zp := by
    rw [hz, vLogInteraction_add_right hvzc hvzp]
  unfold V.signedVQuadratic v13InteractionPlanSum v13InteractionPlan
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    v13InteractionTerm]
  rw [hzz, hvz]
  ring

/-! The construction equation for `v13RefMeasure` exposes the same z split.
    It is a definitional fact, but naming it prevents later producers from
    accidentally substituting a different measure. -/

theorem v13RefMeasure_z_eq_chain_add_poisson
    {q : ℕ} {hq : SignedVBaseRange q}
    (R : V13DecodedRows q)
    (N : V13MeasureNormalization hq (v13RefRaw R)) :
    (v13RefMeasure R N).μz = v13ZChain R + v13ZPoisson R := by
  rfl

theorem signedVQuadratic_v13RefMeasure_eq_v13InteractionPlanSum
    {q : ℕ} {hq : SignedVBaseRange q}
    (R : V13DecodedRows q)
    (N : V13MeasureNormalization hq (v13RefRaw R))
    (H : V13InteractionIntegrability (v13RefMeasure R N)
      (v13ZChain R) (v13ZPoisson R)) :
    V.signedVQuadratic (v13RefMeasure R N) =
      v13InteractionPlanSum (v13RefMeasure R N)
        (v13ZChain R) (v13ZPoisson R) := by
  apply signedVQuadratic_eq_v13InteractionPlanSum
    (v13RefMeasure R N) (v13ZChain R) (v13ZPoisson R)
    (v13RefMeasure_z_eq_chain_add_poisson R N)
  exact H

/-! The cross row is the exact D_q term of the real evaluator.  This pins the
    evaluator row to the same raw measure used by v13RefMeasure; it is the E1
    cross block, not a free term field. -/

theorem v13RefMeasure_crossXV_eq_vEnergyTerm_dq_zero
    {q : ℕ} {hq : SignedVBaseRange q}
    (R : V13DecodedRows q)
    (N : V13MeasureNormalization hq (v13RefRaw R)) :
    v13InteractionTerm (v13RefMeasure R N)
        (v13ZChain R) (v13ZPoisson R) .crossXV =
      vEnergyTerm q R.data .dq 0 := by
  rfl

theorem signedVQuadratic_v13RefMeasure_cross_row
    {q : ℕ} {hq : SignedVBaseRange q}
    (R : V13DecodedRows q)
    (N : V13MeasureNormalization hq (v13RefRaw R)) :
    V.signedVQuadratic (v13RefMeasure R N) =
      (vLogInteraction (v13RefMeasure R N).μx (v13RefMeasure R N).μx +
        vLogInteraction (v13RefMeasure R N).μv (v13RefMeasure R N).μv +
        vLogInteraction (v13RefMeasure R N).μz (v13RefMeasure R N).μz +
        vLogInteraction (v13RefMeasure R N).μv (v13RefMeasure R N).μz) +
        vEnergyTerm q R.data .dq 0 := by
  rw [← v13RefMeasure_crossXV_eq_vEnergyTerm_dq_zero R N]
  simp only [V.signedVQuadratic, v13InteractionTerm]
  ring

end B3

end

end Li2Lean

#print axioms Li2Lean.B3.signedVQuadratic_eq_v13InteractionPlanSum
