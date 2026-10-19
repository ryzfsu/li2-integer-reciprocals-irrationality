/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

The literal signed-V reference package used by the v13 energy and smoothing
proofs.  This file is an interface only: row decoding, measure construction,
and the numerical certificates are supplied by the per-base producers.  The
package keeps those proofs attached to one and the same measure, so a field
bound cannot silently be proved for a different measure.
-/

import Li2Lean.B3.ProducerInterfaces

namespace Li2Lean

noncomputable section

namespace B3

open MeasureTheory Set

/-! ## Printed constants

These are the exact rational endpoints in v13 `v-analytic.tex:337-408,410-467`
and `v-reference-data.tex:1-430`.  They are data, rather than rounded reals.
-/

def vQlow : ℕ → ℚ
  | 2 => -4911272 / 10 ^ 6
  | 3 => -4863007 / 10 ^ 6
  | 4 => -4776198 / 10 ^ 6
  | 5 => -4684191 / 10 ^ 6
  | 6 => -4595191 / 10 ^ 6
  | 7 => -4511619 / 10 ^ 6
  | _ => 0

def vKx : ℕ → ℚ
  | 2 => -4621 / 1000
  | 3 => -5076 / 1000
  | 4 => -5408 / 1000
  | 5 => -5670 / 1000
  | 6 => -5886 / 1000
  | 7 => -6071 / 1000
  | _ => 0

def vKv : ℕ → ℚ
  | 2 => -4475 / 1000
  | 3 => -4632 / 1000
  | 4 => -4727 / 1000
  | 5 => -4791 / 1000
  | 6 => -4839 / 1000
  | 7 => -4876 / 1000
  | _ => 0

def vKz : ℕ → ℚ
  | 2 => -85 / 1000
  | 3 => 388 / 1000
  | 4 => 779 / 1000
  | 5 => 1108002 / 10 ^ 6
  | 6 => 1391 / 1000
  | 7 => 1639 / 1000
  | _ => 0

def vEx : ℕ → ℚ
  | 2 => -62821 / 10 ^ 4
  | 3 => -67656 / 10 ^ 4
  | 4 => -71126 / 10 ^ 4
  | 5 => -73835 / 10 ^ 4
  | 6 => -76061 / 10 ^ 4
  | 7 => -77947 / 10 ^ 4
  | _ => 0

def vEv : ℕ → ℚ
  | 2 => -44935 / 10 ^ 4
  | 3 => -46587 / 10 ^ 4
  | 4 => -47555 / 10 ^ 4
  | 5 => -48208 / 10 ^ 4
  | 6 => -48688 / 10 ^ 4
  | 7 => -49057 / 10 ^ 4
  | _ => 0

def vPathUpper : ℕ → ℚ
  | 2 => 3730292 / 10 ^ 6
  | 3 => 4796889 / 10 ^ 6
  | 4 => 5860319 / 10 ^ 6
  | 5 => 6917916 / 10 ^ 6
  | 6 => 7969979 / 10 ^ 6
  | 7 => 9017257 / 10 ^ 6
  | _ => 0

/-! The two lower support endpoints printed in the reference-data headers.
They are kept as rationals so support certificates can use integer arithmetic.
-/

def vXLow : ℕ → ℚ
  | 2 => (3349364905389 + 94611) / (5 * 10 ^ 13)
  | _ => 3349364905389 / (5 * 10 ^ 13)

def vVLow : ℕ → ℚ := fun _ => 480367989919 / (5 * 10 ^ 13)

/-! ## Integrability ledger

The fields are exactly the logarithmic pairings used by the signed quadratic
energy and the three hatted fields (`v-analytic.tex:18-48,220-301`).
-/

structure SignedVReferenceIntegrable (ν : V.SignedVMeasures) : Prop where
  xx : Integrable (fun p : ℂ × ℂ => li2LogKernel p.1 p.2) (ν.μx.prod ν.μx)
  vv : Integrable (fun p : ℂ × ℂ => li2LogKernel p.1 p.2) (ν.μv.prod ν.μv)
  zz : Integrable (fun p : ℂ × ℂ => li2LogKernel p.1 p.2) (ν.μz.prod ν.μz)
  vz : Integrable (fun p : ℂ × ℂ => li2LogKernel p.1 p.2) (ν.μv.prod ν.μz)
  xv : Integrable (fun p : ℂ × ℂ => V.vCrossKernel ν.q p.1 p.2) (ν.μx.prod ν.μv)

/-! ## Construction-bound package

`VReferencePackage` is a Type-level carrier because a `Prop` structure may not
contain a data field.  No default or arbitrary measure is supplied here.  A
per-base producer supplies the concrete measure and its facts together.
-/

structure VReferenceFacts (q : ℕ) (hq : SignedVBaseRange q)
    (ν : V.SignedVMeasures) (Ax Av Az : ℝ) : Prop where
  q_eq : ν.q = q
  x_support_low :
    ν.μx (Complex.ofReal '' Set.Icc (vXLow q) 1)ᶜ = 0
  v_support_low :
    ν.μv (Complex.ofReal '' Set.Icc (vVLow q) 1)ᶜ = 0
  z_support_source :
    ν.μz ((Complex.ofReal '' Set.Icc (-(q : ℝ)) (-3 / 5)) ∪
      Metric.sphere 0 (3 / 5))ᶜ = 0
  x_support : ν.μx (Complex.ofReal '' Set.Icc (0 : ℝ) 1)ᶜ = 0
  v_support : ν.μv (Complex.ofReal '' Set.Icc (0 : ℝ) 1)ᶜ = 0
  z_support : ν.μz (V.vContourTrace q)ᶜ = 0
  x_atomless : ∀ z : ℂ, ν.μx {z} = 0
  v_atomless : ∀ z : ℂ, ν.μv {z} = 0
  z_atomless : ∀ z : ℂ, ν.μz {z} = 0
  Ax_nonneg : 0 ≤ Ax
  Av_nonneg : 0 ≤ Av
  Az_nonneg : 0 ≤ Az
  x_ball : VBallBound ν.μx Ax
  v_ball : VBallBound ν.μv Av
  z_ball : VBallBound ν.μz Az
  sigma_eq : vSigma q = sigmaBudget Ax Av Az
  energy_lower : ((vQlow q : ℚ) : ℝ) < V.signedVQuadratic ν
  x_field : ∀ t : ℝ, t ∈ Set.Ioc (0 : ℝ) 1 →
    V.signedVFullFieldX ν (t : ℂ) < (vKx q : ℝ)
  v_field : ∀ t : ℝ, t ∈ Set.Ioc (0 : ℝ) 1 →
    V.signedVFullFieldV ν (t : ℂ) < (vKv q : ℝ)
  z_field : ∀ w ∈ V.vContourTrace q,
    V.signedVFullFieldZ ν w < (vKz q : ℝ)
  alpha_le : vAlpha q ≤ (vQlow q : ℝ) - 3 / 2 * Real.log q -
    (vKx q : ℝ) - 5 / 4 * (vKv q : ℝ) - (vKz q : ℝ)
  x_endpoint_disk : ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ ≤ 1 / 250 →
    V.signedVFullFieldX ν w ≤ (vEx q : ℝ)
  v_endpoint_disk : ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ ≤ 1 / 250 →
    V.signedVFullFieldV ν w ≤ (vEv q : ℝ)
  dual_admissible : SignedVReferenceIntegrable ν

structure VReferencePackage (q : ℕ) (hq : SignedVBaseRange q) where
  measure : V.SignedVMeasures
  Ax : ℝ
  Av : ℝ
  Az : ℝ
  facts : VReferenceFacts q hq measure Ax Av Az

def vReference {q : ℕ} {hq : SignedVBaseRange q}
    (P : VReferencePackage q hq) : V.SignedVMeasures := P.measure

def vAx {q : ℕ} {hq : SignedVBaseRange q}
    (P : VReferencePackage q hq) : ℝ := P.Ax

def vAv {q : ℕ} {hq : SignedVBaseRange q}
    (P : VReferencePackage q hq) : ℝ := P.Av

def vAz {q : ℕ} {hq : SignedVBaseRange q}
    (P : VReferencePackage q hq) : ℝ := P.Az

/-! The target certificate is only a projection of the package facts. -/

theorem VReferenceFacts.toEnergyCertificate
    {q : ℕ} {hq : SignedVBaseRange q}
    {ν : V.SignedVMeasures} {Ax Av Az : ℝ}
    (F : VReferenceFacts q hq ν Ax Av Az) :
    VEnergyCertificate q (vAlpha q) (vSigma q) := by
  refine ⟨ν, (vQlow q : ℝ), (vKx q : ℝ), (vKv q : ℝ), (vKz q : ℝ),
    Ax, Av, Az, ?_⟩
  refine ⟨F.q_eq, F.x_support, F.v_support, F.z_support,
    F.x_atomless, F.v_atomless, F.z_atomless,
    F.Ax_nonneg, F.Av_nonneg, F.Az_nonneg,
    F.x_ball, F.v_ball, F.z_ball, F.sigma_eq,
    le_of_lt F.energy_lower, F.x_field, F.v_field, F.z_field,
    F.alpha_le⟩

end B3

end

end Li2Lean

#print axioms Li2Lean.B3.VReferenceFacts.toEnergyCertificate
