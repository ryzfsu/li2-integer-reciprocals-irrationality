/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Generic endpoint-disk assembly for the v13 signed-V reference measure.
The finite evaluator checks are consumed here only through hiLe_spec.
The analytic logarithmic estimates remain explicit certificate fields.
-/

import Li2Lean.B3.ReferencePackageGeneric
import Li2Lean.V.EnergyCertI.IFieldEval
import Li2Lean.V.EnergyCertI.Consts
import Li2Lean.V.EnergyCertI.ISoundEval

namespace Li2Lean

noncomputable section

namespace B3

open MeasureTheory Set
open V
open V.EnergyCertI
open V.EnergyCertI.IK

/-! The endpoint evaluator denominators are positive for every accepted base.
The row source carries the same base range, but this lemma keeps the finite
arithmetic fact explicit at the point where hiLe_spec is used. -/

private theorem exQ_den_pos {q : ℕ} (hq : SignedVBaseRange q) :
    0 < (exQ q).2 := by
  rcases hq with ⟨hlo, hhi⟩
  interval_cases q <;> norm_num [exQ] at *

private theorem evQ_den_pos {q : ℕ} (hq : SignedVBaseRange q) :
    0 < (evQ q).2 := by
  rcases hq with ⟨hlo, hhi⟩
  interval_cases q <;> norm_num [evQ] at *

/-! The x endpoint certificate separates the analytic estimates from the
finite interval evaluator.  In particular, interval_mem is not a restated
endpoint conclusion: it is an integer interval enclosure for the displayed
combination of the supplied integral bounds. -/

structure V13XEndpointCertificate
    {q : ℕ} {hq : SignedVBaseRange q}
    (R : V13DecodedRows q)
    (N : V13MeasureNormalization hq (v13RefRaw R)) where
  J : ℝ
  x_log_bound :
    ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ ≤ 1 / 250 →
      (∫ z : ℂ, Real.log ‖w - z‖
        ∂(v13RefMeasure R N).μx) ≤ J
  cross_lower :
    ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ ≤ 1 / 250 →
      (5 / 4 : ℝ) * Real.log ((q : ℝ) - 1 / 250) ≤
        ∫ t : ℂ, V.vCrossKernel q w t ∂(v13RefMeasure R N).μv
  interval_mem :
    IV.mem (exUB fieldMode R.data q)
      (2 * J + (-5 / 4 : ℝ) * Real.log ((q : ℝ) - 1 / 250) +
        (3 / 4 : ℝ) * Real.log (1 / 250))

/-! The v endpoint certificate has the analogous two one-body estimates and
the cross estimate against the x measure (whose mass is one). -/

structure V13VEndpointCertificate
    {q : ℕ} {hq : SignedVBaseRange q}
    (R : V13DecodedRows q)
    (N : V13MeasureNormalization hq (v13RefRaw R)) where
  V : ℝ
  Z : ℝ
  v_log_bound :
    ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ ≤ 1 / 250 →
      (∫ z : ℂ, Real.log ‖w - z‖
        ∂(v13RefMeasure R N).μv) ≤ V
  z_log_bound :
    ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ ≤ 1 / 250 →
      (∫ z : ℂ, Real.log ‖w - z‖
        ∂(v13RefMeasure R N).μz) ≤ Z
  cross_lower :
    ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ ≤ 1 / 250 →
      Real.log ((q : ℝ) - 1 / 250) ≤
        ∫ t : ℂ, Li2Lean.V.vCrossKernel q t w ∂(v13RefMeasure R N).μx
  interval_mem :
    IV.mem (evUB fieldMode R.data q)
      (2 * V + Z - Real.log ((q : ℝ) - 1 / 250) +
        (1 / 4 : ℝ) * Real.log (1 / 250))

/-! The common x endpoint theorem.  hR remains an explicit row-bound input
to keep the theorem attached to the decoded-row ledger; the actual analytic
combination is supplied by C. -/

theorem v13_x_endpoint_disk
    {q : ℕ} {hq : SignedVBaseRange q}
    (R : V13DecodedRows q)
    (hR : V13DecodedRowBounds q R)
    (N : V13MeasureNormalization hq (v13RefRaw R))
    (C : V13XEndpointCertificate R N)
    (hcheck : hiLe (exUB fieldMode R.data q) (exQ q) = true)
    (hE : IK.val (exQ q) = (vEx q : ℝ))
    (w : ℂ) (hw0 : 0 < ‖w‖) (hw : ‖w‖ ≤ 1 / 250) :
    V.signedVFullFieldX (v13RefMeasure R N) w ≤ (vEx q : ℝ) := by
  have hlognorm : Real.log ‖w‖ ≤ Real.log (1 / 250 : ℝ) :=
    Real.log_le_log hw0 hw
  have hfieldBound :
      V.signedVFullFieldX (v13RefMeasure R N) w ≤
        2 * C.J + (-5 / 4 : ℝ) * Real.log ((q : ℝ) - 1 / 250) +
          (3 / 4 : ℝ) * Real.log (1 / 250) := by
    unfold V.signedVFullFieldX V.signedVFieldX
    rw [show (v13RefMeasure R N).q = q by rfl]
    have hx := C.x_log_bound w hw0 hw
    have hcross := C.cross_lower w hw0 hw
    linarith
  have hupperUB :
      (2 * C.J + (-5 / 4 : ℝ) * Real.log ((q : ℝ) - 1 / 250) +
        (3 / 4 : ℝ) * Real.log (1 / 250)) ≤ IK.val (exQ q) :=
    hiLe_spec (exQ_den_pos hq) C.interval_mem hcheck
  have hupper := le_trans hfieldBound hupperUB
  rw [← hE]
  exact hupper

/-! The common v endpoint theorem. -/

theorem v13_v_endpoint_disk
    {q : ℕ} {hq : SignedVBaseRange q}
    (R : V13DecodedRows q)
    (hR : V13DecodedRowBounds q R)
    (N : V13MeasureNormalization hq (v13RefRaw R))
    (C : V13VEndpointCertificate R N)
    (hcheck : hiLe (evUB fieldMode R.data q) (evQ q) = true)
    (hE : IK.val (evQ q) = (vEv q : ℝ))
    (w : ℂ) (hw0 : 0 < ‖w‖) (hw : ‖w‖ ≤ 1 / 250) :
    V.signedVFullFieldV (v13RefMeasure R N) w ≤ (vEv q : ℝ) := by
  have hlognorm : Real.log ‖w‖ ≤ Real.log (1 / 250 : ℝ) :=
    Real.log_le_log hw0 hw
  have hfieldBound :
      V.signedVFullFieldV (v13RefMeasure R N) w ≤
        2 * C.V + C.Z - Real.log ((q : ℝ) - 1 / 250) +
          (1 / 4 : ℝ) * Real.log (1 / 250) := by
    unfold V.signedVFullFieldV V.signedVFieldV
    rw [show (v13RefMeasure R N).q = q by rfl]
    have hv := C.v_log_bound w hw0 hw
    have hz := C.z_log_bound w hw0 hw
    have hcross := C.cross_lower w hw0 hw
    linarith
  have hupperUB :
      (2 * C.V + C.Z - Real.log ((q : ℝ) - 1 / 250) +
        (1 / 4 : ℝ) * Real.log (1 / 250)) ≤ IK.val (evQ q) :=
    hiLe_spec (evQ_den_pos hq) C.interval_mem hcheck
  have hupper := le_trans hfieldBound hupperUB
  rw [← hE]
  exact hupper

/-! Adapter used by the generic package constructor. -/

def V13NumericCertificates.with_endpoint_disks
    {q : ℕ} {hq : SignedVBaseRange q}
    {R : V13DecodedRows q}
    (C : V13NumericCertificates q hq R)
    (hx : ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ ≤ 1 / 250 →
      V.signedVFullFieldX (v13RefMeasure R C.normalization) w ≤ (vEx q : ℝ))
    (hv : ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ ≤ 1 / 250 →
      V.signedVFullFieldV (v13RefMeasure R C.normalization) w ≤ (vEv q : ℝ)) :
    V13NumericCertificates q hq R :=
  { C with
    x_endpoint_disk := hx
    v_endpoint_disk := hv }

end B3

end

end Li2Lean

#print axioms Li2Lean.B3.v13_x_endpoint_disk
#print axioms Li2Lean.B3.v13_v_endpoint_disk
