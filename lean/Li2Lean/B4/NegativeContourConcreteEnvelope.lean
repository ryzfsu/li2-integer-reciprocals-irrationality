/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B4.NegativeContourBottomClosedForm
import Li2Lean.B4.NegativeContourBottomLeft
import Li2Lean.B4.NegativeContourReflection
import Li2Lean.B4.NegativeContourRight

open Complex Real Set
open scoped BigOperators Interval

namespace Li2Lean.B4.NegContour

noncomputable section

/-!
Concrete four-side assembly for the fixed-height exceptional rectangles in
v13 `hp-tail.tex:307-371`.  The inputs below are the already isolated bottom,
lower-left, and right estimates for the actual Hermite polynomial `hpBpoly`.
No arbitrary coefficient sequence occurs in this file.
-/

/-- The side inputs are all tied to the v13 product `hpNegPhi`.  The only
additional input needed for the reflection step is that the bottom edge does
not meet a pole. -/
structure HpNegConcreteFourSideInputs (q : ℕ) where
  envelope : HpNegBottomLeftEnvelope q
  rightFactor : HpNegRightFactorCertificate q
  bottom_phi_ne : ∀ n : ℕ, envelope.n0 ≤ n → ∀ w ∈ hpNegBottomSide n,
    hpNegPhi n w ≠ 0

/-- The logarithm in every side bound contains the complete complex phase
`exp (lambda*w)`, with `lambda = -log q + pi*I` as in v13
`hp-tail.tex:258-266`.  This identity is useful when checking that a side
bound estimates the full exponent rather than only `log ||Phi||`. -/
theorem hp_neg_boundary_log_full_phase {q n : ℕ} {w : ℂ}
    (hphi : hpNegPhi n w ≠ 0) :
    hpNegBoundaryLog q n w =
      Real.log ‖hpNegPhi n w‖ +
        (-Real.log (q : ℝ) * w.re - Real.pi * w.im) := by
  unfold hpNegBoundaryLog
  rw [norm_mul]
  have hphi_norm : ‖hpNegPhi n w‖ ≠ 0 := norm_ne_zero_iff.mpr hphi
  have hexp : ‖Complex.exp (hpNegLambda q * w)‖ ≠ 0 := by
    rw [hpNegPhaseNorm]
    exact ne_of_gt (Real.exp_pos _)
  rw [Real.log_mul hphi_norm hexp, hpNegPhaseNorm, Real.log_exp]

/-- The q=9 tangent threshold is an exact rational certificate.  In
particular, the phase contribution is already included in the bound certified
by `hpNegT9`; no decimal approximation is used. -/
theorem hp_neg_q9_tangent_lt_log29 :
    (hpNegT 9 : ℝ) < Real.log 29 := by
  simpa [hpNegT] using hp_neg_t9_lt_log29_series

private theorem hp_neg_top_bound_of_bottom
    {q : ℕ} (data : HpNegConcreteFourSideInputs q)
    {n : ℕ} (hn : data.envelope.n0 ≤ n)
    {w : ℂ} (hw : w ∈ hpNegTopSide n) :
    hpNegBoundaryLog q n w ≤
      (n : ℝ) * (hpNegT q : ℝ) +
        (18 : ℝ) * (1 + Real.log ((n + 1 : ℕ) : ℝ)) := by
  have hwb : (starRingEnd ℂ) w ∈ hpNegBottomSide n :=
    hp_neg_top_mem_implies_bottom_mem hw
  have hphi : hpNegPhi n ((starRingEnd ℂ) w) ≠ 0 :=
    data.bottom_phi_ne n hn (starRingEnd ℂ w) hwb
  have hreflect := hp_neg_boundary_log_bottom_reflection
    (q := q) (n := n) hwb hphi
  have hreflect' :
      hpNegBoundaryLog q n w =
        hpNegBoundaryLog q n ((starRingEnd ℂ) w) -
          2 * Real.pi * ((n : ℝ) / 5) := by
    simpa using hreflect
  have hterm : 0 ≤ 2 * Real.pi * ((n : ℝ) / 5) := by
    positivity
  have hbottom := data.envelope.bottom n hn (starRingEnd ℂ w) hwb
  linarith

/-- Assemble the four concrete side estimates into the border certificate
consumed by the B4 contour route.  The lower bound `n0` is inherited from the
sum-to-integral envelope; the right-side estimate is transported from its
`30 ≤ n` interface.  The top edge uses the exact conjugate reflection and is
therefore no new analytic hypothesis. -/
def hpNegBoundaryCertificateOfConcrete
    {q : ℕ} (data : HpNegConcreteFourSideInputs q) :
    HpNegBoundaryCertificate q := by
  refine
    { q_spec := data.envelope.q_spec
      height := hp_neg_height_spec
      tangent_lt_log29 := hp_neg_t_lt_log29 data.envelope.q_spec
      n0 := data.envelope.n0
      n0_spec := data.envelope.n0_spec
      exponent := 18
      exponent_spec := by rfl
      bound := ?_ }
  intro n hn w hw
  rw [hpNegBorder_eq_union_sides] at hw
  rcases hw with hw | hright
  · rcases hw with hw | htop
    · rcases hw with hbottom | hleft
      · exact data.envelope.bottom n hn w hbottom
      · exact data.envelope.left n hn w hleft
    · exact hp_neg_top_bound_of_bottom data hn htop
  · have hn30 : 30 ≤ n := le_trans data.envelope.n0_spec hn
    exact data.rightFactor.logarithmic n hn30 w hright

theorem hpNegConcreteFourSideInputs.q_spec {q : ℕ}
    (data : HpNegConcreteFourSideInputs q) :
    q = 8 ∨ q = 9 ∨ q = 10 :=
  data.envelope.q_spec

end

end Li2Lean.B4.NegContour

#print axioms Li2Lean.B4.NegContour.hp_neg_boundary_log_full_phase
#print axioms Li2Lean.B4.NegContour.hp_neg_q9_tangent_lt_log29
#print axioms Li2Lean.B4.NegContour.hpNegBoundaryCertificateOfConcrete
