/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/

import Li2Lean.V.AllMSmoothing

/-!
Typed producer/consumer surface for the multiplicative S0 estimate.

The bound is the multiplicative form used by v13 `v-analytic.tex:86-87,
106-123,522-530`; the logarithmic bridge is available only with the explicit
nonvanishing field, since Lean defines `Real.log 0 = 0`.

This file reuses `Li2Lean.V.AllMSmoothing` from the Li2(1/2) interface.  The
q = 2 theorem below is a regression specialization and introduces no second
construction.
-/

namespace Li2Lean.B3

noncomputable section

/-- The S0 magnitude field, restated as a producer-facing proposition. -/
def S0MagnitudeGoal (q m L : ℕ) (G : ℂ) (Tq phiMax : ℝ) : Prop :=
  s0MultiplicativeBound q m L G Tq phiMax

theorem s0MagnitudeGoal_iff_bound {q m L : ℕ} {G : ℂ} {Tq phiMax : ℝ} :
    S0MagnitudeGoal q m L G Tq phiMax ↔
      ‖G‖ ≤ s0MagnitudeRhs q m L Tq phiMax := by
  rfl

/-- Convert a certified multiplicative estimate to a log estimate.

The positivity premise for the right-hand side is kept explicit: future S0
producers must prove it from their `Tq` and `phiMax` data rather than relying
on the `Real.log 0` convention.
-/
theorem s0_log_bridge {q m L : ℕ} {G : ℂ} {Tq phiMax : ℝ}
    (hG : G ≠ 0) (hRhs : 0 < s0MagnitudeRhs q m L Tq phiMax)
    (hmag : S0MagnitudeGoal q m L G Tq phiMax) :
    Real.log ‖G‖ ≤ Real.log (s0MagnitudeRhs q m L Tq phiMax) := by
  exact Real.log_le_log (norm_pos_iff.mpr hG) hmag

/-- Certificate form of the same bridge, consuming the shared S0 fields. -/
theorem s0_log_bridge_of_certificate {q m L : ℕ}
    (c : S0MultiplicativeCertificate q m L)
    (hRhs : 0 < s0MagnitudeRhs q m L c.Tq c.phiMax) :
    Real.log ‖c.G‖ ≤ Real.log (s0MagnitudeRhs q m L c.Tq c.phiMax) := by
  exact s0_log_bridge c.G_ne_zero hRhs c.magnitude_bound

/-! Base-2 regression: this is the same theorem at the frozen 1/2 base. -/
theorem s0_log_bridge_q2 {m L : ℕ} {G : ℂ} {Tq phiMax : ℝ}
    (hG : G ≠ 0) (hRhs : 0 < s0MagnitudeRhs 2 m L Tq phiMax)
    (hmag : S0MagnitudeGoal 2 m L G Tq phiMax) :
    Real.log ‖G‖ ≤ Real.log (s0MagnitudeRhs 2 m L Tq phiMax) := by
  exact s0_log_bridge hG hRhs hmag

end

end Li2Lean.B3

#print axioms Li2Lean.B3.s0_log_bridge
#print axioms Li2Lean.B3.s0_log_bridge_q2
