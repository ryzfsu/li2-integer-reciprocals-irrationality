/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B4.RationalHeight

namespace Li2Lean.B4

/-- Every positive saddle height admits a positive rational approximation
from below with an arbitrarily small prescribed error. -/
theorem hp_saddle_rational_height_approx (q : ℝ) (hq : 1 < q)
    (ε : ℝ) (hε : 0 < ε)
    (hεβ : ε < hpSaddleBeta q hq) :
    ∃ b : ℚ, 0 < (b : ℝ) ∧
      (b : ℝ) < hpSaddleBeta q hq ∧
      hpSaddleBeta q hq - ε < (b : ℝ) := by
  have hleft : 0 < hpSaddleBeta q hq - ε := sub_pos.mpr hεβ
  obtain ⟨b, hleftb, hbβ⟩ :=
    exists_rat_btwn (sub_lt_self (hpSaddleBeta q hq) hε)
  exact ⟨b, lt_trans hleft hleftb, hbβ, hleftb⟩

/-- The selected rational approximation below the saddle height. -/
noncomputable def hpSaddleRationalHeightNear (q : ℝ) (hq : 1 < q)
    (ε : ℝ) (hε : 0 < ε)
    (hεβ : ε < hpSaddleBeta q hq) : ℚ :=
  Classical.choose (hp_saddle_rational_height_approx q hq ε hε hεβ)

/-- Specification of the epsilon-controlled rational height. -/
theorem hp_saddle_rational_height_near_spec (q : ℝ) (hq : 1 < q)
    (ε : ℝ) (hε : 0 < ε)
    (hεβ : ε < hpSaddleBeta q hq) :
    0 < (hpSaddleRationalHeightNear q hq ε hε hεβ : ℝ) ∧
      (hpSaddleRationalHeightNear q hq ε hε hεβ : ℝ) < hpSaddleBeta q hq ∧
      hpSaddleBeta q hq - ε <
        (hpSaddleRationalHeightNear q hq ε hε hεβ : ℝ) :=
  Classical.choose_spec (hp_saddle_rational_height_approx q hq ε hε hεβ)

end Li2Lean.B4
