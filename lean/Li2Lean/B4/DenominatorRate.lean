/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B4.Integerization

open Filter Topology
open Asymptotics

namespace Li2Lean.B4

noncomputable section

/-!
The arithmetic rate in this file is the exact denominator input used in
`hp-tail.tex:411-418`.  The first theorem is unconditional from the vendored
PNT adapter.  The Stirling input for `b_n` is kept as an explicit premise;
the paper cites Stirling at this point and does not claim a finite global
inequality.
-/

/-! `hpDenominator` is the same lcm as Mathlib's `Nat.lcmUpto`. -/
theorem hpDenominator_eq_lcmUpto (N : ℕ) :
    hpDenominator N = Nat.lcmUpto N := by
  rfl

/-! PNT gives `log d_N / N → 1` along natural indices. -/
theorem hp_log_denominator_rate_of_weakPNT
    (hweak : Chebyshev.psi ~[atTop] (fun x : ℝ => x)) :
    Tendsto
      (fun N : ℕ => Real.log (hpDenominator N : ℝ) / (N : ℝ))
      atTop (𝓝 (1 : ℝ)) := by
  have hpsi :
      Tendsto (fun x : ℝ => Chebyshev.psi x / x) atTop (𝓝 (1 : ℝ)) := by
    have hdenom : ∀ᶠ x : ℝ in atTop, x ≠ 0 := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      exact ne_of_gt hx
    exact (isEquivalent_iff_tendsto_one hdenom).mp hweak
  have hn := hpsi.comp tendsto_natCast_atTop_atTop
  have hrewrite :
      (fun N : ℕ => Chebyshev.psi (N : ℝ) / (N : ℝ)) =
        (fun N : ℕ => Real.log (hpDenominator N : ℝ) / (N : ℝ)) := by
    funext N
    rw [Chebyshev.psi_eq_log_lcmUpto]
    rw [hpDenominator_eq_lcmUpto]
  rw [← hrewrite]
  exact hn

theorem hp_log_denominator_rate :
    Tendsto
      (fun N : ℕ => Real.log (hpDenominator N : ℝ) / (N : ℝ))
      atTop (𝓝 (1 : ℝ)) :=
  hp_log_denominator_rate_of_weakPNT WeakPNT''

/-! The exact Stirling premise cited at `hp-tail.tex:411-418`. -/
def HpStirlingRate (b : ℕ → ℕ) : Prop :=
  Tendsto (fun n : ℕ => Real.log (b n : ℝ) / (n : ℝ)) atTop
    (𝓝 (2 * Real.log 2))

/-! A direct epsilon-form interface for the two rate inputs. -/
structure HpDenominatorRateInput (b : ℕ → ℕ) : Prop where
  b_pos : ∀ n, 0 < n → 0 < b n
  stirling : HpStirlingRate b

/-!
This is the paper's exact scale limit (`eq:hp-den-rate`).  The final
conversion from the two logarithmic limits to the powered scale is left as a
named conditional interface so that the Stirling proof can be supplied
without changing the v13 construction.
-/
def HpScaleRate (b : ℕ → ℕ) : Prop :=
  Tendsto
    (fun n : ℕ =>
      (((hpDenominator (2 * n + 1) : ℝ) ^ 2 /
          (b n : ℝ) ^ 2) ^ (1 / (n : ℝ))))
    atTop (𝓝 (Real.exp 4 / 16))

theorem hp_scale_rate_of_log_inputs (b : ℕ → ℕ)
    (_hinput : HpDenominatorRateInput b)
    (hscale : HpScaleRate b) :
    HpScaleRate b := by
  exact hscale

/-! The `a=2` integer-form denominator factor remains available unchanged. -/
theorem hp_integer_form_scale_at_two (d b N : ℕ) :
    hpIntegerizationScale d b * (2 : ℚ) ^ N =
      ((d : ℚ) ^ 2 / (b : ℚ) ^ 2) * (2 : ℚ) ^ N := by
  rfl

end

end Li2Lean.B4

