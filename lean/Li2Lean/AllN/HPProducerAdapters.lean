/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.AllN.ProducerAssembly
import Li2Lean.B4.HPIntegralForm
import Li2Lean.B4.DenominatorRate
import Li2Lean.B4.HPNoAdjacentActual

open Filter Topology

namespace Li2Lean.AllNAssembly

noncomputable section

open Li2Lean.B4
open Li2Lean.B4.TailAnalytic

/-!
Adapters for the actual v13 HP sequence. The scale identity is
`hp-tail.tex:177-194`; decay is `:411-474`; the three-form determinant
argument is `:477-566`.
-/

/-- Normalize the B4 `hpLR` scale to the sequence consumed by AllN.
This is the same v13 `d_(2n+1)^2 / b_n^2` scale. -/
theorem hpLR_eq_hpIntegerFormL (a : ℤ) (n : ℕ) :
    TailAnalytic.hpLR a n = AllNAssembly.hpIntegerFormL a n := by
  simp only [TailAnalytic.hpLR, TailAnalytic.hpDR,
    AllNAssembly.hpIntegerFormL]
  rw [← hpDenominator_eq_lcmUpto,
    show AllNAssembly.hpB n = TailAnalytic.hpbN n by rfl]
  simp only [hpIntegerizationScale]
  push_cast
  ring

/-- Convert the actual B4 integer-affine form to the AllN predicate.
This is the integerization output of `hp-tail.tex:176-194`. -/
theorem producer_hpIntegral_of_integral_form {a : ℤ}
    (hI : TailAnalytic.HPIntegralForm a) :
    AllNAssembly.HPIntegralForm a := by
  rcases hI with ⟨X, Y, hform⟩
  refine ⟨X, Y, fun n => ?_⟩
  rw [← hpLR_eq_hpIntegerFormL a n]
  exact hform n

/-- Convert actual `hpLR` decay to the AllN negative-tail predicate.
This is the fixed-base limit glue after the v13 rate estimate. -/
theorem producer_hpDecayNeg {a : ℤ} (_ha : a ≤ (-8 : ℤ))
    (hdecay : Tendsto (TailAnalytic.hpLR a) atTop (𝓝 0)) :
    AllNAssembly.HPDecay a := by
  change Tendsto (AllNAssembly.hpIntegerFormL a) atTop (𝓝 0)
  have hEq : TailAnalytic.hpLR a = AllNAssembly.hpIntegerFormL a :=
    funext (hpLR_eq_hpIntegerFormL a)
  rw [← hEq]
  exact hdecay

/-- Convert actual `hpLR` decay to the AllN positive-tail predicate. -/
theorem producer_hpDecayPos {a : ℤ} (_ha : (12 : ℤ) ≤ a)
    (hdecay : Tendsto (TailAnalytic.hpLR a) atTop (𝓝 0)) :
    AllNAssembly.HPDecay a := by
  change Tendsto (AllNAssembly.hpIntegerFormL a) atTop (𝓝 0)
  have hEq : TailAnalytic.hpLR a = AllNAssembly.hpIntegerFormL a :=
    funext (hpLR_eq_hpIntegerFormL a)
  rw [← hEq]
  exact hdecay

/-- Convert actual `hpLR` adjacent-nonzero to the AllN predicate.
This is `hp-tail.tex:477-566`. -/
theorem producer_hpNoAdj {a : ℤ}
    (_ha : (12 : ℤ) ≤ a ∨ a ≤ -8)
    (hno : ∀ n, ¬ (TailAnalytic.hpLR a n = 0 ∧
      TailAnalytic.hpLR a (n + 1) = 0)) :
    AllNAssembly.HPNoAdjacentZero a := by
  change ∀ n, ¬ (AllNAssembly.hpIntegerFormL a n = 0 ∧
    AllNAssembly.hpIntegerFormL a (n + 1) = 0)
  intro n hzero
  apply hno n
  constructor
  · rw [hpLR_eq_hpIntegerFormL a n]
    exact hzero.1
  · rw [hpLR_eq_hpIntegerFormL a (n + 1)]
    exact hzero.2

/-- The determinant consumer supplies the adjacent-nonzero field once its
three concrete v13 producer identities are proved. -/
theorem producer_hpNoAdj_of_v13_input {a : ℤ}
    (ha : (12 : ℤ) ≤ a ∨ a ≤ -8)
    (I : HPNoAdjacentV13Input a) :
    AllNAssembly.HPNoAdjacentZero a := by
  apply producer_hpNoAdj ha
  exact hpLR_no_adjacent_zero_of_v13_input ha I

/-- Construction-bound inputs for the AllN HP fields. The `integral`,
`decay_*`, and `no_adj` fields all mention the fixed `hpLR` sequence. -/
structure HPProducerInput : Prop where
  integral : ∀ a : ℤ, ((12 : ℤ) ≤ a ∨ a ≤ -8) →
    TailAnalytic.HPIntegralForm a
  decay_pos : ∀ a : ℤ, (12 : ℤ) ≤ a →
    Tendsto (TailAnalytic.hpLR a) atTop (𝓝 0)
  decay_neg : ∀ a : ℤ, a ≤ (-8 : ℤ) →
    Tendsto (TailAnalytic.hpLR a) atTop (𝓝 0)
  no_adj_v13 : ∀ a : ℤ, ((12 : ℤ) ≤ a ∨ a ≤ -8) →
    HPNoAdjacentV13Input a

/-- Field-shaped `hpIntegral` producer for `AllNProducers`. -/
theorem producer_hpIntegral_of_input (I : HPProducerInput) :
    ∀ a : ℤ, ((12 : ℤ) ≤ a ∨ a ≤ -8) → AllNAssembly.HPIntegralForm a := by
  intro a ha
  exact producer_hpIntegral_of_integral_form (I.integral a ha)

/-- Field-shaped `hpDecayNeg` producer for `AllNProducers`. -/
theorem producer_hpDecayNeg_of_input (I : HPProducerInput) :
    ∀ a : ℤ, a ≤ (-8 : ℤ) → AllNAssembly.HPDecay a := by
  intro a ha
  exact producer_hpDecayNeg ha (I.decay_neg a ha)

/-- Field-shaped `hpDecayPos` producer for `AllNProducers`. -/
theorem producer_hpDecayPos_of_input (I : HPProducerInput) :
    ∀ a : ℤ, (12 : ℤ) ≤ a → AllNAssembly.HPDecay a := by
  intro a ha
  exact producer_hpDecayPos ha (I.decay_pos a ha)

/-- Field-shaped `hpNoAdj` producer for `AllNProducers`. -/
theorem producer_hpNoAdj_of_input (I : HPProducerInput) :
    ∀ a : ℤ, ((12 : ℤ) ≤ a ∨ a ≤ -8) →
      AllNAssembly.HPNoAdjacentZero a := by
  intro a ha
  exact producer_hpNoAdj_of_v13_input ha (I.no_adj_v13 a ha)

end

end Li2Lean.AllNAssembly

#print axioms Li2Lean.AllNAssembly.hpLR_eq_hpIntegerFormL
#print axioms Li2Lean.AllNAssembly.producer_hpIntegral_of_input
#print axioms Li2Lean.AllNAssembly.producer_hpDecayNeg_of_input
#print axioms Li2Lean.AllNAssembly.producer_hpDecayPos_of_input
#print axioms Li2Lean.AllNAssembly.producer_hpNoAdj_of_input
#print axioms Li2Lean.AllNAssembly.producer_hpNoAdj_of_v13_input
