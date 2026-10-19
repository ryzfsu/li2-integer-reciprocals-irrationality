/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

The near-field layer-cake calculation for the signed-V smoothing transfer.
-/

import Li2Lean.B3.S0ActualInterface

namespace Li2Lean

noncomputable section

namespace B3

open MeasureTheory Set

/-!
The near-field part of the logarithmic-potential modulus is the literal
layer-cake calculation in v13 `v-analytic.tex:496-520`.  Here `A` is the
disk-density constant and `d` is the centre separation.  The hypotheses are
exactly the positivity of the density and the cutoff condition `2*d <= 1`.
-/
theorem s0_near_field_layer_cake
    {A d : ℝ}
    (hA : 0 ≤ A)
    (hd : 0 < d)
    (h2d : 2 * d ≤ 1) :
    ∫ s in Set.Ioi (0 : ℝ),
      min (2 * A * d) (A * Real.exp (-s)) =
        2 * A * d * (1 + Real.log (1 / (2 * d))) := by
  let t : ℝ := Real.log (1 / (2 * d))
  let C : ℝ := 2 * A * d
  let f : ℝ → ℝ := fun s => min C (A * Real.exp (-s))
  have hden : 0 < 2 * d := by positivity
  have hfrac : (1 : ℝ) ≤ 1 / (2 * d) := by
    apply (le_div_iff₀ hden).2
    simpa using h2d
  have ht : 0 ≤ t := by
    dsimp [t]
    exact Real.log_nonneg hfrac
  have hexp : Real.exp (-t) = 2 * d := by
    dsimp [t]
    rw [Real.exp_neg, Real.exp_log (by positivity : 0 < (1 / (2 * d) : ℝ))]
    field_simp
  have hleft : ∀ s ∈ Set.Ioc (0 : ℝ) t, f s = C := by
    intro s hs
    have hst : s ≤ t := hs.2
    have hexp_le : 2 * d ≤ Real.exp (-s) := by
      rw [← hexp]
      exact Real.exp_le_exp.mpr (by linarith)
    dsimp [f, C]
    rw [min_eq_left]
    nlinarith [mul_le_mul_of_nonneg_left hexp_le hA]
  have hright : ∀ s ∈ Set.Ioi t, f s = A * Real.exp (-s) := by
    intro s hs
    have hst : t < s := hs
    have hexp_le : Real.exp (-s) ≤ 2 * d := by
      rw [← hexp]
      exact Real.exp_le_exp.mpr (by linarith)
    dsimp [f, C]
    rw [min_eq_right]
    nlinarith [mul_le_mul_of_nonneg_left hexp_le hA]
  have hleft_const : IntegrableOn (fun _ : ℝ => C) (Set.Ioc (0 : ℝ) t) := by
    exact integrableOn_const (measure_Ioc_lt_top.ne)
  have hleft_int : IntegrableOn f (Set.Ioc (0 : ℝ) t) := by
    exact hleft_const.congr_fun (fun s hs => (hleft s hs).symm) measurableSet_Ioc
  have htail_exp : IntegrableOn (fun s : ℝ => A * Real.exp (-s)) (Set.Ioi t) := by
    simpa only [IntegrableOn] using
      (Integrable.const_mul (integrableOn_exp_neg_Ioi t) A)
  have htail_int : IntegrableOn f (Set.Ioi t) := by
    exact htail_exp.congr_fun (fun s hs => (hright s hs).symm) measurableSet_Ioi
  have hsplit := setIntegral_union (f := f) (s := Set.Ioc (0 : ℝ) t)
    (t := Set.Ioi t)
    (Ioc_disjoint_Ioi (a := (0 : ℝ)) (b := t) (c := t) le_rfl)
    measurableSet_Ioi hleft_int htail_int
  rw [Ioc_union_Ioi_eq_Ioi ht] at hsplit
  have hleft_eval :
      (∫ s in Set.Ioc (0 : ℝ) t, f s) = C * t := by
    rw [setIntegral_congr_fun measurableSet_Ioc hleft]
    simp [MeasureTheory.integral_const, smul_eq_mul, max_eq_left ht]
    ring
  have htail_eval :
      (∫ s in Set.Ioi t, f s) = A * Real.exp (-t) := by
    rw [setIntegral_congr_fun measurableSet_Ioi hright]
    rw [integral_const_mul]
    rw [integral_exp_neg_Ioi]
  rw [hleft_eval, htail_eval, hexp] at hsplit
  dsimp [f, C] at hsplit ⊢
  linarith

end B3

end
end Li2Lean
