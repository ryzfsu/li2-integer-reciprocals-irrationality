/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/

import Mathlib
import Li2Lean.B3.SignedSmoothing

/-!
# Signed V denominator transfer on finite product measures

This file lifts the pointwise tube estimate in
`source/chapters/v-analytic.tex:546-558` to the product-measure terms that
occur in the signed energy and dual fields.  The two generic integration
lemmas are ordinary finite-measure inequalities; they do not discharge the
v13 integrability or measure-construction obligations.  Those obligations
remain explicit in the hypotheses of the final bridge.

The mass normalization in the last theorem is the v13 pair `(1,5/4)` from
`source/chapters/v-analytic.tex:10-12`.  The proof follows the finite-product
integral pattern audited in the reusable 1/2 `Kit/IntegralSupFinite.lean`
module, while the denominator cost itself comes from
`SignedSmoothing.lean`.
-/

namespace Li2Lean

noncomputable section

namespace B3

open MeasureTheory Set Filter
open scoped ENNReal

/-! ## Finite-measure integral transfer -/

/--
If two integrable real functions differ by at most `C` almost everywhere,
their integrals differ by at most `C` times the measure mass.  This is the
finite-measure form needed after the pointwise v13 denominator estimate.
-/
theorem abs_integral_sub_le_of_ae_abs_sub_le
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {f g : α → ℝ} {C : ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hfg : ∀ᵐ x ∂μ, |f x - g x| ≤ C) (_hC : 0 ≤ C) :
    |(∫ x, f x ∂μ) - ∫ x, g x ∂μ| ≤ C * μ.real Set.univ := by
  rw [← integral_sub hf hg]
  calc
    |∫ x, f x - g x ∂μ| ≤ ∫ x, |f x - g x| ∂μ :=
      abs_integral_le_integral_abs
    _ ≤ ∫ _x : α, C ∂μ := by
      apply integral_mono_ae (hf.sub hg).abs (integrable_const C)
      exact hfg
    _ = C * μ.real Set.univ := by
      rw [integral_const]
      simp [smul_eq_mul, mul_comm]

/-- The mass of a finite product measure is the product of its marginal
masses.  This is the product-measure normalization used by the signed V
energy; no density or support assumption is hidden here. -/
theorem prod_real_univ
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    (μ.prod ν).real Set.univ = μ.real Set.univ * ν.real Set.univ := by
  rw [Measure.real_def, ← Set.univ_prod_univ, Measure.prod_prod]
  simp [Measure.real_def, ENNReal.toReal_mul]

/-- Product-measure version of the preceding transfer. -/
theorem pair_integral_transfer
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {f g : α × β → ℝ} {C : ℝ}
    (hf : Integrable f (μ.prod ν)) (hg : Integrable g (μ.prod ν))
    (hfg : ∀ᵐ p ∂(μ.prod ν), |f p - g p| ≤ C) (hC : 0 ≤ C) :
    |(∫ p, f p ∂(μ.prod ν)) - ∫ p, g p ∂(μ.prod ν)| ≤
      C * μ.real Set.univ * ν.real Set.univ := by
  calc
    |(∫ p, f p ∂(μ.prod ν)) - ∫ p, g p ∂(μ.prod ν)| ≤
        C * (μ.prod ν).real Set.univ :=
      abs_integral_sub_le_of_ae_abs_sub_le (μ.prod ν) hf hg hfg hC
    _ = C * μ.real Set.univ * ν.real Set.univ := by
      rw [prod_real_univ]
      ring

/-! ## The v13 `(1,5/4)` weighted bridge -/

/--
The pointwise cross-denominator cost from `v-analytic.tex:555-558` lifts to
the normalized signed pair `(μ,ν)` with masses `(1,5/4)`.  The fields `hf`
and `hg` deliberately expose the mixed-support integrability obligation;
the theorem supplies only the arithmetic and measure-theoretic lifting.
-/
theorem weighted_pair_integral_transfer
    {q m : ℕ} (hq : 2 ≤ q) (hm : 64 ≤ m)
    (μ ν : Measure ℂ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {f g : ℂ × ℂ → ℝ}
    (hf : Integrable f (μ.prod ν)) (hg : Integrable g (μ.prod ν))
    (hpoint : ∀ᵐ p ∂(μ.prod ν),
      (5 / 4 : ℝ) * |f p - g p| ≤ denominatorTransferCost q * smoothingEpsilon m)
    (hμmass : μ.real Set.univ = 1)
    (hνmass : ν.real Set.univ = 5 / 4) :
    |(∫ p, f p ∂(μ.prod ν)) - ∫ p, g p ∂(μ.prod ν)| ≤
      denominatorTransferCost q * smoothingEpsilon m := by
  have hcost : 0 ≤ denominatorTransferCost q := by
    unfold denominatorTransferCost
    exact mul_nonneg (by norm_num) (denominatorLipschitz_pos hq).le
  have heps : 0 ≤ smoothingEpsilon m :=
    (smoothingEpsilon_pos (by omega : 0 < m)).le
  let D : ℝ := denominatorTransferCost q * smoothingEpsilon m
  have hD : 0 ≤ D := by
    dsimp [D]
    exact mul_nonneg hcost heps
  have hpoint' : ∀ᵐ p ∂(μ.prod ν),
      |f p - g p| ≤ (4 / 5 : ℝ) * D := by
    filter_upwards [hpoint] with p hp
    have habs : 0 ≤ |f p - g p| := abs_nonneg _
    dsimp [D]
    nlinarith
  have hpair := pair_integral_transfer μ ν hf hg hpoint'
    (by positivity : 0 ≤ (4 / 5 : ℝ) * D)
  calc
    |(∫ p, f p ∂(μ.prod ν)) - ∫ p, g p ∂(μ.prod ν)| ≤
        (4 / 5 : ℝ) * D * μ.real Set.univ * ν.real Set.univ := hpair
    _ = D := by rw [hμmass, hνmass]; ring
    _ = denominatorTransferCost q * smoothingEpsilon m := rfl

/-! ## Both orientations of the signed cross term -/

/--
Mass-product form of the preceding bridge.  The signed energy contains the
`x-v` cross term, while the dual fields use the reversed ordering in one of
their mixed integrals (`source/chapters/v-analytic.tex:18-25,34-43`).  This
form exposes the common product mass so both orientations use the same
pointwise v13 estimate.
-/
theorem weighted_pair_integral_transfer_of_mass
    {q m : ℕ} (hq : 2 ≤ q) (hm : 64 ≤ m)
    (μ ν : Measure ℂ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {f g : ℂ × ℂ → ℝ}
    (hf : Integrable f (μ.prod ν)) (hg : Integrable g (μ.prod ν))
    (hpoint : ∀ᵐ p ∂(μ.prod ν),
      (5 / 4 : ℝ) * |f p - g p| ≤ denominatorTransferCost q * smoothingEpsilon m)
    (hmass : μ.real Set.univ * ν.real Set.univ = 5 / 4) :
    |(∫ p, f p ∂(μ.prod ν)) - ∫ p, g p ∂(μ.prod ν)| ≤
      denominatorTransferCost q * smoothingEpsilon m := by
  have hcost : 0 ≤ denominatorTransferCost q := by
    unfold denominatorTransferCost
    exact mul_nonneg (by norm_num) (denominatorLipschitz_pos hq).le
  have heps : 0 ≤ smoothingEpsilon m :=
    (smoothingEpsilon_pos (by omega : 0 < m)).le
  let D : ℝ := denominatorTransferCost q * smoothingEpsilon m
  have hD : 0 ≤ D := by
    dsimp [D]
    exact mul_nonneg hcost heps
  have hpoint' : ∀ᵐ p ∂(μ.prod ν),
      |f p - g p| ≤ (4 / 5 : ℝ) * D := by
    filter_upwards [hpoint] with p hp
    have habs : 0 ≤ |f p - g p| := abs_nonneg _
    dsimp [D]
    nlinarith
  have hpair := pair_integral_transfer μ ν hf hg hpoint'
    (by positivity : 0 ≤ (4 / 5 : ℝ) * D)
  calc
    |(∫ p, f p ∂(μ.prod ν)) - ∫ p, g p ∂(μ.prod ν)| ≤
        (4 / 5 : ℝ) * D * μ.real Set.univ * ν.real Set.univ := hpair
    _ = (4 / 5 : ℝ) * D * (μ.real Set.univ * ν.real Set.univ) := by ring
    _ = D := by rw [hmass]; ring
    _ = denominatorTransferCost q * smoothingEpsilon m := rfl

/-- Reversed v13 mass ordering `(5/4,1)`, for the dual-field orientation. -/
theorem weighted_pair_integral_transfer_reversed
    {q m : ℕ} (hq : 2 ≤ q) (hm : 64 ≤ m)
    (μ ν : Measure ℂ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {f g : ℂ × ℂ → ℝ}
    (hf : Integrable f (μ.prod ν)) (hg : Integrable g (μ.prod ν))
    (hpoint : ∀ᵐ p ∂(μ.prod ν),
      (5 / 4 : ℝ) * |f p - g p| ≤ denominatorTransferCost q * smoothingEpsilon m)
    (hμmass : μ.real Set.univ = 5 / 4)
    (hνmass : ν.real Set.univ = 1) :
    |(∫ p, f p ∂(μ.prod ν)) - ∫ p, g p ∂(μ.prod ν)| ≤
      denominatorTransferCost q * smoothingEpsilon m := by
  apply weighted_pair_integral_transfer_of_mass hq hm μ ν hf hg hpoint
  rw [hμmass, hνmass]
  ring

end B3

end

end Li2Lean

#print axioms Li2Lean.B3.weighted_pair_integral_transfer
