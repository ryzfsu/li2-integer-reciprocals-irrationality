/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/

import Mathlib
import Li2Lean.B3.SmoothedEmpirical
import Li2Lean.P0.TubeCircle
import Li2Lean.V.SignedEnergy

/-!
# Energy adapters for the signed V smoothing interface

The declarations instantiate the frozen v6 empirical-circle energy API at the
translated circles of the v13 signed V construction. They cover the
finite-configuration expansion, its separated-center and collision branches,
and the diagonal circle cost in source/chapters/v-analytic.tex:532-549.
They do not prove the signed three-component energy inequality or the
determinant integral estimate. The imported frozen-v6
realLogKernel/circlePairEnergy use the negative-log convention, whereas the
v13 signed energy I uses positive log. The sign conversion is deliberately
left explicit at the later signed-Q consumer; these adapters must not be
read as that conversion.
-/

namespace Li2Lean

noncomputable section

namespace B3

open MeasureTheory Set Filter
open scoped ENNReal

open Li2Lean.P0

/-- The v13 radius is the inverse square used by the frozen circle API. -/
theorem smoothingEpsilon_eq_inv_sq {m : ℕ} :
    smoothingEpsilon m = ((m : ℝ) ^ 2)⁻¹ := by
  simp [smoothingEpsilon, inv_pow]

/-- Exact product-energy expansion for one translated empirical block,
v13 source/chapters/v-analytic.tex:532-545. -/
theorem translatedEmpiricalMeasure_energy_eq {d : ℕ}
    (u : Fin d → ℂ) {m : ℕ} (hm : 0 < m) :
    (∫ p : ℂ × ℂ, realLogKernel p.1 p.2
      ∂((translatedEmpiricalMeasure u m).prod
        (translatedEmpiricalMeasure u m))) =
      (∑ i : Fin d, ∑ j : Fin d,
        circlePairEnergy (translatedAtomCenter (u i) m)
          (translatedAtomCenter (u j) m) (smoothingEpsilon m)) /
        (m : ℝ) ^ 2 := by
  unfold translatedEmpiricalMeasure
  exact circleEmpiricalMeasure_energy_eq
    (fun i : Fin d => translatedAtomCenter (u i) m)
    (smoothingEpsilon_pos hm) m

/-- Separated-center transfer for a translated empirical block. The
collision branch is exposed separately below, as required by the
Vandermonde-weighted integral. -/
theorem translatedEmpiricalMeasure_energy_transfer {d : ℕ}
    (u : Fin d → ℂ) {m : ℕ} (hm : 0 < m)
    (hcenter : ∀ i j, i ≠ j →
      translatedAtomCenter (u i) m ≠ translatedAtomCenter (u j) m) :
    (∑ i : Fin d, ∑ j : Fin d,
      if i = j then 0 else
        realLogKernel (translatedAtomCenter (u i) m)
          (translatedAtomCenter (u j) m)) / (m : ℝ) ^ 2 ≥
      (∫ p : ℂ × ℂ, realLogKernel p.1 p.2
        ∂((translatedEmpiricalMeasure u m).prod
          (translatedEmpiricalMeasure u m))) -
        (d : ℝ) / (m : ℝ) ^ 2 *
          Real.log (1 / smoothingEpsilon m) := by
  unfold translatedEmpiricalMeasure
  exact circleEmpiricalMeasure_energy_transfer
    (fun i : Fin d => translatedAtomCenter (u i) m)
    (smoothingEpsilon_pos hm) hcenter m

/-- Collision-aware transfer, retaining the zero-Vandermonde alternative. -/
theorem translatedEmpiricalMeasure_energy_collision_split {d : ℕ}
    (u : Fin d → ℂ) {m : ℕ} (hm : 0 < m) :
    vandermondeSq d (fun i : Fin d => translatedAtomCenter (u i) m) = 0 ∨
      (∑ i : Fin d, ∑ j : Fin d,
        if i = j then 0 else
          realLogKernel (translatedAtomCenter (u i) m)
            (translatedAtomCenter (u j) m)) / (m : ℝ) ^ 2 ≥
        (∫ p : ℂ × ℂ, realLogKernel p.1 p.2
          ∂((translatedEmpiricalMeasure u m).prod
            (translatedEmpiricalMeasure u m))) -
          (d : ℝ) / (m : ℝ) ^ 2 *
            Real.log (1 / smoothingEpsilon m) := by
  unfold translatedEmpiricalMeasure
  exact circleEmpiricalMeasure_energy_collision_split
    (fun i : Fin d => translatedAtomCenter (u i) m)
    (smoothingEpsilon_pos hm) m

/-- The diagonal energy of one v13 smoothing circle is log(1/epsilon),
v13 source/chapters/v-analytic.tex:538-542. -/
theorem translatedCirclePairEnergy_self {u : ℂ} {m : ℕ} (hm : 0 < m) :
    circlePairEnergy (translatedAtomCenter u m) (translatedAtomCenter u m)
        (smoothingEpsilon m) =
      Real.log (1 / smoothingEpsilon m) := by
  exact circlePairEnergy_self (translatedAtomCenter u m)
    (smoothingEpsilon_pos hm)

/-- At epsilon=m^-2, the diagonal cost is exactly 2 log m. -/
theorem translatedCirclePairEnergy_self_eq_two_log_m {u : ℂ}
    {m : ℕ} (hm : 0 < m) :
    circlePairEnergy (translatedAtomCenter u m) (translatedAtomCenter u m)
        (smoothingEpsilon m) =
      2 * Real.log (m : ℝ) := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  simpa [smoothingEpsilon, inv_pow] using
    (circlePairEnergy_self_inverse_sq (translatedAtomCenter u m) hmR)

/-! ## Positive-log adapters for the v13 signed energy -/

/-- The positive logarithmic kernel used by v13 I(sigma,eta)
(`source/chapters/v-analytic.tex:14-20`).  The frozen v6 circle API uses
the negative-log kernel, so this is an explicit sign adapter. -/
noncomputable def v13LogKernel (z w : ℂ) : ℝ := Real.log ‖z - w‖

/-- The positive-log circle interaction in v13, as the negation of the
reused frozen-v6 interaction. -/
noncomputable def v13CirclePairEnergy (z w : ℂ) (r : ℝ) : ℝ :=
  -circlePairEnergy z w r

theorem v13LogKernel_eq_neg_realLogKernel (z w : ℂ) :
    v13LogKernel z w = -realLogKernel z w := by
  simp [v13LogKernel, realLogKernel]

theorem v13CirclePairEnergy_eq_neg (z w : ℂ) (r : ℝ) :
    v13CirclePairEnergy z w r = -circlePairEnergy z w r := rfl

theorem translatedCirclePairEnergy_self_eq_log_epsilon {u : ℂ}
    {m : ℕ} (hm : 0 < m) :
    v13CirclePairEnergy (translatedAtomCenter u m)
        (translatedAtomCenter u m) (smoothingEpsilon m) =
      -Real.log (1 / smoothingEpsilon m) := by
  unfold v13CirclePairEnergy
  rw [translatedCirclePairEnergy_self hm]

theorem translatedCirclePairEnergy_self_eq_neg_two_log_m {u : ℂ}
    {m : ℕ} (hm : 0 < m) :
    v13CirclePairEnergy (translatedAtomCenter u m)
        (translatedAtomCenter u m) (smoothingEpsilon m) =
      -(2 * Real.log (m : ℝ)) := by
  unfold v13CirclePairEnergy
  rw [translatedCirclePairEnergy_self_eq_two_log_m hm]

theorem translatedEmpiricalMeasure_v13_energy_eq {d : ℕ}
    (u : Fin d → ℂ) {m : ℕ} (hm : 0 < m) :
    (∫ p : ℂ × ℂ, v13LogKernel p.1 p.2
      ∂((translatedEmpiricalMeasure u m).prod
        (translatedEmpiricalMeasure u m))) =
      (∑ i : Fin d, ∑ j : Fin d,
        v13CirclePairEnergy (translatedAtomCenter (u i) m)
          (translatedAtomCenter (u j) m) (smoothingEpsilon m)) /
        (m : ℝ) ^ 2 := by
  have h := translatedEmpiricalMeasure_energy_eq u hm
  rw [show (fun p : ℂ × ℂ => v13LogKernel p.1 p.2) =
      (fun p => -realLogKernel p.1 p.2) by
        funext p
        exact (v13LogKernel_eq_neg_realLogKernel p.1 p.2)]
  rw [integral_neg, h]
  simp only [v13CirclePairEnergy]
  simp only [Finset.sum_neg_distrib, neg_div]

/-- The signed-V interaction uses the opposite sign from the frozen
negative-log `li2LogInteraction` kernel. -/
theorem vLogInteraction_eq_neg_realLogKernel (μ ν : Measure ℂ) :
    Li2Lean.V.vLogInteraction μ ν =
      -∫ p : ℂ × ℂ, realLogKernel p.1 p.2 ∂(μ.prod ν) := by
  rfl

/-- Exact cross expansion for the signed-V interaction of two translated
empirical blocks. -/
theorem translatedEmpiricalMeasure_vLogInteraction_cross_eq
    {d e : ℕ} (u : Fin d → ℂ) (v : Fin e → ℂ)
    {m : ℕ} (hm : 0 < m) :
    Li2Lean.V.vLogInteraction (translatedEmpiricalMeasure u m)
        (translatedEmpiricalMeasure v m) =
      -((∑ i : Fin d, ∑ j : Fin e,
        circlePairEnergy (translatedAtomCenter (u i) m)
          (translatedAtomCenter (v j) m) (smoothingEpsilon m)) /
        (m : ℝ) ^ 2) := by
  rw [vLogInteraction_eq_neg_realLogKernel,
    translatedEmpiricalMeasure_cross_energy_eq u v hm]

/-- Positive-log form of the v13 smoothing transfer.  This is obtained by
negating the reusable frozen-v6 negative-log estimate; the diagonal cost is
therefore retained with the sign shown in `v-analytic.tex:544-549`. -/
theorem translatedEmpiricalMeasure_v13_energy_transfer {d : ℕ}
    (u : Fin d → ℂ) {m : ℕ} (hm : 0 < m)
    (hcenter : ∀ i j, i ≠ j →
      translatedAtomCenter (u i) m ≠ translatedAtomCenter (u j) m) :
    (∑ i : Fin d, ∑ j : Fin d,
      if i = j then 0 else
        v13LogKernel (translatedAtomCenter (u i) m)
          (translatedAtomCenter (u j) m)) / (m : ℝ) ^ 2 ≤
      (∫ p : ℂ × ℂ, v13LogKernel p.1 p.2
        ∂((translatedEmpiricalMeasure u m).prod
          (translatedEmpiricalMeasure u m))) +
        (d : ℝ) / (m : ℝ) ^ 2 *
          Real.log (1 / smoothingEpsilon m) := by
  have hneg := translatedEmpiricalMeasure_energy_transfer u hm hcenter
  have hA :
      (∑ i : Fin d, ∑ j : Fin d,
        if i = j then 0 else
          v13LogKernel (translatedAtomCenter (u i) m)
            (translatedAtomCenter (u j) m)) / (m : ℝ) ^ 2 =
        -((∑ i : Fin d, ∑ j : Fin d,
          if i = j then 0 else
            realLogKernel (translatedAtomCenter (u i) m)
              (translatedAtomCenter (u j) m)) / (m : ℝ) ^ 2) := by
    simp only [v13LogKernel_eq_neg_realLogKernel]
    have hterm (i j : Fin d) :
        (if i = j then 0 else
          -realLogKernel (translatedAtomCenter (u i) m)
            (translatedAtomCenter (u j) m)) =
        -(if i = j then 0 else
          realLogKernel (translatedAtomCenter (u i) m)
            (translatedAtomCenter (u j) m)) := by
      by_cases hij : i = j <;> simp [hij]
    simp_rw [hterm, Finset.sum_neg_distrib, neg_div]
  have hE :
      (∫ p : ℂ × ℂ, v13LogKernel p.1 p.2
        ∂((translatedEmpiricalMeasure u m).prod
          (translatedEmpiricalMeasure u m))) =
        -( ∫ p : ℂ × ℂ, realLogKernel p.1 p.2
          ∂((translatedEmpiricalMeasure u m).prod
            (translatedEmpiricalMeasure u m))) := by
    rw [show (fun p : ℂ × ℂ => v13LogKernel p.1 p.2) =
        (fun p => -realLogKernel p.1 p.2) by
          funext p
          exact v13LogKernel_eq_neg_realLogKernel p.1 p.2]
    rw [integral_neg]
  rw [hA, hE]
  linarith

/-! The diagonal cost in the exact `epsilon = m⁻²` normalization.  Keeping
this specialization separate lets the S0 transfer assembly use the paper's
`2 d log(m) / m²` term without repeating the inverse-square logarithm algebra.
-/
theorem translatedEmpiricalMeasure_v13_energy_transfer_log_cost {d : ℕ}
    (u : Fin d → ℂ) {m : ℕ} (hm : 0 < m)
    (hcenter : ∀ i j, i ≠ j →
      translatedAtomCenter (u i) m ≠ translatedAtomCenter (u j) m) :
    (∑ i : Fin d, ∑ j : Fin d,
      if i = j then 0 else
        v13LogKernel (translatedAtomCenter (u i) m)
          (translatedAtomCenter (u j) m)) / (m : ℝ) ^ 2 ≤
      (∫ p : ℂ × ℂ, v13LogKernel p.1 p.2
        ∂((translatedEmpiricalMeasure u m).prod
          (translatedEmpiricalMeasure u m))) +
        (2 * (d : ℝ) / (m : ℝ) ^ 2) * Real.log (m : ℝ) := by
  have hbase := translatedEmpiricalMeasure_v13_energy_transfer u hm hcenter
  have hlog : Real.log (1 / smoothingEpsilon m) =
      2 * Real.log (m : ℝ) := by
    rw [smoothingEpsilon_eq_inv_sq]
    rw [one_div, inv_inv, Real.log_pow]
    norm_num
  rw [hlog] at hbase
  have hcost :
      ((d : ℝ) / (m : ℝ) ^ 2) * (2 * Real.log (m : ℝ)) =
        (2 * (d : ℝ) / (m : ℝ) ^ 2) * Real.log (m : ℝ) := by
    ring
  calc
    _ ≤ (∫ p : ℂ × ℂ, v13LogKernel p.1 p.2
        ∂((translatedEmpiricalMeasure u m).prod
          (translatedEmpiricalMeasure u m))) +
        ((d : ℝ) / (m : ℝ) ^ 2) * (2 * Real.log (m : ℝ)) := hbase
    _ = _ := by rw [hcost]

/-- Collision-aware positive-log transfer.  The zero-Vandermonde branch is
kept explicit; only its nonzero branch supplies the pairwise separation needed
by the off-diagonal estimate (`v-analytic.tex:541-546`). -/
theorem translatedEmpiricalMeasure_v13_energy_collision_split {d : ℕ}
    (u : Fin d → ℂ) {m : ℕ} (hm : 0 < m) :
    vandermondeSq d (fun i : Fin d => translatedAtomCenter (u i) m) = 0 ∨
      (∑ i : Fin d, ∑ j : Fin d,
        if i = j then 0 else
          v13LogKernel (translatedAtomCenter (u i) m)
            (translatedAtomCenter (u j) m)) / (m : ℝ) ^ 2 ≤
        (∫ p : ℂ × ℂ, v13LogKernel p.1 p.2
          ∂((translatedEmpiricalMeasure u m).prod
            (translatedEmpiricalMeasure u m))) +
          (d : ℝ) / (m : ℝ) ^ 2 *
            Real.log (1 / smoothingEpsilon m) := by
  let centers : Fin d → ℂ := fun i => translatedAtomCenter (u i) m
  by_cases hV : vandermondeSq d centers = 0
  · exact Or.inl hV
  · right
    have hVbase : vandermonde d centers ≠ 0 := by
      intro hzero
      apply hV
      simp [vandermondeSq, hzero]
    have hcenter : ∀ i j, i ≠ j → centers i ≠ centers j :=
      pairwise_ne_of_vandermonde_ne_zero centers hVbase
    exact translatedEmpiricalMeasure_v13_energy_transfer u hm hcenter

end B3

end

end Li2Lean

#print axioms Li2Lean.B3.translatedEmpiricalMeasure_energy_eq
#print axioms Li2Lean.B3.translatedEmpiricalMeasure_energy_transfer
#print axioms Li2Lean.B3.translatedEmpiricalMeasure_energy_collision_split
#print axioms Li2Lean.B3.translatedCirclePairEnergy_self_eq_two_log_m
#print axioms Li2Lean.B3.v13LogKernel_eq_neg_realLogKernel
#print axioms Li2Lean.B3.v13CirclePairEnergy_eq_neg
#print axioms Li2Lean.B3.translatedCirclePairEnergy_self_eq_log_epsilon
#print axioms Li2Lean.B3.translatedCirclePairEnergy_self_eq_neg_two_log_m
#print axioms Li2Lean.B3.translatedEmpiricalMeasure_v13_energy_eq
#print axioms Li2Lean.B3.translatedEmpiricalMeasure_v13_energy_transfer
#print axioms Li2Lean.B3.translatedEmpiricalMeasure_v13_energy_collision_split

