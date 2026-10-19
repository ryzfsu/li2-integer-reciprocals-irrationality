/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B3.S0TCoreBound
import Li2Lean.B3.PACK9DC6
import Li2Lean.B3.DenominatorIntegral

/-!
# C6 Smoothed Pair Expansions (`H5-c6`)

This module closes the C6 mixed (`z-v`) and denominator (`x-v`) measure-to-discrete
pair expansion gap between the smoothed empirical measures
`v13SmoothedEmpiricalMeasures` (`translatedEmpiricalMeasure`) and the discrete
sums `V.c5CrossLog` and `V.c5DenominatorLog`:

1. **(G1) Cross empirical-measure expansion for `realLogKernel`, `li2LogInteraction`,
   and `V.vLogInteraction`**:
   generalizes `P0.circleEmpiricalMeasure_energy_eq` (`P0/TubeCircleMeasure.lean:291`)
   from a single array `z : Fin d → ℂ` to two arrays `z : Fin d → ℂ` and
   `w : Fin e → ℂ`, and connects it with the sign flip
   `V.vLogInteraction = -li2LogInteraction` and `v13CirclePairEnergy = -circlePairEnergy`.
2. **(G2) Cross empirical-measure expansion for `V.vCrossInteraction q`**:
   defines the per-pair double-circle average `translatedCrossCirclePairEnergy q x y m`,
   proves product-measure integrability on the unit-disk tube for `2 ≤ q` and `64 ≤ m`,
   and expands `V.vCrossInteraction q (translatedEmpiricalMeasure u m) (translatedEmpiricalMeasure v m)`
   into the normalized finite double sum over `Fin d × Fin e`.
3. **(G3) Per-pair and finite-sum C6 transfer inequalities**:
   combines the sub-mean inequality (`c6_cross_pair_transfer` / `circlePairEnergy_le_neg_log_max`)
   for the mixed `z-v` log sum with the Lipschitz tube bounds
   (`c6_denominator_atom_log_upper` and `weighted_denominator_pair_cost`) for the
   `x-v` denominator sum to establish `c6_cross_smoothed_transfer`,
   `c6_denominator_smoothed_transfer`, `c6_denominator_smoothed_abs_transfer`, and
   `v13_c6_mixed_and_denominator_smoothed_transfer`.
-/

namespace Li2Lean.B3

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators ENNReal

/-! ## 1. (G1) Cross empirical-measure expansion for `realLogKernel` and `V.vLogInteraction` -/

/-- Absolute integrability of `P0.realLogKernel` on the product of two circle empirical
    measures with arbitrary finite block sizes `d` and `e`. -/
theorem integrable_realLogKernel_circleEmpiricalMeasure_prod_cross {d e : ℕ}
    (z : Fin d → ℂ) (w : Fin e → ℂ) {r : ℝ} (hr : 0 < r) (m : ℕ) :
    Integrable (fun p : ℂ × ℂ => P0.realLogKernel p.1 p.2)
      ((P0.circleEmpiricalMeasure z r m).prod (P0.circleEmpiricalMeasure w r m)) := by
  simp only [P0.circleEmpiricalMeasure, Measure.prod_smul_left, Measure.prod_smul_right]
  apply Integrable.smul_measure _ ENNReal.ofReal_ne_top
  apply Integrable.smul_measure _ ENNReal.ofReal_ne_top
  rw [Measure.prod_sum, Measure.sum_fintype]
  apply integrable_finsetSum_measure.mpr
  intro ij _
  exact P0.integrable_realLogKernel_circleProbability_prod (z ij.1) (w ij.2) hr

/-- Cross-array generalization of `P0.circleEmpiricalMeasure_energy_eq`
    (`Li2Lean/P0/TubeCircleMeasure.lean:291-303`) for two arrays `z : Fin d → ℂ`
    and `w : Fin e → ℂ`. -/
theorem circleEmpiricalMeasure_cross_energy_eq {d e : ℕ}
    (z : Fin d → ℂ) (w : Fin e → ℂ) {r : ℝ} (hr : 0 < r) (m : ℕ) :
    (∫ p : ℂ × ℂ, P0.realLogKernel p.1 p.2
      ∂((P0.circleEmpiricalMeasure z r m).prod
        (P0.circleEmpiricalMeasure w r m))) =
      (∑ i : Fin d, ∑ j : Fin e, P0.circlePairEnergy (z i) (w j) r) /
        (m : ℝ) ^ 2 := by
  simp only [P0.circleEmpiricalMeasure, Measure.prod_smul_left, Measure.prod_smul_right,
    integral_smul_measure, ENNReal.toReal_ofReal (inv_nonneg.mpr (Nat.cast_nonneg m)),
    smul_eq_mul]
  rw [Measure.prod_sum, Measure.sum_fintype,
    integral_finsetSum_measure (fun ij _ =>
      P0.integrable_realLogKernel_circleProbability_prod (z ij.1) (w ij.2) hr)]
  simp_rw [P0.integral_realLogKernel_circleProbability_prod_eq _ _ hr]
  rw [Fintype.sum_prod_type]
  ring

/-- `li2LogInteraction` expansion for two circle empirical measures. -/
theorem li2LogInteraction_circleEmpiricalMeasure_eq {d e : ℕ}
    (z : Fin d → ℂ) (w : Fin e → ℂ) {r : ℝ} (hr : 0 < r) (m : ℕ) :
    li2LogInteraction (P0.circleEmpiricalMeasure z r m)
      (P0.circleEmpiricalMeasure w r m) =
      (∑ i : Fin d, ∑ j : Fin e, P0.circlePairEnergy (z i) (w j) r) /
        (m : ℝ) ^ 2 := by
  unfold li2LogInteraction
  have hfn : (fun x : ℂ × ℂ => li2LogKernel x.1 x.2) =
      (fun p : ℂ × ℂ => P0.realLogKernel p.1 p.2) := rfl
  rw [hfn]
  exact circleEmpiricalMeasure_cross_energy_eq z w hr m

/-- `V.vLogInteraction` expansion for two circle empirical measures, making the sign
    conversion `V.vLogInteraction = -li2LogInteraction` explicit. -/
theorem vLogInteraction_circleEmpiricalMeasure_eq {d e : ℕ}
    (z : Fin d → ℂ) (w : Fin e → ℂ) {r : ℝ} (hr : 0 < r) (m : ℕ) :
    V.vLogInteraction (P0.circleEmpiricalMeasure z r m)
      (P0.circleEmpiricalMeasure w r m) =
      -(∑ i : Fin d, ∑ j : Fin e, P0.circlePairEnergy (z i) (w j) r) /
        (m : ℝ) ^ 2 := by
  unfold V.vLogInteraction
  rw [li2LogInteraction_circleEmpiricalMeasure_eq z w hr m, neg_div]

/-- Cross product-energy expansion for two translated empirical blocks in the positive-log
    `V.vLogInteraction` / `v13CirclePairEnergy` convention. -/
theorem vLogInteraction_translatedEmpiricalMeasure_eq {d e : ℕ}
    (u : Fin d → ℂ) (v : Fin e → ℂ) {m : ℕ} (hm : 0 < m) :
    V.vLogInteraction (translatedEmpiricalMeasure u m)
      (translatedEmpiricalMeasure v m) =
      (∑ i : Fin d, ∑ j : Fin e,
        v13CirclePairEnergy (translatedAtomCenter (u i) m)
          (translatedAtomCenter (v j) m) (smoothingEpsilon m)) /
        (m : ℝ) ^ 2 := by
  unfold translatedEmpiricalMeasure
  rw [vLogInteraction_circleEmpiricalMeasure_eq _ _ (smoothingEpsilon_pos hm) m]
  simp only [v13CirclePairEnergy, Finset.sum_neg_distrib]

/-! ## 2. (G2) Double-circle pair expansion for `V.vCrossInteraction q` -/

/-- The `P0.circlePoint` parametrization at `translatedAtomCenter u m` and radius
    `smoothingEpsilon m` coincides with `translatedAtom u m`. -/
theorem circlePoint_translatedAtomCenter_eq (u : ℂ) (m : ℕ) (theta : ℝ) :
    P0.circlePoint (translatedAtomCenter u m) (smoothingEpsilon m) theta =
      translatedAtom u m theta := by
  unfold translatedAtom
  exact ContourKit.p0CirclePoint_eq_circleMap
    (translatedAtomCenter u m) (smoothingEpsilon m) theta

/-- Measurability of the cross kernel `V.vCrossKernel q (z, w) = log ‖q + z * w‖`. -/
theorem measurable_vCrossKernel (q : ℕ) :
    Measurable (fun p : ℂ × ℂ => V.vCrossKernel q p.1 p.2) := by
  unfold V.vCrossKernel
  fun_prop

/-- Per-pair double-circle average of the denominator kernel `V.vCrossKernel q`
    over the two translated circles around `x` and `y` at scale `m`. -/
noncomputable def translatedCrossCirclePairEnergy (q : ℕ) (x y : ℂ) (m : ℕ) : ℝ :=
  (∫ p : ℝ × ℝ,
    V.vCrossKernel q (translatedAtom x m p.1) (translatedAtom y m p.2)
    ∂(P0.circleAngleMeasure.prod P0.circleAngleMeasure)) / (2 * Real.pi) ^ 2

/-- The integral of `V.vCrossKernel q` against the product of two translated probability
    circles equals `translatedCrossCirclePairEnergy q x y m`. -/
theorem integral_vCrossKernel_translatedCircleMeasure_prod_eq
    (q : ℕ) (x y : ℂ) (m : ℕ) :
    (∫ p : ℂ × ℂ, V.vCrossKernel q p.1 p.2
      ∂((translatedCircleMeasure x m).prod (translatedCircleMeasure y m))) =
      translatedCrossCirclePairEnergy q x y m := by
  let zx := translatedAtomCenter x m
  let zy := translatedAtomCenter y m
  let r := smoothingEpsilon m
  have hmap : Measurable (Prod.map (P0.circlePoint zx r) (P0.circlePoint zy r)) :=
    (P0.continuous_circlePoint zx r).measurable.prodMap
      (P0.continuous_circlePoint zy r).measurable
  unfold translatedCircleMeasure translatedCrossCirclePairEnergy
  simp only [P0.circleProbability, Measure.prod_smul_left, Measure.prod_smul_right,
    integral_smul_measure, ENNReal.toReal_ofReal (inv_nonneg.mpr Real.two_pi_pos.le),
    smul_eq_mul]
  rw [Measure.map_prod_map P0.circleAngleMeasure P0.circleAngleMeasure
    (P0.continuous_circlePoint zx r).measurable
    (P0.continuous_circlePoint zy r).measurable,
    integral_map_of_stronglyMeasurable hmap
      (measurable_vCrossKernel q).stronglyMeasurable]
  simp only [zx, zy, r, Prod.map, circlePoint_translatedAtomCenter_eq]
  ring

set_option maxHeartbeats 1000000 in
/-- Absolute integrability of the pulled-back cross kernel on
    `P0.circleAngleMeasure.prod P0.circleAngleMeasure` when `‖x‖ ≤ 1`, `‖y‖ ≤ 1`,
    `2 ≤ q`, and `64 ≤ m`. -/
theorem integrable_vCrossKernel_translatedAtom_prod
    {q m : ℕ} (hq : 2 ≤ q) (hm : 64 ≤ m)
    (x y : ℂ) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    Integrable
      (fun p : ℝ × ℝ => V.vCrossKernel q (translatedAtom x m p.1) (translatedAtom y m p.2))
      (P0.circleAngleMeasure.prod P0.circleAngleMeasure) := by
  let zx := translatedAtomCenter x m
  let zy := translatedAtomCenter y m
  let r := smoothingEpsilon m
  let B : ℝ := |V.vCrossKernel q x y| +
    denominatorLipschitz q * (6 * smoothingEpsilon m + 9 * smoothingEpsilon m ^ 2)
  have hmeas_angle : Measurable
      (fun p : ℝ × ℝ => V.vCrossKernel q (P0.circlePoint zx r p.1) (P0.circlePoint zy r p.2)) :=
    (measurable_vCrossKernel q).comp
      (((P0.continuous_circlePoint zx r).measurable.comp measurable_fst).prodMk
        ((P0.continuous_circlePoint zy r).measurable.comp measurable_snd))
  have hfn :
      (fun p : ℝ × ℝ => V.vCrossKernel q (translatedAtom x m p.1) (translatedAtom y m p.2)) =
        (fun p : ℝ × ℝ =>
          V.vCrossKernel q (P0.circlePoint zx r p.1) (P0.circlePoint zy r p.2)) := by
    funext p
    simp only [zx, zy, r, circlePoint_translatedAtomCenter_eq]
  have hmeas : AEStronglyMeasurable
      (fun p : ℝ × ℝ => V.vCrossKernel q (translatedAtom x m p.1) (translatedAtom y m p.2))
      (P0.circleAngleMeasure.prod P0.circleAngleMeasure) := by
    rw [hfn]
    exact hmeas_angle.aestronglyMeasurable
  refine (integrable_const B).mono' hmeas (Filter.Eventually.of_forall (fun p => ?_))
  rw [Real.norm_eq_abs]
  have htr := translatedAtom_denominator_log_transfer hq hm x y p.1 p.2 hx hy
  change |V.vCrossKernel q (translatedAtom x m p.1) (translatedAtom y m p.2) -
    V.vCrossKernel q x y| ≤
    denominatorLipschitz q * (6 * smoothingEpsilon m + 9 * smoothingEpsilon m ^ 2) at htr
  have htr' := abs_le.mp htr
  have hbase := abs_le.mp (le_refl |V.vCrossKernel q x y|)
  dsimp [B]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Absolute integrability of `V.vCrossKernel q` on the product of two translated
    circle probability measures when `‖x‖ ≤ 1`, `‖y‖ ≤ 1`, `2 ≤ q`, and `64 ≤ m`. -/
theorem integrable_vCrossKernel_translatedCircleMeasure_prod
    {q m : ℕ} (hq : 2 ≤ q) (hm : 64 ≤ m)
    (x y : ℂ) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    Integrable (fun p : ℂ × ℂ => V.vCrossKernel q p.1 p.2)
      ((translatedCircleMeasure x m).prod (translatedCircleMeasure y m)) := by
  let zx := translatedAtomCenter x m
  let zy := translatedAtomCenter y m
  let r := smoothingEpsilon m
  have hmap : Measurable (Prod.map (P0.circlePoint zx r) (P0.circlePoint zy r)) :=
    (P0.continuous_circlePoint zx r).measurable.prodMap
      (P0.continuous_circlePoint zy r).measurable
  unfold translatedCircleMeasure
  simp only [P0.circleProbability, Measure.prod_smul_left, Measure.prod_smul_right]
  apply Integrable.smul_measure _ ENNReal.ofReal_ne_top
  apply Integrable.smul_measure _ ENNReal.ofReal_ne_top
  rw [Measure.map_prod_map P0.circleAngleMeasure P0.circleAngleMeasure
    (P0.continuous_circlePoint zx r).measurable
    (P0.continuous_circlePoint zy r).measurable]
  apply (integrable_map_measure (measurable_vCrossKernel q).aestronglyMeasurable
    hmap.aemeasurable).mpr
  simpa only [zx, zy, r, Function.comp_def, Prod.map, circlePoint_translatedAtomCenter_eq] using
    integrable_vCrossKernel_translatedAtom_prod hq hm x y hx hy

/-- Absolute integrability of `V.vCrossKernel q` on the product of two translated
    empirical measures when all centres lie in the closed unit disk. -/
theorem integrable_vCrossKernel_translatedEmpiricalMeasure_prod
    {q d e m : ℕ} (hq : 2 ≤ q) (hm : 64 ≤ m)
    (u : Fin d → ℂ) (v : Fin e → ℂ)
    (hu : ∀ i, ‖u i‖ ≤ 1) (hv : ∀ j, ‖v j‖ ≤ 1) :
    Integrable (fun p : ℂ × ℂ => V.vCrossKernel q p.1 p.2)
      ((translatedEmpiricalMeasure u m).prod (translatedEmpiricalMeasure v m)) := by
  unfold translatedEmpiricalMeasure P0.circleEmpiricalMeasure
  simp only [Measure.prod_smul_left, Measure.prod_smul_right]
  apply Integrable.smul_measure _ ENNReal.ofReal_ne_top
  apply Integrable.smul_measure _ ENNReal.ofReal_ne_top
  rw [Measure.prod_sum, Measure.sum_fintype]
  apply integrable_finsetSum_measure.mpr
  intro ij _
  exact integrable_vCrossKernel_translatedCircleMeasure_prod hq hm
    (u ij.1) (v ij.2) (hu ij.1) (hv ij.2)

/-- Exact finite-sum expansion of `V.vCrossInteraction q` on two translated empirical
    measures into per-pair double-circle averages `translatedCrossCirclePairEnergy`. -/
theorem vCrossInteraction_translatedEmpiricalMeasure_eq
    {q d e m : ℕ} (hq : 2 ≤ q) (hm : 64 ≤ m)
    (u : Fin d → ℂ) (v : Fin e → ℂ)
    (hu : ∀ i, ‖u i‖ ≤ 1) (hv : ∀ j, ‖v j‖ ≤ 1) :
    V.vCrossInteraction q (translatedEmpiricalMeasure u m)
      (translatedEmpiricalMeasure v m) =
      (∑ i : Fin d, ∑ j : Fin e,
        translatedCrossCirclePairEnergy q (u i) (v j) m) /
        (m : ℝ) ^ 2 := by
  unfold V.vCrossInteraction translatedEmpiricalMeasure
  simp only [P0.circleEmpiricalMeasure, Measure.prod_smul_left, Measure.prod_smul_right,
    integral_smul_measure, ENNReal.toReal_ofReal (inv_nonneg.mpr (Nat.cast_nonneg m)),
    smul_eq_mul]
  rw [Measure.prod_sum, Measure.sum_fintype,
    integral_finsetSum_measure (fun ij _ =>
      integrable_vCrossKernel_translatedCircleMeasure_prod hq hm
        (u ij.1) (v ij.2) (hu ij.1) (hv ij.2))]
  have hpair : ∀ (i : Fin d) (j : Fin e),
      (∫ p : ℂ × ℂ, V.vCrossKernel q p.1 p.2
        ∂((P0.circleProbability (translatedAtomCenter (u i) m) (smoothingEpsilon m)).prod
          (P0.circleProbability (translatedAtomCenter (v j) m) (smoothingEpsilon m)))) =
      translatedCrossCirclePairEnergy q (u i) (v j) m :=
    fun i j => integral_vCrossKernel_translatedCircleMeasure_prod_eq q (u i) (v j) m
  simp_rw [hpair]
  rw [Fintype.sum_prod_type]
  ring

/-! ## 3. (G3) Per-pair inequalities and C6 mixed + denominator smoothed transfer -/

/-- Common-translation cancellation for two translated centres. -/
@[simp]
theorem translatedAtomCenter_sub_eq (u v : ℂ) (m : ℕ) :
    translatedAtomCenter u m - translatedAtomCenter v m = u - v := by
  unfold translatedAtomCenter
  ring

/-- `v13LogKernel` is invariant under the common centre shift `+ 2 i ε`. -/
@[simp]
theorem v13LogKernel_translatedAtomCenter_eq (u v : ℂ) (m : ℕ) :
    v13LogKernel (translatedAtomCenter u m) (translatedAtomCenter v m) =
      Real.log ‖u - v‖ := by
  simp [v13LogKernel]

/-- Distinct atoms have distinct translated centres. -/
theorem translatedAtomCenter_ne_of_ne {u v : ℂ} (m : ℕ) (huv : u ≠ v) :
    translatedAtomCenter u m ≠ translatedAtomCenter v m := by
  intro heq
  apply huv
  unfold translatedAtomCenter at heq
  exact add_right_cancel heq

/-- Per-pair subharmonic circle-average lower bound in the positive-log convention:
    `log (max ε ‖u - v‖) ≤ v13CirclePairEnergy (translatedAtomCenter u m) (translatedAtomCenter v m) ε`. -/
theorem v13CirclePairEnergy_ge_log_max (u v : ℂ) {m : ℕ} (hm : 0 < m) :
    Real.log (max (smoothingEpsilon m) ‖u - v‖) ≤
      v13CirclePairEnergy (translatedAtomCenter u m)
        (translatedAtomCenter v m) (smoothingEpsilon m) := by
  unfold v13CirclePairEnergy
  have h := P0.circlePairEnergy_le_neg_log_max
    (translatedAtomCenter u m) (translatedAtomCenter v m) (smoothingEpsilon_pos hm)
  rw [translatedAtomCenter_sub_eq] at h
  linarith

/-- Symmetry of the discrete cross logarithmic sum `V.c5CrossLog`. -/
theorem c5CrossLog_comm {d e : ℕ} (u : Fin d → ℂ) (v : Fin e → ℂ) :
    V.c5CrossLog u v = V.c5CrossLog v u := by
  unfold V.c5CrossLog
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  rw [norm_sub_rev]

/-- `V.c5CrossLog` expressed in terms of `v13LogKernel` at translated centres. -/
theorem c5CrossLog_eq_sum_v13LogKernel_translatedAtomCenter
    {d e : ℕ} (u : Fin d → ℂ) (v : Fin e → ℂ) (m : ℕ) :
    V.c5CrossLog u v =
      ∑ i : Fin d, ∑ j : Fin e,
        v13LogKernel (translatedAtomCenter (u i) m)
          (translatedAtomCenter (v j) m) := by
  unfold V.c5CrossLog
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [v13LogKernel_translatedAtomCenter_eq]

/-- General C6 mixed cross-energy smoothed transfer for two disjoint finite families
    `u : Fin d → ℂ` and `v : Fin e → ℂ`. -/
theorem c6_cross_smoothed_transfer_general
    {d e m : ℕ} (hm : 0 < m)
    (u : Fin d → ℂ) (v : Fin e → ℂ)
    (huv : ∀ i j, u i ≠ v j) :
    V.c5CrossLog u v ≤
      (m : ℝ) ^ 2 *
        V.vLogInteraction (translatedEmpiricalMeasure u m)
          (translatedEmpiricalMeasure v m) := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hpair := c6_cross_pair_transfer u v hm
    (fun i j => translatedAtomCenter_ne_of_ne m (huv i j))
  rw [← c5CrossLog_eq_sum_v13LogKernel_translatedAtomCenter u v m] at hpair
  have hexp := vLogInteraction_translatedEmpiricalMeasure_eq u v hm
  have hexp' :
      (m : ℝ) ^ 2 *
        V.vLogInteraction (translatedEmpiricalMeasure u m)
          (translatedEmpiricalMeasure v m) =
      ∑ i : Fin d, ∑ j : Fin e,
        v13CirclePairEnergy (translatedAtomCenter (u i) m)
          (translatedAtomCenter (v j) m) (smoothingEpsilon m) := by
    rw [hexp]
    field_simp [hmR]
  linarith

/-- C6 mixed `z-v` smoothed transfer at scale `m = 4 * n`, oriented to match
    `V.vLogInteraction M.μv M.μz`. -/
theorem c6_cross_smoothed_transfer
    {n : ℕ} (hn : 0 < n)
    (v : Fin (5 * n) → ℝ) (z : Fin (4 * n) → ℂ)
    (hzv : ∀ i b, z i ≠ (v b : ℂ)) :
    V.c5CrossLog z (fun b => (v b : ℂ)) ≤
      ((4 * n : ℕ) : ℝ) ^ 2 *
        V.vLogInteraction
          (translatedEmpiricalMeasure (fun b => (v b : ℂ)) (4 * n))
          (translatedEmpiricalMeasure z (4 * n)) := by
  have hm : 0 < 4 * n := by omega
  rw [c5CrossLog_comm z (fun b => (v b : ℂ))]
  exact c6_cross_smoothed_transfer_general hm (fun b => (v b : ℂ)) z
    (fun b i => (hzv i b).symm)

/-- Normalized constant integral over `P0.circleAngleMeasure.prod P0.circleAngleMeasure`. -/
theorem integral_const_circleAngleMeasure_prod_div (C : ℝ) :
    (∫ _p : ℝ × ℝ, C ∂(P0.circleAngleMeasure.prod P0.circleAngleMeasure)) /
      (2 * Real.pi) ^ 2 = C := by
  have h2pi : (2 * Real.pi : ℝ) ≠ 0 := mul_ne_zero two_ne_zero Real.pi_ne_zero
  rw [integral_const, prod_real_univ, P0.circleAngleMeasure_mass, smul_eq_mul]
  field_simp [h2pi]

/-- Upper bound on `translatedCrossCirclePairEnergy` from a pointwise upper bound on angles. -/
theorem translatedCrossCirclePairEnergy_le_of_forall
    {q m : ℕ} (hq : 2 ≤ q) (hm : 64 ≤ m)
    (x y : ℂ) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) (C : ℝ)
    (hpt : ∀ p : ℝ × ℝ,
      V.vCrossKernel q (translatedAtom x m p.1) (translatedAtom y m p.2) ≤ C) :
    translatedCrossCirclePairEnergy q x y m ≤ C := by
  unfold translatedCrossCirclePairEnergy
  have hint := integrable_vCrossKernel_translatedAtom_prod hq hm x y hx hy
  have hmono :
      (∫ p : ℝ × ℝ,
        V.vCrossKernel q (translatedAtom x m p.1) (translatedAtom y m p.2)
        ∂(P0.circleAngleMeasure.prod P0.circleAngleMeasure)) ≤
      ∫ _p : ℝ × ℝ, C ∂(P0.circleAngleMeasure.prod P0.circleAngleMeasure) :=
    integral_mono hint (integrable_const C) hpt
  calc
    (∫ p : ℝ × ℝ,
        V.vCrossKernel q (translatedAtom x m p.1) (translatedAtom y m p.2)
        ∂(P0.circleAngleMeasure.prod P0.circleAngleMeasure)) / (2 * Real.pi) ^ 2 ≤
      (∫ _p : ℝ × ℝ, C ∂(P0.circleAngleMeasure.prod P0.circleAngleMeasure)) /
        (2 * Real.pi) ^ 2 :=
      div_le_div_of_nonneg_right hmono (sq_nonneg (2 * Real.pi))
    _ = C := integral_const_circleAngleMeasure_prod_div C

/-- Lower bound on `translatedCrossCirclePairEnergy` from a pointwise lower bound on angles. -/
theorem le_translatedCrossCirclePairEnergy_of_forall
    {q m : ℕ} (hq : 2 ≤ q) (hm : 64 ≤ m)
    (x y : ℂ) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) (C : ℝ)
    (hpt : ∀ p : ℝ × ℝ,
      C ≤ V.vCrossKernel q (translatedAtom x m p.1) (translatedAtom y m p.2)) :
    C ≤ translatedCrossCirclePairEnergy q x y m := by
  unfold translatedCrossCirclePairEnergy
  have hint := integrable_vCrossKernel_translatedAtom_prod hq hm x y hx hy
  have hmono :
      (∫ _p : ℝ × ℝ, C ∂(P0.circleAngleMeasure.prod P0.circleAngleMeasure)) ≤
      ∫ p : ℝ × ℝ,
        V.vCrossKernel q (translatedAtom x m p.1) (translatedAtom y m p.2)
        ∂(P0.circleAngleMeasure.prod P0.circleAngleMeasure) :=
    integral_mono (integrable_const C) hint hpt
  calc
    C = (∫ _p : ℝ × ℝ, C ∂(P0.circleAngleMeasure.prod P0.circleAngleMeasure)) /
        (2 * Real.pi) ^ 2 := (integral_const_circleAngleMeasure_prod_div C).symm
    _ ≤ (∫ p : ℝ × ℝ,
        V.vCrossKernel q (translatedAtom x m p.1) (translatedAtom y m p.2)
        ∂(P0.circleAngleMeasure.prod P0.circleAngleMeasure)) / (2 * Real.pi) ^ 2 :=
      div_le_div_of_nonneg_right hmono (sq_nonneg (2 * Real.pi))

/-- Per-pair double-circle upper bound from `c6_denominator_atom_log_upper`. -/
theorem translatedCrossCirclePairEnergy_upper_lipschitz
    {q m : ℕ} (hq : 2 ≤ q) (hm : 64 ≤ m)
    (x y : ℂ) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    translatedCrossCirclePairEnergy q x y m ≤
      V.vCrossKernel q x y +
        denominatorLipschitz q *
          (6 * smoothingEpsilon m + 9 * smoothingEpsilon m ^ 2) := by
  apply translatedCrossCirclePairEnergy_le_of_forall hq hm x y hx hy
  intro p
  exact c6_denominator_atom_log_upper hq hm x y p.1 p.2 hx hy

/-- Per-pair two-sided weighted denominator transfer for the double-circle average
    `translatedCrossCirclePairEnergy`, lifted from `weighted_denominator_pair_cost`. -/
theorem weighted_translatedCrossCirclePairEnergy_cost
    {q m : ℕ} (hq : 2 ≤ q) (hm : 64 ≤ m)
    (x y : ℂ) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    (5 / 4 : ℝ) *
      |translatedCrossCirclePairEnergy q x y m - V.vCrossKernel q x y| ≤
      denominatorTransferCost q * smoothingEpsilon m := by
  let D : ℝ := (4 / 5 : ℝ) * (denominatorTransferCost q * smoothingEpsilon m)
  have hpt_abs : ∀ p : ℝ × ℝ,
      |V.vCrossKernel q (translatedAtom x m p.1) (translatedAtom y m p.2) -
        V.vCrossKernel q x y| ≤ D := by
    intro p
    have hcost := weighted_denominator_pair_cost hq hm x y p.1 p.2 hx hy
    change (5 / 4 : ℝ) *
      |V.vCrossKernel q (translatedAtom x m p.1) (translatedAtom y m p.2) -
        V.vCrossKernel q x y| ≤
      denominatorTransferCost q * smoothingEpsilon m at hcost
    dsimp [D]
    linarith
  have hupper : translatedCrossCirclePairEnergy q x y m ≤ V.vCrossKernel q x y + D := by
    apply translatedCrossCirclePairEnergy_le_of_forall hq hm x y hx hy
    intro p
    linarith [(abs_le.mp (hpt_abs p)).2]
  have hlower : V.vCrossKernel q x y - D ≤ translatedCrossCirclePairEnergy q x y m := by
    apply le_translatedCrossCirclePairEnergy_of_forall hq hm x y hx hy
    intro p
    linarith [(abs_le.mp (hpt_abs p)).1]
  have habs : |translatedCrossCirclePairEnergy q x y m - V.vCrossKernel q x y| ≤ D :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  dsimp [D] at habs
  linarith

/-- One-sided C6 denominator smoothed transfer:
    `V.c5DenominatorLog - m^2 * V.vCrossInteraction ≤ denominatorTransferCost q`. -/
theorem c6_denominator_smoothed_transfer
    {q n : ℕ} (hq : 2 ≤ q) (hn : 64 ≤ 4 * n)
    (x : Fin (4 * n) → ℝ) (v : Fin (5 * n) → ℝ)
    (hx : ∀ i, x i ∈ Set.Icc (0 : ℝ) 1)
    (hv : ∀ b, v b ∈ Set.Icc (0 : ℝ) 1) :
    -V.c5DenominatorLog (fun i => (x i : ℂ)) (fun b => (v b : ℂ)) q ≤
      -((4 * n : ℕ) : ℝ) ^ 2 *
        V.vCrossInteraction q
          (translatedEmpiricalMeasure (fun i => (x i : ℂ)) (4 * n))
          (translatedEmpiricalMeasure (fun b => (v b : ℂ)) (4 * n)) +
        denominatorTransferCost q := by
  let X : Fin (4 * n) → ℂ := fun i => (x i : ℂ)
  let V_arr : Fin (5 * n) → ℂ := fun b => (v b : ℂ)
  have hm : 0 < 4 * n := by omega
  have hmR : (0 : ℝ) < ((4 * n : ℕ) : ℝ) := by exact_mod_cast hm
  have hx_norm : ∀ i, ‖X i‖ ≤ 1 := fun i => norm_ofReal_le_one_of_mem_Icc (hx i)
  have hv_norm : ∀ b, ‖V_arr b‖ ≤ 1 := fun b => norm_ofReal_le_one_of_mem_Icc (hv b)
  have hpair : ∀ (i : Fin (4 * n)) (b : Fin (5 * n)),
      (5 / 4 : ℝ) *
        (translatedCrossCirclePairEnergy q (X i) (V_arr b) (4 * n) -
          V.vCrossKernel q (X i) (V_arr b)) ≤
        denominatorTransferCost q * smoothingEpsilon (4 * n) := by
    intro i b
    have hcost := weighted_translatedCrossCirclePairEnergy_cost hq hn
      (X i) (V_arr b) (hx_norm i) (hv_norm b)
    have habs :
        translatedCrossCirclePairEnergy q (X i) (V_arr b) (4 * n) -
          V.vCrossKernel q (X i) (V_arr b) ≤
        |translatedCrossCirclePairEnergy q (X i) (V_arr b) (4 * n) -
          V.vCrossKernel q (X i) (V_arr b)| := le_abs_self _
    exact (mul_le_mul_of_nonneg_left habs (by norm_num)).trans hcost
  have hsum :
      (∑ i : Fin (4 * n), ∑ b : Fin (5 * n),
        (5 / 4 : ℝ) *
          (translatedCrossCirclePairEnergy q (X i) (V_arr b) (4 * n) -
            V.vCrossKernel q (X i) (V_arr b))) ≤
      ∑ _i : Fin (4 * n), ∑ _b : Fin (5 * n),
        denominatorTransferCost q * smoothingEpsilon (4 * n) := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro b _
    exact hpair i b
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hrhs :
      ((4 * n : ℕ) : ℝ) * (((5 * n : ℕ) : ℝ) *
        (denominatorTransferCost q * smoothingEpsilon (4 * n))) =
      (5 / 4 : ℝ) * denominatorTransferCost q := by
    rw [smoothingEpsilon_eq_inv_sq]
    have hnR : (n : ℝ) ≠ 0 := by
      have : 0 < n := by omega
      exact_mod_cast this.ne'
    push_cast
    field_simp [hnR]
  have hexp := vCrossInteraction_translatedEmpiricalMeasure_eq hq hn X V_arr hx_norm hv_norm
  have hexp_mul :
      (∑ i : Fin (4 * n), ∑ b : Fin (5 * n),
        translatedCrossCirclePairEnergy q (X i) (V_arr b) (4 * n)) =
      ((4 * n : ℕ) : ℝ) ^ 2 *
        V.vCrossInteraction q
          (translatedEmpiricalMeasure X (4 * n))
          (translatedEmpiricalMeasure V_arr (4 * n)) := by
    rw [hexp]
    field_simp [hmR.ne']
  have hlhs :
      (∑ i : Fin (4 * n), ∑ b : Fin (5 * n),
        (5 / 4 : ℝ) *
          (translatedCrossCirclePairEnergy q (X i) (V_arr b) (4 * n) -
            V.vCrossKernel q (X i) (V_arr b))) =
      (5 / 4 : ℝ) *
        (((4 * n : ℕ) : ℝ) ^ 2 *
          V.vCrossInteraction q
            (translatedEmpiricalMeasure X (4 * n))
            (translatedEmpiricalMeasure V_arr (4 * n)) -
          V.c5DenominatorLog X V_arr q) := by
    unfold V.c5DenominatorLog V.vCrossKernel
    simp_rw [← Finset.mul_sum, Finset.sum_sub_distrib]
    rw [hexp_mul]
  rw [hlhs, hrhs] at hsum
  linarith

/-- Difference form `m^2 * V.vCrossInteraction - V.c5DenominatorLog ≤ denominatorTransferCost q`. -/
theorem c6_denominator_smoothed_sub_le
    {q n : ℕ} (hq : 2 ≤ q) (hn : 64 ≤ 4 * n)
    (x : Fin (4 * n) → ℝ) (v : Fin (5 * n) → ℝ)
    (hx : ∀ i, x i ∈ Set.Icc (0 : ℝ) 1)
    (hv : ∀ b, v b ∈ Set.Icc (0 : ℝ) 1) :
    ((4 * n : ℕ) : ℝ) ^ 2 *
        V.vCrossInteraction q
          (translatedEmpiricalMeasure (fun i => (x i : ℂ)) (4 * n))
          (translatedEmpiricalMeasure (fun b => (v b : ℂ)) (4 * n)) -
      V.c5DenominatorLog (fun i => (x i : ℂ)) (fun b => (v b : ℂ)) q ≤
      denominatorTransferCost q := by
  have h := c6_denominator_smoothed_transfer hq hn x v hx hv
  linarith

/-- Reverse difference form `V.c5DenominatorLog - m^2 * V.vCrossInteraction ≤ denominatorTransferCost q`. -/
theorem c6_denominator_discrete_sub_smoothed_le
    {q n : ℕ} (hq : 2 ≤ q) (hn : 64 ≤ 4 * n)
    (x : Fin (4 * n) → ℝ) (v : Fin (5 * n) → ℝ)
    (hx : ∀ i, x i ∈ Set.Icc (0 : ℝ) 1)
    (hv : ∀ b, v b ∈ Set.Icc (0 : ℝ) 1) :
    V.c5DenominatorLog (fun i => (x i : ℂ)) (fun b => (v b : ℂ)) q -
      ((4 * n : ℕ) : ℝ) ^ 2 *
        V.vCrossInteraction q
          (translatedEmpiricalMeasure (fun i => (x i : ℂ)) (4 * n))
          (translatedEmpiricalMeasure (fun b => (v b : ℂ)) (4 * n)) ≤
      denominatorTransferCost q := by
  let X : Fin (4 * n) → ℂ := fun i => (x i : ℂ)
  let V_arr : Fin (5 * n) → ℂ := fun b => (v b : ℂ)
  have hm : 0 < 4 * n := by omega
  have hmR : (0 : ℝ) < ((4 * n : ℕ) : ℝ) := by exact_mod_cast hm
  have hx_norm : ∀ i, ‖X i‖ ≤ 1 := fun i => norm_ofReal_le_one_of_mem_Icc (hx i)
  have hv_norm : ∀ b, ‖V_arr b‖ ≤ 1 := fun b => norm_ofReal_le_one_of_mem_Icc (hv b)
  have hpair : ∀ (i : Fin (4 * n)) (b : Fin (5 * n)),
      (5 / 4 : ℝ) *
        (V.vCrossKernel q (X i) (V_arr b) -
          translatedCrossCirclePairEnergy q (X i) (V_arr b) (4 * n)) ≤
        denominatorTransferCost q * smoothingEpsilon (4 * n) := by
    intro i b
    have hcost := weighted_translatedCrossCirclePairEnergy_cost hq hn
      (X i) (V_arr b) (hx_norm i) (hv_norm b)
    have habs :
        V.vCrossKernel q (X i) (V_arr b) -
          translatedCrossCirclePairEnergy q (X i) (V_arr b) (4 * n) ≤
        |translatedCrossCirclePairEnergy q (X i) (V_arr b) (4 * n) -
          V.vCrossKernel q (X i) (V_arr b)| := by
      rw [abs_sub_comm]
      exact le_abs_self _
    exact (mul_le_mul_of_nonneg_left habs (by norm_num)).trans hcost
  have hsum :
      (∑ i : Fin (4 * n), ∑ b : Fin (5 * n),
        (5 / 4 : ℝ) *
          (V.vCrossKernel q (X i) (V_arr b) -
            translatedCrossCirclePairEnergy q (X i) (V_arr b) (4 * n))) ≤
      ∑ _i : Fin (4 * n), ∑ _b : Fin (5 * n),
        denominatorTransferCost q * smoothingEpsilon (4 * n) := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro b _
    exact hpair i b
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hrhs :
      ((4 * n : ℕ) : ℝ) * (((5 * n : ℕ) : ℝ) *
        (denominatorTransferCost q * smoothingEpsilon (4 * n))) =
      (5 / 4 : ℝ) * denominatorTransferCost q := by
    rw [smoothingEpsilon_eq_inv_sq]
    have hnR : (n : ℝ) ≠ 0 := by
      have : 0 < n := by omega
      exact_mod_cast this.ne'
    push_cast
    field_simp [hnR]
  have hexp := vCrossInteraction_translatedEmpiricalMeasure_eq hq hn X V_arr hx_norm hv_norm
  have hexp_mul :
      (∑ i : Fin (4 * n), ∑ b : Fin (5 * n),
        translatedCrossCirclePairEnergy q (X i) (V_arr b) (4 * n)) =
      ((4 * n : ℕ) : ℝ) ^ 2 *
        V.vCrossInteraction q
          (translatedEmpiricalMeasure X (4 * n))
          (translatedEmpiricalMeasure V_arr (4 * n)) := by
    rw [hexp]
    field_simp [hmR.ne']
  have hlhs :
      (∑ i : Fin (4 * n), ∑ b : Fin (5 * n),
        (5 / 4 : ℝ) *
          (V.vCrossKernel q (X i) (V_arr b) -
            translatedCrossCirclePairEnergy q (X i) (V_arr b) (4 * n))) =
      (5 / 4 : ℝ) *
        (V.c5DenominatorLog X V_arr q -
          ((4 * n : ℕ) : ℝ) ^ 2 *
            V.vCrossInteraction q
              (translatedEmpiricalMeasure X (4 * n))
              (translatedEmpiricalMeasure V_arr (4 * n))) := by
    unfold V.c5DenominatorLog V.vCrossKernel
    simp_rw [← Finset.mul_sum, Finset.sum_sub_distrib]
    rw [hexp_mul]
  rw [hlhs, hrhs] at hsum
  linarith

/-- Two-sided smoothed denominator transfer between `m^2 * V.vCrossInteraction`
    and `V.c5DenominatorLog` on the unit cube `[0, 1]`. -/
theorem c6_denominator_smoothed_abs_transfer
    {q n : ℕ} (hq : 2 ≤ q) (hn : 64 ≤ 4 * n)
    (x : Fin (4 * n) → ℝ) (v : Fin (5 * n) → ℝ)
    (hx : ∀ i, x i ∈ Set.Icc (0 : ℝ) 1)
    (hv : ∀ b, v b ∈ Set.Icc (0 : ℝ) 1) :
    |((4 * n : ℕ) : ℝ) ^ 2 *
        V.vCrossInteraction q
          (translatedEmpiricalMeasure (fun i => (x i : ℂ)) (4 * n))
          (translatedEmpiricalMeasure (fun b => (v b : ℂ)) (4 * n)) -
      V.c5DenominatorLog (fun i => (x i : ℂ)) (fun b => (v b : ℂ)) q| ≤
      denominatorTransferCost q := by
  have h1 := c6_denominator_smoothed_sub_le hq hn x v hx hv
  have h2 := c6_denominator_discrete_sub_smoothed_le hq hn x v hx hv
  exact abs_le.mpr ⟨by linarith, h1⟩

/-- Combined C6 mixed (`z-v`) and denominator (`x-v`) smoothed transfer under
    `hn : 64 ≤ 4 * n` (`H5-hcore/README.md` §4). -/
theorem v13_c6_mixed_and_denominator_smoothed_transfer_of_ge_64
    {q n : ℕ} (hq : SignedVBaseRange q) (hn : 64 ≤ 4 * n)
    (x : Fin (4 * n) → ℝ) (v : Fin (5 * n) → ℝ) (z : Fin (4 * n) → ℂ)
    (hx : ∀ i, x i ∈ Set.Icc (0 : ℝ) 1)
    (hv : ∀ b, v b ∈ Set.Icc (0 : ℝ) 1)
    (hzv : ∀ i b, z i ≠ (v b : ℂ)) :
    let M := v13SmoothedEmpiricalMeasures hq (by omega)
      (fun i => (x i : ℂ)) (fun b => (v b : ℂ)) z
    V.c5CrossLog z (fun b => (v b : ℂ)) -
      V.c5DenominatorLog (fun i => (x i : ℂ)) (fun b => (v b : ℂ)) q ≤
      ((4 * n : ℕ) : ℝ) ^ 2 *
        (V.vLogInteraction M.μv M.μz -
          V.vCrossInteraction q M.μx M.μv) +
        denominatorTransferCost q := by
  dsimp only [v13SmoothedEmpiricalMeasures]
  have hcross := c6_cross_smoothed_transfer (by omega : 0 < n) v z hzv
  have hden := c6_denominator_smoothed_transfer hq.1 hn x v hx hv
  linarith

/-- Combined C6 mixed (`z-v`) and denominator (`x-v`) smoothed transfer under
    `hn : 16 ≤ n` (the proof plan). -/
theorem v13_c6_mixed_and_denominator_smoothed_transfer
    {q n : ℕ} (hq : SignedVBaseRange q) (hn : 16 ≤ n)
    (x : Fin (4 * n) → ℝ) (v : Fin (5 * n) → ℝ) (z : Fin (4 * n) → ℂ)
    (hx : ∀ i, x i ∈ Set.Icc (0 : ℝ) 1)
    (hv : ∀ b, v b ∈ Set.Icc (0 : ℝ) 1)
    (hzv : ∀ i b, z i ≠ (v b : ℂ)) :
    let M := v13SmoothedEmpiricalMeasures hq (by omega)
      (fun i => (x i : ℂ)) (fun b => (v b : ℂ)) z
    V.c5CrossLog z (fun b => (v b : ℂ)) -
      V.c5DenominatorLog (fun i => (x i : ℂ)) (fun b => (v b : ℂ)) q ≤
      ((4 * n : ℕ) : ℝ) ^ 2 *
        (V.vLogInteraction M.μv M.μz -
          V.vCrossInteraction q M.μx M.μv) +
        denominatorTransferCost q :=
  v13_c6_mixed_and_denominator_smoothed_transfer_of_ge_64 hq (by omega) x v z hx hv hzv

end

end Li2Lean.B3
