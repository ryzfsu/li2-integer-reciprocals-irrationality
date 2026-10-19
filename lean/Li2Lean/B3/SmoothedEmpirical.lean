/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/

import Mathlib
import Li2Lean.B3.SignedSmoothing
import Li2Lean.P0.TubeCircleMeasure

/-!
# Smoothed empirical measures for the signed V construction

The definitions here instantiate the v13 translated circles
`u + 2 i epsilon`, `epsilon = m⁻²` from
`source/chapters/v-analytic.tex:532-549` as probability and empirical
measures.  The circle and empirical-measure APIs are reused from the frozen
Li2(1/2) implementation (`P0/TubeCircleMeasure.lean`); the signed V energy
and its `log |q+uv|` interaction are not imported from P0.

Only measure mass, finite-measure instances, and absolute logarithmic-kernel
integrability are proved here.  The v13 reference measures on the line and
arc, the signed three-component energy, and the determinant bridge remain
separate obligations.
-/

namespace Li2Lean

noncomputable section

namespace B3

open MeasureTheory Set Filter
open scoped ENNReal

open Li2Lean.P0

/-! ## Translated circles and empirical measures -/

/-- One v13 translated probability circle, `v-analytic.tex:532-536`. -/
def translatedCircleMeasure (u : ℂ) (m : ℕ) : Measure ℂ :=
  circleProbability (translatedAtomCenter u m) (smoothingEpsilon m)

instance translatedCircleMeasure_probability (u : ℂ) (m : ℕ) :
    IsProbabilityMeasure (translatedCircleMeasure u m) := by
  unfold translatedCircleMeasure
  infer_instance

theorem translatedCircleMeasure_mass (u : ℂ) (m : ℕ) :
    (translatedCircleMeasure u m).real Set.univ = 1 := by
  simp [translatedCircleMeasure, Measure.real_def]

/--
The v13 empirical smoothing of a finite list of atoms.  The denominator is
the paper's `m`; the list length may be `m`, `5m/4`, or another finite block
size, so its mass is tracked explicitly below.
-/
def translatedEmpiricalMeasure {d : ℕ} (u : Fin d → ℂ) (m : ℕ) : Measure ℂ :=
  circleEmpiricalMeasure
    (fun i : Fin d => translatedAtomCenter (u i) m)
    (smoothingEpsilon m) m

instance translatedEmpiricalMeasure_finite {d : ℕ} (u : Fin d → ℂ) (m : ℕ) :
    IsFiniteMeasure (translatedEmpiricalMeasure u m) := by
  unfold translatedEmpiricalMeasure
  infer_instance

theorem translatedCircleMeasure_radius_pos {u : ℂ} {m : ℕ} (hm : 0 < m) :
    0 < smoothingEpsilon m :=
  smoothingEpsilon_pos hm

/-- The empirical mass is exactly `d/m`, by the reused v6 measure lemma. -/
theorem translatedEmpiricalMeasure_mass {d : ℕ} (u : Fin d → ℂ) (m : ℕ) :
    (translatedEmpiricalMeasure u m).real Set.univ =
      (d : ℝ) / (m : ℝ) := by
  unfold translatedEmpiricalMeasure
  exact circleEmpiricalMeasure_mass _ _ _

/-! ## v13 block mass specializations -/

/-- A block with `d=m` has the unit mass used by the `x` and `z` measures. -/
theorem translatedEmpiricalMeasure_mass_eq_one {m : ℕ} (hm : 0 < m)
    (u : Fin m → ℂ) :
    (translatedEmpiricalMeasure u m).real Set.univ = 1 := by
  rw [translatedEmpiricalMeasure_mass]
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  field_simp

/-- For `m=4n`, a `5n` block has the v13 mass `5/4` used by `v`. -/
theorem translatedEmpiricalMeasure_mass_five_four {n : ℕ} (hn : 0 < n)
    (u : Fin (5 * n) → ℂ) :
    (translatedEmpiricalMeasure u (4 * n)).real Set.univ = (5 / 4 : ℝ) := by
  rw [translatedEmpiricalMeasure_mass]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  push_cast
  field_simp

/-! ## Log-kernel integrability for smoothed blocks -/

/-- Self-energy integrability of one translated empirical block. -/
theorem translatedEmpiricalMeasure_log_integrable {d : ℕ}
    (u : Fin d → ℂ) {m : ℕ} (hm : 0 < m) :
    Integrable (fun p : ℂ × ℂ => realLogKernel p.1 p.2)
      ((translatedEmpiricalMeasure u m).prod (translatedEmpiricalMeasure u m)) := by
  unfold translatedEmpiricalMeasure
  exact integrable_realLogKernel_circleEmpiricalMeasure_prod _
    (smoothingEpsilon_pos hm) m

/-- Cross-energy integrability for two translated empirical blocks with the
same smoothing denominator. -/
theorem translatedEmpiricalMeasure_log_cross_integrable
    {d e : ℕ} (u : Fin d → ℂ) (v : Fin e → ℂ) {m : ℕ} (hm : 0 < m) :
    Integrable (fun p : ℂ × ℂ => realLogKernel p.1 p.2)
      ((translatedEmpiricalMeasure u m).prod (translatedEmpiricalMeasure v m)) := by
  unfold translatedEmpiricalMeasure circleEmpiricalMeasure
  simp only [Measure.prod_smul_left, Measure.prod_smul_right]
  apply Integrable.smul_measure _ ENNReal.ofReal_ne_top
  apply Integrable.smul_measure _ ENNReal.ofReal_ne_top
  rw [Measure.prod_sum, Measure.sum_fintype]
  apply integrable_finsetSum_measure.mpr
  intro ij hij
  exact integrable_realLogKernel_circleProbability_prod
    (translatedAtomCenter (u ij.1) m)
    (translatedAtomCenter (v ij.2) m)
    (smoothingEpsilon_pos hm)

/-- Exact cross-energy expansion for two translated empirical blocks. -/
theorem translatedEmpiricalMeasure_cross_energy_eq
    {d e : ℕ} (u : Fin d → ℂ) (v : Fin e → ℂ)
    {m : ℕ} (hm : 0 < m) :
    (∫ p : ℂ × ℂ, realLogKernel p.1 p.2
      ∂((translatedEmpiricalMeasure u m).prod
        (translatedEmpiricalMeasure v m))) =
      (∑ i : Fin d, ∑ j : Fin e,
        circlePairEnergy (translatedAtomCenter (u i) m)
          (translatedAtomCenter (v j) m) (smoothingEpsilon m)) /
        (m : ℝ) ^ 2 := by
  unfold translatedEmpiricalMeasure
  exact circleEmpiricalMeasure_cross_energy_eq
    (fun i : Fin d => translatedAtomCenter (u i) m)
    (fun j : Fin e => translatedAtomCenter (v j) m)
    (smoothingEpsilon_pos hm) m

theorem translatedEmpiricalMeasure_nullSingleton {d : ℕ}
    (u : Fin d → ℂ) {m : ℕ} (hm : 0 < m) :
    NullSingletonClass (translatedEmpiricalMeasure u m) := by
  unfold translatedEmpiricalMeasure
  exact circleEmpiricalMeasure_nullSingleton _ (smoothingEpsilon_pos hm) m

end B3

end

end Li2Lean

#print axioms Li2Lean.B3.translatedEmpiricalMeasure_mass
#print axioms Li2Lean.B3.translatedEmpiricalMeasure_log_cross_integrable
