/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.EnvMainQ
import Li2Lean.P0.ActualReferenceDual
import Li2Lean.P0.ContourEnergyLowerBound
import Mathlib

open MeasureTheory

namespace Li2Lean.AllNAssembly

noncomputable section

/-! The actual shifted P0 variational profile used by the positive-base route.
This module is kept below `ProducerAssembly` so the tube transfer can consume
the profile without creating an import cycle.  The construction is the affine
shift in v13 `paper-v13/p0-analytic.tex:108-114`. -/

def p0PositiveEnergyDomain (M : P0.P0AdmissibleMeasures) : Prop :=
  P0.P0FiniteEnergyCondition M ∧
    MeasureTheory.Integrable (fun z : ℂ => z.re) M.eta

noncomputable def p0PositiveEnergyValue (lambda : ℝ)
    (M : P0.P0AdmissibleMeasures) : ℝ :=
  P0.p0RegularizedEnergyValue M + lambda *
    ((∫ t : ℝ, t ∂M.mu) - ∫ z : ℂ, z.re ∂M.eta)

theorem p0PositiveEnergyDomain_actualReference :
    p0PositiveEnergyDomain P0.actualReferenceMeasures := by
  have hfin₀ : P0.P0FiniteEnergyCondition P0.actualReferenceMeasures :=
    P0.p0ReferenceMeasures_finite_energy
      P0.p0ReferenceFiniteEnergyData_literal
  have hRe : MeasureTheory.Integrable (fun z : ℂ => z.re)
      P0.actualReferenceMeasures.eta := by
    apply MeasureTheory.Integrable.mono' (MeasureTheory.integrable_const (4 : ℝ))
      Complex.continuous_re.aestronglyMeasurable
    filter_upwards [P0.EnergyLowerBound.eta_ae_norm_le
      P0.actualReferenceMeasures] with z hz
    simpa [Real.norm_eq_abs] using
      (Complex.abs_re_le_norm z).trans hz
  exact ⟨hfin₀, hRe⟩

def p0PositiveEnergyValues (lambda : ℝ) : Set ℝ :=
  {e | ∃ M : P0.P0AdmissibleMeasures,
    p0PositiveEnergyDomain M ∧ e = p0PositiveEnergyValue lambda M}

theorem p0PositiveEnergyValues_nonempty (lambda : ℝ) :
    (p0PositiveEnergyValues lambda).Nonempty := by
  refine ⟨p0PositiveEnergyValue lambda P0.actualReferenceMeasures, ?_⟩
  exact ⟨P0.actualReferenceMeasures, p0PositiveEnergyDomain_actualReference, rfl⟩

/-! Every admissible shift has slope bounded below by `-4`; the support
information is the literal P0 support ledger reused from v13. -/
theorem p0PositiveEnergySlope_ge (M : P0.P0AdmissibleMeasures)
    (hM : p0PositiveEnergyDomain M) :
    (-4 : ℝ) ≤
      (∫ t : ℝ, t ∂M.mu) - ∫ z : ℂ, z.re ∂M.eta := by
  have hmu : MeasureTheory.Integrable (fun t : ℝ => t) M.mu := hM.1.1
  have heta : MeasureTheory.Integrable (fun z : ℂ => z.re) M.eta := hM.2
  have hneg_integrable : MeasureTheory.Integrable (fun z : ℂ => -z.re) M.eta := by
    simpa using heta.neg
  have hmu_ge : (0 : ℝ) ≤ ∫ t : ℝ, t ∂M.mu := by
    have h := P0.EnergyLowerBound.integral_ge_of_ae M.mu hmu
      ((P0.EnergyLowerBound.mu_ae_mem M).mono fun t ht => by
        exact le_trans (by norm_num : (0 : ℝ) ≤ 1 / 2) ht)
    simpa using h
  have heta_le : (∫ z : ℂ, z.re ∂M.eta) ≤ (4 : ℝ) := by
    have hneg := P0.EnergyLowerBound.integral_ge_of_ae M.eta hneg_integrable
      ((P0.EnergyLowerBound.eta_ae_norm_le M).mono fun z hz => by
        have hzre : z.re ≤ 4 := (Complex.re_le_norm z).trans hz
        change (-4 : ℝ) ≤ -z.re
        linarith)
    have hneg' : (-4 : ℝ) ≤ -(∫ z : ℂ, z.re ∂M.eta) := by
      simpa only [integral_neg] using hneg
    linarith
  linarith

theorem p0PositiveEnergyValue_ge (lambda : ℝ) (hlambda : 0 ≤ lambda)
    (M : P0.P0AdmissibleMeasures) (hM : p0PositiveEnergyDomain M) :
    (-200 : ℝ) - 4 * lambda ≤ p0PositiveEnergyValue lambda M := by
  have henergy := P0.EnergyLowerBound.p0RegularizedEnergyValue_ge M hM.1
  have hslope := p0PositiveEnergySlope_ge M hM
  have hmul := mul_le_mul_of_nonneg_left hslope hlambda
  unfold p0PositiveEnergyValue
  linarith

theorem p0PositiveEnergyValues_bddBelow (lambda : ℝ) (hlambda : 0 ≤ lambda) :
    BddBelow (p0PositiveEnergyValues lambda) := by
  refine ⟨(-200 : ℝ) - 4 * lambda, ?_⟩
  rintro e ⟨M, hM, rfl⟩
  exact p0PositiveEnergyValue_ge lambda hlambda M hM

/-! The v13 variational value at logarithmic base shift `lambda`. -/
noncomputable def p0PositiveEnergyProfileActual (lambda : ℝ) : ℝ :=
  sInf (p0PositiveEnergyValues lambda)

theorem p0PositiveEnergyProfileActual_ge (lambda : ℝ) (hlambda : 0 ≤ lambda) :
    (-200 : ℝ) - 4 * lambda ≤ p0PositiveEnergyProfileActual lambda := by
  unfold p0PositiveEnergyProfileActual
  refine le_csInf (p0PositiveEnergyValues_nonempty lambda) ?_
  rintro e ⟨M, hM, rfl⟩
  exact p0PositiveEnergyValue_ge lambda hlambda M hM

end
end Li2Lean.AllNAssembly
