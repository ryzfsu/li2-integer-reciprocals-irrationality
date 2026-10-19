/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/

import Mathlib
import Li2Lean.V.SignedEnergy
import Li2Lean.V.VFamily
import Li2Lean.B3.SmoothedEmpirical
import Li2Lean.B3.SignedSmoothing

/-!
# Measure-level obligations for the signed V argument

This module records the literal unit-interval source and the translated-circle
measures used in `v-analytic.tex:238-301,532-558`.  The generic L6 theorem is
reused only after all finite-mass, atomlessness, and product-integrability
hypotheses have been put in the ledger.  The six printed reference tables are
not instantiated here: this file supplies interfaces for those later rows.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Li2Lean.V

noncomputable section

/-! ## The actual real support and its complex pushforward -/

/-- The raw real support in the v13 reference tables. -/
def v13RealBaseSupport : Set ℝ := Set.Ioc (0 : ℝ) 1

/-- The parameter measure on the literal support `[0,1]`. -/
def v13UnitIntervalParam : Measure ℝ :=
  volume.restrict v13RealBaseSupport

/-- The same base measure viewed on the real axis in `ℂ`. -/
def v13UnitIntervalMeasure : Measure ℂ :=
  Measure.map Complex.ofReal v13UnitIntervalParam

instance v13UnitIntervalParam_finite : IsFiniteMeasure v13UnitIntervalParam := by
  unfold v13UnitIntervalParam v13RealBaseSupport
  infer_instance

instance v13UnitIntervalMeasure_finite : IsFiniteMeasure v13UnitIntervalMeasure := by
  unfold v13UnitIntervalMeasure
  infer_instance

theorem v13UnitIntervalParam_mass :
    v13UnitIntervalParam.real Set.univ = 1 := by
  simp [v13UnitIntervalParam, v13RealBaseSupport, Measure.real_def]

theorem v13UnitIntervalMeasure_mass :
    v13UnitIntervalMeasure.real Set.univ = 1 := by
  unfold v13UnitIntervalMeasure
  rw [map_measureReal_apply Complex.measurable_ofReal MeasurableSet.univ]
  simpa using v13UnitIntervalParam_mass

theorem v13UnitIntervalMeasure_finite_mass :
    v13UnitIntervalMeasure Set.univ ≠ ⊤ := by
  exact measure_ne_top v13UnitIntervalMeasure Set.univ

theorem v13UnitIntervalParam_nullSingleton (x : ℝ) :
    v13UnitIntervalParam {x} = 0 := by
  unfold v13UnitIntervalParam
  rw [Measure.restrict_apply (measurableSet_singleton x)]
  exact measure_mono_null inter_subset_left (measure_singleton x)

theorem v13UnitIntervalMeasure_nullSingleton (z : ℂ) :
    v13UnitIntervalMeasure {z} = 0 := by
  unfold v13UnitIntervalMeasure
  rw [Measure.map_apply Complex.measurable_ofReal (measurableSet_singleton z)]
  by_cases hz : z.im = 0
  · have hzre : z = Complex.ofReal z.re := by
      apply Complex.ext <;> simp [hz]
    have hpre : Complex.ofReal ⁻¹' ({z} : Set ℂ) = {z.re} := by
      ext x
      constructor
      · intro hx
        have hr := congrArg Complex.re hx
        simpa using hr
      · intro hx
        rw [hzre]
        simpa using hx
    rw [hpre, v13UnitIntervalParam_nullSingleton]
  · have hpre : Complex.ofReal ⁻¹' ({z} : Set ℂ) = (∅ : Set ℝ) := by
      ext x
      constructor
      · intro hx
        have hi := congrArg Complex.im hx
        exact (hz hi.symm).elim
      · intro hx
        exact hx.elim
    rw [hpre, measure_empty]

instance v13UnitIntervalMeasure_atomless :
    NullSingletonClass v13UnitIntervalMeasure :=
  ⟨v13UnitIntervalMeasure_nullSingleton⟩

theorem v13UnitIntervalMeasure_prod_map :
    v13UnitIntervalMeasure.prod v13UnitIntervalMeasure =
      Measure.map (Prod.map Complex.ofReal Complex.ofReal)
        (v13UnitIntervalParam.prod v13UnitIntervalParam) := by
  unfold v13UnitIntervalMeasure
  rw [Measure.map_prod_map _ _ Complex.measurable_ofReal Complex.measurable_ofReal]

theorem v13UnitIntervalMeasure_ae_ne_zero :
    ∀ᵐ z ∂v13UnitIntervalMeasure, z ≠ 0 := by
  exact Measure.ae_ne v13UnitIntervalMeasure 0

/-! ## Translated-circle wrappers and the integrability ledger -/

/-- A real atom after the v13 translation `t + 2 i epsilon`. -/
def v13SmoothedCenter (t : ℝ) (m : ℕ) : ℂ :=
  B3.translatedAtomCenter (Complex.ofReal t) m

/-- The probability measure on the translated smoothing circle. -/
def v13SmoothedCircleMeasure (t : ℝ) (m : ℕ) : Measure ℂ :=
  B3.translatedCircleMeasure (Complex.ofReal t) m

/-- The normalized finite empirical smoothing of a real finite block. -/
def v13SmoothedRealEmpirical {d : ℕ} (t : Fin d → ℝ) (m : ℕ) : Measure ℂ :=
  B3.translatedEmpiricalMeasure (fun i => Complex.ofReal (t i)) m

instance v13SmoothedRealEmpirical_finite {d : ℕ} (t : Fin d → ℝ) (m : ℕ) :
    IsFiniteMeasure (v13SmoothedRealEmpirical t m) := by
  unfold v13SmoothedRealEmpirical
  infer_instance

theorem v13SmoothedRealEmpirical_mass {d : ℕ} (t : Fin d → ℝ) (m : ℕ) :
    (v13SmoothedRealEmpirical t m).real Set.univ = (d : ℝ) / (m : ℝ) := by
  unfold v13SmoothedRealEmpirical
  exact B3.translatedEmpiricalMeasure_mass _ _

theorem v13SmoothedCircleMeasure_mass (t : ℝ) (m : ℕ) :
    (v13SmoothedCircleMeasure t m).real Set.univ = 1 := by
  unfold v13SmoothedCircleMeasure
  exact B3.translatedCircleMeasure_mass _ _

theorem v13SmoothedCircleMeasure_atomless {t : ℝ} {m : ℕ} (hm : 0 < m) :
    ∀ z : ℂ, v13SmoothedCircleMeasure t m {z} = 0 := by
  intro z
  unfold v13SmoothedCircleMeasure
  exact (P0.circleProbability_nullSingleton _ (B3.smoothingEpsilon_pos hm)).measure_singleton z

theorem v13SmoothedRealEmpirical_mass_eq_one {m : ℕ} (hm : 0 < m)
    (t : Fin m → ℝ) :
    (v13SmoothedRealEmpirical t m).real Set.univ = 1 := by
  unfold v13SmoothedRealEmpirical
  exact B3.translatedEmpiricalMeasure_mass_eq_one hm (fun i => Complex.ofReal (t i))

theorem v13SmoothedRealEmpirical_mass_five_four {n : ℕ} (hn : 0 < n)
    (t : Fin (5 * n) → ℝ) :
    (v13SmoothedRealEmpirical t (4 * n)).real Set.univ = (5 / 4 : ℝ) := by
  unfold v13SmoothedRealEmpirical
  exact B3.translatedEmpiricalMeasure_mass_five_four hn
    (fun i => Complex.ofReal (t i))

theorem v13SmoothedRealEmpirical_atomless {d : ℕ} (t : Fin d → ℝ)
    {m : ℕ} (hm : 0 < m) :
    ∀ z : ℂ, v13SmoothedRealEmpirical t m {z} = 0 := by
  intro z
  unfold v13SmoothedRealEmpirical
  letI : NullSingletonClass
      (B3.translatedEmpiricalMeasure (fun i : Fin d => Complex.ofReal (t i)) m) :=
    B3.translatedEmpiricalMeasure_nullSingleton
      (fun i : Fin d => Complex.ofReal (t i)) hm
  exact (inferInstance : NullSingletonClass
    (B3.translatedEmpiricalMeasure (fun i : Fin d => Complex.ofReal (t i)) m)).measure_singleton z

theorem v13SmoothedRealEmpirical_prod_diagonal_null {d e : ℕ}
    (t : Fin d → ℝ) (s : Fin e → ℝ) {m : ℕ} (hm : 0 < m) :
    ((v13SmoothedRealEmpirical t m).prod
      (v13SmoothedRealEmpirical s m)) (Set.diagonal ℂ) = 0 := by
  exact P0.L6Variations.prod_diagonal_null_of_right_atomless _ _
    (v13SmoothedRealEmpirical_atomless s hm)

/-! ## Pushforward bookkeeping for `R_q(v)=-q/v` -/

theorem v13Reflection_measurable (q : ℕ) :
    Measurable (vReflection q) := by
  unfold vReflection
  refine Measurable.ite (measurableSet_eq_fun measurable_id measurable_const)
    measurable_const ?_
  fun_prop

theorem v13Reflection_map_prod_map_right (q : ℕ)
    (μ ν : Measure ℂ) [SFinite ν] :
    μ.prod (Measure.map (vReflection q) ν) =
      Measure.map (Prod.map id (vReflection q)) (μ.prod ν) := by
  simpa only [Measure.map_id] using
    (Measure.map_prod_map μ ν measurable_id (v13Reflection_measurable q))

theorem v13Reflection_map_prod_map_left (q : ℕ)
    (μ ν : Measure ℂ) [SFinite μ] [SFinite ν] :
    (Measure.map (vReflection q) μ).prod ν =
      Measure.map (Prod.map (vReflection q) id) (μ.prod ν) := by
  simpa only [Measure.map_id] using
    (Measure.map_prod_map μ ν (v13Reflection_measurable q) measurable_id)

theorem v13Reflection_mass_preserving
    {q : ℕ} (c : VReflectionCertificate q)
    (μ : Measure ℂ) (hμ : μ Set.univ ≠ ⊤) :
    (Measure.map (vReflection q) μ) Set.univ = μ Set.univ := by
  exact c.mass_preserving μ hμ

theorem v13Reflection_distance_ae
    {q : ℕ} (hq : 0 < q) (μ : Measure ℂ) [SFinite μ]
    (hcollision : ∀ᵐ p : ℂ × ℂ ∂(μ.prod μ),
      p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ p.1 ≠ p.2) :
    (fun p : ℂ × ℂ =>
      Real.log ‖vReflection q p.1 - vReflection q p.2‖) =ᵐ[μ.prod μ]
      (fun p => Real.log (q : ℝ) + Real.log ‖p.1 - p.2‖ -
        Real.log ‖p.1‖ - Real.log ‖p.2‖) := by
  filter_upwards [hcollision] with p hp
  exact vReflection_log_distance q hq hp.1 hp.2.1 hp.2.2

theorem v13SmoothedRealEmpirical_log_integrable {d : ℕ}
    (t : Fin d → ℝ) {m : ℕ} (hm : 0 < m) :
    Integrable (fun p : ℂ × ℂ => li2LogKernel p.1 p.2)
      ((v13SmoothedRealEmpirical t m).prod (v13SmoothedRealEmpirical t m)) := by
  unfold v13SmoothedRealEmpirical
  simpa [li2LogKernel, P0.realLogKernel] using
    (B3.translatedEmpiricalMeasure_log_integrable
      (fun i : Fin d => Complex.ofReal (t i)) hm)

theorem v13SmoothedRealEmpirical_log_cross_integrable {d e : ℕ}
    (t : Fin d → ℝ) (s : Fin e → ℝ) {m : ℕ} (hm : 0 < m) :
    Integrable (fun p : ℂ × ℂ => li2LogKernel p.1 p.2)
      ((v13SmoothedRealEmpirical t m).prod (v13SmoothedRealEmpirical s m)) := by
  unfold v13SmoothedRealEmpirical
  simpa [li2LogKernel, P0.realLogKernel] using
    (B3.translatedEmpiricalMeasure_log_cross_integrable
      (fun i : Fin d => Complex.ofReal (t i))
      (fun i : Fin e => Complex.ofReal (s i)) hm)

/-! ## A generic, explicit L6 certificate constructor -/

def l6PairCertificate_of_data (μ ν : Measure ℂ)
    (hμfinite : μ Set.univ ≠ ⊤) (hνfinite : ν Set.univ ≠ ⊤)
    (hmass : μ Set.univ = ν Set.univ)
    (hμatomless : ∀ z : ℂ, μ {z} = 0)
    (hνatomless : ∀ z : ℂ, ν {z} = 0)
    (hμμ : Integrable (fun p : ℂ × ℂ => li2LogKernel p.1 p.2) (μ.prod μ))
    (hνν : Integrable (fun p : ℂ × ℂ => li2LogKernel p.1 p.2) (ν.prod ν))
    (hμν : Integrable (fun p : ℂ × ℂ => li2LogKernel p.1 p.2) (μ.prod ν)) :
    L6PairCertificate :=
  { left := μ
    right := ν
    left_finite := hμfinite
    right_finite := hνfinite
    equal_mass := hmass
    left_atomless := hμatomless
    right_atomless := hνatomless
    int_ll := hμμ
    int_rr := hνν
    int_lr := hμν }

def l6PairCertificate_of_smoothed_real_blocks {d : ℕ}
    (t s : Fin d → ℝ) {m : ℕ} (hm : 0 < m) :
    L6PairCertificate := by
  refine l6PairCertificate_of_data
    (v13SmoothedRealEmpirical t m) (v13SmoothedRealEmpirical s m) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact measure_ne_top _ _
  · exact measure_ne_top _ _
  · have ht := v13SmoothedRealEmpirical_mass t m
    have hs := v13SmoothedRealEmpirical_mass s m
    apply (measureReal_eq_measureReal_iff
      (μ := v13SmoothedRealEmpirical t m)
      (ν := v13SmoothedRealEmpirical s m)).mp
    simpa [ht, hs]
  · exact v13SmoothedRealEmpirical_atomless t hm
  · exact v13SmoothedRealEmpirical_atomless s hm
  · exact v13SmoothedRealEmpirical_log_integrable t hm
  · exact v13SmoothedRealEmpirical_log_integrable s hm
  · exact v13SmoothedRealEmpirical_log_cross_integrable t s hm

/-! ## Support bounds and the denominator kernel -/

theorem v13SmoothedCircle_norm_ae_le {t : ℝ} {m : ℕ} (hm : 0 < m)
    (ht : |t| ≤ 1) :
    ∀ᵐ z ∂(v13SmoothedCircleMeasure t m),
      ‖z‖ ≤ 1 + 3 * B3.smoothingEpsilon m := by
  have hu : ‖(Complex.ofReal t : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact ht
  have hr : 0 < B3.smoothingEpsilon m := B3.smoothingEpsilon_pos hm
  have hr_nonneg : 0 ≤ B3.smoothingEpsilon m := hr.le
  have hcenter : ‖B3.translatedAtomCenter (Complex.ofReal t) m‖ ≤
      1 + 2 * B3.smoothingEpsilon m := by
    unfold B3.translatedAtomCenter
    calc
      ‖(Complex.ofReal t : ℂ) +
          Complex.ofReal (2 * B3.smoothingEpsilon m) * Complex.I‖ ≤
          ‖(Complex.ofReal t : ℂ)‖ +
            ‖Complex.ofReal (2 * B3.smoothingEpsilon m) * Complex.I‖ := norm_add_le _ _
      _ = ‖(Complex.ofReal t : ℂ)‖ + 2 * B3.smoothingEpsilon m := by
        have h2 : 0 ≤ (2 : ℝ) * B3.smoothingEpsilon m := by positivity
        have hnorm : ‖(Complex.ofReal (2 * B3.smoothingEpsilon m) : ℂ)‖ =
            2 * B3.smoothingEpsilon m := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h2]
        rw [norm_mul, hnorm]
        simp
      _ ≤ 1 + 2 * B3.smoothingEpsilon m := by linarith
  have hmem : ∀ᵐ z ∂(v13SmoothedCircleMeasure t m),
      z ∈ Metric.sphere (B3.translatedAtomCenter (Complex.ofReal t) m)
        (B3.smoothingEpsilon m) := by
    unfold v13SmoothedCircleMeasure B3.translatedCircleMeasure
    have h := P0.circleProbability_outside_sphere
      (B3.translatedAtomCenter (Complex.ofReal t) m) hr
    rw [ae_iff]
    change (P0.circleProbability
      (B3.translatedAtomCenter (Complex.ofReal t) m)
      (B3.smoothingEpsilon m))
      (Metric.sphere (B3.translatedAtomCenter (Complex.ofReal t) m)
        (B3.smoothingEpsilon m))ᶜ = 0
    exact h
  filter_upwards [hmem] with z hz
  have hdist : dist z (B3.translatedAtomCenter (Complex.ofReal t) m) =
      B3.smoothingEpsilon m := by
    simpa only [Metric.mem_sphere] using hz
  have hnorm : ‖z - B3.translatedAtomCenter (Complex.ofReal t) m‖ =
      B3.smoothingEpsilon m := by
    simpa only [dist_eq_norm] using hdist
  calc
    ‖z‖ = ‖(z - B3.translatedAtomCenter (Complex.ofReal t) m) +
        B3.translatedAtomCenter (Complex.ofReal t) m‖ := by congr 1 <;> ring
    _ ≤ ‖z - B3.translatedAtomCenter (Complex.ofReal t) m‖ +
        ‖B3.translatedAtomCenter (Complex.ofReal t) m‖ := norm_add_le _ _
    _ ≤ 1 + 3 * B3.smoothingEpsilon m := by linarith

theorem v13SmoothedRealEmpirical_norm_ae_le {d : ℕ}
    (t : Fin d → ℝ) {m : ℕ} (hm : 0 < m)
    (ht : ∀ i, |t i| ≤ 1) :
    ∀ᵐ z ∂(v13SmoothedRealEmpirical t m),
      ‖z‖ ≤ 1 + 3 * B3.smoothingEpsilon m := by
  let E : Set ℂ := {z | ¬ ‖z‖ ≤ 1 + 3 * B3.smoothingEpsilon m}
  have hE : MeasurableSet E := by
    dsimp [E]
    simpa only [not_le] using
      (measurableSet_lt measurable_const measurable_norm)
  have hzero (i : Fin d) :
      P0.circleProbability (B3.translatedAtomCenter (Complex.ofReal (t i)) m)
        (B3.smoothingEpsilon m) E = 0 := by
    have hi := v13SmoothedCircle_norm_ae_le (t := t i) hm (ht i)
    rw [ae_iff] at hi
    change (P0.circleProbability
      (B3.translatedAtomCenter (Complex.ofReal (t i)) m)
      (B3.smoothingEpsilon m)) E = 0
    exact hi
  have hzero' : v13SmoothedRealEmpirical t m E = 0 := by
    unfold v13SmoothedRealEmpirical B3.translatedEmpiricalMeasure P0.circleEmpiricalMeasure
    rw [Measure.smul_apply, Measure.sum_apply _ hE]
    simp only [hzero, tsum_zero, smul_zero]
  rw [ae_iff]
  exact hzero'

theorem v13SmoothedRealEmpirical_norm_ae_le_one_add_three_div_4096
    {d : ℕ} (t : Fin d → ℝ) {m : ℕ} (hm : 64 ≤ m)
    (ht : ∀ i, |t i| ≤ 1) :
    ∀ᵐ z ∂(v13SmoothedRealEmpirical t m),
      ‖z‖ ≤ 1 + (3 / 4096 : ℝ) := by
  have h := v13SmoothedRealEmpirical_norm_ae_le t (by omega : 0 < m) ht
  filter_upwards [h] with z hz
  have heps := B3.smoothingEpsilon_le_one_div_4096 hm
  nlinarith

/-- The literal v13 denominator kernel on a product space. -/
noncomputable def v13DenominatorKernel (q : ℕ) (p : ℂ × ℂ) : ℝ :=
  Real.log ‖(q : ℂ) + p.1 * p.2‖

def v13DenominatorTubeRadius : ℝ := 1 + 3 / 4096

theorem measurable_v13DenominatorKernel (q : ℕ) :
    Measurable (v13DenominatorKernel q) := by
  unfold v13DenominatorKernel
  fun_prop

theorem v13DenominatorKernel_norm_lower {q : ℕ} (hq : 2 ≤ q)
    {p : ℂ × ℂ}
    (h1 : ‖p.1‖ ≤ v13DenominatorTubeRadius)
    (h2 : ‖p.2‖ ≤ v13DenominatorTubeRadius) :
    (q : ℝ) - v13DenominatorTubeRadius ^ 2 ≤
      ‖(q : ℂ) + p.1 * p.2‖ := by
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hqnorm : ‖(q : ℂ)‖ = (q : ℝ) := by norm_cast
  have hprod : ‖p.1 * p.2‖ ≤ v13DenominatorTubeRadius ^ 2 := by
    have hradius : 0 ≤ v13DenominatorTubeRadius := by
      norm_num [v13DenominatorTubeRadius]
    calc
      ‖p.1 * p.2‖ ≤ ‖p.1‖ * ‖p.2‖ := norm_mul_le _ _
      _ ≤ v13DenominatorTubeRadius * v13DenominatorTubeRadius := by gcongr
      _ = v13DenominatorTubeRadius ^ 2 := by ring
  have htri : ‖(q : ℂ)‖ ≤
      ‖(q : ℂ) + p.1 * p.2‖ + ‖p.1 * p.2‖ := by
    calc
      ‖(q : ℂ)‖ = ‖((q : ℂ) + p.1 * p.2) - p.1 * p.2‖ := by congr 1 <;> ring
      _ ≤ ‖(q : ℂ) + p.1 * p.2‖ + ‖p.1 * p.2‖ := norm_sub_le _ _
  rw [hqnorm] at htri
  linarith

theorem v13_denominatorKernel_integrable
    {q : ℕ} (hq : 2 ≤ q) (μ ν : Measure ℂ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {C : ℝ} (hμ : ∀ᵐ z ∂μ, ‖z‖ ≤ C)
    (hν : ∀ᵐ z ∂ν, ‖z‖ ≤ C)
    (hC : 0 ≤ C) (hCq : C ^ 2 < (q : ℝ)) :
    Integrable (v13DenominatorKernel q) (μ.prod ν) := by
  have hlow : 0 < (q : ℝ) - C ^ 2 := by linarith
  have hbound : ∀ᵐ p : ℂ × ℂ ∂(μ.prod ν),
      ‖v13DenominatorKernel q p‖ ≤
        max |Real.log ((q : ℝ) + C ^ 2)|
          |Real.log ((q : ℝ) - C ^ 2)| := by
    filter_upwards [
      (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae hμ,
      (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae hν] with p hp hq'
    have hprod : ‖p.1 * p.2‖ ≤ C ^ 2 := by
      calc
        ‖p.1 * p.2‖ ≤ ‖p.1‖ * ‖p.2‖ := norm_mul_le _ _
        _ ≤ C * C := by gcongr
        _ = C ^ 2 := by ring
    have hlo : (q : ℝ) - C ^ 2 ≤ ‖(q : ℂ) + p.1 * p.2‖ := by
      have hqnorm : ‖(q : ℂ)‖ = (q : ℝ) := by norm_cast
      have htri : ‖(q : ℂ)‖ ≤ ‖(q : ℂ) + p.1 * p.2‖ + ‖p.1 * p.2‖ := by
        calc
          ‖(q : ℂ)‖ = ‖((q : ℂ) + p.1 * p.2) - p.1 * p.2‖ := by congr 1 <;> ring
          _ ≤ ‖(q : ℂ) + p.1 * p.2‖ + ‖p.1 * p.2‖ := norm_sub_le _ _
      rw [hqnorm] at htri
      linarith
    have hhi : ‖(q : ℂ) + p.1 * p.2‖ ≤ (q : ℝ) + C ^ 2 := by
      have hqnorm : ‖(q : ℂ)‖ = (q : ℝ) := by norm_cast
      rw [show (q : ℂ) + p.1 * p.2 = (q : ℂ) + p.1 * p.2 by rfl]
      calc
        ‖(q : ℂ) + p.1 * p.2‖ ≤ ‖(q : ℂ)‖ + ‖p.1 * p.2‖ := norm_add_le _ _
        _ ≤ (q : ℝ) + C ^ 2 := by rw [hqnorm]; linarith
    have hloglo := Real.log_le_log hlow hlo
    have hloghi := Real.log_le_log (lt_of_lt_of_le hlow hlo) hhi
    have hA : |Real.log ((q : ℝ) - C ^ 2)| ≤
        max |Real.log ((q : ℝ) + C ^ 2)|
          |Real.log ((q : ℝ) - C ^ 2)| := le_max_right _ _
    have hB : |Real.log ((q : ℝ) + C ^ 2)| ≤
        max |Real.log ((q : ℝ) + C ^ 2)|
          |Real.log ((q : ℝ) - C ^ 2)| := le_max_left _ _
    change |Real.log ‖(q : ℂ) + p.1 * p.2‖| ≤ _
    rw [abs_le]
    constructor <;> linarith [neg_abs_le (Real.log ((q : ℝ) - C ^ 2)),
      le_abs_self (Real.log ((q : ℝ) + C ^ 2))]
  refine Integrable.of_bound
    (measurable_v13DenominatorKernel q).aestronglyMeasurable
    (max |Real.log ((q : ℝ) + C ^ 2)| |Real.log ((q : ℝ) - C ^ 2)|) ?_
  exact hbound

theorem v13_smoothed_denominatorKernel_integrable {d e : ℕ}
    {q m : ℕ} (hq : 2 ≤ q) (hm : 64 ≤ m)
    (t : Fin d → ℝ) (s : Fin e → ℝ)
    (ht : ∀ i, |t i| ≤ 1) (hs : ∀ i, |s i| ≤ 1) :
    Integrable (v13DenominatorKernel q)
      ((v13SmoothedRealEmpirical t m).prod
        (v13SmoothedRealEmpirical s m)) := by
  refine v13_denominatorKernel_integrable (C := 1 + (3 / 4096 : ℝ)) hq _ _ ?_ ?_ ?_ ?_
  · exact v13SmoothedRealEmpirical_norm_ae_le_one_add_three_div_4096 t hm ht
  · exact v13SmoothedRealEmpirical_norm_ae_le_one_add_three_div_4096 s hm hs
  · norm_num
  · have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
    norm_num
    nlinarith

/-! ## The q=2 denominator and nonvanishing ledger -/

theorem v13_denominator_norm_lower_q2 {p : ℂ × ℂ}
    (h1 : ‖p.1‖ ≤ v13DenominatorTubeRadius)
    (h2 : ‖p.2‖ ≤ v13DenominatorTubeRadius) :
    (2 : ℝ) - v13DenominatorTubeRadius ^ 2 ≤
      ‖(2 : ℂ) + p.1 * p.2‖ := by
  exact v13DenominatorKernel_norm_lower (q := 2) (by omega) h1 h2

theorem v13_positiveBase_two_regression (n : ℕ) :
    vPolynomial n (2 : ℤ) = Matrix.det (vSourceMatrix n (2 : ℤ)) := by
  exact vPolynomial_two n

structure V13NonvanishingLedger where
  q : ℕ
  q_lower : 2 ≤ q
  q_upper : q ≤ 7
  G : ℕ → Polynomial ℚ
  Phi : ℕ → Polynomial ℚ
  G_ne_zero : ∀ n, G n ≠ 0
  Phi_ne_zero : ∀ n, Phi n ≠ 0

theorem V13NonvanishingLedger.q2_polynomial_regression
    (L : V13NonvanishingLedger) (n : ℕ)
    (hG : L.G n = vPolynomial n (-(2 : ℤ))) :
    L.G n = Matrix.det (vSourceMatrix n (-(2 : ℤ))) := by
  rw [hG]
  rfl

end

end Li2Lean.V

#print axioms Li2Lean.V.v13SmoothedRealEmpirical_log_integrable
#print axioms Li2Lean.V.v13_denominatorKernel_integrable

#print axioms Li2Lean.V.v13UnitIntervalMeasure_prod_map
#print axioms Li2Lean.V.l6PairCertificate_of_smoothed_real_blocks
