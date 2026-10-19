/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.ConfigSegment
import Li2Lean.P0.TubeSweepPair
import Li2Lean.B3.V13ReferenceMeasure

/-!
  Atomlessness lemmas for the concrete v13 reference measure components.

  The construction uses finite sums of densities restricted to real intervals,
  followed by `Complex.ofReal`, and an angular density pushed through the
  literal ellipse map.  These lemmas only use those definitions and therefore
  cannot hide atomlessness as an input field.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Li2Lean.B3

noncomputable section

/-! ## Real interval components -/

theorem volume_restrict_Icc_singleton (a b x : ℝ) :
    (volume.restrict (Icc a b)) {x} = 0 := by
  rw [Measure.restrict_apply (measurableSet_singleton x)]
  exact measure_mono_null inter_subset_left (measure_singleton x)

theorem volume_restrict_Ioc_singleton (a b x : ℝ) :
    (volume.restrict (Ioc a b)) {x} = 0 := by
  rw [Measure.restrict_apply (measurableSet_singleton x)]
  exact measure_mono_null inter_subset_left (measure_singleton x)

theorem volume_restrict_Ico_singleton (a b x : ℝ) :
    (volume.restrict (Ico a b)) {x} = 0 := by
  rw [Measure.restrict_apply (measurableSet_singleton x)]
  exact measure_mono_null inter_subset_left (measure_singleton x)

theorem smul_volume_restrict_Icc_singleton (c : ℝ≥0∞) (a b x : ℝ) :
    (c • volume.restrict (Icc a b)) {x} = 0 := by
  rw [Measure.smul_apply, Measure.restrict_apply (measurableSet_singleton x)]
  simp only [smul_eq_mul]
  have hzero : volume ({x} ∩ Icc a b) = 0 :=
    measure_mono_null inter_subset_left (measure_singleton x)
  rw [hzero]
  simp

theorem smul_volume_restrict_Ioc_singleton (c : ℝ≥0∞) (a b x : ℝ) :
    (c • volume.restrict (Ioc a b)) {x} = 0 := by
  rw [Measure.smul_apply, Measure.restrict_apply (measurableSet_singleton x)]
  simp only [smul_eq_mul]
  have hzero : volume ({x} ∩ Ioc a b) = 0 :=
    measure_mono_null inter_subset_left (measure_singleton x)
  rw [hzero]
  simp

theorem smul_volume_restrict_Ico_singleton (c : ℝ≥0∞) (a b x : ℝ) :
    (c • volume.restrict (Ico a b)) {x} = 0 := by
  rw [Measure.smul_apply, Measure.restrict_apply (measurableSet_singleton x)]
  simp only [smul_eq_mul]
  have hzero : volume ({x} ∩ Ico a b) = 0 :=
    measure_mono_null inter_subset_left (measure_singleton x)
  rw [hzero]
  simp

/-! A finite sum of interval densities is atomless.  The index can be any
finite type; this is the form used by the variable-length chain measure. -/

theorem finset_sum_smul_volume_restrict_Icc_singleton
    {ι : Type*} (s : Finset ι) (a b c : ι → ℝ) (x : ℝ) :
    (∑ i ∈ s, ENNReal.ofReal (c i) • volume.restrict (Icc (a i) (b i))) {x} = 0 := by
  rw [Measure.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro i hi
  rw [smul_volume_restrict_Icc_singleton]

theorem finset_sum_smul_volume_restrict_Ioc_singleton
    {ι : Type*} (s : Finset ι) (a b c : ι → ℝ) (x : ℝ) :
    (∑ i ∈ s, ENNReal.ofReal (c i) • volume.restrict (Ioc (a i) (b i))) {x} = 0 := by
  rw [Measure.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro i hi
  rw [smul_volume_restrict_Ioc_singleton]

/-! ## Reference pushforwards -/

theorem referenceMeasure_singleton (start : ℝ) (count : ℕ)
    (units : List ℕ) (x : ℝ) :
    P0.ConfigSegment.referenceMeasure start count units {x} = 0 := by
  unfold P0.ConfigSegment.referenceMeasure
  rw [Measure.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro j hj
  exact smul_volume_restrict_Ico_singleton _ _ _ _

theorem referenceMeasure_map_ofReal_singleton
    (start : ℝ) (count : ℕ) (units : List ℕ) (z : ℂ) :
    (Measure.map Complex.ofReal
      (P0.ConfigSegment.referenceMeasure start count units)) {z} = 0 := by
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
    rw [hpre, referenceMeasure_singleton]
  · have hpre : Complex.ofReal ⁻¹' ({z} : Set ℂ) = (∅ : Set ℝ) := by
      ext x
      constructor
      · intro hx
        have hi := congrArg Complex.im hx
        exact (hz hi.symm).elim
      · intro hx
        exact hx.elim
    rw [hpre, measure_empty]

/-! ## Angular Poisson component -/

/- The concrete v13 rows use the fixed-radius circle law from
`V13ReferenceMeasure`, not the older ellipse law from `P0.TubeEnergy`. -/
theorem v13GlobalCirclePoissonMeasure_singleton (p x : ℂ) :
    v13GlobalCirclePoissonMeasure p {x} = 0 := by
  rw [v13GlobalCirclePoissonMeasure,
    Measure.map_apply (continuous_circleMap 0 v13GlobalPoissonRadius).measurable
      (measurableSet_singleton x)]
  apply withDensity_absolutelyContinuous
  have hc :
      (circleMap 0 v13GlobalPoissonRadius ⁻¹' ({x} : Set ℂ)).Countable :=
    (Set.countable_singleton x).preimage_circleMap 0 (by
      norm_num [v13GlobalPoissonRadius])
  exact hc.measure_zero _

/-! ## Concrete v13 components -/

theorem v13ChainMeasure_singleton (cells : List V13ChainCell) (x : ℝ) :
    v13ChainMeasure cells {x} = 0 := by
  induction cells with
  | nil => simp [v13ChainMeasure]
  | cons c cs ih =>
      simp only [v13ChainMeasure, List.foldr_cons]
      rw [Measure.add_apply]
      rw [Measure.smul_apply, Measure.restrict_apply (measurableSet_singleton x)]
      simp only [smul_eq_mul]
      have hzero : volume ({x} ∩ Ioc c.left c.right) = 0 :=
        measure_mono_null inter_subset_left (measure_singleton x)
      have ih' :
          (List.foldr
            (fun c μ => ENNReal.ofReal c.density •
              volume.restrict (Ioc c.left c.right) + μ) 0 cs) {x} = 0 := by
        simpa [v13ChainMeasure] using ih
      rw [hzero, ih']
      simp

theorem v13ChainMeasureComplex_singleton
    (cells : List V13ChainCell) (z : ℂ) :
    v13ChainMeasureComplex cells {z} = 0 := by
  unfold v13ChainMeasureComplex
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
    rw [hpre, v13ChainMeasure_singleton]
  · have hpre : Complex.ofReal ⁻¹' ({z} : Set ℂ) = (∅ : Set ℝ) := by
      ext x
      constructor
      · intro hx
        have hi := congrArg Complex.im hx
        exact (hz hi.symm).elim
      · intro hx
        exact hx.elim
    rw [hpre, measure_empty]

theorem v13DecodedChainMeasure_singleton
    (rows : List V.EnergyCertI.CP) (z : ℂ) :
    v13DecodedChainMeasure rows {z} = 0 := by
  exact v13ChainMeasureComplex_singleton (v13ChainCells rows) z

theorem v13PoissonAtom_singleton
    (r : V.EnergyCertI.PR) (z : ℂ) :
    v13PoissonAtom r {z} = 0 := by
  unfold v13PoissonAtom
  rw [Measure.smul_apply]
  simp only [smul_eq_mul]
  have hzero : v13GlobalCirclePoissonMeasure (v13PoissonPoint r) {z} = 0 :=
    v13GlobalCirclePoissonMeasure_singleton _ _
  rw [hzero]
  simp

theorem v13PoissonMeasure_singleton
    (rows : List V.EnergyCertI.PR) (z : ℂ) :
    v13PoissonMeasure rows {z} = 0 := by
  induction rows with
  | nil => simp [v13PoissonMeasure]
  | cons r rs ih =>
      simp only [v13PoissonMeasure, List.foldr_cons]
      rw [Measure.add_apply]
      rw [v13PoissonAtom_singleton]
      have ih' :
          (List.foldr (fun r μ => v13PoissonAtom r + μ) 0 rs) {z} = 0 := by
        simpa [v13PoissonMeasure] using ih
      rw [ih']
      simp

theorem v13RefRaw_z_singleton {q : ℕ} (R : V13DecodedRows q) (z : ℂ) :
    (v13RefRaw R).μz {z} = 0 := by
  change (v13DecodedChainMeasure R.data.zp + v13PoissonMeasure R.data.full) {z} = 0
  rw [Measure.add_apply, v13DecodedChainMeasure_singleton,
    v13PoissonMeasure_singleton, zero_add]

theorem v13RefRaw_x_singleton {q : ℕ} (R : V13DecodedRows q) (z : ℂ) :
    (v13RefRaw R).μx {z} = 0 := by
  change v13DecodedChainMeasure R.data.xp {z} = 0
  exact v13DecodedChainMeasure_singleton _ _

theorem v13RefRaw_v_singleton {q : ℕ} (R : V13DecodedRows q) (z : ℂ) :
    (v13RefRaw R).μv {z} = 0 := by
  change v13DecodedChainMeasure R.data.vp {z} = 0
  exact v13DecodedChainMeasure_singleton _ _

theorem v13RefMeasure_x_singleton {q : ℕ} {hq : SignedVBaseRange q}
    (R : V13DecodedRows q) (N : V13MeasureNormalization hq (v13RefRaw R))
    (z : ℂ) :
    (v13RefMeasure R N).μx {z} = 0 := by
  change (v13RefRaw R).μx {z} = 0
  exact v13RefRaw_x_singleton R z

theorem v13RefMeasure_v_singleton {q : ℕ} {hq : SignedVBaseRange q}
    (R : V13DecodedRows q) (N : V13MeasureNormalization hq (v13RefRaw R))
    (z : ℂ) :
    (v13RefMeasure R N).μv {z} = 0 := by
  change (v13RefRaw R).μv {z} = 0
  exact v13RefRaw_v_singleton R z

theorem v13RefMeasure_z_singleton {q : ℕ} {hq : SignedVBaseRange q}
    (R : V13DecodedRows q) (N : V13MeasureNormalization hq (v13RefRaw R))
    (z : ℂ) :
    (v13RefMeasure R N).μz {z} = 0 := by
  change (v13RefRaw R).μz {z} = 0
  exact v13RefRaw_z_singleton R z

/-- The three components of every normalized v13 reference measure are
atomless.  The statement is uniform in the base `q`, decoded rows, and
normalization witness, so it can be projected directly into the three F2
fields of `VReferenceFacts`. -/
theorem v13RefMeasure_atomless {q : ℕ} {hq : SignedVBaseRange q}
    (R : V13DecodedRows q) (N : V13MeasureNormalization hq (v13RefRaw R)) :
    (∀ z : ℂ, (v13RefMeasure R N).μx {z} = 0) ∧
    (∀ z : ℂ, (v13RefMeasure R N).μv {z} = 0) ∧
    (∀ z : ℂ, (v13RefMeasure R N).μz {z} = 0) := by
  exact ⟨v13RefMeasure_x_singleton R N,
    v13RefMeasure_v_singleton R N,
    v13RefMeasure_z_singleton R N⟩

end

end Li2Lean.B3

#print axioms Li2Lean.B3.referenceMeasure_singleton
#print axioms Li2Lean.B3.referenceMeasure_map_ofReal_singleton
#print axioms Li2Lean.B3.v13GlobalCirclePoissonMeasure_singleton
#print axioms Li2Lean.B3.v13RefMeasure_atomless
