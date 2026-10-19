/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 License.

Concrete q = 2 reference-row and measure facts.  The row source is pinned to
the decoded `q2D` table; the normalization witness remains an explicit
mathematical input, so this file does not manufacture a reference package.
-/

import Li2Lean.B3.ReferenceMeasureAtomless
import Li2Lean.B3.V13ChainEnergy
import Li2Lean.B3.ReferenceMeasureSupportCircle

namespace Li2Lean.B3

noncomputable section

open V.EnergyCertI
open MeasureTheory Set
open scoped ENNReal

/-- The concrete q = 2 decoder output used by the EnergyCertI rows. -/
def q2ReferenceRows : V13DecodedRows 2 :=
  { data := q2D
    source := Or.inl ⟨rfl, rfl⟩ }

@[simp] theorem q2ReferenceRows_data : q2ReferenceRows.data = q2D := rfl

/-- The concrete reference constructor retains the signed base index q = 2. -/
theorem q2ReferenceMeasure_q
    {hq : SignedVBaseRange 2}
    (N : V13MeasureNormalization hq (v13RefRaw q2ReferenceRows)) :
    (v13RefMeasure q2ReferenceRows N).q = 2 := by
  rfl

/-- The finite q2 decoder's lower-energy endpoint is the v13 q2 constant
(`v-analytic.tex:375-386`). This is the decoder equality consumed by the
reference-package ledger. -/
theorem q2ReferenceQLowValue :
    IK.val (qlowQ 2) = (vQlow 2 : ℝ) := by
  norm_num [IK.val, qlowQ, vQlow]

/-- Atomlessness of every component of the q = 2 reference measure.

This specializes the measure-level proof to the actual decoded q2 rows; it
does not assume or construct any `VReferencePackage` or ledger. -/
theorem q2ReferenceMeasure_atomless
    {hq : SignedVBaseRange 2}
    (N : V13MeasureNormalization hq (v13RefRaw q2ReferenceRows)) :
    (∀ z : ℂ, (v13RefMeasure q2ReferenceRows N).μx {z} = 0) ∧
    (∀ z : ℂ, (v13RefMeasure q2ReferenceRows N).μv {z} = 0) ∧
    (∀ z : ℂ, (v13RefMeasure q2ReferenceRows N).μz {z} = 0) := by
  exact v13RefMeasure_atomless q2ReferenceRows N

/-! The q2 decoder also gives an explicit normalization witness for the raw
measure.  These are finite integer checks over the printed rows; keeping them
here makes the normalization boundary concrete without claiming the remaining
field, shard, or total-identity obligations. -/

private theorem q2_chain_measure_univ (cells : List V13ChainCell) :
    v13ChainMeasure cells Set.univ =
      (cells.map (fun c => ENNReal.ofReal c.density *
        ENNReal.ofReal (c.right - c.left))).sum := by
  rw [v13ChainMeasure_eq_list_sum]
  induction cells with
  | nil => simp
  | cons c cs ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [Measure.add_apply]
      rw [Measure.smul_apply, Measure.restrict_apply_univ,
        Real.volume_Ioc]
      simp only [smul_eq_mul]
      rw [ih]

private theorem q2_chain_complex_univ (cells : List V13ChainCell) :
    v13ChainMeasureComplex cells Set.univ =
      (cells.map (fun c => ENNReal.ofReal c.density *
        ENNReal.ofReal (c.right - c.left))).sum := by
  unfold v13ChainMeasureComplex
  rw [Measure.map_apply Complex.measurable_ofReal MeasurableSet.univ]
  rw [Set.preimage_univ, q2_chain_measure_univ]

theorem q2ReferenceRaw_x_mass :
    (v13RefRaw q2ReferenceRows).μx Set.univ = (1 : ℝ≥0∞) := by
  unfold v13RefRaw v13DecodedChainMeasure v13ChainMeasureComplex
  rw [Measure.map_apply Complex.measurable_ofReal MeasurableSet.univ]
  rw [Set.preimage_univ, q2_chain_measure_univ]
  norm_num [v13ChainCells, v13ChainCellsAux, q2D, mkIData, chainCP,
    chainCoords, chainMassU, densI, jumpsI, q2XHeader,
    q2XEntries, U, Li2Lean.V.Q2Certificate.decodeChain,
    Li2Lean.V.Q2Certificate.decodeChainAux,
    Li2Lean.V.Q2Certificate.scaleMass,
    Li2Lean.V.Q2Certificate.scaleLength,
    Li2Lean.V.Q2Certificate.correctedLength,
    IK.qsub, IK.qadd, IK.qneg, IK.val,
    ENNReal.ofReal_mul]
  simp (disch := positivity) only [← ENNReal.ofReal_mul]
  simp (disch := positivity) only [← ENNReal.ofReal_add]
  norm_num

theorem q2ReferenceRaw_v_mass :
    (v13RefRaw q2ReferenceRows).μv Set.univ = (5 / 4 : ℝ≥0∞) := by
  unfold v13RefRaw v13DecodedChainMeasure v13ChainMeasureComplex
  rw [Measure.map_apply Complex.measurable_ofReal MeasurableSet.univ]
  rw [Set.preimage_univ, q2_chain_measure_univ]
  norm_num [v13ChainCells, v13ChainCellsAux, q2D, mkIData, chainCP,
    chainCoords, chainMassU, densI, jumpsI, q2YHeader,
    q2YEntries, U, Li2Lean.V.Q2Certificate.decodeChain,
    Li2Lean.V.Q2Certificate.decodeChainAux,
    Li2Lean.V.Q2Certificate.scaleMass,
    Li2Lean.V.Q2Certificate.scaleLength,
    Li2Lean.V.Q2Certificate.correctedLength,
    IK.qsub, IK.qadd, IK.qneg, IK.val,
    ENNReal.ofReal_mul]
  simp (disch := positivity) only [← ENNReal.ofReal_mul]
  simp (disch := positivity) only [← ENNReal.ofReal_add]
  rw [← ENNReal.ofReal_toReal
    (ENNReal.div_ne_top (by norm_num) (by norm_num) :
      (5 / 4 : ℝ≥0∞) ≠ ⊤)]
  norm_num

theorem q2ReferenceRaw_z_chain_mass :
    v13DecodedChainMeasure q2D.zp Set.univ =
      (33849973 / 100000000 : ℝ≥0∞) := by
  unfold v13DecodedChainMeasure v13ChainMeasureComplex
  rw [Measure.map_apply Complex.measurable_ofReal MeasurableSet.univ]
  rw [Set.preimage_univ, q2_chain_measure_univ]
  norm_num [v13ChainCells, v13ChainCellsAux, q2D, mkIData, chainCP,
    chainCoords, chainMassU, densI, jumpsI, q2ZHeader,
    q2ZEntries, U, Li2Lean.V.Q2Certificate.decodeChain,
    Li2Lean.V.Q2Certificate.decodeChainAux,
    Li2Lean.V.Q2Certificate.scaleMass,
    Li2Lean.V.Q2Certificate.scaleLength,
    Li2Lean.V.Q2Certificate.correctedLength,
    IK.qsub, IK.qadd, IK.qneg, IK.val,
    ENNReal.ofReal_mul]
  simp (disch := positivity) only [← ENNReal.ofReal_mul]
  simp (disch := positivity) only [← ENNReal.ofReal_add]
  rw [← ENNReal.ofReal_toReal
    (ENNReal.div_ne_top (by norm_num) (by norm_num) :
      (33849973 / 100000000 : ℝ≥0∞) ≠ ⊤)]
  norm_num

private def q2_poisson_inside (p : Li2Lean.V.Q2Certificate.PoissonPoint) : Bool :=
  p.xUnits ^ 2 + p.yUnits ^ 2 < (30000000000000 : Int) ^ 2

private theorem q2_poisson_inside_all :
    (Li2Lean.V.Q2Certificate.decodePoisson
      Li2Lean.V.EnergyCertI.q2PoissonPrefix).all q2_poisson_inside = true := by
  decide +kernel

private def q2_poisson_inside_pr (r : PR) : Bool :=
  r.cx.1 ^ 2 + r.cy.1 ^ 2 < (30000000000000 : Int) ^ 2

private theorem q2_poisson_inside_full : q2D.full.all q2_poisson_inside_pr = true := by
  decide +kernel

private theorem q2_poisson_norm_of_inside_pr (r : PR)
    (hx : r.cx.2 = U) (hy : r.cy.2 = U)
    (h : r.cx.1 ^ 2 + r.cy.1 ^ 2 < (30000000000000 : Int) ^ 2) :
    ‖v13PoissonPoint r‖ < v13GlobalPoissonRadius := by
  have hr : ((r.cx.1 : ℝ) / (r.cx.2 : ℝ)) ^ 2 +
      ((r.cy.1 : ℝ) / (r.cy.2 : ℝ)) ^ 2 < (3 / 5 : ℝ) ^ 2 := by
    rw [hx, hy]
    have h' : ((r.cx.1 : ℝ) ^ 2 + (r.cy.1 : ℝ) ^ 2) <
        (30000000000000 : ℝ) ^ 2 := by exact_mod_cast h
    norm_num [U]
    nlinarith
  rw [← sq_lt_sq₀ (norm_nonneg _) (by norm_num [v13GlobalPoissonRadius])]
  rw [Complex.sq_norm]
  simpa [v13PoissonPoint, IK.val, v13GlobalPoissonRadius,
    Complex.normSq, pow_two] using hr

private theorem q2_poisson_full_norm :
    ∀ r ∈ q2D.full, ‖v13PoissonPoint r‖ < v13GlobalPoissonRadius := by
  intro r hr
  have hinside := (List.all_eq_true.mp q2_poisson_inside_full) r hr
  have hi : r.cx.1 ^ 2 + r.cy.1 ^ 2 < (30000000000000 : Int) ^ 2 := by
    exact of_decide_eq_true hinside
  have hden : r.cx.2 = U ∧ r.cy.2 = U := by
    change r ∈
      (Li2Lean.V.Q2Certificate.poissonFull
        (Li2Lean.V.Q2Certificate.decodePoisson
          Li2Lean.V.EnergyCertI.q2PoissonPrefix)).map
        (Li2Lean.V.EnergyCertI.prow 1) at hr
    rcases List.mem_map.mp hr with ⟨p, hp, rfl⟩
    constructor <;> rfl
  exact q2_poisson_norm_of_inside_pr r hden.1 hden.2 hi

private theorem q2_poisson_atom_univ {r : PR}
    (hp : ‖v13PoissonPoint r‖ < v13GlobalPoissonRadius) :
    v13PoissonAtom r Set.univ =
      ENNReal.ofReal ((r.mult : ℝ) * IK.val r.w) := by
  rw [v13PoissonAtom, Measure.smul_apply,
    v13GlobalCirclePoissonMeasure_univ hp]
  simp [smul_eq_mul]

private theorem q2_poisson_measure_univ_of_inside
    (rows : List PR)
    (hrows : ∀ r ∈ rows, ‖v13PoissonPoint r‖ < v13GlobalPoissonRadius) :
    v13PoissonMeasure rows Set.univ =
      (rows.map (fun r => ENNReal.ofReal ((r.mult : ℝ) * IK.val r.w))).sum := by
  induction rows with
  | nil => simp [v13PoissonMeasure]
  | cons r rs ih =>
      simp only [v13PoissonMeasure, List.map_cons, List.sum_cons]
      change (v13PoissonAtom r + v13PoissonMeasure rs) Set.univ = _
      rw [Measure.add_apply, q2_poisson_atom_univ (hrows r (by simp))]
      rw [ih (fun r hr => hrows r (by simp [hr]))]

theorem q2ReferenceRaw_poisson_mass :
    v13PoissonMeasure q2D.full Set.univ =
      (66150027 / 100000000 : ℝ≥0∞) := by
  rw [q2_poisson_measure_univ_of_inside q2D.full q2_poisson_full_norm]
  norm_num [q2D, mkIData, v13PoissonMeasure, v13PoissonAtom,
    Li2Lean.V.Q2Certificate.poissonFull,
    Li2Lean.V.Q2Certificate.decodePoisson,
    Li2Lean.V.Q2Certificate.decodePoissonAux,
    Li2Lean.V.Q2Certificate.conjugatePoisson,
    Li2Lean.V.EnergyCertI.prow, q2PoissonPrefix, U, IK.val,
    ENNReal.ofReal_mul]
  simp (disch := positivity) only [← ENNReal.ofReal_add]
  rw [← ENNReal.ofReal_toReal
    (ENNReal.div_ne_top (by norm_num) (by norm_num) :
      (66150027 / 100000000 : ℝ≥0∞) ≠ ⊤)]
  norm_num

theorem q2ReferenceRaw_z_mass :
    (v13RefRaw q2ReferenceRows).μz Set.univ = (1 : ℝ≥0∞) := by
  change (v13DecodedChainMeasure q2D.zp + v13PoissonMeasure q2D.full) Set.univ = _
  rw [Measure.add_apply, q2ReferenceRaw_z_chain_mass,
    q2ReferenceRaw_poisson_mass]
  have h1 : (33849973 / 100000000 : ℝ≥0∞) =
      ENNReal.ofReal ((33849973 : ℝ) / 100000000) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 100000000)]
    norm_num
  have h2 : (66150027 / 100000000 : ℝ≥0∞) =
      ENNReal.ofReal ((66150027 : ℝ) / 100000000) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 100000000)]
    norm_num
  rw [h1, h2, ← ENNReal.ofReal_add (by positivity) (by positivity)]
  norm_num

theorem q2ReferenceNormalization :
    V13MeasureNormalization (by constructor <;> norm_num : SignedVBaseRange 2)
      (v13RefRaw q2ReferenceRows) := by
  refine ⟨q2ReferenceRaw_x_mass, q2ReferenceRaw_v_mass,
    q2ReferenceRaw_z_mass, ?_, ?_, ?_⟩
  · rw [q2ReferenceRaw_x_mass]
    norm_num
  · rw [q2ReferenceRaw_v_mass]
    exact ENNReal.div_ne_top (by norm_num) (by norm_num)
  · rw [q2ReferenceRaw_z_mass]
    norm_num

theorem q2ReferenceMeasure_support
    {hq : SignedVBaseRange 2}
    (N : V13MeasureNormalization hq (v13RefRaw q2ReferenceRows)) :
    (v13RefMeasure q2ReferenceRows N).μx
        (Complex.ofReal '' Icc (vXLow 2) 1)ᶜ = 0 ∧
    (v13RefMeasure q2ReferenceRows N).μv
        (Complex.ofReal '' Icc (vVLow 2) 1)ᶜ = 0 ∧
    (v13RefMeasure q2ReferenceRows N).μz
        ((Complex.ofReal '' Icc (-(2 : ℝ)) (-3 / 5)) ∪
          Metric.sphere 0 (3 / 5))ᶜ = 0 ∧
    (v13RefMeasure q2ReferenceRows N).μx
        (Complex.ofReal '' Icc (0 : ℝ) 1)ᶜ = 0 ∧
    (v13RefMeasure q2ReferenceRows N).μv
        (Complex.ofReal '' Icc (0 : ℝ) 1)ᶜ = 0 ∧
    (v13RefMeasure q2ReferenceRows N).μz (V.vContourTrace 2)ᶜ = 0 := by
  have hxLow : ∀ c ∈ v13ChainCells q2D.xp,
      vXLow 2 ≤ c.left ∧ c.right ≤ 1 := by
    intro c hc
    have h := v13_q2_x_bounds c hc
    norm_num [vXLow] at h ⊢
    constructor
    · exact h.1
    · exact h.2
  have hxFull : ∀ c ∈ v13ChainCells q2D.xp,
      (0 : ℝ) ≤ c.left ∧ c.right ≤ 1 := v13_q2_x_full_bounds
  have hvLow : ∀ c ∈ v13ChainCells q2D.vp,
      vVLow 2 ≤ c.left ∧ c.right ≤ 1 := by
    simpa [vVLow] using v13_q2_v_bounds
  have hvFull : ∀ c ∈ v13ChainCells q2D.vp,
      (0 : ℝ) ≤ c.left ∧ c.right ≤ 1 := v13_q2_v_full_bounds
  have hzSource : ∀ c ∈ v13ChainCells q2D.zp,
      (-(2 : ℝ)) ≤ c.left ∧ c.right ≤ -(3 / 5 : ℝ) :=
    v13_q2_z_source_bounds
  have hzSource' : ∀ c ∈ v13ChainCells q2ReferenceRows.data.zp,
      (-(2 : ℝ)) ≤ c.left ∧ c.right ≤ -(3 / 5 : ℝ) := by
    simpa only [q2ReferenceRows_data] using hzSource
  have hzSource'' : ∀ c ∈ v13ChainCells q2ReferenceRows.data.zp,
      (-(2 : ℝ)) ≤ c.left ∧ c.right ≤ (-3 / 5 : ℝ) := by
    intro c hc
    have h := hzSource' c hc
    constructor
    · exact h.1
    · norm_num at h ⊢
      exact h.2
  let hzSourceSet : Set ℂ :=
      (Complex.ofReal '' Icc (-(2 : ℝ)) (-3 / 5)) ∪
        Metric.sphere 0 (3 / 5)
  have hzRawOut :
      (v13DecodedChainMeasure q2D.zp + v13PoissonMeasure q2D.full)
        hzSourceSetᶜ = 0 := by
    have hchain : v13DecodedChainMeasure q2D.zp
        (Complex.ofReal '' Icc (-(2 : ℝ)) (-3 / 5))ᶜ = 0 := by
      apply v13DecodedChainMeasure_outside_of_cells q2D.zp
        (-(2 : ℝ)) (-3 / 5)
      intro c hc
      have h := hzSource c hc
      constructor
      · exact h.1
      · norm_num at h ⊢
        exact h.2
    have hchain' : v13DecodedChainMeasure q2D.zp hzSourceSetᶜ = 0 :=
      measure_mono_null
        (by
          intro z hzS hzImage
          have hzS' : z ∉
              (Complex.ofReal '' Icc (-(2 : ℝ)) (-3 / 5) ∪
                Metric.sphere 0 (3 / 5)) := by
            simpa [hzSourceSet] using hzS
          exact hzS' (Or.inl hzImage)) hchain
    have hpoisson : v13PoissonMeasure q2D.full
        (Metric.sphere 0 v13GlobalPoissonRadius)ᶜ = 0 :=
      v13GlobalPoissonMeasure_outside_sphere q2D.full
    rw [v13GlobalPoissonRadius] at hpoisson
    have hpoisson' : v13PoissonMeasure q2D.full hzSourceSetᶜ = 0 :=
      measure_mono_null
        (by
          intro z hzS hzSphere
          have hzS' : z ∉
              (Complex.ofReal '' Icc (-(2 : ℝ)) (-3 / 5) ∪
                Metric.sphere 0 (3 / 5)) := by
            simpa [hzSourceSet] using hzS
          exact hzS' (Or.inr hzSphere)) hpoisson
    rw [Measure.add_apply, hchain', hpoisson', zero_add]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · change v13DecodedChainMeasure q2D.xp
      (Complex.ofReal '' Icc (vXLow 2) 1)ᶜ = 0
    exact v13DecodedChainMeasure_outside_of_cells _ _ _ hxLow
  · change v13DecodedChainMeasure q2D.vp
      (Complex.ofReal '' Icc (vVLow 2) 1)ᶜ = 0
    exact v13DecodedChainMeasure_outside_of_cells _ _ _ hvLow
  · have hzraw : (v13RefMeasure q2ReferenceRows N).μz =
        (v13RefRaw q2ReferenceRows).μz := rfl
    rw [hzraw]
    have hzm : (v13RefRaw q2ReferenceRows).μz =
        v13DecodedChainMeasure q2D.zp + v13PoissonMeasure q2D.full := by
      rfl
    rw [hzm]
    simpa [hzSourceSet] using hzRawOut
  · change v13DecodedChainMeasure q2D.xp
      (Complex.ofReal '' Icc (0 : ℝ) 1)ᶜ = 0
    exact v13DecodedChainMeasure_outside_of_cells _ _ _ hxFull
  · change v13DecodedChainMeasure q2D.vp
      (Complex.ofReal '' Icc (0 : ℝ) 1)ᶜ = 0
    exact v13DecodedChainMeasure_outside_of_cells _ _ _ hvFull
  · have hzraw : (v13RefMeasure q2ReferenceRows N).μz =
        (v13RefRaw q2ReferenceRows).μz := rfl
    rw [hzraw]
    apply measure_mono_null
      (s := (V.vContourTrace 2)ᶜ)
      (t := (Complex.ofReal '' Icc (-(2 : ℝ)) (-3 / 5) ∪
        Metric.sphere 0 (3 / 5))ᶜ)
      (by
        intro z hzTrace hzSourceSet
        exact hzTrace (v13_source_subset_trace (by norm_num) hzSourceSet))
    have hzm : (v13RefRaw q2ReferenceRows).μz =
        v13DecodedChainMeasure q2D.zp + v13PoissonMeasure q2D.full := by
      rfl
    rw [hzm]
    simpa [hzSourceSet] using hzRawOut

end

end Li2Lean.B3

#print axioms Li2Lean.B3.q2ReferenceMeasure_q
#print axioms Li2Lean.B3.q2ReferenceMeasure_atomless
