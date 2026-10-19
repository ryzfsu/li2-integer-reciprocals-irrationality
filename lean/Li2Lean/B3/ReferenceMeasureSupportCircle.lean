/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B3.V13ReferenceMeasure
import Li2Lean.V.VPath
import Li2Lean.V.EnergyCertI.Q2Rows
import Li2Lean.V.EnergyCertI.Q5Rows

open MeasureTheory Set
open scoped ENNReal

namespace Li2Lean
namespace B3

noncomputable section

theorem v13ChainMeasure_outside_Icc
    (cells : List V13ChainCell) (A B : ℝ)
    (hcell : ∀ c ∈ cells, A ≤ c.left ∧ c.right ≤ B) :
    v13ChainMeasure cells (Icc A B)ᶜ = 0 := by
  induction cells with
  | nil => simp [v13ChainMeasure]
  | cons c cs ih =>
      simp only [v13ChainMeasure, List.foldr_cons]
      rw [Measure.add_apply]
      have hc := hcell c (by simp)
      have hcs : ∀ d ∈ cs, A ≤ d.left ∧ d.right ≤ B := by
        intro d hd
        exact hcell d (by simp [hd])
      have hsub : (Icc A B)ᶜ ∩ Ioc c.left c.right = (∅ : Set ℝ) := by
        ext x
        constructor
        · intro hx
          exact (hx.1 ⟨le_trans hc.1 (le_of_lt hx.2.1),
            le_trans hx.2.2 hc.2⟩).elim
        · intro hx
          exact hx.elim
      rw [Measure.smul_apply, Measure.restrict_apply measurableSet_Icc.compl,
        hsub, measure_empty]
      simp only [smul_eq_mul, mul_zero]
      simpa [v13ChainMeasure] using ih hcs

theorem v13ChainMeasureComplex_outside_of_cells
    (cells : List V13ChainCell) (A B : ℝ)
    (hcell : ∀ c ∈ cells, A ≤ c.left ∧ c.right ≤ B) :
    v13ChainMeasureComplex cells (Complex.ofReal '' Icc A B)ᶜ = 0 := by
  unfold v13ChainMeasureComplex
  have hcompact : IsCompact (Complex.ofReal '' Icc A B) :=
    isCompact_Icc.image_of_continuousOn Complex.continuous_ofReal.continuousOn
  rw [Measure.map_apply Complex.measurable_ofReal hcompact.measurableSet.compl]
  rw [Set.preimage_compl, Set.preimage_image_eq _ Complex.ofReal_injective]
  exact v13ChainMeasure_outside_Icc cells A B hcell

theorem v13DecodedChainMeasure_outside_of_cells
    (rows : List V.EnergyCertI.CP) (A B : ℝ)
    (hcell : ∀ c ∈ v13ChainCells rows, A ≤ c.left ∧ c.right ≤ B) :
    v13DecodedChainMeasure rows (Complex.ofReal '' Icc A B)ᶜ = 0 := by
  exact v13ChainMeasureComplex_outside_of_cells (v13ChainCells rows) A B hcell

theorem v13_negative_source_subset_trace
    {q : ℕ} (hq : 2 ≤ q) :
    Complex.ofReal '' Icc (-(q : ℝ)) (-3 / 5) ⊆
      V.vNegativeSegment q '' Icc (0 : ℝ) 1 := by
  intro z hz
  rcases hz with ⟨x, hx, rfl⟩
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hden : 0 < (q : ℝ) - 3 / 5 := by linarith
  let t : ℝ := (x + (q : ℝ)) / ((q : ℝ) - 3 / 5)
  have ht0 : 0 ≤ t := by
    dsimp [t]
    apply div_nonneg
    · linarith [hx.1]
    · linarith
  have ht1 : t ≤ 1 := by
    dsimp [t]
    apply (div_le_iff₀ hden).2
    linarith [hx.2]
  refine ⟨t, ⟨ht0, ht1⟩, ?_⟩
  change Complex.ofReal (-(q : ℝ) + ((q : ℝ) - 3 / 5) * t) =
    Complex.ofReal x
  congr 1
  have ht_eq : ((q : ℝ) - 3 / 5) * t = x + (q : ℝ) := by
    dsimp [t]
    have hden' : (q : ℝ) * 5 - 3 ≠ 0 := by nlinarith
    field_simp [hden']
  linarith

theorem v13_circle_subset_trace :
    Metric.sphere 0 (3 / 5 : ℝ) ⊆
      (V.vUpperArc '' Icc (0 : ℝ) 1) ∪
        (V.vLowerArc '' Icc (0 : ℝ) 1) := by
  intro z hz
  have hz' : z ∈ circleMap 0 (3 / 5 : ℝ) '' Ioc (0 : ℝ) (2 * Real.pi) := by
    rw [image_circleMap_Ioc]
    simpa only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 5)] using hz
  rcases hz' with ⟨θ, hθ, rfl⟩
  by_cases hhalf : θ ≤ Real.pi
  · left
    let t : ℝ := θ / Real.pi
    have hpi : 0 < Real.pi := Real.pi_pos
    have ht : t ∈ Icc (0 : ℝ) 1 := by
      constructor
      · dsimp [t]
        exact div_nonneg hθ.1.le hpi.le
      · dsimp [t]
        exact (div_le_iff₀ hpi).2 (by simpa using hhalf)
    refine ⟨t, ht, ?_⟩
    rw [V.vUpperArc, ContourKit.p0CirclePoint_eq_circleMap]
    congr 2
    dsimp [t]
    field_simp
  · right
    let t : ℝ := (θ - Real.pi) / Real.pi
    have hpi : 0 < Real.pi := Real.pi_pos
    have ht : t ∈ Icc (0 : ℝ) 1 := by
      constructor
      · dsimp [t]
        exact div_nonneg (sub_nonneg.mpr (le_of_not_ge hhalf)) hpi.le
      · dsimp [t]
        apply (div_le_iff₀ hpi).2
        linarith [hθ.2]
    refine ⟨t, ht, ?_⟩
    rw [V.vLowerArc, ContourKit.p0CirclePoint_eq_circleMap]
    congr 2
    dsimp [t]
    field_simp
    ring

theorem v13_source_subset_trace {q : ℕ} (hq : 2 ≤ q) :
    (Complex.ofReal '' Icc (-(q : ℝ)) (-3 / 5)) ∪
        Metric.sphere 0 (3 / 5 : ℝ) ⊆ V.vContourTrace q := by
  intro z hz
  rcases hz with hz | hz
  · exact Or.inl (v13_negative_source_subset_trace hq hz)
  · exact Or.inr (Or.inr (v13_circle_subset_trace hz))

theorem v13GlobalPoissonMeasure_outside_sphere
    (rows : List V.EnergyCertI.PR) :
    v13PoissonMeasure rows
        (Metric.sphere 0 v13GlobalPoissonRadius)ᶜ = 0 := by
  induction rows with
  | nil => simp [v13PoissonMeasure]
  | cons r rs ih =>
      simp only [v13PoissonMeasure, List.foldr_cons]
      rw [Measure.add_apply]
      have hr : v13PoissonAtom r
          (Metric.sphere 0 v13GlobalPoissonRadius)ᶜ = 0 := by
        unfold v13PoissonAtom
        rw [Measure.smul_apply, v13GlobalCirclePoissonMeasure_sphere_compl]
        simp
      rw [hr]
      simpa [v13PoissonMeasure] using ih

theorem v13RefRaw_z_outside_of_v13_source
    {q : ℕ} (R : V13DecodedRows q) (A B : ℝ)
    (hcell : ∀ c ∈ v13ChainCells R.data.zp,
      A ≤ c.left ∧ c.right ≤ B) :
    (v13RefRaw R).μz
      ((Complex.ofReal '' Icc A B) ∪
        Metric.sphere 0 v13GlobalPoissonRadius)ᶜ = 0 := by
  change (v13DecodedChainMeasure R.data.zp +
      v13PoissonMeasure R.data.full)
      ((Complex.ofReal '' Icc A B) ∪
        Metric.sphere 0 v13GlobalPoissonRadius)ᶜ = 0
  have hchain : v13DecodedChainMeasure R.data.zp
      ((Complex.ofReal '' Icc A B) ∪
        Metric.sphere 0 v13GlobalPoissonRadius)ᶜ = 0 :=
    measure_mono_null
      (by
        intro z hz hzImage
        exact hz (Or.inl hzImage))
      (v13ChainMeasureComplex_outside_of_cells
        (v13ChainCells R.data.zp) A B hcell)
  have hpoisson : v13PoissonMeasure R.data.full
      ((Complex.ofReal '' Icc A B) ∪
        Metric.sphere 0 v13GlobalPoissonRadius)ᶜ = 0 :=
    measure_mono_null
      (by
        intro z hz hzSphere
        exact hz (Or.inr hzSphere))
      (v13GlobalPoissonMeasure_outside_sphere R.data.full)
  rw [Measure.add_apply, hchain, hpoisson, zero_add]

theorem v13RefMeasure_supports_of_bounds
    {q : ℕ} {hq : SignedVBaseRange q}
    (R : V13DecodedRows q)
    (N : V13MeasureNormalization hq (v13RefRaw R))
    (xLow vLow : ℝ)
    (hxLow : ∀ c ∈ v13ChainCells R.data.xp,
      xLow ≤ c.left ∧ c.right ≤ 1)
    (hxFull : ∀ c ∈ v13ChainCells R.data.xp,
      0 ≤ c.left ∧ c.right ≤ 1)
    (hvLow : ∀ c ∈ v13ChainCells R.data.vp,
      vLow ≤ c.left ∧ c.right ≤ 1)
    (hvFull : ∀ c ∈ v13ChainCells R.data.vp,
      0 ≤ c.left ∧ c.right ≤ 1)
    (hzSource : ∀ c ∈ v13ChainCells R.data.zp,
      (-(q : ℝ)) ≤ c.left ∧ c.right ≤ -(3 / 5 : ℝ)) :
    (v13RefMeasure R N).μx
        (Complex.ofReal '' Icc xLow 1)ᶜ = 0 ∧
    (v13RefMeasure R N).μv
        (Complex.ofReal '' Icc vLow 1)ᶜ = 0 ∧
    (v13RefMeasure R N).μz
        ((Complex.ofReal '' Icc (-(q : ℝ)) (-3 / 5)) ∪
          Metric.sphere 0 (3 / 5))ᶜ = 0 ∧
    (v13RefMeasure R N).μx
        (Complex.ofReal '' Icc (0 : ℝ) 1)ᶜ = 0 ∧
    (v13RefMeasure R N).μv
        (Complex.ofReal '' Icc (0 : ℝ) 1)ᶜ = 0 ∧
    (v13RefMeasure R N).μz (V.vContourTrace q)ᶜ = 0 := by
  have hx₁ : (v13RefMeasure R N).μx
      (Complex.ofReal '' Icc xLow 1)ᶜ = 0 := by
    exact v13DecodedChainMeasure_outside_of_cells _ _ _ hxLow
  have hv₁ : (v13RefMeasure R N).μv
      (Complex.ofReal '' Icc vLow 1)ᶜ = 0 := by
    exact v13DecodedChainMeasure_outside_of_cells _ _ _ hvLow
  have hz₁ : (v13RefMeasure R N).μz
      ((Complex.ofReal '' Icc (-(q : ℝ)) (-3 / 5)) ∪
        Metric.sphere 0 v13GlobalPoissonRadius)ᶜ = 0 := by
    apply v13RefRaw_z_outside_of_v13_source R _ _
    intro c hc
    have h := hzSource c hc
    constructor
    · exact h.1
    · norm_num at h ⊢
      exact h.2
  have hx₂ : (v13RefMeasure R N).μx
      (Complex.ofReal '' Icc (0 : ℝ) 1)ᶜ = 0 := by
    exact v13DecodedChainMeasure_outside_of_cells _ _ _ hxFull
  have hv₂ : (v13RefMeasure R N).μv
      (Complex.ofReal '' Icc (0 : ℝ) 1)ᶜ = 0 := by
    exact v13DecodedChainMeasure_outside_of_cells _ _ _ hvFull
  have hz₂ : (v13RefMeasure R N).μz (V.vContourTrace q)ᶜ = 0 := by
    have hz₁' : (v13RefMeasure R N).μz
        ((Complex.ofReal '' Icc (-(q : ℝ)) (-3 / 5)) ∪
          Metric.sphere 0 (3 / 5))ᶜ = 0 := by
      simpa only [v13GlobalPoissonRadius] using hz₁
    exact measure_mono_null
      (by
        intro z hzT hzS
        exact hzT (v13_source_subset_trace hq.1 hzS)) hz₁'
  exact ⟨hx₁, hv₁, hz₁, hx₂, hv₂, hz₂⟩

set_option maxHeartbeats 2000000 in
theorem v13_q2_x_bounds :
    ∀ c ∈ v13ChainCells V.EnergyCertI.q2D.xp,
      (3349365000000 : ℝ) / (5 * 10 ^ 13) ≤ c.left ∧ c.right ≤ 1 := by
  norm_num [V.EnergyCertI.q2D, V.EnergyCertI.mkIData, v13ChainCells,
    v13ChainCellsAux, V.EnergyCertI.chainCP, V.EnergyCertI.q2XHeader,
    V.EnergyCertI.q2XEntries, V.EnergyCertI.chainCoords,
    Li2Lean.V.Q2Certificate.decodeChain,
    Li2Lean.V.Q2Certificate.decodeChainAux,
    V.EnergyCertI.chainMassU, V.EnergyCertI.densI, V.EnergyCertI.jumpsI,
    V.EnergyCertI.IK.val, V.Q2Certificate.correctedLength,
    V.Q2Certificate.scaleLength, V.Q2Certificate.scaleMass,
    V.EnergyCertI.U]

set_option maxHeartbeats 2000000 in
theorem v13_q2_x_full_bounds :
    ∀ c ∈ v13ChainCells V.EnergyCertI.q2D.xp,
      (0 : ℝ) ≤ c.left ∧ c.right ≤ 1 := by
  norm_num [V.EnergyCertI.q2D, V.EnergyCertI.mkIData, v13ChainCells,
    v13ChainCellsAux, V.EnergyCertI.chainCP, V.EnergyCertI.q2XHeader,
    V.EnergyCertI.q2XEntries, V.EnergyCertI.chainCoords,
    Li2Lean.V.Q2Certificate.decodeChain,
    Li2Lean.V.Q2Certificate.decodeChainAux,
    V.EnergyCertI.chainMassU, V.EnergyCertI.densI, V.EnergyCertI.jumpsI,
    V.EnergyCertI.IK.val, V.Q2Certificate.correctedLength,
    V.Q2Certificate.scaleLength, V.Q2Certificate.scaleMass,
    V.EnergyCertI.U]

set_option maxHeartbeats 2000000 in
theorem v13_q5_x_bounds :
    ∀ c ∈ v13ChainCells V.EnergyCertI.q5D.xp,
      (3349364905389 : ℝ) / (5 * 10 ^ 13) ≤ c.left ∧ c.right ≤ 1 := by
  norm_num [V.EnergyCertI.q5D, V.EnergyCertI.mkIData, v13ChainCells,
    v13ChainCellsAux, V.EnergyCertI.chainCP, V.EnergyCertI.q5XHeader,
    V.EnergyCertI.q5XEntries, V.EnergyCertI.chainCoords,
    Li2Lean.V.Q2Certificate.decodeChain,
    Li2Lean.V.Q2Certificate.decodeChainAux,
    V.EnergyCertI.chainMassU, V.EnergyCertI.densI, V.EnergyCertI.jumpsI,
    V.EnergyCertI.IK.val, V.Q2Certificate.correctedLength,
    V.Q2Certificate.scaleLength, V.Q2Certificate.scaleMass,
    V.EnergyCertI.U]

set_option maxHeartbeats 2000000 in
theorem v13_q5_x_full_bounds :
    ∀ c ∈ v13ChainCells V.EnergyCertI.q5D.xp,
      (0 : ℝ) ≤ c.left ∧ c.right ≤ 1 := by
  norm_num [V.EnergyCertI.q5D, V.EnergyCertI.mkIData, v13ChainCells,
    v13ChainCellsAux, V.EnergyCertI.chainCP, V.EnergyCertI.q5XHeader,
    V.EnergyCertI.q5XEntries, V.EnergyCertI.chainCoords,
    Li2Lean.V.Q2Certificate.decodeChain,
    Li2Lean.V.Q2Certificate.decodeChainAux,
    V.EnergyCertI.chainMassU, V.EnergyCertI.densI, V.EnergyCertI.jumpsI,
    V.EnergyCertI.IK.val, V.Q2Certificate.correctedLength,
    V.Q2Certificate.scaleLength, V.Q2Certificate.scaleMass,
    V.EnergyCertI.U]

set_option maxHeartbeats 2000000 in
theorem v13_q2_v_bounds :
    ∀ c ∈ v13ChainCells V.EnergyCertI.q2D.vp,
      (480367989919 : ℝ) / (5 * 10 ^ 13) ≤ c.left ∧ c.right ≤ 1 := by
  norm_num [V.EnergyCertI.q2D, V.EnergyCertI.mkIData, v13ChainCells,
    v13ChainCellsAux, V.EnergyCertI.chainCP, V.EnergyCertI.q2YHeader,
    V.EnergyCertI.q2YEntries, V.EnergyCertI.chainCoords,
    Li2Lean.V.Q2Certificate.decodeChain,
    Li2Lean.V.Q2Certificate.decodeChainAux,
    V.EnergyCertI.chainMassU, V.EnergyCertI.densI, V.EnergyCertI.jumpsI,
    V.EnergyCertI.IK.val, V.Q2Certificate.correctedLength,
    V.Q2Certificate.scaleLength, V.Q2Certificate.scaleMass,
    V.EnergyCertI.U]

set_option maxHeartbeats 2000000 in
theorem v13_q2_v_full_bounds :
    ∀ c ∈ v13ChainCells V.EnergyCertI.q2D.vp,
      (0 : ℝ) ≤ c.left ∧ c.right ≤ 1 := by
  norm_num [V.EnergyCertI.q2D, V.EnergyCertI.mkIData, v13ChainCells,
    v13ChainCellsAux, V.EnergyCertI.chainCP, V.EnergyCertI.q2YHeader,
    V.EnergyCertI.q2YEntries, V.EnergyCertI.chainCoords,
    Li2Lean.V.Q2Certificate.decodeChain,
    Li2Lean.V.Q2Certificate.decodeChainAux,
    V.EnergyCertI.chainMassU, V.EnergyCertI.densI, V.EnergyCertI.jumpsI,
    V.EnergyCertI.IK.val, V.Q2Certificate.correctedLength,
    V.Q2Certificate.scaleLength, V.Q2Certificate.scaleMass,
    V.EnergyCertI.U]

set_option maxHeartbeats 2000000 in
theorem v13_q5_v_bounds :
    ∀ c ∈ v13ChainCells V.EnergyCertI.q5D.vp,
      (480367989919 : ℝ) / (5 * 10 ^ 13) ≤ c.left ∧ c.right ≤ 1 := by
  norm_num [V.EnergyCertI.q5D, V.EnergyCertI.mkIData, v13ChainCells,
    v13ChainCellsAux, V.EnergyCertI.chainCP, V.EnergyCertI.q5YHeader,
    V.EnergyCertI.q5YEntries, V.EnergyCertI.chainCoords,
    Li2Lean.V.Q2Certificate.decodeChain,
    Li2Lean.V.Q2Certificate.decodeChainAux,
    V.EnergyCertI.chainMassU, V.EnergyCertI.densI, V.EnergyCertI.jumpsI,
    V.EnergyCertI.IK.val, V.Q2Certificate.correctedLength,
    V.Q2Certificate.scaleLength, V.Q2Certificate.scaleMass,
    V.EnergyCertI.U]

set_option maxHeartbeats 2000000 in
theorem v13_q5_v_full_bounds :
    ∀ c ∈ v13ChainCells V.EnergyCertI.q5D.vp,
      (0 : ℝ) ≤ c.left ∧ c.right ≤ 1 := by
  norm_num [V.EnergyCertI.q5D, V.EnergyCertI.mkIData, v13ChainCells,
    v13ChainCellsAux, V.EnergyCertI.chainCP, V.EnergyCertI.q5YHeader,
    V.EnergyCertI.q5YEntries, V.EnergyCertI.chainCoords,
    Li2Lean.V.Q2Certificate.decodeChain,
    Li2Lean.V.Q2Certificate.decodeChainAux,
    V.EnergyCertI.chainMassU, V.EnergyCertI.densI, V.EnergyCertI.jumpsI,
    V.EnergyCertI.IK.val, V.Q2Certificate.correctedLength,
    V.Q2Certificate.scaleLength, V.Q2Certificate.scaleMass,
    V.EnergyCertI.U]

set_option maxHeartbeats 2000000 in
theorem v13_q2_z_source_bounds :
    ∀ c ∈ v13ChainCells V.EnergyCertI.q2D.zp,
      (-2 : ℝ) ≤ c.left ∧ c.right ≤ -(3 / 5 : ℝ) := by
  norm_num [V.EnergyCertI.q2D, V.EnergyCertI.mkIData, v13ChainCells,
    v13ChainCellsAux, V.EnergyCertI.chainCP, V.EnergyCertI.q2ZHeader,
    V.EnergyCertI.q2ZEntries, V.EnergyCertI.chainCoords,
    Li2Lean.V.Q2Certificate.decodeChain,
    Li2Lean.V.Q2Certificate.decodeChainAux,
    V.EnergyCertI.chainMassU, V.EnergyCertI.densI, V.EnergyCertI.jumpsI,
    V.EnergyCertI.IK.val, V.Q2Certificate.correctedLength,
    V.Q2Certificate.scaleLength, V.Q2Certificate.scaleMass,
    V.EnergyCertI.U]

set_option maxHeartbeats 2000000 in
theorem v13_q5_z_source_bounds :
    ∀ c ∈ v13ChainCells V.EnergyCertI.q5D.zp,
      (-5 : ℝ) ≤ c.left ∧ c.right ≤ -(3 / 5 : ℝ) := by
  norm_num [V.EnergyCertI.q5D, V.EnergyCertI.mkIData, v13ChainCells,
    v13ChainCellsAux, V.EnergyCertI.chainCP, V.EnergyCertI.q5ZHeader,
    V.EnergyCertI.q5ZEntries, V.EnergyCertI.chainCoords,
    Li2Lean.V.Q2Certificate.decodeChain,
    Li2Lean.V.Q2Certificate.decodeChainAux,
    V.EnergyCertI.chainMassU, V.EnergyCertI.densI, V.EnergyCertI.jumpsI,
    V.EnergyCertI.IK.val, V.Q2Certificate.correctedLength,
    V.Q2Certificate.scaleLength, V.Q2Certificate.scaleMass,
    V.EnergyCertI.U]

end
end B3
end Li2Lean
