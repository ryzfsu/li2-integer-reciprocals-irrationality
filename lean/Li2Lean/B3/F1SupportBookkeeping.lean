/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.

Generic support bookkeeping for the measure-first signed-V route.  These
lemmas only propagate null complements through map, finite sum, and scalar
measure operations; they do not construct a signed-V reference measure.
-/

import Mathlib
import Li2Lean.P0.ConfigSegment
import Li2Lean.V.VLiteralContour

namespace Li2Lean

noncomputable section

namespace B3

open MeasureTheory Set
open scoped ENNReal
open Li2Lean.P0.ConfigSegment

/-! ## Generic null-complement transport -/

/-- A measurable image of a measure-full set carries the mapped measure.
The image-measurability hypothesis is necessary: a measurable map need not
send a Borel set to a measurable set. -/
theorem measure_map_image_compl_null
    {alpha beta : Type*} [MeasurableSpace alpha] [MeasurableSpace beta]
    (f : alpha → beta) (hf : Measurable f) (μ : Measure alpha)
    {T : Set alpha} (hT : MeasurableSet T)
    (himage : MeasurableSet (f '' T)) (hμ : μ Tᶜ = 0) :
    Measure.map f μ (f '' T)ᶜ = 0 := by
  rw [Measure.map_apply hf himage.compl]
  apply measure_mono_null
    (show f ⁻¹' (f '' T)ᶜ ⊆ Tᶜ by
      intro x hx hxt
      exact hx ⟨x, hxt, rfl⟩)
    hμ

/-- A measurable target superset is enough when the direct image is not known
to be measurable. -/
theorem measure_map_compl_null_of_subset
    {alpha beta : Type*} [MeasurableSpace alpha] [MeasurableSpace beta]
    (f : alpha → beta) (hf : Measurable f) (μ : Measure alpha)
    {T : Set alpha} {U : Set beta} (hU : MeasurableSet U)
    (hsub : f '' T ⊆ U) (hμ : μ Tᶜ = 0) :
    Measure.map f μ Uᶜ = 0 := by
  rw [Measure.map_apply hf hU.compl]
  apply measure_mono_null
    (show f ⁻¹' Uᶜ ⊆ Tᶜ by
      intro x hx hxt
      exact hx (hsub ⟨x, hxt, rfl⟩))
    hμ

/-- Finite sums preserve support in the union of the component supports. -/
theorem measure_sum_iUnion_compl_null
    {ι alpha : Type*} [MeasurableSpace alpha] [Countable ι]
    (μ : ι → Measure alpha) (S : ι → Set alpha)
    (hS : ∀ i, MeasurableSet (S i))
    (hμ : ∀ i, μ i (S i)ᶜ = 0) :
    (Measure.sum μ) (⋃ i, S i)ᶜ = 0 := by
  have hU : MeasurableSet (⋃ i, S i) := MeasurableSet.iUnion hS
  rw [Measure.sum_apply μ hU.compl]
  have hi : ∀ i, μ i (⋃ i, S i)ᶜ = 0 := by
    intro i
    apply measure_mono_null
      (Set.compl_subset_compl.mpr (Set.subset_iUnion S i))
      (hμ i)
  have hz : (fun i => μ i (⋃ i, S i)ᶜ) = (fun _ => 0) := funext hi
  rw [hz]
  exact tsum_zero

/-- Scalar multiplication preserves support. -/
theorem measure_smul_compl_null
    {alpha : Type*} [MeasurableSpace alpha]
    (c : ℝ≥0∞) (μ : Measure alpha) {S : Set alpha}
    (hS : MeasurableSet S) (hμ : μ Sᶜ = 0) :
    (c • μ) Sᶜ = 0 := by
  rw [Measure.smul_apply c μ Sᶜ]
  simp [hμ]

/-! ## The finite interval reference measure -/

/-- The piecewise-uniform reference measure is carried by any measurable set
containing every cell.  The cell hypotheses intentionally stay abstract so
the theorem does not claim endpoint arithmetic for a decoded table. -/
theorem referenceMeasure_compl_null_of_cells_subset
    (start : ℝ) (count : ℕ) (units : List ℕ) (T : Set ℝ)
    (hT : MeasurableSet T)
    (hcell : ∀ j ∈ Finset.range count,
      Set.Ico (referenceCellLeft start j) (referenceCellRight start j) ⊆ T) :
    referenceMeasure start count units Tᶜ = 0 := by
  unfold referenceMeasure
  rw [Measure.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro j hj
  rw [Measure.smul_apply]
  simp only [smul_eq_mul]
  apply mul_eq_zero_of_right
  rw [Measure.restrict_apply hT.compl]
  apply measure_mono_null
  · intro x hx
    exact hx.1 ((hcell j hj) hx.2)
  · exact measure_empty

/-- Widening half-open reference cells to closed cells is harmless for support
containment: only set inclusion is used, not an equality of measures. -/
theorem referenceMeasure_compl_null_of_closed_cells_subset
    (start : ℝ) (count : ℕ) (units : List ℕ) (T : Set ℝ)
    (hT : MeasurableSet T)
    (hcell : ∀ j ∈ Finset.range count,
      Set.Icc (referenceCellLeft start j) (referenceCellRight start j) ⊆ T) :
    referenceMeasure start count units Tᶜ = 0 := by
  apply referenceMeasure_compl_null_of_cells_subset start count units T hT
  intro j hj x hx
  exact hcell j hj ⟨hx.1, le_of_lt hx.2⟩

/-! ## The literal contour parameter support -/

theorem literalContourParameterMeasure_ae_mem :
    ∀ᵐ p : Fin 4 × ℝ ∂V.Literal.vContourParameterMeasure,
      p ∈ (Set.univ : Set (Fin 4)) ×ˢ Set.Icc (0 : ℝ) 1 := by
  have hmeasure :
      (Measure.count.prod volume).restrict
          ((Set.univ : Set (Fin 4)) ×ˢ Set.Icc (0 : ℝ) 1) =
        V.Literal.vContourParameterMeasure := by
    rw [← Measure.prod_restrict]
    simp [V.Literal.vContourParameterMeasure]
  rw [← hmeasure]
  exact ae_restrict_mem (MeasurableSet.univ.prod measurableSet_Icc)

theorem literalContourParameterMeasure_compl_null :
    V.Literal.vContourParameterMeasure
      (((Set.univ : Set (Fin 4)) ×ˢ Set.Icc (0 : ℝ) 1)ᶜ) = 0 := by
  exact (ae_iff.mp literalContourParameterMeasure_ae_mem)

end B3

end

end Li2Lean

#print axioms Li2Lean.B3.measure_map_image_compl_null
#print axioms Li2Lean.B3.measure_map_compl_null_of_subset
#print axioms Li2Lean.B3.measure_sum_iUnion_compl_null
#print axioms Li2Lean.B3.referenceMeasure_compl_null_of_closed_cells_subset
#print axioms Li2Lean.B3.literalContourParameterMeasure_compl_null
