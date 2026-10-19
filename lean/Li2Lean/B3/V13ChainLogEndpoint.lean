/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B3.V13ChainEnergy
import Li2Lean.Kit.LogSegment

namespace Li2Lean.B3

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open V.EnergyCertI
open V.EnergyCertI.IK

theorem integrable_v13ChainMeasure_of_continuousOn_cells
    (cells : List V13ChainCell) (f : ℝ → ℝ)
    (hcont : ∀ c ∈ cells, ContinuousOn f (Icc c.left c.right)) :
    Integrable f (v13ChainMeasure cells) := by
  induction cells with
  | nil => simp [v13ChainMeasure]
  | cons c cs ih =>
      have hc : c ∈ c :: cs := by simp
      have hrest : ∀ d ∈ cs, ContinuousOn f (Icc d.left d.right) := by
        intro d hd
        exact hcont d (by simp [hd])
      have hcell : Integrable f (volume.restrict (Ioc c.left c.right)) :=
        (hcont c hc).integrableOn_compact isCompact_Icc |>.mono_set Ioc_subset_Icc_self
      have hcell' : Integrable f
          (ENNReal.ofReal c.density • volume.restrict (Ioc c.left c.right)) :=
        hcell.smul_measure ENNReal.ofReal_ne_top
      have htail := ih hrest
      have hsplit : v13ChainMeasure (c :: cs) =
          ENNReal.ofReal c.density • volume.restrict (Ioc c.left c.right) +
            v13ChainMeasure cs := by
        simp [v13ChainMeasure]
      rw [hsplit]
      exact hcell'.add_measure htail

/-- A shifted logarithm is integrable against a finite piecewise-uniform
chain whose cells lie to the right of `-δ`. -/
theorem integrable_v13ChainMeasure_log_shift
    (cells : List V13ChainCell) (δ : ℝ) (hδ : 0 < δ)
    (hbounds : ∀ c ∈ cells, 0 ≤ c.left ∧ c.left ≤ c.right) :
    Integrable (fun x : ℝ => Real.log (x + δ)) (v13ChainMeasure cells) := by
  induction cells with
  | nil => simp [v13ChainMeasure]
  | cons c cs ih =>
      have hc : c ∈ c :: cs := by simp
      have hrest : ∀ d ∈ cs, 0 ≤ d.left ∧ d.left ≤ d.right := by
        intro d hd
        exact hbounds d (by simp [hd])
      have hbc := hbounds c hc
      have hcontArg : ContinuousOn (fun x : ℝ => x + δ) (Icc c.left c.right) :=
        continuousOn_id.add continuousOn_const
      have hmap : Set.MapsTo (fun x : ℝ => x + δ) (Icc c.left c.right) (Ioi 0) := by
        intro x hx
        simp only [Set.mem_Ioi]
        linarith [hbc.1, hx.1, hδ]
      have hmapNe : Set.MapsTo (fun x : ℝ => x + δ) (Icc c.left c.right)
          ({0} : Set ℝ)ᶜ := by
        intro x hx
        exact ne_of_gt (hmap hx)
      have hcont : ContinuousOn (fun x : ℝ => Real.log (x + δ))
          (Icc c.left c.right) :=
        Real.continuousOn_log.comp hcontArg hmapNe
      have hcell : Integrable (fun x : ℝ => Real.log (x + δ))
          (volume.restrict (Ioc c.left c.right)) :=
        hcont.integrableOn_compact isCompact_Icc |>.mono_set Ioc_subset_Icc_self
      have hcell' : Integrable (fun x : ℝ => Real.log (x + δ))
          (ENNReal.ofReal (c.density) • volume.restrict (Ioc c.left c.right)) :=
        hcell.smul_measure ENNReal.ofReal_ne_top
      have htail := ih hrest
      have hsplit : v13ChainMeasure (c :: cs) =
          ENNReal.ofReal c.density • volume.restrict (Ioc c.left c.right) +
            v13ChainMeasure cs := by
        simp [v13ChainMeasure]
      rw [hsplit]
      exact hcell'.add_measure htail

/-- The shifted-log integral of a piecewise-uniform chain is the sum of the
exact primitive differences on its cells. -/
theorem integral_v13ChainMeasure_log_shift
    (cells : List V13ChainCell) (δ : ℝ) (hδ : 0 < δ)
    (hbounds : ∀ c ∈ cells, 0 ≤ c.left ∧ c.left ≤ c.right)
    (hdensity : ∀ c ∈ cells, 0 ≤ c.density) :
    (∫ x : ℝ, Real.log (x + δ) ∂v13ChainMeasure cells) =
      (cells.map fun c => c.density *
        (LogSegment.primitive (c.right + δ) - LogSegment.primitive (c.left + δ))).sum := by
  induction cells with
  | nil => simp [v13ChainMeasure]
  | cons c cs ih =>
      have hc : c ∈ c :: cs := by simp
      have hrestB : ∀ d ∈ cs, 0 ≤ d.left ∧ d.left ≤ d.right := by
        intro d hd
        exact hbounds d (by simp [hd])
      have hrestD : ∀ d ∈ cs, 0 ≤ d.density := by
        intro d hd
        exact hdensity d (by simp [hd])
      have hbc := hbounds c hc
      have hdc := hdensity c hc
      have hcontArg : ContinuousOn (fun x : ℝ => x + δ) (Icc c.left c.right) :=
        continuousOn_id.add continuousOn_const
      have hmap : Set.MapsTo (fun x : ℝ => x + δ) (Icc c.left c.right) (Ioi 0) := by
        intro x hx
        simp only [Set.mem_Ioi]
        linarith [hbc.1, hx.1, hδ]
      have hmapNe : Set.MapsTo (fun x : ℝ => x + δ) (Icc c.left c.right)
          ({0} : Set ℝ)ᶜ := by
        intro x hx
        exact ne_of_gt (hmap hx)
      have hcont : ContinuousOn (fun x : ℝ => Real.log (x + δ))
          (Icc c.left c.right) :=
        Real.continuousOn_log.comp hcontArg hmapNe
      have hcell : Integrable (fun x : ℝ => Real.log (x + δ))
          (volume.restrict (Ioc c.left c.right)) :=
        hcont.integrableOn_compact isCompact_Icc |>.mono_set Ioc_subset_Icc_self
      have hcell' : Integrable (fun x : ℝ => Real.log (x + δ))
          (ENNReal.ofReal c.density • volume.restrict (Ioc c.left c.right)) :=
        hcell.smul_measure ENNReal.ofReal_ne_top
      have htailInt := integrable_v13ChainMeasure_log_shift cs δ hδ hrestB
      have hsplit : v13ChainMeasure (c :: cs) =
          ENNReal.ofReal c.density • volume.restrict (Ioc c.left c.right) +
            v13ChainMeasure cs := by
        simp [v13ChainMeasure]
      rw [hsplit, integral_add_measure hcell' htailInt,
        integral_smul_measure,
        ENNReal.toReal_ofReal hdc,
        smul_eq_mul]
      have hseg : (∫ x in Ioc c.left c.right, Real.log (x + δ)) =
          LogSegment.primitive (c.right + δ) -
            LogSegment.primitive (c.left + δ) := by
        rw [← intervalIntegral.integral_of_le hbc.2]
        simpa only [add_comm] using
          (LogSegment.integral_log_add δ c.left c.right)
      rw [hseg, ih hrestB hrestD]
      simp

def v13ChainRowsFirst : List CP → ℝ
  | [] => 0
  | p :: _ => val p.e

def v13ChainRowsLast : List CP → ℝ
  | [] => 0
  | [p] => val p.e
  | _ :: ps => v13ChainRowsLast ps

/-- Finite summation by parts for the decoded density prefix.  The initial
constant density is explicit; the neutral-jump specialization is obtained by
setting it to zero and using the closing jump. -/
theorem v13ChainCellsAux_log_primitive_sum
    (h δ : ℝ) (rows : List CP) :
    ((v13ChainCellsAux h rows).map fun c => c.density *
      (LogSegment.primitive (c.right + δ) -
        LogSegment.primitive (c.left + δ))).sum =
      h * (LogSegment.primitive (v13ChainRowsLast rows + δ) -
        LogSegment.primitive (v13ChainRowsFirst rows + δ)) +
      (rows.map fun p => val p.J *
        (LogSegment.primitive (v13ChainRowsLast rows + δ) -
          LogSegment.primitive (val p.e + δ))).sum := by
  induction rows generalizing h with
  | nil => simp [v13ChainCellsAux, v13ChainRowsFirst, v13ChainRowsLast]
  | cons c rows ih =>
      cases rows with
      | nil => simp [v13ChainCellsAux, v13ChainRowsFirst, v13ChainRowsLast]
      | cons d ds =>
          simp only [v13ChainCellsAux, List.map_cons, List.sum_cons,
            v13ChainRowsFirst, v13ChainRowsLast]
          have htail := ih (h + val c.J)
          simp only [v13ChainRowsFirst] at htail
          rw [htail]
          simp only [List.map_cons, List.sum_cons]
          ring_nf

/-! This is the first comparison needed for the endpoint disk in v13
`v-analytic.tex:449-462`.  The support and non-collision hypotheses are
kept explicit so the logarithm's totalized value at zero is never used. -/
theorem integral_chainMeasureComplex_log_norm_sub_le_shift
    (cells : List V13ChainCell) (δ : ℝ) (w : ℂ)
    (hδ : 0 < δ) (hw : ‖w‖ ≤ δ)
    (hbounds : ∀ c ∈ cells, 0 ≤ c.left ∧ c.left ≤ c.right)
    (hae_nonneg : ∀ᵐ x ∂v13ChainMeasure cells, 0 ≤ x)
    (hae_ne : ∀ᵐ x ∂v13ChainMeasure cells, w ≠ Complex.ofReal x)
    (hInt : Integrable (fun z : ℂ => Real.log ‖w - z‖)
      (v13ChainMeasureComplex cells)) :
    (∫ z : ℂ, Real.log ‖w - z‖ ∂v13ChainMeasureComplex cells) ≤
      ∫ x : ℝ, Real.log (x + δ) ∂v13ChainMeasure cells := by
  have hshiftInt : Integrable (fun x : ℝ => Real.log (x + δ))
      (v13ChainMeasure cells) := by
    exact integrable_v13ChainMeasure_log_shift cells δ hδ hbounds
  let hEmb := Complex.isometry_ofReal.isClosedEmbedding.measurableEmbedding
  have hmapInt : Integrable (fun x : ℝ =>
      Real.log ‖w - Complex.ofReal x‖) (v13ChainMeasure cells) := by
    have hmap : Integrable (fun z : ℂ => Real.log ‖w - z‖)
        (Measure.map Complex.ofReal (v13ChainMeasure cells)) := by
      simpa [v13ChainMeasureComplex] using hInt
    change Integrable ((fun z : ℂ => Real.log ‖w - z‖) ∘ Complex.ofReal)
      (v13ChainMeasure cells)
    exact (hEmb.integrable_map_iff (g := fun z : ℂ => Real.log ‖w - z‖)).mp hmap
  change (∫ z : ℂ, Real.log ‖w - z‖ ∂
      Measure.map Complex.ofReal (v13ChainMeasure cells)) ≤ _
  rw [hEmb.integral_map]
  apply integral_mono_ae hmapInt hshiftInt
  filter_upwards [hae_nonneg, hae_ne] with x hx hne
  have hnorm_pos : 0 < ‖w - Complex.ofReal x‖ := by
    exact norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hnorm : ‖w - Complex.ofReal x‖ ≤ x + δ := by
    calc
      ‖w - Complex.ofReal x‖ ≤ ‖w‖ + ‖Complex.ofReal x‖ := norm_sub_le _ _
      _ = ‖w‖ + x := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx]
      _ ≤ δ + x := by simpa only [add_comm] using add_le_add_left hw x
      _ = x + δ := add_comm _ _
  exact Real.log_le_log hnorm_pos hnorm

end

end Li2Lean.B3
