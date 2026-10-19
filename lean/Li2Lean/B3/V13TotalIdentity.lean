/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
import Li2Lean.B3.V13RowFacts
import Li2Lean.B3.V13CrossEnergy
import Li2Lean.B3.ReferenceDualIntegrable
import Li2Lean.B3.F3Ball

/-!
# Total Quadratic Energy Identity for v13 Reference Measures (`H6-S7`)

This module proves the `q`-generic total energy identity (`S7` on the H6 closure board):
for every decoded v13 reference source `R : V13DecodedRows q` satisfying `V13FieldRowFacts R`,
the 8-part measure interaction plan sum `v13InteractionPlanSum` equals the 7-kind evaluator row
sum `(allKinds.map fun k => ∑ i ∈ Finset.range (kindCount R.data k), vEnergyTerm q R.data k i).sum`.

## Main Theorems

* `v13_chain_cross_eq_rows`: cross logarithmic interaction of two decoded chains equals
  `∑ i ∈ Finset.range pts1.length, vEnergyCrossRow pts1 pts2 i`.
* `v13_chain_self_eq_rows`: self logarithmic interaction of a decoded chain equals
  `∑ i ∈ Finset.range rows.length, vEnergySelfRow rows i`.
* `v13_chain_poisson_eq_intPoi`: combined `z`-chain/Poisson and `v`-chain/Poisson interaction
  equals `∑ i ∈ Finset.range (kindCount R.data .intPoi), vEnergyTerm q R.data .intPoi i`.
* `v13_poisson_self_eq_pp`: self logarithmic interaction of the Poisson cloud equals
  `∑ i ∈ Finset.range (kindCount R.data .pp), vEnergyTerm q R.data .pp i`.
* `v13_evaluator_rows`: full 8-to-7 kind-map identity
  `v13InteractionPlanSum = (allKinds.map ...).sum`.
* `v13_total_fact_of_interaction`, `v13_total_fact_of_ballBound`, and `v13_total_fact`:
  `EnergyTotalSoundnessFact` for any `R : V13DecodedRows q`.
-/

namespace Li2Lean.B3

noncomputable section

open MeasureTheory Set Complex
open scoped ENNReal ComplexConjugate
open V
open V.EnergyCertI
open V.EnergyCertI.IK

/-! The reference measure module exposes the total mass theorem rather than a
probability instance.  Keep this small adapter local to the S7 proof. -/
private theorem isProbabilityMeasure_v13GlobalCirclePoissonMeasure {p : ℂ}
    (hp : ‖p‖ < v13GlobalPoissonRadius) :
    IsProbabilityMeasure (v13GlobalCirclePoissonMeasure p) :=
  ⟨v13GlobalCirclePoissonMeasure_univ hp⟩

instance instIsFiniteMeasure_v13ChainMeasure (cells : List V13ChainCell) :
    IsFiniteMeasure (v13ChainMeasure cells) :=
  v13ChainMeasure_isFinite cells

instance instIsFiniteMeasure_v13ChainMeasureComplex (cells : List V13ChainCell) :
    IsFiniteMeasure (v13ChainMeasureComplex cells) :=
  v13ChainMeasureComplex_isFinite cells

instance instIsFiniteMeasure_v13DecodedChainMeasure (rows : List CP) :
    IsFiniteMeasure (v13DecodedChainMeasure rows) :=
  v13ChainMeasureComplex_isFinite (v13ChainCells rows)

instance instIsFiniteMeasure_v13ZChain {q : ℕ} (R : V13DecodedRows q) :
    IsFiniteMeasure (v13ZChain R) :=
  v13ChainMeasureComplex_isFinite (v13ChainCells R.data.zp)

private theorem list_sum_neg_map {α : Type*} (l : List α) (f : α → ℝ) :
    (l.map (fun x => -f x)).sum = -(l.map f).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      ring

private theorem list_sum_two_mul {α : Type*} (l : List α) (f : α → ℝ) :
    (l.map (fun x => 2 * f x)).sum =
      (l.map f).sum + (l.map f).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      ring

private theorem list_sum_neg_mul_vEnergyG (p : CP) (l : List CP) :
    (l.map fun x => -IK.val p.J * IK.val x.J * vEnergyG (IK.val p.e - IK.val x.e)).sum =
      -(l.map fun x => IK.val p.J * IK.val x.J *
        vEnergyG (IK.val p.e - IK.val x.e)).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      ring

private theorem list_sum_two_self_vEnergyG (p : CP) (l : List CP) :
    (l.map fun x =>
      2 * IK.val p.J * IK.val x.J * vEnergyG (IK.val x.e - IK.val p.e)).sum =
      (l.map fun x => IK.val x.J * IK.val p.J * vEnergyG (IK.val x.e - IK.val p.e)).sum +
        (l.map fun x => IK.val x.J * IK.val p.J * vEnergyG (IK.val x.e - IK.val p.e)).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      ring

/-! ## Section 1: Logarithmic interaction kernel and product measure reductions -/

theorem vLogKernel_eq_log_norm_sub (z w : ℂ) :
    -li2LogKernel z w = Real.log ‖z - w‖ := by
  simp [li2LogKernel]

theorem vLogInteraction_eq_integral_log_norm_sub (μ ν : Measure ℂ) :
    V.vLogInteraction μ ν = ∫ p : ℂ × ℂ, Real.log ‖p.1 - p.2‖ ∂(μ.prod ν) := by
  unfold V.vLogInteraction li2LogInteraction
  rw [← integral_neg]
  simp only [vLogKernel_eq_log_norm_sub]

theorem vLogInteraction_symm (μ ν : Measure ℂ) [SFinite μ] [SFinite ν] :
    V.vLogInteraction μ ν = V.vLogInteraction ν μ := by
  unfold V.vLogInteraction
  rw [P0.L6Variations.li2LogInteraction_comm]

/-! ## Section 2: Chain cross and self interactions (`v13_chain_cross_eq_rows`, `v13_chain_self_eq_rows`) -/

private theorem integrable_log_abs_sub_v13ChainMeasure_prod_single
    (c1 : V13ChainCell) (hc1 : c1.left ≤ c1.right)
    (cells2 : List V13ChainCell) (hcells2 : ∀ c ∈ cells2, c.left ≤ c.right) :
    Integrable (fun p : ℝ × ℝ => Real.log |p.1 - p.2|)
      ((ENNReal.ofReal c1.density • volume.restrict (Ioc c1.left c1.right)).prod
        (v13ChainMeasure cells2)) := by
  induction cells2 with
  | nil =>
      simp [v13ChainMeasure]
  | cons c2 cs2 ih =>
      have hc2 : c2 ∈ c2 :: cs2 := by simp
      have hrest2 : ∀ d ∈ cs2, d.left ≤ d.right := fun d hd => hcells2 d (by simp [hd])
      have hsplit : v13ChainMeasure (c2 :: cs2) =
          ENNReal.ofReal c2.density • volume.restrict (Ioc c2.left c2.right) +
            v13ChainMeasure cs2 := by
        simp [v13ChainMeasure]
      letI : IsFiniteMeasure (v13ChainMeasure cs2) := v13ChainMeasure_isFinite cs2
      rw [hsplit, Measure.prod_add]
      have hrect : Integrable (fun p : ℝ × ℝ => Real.log |p.1 - p.2|)
          ((ENNReal.ofReal c1.density • volume.restrict (Ioc c1.left c1.right)).prod
            (ENNReal.ofReal c2.density • volume.restrict (Ioc c2.left c2.right))) := by
        rw [Measure.prod_smul_left, Measure.prod_smul_right]
        exact ((integrable_log_abs_sub_Ioc_rectangle hc1 (hcells2 c2 hc2)).smul_measure
          ENNReal.ofReal_ne_top).smul_measure ENNReal.ofReal_ne_top
      exact hrect.add_measure (ih hrest2)

theorem integrable_log_abs_sub_v13ChainMeasure_prod
    (cells1 cells2 : List V13ChainCell)
    (hcells1 : ∀ c ∈ cells1, c.left ≤ c.right)
    (hcells2 : ∀ c ∈ cells2, c.left ≤ c.right) :
    Integrable (fun p : ℝ × ℝ => Real.log |p.1 - p.2|)
      ((v13ChainMeasure cells1).prod (v13ChainMeasure cells2)) := by
  letI : IsFiniteMeasure (v13ChainMeasure cells2) := v13ChainMeasure_isFinite cells2
  induction cells1 with
  | nil =>
      simp [v13ChainMeasure]
  | cons c1 cs1 ih =>
      have hc1 : c1 ∈ c1 :: cs1 := by simp
      have hrest1 : ∀ d ∈ cs1, d.left ≤ d.right := fun d hd => hcells1 d (by simp [hd])
      have hsplit : v13ChainMeasure (c1 :: cs1) =
          ENNReal.ofReal c1.density • volume.restrict (Ioc c1.left c1.right) +
            v13ChainMeasure cs1 := by
        simp [v13ChainMeasure]
      letI : IsFiniteMeasure (v13ChainMeasure cs1) := v13ChainMeasure_isFinite cs1
      rw [hsplit, Measure.add_prod]
      exact (integrable_log_abs_sub_v13ChainMeasure_prod_single c1 (hcells1 c1 hc1)
        cells2 hcells2).add_measure (ih hrest1)

private theorem integral_v13ChainMeasure_log_abs_sub_eq_primitive_sum
    (rows : List CP) (x : ℝ)
    (hbounds : ∀ c ∈ v13ChainCells rows, c.left ≤ c.right)
    (hdensity : ∀ c ∈ v13ChainCells rows, 0 ≤ c.density)
    (hjump : (rows.map fun p => IK.val p.J).sum = 0) :
    (∫ y : ℝ, Real.log |x - y| ∂v13ChainMeasure (v13ChainCells rows)) =
      (rows.map fun l => IK.val l.J * LogSegment.primitive (x - IK.val l.e)).sum := by
  have h := integral_v13ChainMeasure_log_norm_sub_complex (v13ChainCells rows) (x : ℂ) hbounds hdensity
  have hcongr : (∫ y : ℝ, Real.log ‖(x : ℂ) - (y : ℂ)‖ ∂v13ChainMeasure (v13ChainCells rows)) =
      ∫ y : ℝ, Real.log |x - y| ∂v13ChainMeasure (v13ChainCells rows) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp [← Complex.ofReal_sub, Complex.norm_real]
  rw [hcongr] at h
  rw [h]
  simp only [Complex.ofReal_re, Complex.ofReal_im]
  rw [v13ChainCells_diff_sum (fun u => vEnergyA (u - x) 0) rows hjump]
  have hvA (s : ℝ) : vEnergyA s 0 = LogSegment.primitive s := by
    by_cases hs : s = 0
    · simp [vEnergyA, hs, LogSegment.primitive]
    · simp [vEnergyA, hs, LogSegment.primitive]
      ring
  have hmap : (rows.map fun l => IK.val l.J * vEnergyA (IK.val l.e - x) 0) =
      rows.map (fun l => -(IK.val l.J * LogSegment.primitive (x - IK.val l.e))) := by
    refine List.map_congr_left (fun l _ => ?_)
    have hneg : LogSegment.primitive (IK.val l.e - x) =
        -LogSegment.primitive (x - IK.val l.e) := by
      rw [show IK.val l.e - x = -(x - IK.val l.e) by ring, primitive_neg]
    rw [hvA, hneg]
    ring
  have hsum : (rows.map fun l => -(IK.val l.J * LogSegment.primitive (x - IK.val l.e))).sum =
      -(rows.map fun l => IK.val l.J * LogSegment.primitive (x - IK.val l.e)).sum :=
    list_sum_neg_map rows (fun l => IK.val l.J * LogSegment.primitive (x - IK.val l.e))
  rw [hmap, hsum, neg_neg]

private theorem integrableOn_Ioc_primitive_jump_sum
    (pts : List CP) {α β : ℝ} (_hαβ : α ≤ β) :
    IntegrableOn (fun x : ℝ => (pts.map fun l => IK.val l.J * LogSegment.primitive (x - IK.val l.e)).sum)
      (Ioc α β) volume := by
  have hcont : Continuous (fun x : ℝ =>
      (pts.map fun l => IK.val l.J * LogSegment.primitive (x - IK.val l.e)).sum) := by
    induction pts with
    | nil =>
        simp only [List.map_nil, List.sum_nil]
        exact continuous_const
    | cons l ls ih =>
        simp only [List.map_cons, List.sum_cons]
        have hterm : Continuous (fun x : ℝ => IK.val l.J * LogSegment.primitive (x - IK.val l.e)) :=
          continuous_const.mul (LogSegment.continuous_primitive.comp (continuous_id.sub continuous_const))
        exact hterm.add ih
  exact (hcont.integrableOn_Icc).mono_set Ioc_subset_Icc_self

private theorem integral_Ioc_primitive_jump_sum
    (pts : List CP) {α β : ℝ} (hαβ : α ≤ β) :
    (∫ x in Ioc α β, (pts.map fun l => IK.val l.J * LogSegment.primitive (x - IK.val l.e)).sum) =
      (pts.map fun l => IK.val l.J * vEnergyG (β - IK.val l.e)).sum -
        (pts.map fun l => IK.val l.J * vEnergyG (α - IK.val l.e)).sum := by
  rw [← intervalIntegral.integral_of_le hαβ]
  induction pts with
  | nil => simp
  | cons l ls ih =>
      simp only [List.map_cons, List.sum_cons]
      have hInt1 : IntervalIntegrable
          (fun x : ℝ => IK.val l.J * LogSegment.primitive (x - IK.val l.e)) volume α β :=
        (continuous_const.mul
          (LogSegment.continuous_primitive.comp (continuous_id.sub continuous_const))).intervalIntegrable α β
      have hInt2 : IntervalIntegrable
          (fun x : ℝ => (ls.map fun p => IK.val p.J * LogSegment.primitive (x - IK.val p.e)).sum)
          volume α β :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le hαβ).mpr
          (integrableOn_Ioc_primitive_jump_sum ls hαβ)
      rw [intervalIntegral.integral_add hInt1 hInt2, ih,
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_comp_sub_right LogSegment.primitive _,
        LogSegment.integral_primitive,
        ← vEnergyG_eq_secondPrimitive, ← vEnergyG_eq_secondPrimitive]
      ring

private theorem integrable_v13ChainMeasure_primitive_jump_sum
    (cells : List V13ChainCell) (pts : List CP)
    (hbounds : ∀ c ∈ cells, c.left ≤ c.right) :
    Integrable (fun x : ℝ => (pts.map fun l => IK.val l.J * LogSegment.primitive (x - IK.val l.e)).sum)
      (v13ChainMeasure cells) := by
  induction cells with
  | nil => simp [v13ChainMeasure]
  | cons c cs ih =>
      have hc : c ∈ c :: cs := by simp
      have hrest : ∀ d ∈ cs, d.left ≤ d.right := fun d hd => hbounds d (by simp [hd])
      have hcell : Integrable
          (fun x : ℝ => (pts.map fun l => IK.val l.J * LogSegment.primitive (x - IK.val l.e)).sum)
          (ENNReal.ofReal c.density • volume.restrict (Ioc c.left c.right)) :=
        (integrableOn_Ioc_primitive_jump_sum pts (hbounds c hc)).integrable.smul_measure
          ENNReal.ofReal_ne_top
      have hsplit : v13ChainMeasure (c :: cs) =
          ENNReal.ofReal c.density • volume.restrict (Ioc c.left c.right) +
            v13ChainMeasure cs := by
        simp [v13ChainMeasure]
      rw [hsplit]
      exact hcell.add_measure (ih hrest)

private theorem integral_v13ChainMeasure_primitive_jump_sum
    (cells : List V13ChainCell) (pts : List CP)
    (hbounds : ∀ c ∈ cells, c.left ≤ c.right)
    (hdensity : ∀ c ∈ cells, 0 ≤ c.density) :
    (∫ x : ℝ, (pts.map fun l => IK.val l.J * LogSegment.primitive (x - IK.val l.e)).sum
        ∂v13ChainMeasure cells) =
      (cells.map fun c => c.density *
        ((pts.map fun l => IK.val l.J * vEnergyG (c.right - IK.val l.e)).sum -
          (pts.map fun l => IK.val l.J * vEnergyG (c.left - IK.val l.e)).sum)).sum := by
  induction cells with
  | nil => simp [v13ChainMeasure]
  | cons c cs ih =>
      have hc : c ∈ c :: cs := by simp
      have hrestB : ∀ d ∈ cs, d.left ≤ d.right := fun d hd => hbounds d (by simp [hd])
      have hrestD : ∀ d ∈ cs, 0 ≤ d.density := fun d hd => hdensity d (by simp [hd])
      have hcell : Integrable
          (fun x : ℝ => (pts.map fun l => IK.val l.J * LogSegment.primitive (x - IK.val l.e)).sum)
          (ENNReal.ofReal c.density • volume.restrict (Ioc c.left c.right)) :=
        (integrableOn_Ioc_primitive_jump_sum pts (hbounds c hc)).integrable.smul_measure
          ENNReal.ofReal_ne_top
      have htail := integrable_v13ChainMeasure_primitive_jump_sum cs pts hrestB
      have hsplit : v13ChainMeasure (c :: cs) =
          ENNReal.ofReal c.density • volume.restrict (Ioc c.left c.right) +
            v13ChainMeasure cs := by
        simp [v13ChainMeasure]
      rw [hsplit, integral_add_measure hcell htail,
        integral_smul_measure, ENNReal.toReal_ofReal (hdensity c hc), smul_eq_mul,
        integral_Ioc_primitive_jump_sum pts (hbounds c hc), ih hrestB hrestD]
      simp

/-- Cross logarithmic interaction of two decoded chains equals the sum of `vEnergyCrossRow`. -/
theorem v13_chain_cross_eq_rows (pts1 pts2 : List CP)
    (hcells1 : ∀ c ∈ v13ChainCells pts1, c.left ≤ c.right ∧ 0 ≤ c.density)
    (hjump1 : (pts1.map fun p => IK.val p.J).sum = 0)
    (hcells2 : ∀ c ∈ v13ChainCells pts2, c.left ≤ c.right ∧ 0 ≤ c.density)
    (hjump2 : (pts2.map fun p => IK.val p.J).sum = 0) :
    V.vLogInteraction (v13DecodedChainMeasure pts1) (v13DecodedChainMeasure pts2) =
      ∑ i ∈ Finset.range pts1.length, vEnergyCrossRow pts1 pts2 i := by
  rw [vLogInteraction_eq_integral_log_norm_sub]
  let hEmb := Complex.isometry_ofReal.isClosedEmbedding.measurableEmbedding
  have hprod_map :
      (∫ p : ℂ × ℂ, Real.log ‖p.1 - p.2‖
          ∂((v13DecodedChainMeasure pts1).prod (v13DecodedChainMeasure pts2))) =
        ∫ p : ℝ × ℝ, Real.log |p.1 - p.2|
          ∂((v13ChainMeasure (v13ChainCells pts1)).prod (v13ChainMeasure (v13ChainCells pts2))) := by
    unfold v13DecodedChainMeasure v13ChainMeasureComplex
    letI : IsFiniteMeasure (v13DecodedChainMeasure pts1) :=
      v13ChainMeasureComplex_isFinite _
    letI : IsFiniteMeasure (v13DecodedChainMeasure pts2) :=
      v13ChainMeasureComplex_isFinite _
    rw [Measure.map_prod_map _ _ hEmb.measurable hEmb.measurable,
      (hEmb.prodMap hEmb).integral_map]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    simp [Prod.map, ← Complex.ofReal_sub, Complex.norm_real]
  rw [hprod_map]
  letI : IsFiniteMeasure (v13ChainMeasure (v13ChainCells pts1)) :=
    v13ChainMeasure_isFinite _
  letI : IsFiniteMeasure (v13ChainMeasure (v13ChainCells pts2)) :=
    v13ChainMeasure_isFinite _
  have hIntProd := integrable_log_abs_sub_v13ChainMeasure_prod
    (v13ChainCells pts1) (v13ChainCells pts2)
    (fun c hc => (hcells1 c hc).1) (fun c hc => (hcells2 c hc).1)
  rw [integral_prod _ hIntProd]
  have hinner : ∀ x : ℝ,
      (∫ y : ℝ, Real.log |x - y| ∂v13ChainMeasure (v13ChainCells pts2)) =
        (pts2.map fun l => IK.val l.J * LogSegment.primitive (x - IK.val l.e)).sum :=
    fun x => integral_v13ChainMeasure_log_abs_sub_eq_primitive_sum pts2 x
      (fun c hc => (hcells2 c hc).1) (fun c hc => (hcells2 c hc).2) hjump2
  simp_rw [hinner]
  rw [integral_v13ChainMeasure_primitive_jump_sum (v13ChainCells pts1) pts2
    (fun c hc => (hcells1 c hc).1) (fun c hc => (hcells1 c hc).2)]
  rw [v13ChainCells_diff_sum
    (fun u => (pts2.map fun l => IK.val l.J * vEnergyG (u - IK.val l.e)).sum) pts1 hjump1]
  rw [vEnergyCrossRows_eq_expanded_jump_sum]
  have hinner_neg (p : CP) :
      (pts2.map fun l => -IK.val p.J * IK.val l.J * vEnergyG (IK.val p.e - IK.val l.e)).sum =
        -(IK.val p.J * (pts2.map fun l => IK.val l.J *
          vEnergyG (IK.val p.e - IK.val l.e)).sum) := by
    rw [show (pts2.map fun l => -IK.val p.J * IK.val l.J *
        vEnergyG (IK.val p.e - IK.val l.e)).sum =
        -(pts2.map fun l => IK.val p.J * IK.val l.J *
          vEnergyG (IK.val p.e - IK.val l.e)).sum by
          exact list_sum_neg_mul_vEnergyG p pts2]
    rw [← List.sum_map_mul_left]
    simp [mul_assoc]
  have hmap :
      pts1.map (fun p =>
        (pts2.map fun l => -IK.val p.J * IK.val l.J *
          vEnergyG (IK.val p.e - IK.val l.e)).sum) =
      pts1.map (fun p => -(IK.val p.J *
        (pts2.map fun l => IK.val l.J * vEnergyG (IK.val p.e - IK.val l.e)).sum)) := by
    refine List.map_congr_left (fun p _ => hinner_neg p)
  rw [hmap, list_sum_neg_map]

private theorem vEnergyG_zero : vEnergyG 0 = 0 := by
  simp [vEnergyG]

private theorem vEnergyG_neg (s : ℝ) : vEnergyG (-s) = vEnergyG s := by
  unfold vEnergyG
  by_cases hs : s = 0
  · subst hs; simp
  · have hns : -s ≠ 0 := neg_ne_zero.mpr hs
    rw [if_neg hns, if_neg hs, abs_neg]
    ring

private theorem vEnergySelfRow_cons_succ (p : CP) (tl : List CP) (k : ℕ) :
    vEnergySelfRow (p :: tl) (k + 1) = vEnergySelfRow tl k := by
  unfold vEnergySelfRow
  simp

private theorem vEnergySelfRow_cons_zero (p : CP) (tl : List CP) :
    vEnergySelfRow (p :: tl) 0 =
      - ((tl.map fun pl =>
        2 * IK.val p.J * IK.val pl.J * vEnergyG (IK.val pl.e - IK.val p.e)).sum) := by
  unfold vEnergySelfRow
  dsimp only [List.drop]
  induction tl with
  | nil => simp
  | cons l ls ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      ring

theorem sum_vEnergySelfRow_eq_expanded_jump_sum (rows : List CP) :
    (∑ i ∈ Finset.range rows.length, vEnergySelfRow rows i) =
      - (rows.map fun p =>
        (rows.map fun l =>
          IK.val p.J * IK.val l.J * vEnergyG (IK.val p.e - IK.val l.e)).sum).sum := by
  induction rows with
  | nil => simp
  | cons p tl ih =>
      rw [List.length_cons, Finset.sum_range_succ']
      simp_rw [vEnergySelfRow_cons_succ]
      rw [ih]
      have h0 : vEnergySelfRow (p :: tl) 0 =
          - ((tl.map fun pl =>
            2 * IK.val p.J * IK.val pl.J * vEnergyG (IK.val pl.e - IK.val p.e)).sum) :=
        vEnergySelfRow_cons_zero p tl
      rw [h0]
      simp only [List.map_cons, List.sum_cons, sub_self, vEnergyG_zero, mul_zero, zero_add]
      have hcol : (tl.map fun q =>
            IK.val q.J * IK.val p.J * vEnergyG (IK.val q.e - IK.val p.e) +
              (tl.map fun l => IK.val q.J * IK.val l.J * vEnergyG (IK.val q.e - IK.val l.e)).sum).sum =
          (tl.map fun q => IK.val q.J * IK.val p.J * vEnergyG (IK.val q.e - IK.val p.e)).sum +
            (tl.map fun q =>
              (tl.map fun l => IK.val q.J * IK.val l.J * vEnergyG (IK.val q.e - IK.val l.e)).sum).sum := by
        rw [← List.sum_map_add]
      rw [hcol]
      have hrow : (tl.map fun l => IK.val p.J * IK.val l.J * vEnergyG (IK.val p.e - IK.val l.e)) =
          tl.map (fun l => IK.val l.J * IK.val p.J * vEnergyG (IK.val l.e - IK.val p.e)) := by
        refine List.map_congr_left (fun l _ => ?_)
        have hsymm : vEnergyG (IK.val p.e - IK.val l.e) = vEnergyG (IK.val l.e - IK.val p.e) := by
          rw [show IK.val p.e - IK.val l.e = -(IK.val l.e - IK.val p.e) by ring, vEnergyG_neg]
        rw [hsymm]
        ring
      have htwo : (tl.map fun pl =>
            2 * IK.val p.J * IK.val pl.J * vEnergyG (IK.val pl.e - IK.val p.e)).sum =
          (tl.map fun l => IK.val l.J * IK.val p.J * vEnergyG (IK.val l.e - IK.val p.e)).sum +
            (tl.map fun l => IK.val l.J * IK.val p.J * vEnergyG (IK.val l.e - IK.val p.e)).sum := by
        exact list_sum_two_self_vEnergyG p tl
      rw [hrow, htwo]
      ring

/-- Self logarithmic interaction of a decoded chain equals the sum of `vEnergySelfRow`. -/
theorem v13_chain_self_eq_rows (rows : List CP)
    (hcells : ∀ c ∈ v13ChainCells rows, c.left ≤ c.right ∧ 0 ≤ c.density)
    (hjump : (rows.map fun p => IK.val p.J).sum = 0) :
    V.vLogInteraction (v13DecodedChainMeasure rows) (v13DecodedChainMeasure rows) =
      ∑ i ∈ Finset.range rows.length, vEnergySelfRow rows i := by
  rw [v13_chain_cross_eq_rows rows rows hcells hjump hcells hjump,
    vEnergyCrossRows_eq_expanded_jump_sum, sum_vEnergySelfRow_eq_expanded_jump_sum]
  have hmap : rows.map (fun p =>
      (rows.map fun l => -IK.val p.J * IK.val l.J *
        vEnergyG (IK.val p.e - IK.val l.e)).sum) =
      rows.map (fun p => -((rows.map fun l => IK.val p.J * IK.val l.J *
        vEnergyG (IK.val p.e - IK.val l.e)).sum)) := by
    refine List.map_congr_left (fun p _ => list_sum_neg_mul_vEnergyG p rows)
  rw [hmap, list_sum_neg_map]

/-! ## Section 3: Product integrability with `v13GlobalCirclePoissonMeasure` -/

private theorem integral_v13GlobalCirclePoissonMeasure_log_norm_sub_ge
    {p : ℂ} (hp : ‖p‖ < v13GlobalPoissonRadius) (w : ℂ) :
    Real.log ((3 / 5 : ℝ) - ‖p‖) ≤
      ∫ z : ℂ, Real.log ‖w - z‖ ∂v13GlobalCirclePoissonMeasure p := by
  have hp_lt : ‖p‖ < (3 / 5 : ℝ) := by simpa [v13GlobalPoissonRadius] using hp
  have hsub_pos : 0 < (3 / 5 : ℝ) - ‖p‖ := sub_pos.mpr hp_lt
  by_cases hw : (3 / 5 : ℝ) ≤ ‖w‖
  · rw [integral_v13GlobalCirclePoissonMeasure_outside_complex hp hw]
    have htri := norm_sub_norm_le w p
    have hwp_ge : (3 / 5 : ℝ) - ‖p‖ ≤ ‖w - p‖ := by linarith
    have hwp_pos : 0 < ‖w - p‖ := lt_of_lt_of_le hsub_pos hwp_ge
    have hsq : (w.re - p.re) ^ 2 + (w.im - p.im) ^ 2 = ‖w - p‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.sub_im]
      ring
    rw [hsq, Real.log_pow, Nat.cast_ofNat]
    have hlog := Real.log_le_log hsub_pos hwp_ge
    linarith
  · push_neg at hw
    rw [integral_v13GlobalCirclePoissonMeasure_inside_complex hp (le_of_lt hw)]
    have hsq : (9 / 25 - (p.re * w.re + p.im * w.im)) ^ 2 + (p.re * w.im - p.im * w.re) ^ 2 =
        ‖((9 / 25 : ℝ) : ℂ) - conj w * p‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
        Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
      ring
    have htri := norm_sub_norm_le ((9 / 25 : ℝ) : ℂ) (conj w * p)
    have h925 : ‖((9 / 25 : ℝ) : ℂ)‖ = (9 / 25 : ℝ) := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num)]
    have hprod_le : ‖conj w * p‖ ≤ (3 / 5 : ℝ) * ‖p‖ := by
      rw [norm_mul, norm_conj]
      exact mul_le_mul_of_nonneg_right (le_of_lt hw) (norm_nonneg p)
    have hge : (3 / 5 : ℝ) * ((3 / 5 : ℝ) - ‖p‖) ≤ ‖((9 / 25 : ℝ) : ℂ) - conj w * p‖ := by
      linarith
    have hpos : 0 < (3 / 5 : ℝ) * ((3 / 5 : ℝ) - ‖p‖) := mul_pos (by norm_num) hsub_pos
    have hlog := Real.log_le_log hpos hge
    rw [Real.log_mul (by norm_num) (ne_of_gt hsub_pos)] at hlog
    rw [hsq, Real.log_pow, Nat.cast_ofNat]
    linarith

private theorem ae_norm_eq_v13GlobalCirclePoissonMeasure (p : ℂ) :
    ∀ᵐ z ∂v13GlobalCirclePoissonMeasure p, ‖z‖ = (3 / 5 : ℝ) := by
  let μ0 := volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))
  have hmeas_d : Measurable (v13GlobalPoissonAngleDensity p) := by
    unfold v13GlobalPoissonAngleDensity poissonKernel
    fun_prop
  unfold v13GlobalCirclePoissonMeasure
  rw [ae_map_iff (continuous_circleMap 0 v13GlobalPoissonRadius).aemeasurable
    (measurableSet_eq_fun measurable_norm measurable_const)]
  refine Filter.Eventually.of_forall (fun θ => ?_)
  simp [circleMap, v13GlobalPoissonRadius]

private theorem ae_ne_v13GlobalCirclePoissonMeasure
    {p : ℂ} (hp : ‖p‖ < v13GlobalPoissonRadius) (w : ℂ) :
    ∀ᵐ z ∂v13GlobalCirclePoissonMeasure p, w ≠ z := by
  let μ0 := volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))
  let r := v13GlobalPoissonRadius
  let a := w / (r : ℂ)
  have hmeas_d : Measurable (v13GlobalPoissonAngleDensity p) := by
    unfold v13GlobalPoissonAngleDensity poissonKernel
    fun_prop
  unfold v13GlobalCirclePoissonMeasure
  have hmap : ∀ᵐ z ∂Measure.map (circleMap 0 v13GlobalPoissonRadius)
      ((volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))).withDensity
        (fun θ => ENNReal.ofReal (v13GlobalPoissonAngleDensity p θ))),
      z ∉ ({w} : Set ℂ) := by
    apply (ae_map_iff (continuous_circleMap 0 v13GlobalPoissonRadius).aemeasurable
      (measurableSet_singleton w).compl).2
    rw [ae_withDensity_iff hmeas_d.ennreal_ofReal]
    filter_upwards [P0.ae_circleMap_ne a μ0] with θ hθ _ hweq
    apply hθ
    have hfactor : w - circleMap 0 r θ = -(r : ℂ) * (circleMap 0 1 θ - a) := by
      dsimp [a, r, v13GlobalPoissonRadius, circleMap]
      push_cast
      ring
    rw [hweq, sub_self] at hfactor
    have hr : (r : ℂ) ≠ 0 := by norm_num [r, v13GlobalPoissonRadius]
    rcases mul_eq_zero.mp hfactor.symm with hneg | hsub
    · exact False.elim (hr (neg_eq_zero.mp hneg))
    · exact sub_eq_zero.mp hsub
  simpa only [Set.mem_singleton_iff, ne_eq, eq_comm] using hmap

private theorem integral_norm_log_norm_sub_v13GlobalCirclePoissonMeasure_le
    {p : ℂ} (hp : ‖p‖ < v13GlobalPoissonRadius) (w : ℂ) :
    ‖∫ z : ℂ, ‖Real.log ‖w - z‖‖ ∂v13GlobalCirclePoissonMeasure p‖ ≤
      2 * (‖w‖ + (3 / 5 : ℝ)) - Real.log ((3 / 5 : ℝ) - ‖p‖) := by
  have hnonneg : 0 ≤ ∫ z : ℂ, ‖Real.log ‖w - z‖‖ ∂v13GlobalCirclePoissonMeasure p :=
    integral_nonneg (fun _ => norm_nonneg _)
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  have hIntLog := integrable_v13GlobalCirclePoissonMeasure_log_norm_sub_complex hp w
  have hIntConst : Integrable (fun _ : ℂ => 2 * (‖w‖ + (3 / 5 : ℝ)))
      (v13GlobalCirclePoissonMeasure p) := by
    haveI := isProbabilityMeasure_v13GlobalCirclePoissonMeasure hp
    exact integrable_const _
  have hle : (∫ z : ℂ, ‖Real.log ‖w - z‖‖ ∂v13GlobalCirclePoissonMeasure p) ≤
      ∫ z : ℂ, (2 * (‖w‖ + (3 / 5 : ℝ)) - Real.log ‖w - z‖)
        ∂v13GlobalCirclePoissonMeasure p := by
    apply integral_mono_ae hIntLog.norm (hIntConst.sub hIntLog)
    filter_upwards [ae_norm_eq_v13GlobalCirclePoissonMeasure p,
      ae_ne_v13GlobalCirclePoissonMeasure hp w] with z hz hne
    have hpos : 0 < ‖w - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    have hlog_le1 : Real.log ‖w - z‖ ≤ ‖w - z‖ - 1 := Real.log_le_sub_one_of_pos hpos
    have htri : ‖w - z‖ ≤ ‖w‖ + (3 / 5 : ℝ) := by
      have h := norm_sub_le w z
      linarith [hz]
    have hM_nonneg : 0 ≤ ‖w‖ + (3 / 5 : ℝ) := by positivity
    rw [Real.norm_eq_abs, abs_le]
    change -(2 * (‖w‖ + (3 / 5 : ℝ)) - Real.log ‖w - z‖) ≤
      Real.log ‖w - z‖ ∧ Real.log ‖w - z‖ ≤
        2 * (‖w‖ + (3 / 5 : ℝ)) - Real.log ‖w - z‖
    have hlog_leM : Real.log ‖w - z‖ ≤ ‖w‖ + (3 / 5 : ℝ) := by
      linarith [hlog_le1, htri]
    constructor <;> linarith
  have hprob : (∫ _ : ℂ, 2 * (‖w‖ + (3 / 5 : ℝ)) ∂v13GlobalCirclePoissonMeasure p) =
      2 * (‖w‖ + (3 / 5 : ℝ)) := by
    haveI := isProbabilityMeasure_v13GlobalCirclePoissonMeasure hp
    simp
  rw [integral_sub hIntConst hIntLog, hprob] at hle
  have hge := integral_v13GlobalCirclePoissonMeasure_log_norm_sub_ge hp w
  linarith

private theorem integrable_linear_norm_v13DecodedChainMeasure
    (rows : List CP) (a b : ℝ) :
    Integrable (fun w : ℂ => a * ‖w‖ + b) (v13DecodedChainMeasure rows) := by
  let hEmb := Complex.isometry_ofReal.isClosedEmbedding.measurableEmbedding
  unfold v13DecodedChainMeasure v13ChainMeasureComplex
  rw [hEmb.integrable_map_iff]
  have hcont : Continuous (fun u : ℝ => a * ‖(u : ℂ)‖ + b) := by fun_prop
  suffices ∀ cells : List V13ChainCell,
      Integrable (fun u : ℝ => a * ‖(u : ℂ)‖ + b) (v13ChainMeasure cells) from
    this (v13ChainCells rows)
  intro cells
  induction cells with
  | nil => simp [v13ChainMeasure]
  | cons c cs ih =>
      have hcell : Integrable (fun u : ℝ => a * ‖(u : ℂ)‖ + b)
          (ENNReal.ofReal c.density • volume.restrict (Ioc c.left c.right)) :=
        ((hcont.integrableOn_Icc).mono_set Ioc_subset_Icc_self).integrable.smul_measure
          ENNReal.ofReal_ne_top
      have hsplit : v13ChainMeasure (c :: cs) =
          ENNReal.ofReal c.density • volume.restrict (Ioc c.left c.right) +
            v13ChainMeasure cs := by
        simp [v13ChainMeasure]
      rw [hsplit]
      exact hcell.add_measure ih

private theorem integrable_linear_norm_v13GlobalCirclePoissonMeasure
    {p1 : ℂ} (hp1 : ‖p1‖ < v13GlobalPoissonRadius) (a b : ℝ) :
    Integrable (fun w : ℂ => a * ‖w‖ + b) (v13GlobalCirclePoissonMeasure p1) := by
  haveI := isProbabilityMeasure_v13GlobalCirclePoissonMeasure hp1
  have hconst : Integrable (fun _ : ℂ => a * (3 / 5 : ℝ) + b)
      (v13GlobalCirclePoissonMeasure p1) := integrable_const _
  refine hconst.congr ?_
  filter_upwards [ae_norm_eq_v13GlobalCirclePoissonMeasure p1] with w hw
  rw [hw]

private theorem integrable_log_norm_sub_chain_poisson_single
    (rows : List CP) {p : ℂ} (hp : ‖p‖ < v13GlobalPoissonRadius) :
    Integrable (fun q : ℂ × ℂ => Real.log ‖q.1 - q.2‖)
      ((v13DecodedChainMeasure rows).prod (v13GlobalCirclePoissonMeasure p)) := by
  haveI := isProbabilityMeasure_v13GlobalCirclePoissonMeasure hp
  have hmeas : AEStronglyMeasurable (fun q : ℂ × ℂ => Real.log ‖q.1 - q.2‖)
      ((v13DecodedChainMeasure rows).prod (v13GlobalCirclePoissonMeasure p)) :=
    (by fun_prop : Measurable (fun q : ℂ × ℂ => Real.log ‖q.1 - q.2‖)).aestronglyMeasurable
  rw [integrable_prod_iff hmeas]
  refine ⟨Filter.Eventually.of_forall (fun w =>
    integrable_v13GlobalCirclePoissonMeasure_log_norm_sub_complex hp w), ?_⟩
  have hdom : Integrable (fun w : ℂ =>
      2 * ‖w‖ + (2 * (3 / 5 : ℝ) - Real.log ((3 / 5 : ℝ) - ‖p‖)))
      (v13DecodedChainMeasure rows) :=
    integrable_linear_norm_v13DecodedChainMeasure rows 2
      (2 * (3 / 5 : ℝ) - Real.log ((3 / 5 : ℝ) - ‖p‖))
  refine hdom.mono' (hmeas.norm.integral_prod_right') ?_
  refine Filter.Eventually.of_forall (fun w => ?_)
  have h := integral_norm_log_norm_sub_v13GlobalCirclePoissonMeasure_le hp w
  linarith

private theorem integrable_log_norm_sub_poisson_poisson_single
    {p1 p2 : ℂ} (hp1 : ‖p1‖ < v13GlobalPoissonRadius) (hp2 : ‖p2‖ < v13GlobalPoissonRadius) :
    Integrable (fun q : ℂ × ℂ => Real.log ‖q.1 - q.2‖)
      ((v13GlobalCirclePoissonMeasure p1).prod (v13GlobalCirclePoissonMeasure p2)) := by
  haveI := isProbabilityMeasure_v13GlobalCirclePoissonMeasure hp1
  haveI := isProbabilityMeasure_v13GlobalCirclePoissonMeasure hp2
  have hmeas : AEStronglyMeasurable (fun q : ℂ × ℂ => Real.log ‖q.1 - q.2‖)
      ((v13GlobalCirclePoissonMeasure p1).prod (v13GlobalCirclePoissonMeasure p2)) :=
    (by fun_prop : Measurable (fun q : ℂ × ℂ => Real.log ‖q.1 - q.2‖)).aestronglyMeasurable
  rw [integrable_prod_iff hmeas]
  refine ⟨Filter.Eventually.of_forall (fun w =>
    integrable_v13GlobalCirclePoissonMeasure_log_norm_sub_complex hp2 w), ?_⟩
  have hdom : Integrable (fun w : ℂ =>
      2 * ‖w‖ + (2 * (3 / 5 : ℝ) - Real.log ((3 / 5 : ℝ) - ‖p2‖)))
      (v13GlobalCirclePoissonMeasure p1) :=
    integrable_linear_norm_v13GlobalCirclePoissonMeasure hp1 2
      (2 * (3 / 5 : ℝ) - Real.log ((3 / 5 : ℝ) - ‖p2‖))
  refine hdom.mono' (hmeas.norm.integral_prod_right') ?_
  refine Filter.Eventually.of_forall (fun w => ?_)
  have h := integral_norm_log_norm_sub_v13GlobalCirclePoissonMeasure_le hp2 w
  linarith

/-! ## Section 4: Linearity of `vLogInteraction` over `v13PoissonMeasure` -/

private theorem isFiniteMeasure_v13PoissonMeasure (rows : List PR)
    (hnorm : ∀ c ∈ rows, ‖v13PoissonPoint c‖ < v13GlobalPoissonRadius) :
    IsFiniteMeasure (v13PoissonMeasure rows) := by
  induction rows with
  | nil =>
      change IsFiniteMeasure (0 : Measure ℂ)
      infer_instance
  | cons c cs ih =>
      have hc : ‖v13PoissonPoint c‖ < v13GlobalPoissonRadius := hnorm c (by simp)
      have hrest : ∀ d ∈ cs, ‖v13PoissonPoint d‖ < v13GlobalPoissonRadius :=
        fun d hd => hnorm d (by simp [hd])
      letI : IsProbabilityMeasure (v13GlobalCirclePoissonMeasure (v13PoissonPoint c)) :=
        isProbabilityMeasure_v13GlobalCirclePoissonMeasure hc
      letI : IsFiniteMeasure (v13PoissonAtom c) := by
        unfold v13PoissonAtom
        exact Measure.smul_finite _ ENNReal.ofReal_ne_top
      letI : IsFiniteMeasure (v13PoissonMeasure cs) := ih hrest
      change IsFiniteMeasure (v13PoissonAtom c + v13PoissonMeasure cs)
      infer_instance

private theorem integrable_log_norm_sub_prod_v13PoissonMeasure_right
    (μ : Measure ℂ) [SFinite μ] (rows : List PR)
    (hnorm : ∀ c ∈ rows, ‖v13PoissonPoint c‖ < v13GlobalPoissonRadius)
    (hsingle : ∀ c ∈ rows,
      Integrable (fun q : ℂ × ℂ => Real.log ‖q.1 - q.2‖)
        (μ.prod (v13GlobalCirclePoissonMeasure (v13PoissonPoint c)))) :
    Integrable (fun q : ℂ × ℂ => Real.log ‖q.1 - q.2‖)
      (μ.prod (v13PoissonMeasure rows)) := by
  induction rows with
  | nil => simp [v13PoissonMeasure]
  | cons c cs ih =>
      have hc : c ∈ c :: cs := by simp
      have hrest_norm : ∀ d ∈ cs, ‖v13PoissonPoint d‖ < v13GlobalPoissonRadius :=
        fun d hd => hnorm d (by simp [hd])
      have hrest : ∀ d ∈ cs,
          Integrable (fun q : ℂ × ℂ => Real.log ‖q.1 - q.2‖)
            (μ.prod (v13GlobalCirclePoissonMeasure (v13PoissonPoint d))) :=
        fun d hd => hsingle d (by simp [hd])
      letI : IsProbabilityMeasure (v13GlobalCirclePoissonMeasure (v13PoissonPoint c)) :=
        isProbabilityMeasure_v13GlobalCirclePoissonMeasure (hnorm c hc)
      letI : IsFiniteMeasure (v13PoissonAtom c) := by
        unfold v13PoissonAtom
        exact Measure.smul_finite _ ENNReal.ofReal_ne_top
      letI : IsFiniteMeasure (v13PoissonMeasure cs) :=
        isFiniteMeasure_v13PoissonMeasure cs hrest_norm
      have hsplit : v13PoissonMeasure (c :: cs) = v13PoissonAtom c + v13PoissonMeasure cs := by
        simp [v13PoissonMeasure]
      rw [hsplit, Measure.prod_add]
      have hatom : Integrable (fun q : ℂ × ℂ => Real.log ‖q.1 - q.2‖)
          (μ.prod (v13PoissonAtom c)) := by
        unfold v13PoissonAtom
        rw [Measure.prod_smul_right]
        exact (hsingle c hc).smul_measure ENNReal.ofReal_ne_top
      exact hatom.add_measure (ih hrest_norm hrest)

private theorem vLogInteraction_v13PoissonMeasure_right
    (μ : Measure ℂ) [SFinite μ] (rows : List PR)
    (hrows : ∀ c ∈ rows, 0 ≤ c.w.1 ∧ 0 < c.w.2)
    (hnorm : ∀ c ∈ rows, ‖v13PoissonPoint c‖ < v13GlobalPoissonRadius)
    (hsingle : ∀ c ∈ rows,
      Integrable (fun q : ℂ × ℂ => Real.log ‖q.1 - q.2‖)
        (μ.prod (v13GlobalCirclePoissonMeasure (v13PoissonPoint c)))) :
    V.vLogInteraction μ (v13PoissonMeasure rows) =
      (rows.map fun c => (c.mult : ℝ) * IK.val c.w *
        V.vLogInteraction μ (v13GlobalCirclePoissonMeasure (v13PoissonPoint c))).sum := by
  induction rows with
  | nil =>
      simp [vLogInteraction_eq_integral_log_norm_sub, v13PoissonMeasure]
  | cons c cs ih =>
      have hc : c ∈ c :: cs := by simp
      have hrest_rows : ∀ d ∈ cs, 0 ≤ d.w.1 ∧ 0 < d.w.2 :=
        fun d hd => hrows d (by simp [hd])
      have hrest_norm : ∀ d ∈ cs, ‖v13PoissonPoint d‖ < v13GlobalPoissonRadius :=
        fun d hd => hnorm d (by simp [hd])
      have hrest_single : ∀ d ∈ cs,
          Integrable (fun q : ℂ × ℂ => Real.log ‖q.1 - q.2‖)
            (μ.prod (v13GlobalCirclePoissonMeasure (v13PoissonPoint d))) :=
        fun d hd => hsingle d (by simp [hd])
      letI : IsProbabilityMeasure (v13GlobalCirclePoissonMeasure (v13PoissonPoint c)) :=
        isProbabilityMeasure_v13GlobalCirclePoissonMeasure (hnorm c hc)
      letI : IsFiniteMeasure (v13PoissonAtom c) := by
        unfold v13PoissonAtom
        exact Measure.smul_finite _ ENNReal.ofReal_ne_top
      letI : IsFiniteMeasure (v13PoissonMeasure cs) :=
        isFiniteMeasure_v13PoissonMeasure cs hrest_norm
      rcases hrows c hc with ⟨hw1, hw2⟩
      have hw_nonneg : 0 ≤ (c.mult : ℝ) * IK.val c.w := by
        apply mul_nonneg (Nat.cast_nonneg _)
        unfold IK.val
        exact div_nonneg (by exact_mod_cast hw1) (by exact_mod_cast hw2.le)
      have hatom : Integrable (fun q : ℂ × ℂ => Real.log ‖q.1 - q.2‖)
          (μ.prod (v13PoissonAtom c)) := by
        unfold v13PoissonAtom
        rw [Measure.prod_smul_right]
        exact (hsingle c hc).smul_measure ENNReal.ofReal_ne_top
      have htail := integrable_log_norm_sub_prod_v13PoissonMeasure_right μ cs hrest_norm hrest_single
      have hsplit : v13PoissonMeasure (c :: cs) = v13PoissonAtom c + v13PoissonMeasure cs := by
        simp [v13PoissonMeasure]
      rw [vLogInteraction_eq_integral_log_norm_sub μ (v13PoissonMeasure (c :: cs)),
        hsplit, Measure.prod_add, integral_add_measure hatom htail]
      have hhead : (∫ q : ℂ × ℂ, Real.log ‖q.1 - q.2‖ ∂(μ.prod (v13PoissonAtom c))) =
          (c.mult : ℝ) * IK.val c.w *
            V.vLogInteraction μ (v13GlobalCirclePoissonMeasure (v13PoissonPoint c)) := by
        unfold v13PoissonAtom
        rw [Measure.prod_smul_right, integral_smul_measure,
          ENNReal.toReal_ofReal hw_nonneg, smul_eq_mul,
          ← vLogInteraction_eq_integral_log_norm_sub]
      rw [hhead, ← vLogInteraction_eq_integral_log_norm_sub μ (v13PoissonMeasure cs),
        ih hrest_rows hrest_norm hrest_single]
      simp

/-! ## Section 5: Chain-Poisson interaction identity (`v13_chain_poisson_eq_intPoi`) -/

theorem vEnergyA_neg_right (s y : ℝ) : vEnergyA s (-y) = vEnergyA s y := by
  unfold vEnergyA
  by_cases hy : y = 0
  · subst hy; simp
  · have hny : -y ≠ 0 := neg_ne_zero.mpr hy
    rw [if_neg hny, if_neg hy, div_neg, Real.arctan_neg]
    have hsq : s ^ 2 + (-y) ^ 2 = s ^ 2 + y ^ 2 := by ring
    rw [hsq]
    ring

private noncomputable def phiOutReal (c : PR) (u : ℝ) : ℝ :=
  vEnergyA (u - IK.val c.cx) (IK.val c.cy)

private noncomputable def phiInReal (c : PR) (u : ℝ) : ℝ :=
  if IK.val c.cx = 0 ∧ IK.val c.cy = 0 then
    u * Real.log (3 / 5 : ℝ)
  else
    let d := (IK.val c.cx) ^ 2 + (IK.val c.cy) ^ 2
    let ax := (9 / 25 : ℝ) * IK.val c.cx / d
    let ay := (9 / 25 : ℝ) * IK.val c.cy / d
    u * ((1 / 2 : ℝ) * Real.log d - Real.log (3 / 5 : ℝ)) +
      vEnergyA (u - ax) ay

private noncomputable def phiVReal (c : PR) (u : ℝ) : ℝ :=
  if (3 / 5 : ℝ) ≤ u then phiOutReal c u
  else phiInReal c u - phiInReal c (3 / 5 : ℝ) + phiOutReal c (3 / 5 : ℝ)

private theorem phiOutReal_eq_vEnergyPhiOut (c : PR) (e : QF) :
    phiOutReal c (IK.val e) = vEnergyPhiOut c e := rfl

private theorem phiInReal_eq_vEnergyPhiIn (c : PR) (e : QF) :
    phiInReal c (IK.val e) = vEnergyPhiIn c e := rfl

private theorem phiVReal_eq_vEnergyPhiV (c : PR) {e : QF} (he : 0 < e.2) :
    phiVReal c (IK.val e) = vEnergyPhiV c e := by
  unfold phiVReal vEnergyPhiV
  have hR_den : 0 < R.2 := by decide
  have hR_val : IK.val R = (3 / 5 : ℝ) := by norm_num [R, IK.val]
  by_cases hle : (3 / 5 : ℝ) ≤ IK.val e
  · have hqle : qle R e = true := (qle_spec hR_den he).mpr (by rw [hR_val]; exact hle)
    rw [if_pos hle, if_pos hqle]
    rfl
  · have hqle : ¬ (qle R e = true) := by
      intro h
      exact hle (by rw [← hR_val]; exact (qle_spec hR_den he).mp h)
    rw [if_neg hle, if_neg hqle]
    rw [← hR_val]
    rfl

private theorem phiVReal_three_fifths (c : PR) :
    phiVReal c (3 / 5 : ℝ) =
      phiInReal c (3 / 5 : ℝ) - phiInReal c (3 / 5 : ℝ) + phiOutReal c (3 / 5 : ℝ) := by
  unfold phiVReal
  rw [if_pos le_rfl]
  ring

private theorem integral_Ioc_poisson_inside_eq_phiInReal
    (c : PR) (hd_pos : 0 < (IK.val c.cx) ^ 2 + (IK.val c.cy) ^ 2)
    (hd_lt : (IK.val c.cx) ^ 2 + (IK.val c.cy) ^ 2 < (3 / 5 : ℝ) ^ 2)
    {α β : ℝ} (h0α : 0 ≤ α) (hαβ : α ≤ β) (hβR : β ≤ (3 / 5 : ℝ)) :
    (∫ u in Ioc α β,
      ((1 / 2 : ℝ) * Real.log ((9 / 25 - IK.val c.cx * u) ^ 2 + (IK.val c.cy * u) ^ 2) -
        Real.log (3 / 5 : ℝ))) =
      phiInReal c β - phiInReal c α := by
  let d := (IK.val c.cx) ^ 2 + (IK.val c.cy) ^ 2
  let ax := (9 / 25 : ℝ) * IK.val c.cx / d
  let ay := (9 / 25 : ℝ) * IK.val c.cy / d
  let ac : ℂ := ⟨ax, ay⟩
  have hnot0 : ¬ (IK.val c.cx = 0 ∧ IK.val c.cy = 0) := by
    rintro ⟨hx0, hy0⟩
    rw [hx0, hy0] at hd_pos
    norm_num at hd_pos
  have hd_ne : d ≠ 0 := ne_of_gt hd_pos
  have hcongr : (∫ u in Ioc α β,
        ((1 / 2 : ℝ) * Real.log ((9 / 25 - IK.val c.cx * u) ^ 2 + (IK.val c.cy * u) ^ 2) -
          Real.log (3 / 5 : ℝ))) =
      ∫ u in Ioc α β,
        (((1 / 2 : ℝ) * Real.log d - Real.log (3 / 5 : ℝ)) + Real.log ‖ac - (u : ℂ)‖) := by
    refine setIntegral_congr_fun measurableSet_Ioc (fun u hu => ?_)
    have hu0 : 0 ≤ u := le_trans h0α hu.1.le
    have huR : u ≤ (3 / 5 : ℝ) := le_trans hu.2 hβR
    have hnorm_sq : ‖ac - (u : ℂ)‖ ^ 2 = (u - ax) ^ 2 + ay ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      dsimp [ac]
      ring
    have hfactor : (9 / 25 - IK.val c.cx * u) ^ 2 + (IK.val c.cy * u) ^ 2 =
        d * ((u - ax) ^ 2 + ay ^ 2) := by
      dsimp [d, ax, ay]
      field_simp [hd_ne]
      ring
    have hcx_sq : (IK.val c.cx) ^ 2 < (3 / 5 : ℝ) ^ 2 := by
      nlinarith [hd_lt, sq_nonneg (IK.val c.cy)]
    have hu_sq : u ^ 2 ≤ (3 / 5 : ℝ) ^ 2 := by nlinarith
    have hprod_sq : (IK.val c.cx * u) ^ 2 < (9 / 25 : ℝ) ^ 2 := by
      calc
        (IK.val c.cx * u) ^ 2 = (IK.val c.cx) ^ 2 * u ^ 2 := by ring
        _ ≤ (IK.val c.cx) ^ 2 * (3 / 5 : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_left hu_sq (sq_nonneg _)
        _ < (3 / 5 : ℝ) ^ 2 * (3 / 5 : ℝ) ^ 2 :=
            mul_lt_mul_of_pos_right hcx_sq (by norm_num)
        _ = (9 / 25 : ℝ) ^ 2 := by norm_num
    have hsub_pos : 0 < (9 / 25 : ℝ) - IK.val c.cx * u := by
      nlinarith [sq_nonneg ((9 / 25 : ℝ) + IK.val c.cx * u)]
    have hlhs_pos : 0 < (9 / 25 - IK.val c.cx * u) ^ 2 + (IK.val c.cy * u) ^ 2 := by
      nlinarith [sq_pos_of_pos hsub_pos, sq_nonneg (IK.val c.cy * u)]
    have hquad_pos : 0 < (u - ax) ^ 2 + ay ^ 2 := by
      rw [hfactor] at hlhs_pos
      exact (mul_pos_iff_of_pos_left hd_pos).mp hlhs_pos
    have hnorm_pos : 0 < ‖ac - (u : ℂ)‖ := by
      by_contra hle
      have h0 : ‖ac - (u : ℂ)‖ = 0 := le_antisymm (not_lt.mp hle) (norm_nonneg _)
      rw [h0] at hnorm_sq
      linarith
    rw [hfactor, Real.log_mul hd_ne (ne_of_gt hquad_pos), ← hnorm_sq,
      Real.log_pow, Nat.cast_ofNat]
    ring
  rw [hcongr]
  have hIntConst : IntegrableOn
      (fun _ : ℝ => (1 / 2 : ℝ) * Real.log d - Real.log (3 / 5 : ℝ)) (Ioc α β) volume :=
    integrableOn_const (measure_Ioc_lt_top.ne)
  have hIntLog := integrableOn_Ioc_log_norm_sub_complex ac hαβ
  rw [integral_add hIntConst.integrable hIntLog.integrable,
    setIntegral_const, Real.volume_real_Ioc_of_le hαβ, smul_eq_mul,
    integral_Ioc_log_norm_sub_complex ac hαβ]
  unfold phiInReal
  simp only [if_neg hnot0]
  dsimp [ac, d, ax, ay]
  ring

private theorem integral_Ioc_poisson_outside_eq_phiOutReal
    (c : PR) (hd_lt : (IK.val c.cx) ^ 2 + (IK.val c.cy) ^ 2 < (3 / 5 : ℝ) ^ 2)
    {α β : ℝ} (hαβ : α ≤ β) (hout : (3 / 5 : ℝ) ≤ α ∨ β ≤ -(3 / 5 : ℝ)) :
    (∫ u in Ioc α β,
      (1 / 2 : ℝ) * Real.log ((u - IK.val c.cx) ^ 2 + (IK.val c.cy) ^ 2)) =
      phiOutReal c β - phiOutReal c α := by
  let pc := v13PoissonPoint c
  have hcongr : (∫ u in Ioc α β,
        (1 / 2 : ℝ) * Real.log ((u - IK.val c.cx) ^ 2 + (IK.val c.cy) ^ 2)) =
      ∫ u in Ioc α β, Real.log ‖pc - (u : ℂ)‖ := by
    refine setIntegral_congr_fun measurableSet_Ioc (fun u hu => ?_)
    have hu_sq : (3 / 5 : ℝ) ^ 2 ≤ u ^ 2 := by
      rcases hout with h1 | h2
      · have hu1 : (3 / 5 : ℝ) ≤ u := le_trans h1 hu.1.le
        nlinarith
      · have hu2 : u ≤ -(3 / 5 : ℝ) := le_trans hu.2 h2
        nlinarith
    have hpos : 0 < (u - IK.val c.cx) ^ 2 + (IK.val c.cy) ^ 2 := by
      by_contra hle
      push_neg at hle
      have h1 : u - IK.val c.cx = 0 := by
        nlinarith [sq_nonneg (u - IK.val c.cx), sq_nonneg (IK.val c.cy)]
      have h2 : IK.val c.cy = 0 := by
        nlinarith [sq_nonneg (u - IK.val c.cx), sq_nonneg (IK.val c.cy)]
      have hux : u = IK.val c.cx := sub_eq_zero.mp h1
      nlinarith [hd_lt, hu_sq]
    have hnorm_sq : ‖pc - (u : ℂ)‖ ^ 2 = (u - IK.val c.cx) ^ 2 + (IK.val c.cy) ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      dsimp [pc, v13PoissonPoint]
      ring
    have hnorm_pos : 0 < ‖pc - (u : ℂ)‖ := by
      by_contra hle
      have h0 : ‖pc - (u : ℂ)‖ = 0 := le_antisymm (not_lt.mp hle) (norm_nonneg _)
      rw [h0] at hnorm_sq
      linarith
    rw [← hnorm_sq, Real.log_pow, Nat.cast_ofNat]
    ring
  rw [hcongr, integral_Ioc_log_norm_sub_complex pc hαβ]
  rfl

private theorem integrableOn_Ioc_poisson_potential_v
    (c : PR) (hnorm : ‖v13PoissonPoint c‖ < v13GlobalPoissonRadius)
    {α β : ℝ} (_hαβ : α ≤ β) :
    IntegrableOn
      (fun u : ℝ => ∫ w : ℂ, Real.log ‖(u : ℂ) - w‖
        ∂v13GlobalCirclePoissonMeasure (v13PoissonPoint c))
      (Ioc α β) volume := by
  haveI := isProbabilityMeasure_v13GlobalCirclePoissonMeasure hnorm
  have hmeas_d : AEStronglyMeasurable (fun u : ℝ =>
      ∫ w : ℂ, Real.log ‖(u : ℂ) - w‖
        ∂v13GlobalCirclePoissonMeasure (v13PoissonPoint c))
      (volume.restrict (Ioc α β)) := by
    have hmeas2 : AEStronglyMeasurable (fun q : ℝ × ℂ => Real.log ‖(q.1 : ℂ) - q.2‖)
        ((volume.restrict (Ioc α β)).prod (v13GlobalCirclePoissonMeasure (v13PoissonPoint c))) :=
      (by fun_prop : Measurable (fun q : ℝ × ℂ => Real.log ‖(q.1 : ℂ) - q.2‖)).aestronglyMeasurable
    exact hmeas2.integral_prod_right'
  have hdom : IntegrableOn
      (fun u : ℝ => 2 * |u| +
        (2 * (3 / 5 : ℝ) - Real.log ((3 / 5 : ℝ) - ‖v13PoissonPoint c‖)))
      (Ioc α β) volume := by
    have hcont : Continuous (fun u : ℝ => 2 * |u| +
        (2 * (3 / 5 : ℝ) - Real.log ((3 / 5 : ℝ) - ‖v13PoissonPoint c‖))) := by fun_prop
    exact (hcont.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  refine hdom.integrable.mono' hmeas_d (Filter.Eventually.of_forall fun u => ?_)
  have hle1 : ‖∫ w : ℂ, Real.log ‖(u : ℂ) - w‖
      ∂v13GlobalCirclePoissonMeasure (v13PoissonPoint c)‖ ≤
      ∫ w : ℂ, ‖Real.log ‖(u : ℂ) - w‖‖
        ∂v13GlobalCirclePoissonMeasure (v13PoissonPoint c) :=
    norm_integral_le_integral_norm _
  have hle2 := integral_norm_log_norm_sub_v13GlobalCirclePoissonMeasure_le hnorm (u : ℂ)
  have hnonneg : 0 ≤ ∫ w : ℂ, ‖Real.log ‖(u : ℂ) - w‖‖
      ∂v13GlobalCirclePoissonMeasure (v13PoissonPoint c) :=
    integral_nonneg (fun _ => norm_nonneg _)
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg] at hle2
  have hnorm_u : ‖(u : ℂ)‖ = |u| := by rw [Complex.norm_real, Real.norm_eq_abs]
  rw [hnorm_u] at hle2
  linarith

private theorem integrable_v13ChainMeasure_poisson_potential
    (c : PR) (hnorm : ‖v13PoissonPoint c‖ < v13GlobalPoissonRadius) :
    ∀ cells : List V13ChainCell,
      (∀ d ∈ cells, 0 ≤ d.left ∧ d.left ≤ d.right ∧ 0 ≤ d.density) →
      Integrable
        (fun u : ℝ => ∫ w : ℂ, Real.log ‖(u : ℂ) - w‖
          ∂v13GlobalCirclePoissonMeasure (v13PoissonPoint c))
        (v13ChainMeasure cells) := by
  intro cells
  induction cells with
  | nil =>
      intro _
      simp [v13ChainMeasure]
  | cons d ds ih =>
      intro hcells
      have hd : d ∈ d :: ds := by simp
      have hrest : ∀ e ∈ ds, 0 ≤ e.left ∧ e.left ≤ e.right ∧ 0 ≤ e.density :=
        fun e he => hcells e (by simp [he])
      rcases hcells d hd with ⟨h0l, hlr, hdens⟩
      have hcell : Integrable
          (fun u : ℝ => ∫ w : ℂ, Real.log ‖(u : ℂ) - w‖
            ∂v13GlobalCirclePoissonMeasure (v13PoissonPoint c))
          (ENNReal.ofReal d.density • volume.restrict (Ioc d.left d.right)) :=
        (integrableOn_Ioc_poisson_potential_v c hnorm hlr).integrable.smul_measure
          ENNReal.ofReal_ne_top
      have htail := ih hrest
      have hsplit : v13ChainMeasure (d :: ds) =
          ENNReal.ofReal d.density • volume.restrict (Ioc d.left d.right) +
            v13ChainMeasure ds := by
        simp [v13ChainMeasure]
      rw [hsplit]
      exact hcell.add_measure htail

private theorem integral_Ioc_poisson_potential_v_eq_phiVReal
    (c : PR) (hd_pos : 0 < (IK.val c.cx) ^ 2 + (IK.val c.cy) ^ 2)
    (hd_lt : (IK.val c.cx) ^ 2 + (IK.val c.cy) ^ 2 < (3 / 5 : ℝ) ^ 2)
    (hnorm : ‖v13PoissonPoint c‖ < v13GlobalPoissonRadius)
    {α β : ℝ} (h0α : 0 ≤ α) (hαβ : α ≤ β) :
    (∫ u in Ioc α β,
      (∫ w : ℂ, Real.log ‖(u : ℂ) - w‖
        ∂v13GlobalCirclePoissonMeasure (v13PoissonPoint c))) =
      phiVReal c β - phiVReal c α := by
  have hin_case : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ (3 / 5 : ℝ) →
      (∫ u in Ioc a b,
        (∫ w : ℂ, Real.log ‖(u : ℂ) - w‖
          ∂v13GlobalCirclePoissonMeasure (v13PoissonPoint c))) =
        phiInReal c b - phiInReal c a := by
    intro a b h0a hab hbR
    have hcongr : (∫ u in Ioc a b,
          (∫ w : ℂ, Real.log ‖(u : ℂ) - w‖
            ∂v13GlobalCirclePoissonMeasure (v13PoissonPoint c))) =
        ∫ u in Ioc a b,
          ((1 / 2 : ℝ) * Real.log ((9 / 25 - IK.val c.cx * u) ^ 2 + (IK.val c.cy * u) ^ 2) -
            Real.log (3 / 5 : ℝ)) := by
      refine setIntegral_congr_fun measurableSet_Ioc (fun u hu => ?_)
      have hu_in : |u| ≤ (3 / 5 : ℝ) := by
        rw [abs_of_nonneg (le_trans h0a hu.1.le)]
        exact le_trans hu.2 hbR
      exact integral_v13GlobalCirclePoissonMeasure_inside hnorm hu_in
    rw [hcongr]
    exact integral_Ioc_poisson_inside_eq_phiInReal c hd_pos hd_lt h0a hab hbR
  have hout_case : ∀ a b : ℝ, (3 / 5 : ℝ) ≤ a → a ≤ b →
      (∫ u in Ioc a b,
        (∫ w : ℂ, Real.log ‖(u : ℂ) - w‖
          ∂v13GlobalCirclePoissonMeasure (v13PoissonPoint c))) =
        phiOutReal c b - phiOutReal c a := by
    intro a b haR hab
    have hcongr : (∫ u in Ioc a b,
          (∫ w : ℂ, Real.log ‖(u : ℂ) - w‖
            ∂v13GlobalCirclePoissonMeasure (v13PoissonPoint c))) =
        ∫ u in Ioc a b,
          (1 / 2 : ℝ) * Real.log ((u - IK.val c.cx) ^ 2 + (IK.val c.cy) ^ 2) := by
      refine setIntegral_congr_fun measurableSet_Ioc (fun u hu => ?_)
      have hu_out : (3 / 5 : ℝ) ≤ |u| := by
        have hu_pos : 0 ≤ u := by linarith [haR, hu.1]
        rw [abs_of_nonneg hu_pos]
        exact le_trans haR hu.1.le
      exact integral_v13GlobalCirclePoissonMeasure_outside hnorm hu_out
    rw [hcongr]
    exact integral_Ioc_poisson_outside_eq_phiOutReal c hd_lt hab (Or.inl haR)
  by_cases hβR : β ≤ (3 / 5 : ℝ)
  · rw [hin_case α β h0α hαβ hβR]
    by_cases hβeq : β = (3 / 5 : ℝ)
    · subst hβeq
      rw [phiVReal_three_fifths c]
      by_cases hαeq : α = (3 / 5 : ℝ)
      · subst hαeq
        rw [phiVReal_three_fifths c]
        ring
      · have hαlt : ¬ ((3 / 5 : ℝ) ≤ α) := not_le.mpr (lt_of_le_of_ne hαβ hαeq)
        unfold phiVReal
        rw [if_neg hαlt]
        ring
    · have hβlt : ¬ ((3 / 5 : ℝ) ≤ β) := not_le.mpr (lt_of_le_of_ne hβR hβeq)
      have hαlt : ¬ ((3 / 5 : ℝ) ≤ α) := not_le.mpr (lt_of_le_of_lt hαβ (lt_of_le_of_ne hβR hβeq))
      unfold phiVReal
      rw [if_neg hβlt, if_neg hαlt]
      ring
  · push_neg at hβR
    by_cases hRα : (3 / 5 : ℝ) ≤ α
    · rw [hout_case α β hRα hαβ]
      unfold phiVReal
      rw [if_pos (le_of_lt hβR), if_pos hRα]
    · push_neg at hRα
      have hsplit : Ioc α β = Ioc α (3 / 5 : ℝ) ∪ Ioc (3 / 5 : ℝ) β :=
        (Ioc_union_Ioc_eq_Ioc (le_of_lt hRα) (le_of_lt hβR)).symm
      rw [hsplit, setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
        (integrableOn_Ioc_poisson_potential_v c hnorm (le_of_lt hRα))
        (integrableOn_Ioc_poisson_potential_v c hnorm (le_of_lt hβR)),
        hin_case α (3 / 5 : ℝ) h0α (le_of_lt hRα) le_rfl,
        hout_case (3 / 5 : ℝ) β le_rfl (le_of_lt hβR)]
      have hαnot : ¬ ((3 / 5 : ℝ) ≤ α) := not_le.mpr hRα
      unfold phiVReal
      rw [if_pos (le_of_lt hβR), if_neg hαnot]
      ring

private theorem vLogInteraction_zChain_poissonSingle
    {q : ℕ} (R : V13DecodedRows q) (hR : V13FieldRowFacts R)
    (c : PR) (hnorm : ‖v13PoissonPoint c‖ < v13GlobalPoissonRadius) :
    V.vLogInteraction (v13ZChain R) (v13GlobalCirclePoissonMeasure (v13PoissonPoint c)) =
      - (R.data.zp.map fun p => IK.val p.J * vEnergyPhiOut c p.e).sum := by
  letI : IsProbabilityMeasure (v13GlobalCirclePoissonMeasure (v13PoissonPoint c)) :=
    isProbabilityMeasure_v13GlobalCirclePoissonMeasure hnorm
  unfold v13ZChain
  rw [vLogInteraction_eq_integral_log_norm_sub,
    integral_prod _ (integrable_log_norm_sub_chain_poisson_single R.data.zp hnorm)]
  let hEmb := Complex.isometry_ofReal.isClosedEmbedding.measurableEmbedding
  have hmap : (∫ z : ℂ, (∫ w : ℂ, Real.log ‖z - w‖
        ∂v13GlobalCirclePoissonMeasure (v13PoissonPoint c))
        ∂v13DecodedChainMeasure R.data.zp) =
      ∫ u : ℝ, (∫ w : ℂ, Real.log ‖(u : ℂ) - w‖
        ∂v13GlobalCirclePoissonMeasure (v13PoissonPoint c))
        ∂v13ChainMeasure (v13ChainCells R.data.zp) := by
    unfold v13DecodedChainMeasure v13ChainMeasureComplex
    rw [hEmb.integral_map]
  rw [hmap]
  have hae := ae_le_of_right_le_v13ChainMeasure (v13ChainCells R.data.zp)
    (fun d hd => (v13DecodedRows_z_source_bounds R d hd).2)
  have hcongr : (∫ u : ℝ, (∫ w : ℂ, Real.log ‖(u : ℂ) - w‖
        ∂v13GlobalCirclePoissonMeasure (v13PoissonPoint c))
        ∂v13ChainMeasure (v13ChainCells R.data.zp)) =
      ∫ u : ℝ, Real.log ‖v13PoissonPoint c - (u : ℂ)‖
        ∂v13ChainMeasure (v13ChainCells R.data.zp) := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with u hu
    have hu_out : (3 / 5 : ℝ) ≤ |u| := by
      have hu_neg : u < 0 := by linarith
      rw [abs_of_neg hu_neg]
      linarith
    rw [integral_v13GlobalCirclePoissonMeasure_outside hnorm hu_out]
    have hnorm_sq : ‖v13PoissonPoint c - (u : ℂ)‖ ^ 2 =
        (u - IK.val c.cx) ^ 2 + (IK.val c.cy) ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      dsimp [v13PoissonPoint]
      ring
    have hp_lt : ‖v13PoissonPoint c‖ < (3 / 5 : ℝ) := by
      simpa [v13GlobalPoissonRadius] using hnorm
    have htri := norm_sub_norm_le (u : ℂ) (v13PoissonPoint c)
    have hnorm_u : (3 / 5 : ℝ) ≤ ‖(u : ℂ)‖ := by
      simpa [Complex.norm_real, Real.norm_eq_abs] using hu_out
    have hpos : 0 < ‖v13PoissonPoint c - (u : ℂ)‖ := by
      rw [norm_sub_rev]
      linarith
    have hsq' : (u - (v13PoissonPoint c).re) ^ 2 +
        (v13PoissonPoint c).im ^ 2 =
        ‖v13PoissonPoint c - (u : ℂ)‖ ^ 2 := by
      simpa [v13PoissonPoint] using hnorm_sq.symm
    rw [hsq', Real.log_pow, Nat.cast_ofNat]
    ring
  rw [hcongr, integral_v13ChainMeasure_log_norm_sub_complex (v13ChainCells R.data.zp)
    (v13PoissonPoint c) (fun d hd => (hR.z_cells d hd).1) (fun d hd => (hR.z_cells d hd).2)]
  exact v13ChainCells_diff_sum (fun u => vEnergyA (u - IK.val c.cx) (IK.val c.cy))
    R.data.zp hR.z_jump

private theorem vLogInteraction_vChain_poissonSingle
    {q : ℕ} (R : V13DecodedRows q) (hR : V13FieldRowFacts R)
    (c : PR) (hd_pos : 0 < (IK.val c.cx) ^ 2 + (IK.val c.cy) ^ 2)
    (hd_lt : (IK.val c.cx) ^ 2 + (IK.val c.cy) ^ 2 < (3 / 5 : ℝ) ^ 2)
    (hnorm : ‖v13PoissonPoint c‖ < v13GlobalPoissonRadius) :
    V.vLogInteraction (v13DecodedChainMeasure R.data.vp)
        (v13GlobalCirclePoissonMeasure (v13PoissonPoint c)) =
      - (R.data.vp.map fun p => IK.val p.J * vEnergyPhiV c p.e).sum := by
  letI : IsProbabilityMeasure (v13GlobalCirclePoissonMeasure (v13PoissonPoint c)) :=
    isProbabilityMeasure_v13GlobalCirclePoissonMeasure hnorm
  rw [vLogInteraction_eq_integral_log_norm_sub,
    integral_prod _ (integrable_log_norm_sub_chain_poisson_single R.data.vp hnorm)]
  let hEmb := Complex.isometry_ofReal.isClosedEmbedding.measurableEmbedding
  have hmap : (∫ z : ℂ, (∫ w : ℂ, Real.log ‖z - w‖
        ∂v13GlobalCirclePoissonMeasure (v13PoissonPoint c))
        ∂v13DecodedChainMeasure R.data.vp) =
      ∫ u : ℝ, (∫ w : ℂ, Real.log ‖(u : ℂ) - w‖
        ∂v13GlobalCirclePoissonMeasure (v13PoissonPoint c))
        ∂v13ChainMeasure (v13ChainCells R.data.vp) := by
    unfold v13DecodedChainMeasure v13ChainMeasureComplex
    rw [hEmb.integral_map]
  rw [hmap]
  have hcells_eval : ∀ cells : List V13ChainCell,
      (∀ d ∈ cells, 0 ≤ d.left ∧ d.left ≤ d.right ∧ 0 ≤ d.density) →
      (∫ u : ℝ, (∫ w : ℂ, Real.log ‖(u : ℂ) - w‖
          ∂v13GlobalCirclePoissonMeasure (v13PoissonPoint c))
          ∂v13ChainMeasure cells) =
        (cells.map fun d => d.density *
          (phiVReal c d.right - phiVReal c d.left)).sum := by
    intro cells hcells
    induction cells with
    | nil => simp [v13ChainMeasure]
    | cons d ds ih =>
        have hd : d ∈ d :: ds := by simp
        have hrest : ∀ e ∈ ds, 0 ≤ e.left ∧ e.left ≤ e.right ∧ 0 ≤ e.density :=
          fun e he => hcells e (by simp [he])
        rcases hcells d hd with ⟨h0l, hlr, hdens⟩
        have hcell : Integrable
            (fun u : ℝ => ∫ w : ℂ, Real.log ‖(u : ℂ) - w‖
              ∂v13GlobalCirclePoissonMeasure (v13PoissonPoint c))
            (ENNReal.ofReal d.density • volume.restrict (Ioc d.left d.right)) :=
          (integrableOn_Ioc_poisson_potential_v c hnorm hlr).integrable.smul_measure
            ENNReal.ofReal_ne_top
        have htail : Integrable
            (fun u : ℝ => ∫ w : ℂ, Real.log ‖(u : ℂ) - w‖
              ∂v13GlobalCirclePoissonMeasure (v13PoissonPoint c))
            (v13ChainMeasure ds) :=
          integrable_v13ChainMeasure_poisson_potential c hnorm ds hrest
        have hsplit : v13ChainMeasure (d :: ds) =
            ENNReal.ofReal d.density • volume.restrict (Ioc d.left d.right) +
              v13ChainMeasure ds := by
          simp [v13ChainMeasure]
        rw [hsplit, integral_add_measure hcell htail,
          integral_smul_measure, ENNReal.toReal_ofReal hdens, smul_eq_mul,
          integral_Ioc_poisson_potential_v_eq_phiVReal c hd_pos hd_lt hnorm h0l hlr,
          ih hrest]
        simp
  rw [hcells_eval (v13ChainCells R.data.vp) hR.v_cells,
    v13ChainCells_diff_sum (phiVReal c) R.data.vp hR.v_jump]
  congr 1
  refine congrArg List.sum (List.map_congr_left fun p hp => ?_)
  rw [phiVReal_eq_vEnergyPhiV c (hR.v_rows p hp).2.1]

private theorem sum_map_poissonFull_eq_preRowsI_of_conj
    (pts : List Li2Lean.V.Q2Certificate.PoissonPoint) (g : PR → ℝ)
    (hconj : ∀ p : Li2Lean.V.Q2Certificate.PoissonPoint,
      g (prow 1 (Li2Lean.V.Q2Certificate.conjugatePoisson p)) = g (prow 1 p))
    (hmult : ∀ (m : ℕ) (p : Li2Lean.V.Q2Certificate.PoissonPoint),
      g (prow m p) = g (prow 1 p)) :
    let F : PR → ℝ := fun c => (c.mult : ℝ) * IK.val c.w * g c
    (((Li2Lean.V.Q2Certificate.poissonFull pts).map (prow 1)).map F).sum =
      ((preRowsI pts).map F).sum := by
  intro F
  have hF_conj (p : Li2Lean.V.Q2Certificate.PoissonPoint) :
      F (prow 1 (Li2Lean.V.Q2Certificate.conjugatePoisson p)) = F (prow 1 p) := by
    dsimp [F]
    rw [hconj p]
    rfl
  have hF_two (p : Li2Lean.V.Q2Certificate.PoissonPoint) :
      F (prow 2 p) = F (prow 1 p) + F (prow 1 p) := by
    dsimp [F]
    rw [hmult 2 p]
    dsimp [prow]
    push_cast
    ring
  have haux : ∀ l : List Li2Lean.V.Q2Certificate.PoissonPoint,
      ((l.map (prow 1)).map F).sum +
        (((l.dropLast.map Li2Lean.V.Q2Certificate.conjugatePoisson).map (prow 1)).map F).sum =
        ((preRowsI l).map F).sum := by
    intro l
    induction l with
    | nil => simp [preRowsI]
    | cons p tl ih =>
        cases tl with
        | nil => simp [preRowsI]
        | cons q rest =>
            have hpre : preRowsI (p :: q :: rest) = prow 2 p :: preRowsI (q :: rest) := rfl
            rw [List.dropLast_cons_cons, hpre]
            simp only [List.map_cons, List.sum_cons] at ih ⊢
            rw [hF_conj p, hF_two p]
            linarith [ih]
  unfold Li2Lean.V.Q2Certificate.poissonFull
  rw [List.map_append, List.map_append, List.sum_append,
    List.map_reverse, List.map_reverse, List.sum_reverse]
  exact haux pts

private theorem sum_range_drop_eq_map_sum {α : Type*} (l : List α) (f : α → ℝ) :
    (∑ i ∈ Finset.range l.length, match l.drop i with | [] => 0 | c :: tail => f c) =
      (l.map f).sum := by
  induction l with
  | nil => simp
  | cons c cs ih =>
      rw [List.length_cons, Finset.sum_range_succ']
      simp only [List.drop_zero, List.drop_succ_cons, List.map_cons, List.sum_cons]
      rw [ih, add_comm]

/-- Combined `z`-chain/Poisson and `v`-chain/Poisson interaction equals the `.intPoi` row sum. -/
theorem v13_chain_poisson_eq_intPoi {q : ℕ} (R : V13DecodedRows q) (hR : V13FieldRowFacts R) :
    2 * V.vLogInteraction (v13ZChain R) (v13ZPoisson R) +
      V.vLogInteraction (v13DecodedChainMeasure R.data.vp) (v13ZPoisson R) =
      ∑ i ∈ Finset.range (kindCount R.data .intPoi), vEnergyTerm q R.data .intPoi i := by
  have hrows : ∀ c ∈ R.data.full, 0 ≤ c.w.1 ∧ 0 < c.w.2 := fun c hc =>
    ⟨(hR.full_rows_data c hc).2.2.2.1, (hR.full_rows_data c hc).2.2.1⟩
  have hnorm : ∀ c ∈ R.data.full, ‖v13PoissonPoint c‖ < v13GlobalPoissonRadius :=
    fun c hc => (hR.full_rows_data c hc).2.2.2.2.2.2.2
  have hZ : V.vLogInteraction (v13ZChain R) (v13ZPoisson R) =
      (R.data.pre.map fun c => (c.mult : ℝ) * IK.val c.w *
        (- (R.data.zp.map fun p => IK.val p.J * vEnergyPhiOut c p.e).sum)).sum := by
    unfold v13ZPoisson
    rw [vLogInteraction_v13PoissonMeasure_right (v13ZChain R) R.data.full hrows hnorm
      (fun c hc => integrable_log_norm_sub_chain_poisson_single R.data.zp (hnorm c hc))]
    have hmap : (R.data.full.map fun c => (c.mult : ℝ) * IK.val c.w *
          V.vLogInteraction (v13ZChain R) (v13GlobalCirclePoissonMeasure (v13PoissonPoint c))) =
        R.data.full.map (fun c => (c.mult : ℝ) * IK.val c.w *
          (- (R.data.zp.map fun p => IK.val p.J * vEnergyPhiOut c p.e).sum)) := by
      refine List.map_congr_left (fun c hc => ?_)
      rw [vLogInteraction_zChain_poissonSingle R hR c (hnorm c hc)]
    rw [hmap]
    rcases v13DecodedRows_poisson_split R with ⟨pts, hpre, hfull, _, _⟩
    rw [hfull, hpre]
    refine sum_map_poissonFull_eq_preRowsI_of_conj pts
      (fun c => - (R.data.zp.map fun p => IK.val p.J * vEnergyPhiOut c p.e).sum)
      (fun pt => ?_) (fun _ _ => rfl)
    congr 1
    refine congrArg List.sum (List.map_congr_left fun p _ => ?_)
    congr 1
    unfold vEnergyPhiOut prow Li2Lean.V.Q2Certificate.conjugatePoisson
    have hcy : IK.val (-pt.yUnits, U) = -IK.val (pt.yUnits, U) := by
      unfold IK.val; push_cast; ring
    dsimp only
    rw [hcy, vEnergyA_neg_right]
  have hV : V.vLogInteraction (v13DecodedChainMeasure R.data.vp) (v13ZPoisson R) =
      (R.data.pre.map fun c => (c.mult : ℝ) * IK.val c.w *
        (- (R.data.vp.map fun p => IK.val p.J * vEnergyPhiV c p.e).sum)).sum := by
    unfold v13ZPoisson
    rw [vLogInteraction_v13PoissonMeasure_right (v13DecodedChainMeasure R.data.vp)
      R.data.full hrows hnorm
      (fun c hc => integrable_log_norm_sub_chain_poisson_single R.data.vp (hnorm c hc))]
    have hmap : (R.data.full.map fun c => (c.mult : ℝ) * IK.val c.w *
          V.vLogInteraction (v13DecodedChainMeasure R.data.vp)
            (v13GlobalCirclePoissonMeasure (v13PoissonPoint c))) =
        R.data.full.map (fun c => (c.mult : ℝ) * IK.val c.w *
          (- (R.data.vp.map fun p => IK.val p.J * vEnergyPhiV c p.e).sum)) := by
      refine List.map_congr_left (fun c hc => ?_)
      rcases hR.full_rows_data c hc with ⟨_, _, _, _, _, hd_pos, hd_lt, hnorm_c⟩
      rw [vLogInteraction_vChain_poissonSingle R hR c hd_pos hd_lt hnorm_c]
    rw [hmap]
    rcases v13DecodedRows_poisson_split R with ⟨pts, hpre, hfull, _, _⟩
    rw [hfull, hpre]
    refine sum_map_poissonFull_eq_preRowsI_of_conj pts
      (fun c => - (R.data.vp.map fun p => IK.val p.J * vEnergyPhiV c p.e).sum)
      (fun pt => ?_) (fun _ _ => rfl)
    congr 1
    refine congrArg List.sum (List.map_congr_left fun p _ => ?_)
    congr 1
    have hcy : IK.val (-pt.yUnits, U) = -IK.val (pt.yUnits, U) := by
      unfold IK.val; push_cast; ring
    have hout_eq : ∀ u : QF, vEnergyPhiOut (prow 1 (Li2Lean.V.Q2Certificate.conjugatePoisson pt)) u =
        vEnergyPhiOut (prow 1 pt) u := by
      intro u
      unfold vEnergyPhiOut prow Li2Lean.V.Q2Certificate.conjugatePoisson
      dsimp only
      rw [hcy, vEnergyA_neg_right]
    have hin_eq : ∀ u : QF, vEnergyPhiIn (prow 1 (Li2Lean.V.Q2Certificate.conjugatePoisson pt)) u =
        vEnergyPhiIn (prow 1 pt) u := by
      intro u
      unfold vEnergyPhiIn prow Li2Lean.V.Q2Certificate.conjugatePoisson
      dsimp only
      have hyzero : -IK.val (pt.yUnits, U) = 0 ↔ IK.val (pt.yUnits, U) = 0 := by
        constructor <;> intro h <;> linarith
      have hysq : (-IK.val (pt.yUnits, U)) ^ 2 = IK.val (pt.yUnits, U) ^ 2 := by ring
      simp only [hcy, neg_eq_zero]
      rw [hysq]
      split_ifs with h0
      · rfl
      · congr 1
        have harg : (9 / 25 : ℝ) * -IK.val (pt.yUnits, U) /
            (IK.val (pt.xUnits, U) ^ 2 + IK.val (pt.yUnits, U) ^ 2) =
            -((9 / 25 : ℝ) * IK.val (pt.yUnits, U) /
              (IK.val (pt.xUnits, U) ^ 2 + IK.val (pt.yUnits, U) ^ 2)) := by
          ring
        rw [harg, vEnergyA_neg_right]
    unfold vEnergyPhiV
    split_ifs <;> simp only [hout_eq, hin_eq]
  rw [hZ, hV]
  change 2 * (R.data.pre.map fun c => (c.mult : ℝ) * IK.val c.w *
        (- (R.data.zp.map fun p => IK.val p.J * vEnergyPhiOut c p.e).sum)).sum +
      (R.data.pre.map fun c => (c.mult : ℝ) * IK.val c.w *
        (- (R.data.vp.map fun p => IK.val p.J * vEnergyPhiV c p.e).sum)).sum =
    ∑ i ∈ Finset.range R.data.pre.length,
      match R.data.pre.drop i with
      | [] => 0
      | c :: tail => vEnergyIntPoiRow R.data c
  have hsum := sum_range_drop_eq_map_sum R.data.pre (vEnergyIntPoiRow R.data)
  have hmain :
      2 * (R.data.pre.map fun c => (c.mult : ℝ) * IK.val c.w *
          (- (R.data.zp.map fun p => IK.val p.J * vEnergyPhiOut c p.e).sum)).sum +
        (R.data.pre.map fun c => (c.mult : ℝ) * IK.val c.w *
          (- (R.data.vp.map fun p => IK.val p.J * vEnergyPhiV c p.e).sum)).sum =
      (R.data.pre.map (vEnergyIntPoiRow R.data)).sum := by
    rw [← List.sum_map_mul_left, ← List.sum_map_add]
    refine congrArg List.sum (List.map_congr_left fun c _ => ?_)
    unfold vEnergyIntPoiRow
    ring
  rw [hmain]
  refine hsum.symm.trans ?_
  apply Finset.sum_congr rfl
  intro i hi
  cases h : R.data.pre.drop i with
  | nil => rfl
  | cons c tail => rfl

/-! ## Section 6: Poisson-Poisson self interaction (`v13_poisson_self_eq_pp`) -/

private theorem vEnergyPpModSq_eq (ci cj : PR)
    (hcix : 0 < ci.cx.2) (hciy : 0 < ci.cy.2)
    (hcjx : 0 < cj.cx.2) (hcjy : 0 < cj.cy.2) :
    vEnergyPpModSq ci cj =
      (9 / 25 - (IK.val ci.cx * IK.val cj.cx + IK.val ci.cy * IK.val cj.cy)) ^ 2 +
        (IK.val ci.cx * IK.val cj.cy - IK.val ci.cy * IK.val cj.cx) ^ 2 := by
  unfold vEnergyPpModSq modsq
  have h1 : 0 < (qmul ci.cx cj.cx).2 := qmul_den_pos hcix hcjx
  have h2 : 0 < (qmul ci.cy cj.cy).2 := qmul_den_pos hciy hcjy
  have h3 : 0 < (qadd (qmul ci.cx cj.cx) (qmul ci.cy cj.cy)).2 := qadd_den_pos h1 h2
  have hR2 : 0 < R2.2 := by decide
  have h4 : 0 < (qsub R2 (qadd (qmul ci.cx cj.cx) (qmul ci.cy cj.cy))).2 := qsub_den_pos hR2 h3
  have h5 : 0 < (qsq (qsub R2 (qadd (qmul ci.cx cj.cx) (qmul ci.cy cj.cy)))).2 := qsq_den_pos h4
  have h6 : 0 < (qmul ci.cx cj.cy).2 := qmul_den_pos hcix hcjy
  have h7 : 0 < (qmul ci.cy cj.cx).2 := qmul_den_pos hciy hcjx
  have h8 : 0 < (qsub (qmul ci.cx cj.cy) (qmul ci.cy cj.cx)).2 := qsub_den_pos h6 h7
  have h9 : 0 < (qsq (qsub (qmul ci.cx cj.cy) (qmul ci.cy cj.cx))).2 := qsq_den_pos h8
  rw [val_qadd h5 h9, val_qsq_local, val_qsq_local, val_qsub hR2 h3, val_qadd h1 h2,
    val_qsub h6 h7, val_qmul, val_qmul, val_qmul, val_qmul]
  have hvalR2 : IK.val R2 = (9 / 25 : ℝ) := by norm_num [R2, IK.val]
  rw [hvalR2]

private theorem vLogInteraction_poissonSingle_eq_vEnergyPpTerm
    (ci cj : PR)
    (hcix : 0 < ci.cx.2) (hciy : 0 < ci.cy.2)
    (hcjx : 0 < cj.cx.2) (hcjy : 0 < cj.cy.2)
    (hci : ‖v13PoissonPoint ci‖ < v13GlobalPoissonRadius)
    (hcj : ‖v13PoissonPoint cj‖ < v13GlobalPoissonRadius) :
    V.vLogInteraction (v13GlobalCirclePoissonMeasure (v13PoissonPoint ci))
        (v13GlobalCirclePoissonMeasure (v13PoissonPoint cj)) =
      vEnergyPpTerm ci cj := by
  letI : IsProbabilityMeasure (v13GlobalCirclePoissonMeasure (v13PoissonPoint ci)) :=
    isProbabilityMeasure_v13GlobalCirclePoissonMeasure hci
  letI : IsProbabilityMeasure (v13GlobalCirclePoissonMeasure (v13PoissonPoint cj)) :=
    isProbabilityMeasure_v13GlobalCirclePoissonMeasure hcj
  rw [vLogInteraction_eq_integral_log_norm_sub,
    integral_prod _ (integrable_log_norm_sub_poisson_poisson_single hci hcj)]
  have hcongr : (∫ w : ℂ, (∫ z : ℂ, Real.log ‖w - z‖
        ∂v13GlobalCirclePoissonMeasure (v13PoissonPoint cj))
        ∂v13GlobalCirclePoissonMeasure (v13PoissonPoint ci)) =
      ∫ w : ℂ, Real.log ‖v13PoissonPoint cj - w‖
        ∂v13GlobalCirclePoissonMeasure (v13PoissonPoint ci) := by
    refine integral_congr_ae ?_
    filter_upwards [ae_norm_eq_v13GlobalCirclePoissonMeasure (v13PoissonPoint ci)] with w hw
    have hw_ge : (3 / 5 : ℝ) ≤ ‖w‖ := le_of_eq hw.symm
    rw [integral_v13GlobalCirclePoissonMeasure_outside_complex hcj hw_ge]
    have hnorm_sq : ‖v13PoissonPoint cj - w‖ ^ 2 =
        (w.re - (v13PoissonPoint cj).re) ^ 2 + (w.im - (v13PoissonPoint cj).im) ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.sub_im]
      ring
    have hcj_lt : ‖v13PoissonPoint cj‖ < (3 / 5 : ℝ) := by
      simpa [v13GlobalPoissonRadius] using hcj
    have htri := norm_sub_norm_le w (v13PoissonPoint cj)
    have hpos : 0 < ‖v13PoissonPoint cj - w‖ := by
      rw [norm_sub_rev]
      linarith
    rw [← hnorm_sq, Real.log_pow, Nat.cast_ofNat]
    ring
  rw [hcongr]
  have hcj_le : ‖v13PoissonPoint cj‖ ≤ (3 / 5 : ℝ) := by
    have hlt : ‖v13PoissonPoint cj‖ < (3 / 5 : ℝ) := by
      simpa [v13GlobalPoissonRadius] using hcj
    exact le_of_lt hlt
  rw [integral_v13GlobalCirclePoissonMeasure_inside_complex hci hcj_le]
  unfold vEnergyPpTerm v13PoissonPoint
  dsimp only
  rw [vEnergyPpModSq_eq ci cj hcix hciy hcjx hcjy]

private theorem modsq_symm (ci cj : PR) : modsq ci cj = modsq cj ci := by
  ext
  · simp only [modsq, R2, qadd, qsq, qsub, qneg, qmul, Int.ofNat_eq_coe]
    push_cast
    ring
  · simp only [modsq, R2, qadd, qsq, qsub, qneg, qmul]
    ring

private theorem vEnergyPpTerm_symm (ci cj : PR) :
    vEnergyPpTerm ci cj = vEnergyPpTerm cj ci := by
  simp only [vEnergyPpTerm, vEnergyPpModSq, modsq_symm ci cj]

private theorem vEnergyPpRow_cons_succ (c : PR) (tl : List PR) (k : ℕ) :
    vEnergyPpRow (c :: tl) (k + 1) = vEnergyPpRow tl k := by
  unfold vEnergyPpRow
  simp

private theorem sum_vEnergyPpRow_eq_double_sum (rows : List PR) :
    (∑ i ∈ Finset.range rows.length, vEnergyPpRow rows i) =
      (rows.map fun ci =>
        (rows.map fun cj =>
          IK.val ci.w * IK.val cj.w * vEnergyPpTerm ci cj).sum).sum := by
  induction rows with
  | nil => simp
  | cons c tl ih =>
      rw [List.length_cons, Finset.sum_range_succ']
      simp_rw [vEnergyPpRow_cons_succ]
      rw [ih]
      have h0 : vEnergyPpRow (c :: tl) 0 =
          IK.val c.w * IK.val c.w * vEnergyPpTerm c c +
            ((tl.map fun cj => 2 * IK.val c.w * IK.val cj.w * vEnergyPpTerm c cj).sum) := by
        unfold vEnergyPpRow
        dsimp only [List.drop]
        ring
      rw [h0]
      simp only [List.map_cons, List.sum_cons]
      have hcol : (tl.map fun ci =>
            IK.val ci.w * IK.val c.w * vEnergyPpTerm ci c +
              (tl.map fun cj => IK.val ci.w * IK.val cj.w * vEnergyPpTerm ci cj).sum).sum =
          (tl.map fun ci => IK.val ci.w * IK.val c.w * vEnergyPpTerm ci c).sum +
            (tl.map fun ci =>
              (tl.map fun cj => IK.val ci.w * IK.val cj.w * vEnergyPpTerm ci cj).sum).sum := by
        rw [← List.sum_map_add]
      rw [hcol]
      have hsymm : (tl.map fun ci => IK.val ci.w * IK.val c.w * vEnergyPpTerm ci c) =
          tl.map (fun cj => IK.val c.w * IK.val cj.w * vEnergyPpTerm c cj) := by
        refine List.map_congr_left (fun cj _ => ?_)
        rw [vEnergyPpTerm_symm cj c]
        ring
      have htwo : (tl.map fun cj => 2 * IK.val c.w * IK.val cj.w * vEnergyPpTerm c cj).sum =
          (tl.map fun cj => IK.val c.w * IK.val cj.w * vEnergyPpTerm c cj).sum +
            (tl.map fun cj => IK.val c.w * IK.val cj.w * vEnergyPpTerm c cj).sum := by
        rw [← List.sum_map_add]
        refine congrArg List.sum (List.map_congr_left fun cj _ => ?_)
        ring
      rw [hsymm, htwo]
      ring

/-- Self logarithmic interaction of the Poisson cloud equals the `.pp` row sum. -/
theorem v13_poisson_self_eq_pp {q : ℕ} (R : V13DecodedRows q) (hR : V13FieldRowFacts R) :
    V.vLogInteraction (v13ZPoisson R) (v13ZPoisson R) =
      ∑ i ∈ Finset.range (kindCount R.data .pp), vEnergyTerm q R.data .pp i := by
  have hrows : ∀ c ∈ R.data.full, 0 ≤ c.w.1 ∧ 0 < c.w.2 := fun c hc =>
    ⟨(hR.full_rows_data c hc).2.2.2.1, (hR.full_rows_data c hc).2.2.1⟩
  have hnorm : ∀ c ∈ R.data.full, ‖v13PoissonPoint c‖ < v13GlobalPoissonRadius :=
    fun c hc => (hR.full_rows_data c hc).2.2.2.2.2.2.2
  rcases v13DecodedRows_poisson_split R with ⟨_, _, _, _, hmult⟩
  letI : IsFiniteMeasure (v13PoissonMeasure R.data.full) :=
    isFiniteMeasure_v13PoissonMeasure R.data.full hnorm
  have hbilin : V.vLogInteraction (v13PoissonMeasure R.data.full) (v13PoissonMeasure R.data.full) =
      (R.data.full.map fun ci =>
        (R.data.full.map fun cj =>
          IK.val ci.w * IK.val cj.w * vEnergyPpTerm ci cj).sum).sum := by
    rw [vLogInteraction_v13PoissonMeasure_right (v13PoissonMeasure R.data.full) R.data.full
      hrows hnorm]
    · refine congrArg List.sum (List.map_congr_left fun cj hcj => ?_)
      letI : IsProbabilityMeasure (v13GlobalCirclePoissonMeasure (v13PoissonPoint cj)) :=
        isProbabilityMeasure_v13GlobalCirclePoissonMeasure (hnorm cj hcj)
      have hcj_mult : (cj.mult : ℝ) = 1 := by exact_mod_cast (hmult cj hcj).1
      rw [hcj_mult, one_mul,
        vLogInteraction_symm (v13PoissonMeasure R.data.full)
          (v13GlobalCirclePoissonMeasure (v13PoissonPoint cj)),
        vLogInteraction_v13PoissonMeasure_right
          (v13GlobalCirclePoissonMeasure (v13PoissonPoint cj)) R.data.full hrows hnorm
          (fun ci hci => integrable_log_norm_sub_poisson_poisson_single
            (hnorm cj hcj) (hnorm ci hci))]
      rw [← List.sum_map_mul_left]
      refine congrArg List.sum (List.map_congr_left fun ci hci => ?_)
      have hci_mult : (ci.mult : ℝ) = 1 := by exact_mod_cast (hmult ci hci).1
      rw [hci_mult, one_mul,
        vLogInteraction_poissonSingle_eq_vEnergyPpTerm cj ci
          (hR.full_rows_data cj hcj).1 (hR.full_rows_data cj hcj).2.1
          (hR.full_rows_data ci hci).1 (hR.full_rows_data ci hci).2.1
          (hnorm cj hcj) (hnorm ci hci),
        vEnergyPpTerm_symm cj ci]
      ring
    · intro cj hcj
      letI : IsProbabilityMeasure (v13GlobalCirclePoissonMeasure (v13PoissonPoint cj)) :=
        isProbabilityMeasure_v13GlobalCirclePoissonMeasure (hnorm cj hcj)
      have hswap := integrable_log_norm_sub_prod_v13PoissonMeasure_right
        (v13GlobalCirclePoissonMeasure (v13PoissonPoint cj)) R.data.full hnorm
        (fun ci hci => integrable_log_norm_sub_poisson_poisson_single
          (hnorm cj hcj) (hnorm ci hci))
      rw [← Measure.prod_swap]
      have hmeas : AEStronglyMeasurable (fun q : ℂ × ℂ => Real.log ‖q.1 - q.2‖)
          (((v13GlobalCirclePoissonMeasure (v13PoissonPoint cj)).prod
            (v13PoissonMeasure R.data.full)).map Prod.swap) :=
        (by fun_prop : Measurable (fun q : ℂ × ℂ => Real.log ‖q.1 - q.2‖)).aestronglyMeasurable
      rw [integrable_map_measure hmeas measurable_swap.aemeasurable]
      refine hswap.congr (Filter.Eventually.of_forall fun p => ?_)
      simp [Function.comp, norm_sub_rev]
  unfold v13ZPoisson kindCount vEnergyTerm
  dsimp only
  rw [hbilin, ← sum_vEnergyPpRow_eq_double_sum]

/-! ## Section 7: Full evaluator-row sum and `EnergyTotalSoundnessFact` -/

/-- The 8-part measure interaction plan sum equals the 7-kind evaluator row sum. -/
theorem v13_evaluator_rows {q : ℕ} {hq : SignedVBaseRange q} (R : V13DecodedRows q)
    (hR : V13FieldRowFacts R) (N : V13MeasureNormalization hq (v13RefRaw R)) :
    v13InteractionPlanSum (v13RefMeasure R N) (v13ZChain R) (v13ZPoisson R) =
      (allKinds.map fun k =>
        ∑ i ∈ Finset.range (kindCount R.data k), vEnergyTerm q R.data k i).sum := by
  have hselfX : V.vLogInteraction (v13RefMeasure R N).μx (v13RefMeasure R N).μx =
      ∑ i ∈ Finset.range (kindCount R.data .selfX), vEnergyTerm q R.data .selfX i :=
    v13_chain_self_eq_rows R.data.xp
      (fun c hc => ⟨(hR.x_cells c hc).2.1, (hR.x_cells c hc).2.2⟩) hR.x_jump
  have hselfV : V.vLogInteraction (v13RefMeasure R N).μv (v13RefMeasure R N).μv =
      ∑ i ∈ Finset.range (kindCount R.data .selfV), vEnergyTerm q R.data .selfV i :=
    v13_chain_self_eq_rows R.data.vp
      (fun c hc => ⟨(hR.v_cells c hc).2.1, (hR.v_cells c hc).2.2⟩) hR.v_jump
  have hselfZ : V.vLogInteraction (v13ZChain R) (v13ZChain R) =
      ∑ i ∈ Finset.range (kindCount R.data .selfZ), vEnergyTerm q R.data .selfZ i :=
    v13_chain_self_eq_rows R.data.zp hR.z_cells hR.z_jump
  have hcrossVZ : V.vLogInteraction (v13RefMeasure R N).μv (v13ZChain R) =
      ∑ i ∈ Finset.range (kindCount R.data .crossVZ), vEnergyTerm q R.data .crossVZ i :=
    v13_chain_cross_eq_rows R.data.vp R.data.zp
      (fun c hc => ⟨(hR.v_cells c hc).2.1, (hR.v_cells c hc).2.2⟩) hR.v_jump
      hR.z_cells hR.z_jump
  have hintPoi : 2 * V.vLogInteraction (v13ZChain R) (v13ZPoisson R) +
      V.vLogInteraction (v13RefMeasure R N).μv (v13ZPoisson R) =
      ∑ i ∈ Finset.range (kindCount R.data .intPoi), vEnergyTerm q R.data .intPoi i :=
    v13_chain_poisson_eq_intPoi R hR
  have hpp : V.vLogInteraction (v13ZPoisson R) (v13ZPoisson R) =
      ∑ i ∈ Finset.range (kindCount R.data .pp), vEnergyTerm q R.data .pp i :=
    v13_poisson_self_eq_pp R hR
  have hdq : -(V.vCrossInteraction (v13RefMeasure R N).q
        (v13RefMeasure R N).μx (v13RefMeasure R N).μv) =
      ∑ i ∈ Finset.range (kindCount R.data .dq), vEnergyTerm q R.data .dq i := by
    have h0 := v13RefMeasure_crossXV_eq_vEnergyTerm_dq_zero R N
    have hcnt : kindCount R.data .dq = 1 := rfl
    rw [hcnt, Finset.sum_range_one]
    exact h0
  unfold v13InteractionPlanSum v13InteractionPlan v13InteractionTerm allKinds
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  linarith

/-- Total energy soundness from `V13FieldRowFacts` and `V13InteractionIntegrability`. -/
theorem v13_total_fact_of_interaction {q : ℕ} {hq : SignedVBaseRange q}
    (R : V13DecodedRows q) (hR : V13FieldRowFacts R)
    (N : V13MeasureNormalization hq (v13RefRaw R))
    (hInt : V13InteractionIntegrability (v13RefMeasure R N) (v13ZChain R) (v13ZPoisson R))
    (plan : List (EKind × Nat × Nat × Int)) :
    EnergyTotalSoundnessFact (v13RefMeasure R N) R.data plan (vEnergyTerm q R.data) :=
  (SignedQuadraticTotalIdentity.toFact
    (⟨by
      rw [signedVQuadratic_v13RefMeasure_eq_v13InteractionPlanSum R N hInt,
        v13_evaluator_rows R hR N]⟩ :
      SignedQuadraticTotalIdentity (v13RefMeasure R N) R.data plan
        (vEnergyTerm q R.data)))

/-- Total energy soundness from `V13FieldRowFacts` and linear ball-growth bounds. -/
theorem v13_total_fact_of_ballBound {q : ℕ} {hq : SignedVBaseRange q}
    (R : V13DecodedRows q) (hR : V13FieldRowFacts R)
    (hrows : V13DecodedRowBounds q R)
    (N : V13MeasureNormalization hq (v13RefRaw R))
    {Ax Av Az : ℝ} (hAx : 0 ≤ Ax) (hAv : 0 ≤ Av) (hAz : 0 ≤ Az)
    (hx : VBallBound (v13RefMeasure R N).μx Ax)
    (hv : VBallBound (v13RefMeasure R N).μv Av)
    (hz : VBallBound (v13RefMeasure R N).μz Az)
    (plan : List (EKind × Nat × Nat × Int)) :
    EnergyTotalSoundnessFact (v13RefMeasure R N) R.data plan (vEnergyTerm q R.data) :=
  v13_total_fact_of_interaction R hR N
    (v13InteractionIntegrability_of_ballBound R hrows N hAx hAv hAz hx hv hz) plan

/-- Total energy soundness (`S7`) from `V13FieldRowFacts` and `V13NumericCertificates`. -/
theorem v13_total_fact {q : ℕ} {hq : SignedVBaseRange q}
    (R : V13DecodedRows q) (hR : V13FieldRowFacts R)
    (C : V13NumericCertificates q hq R)
    (plan : List (EKind × Nat × Nat × Int)) :
    EnergyTotalSoundnessFact (v13RefMeasure R C.normalization) R.data plan (vEnergyTerm q R.data) :=
  v13_total_fact_of_ballBound R hR C.rows C.normalization
    C.Ax_nonneg C.Av_nonneg C.Az_nonneg C.x_ball C.v_ball C.z_ball plan

end

end Li2Lean.B3
