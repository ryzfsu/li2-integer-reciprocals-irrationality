/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Finite q = 6 mass checks for the concrete v13 reference rows. This module
keeps normalization explicit and proves only the row-derived x mass; the
remaining field and energy ledger facts stay at their declared interfaces.
-/

import Li2Lean.B3.Q6ReferenceMeasureFacts
import Li2Lean.B3.V13ChainEnergy

namespace Li2Lean

noncomputable section

namespace B3

open V
open V.EnergyCertI
open V.EnergyCertI.IK
open MeasureTheory Set
open scoped ENNReal

private theorem q6_chain_measure_univ (cells : List V13ChainCell) :
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

private theorem q6_chain_complex_univ (cells : List V13ChainCell) :
    v13ChainMeasureComplex cells Set.univ =
      (cells.map (fun c => ENNReal.ofReal c.density *
        ENNReal.ofReal (c.right - c.left))).sum := by
  unfold v13ChainMeasureComplex
  rw [Measure.map_apply Complex.measurable_ofReal MeasurableSet.univ]
  rw [Set.preimage_univ, q6_chain_measure_univ]

private theorem q6_list_real_sum_nonneg {α : Type} (rows : List α)
    (f : α → ℝ) (hf : ∀ x ∈ rows, 0 ≤ f x) :
    0 ≤ (rows.map f).sum := by
  induction rows with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      apply add_nonneg
      · exact hf x (by simp)
      · apply ih
        intro y hy
        exact hf y (by simp [hy])

private theorem q6_list_ofReal_sum {α : Type} (rows : List α)
    (f : α → ℝ) (hf : ∀ x ∈ rows, 0 ≤ f x) :
    (rows.map (fun x => ENNReal.ofReal (f x))).sum =
      ENNReal.ofReal ((rows.map f).sum) := by
  induction rows with
  | nil => simp
  | cons x xs ih =>
      have htail : ∀ y ∈ xs, 0 ≤ f y := by
        intro y hy
        exact hf y (by simp [hy])
      calc
        (List.map (fun x => ENNReal.ofReal (f x)) (x :: xs)).sum =
            ENNReal.ofReal (f x) + ENNReal.ofReal ((List.map f xs).sum) := by
          simp only [List.map_cons, List.sum_cons, ih htail]
        _ = ENNReal.ofReal (f x + (List.map f xs).sum) := by
          rw [ENNReal.ofReal_add (hf x (by simp))
            (q6_list_real_sum_nonneg xs f htail)]
        _ = ENNReal.ofReal ((List.map f (x :: xs)).sum) := rfl

/-- The x-chain has unit mass, checked directly from the printed q6 table. -/
theorem q6ReferenceRaw_x_mass :
    q6RawReferenceMeasures.μx Set.univ = (1 : ℝ≥0∞) := by
  unfold q6RawReferenceMeasures v13RefRaw v13DecodedChainMeasure
    v13ChainMeasureComplex
  rw [Measure.map_apply Complex.measurable_ofReal MeasurableSet.univ]
  rw [Set.preimage_univ, q6_chain_measure_univ]
  norm_num [v13ChainCells, v13ChainCellsAux, q6D, mkIData, chainCP,
    chainCoords, chainMassU, densI, jumpsI, q6DecodedReferenceRows_data,
    q6XHeader, q6XEntries, U,
    Li2Lean.V.Q2Certificate.decodeChain,
    Li2Lean.V.Q2Certificate.decodeChainAux,
    Li2Lean.V.Q2Certificate.scaleMass,
    Li2Lean.V.Q2Certificate.scaleLength,
    Li2Lean.V.Q2Certificate.correctedLength,
    IK.qsub, IK.qadd, IK.qneg, IK.val, ENNReal.ofReal_mul]
  simp (disch := positivity) only [← ENNReal.ofReal_mul]
  simp (disch := positivity) only [← ENNReal.ofReal_add]
  norm_num

theorem q6ReferenceRaw_v_mass :
    q6RawReferenceMeasures.μv Set.univ = (5 / 4 : ℝ≥0∞) := by
  unfold q6RawReferenceMeasures v13RefRaw v13DecodedChainMeasure v13ChainMeasureComplex
  rw [Measure.map_apply Complex.measurable_ofReal MeasurableSet.univ]
  rw [Set.preimage_univ, q6_chain_measure_univ]
  norm_num [v13ChainCells, v13ChainCellsAux, q6D, mkIData, chainCP,
    chainCoords, chainMassU, densI, jumpsI, q6DecodedReferenceRows_data, q6YHeader,
    q6YEntries, U, Li2Lean.V.Q2Certificate.decodeChain,
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

theorem q6ReferenceRaw_z_chain_mass :
    v13DecodedChainMeasure q6D.zp Set.univ =
      (56919221 / 100000000 : ℝ≥0∞) := by
  unfold v13DecodedChainMeasure v13ChainMeasureComplex
  rw [Measure.map_apply Complex.measurable_ofReal MeasurableSet.univ]
  rw [Set.preimage_univ, q6_chain_measure_univ]
  norm_num [v13ChainCells, v13ChainCellsAux, q6D, mkIData, chainCP,
    chainCoords, chainMassU, densI, jumpsI, q6ZHeader,
    q6ZEntries, U, Li2Lean.V.Q2Certificate.decodeChain,
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
      (56919221 / 100000000 : ℝ≥0∞) ≠ ⊤)]
  norm_num

private def q6_poisson_inside_pr (r : PR) : Bool :=
  r.cx.1 ^ 2 + r.cy.1 ^ 2 < (30000000000000 : Int) ^ 2

private def q6_poisson_weight_nonneg_pr (r : PR) : Bool :=
  decide (0 ≤ r.w.1)

private theorem q6_poisson_inside_full :
    q6D.full.all q6_poisson_inside_pr = true := by
  decide +kernel

private theorem q6_poisson_weight_nonneg_all :
    q6D.full.all q6_poisson_weight_nonneg_pr = true := by
  decide +kernel

private theorem q6_poisson_full_den_mult {r : PR} (hr : r ∈ q6D.full) :
    r.w.2 = U ∧ r.mult = 1 := by
  change r ∈
    (Li2Lean.V.Q2Certificate.poissonFull
      (Li2Lean.V.Q2Certificate.decodePoisson
        Li2Lean.V.EnergyCertI.q6PoissonPrefix)).map
      (Li2Lean.V.EnergyCertI.prow 1) at hr
  rcases List.mem_map.mp hr with ⟨p, hp, rfl⟩
  constructor <;> rfl

private theorem q6_poisson_real_weight_sum :
    (q6D.full.map (fun r => (r.mult : ℝ) * IK.val r.w)).sum =
      (43080779 / 100000000 : ℝ) := by
  have hterm (r : PR) (hr : r ∈ q6D.full) :
      (r.mult : ℝ) * IK.val r.w = (r.w.1 : ℝ) / (U : ℝ) := by
    rcases q6_poisson_full_den_mult hr with ⟨hd, hm⟩
    rw [IK.val, hm, hd]
    norm_num [U]
  have hsum_units : (q6D.full.map (fun r => r.w.1)).sum =
      (21540389500000 : ℤ) := by
    decide +kernel
  have hsum_scaled (rows : List PR)
      (hrows : ∀ r ∈ rows, r.w.2 = U ∧ r.mult = 1) :
      (rows.map (fun r => (r.mult : ℝ) * IK.val r.w)).sum =
        (((rows.map (fun r => r.w.1)).sum : ℤ) : ℝ) / (U : ℝ) := by
    induction rows with
    | nil => simp
    | cons r rs ih =>
        have hrs : ∀ x ∈ rs, x.w.2 = U ∧ x.mult = 1 := by
          intro x hx
          exact hrows x (by simp [hx])
        have htermRows (x : PR) (hx : x ∈ r :: rs) :
            (x.mult : ℝ) * IK.val x.w = (x.w.1 : ℝ) / (U : ℝ) := by
          rcases hrows x hx with ⟨hd, hm⟩
          rw [IK.val, hm, hd]
          norm_num [U]
        simp only [List.map_cons, List.sum_cons]
        rw [htermRows r (by simp), ih hrs]
        push_cast
        ring
  calc
    _ = (((q6D.full.map (fun r => r.w.1)).sum : ℤ) : ℝ) / (U : ℝ) :=
      hsum_scaled q6D.full (by
        intro r hr
        exact q6_poisson_full_den_mult hr)
    _ = (43080779 / 100000000 : ℝ) := by
      rw [hsum_units]
      norm_num [U]

private theorem q6_poisson_norm_of_inside_pr (r : PR)
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

private theorem q6_poisson_full_norm :
    ∀ r ∈ q6D.full, ‖v13PoissonPoint r‖ < v13GlobalPoissonRadius := by
  intro r hr
  have hinside := (List.all_eq_true.mp q6_poisson_inside_full) r hr
  have hi : r.cx.1 ^ 2 + r.cy.1 ^ 2 < (30000000000000 : Int) ^ 2 := by
    exact of_decide_eq_true hinside
  have hden : r.cx.2 = U ∧ r.cy.2 = U := by
    change r ∈
      (Li2Lean.V.Q2Certificate.poissonFull
        (Li2Lean.V.Q2Certificate.decodePoisson
          Li2Lean.V.EnergyCertI.q6PoissonPrefix)).map
        (Li2Lean.V.EnergyCertI.prow 1) at hr
    rcases List.mem_map.mp hr with ⟨p, hp, rfl⟩
    constructor <;> rfl
  exact q6_poisson_norm_of_inside_pr r hden.1 hden.2 hi

private theorem q6_poisson_atom_univ {r : PR}
    (hp : ‖v13PoissonPoint r‖ < v13GlobalPoissonRadius) :
    v13PoissonAtom r Set.univ =
      ENNReal.ofReal ((r.mult : ℝ) * IK.val r.w) := by
  rw [v13PoissonAtom, Measure.smul_apply,
    v13GlobalCirclePoissonMeasure_univ hp]
  simp [smul_eq_mul]

private theorem q6_poisson_measure_univ_of_inside
    (rows : List PR)
    (hrows : ∀ r ∈ rows, ‖v13PoissonPoint r‖ < v13GlobalPoissonRadius) :
    v13PoissonMeasure rows Set.univ =
      (rows.map (fun r => ENNReal.ofReal ((r.mult : ℝ) * IK.val r.w))).sum := by
  induction rows with
  | nil => simp [v13PoissonMeasure]
  | cons r rs ih =>
      simp only [v13PoissonMeasure, List.map_cons, List.sum_cons]
      change (v13PoissonAtom r + v13PoissonMeasure rs) Set.univ = _
      rw [Measure.add_apply, q6_poisson_atom_univ (hrows r (by simp))]
      rw [ih (fun r hr => hrows r (by simp [hr]))]

theorem q6ReferenceRaw_poisson_mass :
    v13PoissonMeasure q6D.full Set.univ =
      (43080779 / 100000000 : ℝ≥0∞) := by
  rw [q6_poisson_measure_univ_of_inside q6D.full q6_poisson_full_norm]
  have hweight : ∀ r ∈ q6D.full,
      0 ≤ (r.mult : ℝ) * IK.val r.w := by
    intro r hr
    have hw := (List.all_eq_true.mp q6_poisson_weight_nonneg_all) r hr
    have hw0 : 0 ≤ r.w.1 := of_decide_eq_true hw
    rw [IK.val]
    exact mul_nonneg (by positivity)
      (div_nonneg (by exact_mod_cast hw0) (by positivity))
  rw [q6_list_ofReal_sum q6D.full
    (fun r => (r.mult : ℝ) * IK.val r.w) hweight]
  rw [q6_poisson_real_weight_sum]
  rw [← ENNReal.ofReal_toReal
    (ENNReal.div_ne_top (by norm_num) (by norm_num) :
      (43080779 / 100000000 : ℝ≥0∞) ≠ ⊤)]
  norm_num

theorem q6ReferenceRaw_z_mass :
    q6RawReferenceMeasures.μz Set.univ = (1 : ℝ≥0∞) := by
  change (v13DecodedChainMeasure q6D.zp + v13PoissonMeasure q6D.full) Set.univ = _
  rw [Measure.add_apply, q6ReferenceRaw_z_chain_mass,
    q6ReferenceRaw_poisson_mass]
  have h1 : (56919221 / 100000000 : ℝ≥0∞) =
      ENNReal.ofReal ((56919221 : ℝ) / 100000000) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 100000000)]
    norm_num
  have h2 : (43080779 / 100000000 : ℝ≥0∞) =
      ENNReal.ofReal ((43080779 : ℝ) / 100000000) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 100000000)]
    norm_num
  rw [h1, h2, ← ENNReal.ofReal_add (by positivity) (by positivity)]
  norm_num

theorem q6ReferenceNormalization :
    V13MeasureNormalization q6ReferenceBaseRange q6RawReferenceMeasures := by
  refine ⟨q6ReferenceRaw_x_mass, q6ReferenceRaw_v_mass,
    q6ReferenceRaw_z_mass, ?_, ?_, ?_⟩
  · rw [q6ReferenceRaw_x_mass]
    norm_num
  · rw [q6ReferenceRaw_v_mass]
    exact ENNReal.div_ne_top (by norm_num) (by norm_num)
  · rw [q6ReferenceRaw_z_mass]
    norm_num

#print axioms Li2Lean.B3.q6ReferenceNormalization

end B3

end

end Li2Lean

#print axioms Li2Lean.B3.q6ReferenceRaw_x_mass
