/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Finite normalization checks for the concrete q = 4 rows.  These lemmas only
evaluate the decoded chain and Poisson masses; analytic field and energy
soundness remain separate obligations.
-/

import Li2Lean.B3.Q4ReferenceMeasureFacts
import Li2Lean.B3.V13ChainEnergy

namespace Li2Lean

noncomputable section

namespace B3

open MeasureTheory Set
open V
open V.EnergyCertI
open V.EnergyCertI.IK
open scoped ENNReal

private theorem q4_chain_measure_univ (cells : List V13ChainCell) :
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

private theorem q4_chain_complex_univ (cells : List V13ChainCell) :
    v13ChainMeasureComplex cells Set.univ =
      (cells.map (fun c => ENNReal.ofReal c.density *
        ENNReal.ofReal (c.right - c.left))).sum := by
  unfold v13ChainMeasureComplex
  rw [Measure.map_apply Complex.measurable_ofReal MeasurableSet.univ]
  rw [Set.preimage_univ, q4_chain_measure_univ]

theorem q4ReferenceRaw_x_mass :
    q4RawReferenceMeasures.μx Set.univ = (1 : ℝ≥0∞) := by
  unfold q4RawReferenceMeasures v13RefRaw v13DecodedChainMeasure
    v13ChainMeasureComplex
  rw [Measure.map_apply Complex.measurable_ofReal MeasurableSet.univ]
  rw [Set.preimage_univ, q4_chain_measure_univ]
  norm_num [v13ChainCells, v13ChainCellsAux, q4DecodedRows, q4D, mkIData, chainCP,
    chainCoords, chainMassU, densI, jumpsI, q4XHeader, q4XEntries, U,
    Li2Lean.V.Q2Certificate.decodeChain,
    Li2Lean.V.Q2Certificate.decodeChainAux,
    Li2Lean.V.Q2Certificate.scaleMass,
    Li2Lean.V.Q2Certificate.scaleLength,
    Li2Lean.V.Q2Certificate.correctedLength,
    IK.qsub, IK.qadd, IK.qneg, IK.val, ENNReal.ofReal_mul]
  simp (disch := norm_num) only [← ENNReal.ofReal_mul]
  simp (disch := norm_num) only [← ENNReal.ofReal_add]
  norm_num

theorem q4ReferenceRaw_v_mass :
    q4RawReferenceMeasures.μv Set.univ = (5 / 4 : ℝ≥0∞) := by
  unfold q4RawReferenceMeasures v13RefRaw v13DecodedChainMeasure
    v13ChainMeasureComplex
  rw [Measure.map_apply Complex.measurable_ofReal MeasurableSet.univ]
  rw [Set.preimage_univ, q4_chain_measure_univ]
  norm_num [v13ChainCells, v13ChainCellsAux, q4DecodedRows, q4D, mkIData, chainCP,
    chainCoords, chainMassU, densI, jumpsI, q4YHeader, q4YEntries, U,
    Li2Lean.V.Q2Certificate.decodeChain,
    Li2Lean.V.Q2Certificate.decodeChainAux,
    Li2Lean.V.Q2Certificate.scaleMass,
    Li2Lean.V.Q2Certificate.scaleLength,
    Li2Lean.V.Q2Certificate.correctedLength,
    IK.qsub, IK.qadd, IK.qneg, IK.val, ENNReal.ofReal_mul]
  simp (disch := norm_num) only [← ENNReal.ofReal_mul]
  simp (disch := norm_num) only [← ENNReal.ofReal_add]
  rw [← ENNReal.ofReal_toReal
    (ENNReal.div_ne_top (by norm_num) (by norm_num) :
      (5 / 4 : ℝ≥0∞) ≠ ⊤)]
  norm_num

theorem q4ReferenceRaw_z_chain_mass :
    v13DecodedChainMeasure q4D.zp Set.univ =
      (6182197 / 12500000 : ℝ≥0∞) := by
  unfold v13DecodedChainMeasure v13ChainMeasureComplex
  rw [Measure.map_apply Complex.measurable_ofReal MeasurableSet.univ]
  rw [Set.preimage_univ, q4_chain_measure_univ]
  norm_num [v13ChainCells, v13ChainCellsAux, q4D, mkIData, chainCP,
    chainCoords, chainMassU, densI, jumpsI, q4ZHeader, q4ZEntries, U,
    Li2Lean.V.Q2Certificate.decodeChain,
    Li2Lean.V.Q2Certificate.decodeChainAux,
    Li2Lean.V.Q2Certificate.scaleMass,
    Li2Lean.V.Q2Certificate.scaleLength,
    Li2Lean.V.Q2Certificate.correctedLength,
    IK.qsub, IK.qadd, IK.qneg, IK.val, ENNReal.ofReal_mul]
  simp (disch := norm_num) only [← ENNReal.ofReal_mul]
  simp (disch := norm_num) only [← ENNReal.ofReal_add]
  rw [← ENNReal.ofReal_toReal
    (ENNReal.div_ne_top (by norm_num) (by norm_num) :
      (6182197 / 12500000 : ℝ≥0∞) ≠ ⊤)]
  norm_num

private def q4_poisson_inside (p : Li2Lean.V.Q2Certificate.PoissonPoint) : Bool :=
  p.xUnits ^ 2 + p.yUnits ^ 2 < (30000000000000 : Int) ^ 2

private theorem q4_poisson_inside_all :
    (Li2Lean.V.Q2Certificate.decodePoisson q4PoissonPrefix).all
      q4_poisson_inside = true := by
  decide +kernel

private def q4_poisson_inside_pr (r : PR) : Bool :=
  r.cx.1 ^ 2 + r.cy.1 ^ 2 < (30000000000000 : Int) ^ 2

private theorem q4_poisson_inside_full :
    q4D.full.all q4_poisson_inside_pr = true := by
  decide +kernel

private theorem q4_poisson_norm_of_inside_pr (r : PR)
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

private theorem q4_poisson_full_norm :
    ∀ r ∈ q4D.full, ‖v13PoissonPoint r‖ < v13GlobalPoissonRadius := by
  intro r hr
  have hinside := (List.all_eq_true.mp q4_poisson_inside_full) r hr
  have hi : r.cx.1 ^ 2 + r.cy.1 ^ 2 < (30000000000000 : Int) ^ 2 :=
    of_decide_eq_true hinside
  have hden : r.cx.2 = U ∧ r.cy.2 = U := by
    change r ∈
      (Li2Lean.V.Q2Certificate.poissonFull
        (Li2Lean.V.Q2Certificate.decodePoisson q4PoissonPrefix)).map
        (Li2Lean.V.EnergyCertI.prow 1) at hr
    rcases List.mem_map.mp hr with ⟨p, hp, rfl⟩
    constructor <;> rfl
  exact q4_poisson_norm_of_inside_pr r hden.1 hden.2 hi

private theorem q4_poisson_atom_univ {r : PR}
    (hp : ‖v13PoissonPoint r‖ < v13GlobalPoissonRadius) :
    v13PoissonAtom r Set.univ =
      ENNReal.ofReal ((r.mult : ℝ) * IK.val r.w) := by
  rw [v13PoissonAtom, Measure.smul_apply,
    v13GlobalCirclePoissonMeasure_univ hp]
  simp [smul_eq_mul]

private theorem q4_poisson_measure_univ_of_inside
    (rows : List PR)
    (hrows : ∀ r ∈ rows, ‖v13PoissonPoint r‖ < v13GlobalPoissonRadius) :
    v13PoissonMeasure rows Set.univ =
      (rows.map (fun r => ENNReal.ofReal ((r.mult : ℝ) * IK.val r.w))).sum := by
  induction rows with
  | nil => simp [v13PoissonMeasure]
  | cons r rs ih =>
      simp only [v13PoissonMeasure, List.map_cons, List.sum_cons]
      change (v13PoissonAtom r + v13PoissonMeasure rs) Set.univ = _
      rw [Measure.add_apply, q4_poisson_atom_univ (hrows r (by simp))]
      rw [ih (fun r hr => hrows r (by simp [hr]))]

theorem q4ReferenceRaw_poisson_mass :
    v13PoissonMeasure q4D.full Set.univ =
      (6317803 / 12500000 : ℝ≥0∞) := by
  rw [q4_poisson_measure_univ_of_inside q4D.full q4_poisson_full_norm]
  norm_num [q4D, mkIData, v13PoissonMeasure, v13PoissonAtom,
    Li2Lean.V.Q2Certificate.poissonFull,
    Li2Lean.V.Q2Certificate.decodePoisson,
    Li2Lean.V.Q2Certificate.decodePoissonAux,
    Li2Lean.V.Q2Certificate.conjugatePoisson,
    Li2Lean.V.EnergyCertI.prow, q4PoissonPrefix, U, IK.val,
    ENNReal.ofReal_mul]
  simp (disch := positivity) only [← ENNReal.ofReal_add]
  rw [← ENNReal.ofReal_toReal
    (ENNReal.div_ne_top (by norm_num) (by norm_num) :
      (6317803 / 12500000 : ℝ≥0∞) ≠ ⊤)]
  norm_num

theorem q4ReferenceRaw_z_mass :
    q4RawReferenceMeasures.μz Set.univ = (1 : ℝ≥0∞) := by
  change (v13DecodedChainMeasure q4D.zp + v13PoissonMeasure q4D.full) Set.univ = _
  rw [Measure.add_apply, q4ReferenceRaw_z_chain_mass,
    q4ReferenceRaw_poisson_mass]
  have h1 : (6182197 / 12500000 : ℝ≥0∞) =
      ENNReal.ofReal ((6182197 : ℝ) / 12500000) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 12500000)]
    norm_num
  have h2 : (6317803 / 12500000 : ℝ≥0∞) =
      ENNReal.ofReal ((6317803 : ℝ) / 12500000) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 12500000)]
    norm_num
  rw [h1, h2, ← ENNReal.ofReal_add (by positivity) (by positivity)]
  norm_num

theorem q4ReferenceNormalization :
    q4ReferenceNormalizationGoal := by
  refine ⟨q4ReferenceRaw_x_mass, q4ReferenceRaw_v_mass,
    q4ReferenceRaw_z_mass, ?_, ?_, ?_⟩
  · rw [q4ReferenceRaw_x_mass]
    norm_num
  · rw [q4ReferenceRaw_v_mass]
    exact ENNReal.div_ne_top (by norm_num) (by norm_num)
  · rw [q4ReferenceRaw_z_mass]
    norm_num

end B3

end

end Li2Lean

#print axioms Li2Lean.B3.q4ReferenceNormalization
