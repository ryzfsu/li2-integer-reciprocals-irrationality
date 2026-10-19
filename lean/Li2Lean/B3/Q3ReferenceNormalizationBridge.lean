/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
/-
Finite q = 3 normalization bridge for the generic decoded source.

The x and v masses are transported from the existing q3 reference facts; the
z mass is evaluated from the v13 z rows and Poisson table.  This module proves
only the explicit normalization boundary.  Field, energy, and total identity
certificates remain separate obligations.
-/
import Li2Lean.B3.Q3ReferenceMeasureFacts
import Li2Lean.B3.Q3ReferenceMassBridges
import Li2Lean.B3.V13ChainEnergy

namespace Li2Lean.B3
noncomputable section
open MeasureTheory Set
open V
open V.EnergyCertI
open V.EnergyCertI.IK
open scoped ENNReal

private theorem q3_chain_measure_univ_probe (cells : List V13ChainCell) :
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

private theorem q3_chain_complex_univ_probe (cells : List V13ChainCell) :
    v13ChainMeasureComplex cells Set.univ =
      (cells.map (fun c => ENNReal.ofReal c.density *
        ENNReal.ofReal (c.right - c.left))).sum := by
  unfold v13ChainMeasureComplex
  rw [Measure.map_apply Complex.measurable_ofReal MeasurableSet.univ]
  rw [Set.preimage_univ, q3_chain_measure_univ_probe]

private def q3_poisson_inside_pr (r : PR) : Bool :=
  r.cx.1 ^ 2 + r.cy.1 ^ 2 < (30000000000000 : Int) ^ 2

private theorem q3_poisson_inside_full :
    q3D.full.all q3_poisson_inside_pr = true := by
  norm_num [q3D, mkIData, q3PoissonPrefix, q3_poisson_inside_pr,
    Li2Lean.V.Q2Certificate.poissonFull,
    Li2Lean.V.Q2Certificate.conjugatePoisson,
    Li2Lean.V.Q2Certificate.decodePoisson,
    Li2Lean.V.Q2Certificate.decodePoissonAux,
    Li2Lean.V.EnergyCertI.prow, U]

private theorem q3_poisson_norm_of_inside_pr (r : PR)
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

private theorem q3_poisson_full_norm :
    ∀ r ∈ q3D.full, ‖v13PoissonPoint r‖ < v13GlobalPoissonRadius := by
  intro r hr
  have hinside := (List.all_eq_true.mp q3_poisson_inside_full) r hr
  have hi : r.cx.1 ^ 2 + r.cy.1 ^ 2 < (30000000000000 : Int) ^ 2 :=
    of_decide_eq_true hinside
  have hden : r.cx.2 = U ∧ r.cy.2 = U := by
    change r ∈
      (Li2Lean.V.Q2Certificate.poissonFull
        (Li2Lean.V.Q2Certificate.decodePoisson q3PoissonPrefix)).map
        (Li2Lean.V.EnergyCertI.prow 1) at hr
    rcases List.mem_map.mp hr with ⟨p, hp, rfl⟩
    constructor <;> rfl
  exact q3_poisson_norm_of_inside_pr r hden.1 hden.2 hi

private theorem q3_poisson_atom_univ {r : PR}
    (hp : ‖v13PoissonPoint r‖ < v13GlobalPoissonRadius) :
    v13PoissonAtom r Set.univ =
      ENNReal.ofReal ((r.mult : ℝ) * IK.val r.w) := by
  rw [v13PoissonAtom, Measure.smul_apply,
    v13GlobalCirclePoissonMeasure_univ hp]
  simp [smul_eq_mul]

private theorem q3_poisson_measure_univ_of_inside
    (rows : List PR)
    (hrows : ∀ r ∈ rows, ‖v13PoissonPoint r‖ < v13GlobalPoissonRadius) :
    v13PoissonMeasure rows Set.univ =
      (rows.map (fun r => ENNReal.ofReal ((r.mult : ℝ) * IK.val r.w))).sum := by
  induction rows with
  | nil => simp [v13PoissonMeasure]
  | cons r rs ih =>
      simp only [v13PoissonMeasure, List.map_cons, List.sum_cons]
      change (v13PoissonAtom r + v13PoissonMeasure rs) Set.univ = _
      rw [Measure.add_apply, q3_poisson_atom_univ (hrows r (by simp))]
      rw [ih (fun r hr => hrows r (by simp [hr]))]

set_option maxHeartbeats 2000000 in
theorem q3_raw_z_mass_bridge :
    (v13RefRaw q3DecodedRows).μz Set.univ = (1 : ℝ≥0∞) := by
  change (v13DecodedChainMeasure q3D.zp + v13PoissonMeasure q3D.full) Set.univ = _
  rw [Measure.add_apply]
  change v13ChainMeasureComplex (v13ChainCells q3D.zp) Set.univ +
      (v13PoissonMeasure q3D.full) Set.univ = _
  rw [q3_chain_complex_univ_probe]
  rw [q3_poisson_measure_univ_of_inside q3D.full q3_poisson_full_norm]
  norm_num [v13ChainCells, v13ChainCellsAux, q3D, mkIData, chainCP,
    chainCoords, chainMassU, densI, jumpsI, q3ZHeader, q3ZEntries,
    Li2Lean.V.Q2Certificate.decodeChain,
    Li2Lean.V.Q2Certificate.decodeChainAux,
    Li2Lean.V.Q2Certificate.scaleMass,
    Li2Lean.V.Q2Certificate.scaleLength,
    Li2Lean.V.Q2Certificate.correctedLength,
    v13PoissonMeasure, v13PoissonAtom,
    Li2Lean.V.Q2Certificate.poissonFull,
    Li2Lean.V.Q2Certificate.decodePoisson,
    Li2Lean.V.Q2Certificate.decodePoissonAux,
    Li2Lean.V.Q2Certificate.conjugatePoisson,
    Li2Lean.V.EnergyCertI.prow, q3PoissonPrefix, U,
    IK.qsub, IK.qadd, IK.qneg, IK.val,
    ENNReal.ofReal_mul]
  simp (disch := positivity) only [← ENNReal.ofReal_mul]
  simp (disch := positivity) only [← ENNReal.ofReal_add]
  norm_num

theorem q3ReferenceNormalization_of_hq (hq : SignedVBaseRange 3) :
    V13MeasureNormalization hq (v13RefRaw q3DecodedRows) := by
  refine ⟨q3_raw_x_mass_bridge, q3_raw_v_mass_bridge,
    q3_raw_z_mass_bridge, ?_, ?_, ?_⟩
  · rw [q3_raw_x_mass_bridge]
    norm_num
  · rw [q3_raw_v_mass_bridge]
    exact ENNReal.div_ne_top (by norm_num) (by norm_num)
  · rw [q3_raw_z_mass_bridge]
    norm_num

#print axioms Li2Lean.B3.q3_raw_z_mass_bridge
#print axioms Li2Lean.B3.q3ReferenceNormalization_of_hq

end
end Li2Lean.B3

