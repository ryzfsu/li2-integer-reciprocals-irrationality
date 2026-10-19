/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license.

Concrete q = 5 raw measure facts.  The proof follows the q = 2
normalization calculation and unfolds only the pinned v13 q5 decoder rows.
-/

import Li2Lean.B3.Q5ReferencePackageAssembly
import Li2Lean.B3.V13ChainEnergy

namespace Li2Lean

noncomputable section

namespace B3

open V.EnergyCertI
open MeasureTheory Set
open scoped ENNReal

private theorem q5_chain_measure_univ (cells : List V13ChainCell) :
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

theorem q5ReferenceRaw_x_mass :
    q5RawReferenceMeasures.μx Set.univ = (1 : ℝ≥0∞) := by
  unfold q5RawReferenceMeasures v13RefRaw v13DecodedChainMeasure
    v13ChainMeasureComplex
  rw [Measure.map_apply Complex.measurable_ofReal MeasurableSet.univ]
  rw [Set.preimage_univ, q5_chain_measure_univ]
  norm_num [v13ChainCells, v13ChainCellsAux, q5DecodedReferenceRows, q5D, mkIData, chainCP,
    chainCoords, chainMassU, densI, jumpsI, q5XHeader,
    q5XEntries, U, Li2Lean.V.Q2Certificate.decodeChain,
    Li2Lean.V.Q2Certificate.decodeChainAux,
    Li2Lean.V.Q2Certificate.scaleMass,
    Li2Lean.V.Q2Certificate.scaleLength,
    Li2Lean.V.Q2Certificate.correctedLength,
    IK.qsub, IK.qadd, IK.qneg, IK.val,
    ENNReal.ofReal_mul]
  try simp (disch := positivity) only [← ENNReal.ofReal_mul]
  try simp (disch := positivity) only [← ENNReal.ofReal_add]
  norm_num

theorem q5ReferenceRaw_v_mass :
    q5RawReferenceMeasures.μv Set.univ = (5 / 4 : ℝ≥0∞) := by
  unfold q5RawReferenceMeasures v13RefRaw v13DecodedChainMeasure
    v13ChainMeasureComplex
  rw [Measure.map_apply Complex.measurable_ofReal MeasurableSet.univ]
  rw [Set.preimage_univ, q5_chain_measure_univ]
  norm_num [v13ChainCells, v13ChainCellsAux, q5DecodedReferenceRows, q5D, mkIData, chainCP,
    chainCoords, chainMassU, densI, jumpsI, q5YHeader,
    q5YEntries, U, Li2Lean.V.Q2Certificate.decodeChain,
    Li2Lean.V.Q2Certificate.decodeChainAux,
    Li2Lean.V.Q2Certificate.scaleMass,
    Li2Lean.V.Q2Certificate.scaleLength,
    Li2Lean.V.Q2Certificate.correctedLength,
    IK.qsub, IK.qadd, IK.qneg, IK.val,
    ENNReal.ofReal_mul]
  try simp (disch := positivity) only [← ENNReal.ofReal_mul]
  try simp (disch := positivity) only [← ENNReal.ofReal_add]
  rw [← ENNReal.ofReal_toReal
    (ENNReal.div_ne_top (by norm_num) (by norm_num) :
      (5 / 4 : ℝ≥0∞) ≠ ⊤)]
  norm_num

end B3

end

end Li2Lean
