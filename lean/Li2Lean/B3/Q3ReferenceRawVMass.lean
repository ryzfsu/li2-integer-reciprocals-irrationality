/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Finite mass check for the q = 3 v-chain decoded from the v13 rows.
-/

import Li2Lean.B3.EnergySoundnessInputs
import Li2Lean.B3.V13ReferenceMeasure
import Li2Lean.B3.V13ChainEnergy
import Li2Lean.V.EnergyCertI.Q3Rows

namespace Li2Lean

noncomputable section

namespace B3

open MeasureTheory Set
open V.EnergyCertI
open V.EnergyCertI.IK
open scoped ENNReal

/-- The raw q = 3 v-measure has the prescribed mass `5/4`. -/
theorem q3ReferenceRaw_v_mass :
    v13DecodedChainMeasure V.EnergyCertI.q3D.vp Set.univ =
      (5 / 4 : ℝ≥0∞) := by
  have hchain (cells : List V13ChainCell) :
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
  unfold v13DecodedChainMeasure v13ChainMeasureComplex
  rw [Measure.map_apply Complex.measurable_ofReal MeasurableSet.univ]
  rw [Set.preimage_univ, hchain]
  norm_num [v13ChainCells, v13ChainCellsAux, V.EnergyCertI.q3D,
    mkIData, chainCP,
    chainCoords, chainMassU, densI, jumpsI, q3YHeader,
    q3YEntries, U, Li2Lean.V.Q2Certificate.decodeChain,
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

end B3

end

end Li2Lean

#print axioms Li2Lean.B3.q3ReferenceRaw_v_mass
