/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.AllN.R3Q11PinnedFloor
import Li2Lean.P0.Q11PenaltyRowsProducer

/-! The complete pinned-row packet consumed by the existing q = 11 producer.
The proved global floor permits one cell with zero allowance and zero mass. -/

namespace Li2Lean.P0.Q11Data

noncomputable section

open MeasureTheory Set Li2Lean.F_L8 CA.Receipt

def r3_q11_pinned_penalty_rows : Q11PinnedPenaltyRowsV13 where
  cells := [⟨1 / 4, 5 / 4, q11EtaFloorQ⟩]
  allowance := 0
  chain := ExactChain.one _ _ _ rfl rfl (by norm_num)
  lower := by
    intro c hc x hlo hhi
    simp only [List.mem_singleton] at hc
    subst c
    have hx : x ∈ Set.Icc (1 / 4 : ℝ) (5 / 4 : ℝ) := by
      constructor
      · simpa using hlo
      · simpa using hhi
    simpa [q11EtaFloorQ_eq, neg_div] using r3_q11_pinned_floor hx
  mass_le := by
    norm_num [penaltyMass, q11PinnedPenaltyUpperQ_eq]
  integrable := by
    refine IntegrableOn.congr_fun (f := fun _ : ℝ => (0 : ℝ))
      integrableOn_zero ?_ measurableSet_Icc
    intro x hx
    have hfloor : (q11EtaFloorQ : ℝ) ≤ q11Weta (x : ℂ) := by
      simpa [q11EtaFloorQ_eq, neg_div] using r3_q11_pinned_floor hx
    exact (max_eq_right (sub_nonpos.mpr hfloor)).symm

theorem r3_q11_pinned_penalty_rows_nonempty :
    Nonempty Q11PinnedPenaltyRowsV13 :=
  ⟨r3_q11_pinned_penalty_rows⟩

end

end Li2Lean.P0.Q11Data

#print axioms Li2Lean.P0.Q11Data.r3_q11_pinned_penalty_rows
#print axioms Li2Lean.P0.Q11Data.r3_q11_pinned_penalty_rows_nonempty
