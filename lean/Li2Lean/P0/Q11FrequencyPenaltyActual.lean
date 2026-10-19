/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.Q11FrequencyPrefixActual
import Li2Lean.P0.Q11FrequencyRowCheck
import Li2Lean.P0.Q11FrequencyIntCert
import Li2Lean.P0.Q11FrequencyPenaltyRowsAgy
import Li2Lean.P0.Q11PenaltyRowsProducer

namespace Li2Lean.P0.Q11Data

open Li2Lean.F_L8
open Li2Lean.P0.CA.Frequency
open Li2Lean.P0.CA.Receipt

/-- The 44-cell tail on `[289/160, 81/10]`; every cell uses the
    certified floor `1217/200`, so this tail contributes no penalty. -/
def q11FrequencyTailCells : List ReceiptCell := [
  ⟨(289 / 160 : ℚ), (74399 / 40960 : ℚ), (1217 / 200 : ℚ)⟩,
  ⟨(74399 / 40960 : ℚ), (74861 / 40960 : ℚ), (1217 / 200 : ℚ)⟩,
  ⟨(74861 / 40960 : ℚ), (4711 / 2560 : ℚ), (1217 / 200 : ℚ)⟩,
  ⟨(4711 / 2560 : ℚ), (4747 / 2560 : ℚ), (1217 / 200 : ℚ)⟩,
  ⟨(4747 / 2560 : ℚ), (19149 / 10240 : ℚ), (1217 / 200 : ℚ)⟩,
  ⟨(19149 / 10240 : ℚ), (77317 / 40960 : ℚ), (1217 / 200 : ℚ)⟩,
  ⟨(77317 / 40960 : ℚ), (39063 / 20480 : ℚ), (1217 / 200 : ℚ)⟩,
  ⟨(39063 / 20480 : ℚ), (39517 / 20480 : ℚ), (1217 / 200 : ℚ)⟩,
  ⟨(39517 / 20480 : ℚ), (80053 / 40960 : ℚ), (1217 / 200 : ℚ)⟩,
  ⟨(80053 / 40960 : ℚ), (40599 / 20480 : ℚ), (1217 / 200 : ℚ)⟩,
  ⟨(40599 / 20480 : ℚ), (20621 / 10240 : ℚ), (1217 / 200 : ℚ)⟩,
  ⟨(20621 / 10240 : ℚ), (41963 / 20480 : ℚ), (1217 / 200 : ℚ)⟩,
  ⟨(41963 / 20480 : ℚ), (85541 / 40960 : ℚ), (1217 / 200 : ℚ)⟩,
  ⟨(85541 / 40960 : ℚ), (5459 / 2560 : ℚ), (1217 / 200 : ℚ)⟩,
  ⟨(5459 / 2560 : ℚ), (22337 / 10240 : ℚ), (1217 / 200 : ℚ)⟩,
  ⟨(22337 / 10240 : ℚ), (91563 / 40960 : ℚ), (1217 / 200 : ℚ)⟩,
  ⟨(91563 / 40960 : ℚ), (93989 / 40960 : ℚ), (1217 / 200 : ℚ)⟩,
  ⟨(93989 / 40960 : ℚ), (48307 / 20480 : ℚ), (1217 / 200 : ℚ)⟩,
  ⟨(48307 / 20480 : ℚ), (99397 / 40960 : ℚ), (1217 / 200 : ℚ)⟩,
  ⟨(99397 / 40960 : ℚ), (51107 / 20480 : ℚ), (1217 / 200 : ℚ)⟩,
  ⟨(51107 / 20480 : ℚ), (52501 / 20480 : ℚ), (1217 / 200 : ℚ)⟩,
  ⟨(52501 / 20480 : ℚ), (26981 / 10240 : ℚ), (1217 / 200 : ℚ)⟩,
  ⟨(26981 / 10240 : ℚ), (11105 / 4096 : ℚ), (1217 / 200 : ℚ)⟩,
  ⟨(11105 / 4096 : ℚ), (57219 / 20480 : ℚ), (1217 / 200 : ℚ)⟩,
  ⟨(57219 / 20480 : ℚ), (118143 / 40960 : ℚ), (1217 / 200 : ℚ)⟩,
  ⟨(118143 / 40960 : ℚ), (6111 / 2048 : ℚ), (1217 / 200 : ℚ)⟩,
  ⟨(6111 / 2048 : ℚ), (63363 / 20480 : ℚ), (1217 / 200 : ℚ)⟩,
  ⟨(63363 / 20480 : ℚ), (3293 / 1024 : ℚ), (1217 / 200 : ℚ)⟩,
  ⟨(3293 / 1024 : ℚ), (8579 / 2560 : ℚ), (1217 / 200 : ℚ)⟩,
  ⟨(8579 / 2560 : ℚ), (143419 / 40960 : ℚ), (1217 / 200 : ℚ)⟩,
  ⟨(143419 / 40960 : ℚ), (150237 / 40960 : ℚ), (1217 / 200 : ℚ)⟩,
  ⟨(150237 / 40960 : ℚ), (9861 / 2560 : ℚ), (1217 / 200 : ℚ)⟩,
  ⟨(9861 / 2560 : ℚ), (166107 / 40960 : ℚ), (1217 / 200 : ℚ)⟩,
  ⟨(166107 / 40960 : ℚ), (35061 / 8192 : ℚ), (1217 / 200 : ℚ)⟩,
  ⟨(35061 / 8192 : ℚ), (37089 / 8192 : ℚ), (1217 / 200 : ℚ)⟩,
  ⟨(37089 / 8192 : ℚ), (196603 / 40960 : ℚ), (1217 / 200 : ℚ)⟩,
  ⟨(196603 / 40960 : ℚ), (208857 / 40960 : ℚ), (1217 / 200 : ℚ)⟩,
  ⟨(208857 / 40960 : ℚ), (13893 / 2560 : ℚ), (1217 / 200 : ℚ)⟩,
  ⟨(13893 / 2560 : ℚ), (118489 / 20480 : ℚ), (1217 / 200 : ℚ)⟩,
  ⟨(118489 / 20480 : ℚ), (253009 / 40960 : ℚ), (1217 / 200 : ℚ)⟩,
  ⟨(253009 / 40960 : ℚ), (270467 / 40960 : ℚ), (1217 / 200 : ℚ)⟩,
  ⟨(270467 / 40960 : ℚ), (289439 / 40960 : ℚ), (1217 / 200 : ℚ)⟩,
  ⟨(289439 / 40960 : ℚ), (310013 / 40960 : ℚ), (1217 / 200 : ℚ)⟩,
  ⟨(310013 / 40960 : ℚ), (81 / 10 : ℚ), (1217 / 200 : ℚ)⟩
]

theorem q11FrequencyTailCells_chain_check :
    chainCheck q11FrequencyTailCells (289 / 160 : ℚ) (81 / 10 : ℚ) = true :=
  chainCheck_eq_true_of_chainCheckZ (by decide +kernel)

theorem q11FrequencyTailCells_chain :
    ExactChain q11FrequencyTailCells (289 / 160 : ℚ) (81 / 10 : ℚ) :=
  chainCheck_sound q11FrequencyTailCells_chain_check

theorem q11FrequencyTailCells_check :
    q11FrequencyTailCells.all q11CellCheck = true :=
  all_q11CellCheck_of_all_q11CellCheckZ (by decide +kernel)

theorem q11FrequencyTailCells_lower :
    Q11FrequencyCellsLower q11FrequencyTailCells := by
  intro c hc t hlo hhi
  exact q11CellCheck_sound (List.all_eq_true.mp q11FrequencyTailCells_check c hc)
    hlo hhi

theorem q11FrequencyTailCells_penalty :
    penaltyMass (1217 / 200 : ℚ) 0 q11FrequencyTailCells = 0 :=
  penaltyMass_eq_zero_of_penaltyMassZCheck (by decide +kernel)

def q11FrequencyCellsActual : List ReceiptCell :=
  q11FrequencyPrefixRows ++ q11FrequencyTailCells

theorem q11FrequencyCellsActual_chain :
    ExactChain q11FrequencyCellsActual (1 / 2 : ℚ) (81 / 10 : ℚ) := by
  unfold q11FrequencyCellsActual
  exact exactChain_append
    (List.ne_nil_of_length_pos (by decide +kernel))
    q11FrequencyPrefixRows_chain q11FrequencyTailCells_chain

theorem q11FrequencyCellsActual_lower :
    Q11FrequencyCellsLower q11FrequencyCellsActual := by
  intro c hc t hlo hhi
  rcases List.mem_append.mp hc with hc | hc
  · exact q11FrequencyPrefixRows_lower c hc t hlo hhi
  · exact q11FrequencyTailCells_lower c hc t hlo hhi

theorem q11FrequencyCellsActual_lower_with_zero :
    ∀ c ∈ q11FrequencyCellsActual, ∀ t : ℝ,
      (c.lo : ℝ) ≤ t → t ≤ (c.hi : ℝ) →
        ((c.lower : ℝ) - ((0 : ℚ) : ℝ)) ≤ q11Wmu t := by
  intro c hc t hlo hhi
  simpa using q11FrequencyCellsActual_lower c hc t hlo hhi

theorem q11FrequencyCellsActual_penalty :
    penaltyMass (1217 / 200 : ℚ) 0 q11FrequencyCellsActual =
      (437939106871569 / 409600000000000 : ℚ) := by
  rw [q11FrequencyCellsActual, penaltyMass_append,
    q11FrequencyPrefixRows_penalty, q11FrequencyTailCells_penalty, add_zero]

noncomputable def q11FrequencyPenaltyRowsV13_actual :
    Q11FrequencyPenaltyRowsV13 where
  cells := q11FrequencyCellsActual
  allowance := 0
  chain := q11FrequencyCellsActual_chain
  lower := q11FrequencyCellsActual_lower_with_zero
  mass_le := by
    rw [q11FrequencyFloorQ_eq, q11FrequencyPenaltyUpperQ_eq,
      q11FrequencyCellsActual_penalty]
    norm_num
  integrable :=
    q11FrequencyPenalty_integrable_of_lower_audit q11FrequencyCellsActual 0
      q11FrequencyCellsActual_chain q11FrequencyCellsActual_lower_with_zero
      measurable_q11Wmu

theorem q11FrequencyPenaltyRowsV13_actual_nonempty :
    Nonempty Q11FrequencyPenaltyRowsV13 :=
  ⟨q11FrequencyPenaltyRowsV13_actual⟩

#print axioms q11FrequencyPenaltyRowsV13_actual
end Li2Lean.P0.Q11Data
