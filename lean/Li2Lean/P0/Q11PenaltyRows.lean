/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.Q11EndpointBridge
import Li2Lean.P0.CA.Receipt.Penalty

/-!
q = 11 finite-row interface for the two actual positive-part penalties.

The row lists are producer inputs: this file does not manufacture a
continuum C-A certificate from scalar table data. It does prove the
measure-level consequences of an exact finite chain, including the complete
frequency half-line by using the already proved q11 tail floor.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Li2Lean.P0.Q11Data

noncomputable section

open Li2Lean.F_L8
open Li2Lean.P0.CA.Receipt

def q11EtaFloorQ : ℚ := etaFloor.num / etaFloor.den

def q11FrequencyFloorQ : ℚ := frequencyFloor.num / frequencyFloor.den

def q11PinnedPenaltyUpperQ : ℚ := pinnedPenaltyUpper.num / pinnedPenaltyUpper.den

def q11FrequencyPenaltyUpperQ : ℚ :=
  frequencyPenaltyUpper.num / frequencyPenaltyUpper.den

def q11QLogLower : Prop := ratioToReal qLogLower < q11ActualReference.qLog

/-! Soundness helper for a producer's integer numerator/denominator check. -/
theorem q11_ratioLeBool_sound {x y : IntRatio}
    (hx : 0 < x.den) (hy : 0 < y.den)
    (h : ratioLeBool x y = true) :
    (x.num : ℚ) / x.den ≤ (y.num : ℚ) / y.den := by
  have hcross : x.num * (y.den : ℤ) ≤ y.num * (x.den : ℤ) := by
    simpa [ratioLeBool] using (of_decide_eq_true h)
  have hxd : (x.den : ℚ) > 0 := by exact_mod_cast hx
  have hyd : (y.den : ℚ) > 0 := by exact_mod_cast hy
  apply (div_le_div_iff₀ hxd hyd).2
  exact_mod_cast hcross

theorem q11EtaFloorQ_eq : q11EtaFloorQ = -(3359 / 500 : ℚ) := by
  norm_num [q11EtaFloorQ, etaFloor]

theorem q11FrequencyFloorQ_eq : q11FrequencyFloorQ = 1217 / 200 := by
  norm_num [q11FrequencyFloorQ, frequencyFloor]

theorem q11PinnedPenaltyUpperQ_eq :
    q11PinnedPenaltyUpperQ = 1 / 1000000 := by
  norm_num [q11PinnedPenaltyUpperQ, pinnedPenaltyUpper]

theorem q11FrequencyPenaltyUpperQ_eq :
    q11FrequencyPenaltyUpperQ = 1069189 / 1000000 := by
  norm_num [q11FrequencyPenaltyUpperQ, frequencyPenaltyUpper]

theorem q11_frequency_floor_le_tail {t : ℝ} (ht : (81 / 10 : ℝ) ≤ t) :
    (q11FrequencyFloorQ : ℝ) ≤ q11Wmu t := by
  have htail := q11Wmu_tail_floor ht
  rw [q11FrequencyFloorQ_eq]
  norm_num at htail ⊢
  linarith

/-! The q11 finite-row obligations. `pinned_mass_le` and
`frequency_mass_le` are intentionally explicit rational inequalities. A
producer may discharge them from integer numerator/denominator Boolean
checks; downstream theorems never need to decide a Rat product. -/
structure Q11PenaltyRows where
  pinnedCells : List ReceiptCell
  pinnedAllowance : ℚ
  pinnedChain : ExactChain pinnedCells (1 / 4) (5 / 4)
  pinnedLower : ∀ c ∈ pinnedCells, ∀ x : ℝ,
    (c.lo : ℝ) ≤ x → x ≤ (c.hi : ℝ) →
      ((c.lower : ℝ) - (pinnedAllowance : ℝ)) ≤
        q11Weta (x : ℂ)
  pinned_mass_le :
    penaltyMass q11EtaFloorQ pinnedAllowance pinnedCells ≤ q11PinnedPenaltyUpperQ
  pinned_integrable :
    IntegrableOn
      (fun x : ℝ => max ((q11EtaFloorQ : ℝ) - q11Weta (x : ℂ)) 0)
      (Icc (1 / 4 : ℝ) (5 / 4 : ℝ))
  frequencyCells : List ReceiptCell
  frequencyAllowance : ℚ
  frequencyChain : ExactChain frequencyCells (1 / 2) (81 / 10)
  frequencyLower : ∀ c ∈ frequencyCells, ∀ t : ℝ,
    (c.lo : ℝ) ≤ t → t ≤ (c.hi : ℝ) →
      ((c.lower : ℝ) - (frequencyAllowance : ℝ)) ≤
        q11Wmu t
  frequency_mass_le :
    penaltyMass q11FrequencyFloorQ frequencyAllowance frequencyCells ≤
      q11FrequencyPenaltyUpperQ
  frequency_integrable :
    IntegrableOn
      (fun t : ℝ => max ((q11FrequencyFloorQ : ℝ) - q11Wmu t) 0)
      (Ici (1 / 2 : ℝ))
  contour_lower :
    ∀ z ∈ Gamma, (q11EtaFloorQ : ℝ) ≤ q11Weta z
  qLog_lower : q11QLogLower

theorem q11_pinned_sub_le_stepMajorant (R : Q11PenaltyRows)
    {x : ℝ} (hx : x ∈ Icc (1 / 4 : ℝ) (5 / 4 : ℝ)) :
    (q11EtaFloorQ : ℝ) - q11Weta (x : ℂ) ≤
      stepMajorant q11EtaFloorQ R.pinnedAllowance R.pinnedCells x := by
  exact sub_le_stepMajorant R.pinnedChain q11EtaFloorQ R.pinnedAllowance
    R.pinnedLower (by simpa using hx.1) (by simpa using hx.2)

theorem q11_pinned_max_le_stepMajorant (R : Q11PenaltyRows)
    {x : ℝ} (hx : x ∈ Icc (1 / 4 : ℝ) (5 / 4 : ℝ)) :
    max ((q11EtaFloorQ : ℝ) - q11Weta (x : ℂ)) 0 ≤
      stepMajorant q11EtaFloorQ R.pinnedAllowance R.pinnedCells x := by
  exact max_le (q11_pinned_sub_le_stepMajorant R hx)
    (stepMajorant_nonneg _ _ _ _)

theorem q11_pinned_penalty_le (R : Q11PenaltyRows) :
    (∫ x in Icc (1 / 4 : ℝ) (5 / 4 : ℝ),
      max ((q11EtaFloorQ : ℝ) - q11Weta (x : ℂ)) 0) ≤
      (q11PinnedPenaltyUpperQ : ℝ) := by
  have hmono := integral_mono_ae R.pinned_integrable
    (stepMajorant_integrableOn q11EtaFloorQ R.pinnedAllowance R.pinnedCells
      (Icc (1 / 4 : ℝ) (5 / 4 : ℝ)))
    (ae_restrict_mem measurableSet_Icc |>.mono (fun x hx =>
      q11_pinned_max_le_stepMajorant R hx))
  have hmass := integral_stepMajorant_le q11EtaFloorQ R.pinnedAllowance
    (Icc (1 / 4 : ℝ) (5 / 4 : ℝ)) R.pinnedCells
    (exactChain_widths R.pinnedChain)
  have hmass' : (penaltyMass q11EtaFloorQ R.pinnedAllowance R.pinnedCells : ℝ) ≤
      (q11PinnedPenaltyUpperQ : ℝ) := by
    exact_mod_cast R.pinned_mass_le
  exact hmono.trans (hmass.trans hmass')

theorem q11_frequency_sub_le_stepMajorant (R : Q11PenaltyRows)
    {t : ℝ} (ht : t ∈ Icc (1 / 2 : ℝ) (81 / 10 : ℝ)) :
    (q11FrequencyFloorQ : ℝ) - q11Wmu t ≤
      stepMajorant q11FrequencyFloorQ R.frequencyAllowance R.frequencyCells t := by
  exact sub_le_stepMajorant R.frequencyChain q11FrequencyFloorQ
    R.frequencyAllowance R.frequencyLower (by simpa using ht.1) (by simpa using ht.2)

theorem q11_frequency_max_le_stepMajorant (R : Q11PenaltyRows)
    {t : ℝ} (ht : t ∈ Ici (1 / 2 : ℝ)) :
    max ((q11FrequencyFloorQ : ℝ) - q11Wmu t) 0 ≤
      stepMajorant q11FrequencyFloorQ R.frequencyAllowance R.frequencyCells t := by
  by_cases hle : t ≤ (81 / 10 : ℝ)
  · exact max_le (q11_frequency_sub_le_stepMajorant R
      ⟨mem_Ici.mp ht, hle⟩) (stepMajorant_nonneg _ _ _ _)
  · have htail : (q11FrequencyFloorQ : ℝ) ≤ q11Wmu t :=
      q11_frequency_floor_le_tail (le_of_not_ge hle)
    rw [max_eq_right (sub_nonpos.mpr htail)]
    exact stepMajorant_nonneg _ _ _ _

theorem q11_frequency_penalty_le (R : Q11PenaltyRows) :
    (∫ t in Ici (1 / 2 : ℝ),
      max ((q11FrequencyFloorQ : ℝ) - q11Wmu t) 0) ≤
      (q11FrequencyPenaltyUpperQ : ℝ) := by
  have hmono := integral_mono_ae R.frequency_integrable
    (stepMajorant_integrableOn q11FrequencyFloorQ R.frequencyAllowance
      R.frequencyCells (Ici (1 / 2 : ℝ)))
    (ae_restrict_mem measurableSet_Ici |>.mono (fun t ht =>
      q11_frequency_max_le_stepMajorant R ht))
  have hmass := integral_stepMajorant_le q11FrequencyFloorQ R.frequencyAllowance
    (Ici (1 / 2 : ℝ)) R.frequencyCells
    (exactChain_widths R.frequencyChain)
  have hmass' :
      (penaltyMass q11FrequencyFloorQ R.frequencyAllowance R.frequencyCells : ℝ) ≤
        (q11FrequencyPenaltyUpperQ : ℝ) := by
    exact_mod_cast R.frequency_mass_le
  exact hmono.trans (hmass.trans hmass')

theorem q11_frequency_positivePart_zero_on_tail (_R : Q11PenaltyRows)
    {t : ℝ} (ht : (81 / 10 : ℝ) ≤ t) :
    max ((q11FrequencyFloorQ : ℝ) - q11Wmu t) 0 = 0 := by
  exact max_eq_right (sub_nonpos.mpr (q11_frequency_floor_le_tail ht))

end

end Li2Lean.P0.Q11Data
