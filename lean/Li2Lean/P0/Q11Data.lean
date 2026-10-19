/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Mathlib

namespace Li2Lean.P0.Q11Data

/-!
The q = 11 endpoint data from paper v13, `chapters/p0-reference-data.tex`,
Table `tab:q11data`.  The decimal table is stored only as natural-number
units; no `Rat` multiplication is used in the certificate checks.
-/

def denominator : ℕ := 3000000000000

def pinnedEdge32Units : List ℕ := [8, 12, 16, 20, 24, 28, 32, 36, 40]

def pinnedMassUnits : List ℕ :=
  [28, 0, 107702656325, 206939134529, 260854191850,
   321658806124, 374999999996, 374999999996]

def frequencyEdge2Units : List ℕ := [1, 3, 5, 7, 9]

def frequencyMassUnits : List ℕ :=
  [2334546252656, 652078675810, 13375071534, 0]

def contourPairMassUnits : List ℕ :=
  [105521636098, 103136532801, 98660112985, 92490547592,
   84344850292, 75717735060, 60802883424, 55748307324]

def contourNodeCount : ℕ := 64
def contourFejerDegree : ℕ := 48

/-! Scalar floors and outward penalties from `p0-analytic.tex`, Table
`tab:p0-q-bounds`.  Each pair denotes an integer numerator over a positive
integer denominator, so downstream checks can use cross multiplication. -/
structure IntRatio where
  num : ℤ
  den : ℕ
deriving DecidableEq, Repr

def etaFloor : IntRatio := ⟨-3359, 500⟩
def frequencyFloor : IntRatio := ⟨1217, 200⟩
def alphaLower : IntRatio := ⟨77597, 100000⟩
def qLogLower : IntRatio := ⟨-635537, 1000000⟩
def pinnedPenaltyUpper : IntRatio := ⟨1, 1000000⟩
def frequencyPenaltyUpper : IntRatio := ⟨1069189, 1000000⟩
def arithmeticConstantUpper : IntRatio := ⟨1271001, 500000⟩
def endpointTangentUpper : IntRatio := ⟨772577360778, 1000000000000⟩

def contourPairMassUnit (j : ℕ) : ℕ := contourPairMassUnits.getD j 0

/-! The table lists the first eight contour nodes.  The first half is
zero-filled afterwards, and the second half is obtained by reflection. -/
def contourMassUnit (j : ℕ) : ℕ :=
  if j < 8 then contourPairMassUnit j
  else if j < 56 then 0
  else contourPairMassUnit (63 - j)

theorem denominator_pos : 0 < denominator := by decide +kernel
theorem pinned_edges_length : pinnedEdge32Units.length = 9 := by decide +kernel
theorem pinned_masses_length : pinnedMassUnits.length = 8 := by decide +kernel
theorem frequency_edges_length : frequencyEdge2Units.length = 5 := by decide +kernel
theorem frequency_masses_length : frequencyMassUnits.length = 4 := by decide +kernel
theorem contour_pair_masses_length : contourPairMassUnits.length = 8 := by decide +kernel
theorem contour_node_count_eq : contourNodeCount = 64 := by decide +kernel
theorem contour_fejer_degree_eq : contourFejerDegree = 48 := by decide +kernel

theorem pinned_mass_sum : pinnedMassUnits.sum = 1647154788848 := by decide +kernel
theorem frequency_mass_sum : frequencyMassUnits.sum = denominator := by decide +kernel
theorem contour_pair_mass_sum : contourPairMassUnits.sum = 676422605576 := by decide +kernel

/-! This is the mass-one condition for the paper's contour-plus-pinned
measure `eta_0`: every printed contour pair contributes twice. -/
theorem eta_mass_sum : pinnedMassUnits.sum + 2 * contourPairMassUnits.sum = denominator := by
  decide +kernel

/-! Real-valued form of the mass-one certificate used by the endpoint
measure.  Keeping this as an explicit cast avoids redoing the table
arithmetic in downstream measure normalizations. -/
theorem eta_mass_partition_real :
    ((pinnedMassUnits.sum : ℝ) +
      2 * (contourPairMassUnits.sum : ℝ)) /
      (denominator : ℝ) = 1 := by
  norm_num [pinned_mass_sum, contour_pair_mass_sum, denominator]

theorem eta_floor_den_pos : 0 < etaFloor.den := by decide +kernel
theorem frequency_floor_den_pos : 0 < frequencyFloor.den := by decide +kernel
theorem alpha_lower_den_pos : 0 < alphaLower.den := by decide +kernel
theorem qLog_lower_den_pos : 0 < qLogLower.den := by decide +kernel
theorem pinned_penalty_den_pos : 0 < pinnedPenaltyUpper.den := by decide +kernel
theorem frequency_penalty_den_pos : 0 < frequencyPenaltyUpper.den := by decide +kernel
theorem arithmetic_constant_den_pos : 0 < arithmeticConstantUpper.den := by decide +kernel
theorem endpoint_tangent_den_pos : 0 < endpointTangentUpper.den := by decide +kernel

/-! Integer cross-multiplication check of the q=11 endpoint margin printed in
`p0-analytic.tex`: alpha's lower bound minus the tangent upper bound is
strictly greater than 3/1000. -/
theorem endpoint_margin_gt_three_per_thousand :
    (77597 : ℤ) * 1000000000000 - 772577360778 * 100000 >
      3 * 100 * 1000000000000 := by
  norm_num

theorem contour_massUnit_reflection (j : ℕ) (hj : j < contourNodeCount) :
    contourMassUnit j = contourMassUnit (contourNodeCount - 1 - j) := by
  rw [contour_node_count_eq] at hj ⊢
  interval_cases j <;> decide +kernel

end Li2Lean.P0.Q11Data
