/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.Q11CA.Contour.Q11Shard000
import Li2Lean.P0.Q11CA.Contour.Q11Shard001
import Li2Lean.P0.Q11CA.Contour.Q11Shard002
import Li2Lean.P0.Q11CA.Contour.Q11Shard003
import Li2Lean.P0.Q11CA.Contour.Q11Shard004
import Li2Lean.P0.Q11CA.Contour.Q11Shard005
import Li2Lean.P0.Q11CA.Contour.Q11BTab

open MeasureTheory Set
open scoped BigOperators

namespace Li2Lean.P0.Q11Data

noncomputable section

open Li2Lean.P0.CA.Contour
open Li2Lean.P0.CA.Contour.QI
open Li2Lean.P0.CA.Receipt

def q11AllGroups : List Grp :=
  q11Shard000 ++ q11Shard001 ++ q11Shard002 ++
    q11Shard003 ++ q11Shard004 ++ q11Shard005

theorem q11AllGroups_length : q11AllGroups.length = 240 := by
  set_option maxRecDepth 100000 in
    decide

theorem q11AllCells_length : (q11AllGroups.flatMap Grp.cells).length = 320 := by
  set_option maxRecDepth 100000 in
    decide

theorem q11AllGroups_ok :
    q11AllGrpFrom (fun k => q11BTab.getD k (pt 0)) q11AllGroups = true := by
  simp only [q11AllGroups, q11AllGrpFrom_append,
    q11Shard000_ok, q11Shard001_ok, q11Shard002_ok,
    q11Shard003_ok, q11Shard004_ok, q11Shard005_ok,
    Bool.true_and]

theorem q11AllGroups_floor :
    floorCheck (-(3359 / 500 : ℚ))
      ((q11AllGroups.flatMap Grp.cells).map Cell.cell) = true := by
  set_option maxRecDepth 100000 in
  set_option maxHeartbeats 16000000 in
    decide +kernel

theorem q11AllGroups_chain :
    chainCheck ((q11AllGroups.flatMap Grp.cells).map Cell.cell) 0 1 = true := by
  set_option maxRecDepth 100000 in
  set_option maxHeartbeats 16000000 in
    decide +kernel

theorem q11AllRows_numeric :
    q11GammaRowsCheck (q11FullGammaRows q11AllGroups) = true :=
  q11FullGammaRows_numeric q11AllGroups_ok

theorem q11AllRows_cover :
    ∀ u : ℝ, 0 ≤ u → u ≤ 1 →
      ∃ r ∈ q11FullGammaRows q11AllGroups,
        (r.lo : ℝ) ≤ u ∧ u ≤ (r.hi : ℝ) :=
  q11FullGammaRows_cover q11AllGroups_chain

def q11AllCertificate : Q11GammaContourCertificate :=
  q11GammaContourCertificate_of_groupsFrom
    (q11BTabOk_sound q11BTab_ok) q11AllGroups q11AllGroups_ok
      q11AllGroups_floor q11AllGroups_chain

theorem q11AllContourFloor :
    ∀ z ∈ Gamma, ratioToReal etaFloor ≤ q11Weta z :=
  q11GammaContourFloor_of_bTab_and_groups
    (bTab := q11BTab) q11BTab_ok q11AllGroups_ok q11AllGroups_floor q11AllGroups_chain

#print axioms q11AllGroups_length
#print axioms q11AllCells_length
#print axioms q11AllGroups_ok
#print axioms q11AllGroups_floor
#print axioms q11AllGroups_chain
#print axioms q11AllRows_numeric
#print axioms q11AllRows_cover
#print axioms q11AllContourFloor

end
end Li2Lean.P0.Q11Data
