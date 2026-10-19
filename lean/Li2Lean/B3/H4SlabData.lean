/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B3.H4SlabData00
import Li2Lean.B3.H4SlabData01
import Li2Lean.B3.H4SlabData02
import Li2Lean.B3.H4SlabData03
import Li2Lean.B3.H4SlabData04
import Li2Lean.B3.H4SlabData05
import Li2Lean.B3.H4SlabData06
import Li2Lean.B3.H4SlabData07
import Li2Lean.B3.H4SlabData08

/-! The full v13 H4 slab table: 9 kernel-checked shards.
Shard bounds: [1/40, 2/71], [2/71, 5/156], [5/156, 7/188], [7/188, 2/45], [2/45, 11/200], [11/200, 7/96], [7/96, 3/28], [3/28, 1/5], [1/5, 5/4]. -/

namespace Li2Lean.B3

def v13SlabData : List VSlab :=
    v13SlabData00 ++
    v13SlabData01 ++
    v13SlabData02 ++
    v13SlabData03 ++
    v13SlabData04 ++
    v13SlabData05 ++
    v13SlabData06 ++
    v13SlabData07 ++
    v13SlabData08

theorem v13SlabData_all_ok : v13SlabData.all VSlab.ok = true := by
  have h00 := (Bool.and_eq_true _ _).mp v13SlabData00_ok
  have h01 := (Bool.and_eq_true _ _).mp v13SlabData01_ok
  have h02 := (Bool.and_eq_true _ _).mp v13SlabData02_ok
  have h03 := (Bool.and_eq_true _ _).mp v13SlabData03_ok
  have h04 := (Bool.and_eq_true _ _).mp v13SlabData04_ok
  have h05 := (Bool.and_eq_true _ _).mp v13SlabData05_ok
  have h06 := (Bool.and_eq_true _ _).mp v13SlabData06_ok
  have h07 := (Bool.and_eq_true _ _).mp v13SlabData07_ok
  have h08 := (Bool.and_eq_true _ _).mp v13SlabData08_ok
  simp only [v13SlabData, List.all_append, h00.1, h01.1, h02.1, h03.1, h04.1, h05.1, h06.1, h07.1, h08.1, Bool.and_self]

theorem v13SlabData_ok : ∀ s ∈ v13SlabData, s.ok = true :=
  fun s hs => List.all_eq_true.mp v13SlabData_all_ok s hs

theorem v13SlabData_chain :
    vSlabChain ((1 : ℚ) / 40) ((5 : ℚ) / 4) v13SlabData = true := by
  have h00 := (Bool.and_eq_true _ _).mp v13SlabData00_ok
  have h01 := (Bool.and_eq_true _ _).mp v13SlabData01_ok
  have h02 := (Bool.and_eq_true _ _).mp v13SlabData02_ok
  have h03 := (Bool.and_eq_true _ _).mp v13SlabData03_ok
  have h04 := (Bool.and_eq_true _ _).mp v13SlabData04_ok
  have h05 := (Bool.and_eq_true _ _).mp v13SlabData05_ok
  have h06 := (Bool.and_eq_true _ _).mp v13SlabData06_ok
  have h07 := (Bool.and_eq_true _ _).mp v13SlabData07_ok
  have h08 := (Bool.and_eq_true _ _).mp v13SlabData08_ok
  exact vSlabChain_append (vSlabChain_append (vSlabChain_append (vSlabChain_append (vSlabChain_append (vSlabChain_append (vSlabChain_append (vSlabChain_append (h00.2) h01.2) h02.2) h03.2) h04.2) h05.2) h06.2) h07.2) h08.2

end Li2Lean.B3

#print axioms Li2Lean.B3.v13SlabData_ok
#print axioms Li2Lean.B3.v13SlabData_chain
