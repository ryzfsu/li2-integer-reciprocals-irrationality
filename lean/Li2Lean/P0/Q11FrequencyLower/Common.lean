/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.Q11FrequencyRowCheck
import Li2Lean.P0.Q11FrequencyTable.Aggregator

namespace Li2Lean.P0.Q11Data

open Li2Lean.F_L8
open Li2Lean.P0.CA.Frequency
open Li2Lean.P0.CA.Receipt

def q11Split3Cell (c : ReceiptCell) : List ReceiptCell :=
  [⟨c.lo, c.lo + (c.hi - c.lo) / 3, c.lower⟩,
   ⟨c.lo + (c.hi - c.lo) / 3,
      c.lo + 2 * ((c.hi - c.lo) / 3), c.lower⟩,
   ⟨c.lo + 2 * ((c.hi - c.lo) / 3), c.hi, c.lower⟩]

def q11RowIOfCell (c : ReceiptCell) : RowI :=
  (c.lo.num, c.lo.den, c.hi.num, c.hi.den, c.lower)

def q11ChunkRows (cells : List ReceiptCell) : List RowI :=
  cells.flatMap q11Split3Cell |>.map q11RowIOfCell

def q11ChunkCells (cells : List ReceiptCell) : List ReceiptCell :=
  (q11ChunkRows cells).map RowI.toCell

theorem q11RowIOfCell_toCell (c : ReceiptCell) :
    (q11RowIOfCell c).toCell = c := by
  simp [q11RowIOfCell, RowI.toCell, Rat.num_div_den]

theorem q11ChunkRows_take_drop (cells : List ReceiptCell) (n : ℕ) :
    q11ChunkRows (cells.take n) ++ q11ChunkRows (cells.drop n) =
      q11ChunkRows cells := by
  unfold q11ChunkRows
  rw [← List.map_append, ← List.flatMap_append, List.take_append_drop]

theorem q11ChunkCells_take_drop (cells : List ReceiptCell) (n : ℕ) :
    q11ChunkCells (cells.take n) ++ q11ChunkCells (cells.drop n) =
      q11ChunkCells cells := by
  unfold q11ChunkCells
  rw [← List.map_append, q11ChunkRows_take_drop]

theorem q11ChunkCells_take_add (cells : List ReceiptCell) (n m : ℕ) :
    q11ChunkCells (cells.take (n + m)) =
      q11ChunkCells (cells.take n) ++
        q11ChunkCells ((cells.drop n).take m) := by
  unfold q11ChunkCells q11ChunkRows
  rw [List.take_add, List.flatMap_append, List.map_append]
  simp only [List.map_append]

theorem q11ChunkCells_lower_of_chunks
    {chunks : List (List ReceiptCell)}
    (hcheck : ∀ chunk ∈ chunks,
      Q11FrequencyCellsLower (q11ChunkCells chunk)) :
    Q11FrequencyCellsLower (chunks.flatMap q11ChunkCells) := by
  induction chunks with
  | nil =>
      intro c hc
      simp at hc
  | cons chunk rest ih =>
      rw [List.flatMap_cons]
      apply q11FrequencyCellsLower_append
      · exact hcheck chunk (by simp)
      · apply ih
        intro c hc
        exact hcheck c (by simp [hc])

theorem q11Split3Cell_chain {c : ReceiptCell} (hwidth : c.lo ≤ c.hi) :
    ExactChain (q11Split3Cell c) c.lo c.hi := by
  apply exactChain_iff_spec.mpr
  norm_num [q11Split3Cell, ExactChainSpec]
  constructor
  · linarith
  · constructor
    · linarith
    · linarith

theorem q11ChunkCells_eq_flatMap (cells : List ReceiptCell) :
    q11ChunkCells cells = cells.flatMap q11Split3Cell := by
  induction cells with
  | nil => rfl
  | cons c cs ih =>
      simp [q11ChunkCells, q11ChunkRows, List.map_map, Function.comp_def,
        List.flatMap_cons, ih, q11RowIOfCell_toCell]

theorem q11ChunkCells_flatMap (chunks : List (List ReceiptCell)) :
    q11ChunkCells (chunks.flatMap id) = chunks.flatMap q11ChunkCells := by
  induction chunks with
  | nil => rfl
  | cons chunk rest ih =>
      simp only [List.flatMap_cons, id_eq]
      calc
        q11ChunkCells (chunk ++ rest.flatMap id) =
            (chunk ++ rest.flatMap id).flatMap q11Split3Cell :=
          q11ChunkCells_eq_flatMap _
        _ = chunk.flatMap q11Split3Cell ++
            (rest.flatMap id).flatMap q11Split3Cell := by
          rw [List.flatMap_append]
        _ = q11ChunkCells chunk ++ q11ChunkCells (rest.flatMap id) := by
          rw [← q11ChunkCells_eq_flatMap chunk,
            ← q11ChunkCells_eq_flatMap (rest.flatMap id)]
        _ = q11ChunkCells chunk ++ rest.flatMap q11ChunkCells := by
          rw [ih]

theorem q11ExactChain_width_of_mem {cells : List ReceiptCell} {a b : ℚ}
    (hchain : ExactChain cells a b) :
    ∀ c ∈ cells, c.lo ≤ c.hi := by
  induction cells generalizing a b with
  | nil =>
      intro c hc
      simp at hc
  | cons c cs ih =>
      cases cs with
      | nil =>
          have hs := exactChain_iff_spec.mp hchain
          intro d hd
          simp only [List.mem_singleton] at hd
          subst d
          exact hs.2.2
      | cons d rest =>
          have hs := exactChain_iff_spec.mp hchain
          rcases hs with ⟨hleft, hadj, hwidth, htail⟩
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hwidth
          · exact ih (exactChain_iff_spec.mpr htail) x hx

theorem q11ChunkCells_chain_aux :
    ∀ (cells : List ReceiptCell) (a b : ℚ),
      ExactChain cells a b →
      (∀ c ∈ cells, c.lo ≤ c.hi) →
      ExactChain (q11ChunkCells cells) a b
  | [], _, _, h, _ => by cases h
  | c :: cs, a, b, hchain, hwidth => by
      cases cs with
      | nil =>
          have hspec := exactChain_iff_spec.mp hchain
          rcases hspec with ⟨hfirst, hlast, hcwidth⟩
          have hs := q11Split3Cell_chain (hwidth c (by simp))
          simpa [q11ChunkCells_eq_flatMap, hfirst, hlast] using hs
      | cons d rest =>
          have hspec := exactChain_iff_spec.mp hchain
          rcases hspec with ⟨hfirst, hadj, hcwidth, htail⟩
          have hs := q11Split3Cell_chain (hwidth c (by simp))
          have htail' := q11ChunkCells_chain_aux (d :: rest) d.lo b
            (exactChain_iff_spec.mpr htail) (by
              intro x hx
              exact hwidth x (by simp [hx]))
          have htail'' : ExactChain (q11ChunkCells (d :: rest)) c.hi b := by
            simpa [hadj] using htail'
          have hj := exactChain_join hs htail''
          simpa [q11ChunkCells_eq_flatMap, hfirst, hadj] using hj

theorem q11ChunkCells_chain {cells : List ReceiptCell} {a b : ℚ}
    (hchain : ExactChain cells a b)
    (hwidth : ∀ c ∈ cells, c.lo ≤ c.hi) :
    ExactChain (q11ChunkCells cells) a b :=
  q11ChunkCells_chain_aux cells a b hchain hwidth

theorem q11ChunkCells_lower_of_check {cells : List ReceiptCell}
    (h : q11ShardCheckWeightedTight (q11ChunkRows cells) = true) :
    Q11FrequencyCellsLower (q11ChunkCells cells) := by
  intro c hc t hlo hhi
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hc
  have hrc : r.toCell ∈ (q11ChunkRows cells).map RowI.toCell :=
    List.mem_map.mpr ⟨r, hr, rfl⟩
  exact q11ShardCheckWeightedTight_sound h (r.toCell) hrc t hlo hhi

end Li2Lean.P0.Q11Data
