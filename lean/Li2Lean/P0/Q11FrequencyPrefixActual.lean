/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.Q11FrequencyLower.Prefix000
import Li2Lean.P0.Q11FrequencyLower.Prefix000B
import Li2Lean.P0.Q11FrequencyLower.Prefix000C
import Li2Lean.P0.Q11FrequencyLower.Prefix000D
import Li2Lean.P0.Q11FrequencyLower.Prefix001
import Li2Lean.P0.Q11FrequencyLower.Prefix001B
import Li2Lean.P0.Q11FrequencyLower.Prefix001C
import Li2Lean.P0.Q11FrequencyLower.Prefix001D
import Li2Lean.P0.Q11FrequencyLower.Prefix002
import Li2Lean.P0.Q11FrequencyLower.Prefix002B
import Li2Lean.P0.Q11FrequencyLower.Prefix002C
import Li2Lean.P0.Q11FrequencyLower.Prefix002D
import Li2Lean.P0.Q11FrequencyLower.Prefix003
import Li2Lean.P0.Q11FrequencyLower.Prefix003B
import Li2Lean.P0.Q11FrequencyLower.Prefix003C
import Li2Lean.P0.Q11FrequencyLower.Prefix003D
import Li2Lean.P0.Q11FrequencyLower.Prefix004
import Li2Lean.P0.Q11FrequencyLower.Prefix004B
import Li2Lean.P0.Q11FrequencyLower.Prefix004C
import Li2Lean.P0.Q11FrequencyLower.Prefix004D
import Li2Lean.P0.Q11FrequencyLower.Prefix005
import Li2Lean.P0.Q11FrequencyLower.Prefix005B
import Li2Lean.P0.Q11FrequencyLower.Prefix005C
import Li2Lean.P0.Q11FrequencyLower.Prefix005D
import Li2Lean.P0.Q11FrequencyLower.Prefix006
import Li2Lean.P0.Q11FrequencyLower.Prefix006B
import Li2Lean.P0.Q11FrequencyLower.Prefix006C
import Li2Lean.P0.Q11FrequencyLower.Prefix006D
import Li2Lean.P0.Q11FrequencyLower.Prefix007
import Li2Lean.P0.Q11FrequencyLower.Prefix007B
import Li2Lean.P0.Q11FrequencyLower.Prefix007C
import Li2Lean.P0.Q11FrequencyLower.Prefix007D
import Li2Lean.P0.Q11FrequencyLower.Prefix008
import Li2Lean.P0.Q11FrequencyLower.Prefix008B
import Li2Lean.P0.Q11FrequencyLower.Prefix008C
import Li2Lean.P0.Q11FrequencyLower.Prefix008D
import Li2Lean.P0.Q11FrequencyLower.Prefix009
import Li2Lean.P0.Q11FrequencyLower.Prefix009B
import Li2Lean.P0.Q11FrequencyLower.Prefix009C
import Li2Lean.P0.Q11FrequencyLower.Prefix009D
import Li2Lean.P0.Q11FrequencyLower.Prefix010
import Li2Lean.P0.Q11FrequencyLower.Prefix010B
import Li2Lean.P0.Q11FrequencyLower.Prefix010C
import Li2Lean.P0.Q11FrequencyLower.Prefix010D
import Li2Lean.P0.Q11FrequencyPenaltyRowsAgy

namespace Li2Lean.P0.Q11Data

open Li2Lean.F_L8
open Li2Lean.P0.CA.Frequency
open Li2Lean.P0.CA.Receipt

theorem q11ChunkCells_lower_of_take_add
    (cells : List ReceiptCell) (n m : ℕ)
    (h1 : Q11FrequencyCellsLower (q11ChunkCells (cells.take n)))
    (h2 : Q11FrequencyCellsLower
      (q11ChunkCells ((cells.drop n).take m))) :
    Q11FrequencyCellsLower (q11ChunkCells (cells.take (n + m))) := by
  rw [q11ChunkCells_take_add]
  exact q11FrequencyCellsLower_append h1 h2

theorem q11FrequencyCellsLower_of_chunked
    {cells : List ReceiptCell}
    (hwidth : ∀ c ∈ cells, c.lo ≤ c.hi)
    (hchunk : Q11FrequencyCellsLower (q11ChunkCells cells)) :
    Q11FrequencyCellsLower cells := by
  intro c hc t hlo hhi
  have hsplit := q11Split3Cell_chain (c := c) (hwidth c hc)
  obtain ⟨d, hd, _, hdl, hdh⟩ := exactChain_covers hsplit t hlo hhi
  have hmem : d ∈ q11ChunkCells cells := by
    rw [q11ChunkCells_eq_flatMap]
    exact List.mem_flatMap.mpr ⟨c, hc, hd⟩
  have hlow := hchunk d hmem t hdl hdh
  have hEq : d.lower = c.lower := by
    simp only [q11Split3Cell, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl <;> rfl
  simpa [hEq] using hlow

theorem q11FrequencyRowsRows000_chunked_lower :
    Q11FrequencyCellsLower (q11ChunkCells q11FrequencyRowsRows000) := by
  have h0 : Q11FrequencyCellsLower
      (q11ChunkCells (q11FrequencyRowsRows000.take 8)) := by
    simpa [q11FrequencyRowsRows000Chunk00] using q11FrequencyRowsRows000Chunk00_lower
  have h1 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows000 8 8 h0
    (by simpa [q11FrequencyRowsRows000Chunk01] using q11FrequencyRowsRows000Chunk01_lower)
  have h2 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows000 16 8 h1
    (by simpa [q11FrequencyRowsRows000Chunk02] using q11FrequencyRowsRows000Chunk02_lower)
  have h3 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows000 24 8 h2
    (by simpa [q11FrequencyRowsRows000Chunk03] using q11FrequencyRowsRows000Chunk03_lower)
  have h4 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows000 32 8 h3
    (by simpa [q11FrequencyRowsRows000Chunk04] using q11FrequencyRowsRows000Chunk04_lower)
  have h5 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows000 40 8 h4
    (by simpa [q11FrequencyRowsRows000Chunk05] using q11FrequencyRowsRows000Chunk05_lower)
  have h6 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows000 48 8 h5
    (by simpa [q11FrequencyRowsRows000Chunk06] using q11FrequencyRowsRows000Chunk06_lower)
  have h7 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows000 56 8 h6
    (by simpa [q11FrequencyRowsRows000Chunk07] using q11FrequencyRowsRows000Chunk07_lower)
  have h8 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows000 64 8 h7
    (by simpa [q11FrequencyRowsRows000ChunkB00] using q11FrequencyRowsRows000ChunkB00_lower)
  have h9 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows000 72 8 h8
    (by simpa [q11FrequencyRowsRows000ChunkB01] using q11FrequencyRowsRows000ChunkB01_lower)
  have h10 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows000 80 8 h9
    (by simpa [q11FrequencyRowsRows000ChunkB02] using q11FrequencyRowsRows000ChunkB02_lower)
  have h11 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows000 88 8 h10
    (by simpa [q11FrequencyRowsRows000ChunkB03] using q11FrequencyRowsRows000ChunkB03_lower)
  have h12 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows000 96 8 h11
    (by simpa [q11FrequencyRowsRows000ChunkB04] using q11FrequencyRowsRows000ChunkB04_lower)
  have h13 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows000 104 8 h12
    (by simpa [q11FrequencyRowsRows000ChunkB05] using q11FrequencyRowsRows000ChunkB05_lower)
  have h14 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows000 112 8 h13
    (by simpa [q11FrequencyRowsRows000ChunkB06] using q11FrequencyRowsRows000ChunkB06_lower)
  have h15 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows000 120 8 h14
    (by simpa [q11FrequencyRowsRows000ChunkB07] using q11FrequencyRowsRows000ChunkB07_lower)
  have h16 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows000 128 8 h15
    (by simpa [q11FrequencyRowsRows000ChunkC00] using q11FrequencyRowsRows000ChunkC00_lower)
  have h17 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows000 136 8 h16
    (by simpa [q11FrequencyRowsRows000ChunkC01] using q11FrequencyRowsRows000ChunkC01_lower)
  have h18 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows000 144 8 h17
    (by simpa [q11FrequencyRowsRows000ChunkC02] using q11FrequencyRowsRows000ChunkC02_lower)
  have h19 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows000 152 8 h18
    (by simpa [q11FrequencyRowsRows000ChunkC03] using q11FrequencyRowsRows000ChunkC03_lower)
  have h20 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows000 160 8 h19
    (by simpa [q11FrequencyRowsRows000ChunkC04] using q11FrequencyRowsRows000ChunkC04_lower)
  have h21 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows000 168 8 h20
    (by simpa [q11FrequencyRowsRows000ChunkC05] using q11FrequencyRowsRows000ChunkC05_lower)
  have h22 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows000 176 8 h21
    (by simpa [q11FrequencyRowsRows000ChunkC06] using q11FrequencyRowsRows000ChunkC06_lower)
  have h23 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows000 184 8 h22
    (by simpa [q11FrequencyRowsRows000ChunkC07] using q11FrequencyRowsRows000ChunkC07_lower)
  have h24 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows000 192 8 h23
    (by simpa [q11FrequencyRowsRows000ChunkD00] using q11FrequencyRowsRows000ChunkD00_lower)
  have h25 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows000 200 8 h24
    (by simpa [q11FrequencyRowsRows000ChunkD01] using q11FrequencyRowsRows000ChunkD01_lower)
  have h26 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows000 208 8 h25
    (by simpa [q11FrequencyRowsRows000ChunkD02] using q11FrequencyRowsRows000ChunkD02_lower)
  have h27 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows000 216 8 h26
    (by simpa [q11FrequencyRowsRows000ChunkD03] using q11FrequencyRowsRows000ChunkD03_lower)
  have h28 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows000 224 8 h27
    (by simpa [q11FrequencyRowsRows000ChunkD04] using q11FrequencyRowsRows000ChunkD04_lower)
  have h29 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows000 232 8 h28
    (by simpa [q11FrequencyRowsRows000ChunkD05] using q11FrequencyRowsRows000ChunkD05_lower)
  have h30 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows000 240 8 h29
    (by simpa [q11FrequencyRowsRows000ChunkD06] using q11FrequencyRowsRows000ChunkD06_lower)
  have h31 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows000 248 8 h30
    (by simpa [q11FrequencyRowsRows000ChunkD07] using q11FrequencyRowsRows000ChunkD07_lower)
  have hrows : q11FrequencyRowsRows000.take 256 = q11FrequencyRowsRows000 := by
    apply List.take_of_length_le
    simp [q11FrequencyRowsRows000_length]
  simpa only [hrows] using h31

theorem q11FrequencyRowsRows000_lower :
    Q11FrequencyCellsLower q11FrequencyRowsRows000 := by
  exact q11FrequencyCellsLower_of_chunked
    (cells := q11FrequencyRowsRows000)
    (q11ExactChain_width_of_mem (chainCheck_sound q11FrequencyRowsRows000_chain))
    q11FrequencyRowsRows000_chunked_lower

theorem q11FrequencyRowsRows001_chunked_lower :
    Q11FrequencyCellsLower (q11ChunkCells q11FrequencyRowsRows001) := by
  have h0 : Q11FrequencyCellsLower
      (q11ChunkCells (q11FrequencyRowsRows001.take 8)) := by
    simpa [q11FrequencyRowsRows001Chunk00] using q11FrequencyRowsRows001Chunk00_lower
  have h1 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows001 8 8 h0
    (by simpa [q11FrequencyRowsRows001Chunk01] using q11FrequencyRowsRows001Chunk01_lower)
  have h2 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows001 16 8 h1
    (by simpa [q11FrequencyRowsRows001Chunk02] using q11FrequencyRowsRows001Chunk02_lower)
  have h3 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows001 24 8 h2
    (by simpa [q11FrequencyRowsRows001Chunk03] using q11FrequencyRowsRows001Chunk03_lower)
  have h4 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows001 32 8 h3
    (by simpa [q11FrequencyRowsRows001Chunk04] using q11FrequencyRowsRows001Chunk04_lower)
  have h5 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows001 40 8 h4
    (by simpa [q11FrequencyRowsRows001Chunk05] using q11FrequencyRowsRows001Chunk05_lower)
  have h6 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows001 48 8 h5
    (by simpa [q11FrequencyRowsRows001Chunk06] using q11FrequencyRowsRows001Chunk06_lower)
  have h7 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows001 56 8 h6
    (by simpa [q11FrequencyRowsRows001Chunk07] using q11FrequencyRowsRows001Chunk07_lower)
  have h8 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows001 64 8 h7
    (by simpa [q11FrequencyRowsRows001ChunkB00] using q11FrequencyRowsRows001ChunkB00_lower)
  have h9 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows001 72 8 h8
    (by simpa [q11FrequencyRowsRows001ChunkB01] using q11FrequencyRowsRows001ChunkB01_lower)
  have h10 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows001 80 8 h9
    (by simpa [q11FrequencyRowsRows001ChunkB02] using q11FrequencyRowsRows001ChunkB02_lower)
  have h11 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows001 88 8 h10
    (by simpa [q11FrequencyRowsRows001ChunkB03] using q11FrequencyRowsRows001ChunkB03_lower)
  have h12 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows001 96 8 h11
    (by simpa [q11FrequencyRowsRows001ChunkB04] using q11FrequencyRowsRows001ChunkB04_lower)
  have h13 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows001 104 8 h12
    (by simpa [q11FrequencyRowsRows001ChunkB05] using q11FrequencyRowsRows001ChunkB05_lower)
  have h14 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows001 112 8 h13
    (by simpa [q11FrequencyRowsRows001ChunkB06] using q11FrequencyRowsRows001ChunkB06_lower)
  have h15 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows001 120 8 h14
    (by simpa [q11FrequencyRowsRows001ChunkB07] using q11FrequencyRowsRows001ChunkB07_lower)
  have h16 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows001 128 8 h15
    (by simpa [q11FrequencyRowsRows001ChunkC00] using q11FrequencyRowsRows001ChunkC00_lower)
  have h17 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows001 136 8 h16
    (by simpa [q11FrequencyRowsRows001ChunkC01] using q11FrequencyRowsRows001ChunkC01_lower)
  have h18 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows001 144 8 h17
    (by simpa [q11FrequencyRowsRows001ChunkC02] using q11FrequencyRowsRows001ChunkC02_lower)
  have h19 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows001 152 8 h18
    (by simpa [q11FrequencyRowsRows001ChunkC03] using q11FrequencyRowsRows001ChunkC03_lower)
  have h20 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows001 160 8 h19
    (by simpa [q11FrequencyRowsRows001ChunkC04] using q11FrequencyRowsRows001ChunkC04_lower)
  have h21 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows001 168 8 h20
    (by simpa [q11FrequencyRowsRows001ChunkC05] using q11FrequencyRowsRows001ChunkC05_lower)
  have h22 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows001 176 8 h21
    (by simpa [q11FrequencyRowsRows001ChunkC06] using q11FrequencyRowsRows001ChunkC06_lower)
  have h23 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows001 184 8 h22
    (by simpa [q11FrequencyRowsRows001ChunkC07] using q11FrequencyRowsRows001ChunkC07_lower)
  have h24 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows001 192 8 h23
    (by simpa [q11FrequencyRowsRows001ChunkD00] using q11FrequencyRowsRows001ChunkD00_lower)
  have h25 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows001 200 8 h24
    (by simpa [q11FrequencyRowsRows001ChunkD01] using q11FrequencyRowsRows001ChunkD01_lower)
  have h26 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows001 208 8 h25
    (by simpa [q11FrequencyRowsRows001ChunkD02] using q11FrequencyRowsRows001ChunkD02_lower)
  have h27 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows001 216 8 h26
    (by simpa [q11FrequencyRowsRows001ChunkD03] using q11FrequencyRowsRows001ChunkD03_lower)
  have h28 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows001 224 8 h27
    (by simpa [q11FrequencyRowsRows001ChunkD04] using q11FrequencyRowsRows001ChunkD04_lower)
  have h29 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows001 232 8 h28
    (by simpa [q11FrequencyRowsRows001ChunkD05] using q11FrequencyRowsRows001ChunkD05_lower)
  have h30 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows001 240 8 h29
    (by simpa [q11FrequencyRowsRows001ChunkD06] using q11FrequencyRowsRows001ChunkD06_lower)
  have h31 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows001 248 8 h30
    (by simpa [q11FrequencyRowsRows001ChunkD07] using q11FrequencyRowsRows001ChunkD07_lower)
  have hrows : q11FrequencyRowsRows001.take 256 = q11FrequencyRowsRows001 := by
    apply List.take_of_length_le
    simp [q11FrequencyRowsRows001_length]
  simpa only [hrows] using h31

theorem q11FrequencyRowsRows001_lower :
    Q11FrequencyCellsLower q11FrequencyRowsRows001 := by
  exact q11FrequencyCellsLower_of_chunked
    (cells := q11FrequencyRowsRows001)
    (q11ExactChain_width_of_mem (chainCheck_sound q11FrequencyRowsRows001_chain))
    q11FrequencyRowsRows001_chunked_lower

theorem q11FrequencyRowsRows002_chunked_lower :
    Q11FrequencyCellsLower (q11ChunkCells q11FrequencyRowsRows002) := by
  have h0 : Q11FrequencyCellsLower
      (q11ChunkCells (q11FrequencyRowsRows002.take 8)) := by
    simpa [q11FrequencyRowsRows002Chunk00] using q11FrequencyRowsRows002Chunk00_lower
  have h1 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows002 8 8 h0
    (by simpa [q11FrequencyRowsRows002Chunk01] using q11FrequencyRowsRows002Chunk01_lower)
  have h2 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows002 16 8 h1
    (by simpa [q11FrequencyRowsRows002Chunk02] using q11FrequencyRowsRows002Chunk02_lower)
  have h3 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows002 24 8 h2
    (by simpa [q11FrequencyRowsRows002Chunk03] using q11FrequencyRowsRows002Chunk03_lower)
  have h4 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows002 32 8 h3
    (by simpa [q11FrequencyRowsRows002Chunk04] using q11FrequencyRowsRows002Chunk04_lower)
  have h5 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows002 40 8 h4
    (by simpa [q11FrequencyRowsRows002Chunk05] using q11FrequencyRowsRows002Chunk05_lower)
  have h6 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows002 48 8 h5
    (by simpa [q11FrequencyRowsRows002Chunk06] using q11FrequencyRowsRows002Chunk06_lower)
  have h7 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows002 56 8 h6
    (by simpa [q11FrequencyRowsRows002Chunk07] using q11FrequencyRowsRows002Chunk07_lower)
  have h8 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows002 64 8 h7
    (by simpa [q11FrequencyRowsRows002ChunkB00] using q11FrequencyRowsRows002ChunkB00_lower)
  have h9 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows002 72 8 h8
    (by simpa [q11FrequencyRowsRows002ChunkB01] using q11FrequencyRowsRows002ChunkB01_lower)
  have h10 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows002 80 8 h9
    (by simpa [q11FrequencyRowsRows002ChunkB02] using q11FrequencyRowsRows002ChunkB02_lower)
  have h11 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows002 88 8 h10
    (by simpa [q11FrequencyRowsRows002ChunkB03] using q11FrequencyRowsRows002ChunkB03_lower)
  have h12 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows002 96 8 h11
    (by simpa [q11FrequencyRowsRows002ChunkB04] using q11FrequencyRowsRows002ChunkB04_lower)
  have h13 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows002 104 8 h12
    (by simpa [q11FrequencyRowsRows002ChunkB05] using q11FrequencyRowsRows002ChunkB05_lower)
  have h14 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows002 112 8 h13
    (by simpa [q11FrequencyRowsRows002ChunkB06] using q11FrequencyRowsRows002ChunkB06_lower)
  have h15 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows002 120 8 h14
    (by simpa [q11FrequencyRowsRows002ChunkB07] using q11FrequencyRowsRows002ChunkB07_lower)
  have h16 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows002 128 8 h15
    (by simpa [q11FrequencyRowsRows002ChunkC00] using q11FrequencyRowsRows002ChunkC00_lower)
  have h17 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows002 136 8 h16
    (by simpa [q11FrequencyRowsRows002ChunkC01] using q11FrequencyRowsRows002ChunkC01_lower)
  have h18 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows002 144 8 h17
    (by simpa [q11FrequencyRowsRows002ChunkC02] using q11FrequencyRowsRows002ChunkC02_lower)
  have h19 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows002 152 8 h18
    (by simpa [q11FrequencyRowsRows002ChunkC03] using q11FrequencyRowsRows002ChunkC03_lower)
  have h20 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows002 160 8 h19
    (by simpa [q11FrequencyRowsRows002ChunkC04] using q11FrequencyRowsRows002ChunkC04_lower)
  have h21 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows002 168 8 h20
    (by simpa [q11FrequencyRowsRows002ChunkC05] using q11FrequencyRowsRows002ChunkC05_lower)
  have h22 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows002 176 8 h21
    (by simpa [q11FrequencyRowsRows002ChunkC06] using q11FrequencyRowsRows002ChunkC06_lower)
  have h23 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows002 184 8 h22
    (by simpa [q11FrequencyRowsRows002ChunkC07] using q11FrequencyRowsRows002ChunkC07_lower)
  have h24 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows002 192 8 h23
    (by simpa [q11FrequencyRowsRows002ChunkD00] using q11FrequencyRowsRows002ChunkD00_lower)
  have h25 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows002 200 8 h24
    (by simpa [q11FrequencyRowsRows002ChunkD01] using q11FrequencyRowsRows002ChunkD01_lower)
  have h26 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows002 208 8 h25
    (by simpa [q11FrequencyRowsRows002ChunkD02] using q11FrequencyRowsRows002ChunkD02_lower)
  have h27 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows002 216 8 h26
    (by simpa [q11FrequencyRowsRows002ChunkD03] using q11FrequencyRowsRows002ChunkD03_lower)
  have h28 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows002 224 8 h27
    (by simpa [q11FrequencyRowsRows002ChunkD04] using q11FrequencyRowsRows002ChunkD04_lower)
  have h29 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows002 232 8 h28
    (by simpa [q11FrequencyRowsRows002ChunkD05] using q11FrequencyRowsRows002ChunkD05_lower)
  have h30 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows002 240 8 h29
    (by simpa [q11FrequencyRowsRows002ChunkD06] using q11FrequencyRowsRows002ChunkD06_lower)
  have h31 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows002 248 8 h30
    (by simpa [q11FrequencyRowsRows002ChunkD07] using q11FrequencyRowsRows002ChunkD07_lower)
  have hrows : q11FrequencyRowsRows002.take 256 = q11FrequencyRowsRows002 := by
    apply List.take_of_length_le
    simp [q11FrequencyRowsRows002_length]
  simpa only [hrows] using h31

theorem q11FrequencyRowsRows002_lower :
    Q11FrequencyCellsLower q11FrequencyRowsRows002 := by
  exact q11FrequencyCellsLower_of_chunked
    (cells := q11FrequencyRowsRows002)
    (q11ExactChain_width_of_mem (chainCheck_sound q11FrequencyRowsRows002_chain))
    q11FrequencyRowsRows002_chunked_lower

theorem q11FrequencyRowsRows003_chunked_lower :
    Q11FrequencyCellsLower (q11ChunkCells q11FrequencyRowsRows003) := by
  have h0 : Q11FrequencyCellsLower
      (q11ChunkCells (q11FrequencyRowsRows003.take 8)) := by
    simpa [q11FrequencyRowsRows003Chunk00] using q11FrequencyRowsRows003Chunk00_lower
  have h1 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows003 8 8 h0
    (by simpa [q11FrequencyRowsRows003Chunk01] using q11FrequencyRowsRows003Chunk01_lower)
  have h2 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows003 16 8 h1
    (by simpa [q11FrequencyRowsRows003Chunk02] using q11FrequencyRowsRows003Chunk02_lower)
  have h3 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows003 24 8 h2
    (by simpa [q11FrequencyRowsRows003Chunk03] using q11FrequencyRowsRows003Chunk03_lower)
  have h4 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows003 32 8 h3
    (by simpa [q11FrequencyRowsRows003Chunk04] using q11FrequencyRowsRows003Chunk04_lower)
  have h5 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows003 40 8 h4
    (by simpa [q11FrequencyRowsRows003Chunk05] using q11FrequencyRowsRows003Chunk05_lower)
  have h6 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows003 48 8 h5
    (by simpa [q11FrequencyRowsRows003Chunk06] using q11FrequencyRowsRows003Chunk06_lower)
  have h7 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows003 56 8 h6
    (by simpa [q11FrequencyRowsRows003Chunk07] using q11FrequencyRowsRows003Chunk07_lower)
  have h8 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows003 64 8 h7
    (by simpa [q11FrequencyRowsRows003ChunkB00] using q11FrequencyRowsRows003ChunkB00_lower)
  have h9 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows003 72 8 h8
    (by simpa [q11FrequencyRowsRows003ChunkB01] using q11FrequencyRowsRows003ChunkB01_lower)
  have h10 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows003 80 8 h9
    (by simpa [q11FrequencyRowsRows003ChunkB02] using q11FrequencyRowsRows003ChunkB02_lower)
  have h11 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows003 88 8 h10
    (by simpa [q11FrequencyRowsRows003ChunkB03] using q11FrequencyRowsRows003ChunkB03_lower)
  have h12 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows003 96 8 h11
    (by simpa [q11FrequencyRowsRows003ChunkB04] using q11FrequencyRowsRows003ChunkB04_lower)
  have h13 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows003 104 8 h12
    (by simpa [q11FrequencyRowsRows003ChunkB05] using q11FrequencyRowsRows003ChunkB05_lower)
  have h14 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows003 112 8 h13
    (by simpa [q11FrequencyRowsRows003ChunkB06] using q11FrequencyRowsRows003ChunkB06_lower)
  have h15 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows003 120 8 h14
    (by simpa [q11FrequencyRowsRows003ChunkB07] using q11FrequencyRowsRows003ChunkB07_lower)
  have h16 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows003 128 8 h15
    (by simpa [q11FrequencyRowsRows003ChunkC00] using q11FrequencyRowsRows003ChunkC00_lower)
  have h17 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows003 136 8 h16
    (by simpa [q11FrequencyRowsRows003ChunkC01] using q11FrequencyRowsRows003ChunkC01_lower)
  have h18 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows003 144 8 h17
    (by simpa [q11FrequencyRowsRows003ChunkC02] using q11FrequencyRowsRows003ChunkC02_lower)
  have h19 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows003 152 8 h18
    (by simpa [q11FrequencyRowsRows003ChunkC03] using q11FrequencyRowsRows003ChunkC03_lower)
  have h20 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows003 160 8 h19
    (by simpa [q11FrequencyRowsRows003ChunkC04] using q11FrequencyRowsRows003ChunkC04_lower)
  have h21 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows003 168 8 h20
    (by simpa [q11FrequencyRowsRows003ChunkC05] using q11FrequencyRowsRows003ChunkC05_lower)
  have h22 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows003 176 8 h21
    (by simpa [q11FrequencyRowsRows003ChunkC06] using q11FrequencyRowsRows003ChunkC06_lower)
  have h23 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows003 184 8 h22
    (by simpa [q11FrequencyRowsRows003ChunkC07] using q11FrequencyRowsRows003ChunkC07_lower)
  have h24 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows003 192 8 h23
    (by simpa [q11FrequencyRowsRows003ChunkD00] using q11FrequencyRowsRows003ChunkD00_lower)
  have h25 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows003 200 8 h24
    (by simpa [q11FrequencyRowsRows003ChunkD01] using q11FrequencyRowsRows003ChunkD01_lower)
  have h26 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows003 208 8 h25
    (by simpa [q11FrequencyRowsRows003ChunkD02] using q11FrequencyRowsRows003ChunkD02_lower)
  have h27 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows003 216 8 h26
    (by simpa [q11FrequencyRowsRows003ChunkD03] using q11FrequencyRowsRows003ChunkD03_lower)
  have h28 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows003 224 8 h27
    (by simpa [q11FrequencyRowsRows003ChunkD04] using q11FrequencyRowsRows003ChunkD04_lower)
  have h29 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows003 232 8 h28
    (by simpa [q11FrequencyRowsRows003ChunkD05] using q11FrequencyRowsRows003ChunkD05_lower)
  have h30 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows003 240 8 h29
    (by simpa [q11FrequencyRowsRows003ChunkD06] using q11FrequencyRowsRows003ChunkD06_lower)
  have h31 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows003 248 8 h30
    (by simpa [q11FrequencyRowsRows003ChunkD07] using q11FrequencyRowsRows003ChunkD07_lower)
  have hrows : q11FrequencyRowsRows003.take 256 = q11FrequencyRowsRows003 := by
    apply List.take_of_length_le
    simp [q11FrequencyRowsRows003_length]
  simpa only [hrows] using h31

theorem q11FrequencyRowsRows003_lower :
    Q11FrequencyCellsLower q11FrequencyRowsRows003 := by
  exact q11FrequencyCellsLower_of_chunked
    (cells := q11FrequencyRowsRows003)
    (q11ExactChain_width_of_mem (chainCheck_sound q11FrequencyRowsRows003_chain))
    q11FrequencyRowsRows003_chunked_lower

theorem q11FrequencyRowsRows004_chunked_lower :
    Q11FrequencyCellsLower (q11ChunkCells q11FrequencyRowsRows004) := by
  have h0 : Q11FrequencyCellsLower
      (q11ChunkCells (q11FrequencyRowsRows004.take 8)) := by
    simpa [q11FrequencyRowsRows004Chunk00] using q11FrequencyRowsRows004Chunk00_lower
  have h1 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows004 8 8 h0
    (by simpa [q11FrequencyRowsRows004Chunk01] using q11FrequencyRowsRows004Chunk01_lower)
  have h2 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows004 16 8 h1
    (by simpa [q11FrequencyRowsRows004Chunk02] using q11FrequencyRowsRows004Chunk02_lower)
  have h3 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows004 24 8 h2
    (by simpa [q11FrequencyRowsRows004Chunk03] using q11FrequencyRowsRows004Chunk03_lower)
  have h4 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows004 32 8 h3
    (by simpa [q11FrequencyRowsRows004Chunk04] using q11FrequencyRowsRows004Chunk04_lower)
  have h5 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows004 40 8 h4
    (by simpa [q11FrequencyRowsRows004Chunk05] using q11FrequencyRowsRows004Chunk05_lower)
  have h6 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows004 48 8 h5
    (by simpa [q11FrequencyRowsRows004Chunk06] using q11FrequencyRowsRows004Chunk06_lower)
  have h7 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows004 56 8 h6
    (by simpa [q11FrequencyRowsRows004Chunk07] using q11FrequencyRowsRows004Chunk07_lower)
  have h8 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows004 64 8 h7
    (by simpa [q11FrequencyRowsRows004ChunkB00] using q11FrequencyRowsRows004ChunkB00_lower)
  have h9 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows004 72 8 h8
    (by simpa [q11FrequencyRowsRows004ChunkB01] using q11FrequencyRowsRows004ChunkB01_lower)
  have h10 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows004 80 8 h9
    (by simpa [q11FrequencyRowsRows004ChunkB02] using q11FrequencyRowsRows004ChunkB02_lower)
  have h11 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows004 88 8 h10
    (by simpa [q11FrequencyRowsRows004ChunkB03] using q11FrequencyRowsRows004ChunkB03_lower)
  have h12 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows004 96 8 h11
    (by simpa [q11FrequencyRowsRows004ChunkB04] using q11FrequencyRowsRows004ChunkB04_lower)
  have h13 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows004 104 8 h12
    (by simpa [q11FrequencyRowsRows004ChunkB05] using q11FrequencyRowsRows004ChunkB05_lower)
  have h14 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows004 112 8 h13
    (by simpa [q11FrequencyRowsRows004ChunkB06] using q11FrequencyRowsRows004ChunkB06_lower)
  have h15 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows004 120 8 h14
    (by simpa [q11FrequencyRowsRows004ChunkB07] using q11FrequencyRowsRows004ChunkB07_lower)
  have h16 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows004 128 8 h15
    (by simpa [q11FrequencyRowsRows004ChunkC00] using q11FrequencyRowsRows004ChunkC00_lower)
  have h17 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows004 136 8 h16
    (by simpa [q11FrequencyRowsRows004ChunkC01] using q11FrequencyRowsRows004ChunkC01_lower)
  have h18 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows004 144 8 h17
    (by simpa [q11FrequencyRowsRows004ChunkC02] using q11FrequencyRowsRows004ChunkC02_lower)
  have h19 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows004 152 8 h18
    (by simpa [q11FrequencyRowsRows004ChunkC03] using q11FrequencyRowsRows004ChunkC03_lower)
  have h20 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows004 160 8 h19
    (by simpa [q11FrequencyRowsRows004ChunkC04] using q11FrequencyRowsRows004ChunkC04_lower)
  have h21 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows004 168 8 h20
    (by simpa [q11FrequencyRowsRows004ChunkC05] using q11FrequencyRowsRows004ChunkC05_lower)
  have h22 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows004 176 8 h21
    (by simpa [q11FrequencyRowsRows004ChunkC06] using q11FrequencyRowsRows004ChunkC06_lower)
  have h23 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows004 184 8 h22
    (by simpa [q11FrequencyRowsRows004ChunkC07] using q11FrequencyRowsRows004ChunkC07_lower)
  have h24 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows004 192 8 h23
    (by simpa [q11FrequencyRowsRows004ChunkD00] using q11FrequencyRowsRows004ChunkD00_lower)
  have h25 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows004 200 8 h24
    (by simpa [q11FrequencyRowsRows004ChunkD01] using q11FrequencyRowsRows004ChunkD01_lower)
  have h26 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows004 208 8 h25
    (by simpa [q11FrequencyRowsRows004ChunkD02] using q11FrequencyRowsRows004ChunkD02_lower)
  have h27 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows004 216 8 h26
    (by simpa [q11FrequencyRowsRows004ChunkD03] using q11FrequencyRowsRows004ChunkD03_lower)
  have h28 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows004 224 8 h27
    (by simpa [q11FrequencyRowsRows004ChunkD04] using q11FrequencyRowsRows004ChunkD04_lower)
  have h29 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows004 232 8 h28
    (by simpa [q11FrequencyRowsRows004ChunkD05] using q11FrequencyRowsRows004ChunkD05_lower)
  have h30 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows004 240 8 h29
    (by simpa [q11FrequencyRowsRows004ChunkD06] using q11FrequencyRowsRows004ChunkD06_lower)
  have h31 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows004 248 8 h30
    (by simpa [q11FrequencyRowsRows004ChunkD07] using q11FrequencyRowsRows004ChunkD07_lower)
  have hrows : q11FrequencyRowsRows004.take 256 = q11FrequencyRowsRows004 := by
    apply List.take_of_length_le
    simp [q11FrequencyRowsRows004_length]
  simpa only [hrows] using h31

theorem q11FrequencyRowsRows004_lower :
    Q11FrequencyCellsLower q11FrequencyRowsRows004 := by
  exact q11FrequencyCellsLower_of_chunked
    (cells := q11FrequencyRowsRows004)
    (q11ExactChain_width_of_mem (chainCheck_sound q11FrequencyRowsRows004_chain))
    q11FrequencyRowsRows004_chunked_lower

theorem q11FrequencyRowsRows005_chunked_lower :
    Q11FrequencyCellsLower (q11ChunkCells q11FrequencyRowsRows005) := by
  have h0 : Q11FrequencyCellsLower
      (q11ChunkCells (q11FrequencyRowsRows005.take 8)) := by
    simpa [q11FrequencyRowsRows005Chunk00] using q11FrequencyRowsRows005Chunk00_lower
  have h1 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows005 8 8 h0
    (by simpa [q11FrequencyRowsRows005Chunk01] using q11FrequencyRowsRows005Chunk01_lower)
  have h2 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows005 16 8 h1
    (by simpa [q11FrequencyRowsRows005Chunk02] using q11FrequencyRowsRows005Chunk02_lower)
  have h3 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows005 24 8 h2
    (by simpa [q11FrequencyRowsRows005Chunk03] using q11FrequencyRowsRows005Chunk03_lower)
  have h4 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows005 32 8 h3
    (by simpa [q11FrequencyRowsRows005Chunk04] using q11FrequencyRowsRows005Chunk04_lower)
  have h5 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows005 40 8 h4
    (by simpa [q11FrequencyRowsRows005Chunk05] using q11FrequencyRowsRows005Chunk05_lower)
  have h6 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows005 48 8 h5
    (by simpa [q11FrequencyRowsRows005Chunk06] using q11FrequencyRowsRows005Chunk06_lower)
  have h7 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows005 56 8 h6
    (by simpa [q11FrequencyRowsRows005Chunk07] using q11FrequencyRowsRows005Chunk07_lower)
  have h8 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows005 64 8 h7
    (by simpa [q11FrequencyRowsRows005ChunkB00] using q11FrequencyRowsRows005ChunkB00_lower)
  have h9 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows005 72 8 h8
    (by simpa [q11FrequencyRowsRows005ChunkB01] using q11FrequencyRowsRows005ChunkB01_lower)
  have h10 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows005 80 8 h9
    (by simpa [q11FrequencyRowsRows005ChunkB02] using q11FrequencyRowsRows005ChunkB02_lower)
  have h11 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows005 88 8 h10
    (by simpa [q11FrequencyRowsRows005ChunkB03] using q11FrequencyRowsRows005ChunkB03_lower)
  have h12 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows005 96 8 h11
    (by simpa [q11FrequencyRowsRows005ChunkB04] using q11FrequencyRowsRows005ChunkB04_lower)
  have h13 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows005 104 8 h12
    (by simpa [q11FrequencyRowsRows005ChunkB05] using q11FrequencyRowsRows005ChunkB05_lower)
  have h14 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows005 112 8 h13
    (by simpa [q11FrequencyRowsRows005ChunkB06] using q11FrequencyRowsRows005ChunkB06_lower)
  have h15 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows005 120 8 h14
    (by simpa [q11FrequencyRowsRows005ChunkB07] using q11FrequencyRowsRows005ChunkB07_lower)
  have h16 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows005 128 8 h15
    (by simpa [q11FrequencyRowsRows005ChunkC00] using q11FrequencyRowsRows005ChunkC00_lower)
  have h17 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows005 136 8 h16
    (by simpa [q11FrequencyRowsRows005ChunkC01] using q11FrequencyRowsRows005ChunkC01_lower)
  have h18 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows005 144 8 h17
    (by simpa [q11FrequencyRowsRows005ChunkC02] using q11FrequencyRowsRows005ChunkC02_lower)
  have h19 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows005 152 8 h18
    (by simpa [q11FrequencyRowsRows005ChunkC03] using q11FrequencyRowsRows005ChunkC03_lower)
  have h20 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows005 160 8 h19
    (by simpa [q11FrequencyRowsRows005ChunkC04] using q11FrequencyRowsRows005ChunkC04_lower)
  have h21 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows005 168 8 h20
    (by simpa [q11FrequencyRowsRows005ChunkC05] using q11FrequencyRowsRows005ChunkC05_lower)
  have h22 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows005 176 8 h21
    (by simpa [q11FrequencyRowsRows005ChunkC06] using q11FrequencyRowsRows005ChunkC06_lower)
  have h23 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows005 184 8 h22
    (by simpa [q11FrequencyRowsRows005ChunkC07] using q11FrequencyRowsRows005ChunkC07_lower)
  have h24 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows005 192 8 h23
    (by simpa [q11FrequencyRowsRows005ChunkD00] using q11FrequencyRowsRows005ChunkD00_lower)
  have h25 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows005 200 8 h24
    (by simpa [q11FrequencyRowsRows005ChunkD01] using q11FrequencyRowsRows005ChunkD01_lower)
  have h26 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows005 208 8 h25
    (by simpa [q11FrequencyRowsRows005ChunkD02] using q11FrequencyRowsRows005ChunkD02_lower)
  have h27 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows005 216 8 h26
    (by simpa [q11FrequencyRowsRows005ChunkD03] using q11FrequencyRowsRows005ChunkD03_lower)
  have h28 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows005 224 8 h27
    (by simpa [q11FrequencyRowsRows005ChunkD04] using q11FrequencyRowsRows005ChunkD04_lower)
  have h29 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows005 232 8 h28
    (by simpa [q11FrequencyRowsRows005ChunkD05] using q11FrequencyRowsRows005ChunkD05_lower)
  have h30 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows005 240 8 h29
    (by simpa [q11FrequencyRowsRows005ChunkD06] using q11FrequencyRowsRows005ChunkD06_lower)
  have h31 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows005 248 8 h30
    (by simpa [q11FrequencyRowsRows005ChunkD07] using q11FrequencyRowsRows005ChunkD07_lower)
  have hrows : q11FrequencyRowsRows005.take 256 = q11FrequencyRowsRows005 := by
    apply List.take_of_length_le
    simp [q11FrequencyRowsRows005_length]
  simpa only [hrows] using h31

theorem q11FrequencyRowsRows005_lower :
    Q11FrequencyCellsLower q11FrequencyRowsRows005 := by
  exact q11FrequencyCellsLower_of_chunked
    (cells := q11FrequencyRowsRows005)
    (q11ExactChain_width_of_mem (chainCheck_sound q11FrequencyRowsRows005_chain))
    q11FrequencyRowsRows005_chunked_lower

theorem q11FrequencyRowsRows006_chunked_lower :
    Q11FrequencyCellsLower (q11ChunkCells q11FrequencyRowsRows006) := by
  have h0 : Q11FrequencyCellsLower
      (q11ChunkCells (q11FrequencyRowsRows006.take 8)) := by
    simpa [q11FrequencyRowsRows006Chunk00] using q11FrequencyRowsRows006Chunk00_lower
  have h1 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows006 8 8 h0
    (by simpa [q11FrequencyRowsRows006Chunk01] using q11FrequencyRowsRows006Chunk01_lower)
  have h2 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows006 16 8 h1
    (by simpa [q11FrequencyRowsRows006Chunk02] using q11FrequencyRowsRows006Chunk02_lower)
  have h3 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows006 24 8 h2
    (by simpa [q11FrequencyRowsRows006Chunk03] using q11FrequencyRowsRows006Chunk03_lower)
  have h4 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows006 32 8 h3
    (by simpa [q11FrequencyRowsRows006Chunk04] using q11FrequencyRowsRows006Chunk04_lower)
  have h5 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows006 40 8 h4
    (by simpa [q11FrequencyRowsRows006Chunk05] using q11FrequencyRowsRows006Chunk05_lower)
  have h6 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows006 48 8 h5
    (by simpa [q11FrequencyRowsRows006Chunk06] using q11FrequencyRowsRows006Chunk06_lower)
  have h7 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows006 56 8 h6
    (by simpa [q11FrequencyRowsRows006Chunk07] using q11FrequencyRowsRows006Chunk07_lower)
  have h8 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows006 64 8 h7
    (by simpa [q11FrequencyRowsRows006ChunkB00] using q11FrequencyRowsRows006ChunkB00_lower)
  have h9 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows006 72 8 h8
    (by simpa [q11FrequencyRowsRows006ChunkB01] using q11FrequencyRowsRows006ChunkB01_lower)
  have h10 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows006 80 8 h9
    (by simpa [q11FrequencyRowsRows006ChunkB02] using q11FrequencyRowsRows006ChunkB02_lower)
  have h11 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows006 88 8 h10
    (by simpa [q11FrequencyRowsRows006ChunkB03] using q11FrequencyRowsRows006ChunkB03_lower)
  have h12 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows006 96 8 h11
    (by simpa [q11FrequencyRowsRows006ChunkB04] using q11FrequencyRowsRows006ChunkB04_lower)
  have h13 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows006 104 8 h12
    (by simpa [q11FrequencyRowsRows006ChunkB05] using q11FrequencyRowsRows006ChunkB05_lower)
  have h14 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows006 112 8 h13
    (by simpa [q11FrequencyRowsRows006ChunkB06] using q11FrequencyRowsRows006ChunkB06_lower)
  have h15 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows006 120 8 h14
    (by simpa [q11FrequencyRowsRows006ChunkB07] using q11FrequencyRowsRows006ChunkB07_lower)
  have h16 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows006 128 8 h15
    (by simpa [q11FrequencyRowsRows006ChunkC00] using q11FrequencyRowsRows006ChunkC00_lower)
  have h17 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows006 136 8 h16
    (by simpa [q11FrequencyRowsRows006ChunkC01] using q11FrequencyRowsRows006ChunkC01_lower)
  have h18 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows006 144 8 h17
    (by simpa [q11FrequencyRowsRows006ChunkC02] using q11FrequencyRowsRows006ChunkC02_lower)
  have h19 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows006 152 8 h18
    (by simpa [q11FrequencyRowsRows006ChunkC03] using q11FrequencyRowsRows006ChunkC03_lower)
  have h20 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows006 160 8 h19
    (by simpa [q11FrequencyRowsRows006ChunkC04] using q11FrequencyRowsRows006ChunkC04_lower)
  have h21 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows006 168 8 h20
    (by simpa [q11FrequencyRowsRows006ChunkC05] using q11FrequencyRowsRows006ChunkC05_lower)
  have h22 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows006 176 8 h21
    (by simpa [q11FrequencyRowsRows006ChunkC06] using q11FrequencyRowsRows006ChunkC06_lower)
  have h23 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows006 184 8 h22
    (by simpa [q11FrequencyRowsRows006ChunkC07] using q11FrequencyRowsRows006ChunkC07_lower)
  have h24 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows006 192 8 h23
    (by simpa [q11FrequencyRowsRows006ChunkD00] using q11FrequencyRowsRows006ChunkD00_lower)
  have h25 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows006 200 8 h24
    (by simpa [q11FrequencyRowsRows006ChunkD01] using q11FrequencyRowsRows006ChunkD01_lower)
  have h26 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows006 208 8 h25
    (by simpa [q11FrequencyRowsRows006ChunkD02] using q11FrequencyRowsRows006ChunkD02_lower)
  have h27 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows006 216 8 h26
    (by simpa [q11FrequencyRowsRows006ChunkD03] using q11FrequencyRowsRows006ChunkD03_lower)
  have h28 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows006 224 8 h27
    (by simpa [q11FrequencyRowsRows006ChunkD04] using q11FrequencyRowsRows006ChunkD04_lower)
  have h29 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows006 232 8 h28
    (by simpa [q11FrequencyRowsRows006ChunkD05] using q11FrequencyRowsRows006ChunkD05_lower)
  have h30 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows006 240 8 h29
    (by simpa [q11FrequencyRowsRows006ChunkD06] using q11FrequencyRowsRows006ChunkD06_lower)
  have h31 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows006 248 8 h30
    (by simpa [q11FrequencyRowsRows006ChunkD07] using q11FrequencyRowsRows006ChunkD07_lower)
  have hrows : q11FrequencyRowsRows006.take 256 = q11FrequencyRowsRows006 := by
    apply List.take_of_length_le
    simp [q11FrequencyRowsRows006_length]
  simpa only [hrows] using h31

theorem q11FrequencyRowsRows006_lower :
    Q11FrequencyCellsLower q11FrequencyRowsRows006 := by
  exact q11FrequencyCellsLower_of_chunked
    (cells := q11FrequencyRowsRows006)
    (q11ExactChain_width_of_mem (chainCheck_sound q11FrequencyRowsRows006_chain))
    q11FrequencyRowsRows006_chunked_lower

theorem q11FrequencyRowsRows007_chunked_lower :
    Q11FrequencyCellsLower (q11ChunkCells q11FrequencyRowsRows007) := by
  have h0 : Q11FrequencyCellsLower
      (q11ChunkCells (q11FrequencyRowsRows007.take 8)) := by
    simpa [q11FrequencyRowsRows007Chunk00] using q11FrequencyRowsRows007Chunk00_lower
  have h1 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows007 8 8 h0
    (by simpa [q11FrequencyRowsRows007Chunk01] using q11FrequencyRowsRows007Chunk01_lower)
  have h2 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows007 16 8 h1
    (by simpa [q11FrequencyRowsRows007Chunk02] using q11FrequencyRowsRows007Chunk02_lower)
  have h3 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows007 24 8 h2
    (by simpa [q11FrequencyRowsRows007Chunk03] using q11FrequencyRowsRows007Chunk03_lower)
  have h4 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows007 32 8 h3
    (by simpa [q11FrequencyRowsRows007Chunk04] using q11FrequencyRowsRows007Chunk04_lower)
  have h5 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows007 40 8 h4
    (by simpa [q11FrequencyRowsRows007Chunk05] using q11FrequencyRowsRows007Chunk05_lower)
  have h6 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows007 48 8 h5
    (by simpa [q11FrequencyRowsRows007Chunk06] using q11FrequencyRowsRows007Chunk06_lower)
  have h7 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows007 56 8 h6
    (by simpa [q11FrequencyRowsRows007Chunk07] using q11FrequencyRowsRows007Chunk07_lower)
  have h8 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows007 64 8 h7
    (by simpa [q11FrequencyRowsRows007ChunkB00] using q11FrequencyRowsRows007ChunkB00_lower)
  have h9 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows007 72 8 h8
    (by simpa [q11FrequencyRowsRows007ChunkB01] using q11FrequencyRowsRows007ChunkB01_lower)
  have h10 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows007 80 8 h9
    (by simpa [q11FrequencyRowsRows007ChunkB02] using q11FrequencyRowsRows007ChunkB02_lower)
  have h11 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows007 88 8 h10
    (by simpa [q11FrequencyRowsRows007ChunkB03] using q11FrequencyRowsRows007ChunkB03_lower)
  have h12 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows007 96 8 h11
    (by simpa [q11FrequencyRowsRows007ChunkB04] using q11FrequencyRowsRows007ChunkB04_lower)
  have h13 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows007 104 8 h12
    (by simpa [q11FrequencyRowsRows007ChunkB05] using q11FrequencyRowsRows007ChunkB05_lower)
  have h14 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows007 112 8 h13
    (by simpa [q11FrequencyRowsRows007ChunkB06] using q11FrequencyRowsRows007ChunkB06_lower)
  have h15 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows007 120 8 h14
    (by simpa [q11FrequencyRowsRows007ChunkB07] using q11FrequencyRowsRows007ChunkB07_lower)
  have h16 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows007 128 8 h15
    (by simpa [q11FrequencyRowsRows007ChunkC00] using q11FrequencyRowsRows007ChunkC00_lower)
  have h17 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows007 136 8 h16
    (by simpa [q11FrequencyRowsRows007ChunkC01] using q11FrequencyRowsRows007ChunkC01_lower)
  have h18 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows007 144 8 h17
    (by simpa [q11FrequencyRowsRows007ChunkC02] using q11FrequencyRowsRows007ChunkC02_lower)
  have h19 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows007 152 8 h18
    (by simpa [q11FrequencyRowsRows007ChunkC03] using q11FrequencyRowsRows007ChunkC03_lower)
  have h20 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows007 160 8 h19
    (by simpa [q11FrequencyRowsRows007ChunkC04] using q11FrequencyRowsRows007ChunkC04_lower)
  have h21 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows007 168 8 h20
    (by simpa [q11FrequencyRowsRows007ChunkC05] using q11FrequencyRowsRows007ChunkC05_lower)
  have h22 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows007 176 8 h21
    (by simpa [q11FrequencyRowsRows007ChunkC06] using q11FrequencyRowsRows007ChunkC06_lower)
  have h23 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows007 184 8 h22
    (by simpa [q11FrequencyRowsRows007ChunkC07] using q11FrequencyRowsRows007ChunkC07_lower)
  have h24 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows007 192 8 h23
    (by simpa [q11FrequencyRowsRows007ChunkD00] using q11FrequencyRowsRows007ChunkD00_lower)
  have h25 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows007 200 8 h24
    (by simpa [q11FrequencyRowsRows007ChunkD01] using q11FrequencyRowsRows007ChunkD01_lower)
  have h26 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows007 208 8 h25
    (by simpa [q11FrequencyRowsRows007ChunkD02] using q11FrequencyRowsRows007ChunkD02_lower)
  have h27 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows007 216 8 h26
    (by simpa [q11FrequencyRowsRows007ChunkD03] using q11FrequencyRowsRows007ChunkD03_lower)
  have h28 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows007 224 8 h27
    (by simpa [q11FrequencyRowsRows007ChunkD04] using q11FrequencyRowsRows007ChunkD04_lower)
  have h29 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows007 232 8 h28
    (by simpa [q11FrequencyRowsRows007ChunkD05] using q11FrequencyRowsRows007ChunkD05_lower)
  have h30 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows007 240 8 h29
    (by simpa [q11FrequencyRowsRows007ChunkD06] using q11FrequencyRowsRows007ChunkD06_lower)
  have h31 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows007 248 8 h30
    (by simpa [q11FrequencyRowsRows007ChunkD07] using q11FrequencyRowsRows007ChunkD07_lower)
  have hrows : q11FrequencyRowsRows007.take 256 = q11FrequencyRowsRows007 := by
    apply List.take_of_length_le
    simp [q11FrequencyRowsRows007_length]
  simpa only [hrows] using h31

theorem q11FrequencyRowsRows007_lower :
    Q11FrequencyCellsLower q11FrequencyRowsRows007 := by
  exact q11FrequencyCellsLower_of_chunked
    (cells := q11FrequencyRowsRows007)
    (q11ExactChain_width_of_mem (chainCheck_sound q11FrequencyRowsRows007_chain))
    q11FrequencyRowsRows007_chunked_lower

theorem q11FrequencyRowsRows008_chunked_lower :
    Q11FrequencyCellsLower (q11ChunkCells q11FrequencyRowsRows008) := by
  have h0 : Q11FrequencyCellsLower
      (q11ChunkCells (q11FrequencyRowsRows008.take 8)) := by
    simpa [q11FrequencyRowsRows008Chunk00] using q11FrequencyRowsRows008Chunk00_lower
  have h1 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows008 8 8 h0
    (by simpa [q11FrequencyRowsRows008Chunk01] using q11FrequencyRowsRows008Chunk01_lower)
  have h2 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows008 16 8 h1
    (by simpa [q11FrequencyRowsRows008Chunk02] using q11FrequencyRowsRows008Chunk02_lower)
  have h3 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows008 24 8 h2
    (by simpa [q11FrequencyRowsRows008Chunk03] using q11FrequencyRowsRows008Chunk03_lower)
  have h4 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows008 32 8 h3
    (by simpa [q11FrequencyRowsRows008Chunk04] using q11FrequencyRowsRows008Chunk04_lower)
  have h5 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows008 40 8 h4
    (by simpa [q11FrequencyRowsRows008Chunk05] using q11FrequencyRowsRows008Chunk05_lower)
  have h6 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows008 48 8 h5
    (by simpa [q11FrequencyRowsRows008Chunk06] using q11FrequencyRowsRows008Chunk06_lower)
  have h7 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows008 56 8 h6
    (by simpa [q11FrequencyRowsRows008Chunk07] using q11FrequencyRowsRows008Chunk07_lower)
  have h8 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows008 64 8 h7
    (by simpa [q11FrequencyRowsRows008ChunkB00] using q11FrequencyRowsRows008ChunkB00_lower)
  have h9 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows008 72 8 h8
    (by simpa [q11FrequencyRowsRows008ChunkB01] using q11FrequencyRowsRows008ChunkB01_lower)
  have h10 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows008 80 8 h9
    (by simpa [q11FrequencyRowsRows008ChunkB02] using q11FrequencyRowsRows008ChunkB02_lower)
  have h11 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows008 88 8 h10
    (by simpa [q11FrequencyRowsRows008ChunkB03] using q11FrequencyRowsRows008ChunkB03_lower)
  have h12 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows008 96 8 h11
    (by simpa [q11FrequencyRowsRows008ChunkB04] using q11FrequencyRowsRows008ChunkB04_lower)
  have h13 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows008 104 8 h12
    (by simpa [q11FrequencyRowsRows008ChunkB05] using q11FrequencyRowsRows008ChunkB05_lower)
  have h14 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows008 112 8 h13
    (by simpa [q11FrequencyRowsRows008ChunkB06] using q11FrequencyRowsRows008ChunkB06_lower)
  have h15 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows008 120 8 h14
    (by simpa [q11FrequencyRowsRows008ChunkB07] using q11FrequencyRowsRows008ChunkB07_lower)
  have h16 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows008 128 8 h15
    (by simpa [q11FrequencyRowsRows008ChunkC00] using q11FrequencyRowsRows008ChunkC00_lower)
  have h17 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows008 136 8 h16
    (by simpa [q11FrequencyRowsRows008ChunkC01] using q11FrequencyRowsRows008ChunkC01_lower)
  have h18 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows008 144 8 h17
    (by simpa [q11FrequencyRowsRows008ChunkC02] using q11FrequencyRowsRows008ChunkC02_lower)
  have h19 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows008 152 8 h18
    (by simpa [q11FrequencyRowsRows008ChunkC03] using q11FrequencyRowsRows008ChunkC03_lower)
  have h20 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows008 160 8 h19
    (by simpa [q11FrequencyRowsRows008ChunkC04] using q11FrequencyRowsRows008ChunkC04_lower)
  have h21 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows008 168 8 h20
    (by simpa [q11FrequencyRowsRows008ChunkC05] using q11FrequencyRowsRows008ChunkC05_lower)
  have h22 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows008 176 8 h21
    (by simpa [q11FrequencyRowsRows008ChunkC06] using q11FrequencyRowsRows008ChunkC06_lower)
  have h23 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows008 184 8 h22
    (by simpa [q11FrequencyRowsRows008ChunkC07] using q11FrequencyRowsRows008ChunkC07_lower)
  have h24 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows008 192 8 h23
    (by simpa [q11FrequencyRowsRows008ChunkD00] using q11FrequencyRowsRows008ChunkD00_lower)
  have h25 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows008 200 8 h24
    (by simpa [q11FrequencyRowsRows008ChunkD01] using q11FrequencyRowsRows008ChunkD01_lower)
  have h26 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows008 208 8 h25
    (by simpa [q11FrequencyRowsRows008ChunkD02] using q11FrequencyRowsRows008ChunkD02_lower)
  have h27 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows008 216 8 h26
    (by simpa [q11FrequencyRowsRows008ChunkD03] using q11FrequencyRowsRows008ChunkD03_lower)
  have h28 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows008 224 8 h27
    (by simpa [q11FrequencyRowsRows008ChunkD04] using q11FrequencyRowsRows008ChunkD04_lower)
  have h29 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows008 232 8 h28
    (by simpa [q11FrequencyRowsRows008ChunkD05] using q11FrequencyRowsRows008ChunkD05_lower)
  have h30 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows008 240 8 h29
    (by simpa [q11FrequencyRowsRows008ChunkD06] using q11FrequencyRowsRows008ChunkD06_lower)
  have h31 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows008 248 8 h30
    (by simpa [q11FrequencyRowsRows008ChunkD07] using q11FrequencyRowsRows008ChunkD07_lower)
  have hrows : q11FrequencyRowsRows008.take 256 = q11FrequencyRowsRows008 := by
    apply List.take_of_length_le
    simp [q11FrequencyRowsRows008_length]
  simpa only [hrows] using h31

theorem q11FrequencyRowsRows008_lower :
    Q11FrequencyCellsLower q11FrequencyRowsRows008 := by
  exact q11FrequencyCellsLower_of_chunked
    (cells := q11FrequencyRowsRows008)
    (q11ExactChain_width_of_mem (chainCheck_sound q11FrequencyRowsRows008_chain))
    q11FrequencyRowsRows008_chunked_lower

theorem q11FrequencyRowsRows009_chunked_lower :
    Q11FrequencyCellsLower (q11ChunkCells q11FrequencyRowsRows009) := by
  have h0 : Q11FrequencyCellsLower
      (q11ChunkCells (q11FrequencyRowsRows009.take 8)) := by
    simpa [q11FrequencyRowsRows009Chunk00] using q11FrequencyRowsRows009Chunk00_lower
  have h1 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows009 8 8 h0
    (by simpa [q11FrequencyRowsRows009Chunk01] using q11FrequencyRowsRows009Chunk01_lower)
  have h2 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows009 16 8 h1
    (by simpa [q11FrequencyRowsRows009Chunk02] using q11FrequencyRowsRows009Chunk02_lower)
  have h3 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows009 24 8 h2
    (by simpa [q11FrequencyRowsRows009Chunk03] using q11FrequencyRowsRows009Chunk03_lower)
  have h4 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows009 32 8 h3
    (by simpa [q11FrequencyRowsRows009Chunk04] using q11FrequencyRowsRows009Chunk04_lower)
  have h5 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows009 40 8 h4
    (by simpa [q11FrequencyRowsRows009Chunk05] using q11FrequencyRowsRows009Chunk05_lower)
  have h6 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows009 48 8 h5
    (by simpa [q11FrequencyRowsRows009Chunk06] using q11FrequencyRowsRows009Chunk06_lower)
  have h7 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows009 56 8 h6
    (by simpa [q11FrequencyRowsRows009Chunk07] using q11FrequencyRowsRows009Chunk07_lower)
  have h8 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows009 64 8 h7
    (by simpa [q11FrequencyRowsRows009ChunkB00] using q11FrequencyRowsRows009ChunkB00_lower)
  have h9 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows009 72 8 h8
    (by simpa [q11FrequencyRowsRows009ChunkB01] using q11FrequencyRowsRows009ChunkB01_lower)
  have h10 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows009 80 8 h9
    (by simpa [q11FrequencyRowsRows009ChunkB02] using q11FrequencyRowsRows009ChunkB02_lower)
  have h11 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows009 88 8 h10
    (by simpa [q11FrequencyRowsRows009ChunkB03] using q11FrequencyRowsRows009ChunkB03_lower)
  have h12 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows009 96 8 h11
    (by simpa [q11FrequencyRowsRows009ChunkB04] using q11FrequencyRowsRows009ChunkB04_lower)
  have h13 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows009 104 8 h12
    (by simpa [q11FrequencyRowsRows009ChunkB05] using q11FrequencyRowsRows009ChunkB05_lower)
  have h14 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows009 112 8 h13
    (by simpa [q11FrequencyRowsRows009ChunkB06] using q11FrequencyRowsRows009ChunkB06_lower)
  have h15 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows009 120 8 h14
    (by simpa [q11FrequencyRowsRows009ChunkB07] using q11FrequencyRowsRows009ChunkB07_lower)
  have h16 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows009 128 8 h15
    (by simpa [q11FrequencyRowsRows009ChunkC00] using q11FrequencyRowsRows009ChunkC00_lower)
  have h17 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows009 136 8 h16
    (by simpa [q11FrequencyRowsRows009ChunkC01] using q11FrequencyRowsRows009ChunkC01_lower)
  have h18 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows009 144 8 h17
    (by simpa [q11FrequencyRowsRows009ChunkC02] using q11FrequencyRowsRows009ChunkC02_lower)
  have h19 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows009 152 8 h18
    (by simpa [q11FrequencyRowsRows009ChunkC03] using q11FrequencyRowsRows009ChunkC03_lower)
  have h20 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows009 160 8 h19
    (by simpa [q11FrequencyRowsRows009ChunkC04] using q11FrequencyRowsRows009ChunkC04_lower)
  have h21 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows009 168 8 h20
    (by simpa [q11FrequencyRowsRows009ChunkC05] using q11FrequencyRowsRows009ChunkC05_lower)
  have h22 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows009 176 8 h21
    (by simpa [q11FrequencyRowsRows009ChunkC06] using q11FrequencyRowsRows009ChunkC06_lower)
  have h23 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows009 184 8 h22
    (by simpa [q11FrequencyRowsRows009ChunkC07] using q11FrequencyRowsRows009ChunkC07_lower)
  have h24 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows009 192 8 h23
    (by simpa [q11FrequencyRowsRows009ChunkD00] using q11FrequencyRowsRows009ChunkD00_lower)
  have h25 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows009 200 8 h24
    (by simpa [q11FrequencyRowsRows009ChunkD01] using q11FrequencyRowsRows009ChunkD01_lower)
  have h26 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows009 208 8 h25
    (by simpa [q11FrequencyRowsRows009ChunkD02] using q11FrequencyRowsRows009ChunkD02_lower)
  have h27 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows009 216 8 h26
    (by simpa [q11FrequencyRowsRows009ChunkD03] using q11FrequencyRowsRows009ChunkD03_lower)
  have h28 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows009 224 8 h27
    (by simpa [q11FrequencyRowsRows009ChunkD04] using q11FrequencyRowsRows009ChunkD04_lower)
  have h29 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows009 232 8 h28
    (by simpa [q11FrequencyRowsRows009ChunkD05] using q11FrequencyRowsRows009ChunkD05_lower)
  have h30 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows009 240 8 h29
    (by simpa [q11FrequencyRowsRows009ChunkD06] using q11FrequencyRowsRows009ChunkD06_lower)
  have h31 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows009 248 8 h30
    (by simpa [q11FrequencyRowsRows009ChunkD07] using q11FrequencyRowsRows009ChunkD07_lower)
  have hrows : q11FrequencyRowsRows009.take 256 = q11FrequencyRowsRows009 := by
    apply List.take_of_length_le
    simp [q11FrequencyRowsRows009_length]
  simpa only [hrows] using h31

theorem q11FrequencyRowsRows009_lower :
    Q11FrequencyCellsLower q11FrequencyRowsRows009 := by
  exact q11FrequencyCellsLower_of_chunked
    (cells := q11FrequencyRowsRows009)
    (q11ExactChain_width_of_mem (chainCheck_sound q11FrequencyRowsRows009_chain))
    q11FrequencyRowsRows009_chunked_lower

theorem q11FrequencyRowsRows010_chunked_lower :
    Q11FrequencyCellsLower (q11ChunkCells q11FrequencyRowsRows010) := by
  have h0 : Q11FrequencyCellsLower
      (q11ChunkCells (q11FrequencyRowsRows010.take 8)) := by
    simpa [q11FrequencyRowsRows010Chunk00] using q11FrequencyRowsRows010Chunk00_lower
  have h1 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows010 8 8 h0
    (by simpa [q11FrequencyRowsRows010Chunk01] using q11FrequencyRowsRows010Chunk01_lower)
  have h2 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows010 16 8 h1
    (by simpa [q11FrequencyRowsRows010Chunk02] using q11FrequencyRowsRows010Chunk02_lower)
  have h3 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows010 24 8 h2
    (by simpa [q11FrequencyRowsRows010Chunk03] using q11FrequencyRowsRows010Chunk03_lower)
  have h4 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows010 32 8 h3
    (by simpa [q11FrequencyRowsRows010Chunk04] using q11FrequencyRowsRows010Chunk04_lower)
  have h5 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows010 40 8 h4
    (by simpa [q11FrequencyRowsRows010Chunk05] using q11FrequencyRowsRows010Chunk05_lower)
  have h6 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows010 48 8 h5
    (by simpa [q11FrequencyRowsRows010Chunk06] using q11FrequencyRowsRows010Chunk06_lower)
  have h7 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows010 56 8 h6
    (by simpa [q11FrequencyRowsRows010Chunk07] using q11FrequencyRowsRows010Chunk07_lower)
  have h8 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows010 64 8 h7
    (by simpa [q11FrequencyRowsRows010ChunkB00] using q11FrequencyRowsRows010ChunkB00_lower)
  have h9 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows010 72 8 h8
    (by simpa [q11FrequencyRowsRows010ChunkB01] using q11FrequencyRowsRows010ChunkB01_lower)
  have h10 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows010 80 8 h9
    (by simpa [q11FrequencyRowsRows010ChunkB02] using q11FrequencyRowsRows010ChunkB02_lower)
  have h11 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows010 88 8 h10
    (by simpa [q11FrequencyRowsRows010ChunkB03] using q11FrequencyRowsRows010ChunkB03_lower)
  have h12 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows010 96 8 h11
    (by simpa [q11FrequencyRowsRows010ChunkB04] using q11FrequencyRowsRows010ChunkB04_lower)
  have h13 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows010 104 8 h12
    (by simpa [q11FrequencyRowsRows010ChunkB05] using q11FrequencyRowsRows010ChunkB05_lower)
  have h14 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows010 112 8 h13
    (by simpa [q11FrequencyRowsRows010ChunkB06] using q11FrequencyRowsRows010ChunkB06_lower)
  have h15 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows010 120 8 h14
    (by simpa [q11FrequencyRowsRows010ChunkB07] using q11FrequencyRowsRows010ChunkB07_lower)
  have h16 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows010 128 8 h15
    (by simpa [q11FrequencyRowsRows010ChunkC00] using q11FrequencyRowsRows010ChunkC00_lower)
  have h17 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows010 136 8 h16
    (by simpa [q11FrequencyRowsRows010ChunkC01] using q11FrequencyRowsRows010ChunkC01_lower)
  have h18 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows010 144 8 h17
    (by simpa [q11FrequencyRowsRows010ChunkC02] using q11FrequencyRowsRows010ChunkC02_lower)
  have h19 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows010 152 8 h18
    (by simpa [q11FrequencyRowsRows010ChunkC03] using q11FrequencyRowsRows010ChunkC03_lower)
  have h20 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows010 160 8 h19
    (by simpa [q11FrequencyRowsRows010ChunkC04] using q11FrequencyRowsRows010ChunkC04_lower)
  have h21 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows010 168 8 h20
    (by simpa [q11FrequencyRowsRows010ChunkC05] using q11FrequencyRowsRows010ChunkC05_lower)
  have h22 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows010 176 8 h21
    (by simpa [q11FrequencyRowsRows010ChunkC06] using q11FrequencyRowsRows010ChunkC06_lower)
  have h23 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows010 184 8 h22
    (by simpa [q11FrequencyRowsRows010ChunkC07] using q11FrequencyRowsRows010ChunkC07_lower)
  have h24 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows010 192 8 h23
    (by simpa [q11FrequencyRowsRows010ChunkD00] using q11FrequencyRowsRows010ChunkD00_lower)
  have h25 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows010 200 8 h24
    (by simpa [q11FrequencyRowsRows010ChunkD01] using q11FrequencyRowsRows010ChunkD01_lower)
  have h26 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows010 208 8 h25
    (by simpa [q11FrequencyRowsRows010ChunkD02] using q11FrequencyRowsRows010ChunkD02_lower)
  have h27 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows010 216 8 h26
    (by simpa [q11FrequencyRowsRows010ChunkD03] using q11FrequencyRowsRows010ChunkD03_lower)
  have h28 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows010 224 8 h27
    (by simpa [q11FrequencyRowsRows010ChunkD04] using q11FrequencyRowsRows010ChunkD04_lower)
  have h29 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows010 232 8 h28
    (by simpa [q11FrequencyRowsRows010ChunkD05] using q11FrequencyRowsRows010ChunkD05_lower)
  have h30 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows010 240 8 h29
    (by simpa [q11FrequencyRowsRows010ChunkD06] using q11FrequencyRowsRows010ChunkD06_lower)
  have h31 := q11ChunkCells_lower_of_take_add q11FrequencyRowsRows010 248 8 h30
    (by simpa [q11FrequencyRowsRows010ChunkD07] using q11FrequencyRowsRows010ChunkD07_lower)
  have hrows : q11FrequencyRowsRows010.take 256 = q11FrequencyRowsRows010 := by
    apply List.take_of_length_le
    simp [q11FrequencyRowsRows010_length]
  simpa only [hrows] using h31

theorem q11FrequencyRowsRows010_lower :
    Q11FrequencyCellsLower q11FrequencyRowsRows010 := by
  exact q11FrequencyCellsLower_of_chunked
    (cells := q11FrequencyRowsRows010)
    (q11ExactChain_width_of_mem (chainCheck_sound q11FrequencyRowsRows010_chain))
    q11FrequencyRowsRows010_chunked_lower

def q11FrequencyPrefixRows : List ReceiptCell :=
  q11FrequencyRowsRows000 ++
  q11FrequencyRowsRows001 ++
  q11FrequencyRowsRows002 ++
  q11FrequencyRowsRows003 ++
  q11FrequencyRowsRows004 ++
  q11FrequencyRowsRows005 ++
  q11FrequencyRowsRows006 ++
  q11FrequencyRowsRows007 ++
  q11FrequencyRowsRows008 ++
  q11FrequencyRowsRows009 ++
  q11FrequencyRowsRows010

theorem q11FrequencyPrefixRows_lower :
    Q11FrequencyCellsLower q11FrequencyPrefixRows := by
  unfold q11FrequencyPrefixRows
  have h10 := q11FrequencyCellsLower_append
    q11FrequencyRowsRows009_lower q11FrequencyRowsRows010_lower
  have h09 := q11FrequencyCellsLower_append
    q11FrequencyRowsRows008_lower h10
  have h08 := q11FrequencyCellsLower_append
    q11FrequencyRowsRows007_lower h09
  have h07 := q11FrequencyCellsLower_append
    q11FrequencyRowsRows006_lower h08
  have h06 := q11FrequencyCellsLower_append
    q11FrequencyRowsRows005_lower h07
  have h05 := q11FrequencyCellsLower_append
    q11FrequencyRowsRows004_lower h06
  have h04 := q11FrequencyCellsLower_append
    q11FrequencyRowsRows003_lower h05
  have h03 := q11FrequencyCellsLower_append
    q11FrequencyRowsRows002_lower h04
  have h02 := q11FrequencyCellsLower_append
    q11FrequencyRowsRows001_lower h03
  have h01 := q11FrequencyCellsLower_append
    q11FrequencyRowsRows000_lower h02
  set_option maxRecDepth 100000 in
    exact h01

theorem q11FrequencyPrefixRows_chain :
    ExactChain q11FrequencyPrefixRows (1 / 2 : ℚ) (289 / 160 : ℚ) := by
  unfold q11FrequencyPrefixRows
  exact (exactChain_append
      (List.ne_nil_of_length_pos (by rw [q11FrequencyRowsRows010_length]; norm_num))
      (exactChain_append
      (List.ne_nil_of_length_pos (by rw [q11FrequencyRowsRows009_length]; norm_num))
      (exactChain_append
      (List.ne_nil_of_length_pos (by rw [q11FrequencyRowsRows008_length]; norm_num))
      (exactChain_append
      (List.ne_nil_of_length_pos (by rw [q11FrequencyRowsRows007_length]; norm_num))
      (exactChain_append
      (List.ne_nil_of_length_pos (by rw [q11FrequencyRowsRows006_length]; norm_num))
      (exactChain_append
      (List.ne_nil_of_length_pos (by rw [q11FrequencyRowsRows005_length]; norm_num))
      (exactChain_append
      (List.ne_nil_of_length_pos (by rw [q11FrequencyRowsRows004_length]; norm_num))
      (exactChain_append
      (List.ne_nil_of_length_pos (by rw [q11FrequencyRowsRows003_length]; norm_num))
      (exactChain_append
      (List.ne_nil_of_length_pos (by rw [q11FrequencyRowsRows002_length]; norm_num))
      (exactChain_append
      (List.ne_nil_of_length_pos (by rw [q11FrequencyRowsRows001_length]; norm_num))
      (chainCheck_sound q11FrequencyRowsRows000_chain)
      (chainCheck_sound q11FrequencyRowsRows001_chain))
      (chainCheck_sound q11FrequencyRowsRows002_chain))
      (chainCheck_sound q11FrequencyRowsRows003_chain))
      (chainCheck_sound q11FrequencyRowsRows004_chain))
      (chainCheck_sound q11FrequencyRowsRows005_chain))
      (chainCheck_sound q11FrequencyRowsRows006_chain))
      (chainCheck_sound q11FrequencyRowsRows007_chain))
      (chainCheck_sound q11FrequencyRowsRows008_chain))
      (chainCheck_sound q11FrequencyRowsRows009_chain))
      (chainCheck_sound q11FrequencyRowsRows010_chain))

theorem q11FrequencyPrefixRows_penalty :
    penaltyMass (1217 / 200 : ℚ) 0 q11FrequencyPrefixRows =
      (437939106871569 / 409600000000000 : ℚ) := by
  simp only [q11FrequencyPrefixRows, penaltyMass_append,
    q11FrequencyRowsRows000_penalty, q11FrequencyRowsRows001_penalty,
    q11FrequencyRowsRows002_penalty, q11FrequencyRowsRows003_penalty,
    q11FrequencyRowsRows004_penalty, q11FrequencyRowsRows005_penalty,
    q11FrequencyRowsRows006_penalty, q11FrequencyRowsRows007_penalty,
    q11FrequencyRowsRows008_penalty, q11FrequencyRowsRows009_penalty,
    q11FrequencyRowsRows010_penalty]
  norm_num

end Li2Lean.P0.Q11Data
