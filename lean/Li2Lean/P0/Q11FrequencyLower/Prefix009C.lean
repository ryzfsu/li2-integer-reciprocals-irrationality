/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.Q11FrequencyLower.Common

namespace Li2Lean.P0.Q11Data

/-! Generated q=11 frequency lower checks.  Each chunk reuses the chained
    endpoint-vector checker; the source table rows are unchanged. -/

open Li2Lean.F_L8
open Li2Lean.P0.CA.Frequency
open Li2Lean.P0.CA.Receipt
def q11FrequencyRowsRows009ChunkC00 : List ReceiptCell :=
  (q11FrequencyRowsRows009.drop 128).take 8

theorem q11FrequencyRowsRows009ChunkC00_check :
    q11ShardCheckWeightedTight (q11ChunkRows q11FrequencyRowsRows009ChunkC00) = true := by
  decide +kernel

theorem q11FrequencyRowsRows009ChunkC00_lower :
    Q11FrequencyCellsLower (q11ChunkCells q11FrequencyRowsRows009ChunkC00) :=
  q11ChunkCells_lower_of_check q11FrequencyRowsRows009ChunkC00_check

def q11FrequencyRowsRows009ChunkC01 : List ReceiptCell :=
  (q11FrequencyRowsRows009.drop 136).take 8

theorem q11FrequencyRowsRows009ChunkC01_check :
    q11ShardCheckWeightedTight (q11ChunkRows q11FrequencyRowsRows009ChunkC01) = true := by
  decide +kernel

theorem q11FrequencyRowsRows009ChunkC01_lower :
    Q11FrequencyCellsLower (q11ChunkCells q11FrequencyRowsRows009ChunkC01) :=
  q11ChunkCells_lower_of_check q11FrequencyRowsRows009ChunkC01_check

def q11FrequencyRowsRows009ChunkC02 : List ReceiptCell :=
  (q11FrequencyRowsRows009.drop 144).take 8

theorem q11FrequencyRowsRows009ChunkC02_check :
    q11ShardCheckWeightedTight (q11ChunkRows q11FrequencyRowsRows009ChunkC02) = true := by
  decide +kernel

theorem q11FrequencyRowsRows009ChunkC02_lower :
    Q11FrequencyCellsLower (q11ChunkCells q11FrequencyRowsRows009ChunkC02) :=
  q11ChunkCells_lower_of_check q11FrequencyRowsRows009ChunkC02_check

def q11FrequencyRowsRows009ChunkC03 : List ReceiptCell :=
  (q11FrequencyRowsRows009.drop 152).take 8

theorem q11FrequencyRowsRows009ChunkC03_check :
    q11ShardCheckWeightedTight (q11ChunkRows q11FrequencyRowsRows009ChunkC03) = true := by
  decide +kernel

theorem q11FrequencyRowsRows009ChunkC03_lower :
    Q11FrequencyCellsLower (q11ChunkCells q11FrequencyRowsRows009ChunkC03) :=
  q11ChunkCells_lower_of_check q11FrequencyRowsRows009ChunkC03_check

def q11FrequencyRowsRows009ChunkC04 : List ReceiptCell :=
  (q11FrequencyRowsRows009.drop 160).take 8

theorem q11FrequencyRowsRows009ChunkC04_check :
    q11ShardCheckWeightedTight (q11ChunkRows q11FrequencyRowsRows009ChunkC04) = true := by
  decide +kernel

theorem q11FrequencyRowsRows009ChunkC04_lower :
    Q11FrequencyCellsLower (q11ChunkCells q11FrequencyRowsRows009ChunkC04) :=
  q11ChunkCells_lower_of_check q11FrequencyRowsRows009ChunkC04_check

def q11FrequencyRowsRows009ChunkC05 : List ReceiptCell :=
  (q11FrequencyRowsRows009.drop 168).take 8

theorem q11FrequencyRowsRows009ChunkC05_check :
    q11ShardCheckWeightedTight (q11ChunkRows q11FrequencyRowsRows009ChunkC05) = true := by
  decide +kernel

theorem q11FrequencyRowsRows009ChunkC05_lower :
    Q11FrequencyCellsLower (q11ChunkCells q11FrequencyRowsRows009ChunkC05) :=
  q11ChunkCells_lower_of_check q11FrequencyRowsRows009ChunkC05_check

def q11FrequencyRowsRows009ChunkC06 : List ReceiptCell :=
  (q11FrequencyRowsRows009.drop 176).take 8

theorem q11FrequencyRowsRows009ChunkC06_check :
    q11ShardCheckWeightedTight (q11ChunkRows q11FrequencyRowsRows009ChunkC06) = true := by
  decide +kernel

theorem q11FrequencyRowsRows009ChunkC06_lower :
    Q11FrequencyCellsLower (q11ChunkCells q11FrequencyRowsRows009ChunkC06) :=
  q11ChunkCells_lower_of_check q11FrequencyRowsRows009ChunkC06_check

def q11FrequencyRowsRows009ChunkC07 : List ReceiptCell :=
  (q11FrequencyRowsRows009.drop 184).take 8

theorem q11FrequencyRowsRows009ChunkC07_check :
    q11ShardCheckWeightedTight (q11ChunkRows q11FrequencyRowsRows009ChunkC07) = true := by
  decide +kernel

theorem q11FrequencyRowsRows009ChunkC07_lower :
    Q11FrequencyCellsLower (q11ChunkCells q11FrequencyRowsRows009ChunkC07) :=
  q11ChunkCells_lower_of_check q11FrequencyRowsRows009ChunkC07_check

end Li2Lean.P0.Q11Data
