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
def q11FrequencyRowsRows009ChunkD00 : List ReceiptCell :=
  (q11FrequencyRowsRows009.drop 192).take 8

theorem q11FrequencyRowsRows009ChunkD00_check :
    q11ShardCheckWeightedTight (q11ChunkRows q11FrequencyRowsRows009ChunkD00) = true := by
  decide +kernel

theorem q11FrequencyRowsRows009ChunkD00_lower :
    Q11FrequencyCellsLower (q11ChunkCells q11FrequencyRowsRows009ChunkD00) :=
  q11ChunkCells_lower_of_check q11FrequencyRowsRows009ChunkD00_check

def q11FrequencyRowsRows009ChunkD01 : List ReceiptCell :=
  (q11FrequencyRowsRows009.drop 200).take 8

theorem q11FrequencyRowsRows009ChunkD01_check :
    q11ShardCheckWeightedTight (q11ChunkRows q11FrequencyRowsRows009ChunkD01) = true := by
  decide +kernel

theorem q11FrequencyRowsRows009ChunkD01_lower :
    Q11FrequencyCellsLower (q11ChunkCells q11FrequencyRowsRows009ChunkD01) :=
  q11ChunkCells_lower_of_check q11FrequencyRowsRows009ChunkD01_check

def q11FrequencyRowsRows009ChunkD02 : List ReceiptCell :=
  (q11FrequencyRowsRows009.drop 208).take 8

theorem q11FrequencyRowsRows009ChunkD02_check :
    q11ShardCheckWeightedTight (q11ChunkRows q11FrequencyRowsRows009ChunkD02) = true := by
  decide +kernel

theorem q11FrequencyRowsRows009ChunkD02_lower :
    Q11FrequencyCellsLower (q11ChunkCells q11FrequencyRowsRows009ChunkD02) :=
  q11ChunkCells_lower_of_check q11FrequencyRowsRows009ChunkD02_check

def q11FrequencyRowsRows009ChunkD03 : List ReceiptCell :=
  (q11FrequencyRowsRows009.drop 216).take 8

theorem q11FrequencyRowsRows009ChunkD03_check :
    q11ShardCheckWeightedTight (q11ChunkRows q11FrequencyRowsRows009ChunkD03) = true := by
  decide +kernel

theorem q11FrequencyRowsRows009ChunkD03_lower :
    Q11FrequencyCellsLower (q11ChunkCells q11FrequencyRowsRows009ChunkD03) :=
  q11ChunkCells_lower_of_check q11FrequencyRowsRows009ChunkD03_check

def q11FrequencyRowsRows009ChunkD04 : List ReceiptCell :=
  (q11FrequencyRowsRows009.drop 224).take 8

theorem q11FrequencyRowsRows009ChunkD04_check :
    q11ShardCheckWeightedTight (q11ChunkRows q11FrequencyRowsRows009ChunkD04) = true := by
  decide +kernel

theorem q11FrequencyRowsRows009ChunkD04_lower :
    Q11FrequencyCellsLower (q11ChunkCells q11FrequencyRowsRows009ChunkD04) :=
  q11ChunkCells_lower_of_check q11FrequencyRowsRows009ChunkD04_check

def q11FrequencyRowsRows009ChunkD05 : List ReceiptCell :=
  (q11FrequencyRowsRows009.drop 232).take 8

theorem q11FrequencyRowsRows009ChunkD05_check :
    q11ShardCheckWeightedTight (q11ChunkRows q11FrequencyRowsRows009ChunkD05) = true := by
  decide +kernel

theorem q11FrequencyRowsRows009ChunkD05_lower :
    Q11FrequencyCellsLower (q11ChunkCells q11FrequencyRowsRows009ChunkD05) :=
  q11ChunkCells_lower_of_check q11FrequencyRowsRows009ChunkD05_check

def q11FrequencyRowsRows009ChunkD06 : List ReceiptCell :=
  (q11FrequencyRowsRows009.drop 240).take 8

theorem q11FrequencyRowsRows009ChunkD06_check :
    q11ShardCheckWeightedTight (q11ChunkRows q11FrequencyRowsRows009ChunkD06) = true := by
  decide +kernel

theorem q11FrequencyRowsRows009ChunkD06_lower :
    Q11FrequencyCellsLower (q11ChunkCells q11FrequencyRowsRows009ChunkD06) :=
  q11ChunkCells_lower_of_check q11FrequencyRowsRows009ChunkD06_check

def q11FrequencyRowsRows009ChunkD07 : List ReceiptCell :=
  (q11FrequencyRowsRows009.drop 248).take 8

theorem q11FrequencyRowsRows009ChunkD07_check :
    q11ShardCheckWeightedTight (q11ChunkRows q11FrequencyRowsRows009ChunkD07) = true := by
  decide +kernel

theorem q11FrequencyRowsRows009ChunkD07_lower :
    Q11FrequencyCellsLower (q11ChunkCells q11FrequencyRowsRows009ChunkD07) :=
  q11ChunkCells_lower_of_check q11FrequencyRowsRows009ChunkD07_check

end Li2Lean.P0.Q11Data
