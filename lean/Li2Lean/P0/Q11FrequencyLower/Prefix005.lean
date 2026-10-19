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
def q11FrequencyRowsRows005Chunk00 : List ReceiptCell :=
  (q11FrequencyRowsRows005.drop 0).take 8

theorem q11FrequencyRowsRows005Chunk00_check :
    q11ShardCheckWeightedTight (q11ChunkRows q11FrequencyRowsRows005Chunk00) = true := by
  decide +kernel

theorem q11FrequencyRowsRows005Chunk00_lower :
    Q11FrequencyCellsLower (q11ChunkCells q11FrequencyRowsRows005Chunk00) :=
  q11ChunkCells_lower_of_check q11FrequencyRowsRows005Chunk00_check

def q11FrequencyRowsRows005Chunk01 : List ReceiptCell :=
  (q11FrequencyRowsRows005.drop 8).take 8

theorem q11FrequencyRowsRows005Chunk01_check :
    q11ShardCheckWeightedTight (q11ChunkRows q11FrequencyRowsRows005Chunk01) = true := by
  decide +kernel

theorem q11FrequencyRowsRows005Chunk01_lower :
    Q11FrequencyCellsLower (q11ChunkCells q11FrequencyRowsRows005Chunk01) :=
  q11ChunkCells_lower_of_check q11FrequencyRowsRows005Chunk01_check

def q11FrequencyRowsRows005Chunk02 : List ReceiptCell :=
  (q11FrequencyRowsRows005.drop 16).take 8

theorem q11FrequencyRowsRows005Chunk02_check :
    q11ShardCheckWeightedTight (q11ChunkRows q11FrequencyRowsRows005Chunk02) = true := by
  decide +kernel

theorem q11FrequencyRowsRows005Chunk02_lower :
    Q11FrequencyCellsLower (q11ChunkCells q11FrequencyRowsRows005Chunk02) :=
  q11ChunkCells_lower_of_check q11FrequencyRowsRows005Chunk02_check

def q11FrequencyRowsRows005Chunk03 : List ReceiptCell :=
  (q11FrequencyRowsRows005.drop 24).take 8

theorem q11FrequencyRowsRows005Chunk03_check :
    q11ShardCheckWeightedTight (q11ChunkRows q11FrequencyRowsRows005Chunk03) = true := by
  decide +kernel

theorem q11FrequencyRowsRows005Chunk03_lower :
    Q11FrequencyCellsLower (q11ChunkCells q11FrequencyRowsRows005Chunk03) :=
  q11ChunkCells_lower_of_check q11FrequencyRowsRows005Chunk03_check

def q11FrequencyRowsRows005Chunk04 : List ReceiptCell :=
  (q11FrequencyRowsRows005.drop 32).take 8

theorem q11FrequencyRowsRows005Chunk04_check :
    q11ShardCheckWeightedTight (q11ChunkRows q11FrequencyRowsRows005Chunk04) = true := by
  decide +kernel

theorem q11FrequencyRowsRows005Chunk04_lower :
    Q11FrequencyCellsLower (q11ChunkCells q11FrequencyRowsRows005Chunk04) :=
  q11ChunkCells_lower_of_check q11FrequencyRowsRows005Chunk04_check

def q11FrequencyRowsRows005Chunk05 : List ReceiptCell :=
  (q11FrequencyRowsRows005.drop 40).take 8

theorem q11FrequencyRowsRows005Chunk05_check :
    q11ShardCheckWeightedTight (q11ChunkRows q11FrequencyRowsRows005Chunk05) = true := by
  decide +kernel

theorem q11FrequencyRowsRows005Chunk05_lower :
    Q11FrequencyCellsLower (q11ChunkCells q11FrequencyRowsRows005Chunk05) :=
  q11ChunkCells_lower_of_check q11FrequencyRowsRows005Chunk05_check

def q11FrequencyRowsRows005Chunk06 : List ReceiptCell :=
  (q11FrequencyRowsRows005.drop 48).take 8

theorem q11FrequencyRowsRows005Chunk06_check :
    q11ShardCheckWeightedTight (q11ChunkRows q11FrequencyRowsRows005Chunk06) = true := by
  decide +kernel

theorem q11FrequencyRowsRows005Chunk06_lower :
    Q11FrequencyCellsLower (q11ChunkCells q11FrequencyRowsRows005Chunk06) :=
  q11ChunkCells_lower_of_check q11FrequencyRowsRows005Chunk06_check

def q11FrequencyRowsRows005Chunk07 : List ReceiptCell :=
  (q11FrequencyRowsRows005.drop 56).take 8

theorem q11FrequencyRowsRows005Chunk07_check :
    q11ShardCheckWeightedTight (q11ChunkRows q11FrequencyRowsRows005Chunk07) = true := by
  decide +kernel

theorem q11FrequencyRowsRows005Chunk07_lower :
    Q11FrequencyCellsLower (q11ChunkCells q11FrequencyRowsRows005Chunk07) :=
  q11ChunkCells_lower_of_check q11FrequencyRowsRows005Chunk07_check

end Li2Lean.P0.Q11Data
