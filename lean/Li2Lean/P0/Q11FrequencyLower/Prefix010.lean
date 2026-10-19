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
def q11FrequencyRowsRows010Chunk00 : List ReceiptCell :=
  (q11FrequencyRowsRows010.drop 0).take 8

theorem q11FrequencyRowsRows010Chunk00_check :
    q11ShardCheckWeightedTight (q11ChunkRows q11FrequencyRowsRows010Chunk00) = true := by
  decide +kernel

theorem q11FrequencyRowsRows010Chunk00_lower :
    Q11FrequencyCellsLower (q11ChunkCells q11FrequencyRowsRows010Chunk00) :=
  q11ChunkCells_lower_of_check q11FrequencyRowsRows010Chunk00_check

def q11FrequencyRowsRows010Chunk01 : List ReceiptCell :=
  (q11FrequencyRowsRows010.drop 8).take 8

theorem q11FrequencyRowsRows010Chunk01_check :
    q11ShardCheckWeightedTight (q11ChunkRows q11FrequencyRowsRows010Chunk01) = true := by
  decide +kernel

theorem q11FrequencyRowsRows010Chunk01_lower :
    Q11FrequencyCellsLower (q11ChunkCells q11FrequencyRowsRows010Chunk01) :=
  q11ChunkCells_lower_of_check q11FrequencyRowsRows010Chunk01_check

def q11FrequencyRowsRows010Chunk02 : List ReceiptCell :=
  (q11FrequencyRowsRows010.drop 16).take 8

theorem q11FrequencyRowsRows010Chunk02_check :
    q11ShardCheckWeightedTight (q11ChunkRows q11FrequencyRowsRows010Chunk02) = true := by
  decide +kernel

theorem q11FrequencyRowsRows010Chunk02_lower :
    Q11FrequencyCellsLower (q11ChunkCells q11FrequencyRowsRows010Chunk02) :=
  q11ChunkCells_lower_of_check q11FrequencyRowsRows010Chunk02_check

def q11FrequencyRowsRows010Chunk03 : List ReceiptCell :=
  (q11FrequencyRowsRows010.drop 24).take 8

theorem q11FrequencyRowsRows010Chunk03_check :
    q11ShardCheckWeightedTight (q11ChunkRows q11FrequencyRowsRows010Chunk03) = true := by
  decide +kernel

theorem q11FrequencyRowsRows010Chunk03_lower :
    Q11FrequencyCellsLower (q11ChunkCells q11FrequencyRowsRows010Chunk03) :=
  q11ChunkCells_lower_of_check q11FrequencyRowsRows010Chunk03_check

def q11FrequencyRowsRows010Chunk04 : List ReceiptCell :=
  (q11FrequencyRowsRows010.drop 32).take 8

theorem q11FrequencyRowsRows010Chunk04_check :
    q11ShardCheckWeightedTight (q11ChunkRows q11FrequencyRowsRows010Chunk04) = true := by
  decide +kernel

theorem q11FrequencyRowsRows010Chunk04_lower :
    Q11FrequencyCellsLower (q11ChunkCells q11FrequencyRowsRows010Chunk04) :=
  q11ChunkCells_lower_of_check q11FrequencyRowsRows010Chunk04_check

def q11FrequencyRowsRows010Chunk05 : List ReceiptCell :=
  (q11FrequencyRowsRows010.drop 40).take 8

theorem q11FrequencyRowsRows010Chunk05_check :
    q11ShardCheckWeightedTight (q11ChunkRows q11FrequencyRowsRows010Chunk05) = true := by
  decide +kernel

theorem q11FrequencyRowsRows010Chunk05_lower :
    Q11FrequencyCellsLower (q11ChunkCells q11FrequencyRowsRows010Chunk05) :=
  q11ChunkCells_lower_of_check q11FrequencyRowsRows010Chunk05_check

def q11FrequencyRowsRows010Chunk06 : List ReceiptCell :=
  (q11FrequencyRowsRows010.drop 48).take 8

theorem q11FrequencyRowsRows010Chunk06_check :
    q11ShardCheckWeightedTight (q11ChunkRows q11FrequencyRowsRows010Chunk06) = true := by
  decide +kernel

theorem q11FrequencyRowsRows010Chunk06_lower :
    Q11FrequencyCellsLower (q11ChunkCells q11FrequencyRowsRows010Chunk06) :=
  q11ChunkCells_lower_of_check q11FrequencyRowsRows010Chunk06_check

def q11FrequencyRowsRows010Chunk07 : List ReceiptCell :=
  (q11FrequencyRowsRows010.drop 56).take 8

theorem q11FrequencyRowsRows010Chunk07_check :
    q11ShardCheckWeightedTight (q11ChunkRows q11FrequencyRowsRows010Chunk07) = true := by
  decide +kernel

theorem q11FrequencyRowsRows010Chunk07_lower :
    Q11FrequencyCellsLower (q11ChunkCells q11FrequencyRowsRows010Chunk07) :=
  q11ChunkCells_lower_of_check q11FrequencyRowsRows010Chunk07_check

end Li2Lean.P0.Q11Data
