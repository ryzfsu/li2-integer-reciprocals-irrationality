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
def q11FrequencyRowsRows002ChunkB00 : List ReceiptCell :=
  (q11FrequencyRowsRows002.drop 64).take 8

theorem q11FrequencyRowsRows002ChunkB00_check :
    q11ShardCheckWeightedTight (q11ChunkRows q11FrequencyRowsRows002ChunkB00) = true := by
  decide +kernel

theorem q11FrequencyRowsRows002ChunkB00_lower :
    Q11FrequencyCellsLower (q11ChunkCells q11FrequencyRowsRows002ChunkB00) :=
  q11ChunkCells_lower_of_check q11FrequencyRowsRows002ChunkB00_check

def q11FrequencyRowsRows002ChunkB01 : List ReceiptCell :=
  (q11FrequencyRowsRows002.drop 72).take 8

theorem q11FrequencyRowsRows002ChunkB01_check :
    q11ShardCheckWeightedTight (q11ChunkRows q11FrequencyRowsRows002ChunkB01) = true := by
  decide +kernel

theorem q11FrequencyRowsRows002ChunkB01_lower :
    Q11FrequencyCellsLower (q11ChunkCells q11FrequencyRowsRows002ChunkB01) :=
  q11ChunkCells_lower_of_check q11FrequencyRowsRows002ChunkB01_check

def q11FrequencyRowsRows002ChunkB02 : List ReceiptCell :=
  (q11FrequencyRowsRows002.drop 80).take 8

theorem q11FrequencyRowsRows002ChunkB02_check :
    q11ShardCheckWeightedTight (q11ChunkRows q11FrequencyRowsRows002ChunkB02) = true := by
  decide +kernel

theorem q11FrequencyRowsRows002ChunkB02_lower :
    Q11FrequencyCellsLower (q11ChunkCells q11FrequencyRowsRows002ChunkB02) :=
  q11ChunkCells_lower_of_check q11FrequencyRowsRows002ChunkB02_check

def q11FrequencyRowsRows002ChunkB03 : List ReceiptCell :=
  (q11FrequencyRowsRows002.drop 88).take 8

theorem q11FrequencyRowsRows002ChunkB03_check :
    q11ShardCheckWeightedTight (q11ChunkRows q11FrequencyRowsRows002ChunkB03) = true := by
  decide +kernel

theorem q11FrequencyRowsRows002ChunkB03_lower :
    Q11FrequencyCellsLower (q11ChunkCells q11FrequencyRowsRows002ChunkB03) :=
  q11ChunkCells_lower_of_check q11FrequencyRowsRows002ChunkB03_check

def q11FrequencyRowsRows002ChunkB04 : List ReceiptCell :=
  (q11FrequencyRowsRows002.drop 96).take 8

theorem q11FrequencyRowsRows002ChunkB04_check :
    q11ShardCheckWeightedTight (q11ChunkRows q11FrequencyRowsRows002ChunkB04) = true := by
  decide +kernel

theorem q11FrequencyRowsRows002ChunkB04_lower :
    Q11FrequencyCellsLower (q11ChunkCells q11FrequencyRowsRows002ChunkB04) :=
  q11ChunkCells_lower_of_check q11FrequencyRowsRows002ChunkB04_check

def q11FrequencyRowsRows002ChunkB05 : List ReceiptCell :=
  (q11FrequencyRowsRows002.drop 104).take 8

theorem q11FrequencyRowsRows002ChunkB05_check :
    q11ShardCheckWeightedTight (q11ChunkRows q11FrequencyRowsRows002ChunkB05) = true := by
  decide +kernel

theorem q11FrequencyRowsRows002ChunkB05_lower :
    Q11FrequencyCellsLower (q11ChunkCells q11FrequencyRowsRows002ChunkB05) :=
  q11ChunkCells_lower_of_check q11FrequencyRowsRows002ChunkB05_check

def q11FrequencyRowsRows002ChunkB06 : List ReceiptCell :=
  (q11FrequencyRowsRows002.drop 112).take 8

theorem q11FrequencyRowsRows002ChunkB06_check :
    q11ShardCheckWeightedTight (q11ChunkRows q11FrequencyRowsRows002ChunkB06) = true := by
  decide +kernel

theorem q11FrequencyRowsRows002ChunkB06_lower :
    Q11FrequencyCellsLower (q11ChunkCells q11FrequencyRowsRows002ChunkB06) :=
  q11ChunkCells_lower_of_check q11FrequencyRowsRows002ChunkB06_check

def q11FrequencyRowsRows002ChunkB07 : List ReceiptCell :=
  (q11FrequencyRowsRows002.drop 120).take 8

theorem q11FrequencyRowsRows002ChunkB07_check :
    q11ShardCheckWeightedTight (q11ChunkRows q11FrequencyRowsRows002ChunkB07) = true := by
  decide +kernel

theorem q11FrequencyRowsRows002ChunkB07_lower :
    Q11FrequencyCellsLower (q11ChunkCells q11FrequencyRowsRows002ChunkB07) :=
  q11ChunkCells_lower_of_check q11FrequencyRowsRows002ChunkB07_check

end Li2Lean.P0.Q11Data
