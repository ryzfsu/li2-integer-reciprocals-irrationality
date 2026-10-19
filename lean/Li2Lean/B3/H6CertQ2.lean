/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
import Li2Lean.B3.V13FieldCellGeneric
import Li2Lean.B3.H6CertBridges
import Li2Lean.V.EnergyCertI.Q2Assembly
import Li2Lean.B3.H6BallSigmaPerQ          -- `q2_field_row_facts`
import Li2Lean.B3.Q2ReferenceNormalizationAdapter

/-! H6 certificate ledger for q = 2, row source `q2ReferenceRows` (data `q2D`).
Same generated template as `H6CertQ5` / `H6CertQ7`; block counts follow
`Li2Lean/V/EnergyCertI/Q2Assembly.lean` (x 49, vlo 70, vhi 71, zneg 53,
zpos 1, arc1 31, arc2 43; energy plan 35 shards).  The S6-dq series is an
explicit input of `energy`, discharged in the leaf by `v13_dq_series_core`.
This module deliberately does not import `Q2CellSoundnessProof` (its public
names clash with `V13RowFacts`). -/
namespace Li2Lean.B3

noncomputable section

open MeasureTheory Set Complex
set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000
open scoped ENNReal ComplexConjugate
open V
open V.EnergyCertI
open V.EnergyCertI.IK

namespace H6CertQ2

def xBlocks : List (List QF) := [
  q2F_x_000_b, q2F_x_001_b, q2F_x_002_b, q2F_x_003_b, q2F_x_004_b,
  q2F_x_005_b, q2F_x_006_b, q2F_x_007_b, q2F_x_008_b, q2F_x_009_b,
  q2F_x_010_b, q2F_x_011_b, q2F_x_012_b, q2F_x_013_b, q2F_x_014_b,
  q2F_x_015_b, q2F_x_016_b, q2F_x_017_b, q2F_x_018_b, q2F_x_019_b,
  q2F_x_020_b, q2F_x_021_b, q2F_x_022_b, q2F_x_023_b, q2F_x_024_b,
  q2F_x_025_b, q2F_x_026_b, q2F_x_027_b, q2F_x_028_b, q2F_x_029_b,
  q2F_x_030_b, q2F_x_031_b, q2F_x_032_b, q2F_x_033_b, q2F_x_034_b,
  q2F_x_035_b, q2F_x_036_b, q2F_x_037_b, q2F_x_038_b, q2F_x_039_b,
  q2F_x_040_b, q2F_x_041_b, q2F_x_042_b, q2F_x_043_b, q2F_x_044_b,
  q2F_x_045_b, q2F_x_046_b, q2F_x_047_b, q2F_x_048_b]

set_option maxHeartbeats 4000000 in
theorem xBlocks_wf : ∀ s ∈ xBlocks, blockWF s = true := by
  unfold xBlocks
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem xBlocks_cells :
    ∀ s ∈ xBlocks, cellsOK (fieldUB q2D 2 vLogRF .x) (kxQ 2) s = true := by
  intro s hs
  simp only [xBlocks, List.mem_cons, List.mem_singleton, List.not_mem_nil,
    or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [q2F_x_000, q2F_x_001, q2F_x_002, q2F_x_003, q2F_x_004, q2F_x_005,
    q2F_x_006, q2F_x_007, q2F_x_008, q2F_x_009, q2F_x_010, q2F_x_011,
    q2F_x_012, q2F_x_013, q2F_x_014, q2F_x_015, q2F_x_016, q2F_x_017,
    q2F_x_018, q2F_x_019, q2F_x_020, q2F_x_021, q2F_x_022, q2F_x_023,
    q2F_x_024, q2F_x_025, q2F_x_026, q2F_x_027, q2F_x_028, q2F_x_029,
    q2F_x_030, q2F_x_031, q2F_x_032, q2F_x_033, q2F_x_034, q2F_x_035,
    q2F_x_036, q2F_x_037, q2F_x_038, q2F_x_039, q2F_x_040, q2F_x_041,
    q2F_x_042, q2F_x_043, q2F_x_044, q2F_x_045, q2F_x_046, q2F_x_047,
    q2F_x_048]

theorem xBlocks_chain : chainOK (1, 250) (1, 1) xBlocks = true := by
  unfold xBlocks
  exact q2F_x_chain

def vloBlocks : List (List QF) := [
  q2F_vlo_000_b, q2F_vlo_001_b, q2F_vlo_002_b, q2F_vlo_003_b, q2F_vlo_004_b,
  q2F_vlo_005_b, q2F_vlo_006_b, q2F_vlo_007_b, q2F_vlo_008_b, q2F_vlo_009_b,
  q2F_vlo_010_b, q2F_vlo_011_b, q2F_vlo_012_b, q2F_vlo_013_b, q2F_vlo_014_b,
  q2F_vlo_015_b, q2F_vlo_016_b, q2F_vlo_017_b, q2F_vlo_018_b, q2F_vlo_019_b,
  q2F_vlo_020_b, q2F_vlo_021_b, q2F_vlo_022_b, q2F_vlo_023_b, q2F_vlo_024_b,
  q2F_vlo_025_b, q2F_vlo_026_b, q2F_vlo_027_b, q2F_vlo_028_b, q2F_vlo_029_b,
  q2F_vlo_030_b, q2F_vlo_031_b, q2F_vlo_032_b, q2F_vlo_033_b, q2F_vlo_034_b,
  q2F_vlo_035_b, q2F_vlo_036_b, q2F_vlo_037_b, q2F_vlo_038_b, q2F_vlo_039_b,
  q2F_vlo_040_b, q2F_vlo_041_b, q2F_vlo_042_b, q2F_vlo_043_b, q2F_vlo_044_b,
  q2F_vlo_045_b, q2F_vlo_046_b, q2F_vlo_047_b, q2F_vlo_048_b, q2F_vlo_049_b,
  q2F_vlo_050_b, q2F_vlo_051_b, q2F_vlo_052_b, q2F_vlo_053_b, q2F_vlo_054_b,
  q2F_vlo_055_b, q2F_vlo_056_b, q2F_vlo_057_b, q2F_vlo_058_b, q2F_vlo_059_b,
  q2F_vlo_060_b, q2F_vlo_061_b, q2F_vlo_062_b, q2F_vlo_063_b, q2F_vlo_064_b,
  q2F_vlo_065_b, q2F_vlo_066_b, q2F_vlo_067_b, q2F_vlo_068_b, q2F_vlo_069_b]

set_option maxHeartbeats 4000000 in
theorem vloBlocks_wf : ∀ s ∈ vloBlocks, blockWF s = true := by
  unfold vloBlocks
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem vloBlocks_cells :
    ∀ s ∈ vloBlocks, cellsOK (fieldUB q2D 2 vLogRF .vlo) (kvQ 2) s = true := by
  intro s hs
  simp only [vloBlocks, List.mem_cons, List.mem_singleton, List.not_mem_nil,
    or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [q2F_vlo_000, q2F_vlo_001, q2F_vlo_002, q2F_vlo_003, q2F_vlo_004, q2F_vlo_005,
    q2F_vlo_006, q2F_vlo_007, q2F_vlo_008, q2F_vlo_009, q2F_vlo_010, q2F_vlo_011,
    q2F_vlo_012, q2F_vlo_013, q2F_vlo_014, q2F_vlo_015, q2F_vlo_016, q2F_vlo_017,
    q2F_vlo_018, q2F_vlo_019, q2F_vlo_020, q2F_vlo_021, q2F_vlo_022, q2F_vlo_023,
    q2F_vlo_024, q2F_vlo_025, q2F_vlo_026, q2F_vlo_027, q2F_vlo_028, q2F_vlo_029,
    q2F_vlo_030, q2F_vlo_031, q2F_vlo_032, q2F_vlo_033, q2F_vlo_034, q2F_vlo_035,
    q2F_vlo_036, q2F_vlo_037, q2F_vlo_038, q2F_vlo_039, q2F_vlo_040, q2F_vlo_041,
    q2F_vlo_042, q2F_vlo_043, q2F_vlo_044, q2F_vlo_045, q2F_vlo_046, q2F_vlo_047,
    q2F_vlo_048, q2F_vlo_049, q2F_vlo_050, q2F_vlo_051, q2F_vlo_052, q2F_vlo_053,
    q2F_vlo_054, q2F_vlo_055, q2F_vlo_056, q2F_vlo_057, q2F_vlo_058, q2F_vlo_059,
    q2F_vlo_060, q2F_vlo_061, q2F_vlo_062, q2F_vlo_063, q2F_vlo_064, q2F_vlo_065,
    q2F_vlo_066, q2F_vlo_067, q2F_vlo_068, q2F_vlo_069]

theorem vloBlocks_chain : chainOK (1, 250) (3, 5) vloBlocks = true := by
  unfold vloBlocks
  exact q2F_vlo_chain

def vhiBlocks : List (List QF) := [
  q2F_vhi_000_b, q2F_vhi_001_b, q2F_vhi_002_b, q2F_vhi_003_b, q2F_vhi_004_b,
  q2F_vhi_005_b, q2F_vhi_006_b, q2F_vhi_007_b, q2F_vhi_008_b, q2F_vhi_009_b,
  q2F_vhi_010_b, q2F_vhi_011_b, q2F_vhi_012_b, q2F_vhi_013_b, q2F_vhi_014_b,
  q2F_vhi_015_b, q2F_vhi_016_b, q2F_vhi_017_b, q2F_vhi_018_b, q2F_vhi_019_b,
  q2F_vhi_020_b, q2F_vhi_021_b, q2F_vhi_022_b, q2F_vhi_023_b, q2F_vhi_024_b,
  q2F_vhi_025_b, q2F_vhi_026_b, q2F_vhi_027_b, q2F_vhi_028_b, q2F_vhi_029_b,
  q2F_vhi_030_b, q2F_vhi_031_b, q2F_vhi_032_b, q2F_vhi_033_b, q2F_vhi_034_b,
  q2F_vhi_035_b, q2F_vhi_036_b, q2F_vhi_037_b, q2F_vhi_038_b, q2F_vhi_039_b,
  q2F_vhi_040_b, q2F_vhi_041_b, q2F_vhi_042_b, q2F_vhi_043_b, q2F_vhi_044_b,
  q2F_vhi_045_b, q2F_vhi_046_b, q2F_vhi_047_b, q2F_vhi_048_b, q2F_vhi_049_b,
  q2F_vhi_050_b, q2F_vhi_051_b, q2F_vhi_052_b, q2F_vhi_053_b, q2F_vhi_054_b,
  q2F_vhi_055_b, q2F_vhi_056_b, q2F_vhi_057_b, q2F_vhi_058_b, q2F_vhi_059_b,
  q2F_vhi_060_b, q2F_vhi_061_b, q2F_vhi_062_b, q2F_vhi_063_b, q2F_vhi_064_b,
  q2F_vhi_065_b, q2F_vhi_066_b, q2F_vhi_067_b, q2F_vhi_068_b, q2F_vhi_069_b,
  q2F_vhi_070_b]

set_option maxHeartbeats 4000000 in
theorem vhiBlocks_wf : ∀ s ∈ vhiBlocks, blockWF s = true := by
  unfold vhiBlocks
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem vhiBlocks_cells :
    ∀ s ∈ vhiBlocks, cellsOK (fieldUB q2D 2 vLogRF .vhi) (kvQ 2) s = true := by
  intro s hs
  simp only [vhiBlocks, List.mem_cons, List.mem_singleton, List.not_mem_nil,
    or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [q2F_vhi_000, q2F_vhi_001, q2F_vhi_002, q2F_vhi_003, q2F_vhi_004, q2F_vhi_005,
    q2F_vhi_006, q2F_vhi_007, q2F_vhi_008, q2F_vhi_009, q2F_vhi_010, q2F_vhi_011,
    q2F_vhi_012, q2F_vhi_013, q2F_vhi_014, q2F_vhi_015, q2F_vhi_016, q2F_vhi_017,
    q2F_vhi_018, q2F_vhi_019, q2F_vhi_020, q2F_vhi_021, q2F_vhi_022, q2F_vhi_023,
    q2F_vhi_024, q2F_vhi_025, q2F_vhi_026, q2F_vhi_027, q2F_vhi_028, q2F_vhi_029,
    q2F_vhi_030, q2F_vhi_031, q2F_vhi_032, q2F_vhi_033, q2F_vhi_034, q2F_vhi_035,
    q2F_vhi_036, q2F_vhi_037, q2F_vhi_038, q2F_vhi_039, q2F_vhi_040, q2F_vhi_041,
    q2F_vhi_042, q2F_vhi_043, q2F_vhi_044, q2F_vhi_045, q2F_vhi_046, q2F_vhi_047,
    q2F_vhi_048, q2F_vhi_049, q2F_vhi_050, q2F_vhi_051, q2F_vhi_052, q2F_vhi_053,
    q2F_vhi_054, q2F_vhi_055, q2F_vhi_056, q2F_vhi_057, q2F_vhi_058, q2F_vhi_059,
    q2F_vhi_060, q2F_vhi_061, q2F_vhi_062, q2F_vhi_063, q2F_vhi_064, q2F_vhi_065,
    q2F_vhi_066, q2F_vhi_067, q2F_vhi_068, q2F_vhi_069, q2F_vhi_070]

theorem vhiBlocks_chain : chainOK (3, 5) (1, 1) vhiBlocks = true := by
  unfold vhiBlocks
  exact q2F_vhi_chain

def znegBlocks : List (List QF) := [
  q2F_zneg_000_b, q2F_zneg_001_b, q2F_zneg_002_b, q2F_zneg_003_b, q2F_zneg_004_b,
  q2F_zneg_005_b, q2F_zneg_006_b, q2F_zneg_007_b, q2F_zneg_008_b, q2F_zneg_009_b,
  q2F_zneg_010_b, q2F_zneg_011_b, q2F_zneg_012_b, q2F_zneg_013_b, q2F_zneg_014_b,
  q2F_zneg_015_b, q2F_zneg_016_b, q2F_zneg_017_b, q2F_zneg_018_b, q2F_zneg_019_b,
  q2F_zneg_020_b, q2F_zneg_021_b, q2F_zneg_022_b, q2F_zneg_023_b, q2F_zneg_024_b,
  q2F_zneg_025_b, q2F_zneg_026_b, q2F_zneg_027_b, q2F_zneg_028_b, q2F_zneg_029_b,
  q2F_zneg_030_b, q2F_zneg_031_b, q2F_zneg_032_b, q2F_zneg_033_b, q2F_zneg_034_b,
  q2F_zneg_035_b, q2F_zneg_036_b, q2F_zneg_037_b, q2F_zneg_038_b, q2F_zneg_039_b,
  q2F_zneg_040_b, q2F_zneg_041_b, q2F_zneg_042_b, q2F_zneg_043_b, q2F_zneg_044_b,
  q2F_zneg_045_b, q2F_zneg_046_b, q2F_zneg_047_b, q2F_zneg_048_b, q2F_zneg_049_b,
  q2F_zneg_050_b, q2F_zneg_051_b, q2F_zneg_052_b]

set_option maxHeartbeats 4000000 in
theorem znegBlocks_wf : ∀ s ∈ znegBlocks, blockWF s = true := by
  unfold znegBlocks
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem znegBlocks_cells :
    ∀ s ∈ znegBlocks, cellsOK (fieldUB q2D 2 vLogRF .zneg) (kzQ 2) s = true := by
  intro s hs
  simp only [znegBlocks, List.mem_cons, List.mem_singleton, List.not_mem_nil,
    or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [q2F_zneg_000, q2F_zneg_001, q2F_zneg_002, q2F_zneg_003, q2F_zneg_004, q2F_zneg_005,
    q2F_zneg_006, q2F_zneg_007, q2F_zneg_008, q2F_zneg_009, q2F_zneg_010, q2F_zneg_011,
    q2F_zneg_012, q2F_zneg_013, q2F_zneg_014, q2F_zneg_015, q2F_zneg_016, q2F_zneg_017,
    q2F_zneg_018, q2F_zneg_019, q2F_zneg_020, q2F_zneg_021, q2F_zneg_022, q2F_zneg_023,
    q2F_zneg_024, q2F_zneg_025, q2F_zneg_026, q2F_zneg_027, q2F_zneg_028, q2F_zneg_029,
    q2F_zneg_030, q2F_zneg_031, q2F_zneg_032, q2F_zneg_033, q2F_zneg_034, q2F_zneg_035,
    q2F_zneg_036, q2F_zneg_037, q2F_zneg_038, q2F_zneg_039, q2F_zneg_040, q2F_zneg_041,
    q2F_zneg_042, q2F_zneg_043, q2F_zneg_044, q2F_zneg_045, q2F_zneg_046, q2F_zneg_047,
    q2F_zneg_048, q2F_zneg_049, q2F_zneg_050, q2F_zneg_051, q2F_zneg_052]

theorem znegBlocks_chain : chainOK (-2, 1) (-3, 5) znegBlocks = true := by
  unfold znegBlocks
  exact q2F_zneg_chain

def zposBlocks : List (List QF) := [
  q2F_zpos_000_b]

set_option maxHeartbeats 4000000 in
theorem zposBlocks_wf : ∀ s ∈ zposBlocks, blockWF s = true := by
  unfold zposBlocks
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem zposBlocks_cells :
    ∀ s ∈ zposBlocks, cellsOK (fieldUB q2D 2 vLogRF .zpos) (kzQ 2) s = true := by
  intro s hs
  simp only [zposBlocks, List.mem_cons, List.mem_singleton, List.not_mem_nil,
    or_false] at hs
  rcases hs with rfl
  exacts [q2F_zpos_000]

theorem zposBlocks_chain : chainOK (3, 5) (1, 1) zposBlocks = true := by
  unfold zposBlocks
  exact q2F_zpos_chain

def arc1Blocks : List (List QF) := [
  q2F_arc1_000_b, q2F_arc1_001_b, q2F_arc1_002_b, q2F_arc1_003_b, q2F_arc1_004_b,
  q2F_arc1_005_b, q2F_arc1_006_b, q2F_arc1_007_b, q2F_arc1_008_b, q2F_arc1_009_b,
  q2F_arc1_010_b, q2F_arc1_011_b, q2F_arc1_012_b, q2F_arc1_013_b, q2F_arc1_014_b,
  q2F_arc1_015_b, q2F_arc1_016_b, q2F_arc1_017_b, q2F_arc1_018_b, q2F_arc1_019_b,
  q2F_arc1_020_b, q2F_arc1_021_b, q2F_arc1_022_b, q2F_arc1_023_b, q2F_arc1_024_b,
  q2F_arc1_025_b, q2F_arc1_026_b, q2F_arc1_027_b, q2F_arc1_028_b, q2F_arc1_029_b,
  q2F_arc1_030_b]

set_option maxHeartbeats 4000000 in
theorem arc1Blocks_wf : ∀ s ∈ arc1Blocks, blockWF s = true := by
  unfold arc1Blocks
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem arc1Blocks_cells :
    ∀ s ∈ arc1Blocks, cellsOK (fieldUB q2D 2 vLogRF .arc1) (kzQ 2) s = true := by
  intro s hs
  simp only [arc1Blocks, List.mem_cons, List.mem_singleton, List.not_mem_nil,
    or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [q2F_arc1_000, q2F_arc1_001, q2F_arc1_002, q2F_arc1_003, q2F_arc1_004, q2F_arc1_005,
    q2F_arc1_006, q2F_arc1_007, q2F_arc1_008, q2F_arc1_009, q2F_arc1_010, q2F_arc1_011,
    q2F_arc1_012, q2F_arc1_013, q2F_arc1_014, q2F_arc1_015, q2F_arc1_016, q2F_arc1_017,
    q2F_arc1_018, q2F_arc1_019, q2F_arc1_020, q2F_arc1_021, q2F_arc1_022, q2F_arc1_023,
    q2F_arc1_024, q2F_arc1_025, q2F_arc1_026, q2F_arc1_027, q2F_arc1_028, q2F_arc1_029,
    q2F_arc1_030]

theorem arc1Blocks_chain : chainOK (0, 1) (1, 1) arc1Blocks = true := by
  unfold arc1Blocks
  exact q2F_arc1_chain

def arc2Blocks : List (List QF) := [
  q2F_arc2_000_b, q2F_arc2_001_b, q2F_arc2_002_b, q2F_arc2_003_b, q2F_arc2_004_b,
  q2F_arc2_005_b, q2F_arc2_006_b, q2F_arc2_007_b, q2F_arc2_008_b, q2F_arc2_009_b,
  q2F_arc2_010_b, q2F_arc2_011_b, q2F_arc2_012_b, q2F_arc2_013_b, q2F_arc2_014_b,
  q2F_arc2_015_b, q2F_arc2_016_b, q2F_arc2_017_b, q2F_arc2_018_b, q2F_arc2_019_b,
  q2F_arc2_020_b, q2F_arc2_021_b, q2F_arc2_022_b, q2F_arc2_023_b, q2F_arc2_024_b,
  q2F_arc2_025_b, q2F_arc2_026_b, q2F_arc2_027_b, q2F_arc2_028_b, q2F_arc2_029_b,
  q2F_arc2_030_b, q2F_arc2_031_b, q2F_arc2_032_b, q2F_arc2_033_b, q2F_arc2_034_b,
  q2F_arc2_035_b, q2F_arc2_036_b, q2F_arc2_037_b, q2F_arc2_038_b, q2F_arc2_039_b,
  q2F_arc2_040_b, q2F_arc2_041_b, q2F_arc2_042_b]

set_option maxHeartbeats 4000000 in
theorem arc2Blocks_wf : ∀ s ∈ arc2Blocks, blockWF s = true := by
  unfold arc2Blocks
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem arc2Blocks_cells :
    ∀ s ∈ arc2Blocks, cellsOK (fieldUB q2D 2 vLogRF .arc2) (kzQ 2) s = true := by
  intro s hs
  simp only [arc2Blocks, List.mem_cons, List.mem_singleton, List.not_mem_nil,
    or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [q2F_arc2_000, q2F_arc2_001, q2F_arc2_002, q2F_arc2_003, q2F_arc2_004, q2F_arc2_005,
    q2F_arc2_006, q2F_arc2_007, q2F_arc2_008, q2F_arc2_009, q2F_arc2_010, q2F_arc2_011,
    q2F_arc2_012, q2F_arc2_013, q2F_arc2_014, q2F_arc2_015, q2F_arc2_016, q2F_arc2_017,
    q2F_arc2_018, q2F_arc2_019, q2F_arc2_020, q2F_arc2_021, q2F_arc2_022, q2F_arc2_023,
    q2F_arc2_024, q2F_arc2_025, q2F_arc2_026, q2F_arc2_027, q2F_arc2_028, q2F_arc2_029,
    q2F_arc2_030, q2F_arc2_031, q2F_arc2_032, q2F_arc2_033, q2F_arc2_034, q2F_arc2_035,
    q2F_arc2_036, q2F_arc2_037, q2F_arc2_038, q2F_arc2_039, q2F_arc2_040, q2F_arc2_041,
    q2F_arc2_042]

theorem arc2Blocks_chain : chainOK (0, 1) (1, 1) arc2Blocks = true := by
  unfold arc2Blocks
  exact q2F_arc2_chain

set_option maxHeartbeats 4000000 in
theorem energy_checks :
    ∀ e ∈ q2EnergyPlan,
      energyShardOK q2D 2 vLogRE e.1 e.2.1 e.2.2.1 e.2.2.2 = true := by
  intro e he
  simp only [q2EnergyPlan, List.mem_cons, List.mem_singleton, List.not_mem_nil,
    or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [q2E_selfX_0_42, q2E_selfV_0_49, q2E_selfZ_0_32, q2E_selfZ_32_63,
    q2E_crossVZ_0_23, q2E_crossVZ_23_46, q2E_crossVZ_46_49, q2E_intPoi_0_4,
    q2E_intPoi_4_8, q2E_intPoi_8_12, q2E_intPoi_12_16, q2E_intPoi_16_20,
    q2E_intPoi_20_24, q2E_intPoi_24_28, q2E_intPoi_28_32, q2E_intPoi_32_36,
    q2E_intPoi_36_40, q2E_intPoi_40_44, q2E_intPoi_44_48, q2E_intPoi_48_52,
    q2E_intPoi_52_56, q2E_intPoi_56_60, q2E_intPoi_60_64, q2E_intPoi_64_68,
    q2E_intPoi_68_72, q2E_intPoi_72_75, q2E_pp_0_10, q2E_pp_10_21,
    q2E_pp_21_33, q2E_pp_33_46, q2E_pp_46_61, q2E_pp_61_79,
    q2E_pp_79_105, q2E_pp_105_149, q2E_dq_0_1]

theorem dq_plan :
    ∀ e ∈ q2EnergyPlan, e.1 = EKind.dq → e.2.1 = 0 ∧ e.2.2.1 = 1 := by
  unfold q2EnergyPlan
  decide +kernel

theorem mx_den_pos : 0 < q2D.mx.2 := by decide +kernel
theorem mv_den_pos : 0 < q2D.mv.2 := by decide +kernel
theorem pm_den_pos : 0 < q2D.pm.2 := by decide +kernel

variable {hq : SignedVBaseRange 2}

/-- Five ledger witnesses (`CellSoundnessOn`) for any sound `lr`
(the leaf uses `lr = vLogRE`). -/
theorem cells (N : V13MeasureNormalization hq (v13RefRaw q2ReferenceRows))
    {lr : IV} (hlr : IV.mem lr (Real.log (3 / 5 : ℝ))) :
    V13FiveCells q2ReferenceRows N lr :=
  v13_five_cells q2ReferenceRows q2_field_row_facts N hlr

/-- `C.x_field` from the finite x chain and the x endpoint disk. -/
theorem x_field (N : V13MeasureNormalization hq (v13RefRaw q2ReferenceRows))
    (hend : ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ ≤ 1 / 250 →
      V.signedVFullFieldX (v13RefMeasure q2ReferenceRows N) w ≤ (vEx 2 : ℝ)) :
    ∀ t : ℝ, t ∈ Set.Ioc (0 : ℝ) 1 →
      V.signedVFullFieldX (v13RefMeasure q2ReferenceRows N) (t : ℂ) < (vKx 2 : ℝ) :=
  v13_x_field_of_blocks q2ReferenceRows q2_field_row_facts N
    xBlocks_wf xBlocks_cells xBlocks_chain hend

/-- `C.v_field` from the two finite v chains and the v endpoint disk. -/
theorem v_field (N : V13MeasureNormalization hq (v13RefRaw q2ReferenceRows))
    (hend : ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ ≤ 1 / 250 →
      V.signedVFullFieldV (v13RefMeasure q2ReferenceRows N) w ≤ (vEv 2 : ℝ)) :
    ∀ t : ℝ, t ∈ Set.Ioc (0 : ℝ) 1 →
      V.signedVFullFieldV (v13RefMeasure q2ReferenceRows N) (t : ℂ) < (vKv 2 : ℝ) :=
  v13_v_field_of_blocks q2ReferenceRows q2_field_row_facts N
    vloBlocks_wf vloBlocks_cells vloBlocks_chain
    vhiBlocks_wf vhiBlocks_cells vhiBlocks_chain hend

/-- `C.z_field` from the zneg/zpos chains and the two arc chains. -/
theorem z_field (N : V13MeasureNormalization hq (v13RefRaw q2ReferenceRows)) :
    ∀ w ∈ V.vContourTrace 2,
      V.signedVFullFieldZ (v13RefMeasure q2ReferenceRows N) w < (vKz 2 : ℝ) :=
  v13_z_field_of_blocks (q := 2) (hq := hq) q2ReferenceRows q2_field_row_facts N
    znegBlocks_wf znegBlocks_cells (by exact znegBlocks_chain)
    zposBlocks_wf zposBlocks_cells zposBlocks_chain
    arc1Blocks_wf arc1Blocks_cells arc1Blocks_chain
    arc2Blocks_wf arc2Blocks_cells arc2Blocks_chain

/-- Endpoint evaluator checks, split out of `q2Endpoint_check`. -/
theorem ex_check : hiLe (exUB fieldMode q2D 2) (exQ 2) = true := by
  have h := q2Endpoint_check
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1

theorem ev_check : hiLe (evUB fieldMode q2D 2) (evQ 2) = true := by
  have h := q2Endpoint_check
  simp only [Bool.and_eq_true] at h
  exact h.1.1.2

/-- Generic x endpoint disk at q = 2 (alternative on master:
`q2ReferenceMeasure_x_endpoint_disk` in `Q2EndpointDisk`, not used here). -/
theorem x_endpoint_disk (hrows : V13DecodedRowBounds 2 q2ReferenceRows)
    (N : V13MeasureNormalization hq (v13RefRaw q2ReferenceRows)) :
    ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ ≤ 1 / 250 →
      V.signedVFullFieldX (v13RefMeasure q2ReferenceRows N) w ≤ (vEx 2 : ℝ) :=
  fun w hw0 hw => v13_x_endpoint_disk q2ReferenceRows hrows N
    (v13_x_endpoint_certificate q2ReferenceRows q2_field_row_facts hrows N)
    ex_check (val_exQ_eq_vEx hq) w hw0 hw

/-- Energy shard ledger at `lr = vLogRE`; `hseries` is the S6-dq identity. -/
theorem energy (N : V13MeasureNormalization hq (v13RefRaw q2ReferenceRows))
    (hseries : V13DqSeries q2ReferenceRows N) :
    EnergyShardSoundnessFact q2ReferenceRows.data 2 vLogRE
      (planOf q2ReferenceRows.data 2) (vEnergyTerm 2 q2ReferenceRows.data) := by
  rw [planOf_q2]
  exact v13_energy_shard_fact q2ReferenceRows q2_field_row_facts N
    mx_den_pos mv_den_pos h6_vLogRE_sound
    q2EnergyPlan energy_checks dq_plan hseries

theorem poisson_mass_real :
    (v13PoissonMeasure q2ReferenceRows.data.full).real Set.univ =
      IK.val q2ReferenceRows.data.pm := by
  -- same normalisation as `Q2VEndpointDisk.lean:1292` (`hpmval`)
  have hpm : IK.val q2D.pm = (66150027 / 100000000 : ℝ) := by
    norm_num [q2D, mkIData, q2PoissonPrefix,
      Li2Lean.V.Q2Certificate.poissonFull,
      Li2Lean.V.Q2Certificate.conjugatePoisson,
      Li2Lean.V.Q2Certificate.decodePoisson,
      Li2Lean.V.Q2Certificate.decodePoissonAux,
      Li2Lean.V.EnergyCertI.prow, U, IK.val, Li2Lean.V.EnergyCertI.sumU]
  have hmass : (v13PoissonMeasure q2D.full).real Set.univ =
      (66150027 / 100000000 : ℝ) := by
    simpa [Measure.real_def] using congrArg ENNReal.toReal q2ReferenceRaw_poisson_mass
  change (v13PoissonMeasure q2D.full).real Set.univ = IK.val q2D.pm
  rw [hmass, hpm]

/-- Generic v endpoint disk instantiated at q = 2. -/
theorem v_endpoint_disk (hrows : V13DecodedRowBounds 2 q2ReferenceRows)
    (N : V13MeasureNormalization hq (v13RefRaw q2ReferenceRows)) :
    ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ ≤ 1 / 250 →
      V.signedVFullFieldV (v13RefMeasure q2ReferenceRows N) w ≤ (vEv 2 : ℝ) :=
  fun w hw0 hw => v13_v_endpoint_disk q2ReferenceRows hrows N
    (v13_v_endpoint_certificate q2ReferenceRows q2_field_row_facts hrows N
      pm_den_pos poisson_mass_real)
    ev_check (val_evQ_eq_vEv hq) w hw0 hw

end H6CertQ2

end

end Li2Lean.B3
