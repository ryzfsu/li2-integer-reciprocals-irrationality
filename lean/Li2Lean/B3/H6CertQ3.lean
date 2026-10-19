/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
/-
  H6 q = 3 certificate ledger.

  This file is the q = 3 data instance of the generic H6 certificate
  bridges.  All finite block and shard witnesses are taken from the v13
  generated q3 tables.  The q3 Poisson mass is computed from the generic
  decoded-row sum and q3's finite Poisson table, rather than assumed as an
  external premise.
-/

import Li2Lean.B3.V13FieldCellGeneric
import Li2Lean.B3.H6CertBridges
import Li2Lean.B3.H6Q3FieldRowFacts
import Li2Lean.B3.Q3ReferenceRowBounds
import Li2Lean.V.EnergyCertI.Q3Assembly

namespace Li2Lean.B3

noncomputable section

open MeasureTheory Set Complex
open scoped ENNReal ComplexConjugate
open V
open V.EnergyCertI
open V.EnergyCertI.IK

namespace H6CertQ3

def xBlocks : List (List QF) := [
  q3F_x_000_b, q3F_x_001_b, q3F_x_002_b, q3F_x_003_b, q3F_x_004_b, q3F_x_005_b,
  q3F_x_006_b, q3F_x_007_b, q3F_x_008_b, q3F_x_009_b, q3F_x_010_b, q3F_x_011_b,
  q3F_x_012_b, q3F_x_013_b, q3F_x_014_b, q3F_x_015_b, q3F_x_016_b, q3F_x_017_b,
  q3F_x_018_b, q3F_x_019_b, q3F_x_020_b, q3F_x_021_b, q3F_x_022_b, q3F_x_023_b,
  q3F_x_024_b, q3F_x_025_b, q3F_x_026_b, q3F_x_027_b, q3F_x_028_b, q3F_x_029_b,
  q3F_x_030_b, q3F_x_031_b, q3F_x_032_b, q3F_x_033_b, q3F_x_034_b, q3F_x_035_b,
  q3F_x_036_b, q3F_x_037_b, q3F_x_038_b, q3F_x_039_b, q3F_x_040_b, q3F_x_041_b,
  q3F_x_042_b, q3F_x_043_b, q3F_x_044_b, q3F_x_045_b]

set_option maxHeartbeats 4000000 in
theorem xBlocks_wf : ∀ s ∈ xBlocks, blockWF s = true := by
  -- Verified certificate computation.
  -- rcases pattern of `Q2VFieldGlobal.q2_vlo_blocks_wf`.
  unfold xBlocks
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem xBlocks_cells :
    ∀ s ∈ xBlocks, cellsOK (fieldUB q3D 3 vLogRF .x) (kxQ 3) s = true := by
  intro s hs
  simp only [xBlocks, List.mem_cons, List.mem_singleton, List.not_mem_nil,
    or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
  exacts [q3F_x_000, q3F_x_001, q3F_x_002, q3F_x_003, q3F_x_004, q3F_x_005, q3F_x_006,
    q3F_x_007, q3F_x_008, q3F_x_009, q3F_x_010, q3F_x_011, q3F_x_012, q3F_x_013,
    q3F_x_014, q3F_x_015, q3F_x_016, q3F_x_017, q3F_x_018, q3F_x_019, q3F_x_020,
    q3F_x_021, q3F_x_022, q3F_x_023, q3F_x_024, q3F_x_025, q3F_x_026, q3F_x_027,
    q3F_x_028, q3F_x_029, q3F_x_030, q3F_x_031, q3F_x_032, q3F_x_033, q3F_x_034,
    q3F_x_035, q3F_x_036, q3F_x_037, q3F_x_038, q3F_x_039, q3F_x_040, q3F_x_041,
    q3F_x_042, q3F_x_043, q3F_x_044, q3F_x_045]

theorem xBlocks_chain : chainOK (1, 250) (1, 1) xBlocks = true := by
  unfold xBlocks
  exact q3F_x_chain

def vloBlocks : List (List QF) := [
  q3F_vlo_000_b, q3F_vlo_001_b, q3F_vlo_002_b, q3F_vlo_003_b, q3F_vlo_004_b,
  q3F_vlo_005_b, q3F_vlo_006_b, q3F_vlo_007_b, q3F_vlo_008_b, q3F_vlo_009_b,
  q3F_vlo_010_b, q3F_vlo_011_b, q3F_vlo_012_b, q3F_vlo_013_b, q3F_vlo_014_b,
  q3F_vlo_015_b, q3F_vlo_016_b, q3F_vlo_017_b, q3F_vlo_018_b, q3F_vlo_019_b,
  q3F_vlo_020_b, q3F_vlo_021_b, q3F_vlo_022_b, q3F_vlo_023_b, q3F_vlo_024_b,
  q3F_vlo_025_b, q3F_vlo_026_b, q3F_vlo_027_b, q3F_vlo_028_b, q3F_vlo_029_b,
  q3F_vlo_030_b, q3F_vlo_031_b, q3F_vlo_032_b, q3F_vlo_033_b, q3F_vlo_034_b,
  q3F_vlo_035_b, q3F_vlo_036_b, q3F_vlo_037_b, q3F_vlo_038_b, q3F_vlo_039_b,
  q3F_vlo_040_b, q3F_vlo_041_b, q3F_vlo_042_b, q3F_vlo_043_b, q3F_vlo_044_b,
  q3F_vlo_045_b, q3F_vlo_046_b, q3F_vlo_047_b, q3F_vlo_048_b, q3F_vlo_049_b,
  q3F_vlo_050_b, q3F_vlo_051_b, q3F_vlo_052_b, q3F_vlo_053_b, q3F_vlo_054_b,
  q3F_vlo_055_b, q3F_vlo_056_b, q3F_vlo_057_b, q3F_vlo_058_b, q3F_vlo_059_b,
  q3F_vlo_060_b, q3F_vlo_061_b, q3F_vlo_062_b, q3F_vlo_063_b, q3F_vlo_064_b,
  q3F_vlo_065_b]

set_option maxHeartbeats 4000000 in
theorem vloBlocks_wf : ∀ s ∈ vloBlocks, blockWF s = true := by
  -- Verified certificate computation.
  -- rcases pattern of `Q2VFieldGlobal.q2_vlo_blocks_wf`.
  unfold vloBlocks
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem vloBlocks_cells :
    ∀ s ∈ vloBlocks, cellsOK (fieldUB q3D 3 vLogRF .vlo) (kvQ 3) s = true := by
  intro s hs
  simp only [vloBlocks, List.mem_cons, List.mem_singleton, List.not_mem_nil,
    or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
  exacts [q3F_vlo_000, q3F_vlo_001, q3F_vlo_002, q3F_vlo_003, q3F_vlo_004, q3F_vlo_005,
    q3F_vlo_006, q3F_vlo_007, q3F_vlo_008, q3F_vlo_009, q3F_vlo_010, q3F_vlo_011,
    q3F_vlo_012, q3F_vlo_013, q3F_vlo_014, q3F_vlo_015, q3F_vlo_016, q3F_vlo_017,
    q3F_vlo_018, q3F_vlo_019, q3F_vlo_020, q3F_vlo_021, q3F_vlo_022, q3F_vlo_023,
    q3F_vlo_024, q3F_vlo_025, q3F_vlo_026, q3F_vlo_027, q3F_vlo_028, q3F_vlo_029,
    q3F_vlo_030, q3F_vlo_031, q3F_vlo_032, q3F_vlo_033, q3F_vlo_034, q3F_vlo_035,
    q3F_vlo_036, q3F_vlo_037, q3F_vlo_038, q3F_vlo_039, q3F_vlo_040, q3F_vlo_041,
    q3F_vlo_042, q3F_vlo_043, q3F_vlo_044, q3F_vlo_045, q3F_vlo_046, q3F_vlo_047,
    q3F_vlo_048, q3F_vlo_049, q3F_vlo_050, q3F_vlo_051, q3F_vlo_052, q3F_vlo_053,
    q3F_vlo_054, q3F_vlo_055, q3F_vlo_056, q3F_vlo_057, q3F_vlo_058, q3F_vlo_059,
    q3F_vlo_060, q3F_vlo_061, q3F_vlo_062, q3F_vlo_063, q3F_vlo_064, q3F_vlo_065]

theorem vloBlocks_chain : chainOK (1, 250) (3, 5) vloBlocks = true := by
  unfold vloBlocks
  exact q3F_vlo_chain

def vhiBlocks : List (List QF) := [
  q3F_vhi_000_b, q3F_vhi_001_b, q3F_vhi_002_b, q3F_vhi_003_b, q3F_vhi_004_b,
  q3F_vhi_005_b, q3F_vhi_006_b, q3F_vhi_007_b, q3F_vhi_008_b, q3F_vhi_009_b,
  q3F_vhi_010_b, q3F_vhi_011_b, q3F_vhi_012_b, q3F_vhi_013_b, q3F_vhi_014_b,
  q3F_vhi_015_b, q3F_vhi_016_b, q3F_vhi_017_b, q3F_vhi_018_b, q3F_vhi_019_b,
  q3F_vhi_020_b, q3F_vhi_021_b, q3F_vhi_022_b, q3F_vhi_023_b, q3F_vhi_024_b,
  q3F_vhi_025_b, q3F_vhi_026_b, q3F_vhi_027_b, q3F_vhi_028_b, q3F_vhi_029_b,
  q3F_vhi_030_b, q3F_vhi_031_b, q3F_vhi_032_b, q3F_vhi_033_b, q3F_vhi_034_b,
  q3F_vhi_035_b, q3F_vhi_036_b, q3F_vhi_037_b, q3F_vhi_038_b, q3F_vhi_039_b,
  q3F_vhi_040_b, q3F_vhi_041_b, q3F_vhi_042_b, q3F_vhi_043_b, q3F_vhi_044_b,
  q3F_vhi_045_b, q3F_vhi_046_b, q3F_vhi_047_b, q3F_vhi_048_b, q3F_vhi_049_b,
  q3F_vhi_050_b, q3F_vhi_051_b, q3F_vhi_052_b, q3F_vhi_053_b, q3F_vhi_054_b,
  q3F_vhi_055_b, q3F_vhi_056_b, q3F_vhi_057_b, q3F_vhi_058_b, q3F_vhi_059_b,
  q3F_vhi_060_b, q3F_vhi_061_b, q3F_vhi_062_b, q3F_vhi_063_b, q3F_vhi_064_b,
  q3F_vhi_065_b, q3F_vhi_066_b, q3F_vhi_067_b]

set_option maxHeartbeats 4000000 in
theorem vhiBlocks_wf : ∀ s ∈ vhiBlocks, blockWF s = true := by
  -- Verified certificate computation.
  -- rcases pattern of `Q2VFieldGlobal.q2_vlo_blocks_wf`.
  unfold vhiBlocks
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem vhiBlocks_cells :
    ∀ s ∈ vhiBlocks, cellsOK (fieldUB q3D 3 vLogRF .vhi) (kvQ 3) s = true := by
  intro s hs
  simp only [vhiBlocks, List.mem_cons, List.mem_singleton, List.not_mem_nil,
    or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
  exacts [q3F_vhi_000, q3F_vhi_001, q3F_vhi_002, q3F_vhi_003, q3F_vhi_004, q3F_vhi_005,
    q3F_vhi_006, q3F_vhi_007, q3F_vhi_008, q3F_vhi_009, q3F_vhi_010, q3F_vhi_011,
    q3F_vhi_012, q3F_vhi_013, q3F_vhi_014, q3F_vhi_015, q3F_vhi_016, q3F_vhi_017,
    q3F_vhi_018, q3F_vhi_019, q3F_vhi_020, q3F_vhi_021, q3F_vhi_022, q3F_vhi_023,
    q3F_vhi_024, q3F_vhi_025, q3F_vhi_026, q3F_vhi_027, q3F_vhi_028, q3F_vhi_029,
    q3F_vhi_030, q3F_vhi_031, q3F_vhi_032, q3F_vhi_033, q3F_vhi_034, q3F_vhi_035,
    q3F_vhi_036, q3F_vhi_037, q3F_vhi_038, q3F_vhi_039, q3F_vhi_040, q3F_vhi_041,
    q3F_vhi_042, q3F_vhi_043, q3F_vhi_044, q3F_vhi_045, q3F_vhi_046, q3F_vhi_047,
    q3F_vhi_048, q3F_vhi_049, q3F_vhi_050, q3F_vhi_051, q3F_vhi_052, q3F_vhi_053,
    q3F_vhi_054, q3F_vhi_055, q3F_vhi_056, q3F_vhi_057, q3F_vhi_058, q3F_vhi_059,
    q3F_vhi_060, q3F_vhi_061, q3F_vhi_062, q3F_vhi_063, q3F_vhi_064, q3F_vhi_065,
    q3F_vhi_066, q3F_vhi_067]

theorem vhiBlocks_chain : chainOK (3, 5) (1, 1) vhiBlocks = true := by
  unfold vhiBlocks
  exact q3F_vhi_chain

def znegBlocks : List (List QF) := [
  q3F_zneg_000_b, q3F_zneg_001_b, q3F_zneg_002_b, q3F_zneg_003_b, q3F_zneg_004_b,
  q3F_zneg_005_b, q3F_zneg_006_b, q3F_zneg_007_b, q3F_zneg_008_b, q3F_zneg_009_b,
  q3F_zneg_010_b, q3F_zneg_011_b, q3F_zneg_012_b, q3F_zneg_013_b, q3F_zneg_014_b,
  q3F_zneg_015_b, q3F_zneg_016_b, q3F_zneg_017_b, q3F_zneg_018_b, q3F_zneg_019_b,
  q3F_zneg_020_b, q3F_zneg_021_b, q3F_zneg_022_b, q3F_zneg_023_b, q3F_zneg_024_b,
  q3F_zneg_025_b, q3F_zneg_026_b, q3F_zneg_027_b, q3F_zneg_028_b, q3F_zneg_029_b,
  q3F_zneg_030_b, q3F_zneg_031_b, q3F_zneg_032_b, q3F_zneg_033_b, q3F_zneg_034_b,
  q3F_zneg_035_b, q3F_zneg_036_b, q3F_zneg_037_b, q3F_zneg_038_b, q3F_zneg_039_b,
  q3F_zneg_040_b, q3F_zneg_041_b, q3F_zneg_042_b, q3F_zneg_043_b, q3F_zneg_044_b,
  q3F_zneg_045_b, q3F_zneg_046_b, q3F_zneg_047_b, q3F_zneg_048_b, q3F_zneg_049_b,
  q3F_zneg_050_b, q3F_zneg_051_b, q3F_zneg_052_b, q3F_zneg_053_b, q3F_zneg_054_b,
  q3F_zneg_055_b, q3F_zneg_056_b, q3F_zneg_057_b, q3F_zneg_058_b, q3F_zneg_059_b,
  q3F_zneg_060_b, q3F_zneg_061_b]

set_option maxHeartbeats 4000000 in
theorem znegBlocks_wf : ∀ s ∈ znegBlocks, blockWF s = true := by
  -- Verified certificate computation.
  -- rcases pattern of `Q2VFieldGlobal.q2_vlo_blocks_wf`.
  unfold znegBlocks
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem znegBlocks_cells :
    ∀ s ∈ znegBlocks, cellsOK (fieldUB q3D 3 vLogRF .zneg) (kzQ 3) s = true := by
  intro s hs
  simp only [znegBlocks, List.mem_cons, List.mem_singleton, List.not_mem_nil,
    or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
  exacts [q3F_zneg_000, q3F_zneg_001, q3F_zneg_002, q3F_zneg_003, q3F_zneg_004, q3F_zneg_005,
    q3F_zneg_006, q3F_zneg_007, q3F_zneg_008, q3F_zneg_009, q3F_zneg_010, q3F_zneg_011,
    q3F_zneg_012, q3F_zneg_013, q3F_zneg_014, q3F_zneg_015, q3F_zneg_016, q3F_zneg_017,
    q3F_zneg_018, q3F_zneg_019, q3F_zneg_020, q3F_zneg_021, q3F_zneg_022, q3F_zneg_023,
    q3F_zneg_024, q3F_zneg_025, q3F_zneg_026, q3F_zneg_027, q3F_zneg_028, q3F_zneg_029,
    q3F_zneg_030, q3F_zneg_031, q3F_zneg_032, q3F_zneg_033, q3F_zneg_034, q3F_zneg_035,
    q3F_zneg_036, q3F_zneg_037, q3F_zneg_038, q3F_zneg_039, q3F_zneg_040, q3F_zneg_041,
    q3F_zneg_042, q3F_zneg_043, q3F_zneg_044, q3F_zneg_045, q3F_zneg_046, q3F_zneg_047,
    q3F_zneg_048, q3F_zneg_049, q3F_zneg_050, q3F_zneg_051, q3F_zneg_052, q3F_zneg_053,
    q3F_zneg_054, q3F_zneg_055, q3F_zneg_056, q3F_zneg_057, q3F_zneg_058, q3F_zneg_059,
    q3F_zneg_060, q3F_zneg_061]

theorem znegBlocks_chain : chainOK (-3, 1) (-3, 5) znegBlocks = true := by
  unfold znegBlocks
  exact q3F_zneg_chain

def zposBlocks : List (List QF) := [
  q3F_zpos_000_b]

set_option maxHeartbeats 4000000 in
theorem zposBlocks_wf : ∀ s ∈ zposBlocks, blockWF s = true := by
  -- Verified certificate computation.
  -- rcases pattern of `Q2VFieldGlobal.q2_vlo_blocks_wf`.
  unfold zposBlocks
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem zposBlocks_cells :
    ∀ s ∈ zposBlocks, cellsOK (fieldUB q3D 3 vLogRF .zpos) (kzQ 3) s = true := by
  intro s hs
  simp only [zposBlocks, List.mem_cons, List.mem_singleton, List.not_mem_nil,
    or_false] at hs
  rcases hs with rfl
  exacts [q3F_zpos_000]

theorem zposBlocks_chain : chainOK (3, 5) (1, 1) zposBlocks = true := by
  unfold zposBlocks
  exact q3F_zpos_chain

def arc1Blocks : List (List QF) := [
  q3F_arc1_000_b, q3F_arc1_001_b, q3F_arc1_002_b, q3F_arc1_003_b, q3F_arc1_004_b,
  q3F_arc1_005_b, q3F_arc1_006_b, q3F_arc1_007_b, q3F_arc1_008_b, q3F_arc1_009_b,
  q3F_arc1_010_b, q3F_arc1_011_b, q3F_arc1_012_b, q3F_arc1_013_b, q3F_arc1_014_b,
  q3F_arc1_015_b, q3F_arc1_016_b, q3F_arc1_017_b, q3F_arc1_018_b, q3F_arc1_019_b,
  q3F_arc1_020_b, q3F_arc1_021_b, q3F_arc1_022_b, q3F_arc1_023_b, q3F_arc1_024_b,
  q3F_arc1_025_b, q3F_arc1_026_b, q3F_arc1_027_b]

set_option maxHeartbeats 4000000 in
theorem arc1Blocks_wf : ∀ s ∈ arc1Blocks, blockWF s = true := by
  -- Verified certificate computation.
  -- rcases pattern of `Q2VFieldGlobal.q2_vlo_blocks_wf`.
  unfold arc1Blocks
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem arc1Blocks_cells :
    ∀ s ∈ arc1Blocks, cellsOK (fieldUB q3D 3 vLogRF .arc1) (kzQ 3) s = true := by
  intro s hs
  simp only [arc1Blocks, List.mem_cons, List.mem_singleton, List.not_mem_nil,
    or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
  exacts [q3F_arc1_000, q3F_arc1_001, q3F_arc1_002, q3F_arc1_003, q3F_arc1_004, q3F_arc1_005,
    q3F_arc1_006, q3F_arc1_007, q3F_arc1_008, q3F_arc1_009, q3F_arc1_010, q3F_arc1_011,
    q3F_arc1_012, q3F_arc1_013, q3F_arc1_014, q3F_arc1_015, q3F_arc1_016, q3F_arc1_017,
    q3F_arc1_018, q3F_arc1_019, q3F_arc1_020, q3F_arc1_021, q3F_arc1_022, q3F_arc1_023,
    q3F_arc1_024, q3F_arc1_025, q3F_arc1_026, q3F_arc1_027]

theorem arc1Blocks_chain : chainOK (0, 1) (1, 1) arc1Blocks = true := by
  unfold arc1Blocks
  exact q3F_arc1_chain

def arc2Blocks : List (List QF) := [
  q3F_arc2_000_b, q3F_arc2_001_b, q3F_arc2_002_b, q3F_arc2_003_b, q3F_arc2_004_b,
  q3F_arc2_005_b, q3F_arc2_006_b, q3F_arc2_007_b, q3F_arc2_008_b, q3F_arc2_009_b,
  q3F_arc2_010_b, q3F_arc2_011_b, q3F_arc2_012_b, q3F_arc2_013_b, q3F_arc2_014_b,
  q3F_arc2_015_b, q3F_arc2_016_b, q3F_arc2_017_b, q3F_arc2_018_b, q3F_arc2_019_b,
  q3F_arc2_020_b, q3F_arc2_021_b, q3F_arc2_022_b, q3F_arc2_023_b, q3F_arc2_024_b,
  q3F_arc2_025_b, q3F_arc2_026_b, q3F_arc2_027_b, q3F_arc2_028_b, q3F_arc2_029_b,
  q3F_arc2_030_b, q3F_arc2_031_b, q3F_arc2_032_b, q3F_arc2_033_b, q3F_arc2_034_b,
  q3F_arc2_035_b, q3F_arc2_036_b, q3F_arc2_037_b, q3F_arc2_038_b, q3F_arc2_039_b,
  q3F_arc2_040_b, q3F_arc2_041_b]

set_option maxHeartbeats 4000000 in
theorem arc2Blocks_wf : ∀ s ∈ arc2Blocks, blockWF s = true := by
  -- Verified certificate computation.
  -- rcases pattern of `Q2VFieldGlobal.q2_vlo_blocks_wf`.
  unfold arc2Blocks
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem arc2Blocks_cells :
    ∀ s ∈ arc2Blocks, cellsOK (fieldUB q3D 3 vLogRF .arc2) (kzQ 3) s = true := by
  intro s hs
  simp only [arc2Blocks, List.mem_cons, List.mem_singleton, List.not_mem_nil,
    or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
  exacts [q3F_arc2_000, q3F_arc2_001, q3F_arc2_002, q3F_arc2_003, q3F_arc2_004, q3F_arc2_005,
    q3F_arc2_006, q3F_arc2_007, q3F_arc2_008, q3F_arc2_009, q3F_arc2_010, q3F_arc2_011,
    q3F_arc2_012, q3F_arc2_013, q3F_arc2_014, q3F_arc2_015, q3F_arc2_016, q3F_arc2_017,
    q3F_arc2_018, q3F_arc2_019, q3F_arc2_020, q3F_arc2_021, q3F_arc2_022, q3F_arc2_023,
    q3F_arc2_024, q3F_arc2_025, q3F_arc2_026, q3F_arc2_027, q3F_arc2_028, q3F_arc2_029,
    q3F_arc2_030, q3F_arc2_031, q3F_arc2_032, q3F_arc2_033, q3F_arc2_034, q3F_arc2_035,
    q3F_arc2_036, q3F_arc2_037, q3F_arc2_038, q3F_arc2_039, q3F_arc2_040, q3F_arc2_041]

theorem arc2Blocks_chain : chainOK (0, 1) (1, 1) arc2Blocks = true := by
  unfold arc2Blocks
  exact q3F_arc2_chain

set_option maxHeartbeats 4000000 in
theorem energy_checks :
    ∀ e ∈ q3EnergyPlan,
      energyShardOK q3D 3 vLogRE e.1 e.2.1 e.2.2.1 e.2.2.2 = true := by
  intro e he
  simp only [q3EnergyPlan, List.mem_cons, List.mem_singleton, List.not_mem_nil,
    or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
  exacts [q3E_selfX_0_41, q3E_selfV_0_49, q3E_selfZ_0_32, q3E_selfZ_32_63, q3E_crossVZ_0_23,
    q3E_crossVZ_23_46, q3E_crossVZ_46_49, q3E_intPoi_0_4, q3E_intPoi_4_8,
    q3E_intPoi_8_12, q3E_intPoi_12_16, q3E_intPoi_16_20, q3E_intPoi_20_24,
    q3E_intPoi_24_28, q3E_intPoi_28_32, q3E_intPoi_32_36, q3E_intPoi_36_40,
    q3E_intPoi_40_44, q3E_intPoi_44_48, q3E_intPoi_48_52, q3E_intPoi_52_56,
    q3E_intPoi_56_60, q3E_intPoi_60_64, q3E_intPoi_64_68, q3E_intPoi_68_72,
    q3E_pp_0_10, q3E_pp_10_21, q3E_pp_21_33, q3E_pp_33_47, q3E_pp_47_64, q3E_pp_64_85,
    q3E_pp_85_122, q3E_pp_122_143, q3E_dq_0_1]

theorem dq_plan :
    ∀ e ∈ q3EnergyPlan, e.1 = EKind.dq → e.2.1 = 0 ∧ e.2.2.1 = 1 := by
  unfold q3EnergyPlan
  decide +kernel

theorem mx_den_pos : 0 < q3D.mx.2 := by decide +kernel
theorem mv_den_pos : 0 < q3D.mv.2 := by decide +kernel
theorem pm_den_pos : 0 < q3D.pm.2 := by decide +kernel


variable {hq : SignedVBaseRange 3}

/-- Five ledger witnesses (`CellSoundnessOn`) for any sound `lr`
(the leaf uses `lr = vLogRE`). -/
theorem cells (N : V13MeasureNormalization hq (v13RefRaw q3DecodedRows))
    {lr : IV} (hlr : IV.mem lr (Real.log (3 / 5 : ℝ))) :
    V13FiveCells q3DecodedRows N lr :=
  v13_five_cells q3DecodedRows q3_field_row_facts N hlr

/-- `C.x_field` from the finite x chain and the x endpoint disk. -/
theorem x_field (N : V13MeasureNormalization hq (v13RefRaw q3DecodedRows))
    (hend : ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ ≤ 1 / 250 →
      V.signedVFullFieldX (v13RefMeasure q3DecodedRows N) w ≤ (vEx 3 : ℝ)) :
    ∀ t : ℝ, t ∈ Set.Ioc (0 : ℝ) 1 →
      V.signedVFullFieldX (v13RefMeasure q3DecodedRows N) (t : ℂ) < (vKx 3 : ℝ) :=
  v13_x_field_of_blocks q3DecodedRows q3_field_row_facts N xBlocks_wf xBlocks_cells xBlocks_chain hend

/-- `C.v_field` from the two finite v chains and the v endpoint disk. -/
theorem v_field (N : V13MeasureNormalization hq (v13RefRaw q3DecodedRows))
    (hend : ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ ≤ 1 / 250 →
      V.signedVFullFieldV (v13RefMeasure q3DecodedRows N) w ≤ (vEv 3 : ℝ)) :
    ∀ t : ℝ, t ∈ Set.Ioc (0 : ℝ) 1 →
      V.signedVFullFieldV (v13RefMeasure q3DecodedRows N) (t : ℂ) < (vKv 3 : ℝ) :=
  v13_v_field_of_blocks q3DecodedRows q3_field_row_facts N vloBlocks_wf vloBlocks_cells vloBlocks_chain
    vhiBlocks_wf vhiBlocks_cells vhiBlocks_chain hend

/-- `C.z_field` from the zneg/zpos chains and the two arc chains. -/
theorem z_field (N : V13MeasureNormalization hq (v13RefRaw q3DecodedRows)) :
    ∀ w ∈ V.vContourTrace 3,
      V.signedVFullFieldZ (v13RefMeasure q3DecodedRows N) w < (vKz 3 : ℝ) :=
  v13_z_field_of_blocks q3DecodedRows q3_field_row_facts N
    znegBlocks_wf znegBlocks_cells (by exact znegBlocks_chain)  -- Verified certificate computation.
    zposBlocks_wf zposBlocks_cells zposBlocks_chain
    arc1Blocks_wf arc1Blocks_cells arc1Blocks_chain
    arc2Blocks_wf arc2Blocks_cells arc2Blocks_chain

/-- Endpoint evaluator checks, split out of `q3Endpoint_check`. -/
theorem ex_check : hiLe (exUB fieldMode q3D 3) (exQ 3) = true := by
  have h := q3Endpoint_check
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1

theorem ev_check : hiLe (evUB fieldMode q3D 3) (evQ 3) = true := by
  have h := q3Endpoint_check
  simp only [Bool.and_eq_true] at h
  exact h.1.1.2

/-- Generic x endpoint disk (supersedes the per-q Q4/Q2 endpoint files). -/
theorem x_endpoint_disk (hrows : V13DecodedRowBounds 3 q3DecodedRows)
    (N : V13MeasureNormalization hq (v13RefRaw q3DecodedRows)) :
    ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ ≤ 1 / 250 →
      V.signedVFullFieldX (v13RefMeasure q3DecodedRows N) w ≤ (vEx 3 : ℝ) :=
  fun w hw0 hw => v13_x_endpoint_disk q3DecodedRows hrows N
    (v13_x_endpoint_certificate q3DecodedRows q3_field_row_facts hrows N) ex_check (val_exQ_eq_vEx hq) w hw0 hw

/-- Energy shard ledger at `lr = vLogRE`.  The only non-finite input is the
dq series identity `hseries` (open analytic item S6-dq, same for all q). -/
theorem energy (N : V13MeasureNormalization hq (v13RefRaw q3DecodedRows))
    (hseries : V13DqSeries q3DecodedRows N) :
    EnergyShardSoundnessFact q3DecodedRows.data 3 vLogRE
      (planOf q3DecodedRows.data 3) (vEnergyTerm 3 q3DecodedRows.data) := by
  rw [planOf_q3]
  exact v13_energy_shard_fact q3DecodedRows q3_field_row_facts N mx_den_pos mv_den_pos h6_vLogRE_sound
    q3EnergyPlan energy_checks dq_plan hseries


/-- The q3 Poisson mass is not imported from a private q3 helper.  It is
recomputed from the generic decoded-row sum and the public q3 row facts. -/
theorem poisson_mass_real :
    (v13PoissonMeasure q3DecodedRows.data.full).real Set.univ =
      IK.val q3DecodedRows.data.pm := by
  have hpm : IK.val q3D.pm = (28293299 / 50000000 : ℝ) := by
    have hq : q3D.pm = (28293299000000, 50000000000000) := by decide +kernel
    rw [hq]
    norm_num [IK.val]
  have huniv : v13PoissonMeasure q3D.full Set.univ =
      (28293299 / 50000000 : ℝ≥0∞) := by
    rw [v13PoissonMeasure_univ_eq_sum q3D.full
      (fun c hc => (q3_field_row_facts.full_rows_data c hc).2.2.2.2.2.2.2)]
    norm_num [q3D, mkIData, v13PoissonMeasure, v13PoissonAtom,
      Li2Lean.V.Q2Certificate.poissonFull,
      Li2Lean.V.Q2Certificate.decodePoisson,
      Li2Lean.V.Q2Certificate.decodePoissonAux,
      Li2Lean.V.Q2Certificate.conjugatePoisson,
      Li2Lean.V.EnergyCertI.prow, q3PoissonPrefix, U, IK.val,
      ENNReal.ofReal_mul]
    simp (disch := positivity) only [← ENNReal.ofReal_add]
    rw [← ENNReal.ofReal_toReal
      (ENNReal.div_ne_top (by norm_num) (by norm_num) :
        (28293299 / 50000000 : ℝ≥0∞) ≠ ⊤)]
    norm_num
  have hmass : (v13PoissonMeasure q3D.full).real Set.univ =
      (28293299 / 50000000 : ℝ) := by
    simpa [Measure.real_def] using congrArg ENNReal.toReal huniv
  change (v13PoissonMeasure q3D.full).real Set.univ = IK.val q3D.pm
  rw [hmass, hpm]

theorem v_endpoint_disk (hrows : V13DecodedRowBounds 3 q3DecodedRows)
    (N : V13MeasureNormalization hq (v13RefRaw q3DecodedRows))
    : ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ ≤ 1 / 250 →
      V.signedVFullFieldV (v13RefMeasure q3DecodedRows N) w ≤ (vEv 3 : ℝ) :=
  fun w hw0 hw => v13_v_endpoint_disk q3DecodedRows hrows N
    (v13_v_endpoint_certificate q3DecodedRows q3_field_row_facts hrows N pm_den_pos poisson_mass_real)
    ev_check (val_evQ_eq_vEv hq) w hw0 hw

end H6CertQ3

end

end Li2Lean.B3

#print axioms Li2Lean.B3.H6CertQ3.xBlocks_wf
#print axioms Li2Lean.B3.H6CertQ3.poisson_mass_real
#print axioms Li2Lean.B3.H6CertQ3.cells
#print axioms Li2Lean.B3.H6CertQ3.x_field
#print axioms Li2Lean.B3.H6CertQ3.v_field
#print axioms Li2Lean.B3.H6CertQ3.z_field
#print axioms Li2Lean.B3.H6CertQ3.v_endpoint_disk
#print axioms Li2Lean.B3.H6CertQ3.energy
