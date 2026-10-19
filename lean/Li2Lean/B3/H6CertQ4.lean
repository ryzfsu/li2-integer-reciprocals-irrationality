/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B3.V13FieldCellGeneric
import Li2Lean.B3.H6CertBridges
import Li2Lean.V.EnergyCertI.Q4Assembly
import Li2Lean.B3.H6Q4FieldRowFacts
import Li2Lean.B3.Q4EndpointDisk
import Li2Lean.B3.Q4ReferenceNormalization

/-! H6 certificate ledger for q = 4. Generated from the H6CertPerQ source; the S6-dq series remains an explicit input. -/
namespace Li2Lean.B3

noncomputable section

open MeasureTheory Set Complex
open scoped ENNReal ComplexConjugate
open V
open V.EnergyCertI
open V.EnergyCertI.IK
/-! ## Part D: per-q instances (generated from the master certificate files). -/

set_option maxRecDepth 100000

/-! ### q = 4 -/

namespace H6CertQ4

def xBlocks : List (List QF) := [
  q4F_x_000_b, q4F_x_001_b, q4F_x_002_b, q4F_x_003_b, q4F_x_004_b, q4F_x_005_b,
  q4F_x_006_b, q4F_x_007_b, q4F_x_008_b, q4F_x_009_b, q4F_x_010_b, q4F_x_011_b,
  q4F_x_012_b, q4F_x_013_b, q4F_x_014_b, q4F_x_015_b, q4F_x_016_b, q4F_x_017_b,
  q4F_x_018_b, q4F_x_019_b, q4F_x_020_b, q4F_x_021_b, q4F_x_022_b, q4F_x_023_b,
  q4F_x_024_b, q4F_x_025_b, q4F_x_026_b, q4F_x_027_b, q4F_x_028_b, q4F_x_029_b,
  q4F_x_030_b, q4F_x_031_b, q4F_x_032_b, q4F_x_033_b, q4F_x_034_b, q4F_x_035_b,
  q4F_x_036_b, q4F_x_037_b, q4F_x_038_b, q4F_x_039_b, q4F_x_040_b, q4F_x_041_b,
  q4F_x_042_b, q4F_x_043_b, q4F_x_044_b, q4F_x_045_b]

set_option maxHeartbeats 4000000 in
theorem xBlocks_wf : ∀ s ∈ xBlocks, blockWF s = true := by
  -- rcases pattern of `Q2VFieldGlobal.q2_vlo_blocks_wf`.
  unfold xBlocks
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem xBlocks_cells :
    ∀ s ∈ xBlocks, cellsOK (fieldUB q4D 4 vLogRF .x) (kxQ 4) s = true := by
  intro s hs
  simp only [xBlocks, List.mem_cons, List.mem_singleton, List.not_mem_nil,
    or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
  exacts [q4F_x_000, q4F_x_001, q4F_x_002, q4F_x_003, q4F_x_004, q4F_x_005, q4F_x_006,
    q4F_x_007, q4F_x_008, q4F_x_009, q4F_x_010, q4F_x_011, q4F_x_012, q4F_x_013,
    q4F_x_014, q4F_x_015, q4F_x_016, q4F_x_017, q4F_x_018, q4F_x_019, q4F_x_020,
    q4F_x_021, q4F_x_022, q4F_x_023, q4F_x_024, q4F_x_025, q4F_x_026, q4F_x_027,
    q4F_x_028, q4F_x_029, q4F_x_030, q4F_x_031, q4F_x_032, q4F_x_033, q4F_x_034,
    q4F_x_035, q4F_x_036, q4F_x_037, q4F_x_038, q4F_x_039, q4F_x_040, q4F_x_041,
    q4F_x_042, q4F_x_043, q4F_x_044, q4F_x_045]

theorem xBlocks_chain : chainOK (1, 250) (1, 1) xBlocks = true := by
  unfold xBlocks
  exact q4F_x_chain

def vloBlocks : List (List QF) := [
  q4F_vlo_000_b, q4F_vlo_001_b, q4F_vlo_002_b, q4F_vlo_003_b, q4F_vlo_004_b,
  q4F_vlo_005_b, q4F_vlo_006_b, q4F_vlo_007_b, q4F_vlo_008_b, q4F_vlo_009_b,
  q4F_vlo_010_b, q4F_vlo_011_b, q4F_vlo_012_b, q4F_vlo_013_b, q4F_vlo_014_b,
  q4F_vlo_015_b, q4F_vlo_016_b, q4F_vlo_017_b, q4F_vlo_018_b, q4F_vlo_019_b,
  q4F_vlo_020_b, q4F_vlo_021_b, q4F_vlo_022_b, q4F_vlo_023_b, q4F_vlo_024_b,
  q4F_vlo_025_b, q4F_vlo_026_b, q4F_vlo_027_b, q4F_vlo_028_b, q4F_vlo_029_b,
  q4F_vlo_030_b, q4F_vlo_031_b, q4F_vlo_032_b, q4F_vlo_033_b, q4F_vlo_034_b,
  q4F_vlo_035_b, q4F_vlo_036_b, q4F_vlo_037_b, q4F_vlo_038_b, q4F_vlo_039_b,
  q4F_vlo_040_b, q4F_vlo_041_b, q4F_vlo_042_b, q4F_vlo_043_b, q4F_vlo_044_b,
  q4F_vlo_045_b, q4F_vlo_046_b, q4F_vlo_047_b, q4F_vlo_048_b, q4F_vlo_049_b,
  q4F_vlo_050_b, q4F_vlo_051_b, q4F_vlo_052_b, q4F_vlo_053_b, q4F_vlo_054_b,
  q4F_vlo_055_b, q4F_vlo_056_b, q4F_vlo_057_b, q4F_vlo_058_b, q4F_vlo_059_b,
  q4F_vlo_060_b, q4F_vlo_061_b, q4F_vlo_062_b, q4F_vlo_063_b, q4F_vlo_064_b,
  q4F_vlo_065_b, q4F_vlo_066_b, q4F_vlo_067_b]

set_option maxHeartbeats 4000000 in
theorem vloBlocks_wf : ∀ s ∈ vloBlocks, blockWF s = true := by
  -- rcases pattern of `Q2VFieldGlobal.q2_vlo_blocks_wf`.
  unfold vloBlocks
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem vloBlocks_cells :
    ∀ s ∈ vloBlocks, cellsOK (fieldUB q4D 4 vLogRF .vlo) (kvQ 4) s = true := by
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
      rfl | rfl | rfl | rfl
  exacts [q4F_vlo_000, q4F_vlo_001, q4F_vlo_002, q4F_vlo_003, q4F_vlo_004, q4F_vlo_005,
    q4F_vlo_006, q4F_vlo_007, q4F_vlo_008, q4F_vlo_009, q4F_vlo_010, q4F_vlo_011,
    q4F_vlo_012, q4F_vlo_013, q4F_vlo_014, q4F_vlo_015, q4F_vlo_016, q4F_vlo_017,
    q4F_vlo_018, q4F_vlo_019, q4F_vlo_020, q4F_vlo_021, q4F_vlo_022, q4F_vlo_023,
    q4F_vlo_024, q4F_vlo_025, q4F_vlo_026, q4F_vlo_027, q4F_vlo_028, q4F_vlo_029,
    q4F_vlo_030, q4F_vlo_031, q4F_vlo_032, q4F_vlo_033, q4F_vlo_034, q4F_vlo_035,
    q4F_vlo_036, q4F_vlo_037, q4F_vlo_038, q4F_vlo_039, q4F_vlo_040, q4F_vlo_041,
    q4F_vlo_042, q4F_vlo_043, q4F_vlo_044, q4F_vlo_045, q4F_vlo_046, q4F_vlo_047,
    q4F_vlo_048, q4F_vlo_049, q4F_vlo_050, q4F_vlo_051, q4F_vlo_052, q4F_vlo_053,
    q4F_vlo_054, q4F_vlo_055, q4F_vlo_056, q4F_vlo_057, q4F_vlo_058, q4F_vlo_059,
    q4F_vlo_060, q4F_vlo_061, q4F_vlo_062, q4F_vlo_063, q4F_vlo_064, q4F_vlo_065,
    q4F_vlo_066, q4F_vlo_067]

theorem vloBlocks_chain : chainOK (1, 250) (3, 5) vloBlocks = true := by
  unfold vloBlocks
  exact q4F_vlo_chain

def vhiBlocks : List (List QF) := [
  q4F_vhi_000_b, q4F_vhi_001_b, q4F_vhi_002_b, q4F_vhi_003_b, q4F_vhi_004_b,
  q4F_vhi_005_b, q4F_vhi_006_b, q4F_vhi_007_b, q4F_vhi_008_b, q4F_vhi_009_b,
  q4F_vhi_010_b, q4F_vhi_011_b, q4F_vhi_012_b, q4F_vhi_013_b, q4F_vhi_014_b,
  q4F_vhi_015_b, q4F_vhi_016_b, q4F_vhi_017_b, q4F_vhi_018_b, q4F_vhi_019_b,
  q4F_vhi_020_b, q4F_vhi_021_b, q4F_vhi_022_b, q4F_vhi_023_b, q4F_vhi_024_b,
  q4F_vhi_025_b, q4F_vhi_026_b, q4F_vhi_027_b, q4F_vhi_028_b, q4F_vhi_029_b,
  q4F_vhi_030_b, q4F_vhi_031_b, q4F_vhi_032_b, q4F_vhi_033_b, q4F_vhi_034_b,
  q4F_vhi_035_b, q4F_vhi_036_b, q4F_vhi_037_b, q4F_vhi_038_b, q4F_vhi_039_b,
  q4F_vhi_040_b, q4F_vhi_041_b, q4F_vhi_042_b, q4F_vhi_043_b, q4F_vhi_044_b,
  q4F_vhi_045_b, q4F_vhi_046_b, q4F_vhi_047_b, q4F_vhi_048_b, q4F_vhi_049_b,
  q4F_vhi_050_b, q4F_vhi_051_b, q4F_vhi_052_b, q4F_vhi_053_b, q4F_vhi_054_b,
  q4F_vhi_055_b, q4F_vhi_056_b, q4F_vhi_057_b, q4F_vhi_058_b, q4F_vhi_059_b,
  q4F_vhi_060_b, q4F_vhi_061_b, q4F_vhi_062_b, q4F_vhi_063_b, q4F_vhi_064_b,
  q4F_vhi_065_b, q4F_vhi_066_b, q4F_vhi_067_b, q4F_vhi_068_b, q4F_vhi_069_b]

set_option maxHeartbeats 4000000 in
theorem vhiBlocks_wf : ∀ s ∈ vhiBlocks, blockWF s = true := by
  -- rcases pattern of `Q2VFieldGlobal.q2_vlo_blocks_wf`.
  unfold vhiBlocks
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem vhiBlocks_cells :
    ∀ s ∈ vhiBlocks, cellsOK (fieldUB q4D 4 vLogRF .vhi) (kvQ 4) s = true := by
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
      rfl | rfl | rfl | rfl | rfl | rfl
  exacts [q4F_vhi_000, q4F_vhi_001, q4F_vhi_002, q4F_vhi_003, q4F_vhi_004, q4F_vhi_005,
    q4F_vhi_006, q4F_vhi_007, q4F_vhi_008, q4F_vhi_009, q4F_vhi_010, q4F_vhi_011,
    q4F_vhi_012, q4F_vhi_013, q4F_vhi_014, q4F_vhi_015, q4F_vhi_016, q4F_vhi_017,
    q4F_vhi_018, q4F_vhi_019, q4F_vhi_020, q4F_vhi_021, q4F_vhi_022, q4F_vhi_023,
    q4F_vhi_024, q4F_vhi_025, q4F_vhi_026, q4F_vhi_027, q4F_vhi_028, q4F_vhi_029,
    q4F_vhi_030, q4F_vhi_031, q4F_vhi_032, q4F_vhi_033, q4F_vhi_034, q4F_vhi_035,
    q4F_vhi_036, q4F_vhi_037, q4F_vhi_038, q4F_vhi_039, q4F_vhi_040, q4F_vhi_041,
    q4F_vhi_042, q4F_vhi_043, q4F_vhi_044, q4F_vhi_045, q4F_vhi_046, q4F_vhi_047,
    q4F_vhi_048, q4F_vhi_049, q4F_vhi_050, q4F_vhi_051, q4F_vhi_052, q4F_vhi_053,
    q4F_vhi_054, q4F_vhi_055, q4F_vhi_056, q4F_vhi_057, q4F_vhi_058, q4F_vhi_059,
    q4F_vhi_060, q4F_vhi_061, q4F_vhi_062, q4F_vhi_063, q4F_vhi_064, q4F_vhi_065,
    q4F_vhi_066, q4F_vhi_067, q4F_vhi_068, q4F_vhi_069]

theorem vhiBlocks_chain : chainOK (3, 5) (1, 1) vhiBlocks = true := by
  unfold vhiBlocks
  exact q4F_vhi_chain

def znegBlocks : List (List QF) := [
  q4F_zneg_000_b, q4F_zneg_001_b, q4F_zneg_002_b, q4F_zneg_003_b, q4F_zneg_004_b,
  q4F_zneg_005_b, q4F_zneg_006_b, q4F_zneg_007_b, q4F_zneg_008_b, q4F_zneg_009_b,
  q4F_zneg_010_b, q4F_zneg_011_b, q4F_zneg_012_b, q4F_zneg_013_b, q4F_zneg_014_b,
  q4F_zneg_015_b, q4F_zneg_016_b, q4F_zneg_017_b, q4F_zneg_018_b, q4F_zneg_019_b,
  q4F_zneg_020_b, q4F_zneg_021_b, q4F_zneg_022_b, q4F_zneg_023_b, q4F_zneg_024_b,
  q4F_zneg_025_b, q4F_zneg_026_b, q4F_zneg_027_b, q4F_zneg_028_b, q4F_zneg_029_b,
  q4F_zneg_030_b, q4F_zneg_031_b, q4F_zneg_032_b, q4F_zneg_033_b, q4F_zneg_034_b,
  q4F_zneg_035_b, q4F_zneg_036_b, q4F_zneg_037_b, q4F_zneg_038_b, q4F_zneg_039_b,
  q4F_zneg_040_b, q4F_zneg_041_b, q4F_zneg_042_b, q4F_zneg_043_b, q4F_zneg_044_b,
  q4F_zneg_045_b, q4F_zneg_046_b, q4F_zneg_047_b, q4F_zneg_048_b, q4F_zneg_049_b,
  q4F_zneg_050_b, q4F_zneg_051_b, q4F_zneg_052_b, q4F_zneg_053_b, q4F_zneg_054_b,
  q4F_zneg_055_b, q4F_zneg_056_b, q4F_zneg_057_b, q4F_zneg_058_b, q4F_zneg_059_b,
  q4F_zneg_060_b, q4F_zneg_061_b, q4F_zneg_062_b, q4F_zneg_063_b, q4F_zneg_064_b,
  q4F_zneg_065_b, q4F_zneg_066_b, q4F_zneg_067_b, q4F_zneg_068_b, q4F_zneg_069_b,
  q4F_zneg_070_b, q4F_zneg_071_b, q4F_zneg_072_b, q4F_zneg_073_b, q4F_zneg_074_b,
  q4F_zneg_075_b, q4F_zneg_076_b, q4F_zneg_077_b, q4F_zneg_078_b, q4F_zneg_079_b,
  q4F_zneg_080_b, q4F_zneg_081_b, q4F_zneg_082_b, q4F_zneg_083_b, q4F_zneg_084_b,
  q4F_zneg_085_b, q4F_zneg_086_b, q4F_zneg_087_b, q4F_zneg_088_b, q4F_zneg_089_b,
  q4F_zneg_090_b, q4F_zneg_091_b]

set_option maxHeartbeats 4000000 in
theorem znegBlocks_wf : ∀ s ∈ znegBlocks, blockWF s = true := by
  -- rcases pattern of `Q2VFieldGlobal.q2_vlo_blocks_wf`.
  unfold znegBlocks
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem znegBlocks_cells :
    ∀ s ∈ znegBlocks, cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) s = true := by
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
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
  exacts [q4F_zneg_000, q4F_zneg_001, q4F_zneg_002, q4F_zneg_003, q4F_zneg_004, q4F_zneg_005,
    q4F_zneg_006, q4F_zneg_007, q4F_zneg_008, q4F_zneg_009, q4F_zneg_010, q4F_zneg_011,
    q4F_zneg_012, q4F_zneg_013, q4F_zneg_014, q4F_zneg_015, q4F_zneg_016, q4F_zneg_017,
    q4F_zneg_018, q4F_zneg_019, q4F_zneg_020, q4F_zneg_021, q4F_zneg_022, q4F_zneg_023,
    q4F_zneg_024, q4F_zneg_025, q4F_zneg_026, q4F_zneg_027, q4F_zneg_028, q4F_zneg_029,
    q4F_zneg_030, q4F_zneg_031, q4F_zneg_032, q4F_zneg_033, q4F_zneg_034, q4F_zneg_035,
    q4F_zneg_036, q4F_zneg_037, q4F_zneg_038, q4F_zneg_039, q4F_zneg_040, q4F_zneg_041,
    q4F_zneg_042, q4F_zneg_043, q4F_zneg_044, q4F_zneg_045, q4F_zneg_046, q4F_zneg_047,
    q4F_zneg_048, q4F_zneg_049, q4F_zneg_050, q4F_zneg_051, q4F_zneg_052, q4F_zneg_053,
    q4F_zneg_054, q4F_zneg_055, q4F_zneg_056, q4F_zneg_057, q4F_zneg_058, q4F_zneg_059,
    q4F_zneg_060, q4F_zneg_061, q4F_zneg_062, q4F_zneg_063, q4F_zneg_064, q4F_zneg_065,
    q4F_zneg_066, q4F_zneg_067, q4F_zneg_068, q4F_zneg_069, q4F_zneg_070, q4F_zneg_071,
    q4F_zneg_072, q4F_zneg_073, q4F_zneg_074, q4F_zneg_075, q4F_zneg_076, q4F_zneg_077,
    q4F_zneg_078, q4F_zneg_079, q4F_zneg_080, q4F_zneg_081, q4F_zneg_082, q4F_zneg_083,
    q4F_zneg_084, q4F_zneg_085, q4F_zneg_086, q4F_zneg_087, q4F_zneg_088, q4F_zneg_089,
    q4F_zneg_090, q4F_zneg_091]

theorem znegBlocks_chain : chainOK (-4, 1) (-3, 5) znegBlocks = true := by
  unfold znegBlocks
  exact q4F_zneg_chain

def zposBlocks : List (List QF) := [
  q4F_zpos_000_b]

set_option maxHeartbeats 4000000 in
theorem zposBlocks_wf : ∀ s ∈ zposBlocks, blockWF s = true := by
  -- rcases pattern of `Q2VFieldGlobal.q2_vlo_blocks_wf`.
  unfold zposBlocks
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem zposBlocks_cells :
    ∀ s ∈ zposBlocks, cellsOK (fieldUB q4D 4 vLogRF .zpos) (kzQ 4) s = true := by
  intro s hs
  simp only [zposBlocks, List.mem_cons, List.mem_singleton, List.not_mem_nil,
    or_false] at hs
  rcases hs with rfl
  exacts [q4F_zpos_000]

theorem zposBlocks_chain : chainOK (3, 5) (1, 1) zposBlocks = true := by
  unfold zposBlocks
  exact q4F_zpos_chain

def arc1Blocks : List (List QF) := [
  q4F_arc1_000_b, q4F_arc1_001_b, q4F_arc1_002_b, q4F_arc1_003_b, q4F_arc1_004_b,
  q4F_arc1_005_b, q4F_arc1_006_b, q4F_arc1_007_b, q4F_arc1_008_b, q4F_arc1_009_b,
  q4F_arc1_010_b, q4F_arc1_011_b, q4F_arc1_012_b, q4F_arc1_013_b, q4F_arc1_014_b,
  q4F_arc1_015_b, q4F_arc1_016_b, q4F_arc1_017_b, q4F_arc1_018_b, q4F_arc1_019_b,
  q4F_arc1_020_b, q4F_arc1_021_b, q4F_arc1_022_b, q4F_arc1_023_b]

set_option maxHeartbeats 4000000 in
theorem arc1Blocks_wf : ∀ s ∈ arc1Blocks, blockWF s = true := by
  -- rcases pattern of `Q2VFieldGlobal.q2_vlo_blocks_wf`.
  unfold arc1Blocks
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem arc1Blocks_cells :
    ∀ s ∈ arc1Blocks, cellsOK (fieldUB q4D 4 vLogRF .arc1) (kzQ 4) s = true := by
  intro s hs
  simp only [arc1Blocks, List.mem_cons, List.mem_singleton, List.not_mem_nil,
    or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [q4F_arc1_000, q4F_arc1_001, q4F_arc1_002, q4F_arc1_003, q4F_arc1_004, q4F_arc1_005,
    q4F_arc1_006, q4F_arc1_007, q4F_arc1_008, q4F_arc1_009, q4F_arc1_010, q4F_arc1_011,
    q4F_arc1_012, q4F_arc1_013, q4F_arc1_014, q4F_arc1_015, q4F_arc1_016, q4F_arc1_017,
    q4F_arc1_018, q4F_arc1_019, q4F_arc1_020, q4F_arc1_021, q4F_arc1_022, q4F_arc1_023]

theorem arc1Blocks_chain : chainOK (0, 1) (1, 1) arc1Blocks = true := by
  unfold arc1Blocks
  exact q4F_arc1_chain

def arc2Blocks : List (List QF) := [
  q4F_arc2_000_b, q4F_arc2_001_b, q4F_arc2_002_b, q4F_arc2_003_b, q4F_arc2_004_b,
  q4F_arc2_005_b, q4F_arc2_006_b, q4F_arc2_007_b, q4F_arc2_008_b, q4F_arc2_009_b,
  q4F_arc2_010_b, q4F_arc2_011_b, q4F_arc2_012_b, q4F_arc2_013_b, q4F_arc2_014_b,
  q4F_arc2_015_b, q4F_arc2_016_b, q4F_arc2_017_b, q4F_arc2_018_b, q4F_arc2_019_b,
  q4F_arc2_020_b, q4F_arc2_021_b, q4F_arc2_022_b, q4F_arc2_023_b, q4F_arc2_024_b,
  q4F_arc2_025_b, q4F_arc2_026_b, q4F_arc2_027_b, q4F_arc2_028_b, q4F_arc2_029_b,
  q4F_arc2_030_b, q4F_arc2_031_b, q4F_arc2_032_b, q4F_arc2_033_b, q4F_arc2_034_b,
  q4F_arc2_035_b, q4F_arc2_036_b, q4F_arc2_037_b, q4F_arc2_038_b, q4F_arc2_039_b,
  q4F_arc2_040_b]

set_option maxHeartbeats 4000000 in
theorem arc2Blocks_wf : ∀ s ∈ arc2Blocks, blockWF s = true := by
  -- rcases pattern of `Q2VFieldGlobal.q2_vlo_blocks_wf`.
  unfold arc2Blocks
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem arc2Blocks_cells :
    ∀ s ∈ arc2Blocks, cellsOK (fieldUB q4D 4 vLogRF .arc2) (kzQ 4) s = true := by
  intro s hs
  simp only [arc2Blocks, List.mem_cons, List.mem_singleton, List.not_mem_nil,
    or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl
  exacts [q4F_arc2_000, q4F_arc2_001, q4F_arc2_002, q4F_arc2_003, q4F_arc2_004, q4F_arc2_005,
    q4F_arc2_006, q4F_arc2_007, q4F_arc2_008, q4F_arc2_009, q4F_arc2_010, q4F_arc2_011,
    q4F_arc2_012, q4F_arc2_013, q4F_arc2_014, q4F_arc2_015, q4F_arc2_016, q4F_arc2_017,
    q4F_arc2_018, q4F_arc2_019, q4F_arc2_020, q4F_arc2_021, q4F_arc2_022, q4F_arc2_023,
    q4F_arc2_024, q4F_arc2_025, q4F_arc2_026, q4F_arc2_027, q4F_arc2_028, q4F_arc2_029,
    q4F_arc2_030, q4F_arc2_031, q4F_arc2_032, q4F_arc2_033, q4F_arc2_034, q4F_arc2_035,
    q4F_arc2_036, q4F_arc2_037, q4F_arc2_038, q4F_arc2_039, q4F_arc2_040]

theorem arc2Blocks_chain : chainOK (0, 1) (1, 1) arc2Blocks = true := by
  unfold arc2Blocks
  exact q4F_arc2_chain

set_option maxHeartbeats 4000000 in
theorem energy_checks :
    ∀ e ∈ q4EnergyPlan,
      energyShardOK q4D 4 vLogRE e.1 e.2.1 e.2.2.1 e.2.2.2 = true := by
  intro e he
  simp only [q4EnergyPlan, List.mem_cons, List.mem_singleton, List.not_mem_nil,
    or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl
  exacts [q4E_selfX_0_41, q4E_selfV_0_49, q4E_selfZ_0_32, q4E_selfZ_32_63, q4E_crossVZ_0_23,
    q4E_crossVZ_23_46, q4E_crossVZ_46_49, q4E_intPoi_0_4, q4E_intPoi_4_8,
    q4E_intPoi_8_12, q4E_intPoi_12_16, q4E_intPoi_16_20, q4E_intPoi_20_24,
    q4E_intPoi_24_28, q4E_intPoi_28_32, q4E_intPoi_32_36, q4E_intPoi_36_40,
    q4E_intPoi_40_44, q4E_intPoi_44_48, q4E_intPoi_48_52, q4E_intPoi_52_56,
    q4E_intPoi_56_60, q4E_intPoi_60_64, q4E_intPoi_64_68, q4E_intPoi_68_71,
    q4E_pp_0_11, q4E_pp_11_23, q4E_pp_23_36, q4E_pp_36_51, q4E_pp_51_69, q4E_pp_69_94,
    q4E_pp_94_141, q4E_dq_0_1]

theorem dq_plan :
    ∀ e ∈ q4EnergyPlan, e.1 = EKind.dq → e.2.1 = 0 ∧ e.2.2.1 = 1 := by
  unfold q4EnergyPlan
  decide +kernel

theorem mx_den_pos : 0 < q4D.mx.2 := by decide +kernel
theorem mv_den_pos : 0 < q4D.mv.2 := by decide +kernel
theorem pm_den_pos : 0 < q4D.pm.2 := by decide +kernel


variable {hq : SignedVBaseRange 4}

/-- Five ledger witnesses (`CellSoundnessOn`) for any sound `lr`
(the leaf uses `lr = vLogRE`). -/
theorem cells (N : V13MeasureNormalization hq (v13RefRaw q4DecodedRows))
    {lr : IV} (hlr : IV.mem lr (Real.log (3 / 5 : ℝ))) :
    V13FiveCells q4DecodedRows N lr :=
  v13_five_cells q4DecodedRows q4_field_row_facts N hlr

/-- `C.x_field` from the finite x chain and the x endpoint disk. -/
theorem x_field (N : V13MeasureNormalization hq (v13RefRaw q4DecodedRows))
    (hend : ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ ≤ 1 / 250 →
      V.signedVFullFieldX (v13RefMeasure q4DecodedRows N) w ≤ (vEx 4 : ℝ)) :
    ∀ t : ℝ, t ∈ Set.Ioc (0 : ℝ) 1 →
      V.signedVFullFieldX (v13RefMeasure q4DecodedRows N) (t : ℂ) < (vKx 4 : ℝ) :=
  v13_x_field_of_blocks q4DecodedRows q4_field_row_facts N xBlocks_wf xBlocks_cells xBlocks_chain hend

/-- `C.v_field` from the two finite v chains and the v endpoint disk. -/
theorem v_field (N : V13MeasureNormalization hq (v13RefRaw q4DecodedRows))
    (hend : ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ ≤ 1 / 250 →
      V.signedVFullFieldV (v13RefMeasure q4DecodedRows N) w ≤ (vEv 4 : ℝ)) :
    ∀ t : ℝ, t ∈ Set.Ioc (0 : ℝ) 1 →
      V.signedVFullFieldV (v13RefMeasure q4DecodedRows N) (t : ℂ) < (vKv 4 : ℝ) :=
  v13_v_field_of_blocks q4DecodedRows q4_field_row_facts N vloBlocks_wf vloBlocks_cells vloBlocks_chain
    vhiBlocks_wf vhiBlocks_cells vhiBlocks_chain hend

/-- `C.z_field` from the zneg/zpos chains and the two arc chains. -/
theorem z_field (N : V13MeasureNormalization hq (v13RefRaw q4DecodedRows)) :
    ∀ w ∈ V.vContourTrace 4,
      V.signedVFullFieldZ (v13RefMeasure q4DecodedRows N) w < (vKz 4 : ℝ) :=
  v13_z_field_of_blocks q4DecodedRows q4_field_row_facts N
    znegBlocks_wf znegBlocks_cells (by exact znegBlocks_chain)
    zposBlocks_wf zposBlocks_cells zposBlocks_chain
    arc1Blocks_wf arc1Blocks_cells arc1Blocks_chain
    arc2Blocks_wf arc2Blocks_cells arc2Blocks_chain

/-- Endpoint evaluator checks, split out of `q4Endpoint_check`. -/
theorem ex_check : hiLe (exUB fieldMode q4D 4) (exQ 4) = true := by
  have h := q4Endpoint_check
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1

theorem ev_check : hiLe (evUB fieldMode q4D 4) (evQ 4) = true := by
  have h := q4Endpoint_check
  simp only [Bool.and_eq_true] at h
  exact h.1.1.2

/-- Generic x endpoint disk (supersedes the per-q Q4/Q2 endpoint files). -/
theorem x_endpoint_disk (hrows : V13DecodedRowBounds 4 q4DecodedRows)
    (N : V13MeasureNormalization hq (v13RefRaw q4DecodedRows)) :
    ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ ≤ 1 / 250 →
      V.signedVFullFieldX (v13RefMeasure q4DecodedRows N) w ≤ (vEx 4 : ℝ) :=
  fun w hw0 hw => v13_x_endpoint_disk q4DecodedRows hrows N
    (v13_x_endpoint_certificate q4DecodedRows q4_field_row_facts hrows N) ex_check (val_exQ_eq_vEx hq) w hw0 hw

/-- Energy shard ledger at `lr = vLogRE`.  The only non-finite input is the
dq series identity `hseries` (open analytic item S6-dq, same for all q). -/
theorem energy (N : V13MeasureNormalization hq (v13RefRaw q4DecodedRows))
    (hseries : V13DqSeries q4DecodedRows N) :
    EnergyShardSoundnessFact q4DecodedRows.data 4 vLogRE
      (planOf q4DecodedRows.data 4) (vEnergyTerm 4 q4DecodedRows.data) := by
  rw [planOf_q4]
  exact v13_energy_shard_fact q4DecodedRows q4_field_row_facts N mx_den_pos mv_den_pos h6_vLogRE_sound
    q4EnergyPlan energy_checks dq_plan hseries


theorem poisson_mass_real :
    (v13PoissonMeasure q4DecodedRows.data.full).real Set.univ = IK.val q4DecodedRows.data.pm := by
  have hpm : IK.val q4D.pm = (6317803 / 12500000 : ℝ) := by
    norm_num [q4D, mkIData, q4PoissonPrefix,
      Li2Lean.V.Q2Certificate.poissonFull,
      Li2Lean.V.Q2Certificate.conjugatePoisson,
      Li2Lean.V.Q2Certificate.decodePoisson,
      Li2Lean.V.Q2Certificate.decodePoissonAux,
      Li2Lean.V.EnergyCertI.prow, U, IK.val, Li2Lean.V.EnergyCertI.sumU]
  have hmass : (v13PoissonMeasure q4D.full).real Set.univ = (6317803 / 12500000 : ℝ) := by
    simpa [Measure.real_def] using congrArg ENNReal.toReal q4ReferenceRaw_poisson_mass
  change (v13PoissonMeasure q4D.full).real Set.univ = IK.val q4D.pm
  rw [hmass, hpm]

/-- Generic v endpoint disk instantiated at q = 4. -/
theorem v_endpoint_disk (hrows : V13DecodedRowBounds 4 q4DecodedRows)
    (N : V13MeasureNormalization hq (v13RefRaw q4DecodedRows)) :
    ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ ≤ 1 / 250 →
      V.signedVFullFieldV (v13RefMeasure q4DecodedRows N) w ≤ (vEv 4 : ℝ) :=
  fun w hw0 hw => v13_v_endpoint_disk q4DecodedRows hrows N
    (v13_v_endpoint_certificate q4DecodedRows q4_field_row_facts hrows N pm_den_pos poisson_mass_real)
    ev_check (val_evQ_eq_vEv hq) w hw0 hw

end H6CertQ4
