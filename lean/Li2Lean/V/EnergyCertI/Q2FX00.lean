/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
/-
Generated certificate data
from v13 `v-reference-data.tex` (sha256 e3983e04...cd9b).  elaborated.
-/

import Li2Lean.V.EnergyCertI.Q2Rows
import Li2Lean.V.EnergyCertI.Consts

namespace Li2Lean.V.EnergyCertI

open IK

/-- Breakpoints of cells 0..24 of piece `x` (q = 2). -/
def q2F_x_000_b : List QF := [
  (1, 250), (281, 8000), (1373, 32000), (811, 16000),
  (3493, 64000), (1871, 32000), (7733, 128000), (3991, 64000),
  (8231, 128000), (53, 800), (8729, 128000), (17707, 256000),
  (4489, 64000), (3641, 51200), (9227, 128000), (18703, 256000),
  (2369, 32000), (19201, 256000), (389, 5120), (19699, 256000),
  (4987, 64000), (20197, 256000), (10223, 128000), (4139, 51200),
  (41639, 512000), (1309, 16000)]

/-- 25 cells, about 2325 transcendental evaluations (field mode). -/
theorem q2F_x_000 :
    cellsOK (fieldUB q2D 2 vLogRF .x) (kxQ 2) q2F_x_000_b = true := by
  decide +kernel

/-- Breakpoints of cells 25..49 of piece `x` (q = 2). -/
def q2F_x_001_b : List QF := [
  (1309, 16000), (42137, 512000), (21193, 256000), (10721, 128000),
  (21691, 256000), (1097, 12800), (22189, 256000), (11219, 128000),
  (22687, 256000), (2867, 32000), (4637, 51200), (11717, 128000),
  (23683, 256000), (5983, 64000), (24181, 256000), (2443, 25600),
  (24679, 256000), (779, 8000), (25177, 256000), (12713, 128000),
  (1027, 10240), (6481, 64000), (26173, 256000), (13211, 128000),
  (26671, 256000), (673, 6400)]

/-- 25 cells, about 2325 transcendental evaluations (field mode). -/
theorem q2F_x_001 :
    cellsOK (fieldUB q2D 2 vLogRF .x) (kxQ 2) q2F_x_001_b = true := by
  decide +kernel

/-- Breakpoints of cells 50..74 of piece `x` (q = 2). -/
def q2F_x_002_b : List QF := [
  (673, 6400), (27169, 256000), (13709, 128000), (27667, 256000),
  (6979, 64000), (5633, 51200), (14207, 128000), (28663, 256000),
  (1807, 16000), (29161, 256000), (2941, 25600), (29659, 256000),
  (7477, 64000), (30157, 256000), (15203, 128000), (6131, 51200),
  (3863, 32000), (31153, 256000), (15701, 128000), (31651, 256000),
  (319, 2560), (32149, 256000), (16199, 128000), (32647, 256000),
  (257, 2000), (6629, 51200)]

/-- 25 cells, about 2325 transcendental evaluations (field mode). -/
theorem q2F_x_002 :
    cellsOK (fieldUB q2D 2 vLogRF .x) (kxQ 2) q2F_x_002_b = true := by
  decide +kernel

/-- Breakpoints of cells 75..99 of piece `x` (q = 2). -/
def q2F_x_003_b : List QF := [
  (6629, 51200), (16697, 128000), (33643, 256000), (8473, 64000),
  (34141, 256000), (3439, 25600), (34639, 256000), (4361, 32000),
  (35137, 256000), (17693, 128000), (7127, 51200), (8971, 64000),
  (36133, 256000), (18191, 128000), (36631, 256000), (461, 3200),
  (37129, 256000), (18689, 128000), (37627, 256000), (9469, 64000),
  (305, 2048), (19187, 128000), (38623, 256000), (4859, 32000),
  (39121, 256000), (3937, 25600)]

/-- 25 cells, about 2325 transcendental evaluations (field mode). -/
theorem q2F_x_003 :
    cellsOK (fieldUB q2D 2 vLogRF .x) (kxQ 2) q2F_x_003_b = true := by
  decide +kernel

/-- Breakpoints of cells 100..124 of piece `x` (q = 2). -/
def q2F_x_004_b : List QF := [
  (3937, 25600), (39619, 256000), (9967, 64000), (40117, 256000),
  (20183, 128000), (8123, 51200), (1277, 8000), (41113, 256000),
  (20681, 128000), (41611, 256000), (2093, 12800), (42109, 256000),
  (21179, 128000), (42607, 256000), (5357, 32000), (8621, 51200),
  (21677, 128000), (43603, 256000), (10963, 64000), (44101, 256000),
  (887, 5120), (44599, 256000), (2803, 16000), (45097, 256000),
  (22673, 128000), (9119, 51200)]

/-- 25 cells, about 2325 transcendental evaluations (field mode). -/
theorem q2F_x_004 :
    cellsOK (fieldUB q2D 2 vLogRF .x) (kxQ 2) q2F_x_004_b = true := by
  decide +kernel

/-- Breakpoints of cells 125..149 of piece `x` (q = 2). -/
def q2F_x_005_b : List QF := [
  (9119, 51200), (11461, 64000), (46093, 256000), (23171, 128000),
  (46591, 256000), (1171, 6400), (47089, 256000), (23669, 128000),
  (47587, 256000), (11959, 64000), (9617, 51200), (24167, 128000),
  (48583, 256000), (763, 4000), (49081, 256000), (4933, 25600),
  (49579, 256000), (12457, 64000), (50077, 256000), (25163, 128000),
  (2023, 10240), (6353, 32000), (51073, 256000), (25661, 128000),
  (51571, 256000), (2591, 12800)]

/-- 25 cells, about 2325 transcendental evaluations (field mode). -/
theorem q2F_x_005 :
    cellsOK (fieldUB q2D 2 vLogRF .x) (kxQ 2) q2F_x_005_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
