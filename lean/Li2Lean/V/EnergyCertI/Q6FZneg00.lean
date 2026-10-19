/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
/-
Generated certificate data
from v13 `v-reference-data.tex` (sha256 e3983e04...cd9b).  elaborated.
-/

import Li2Lean.V.EnergyCertI.Q6Rows
import Li2Lean.V.EnergyCertI.Consts

namespace Li2Lean.V.EnergyCertI

open IK

/-- Breakpoints of cells 0..12 of piece `zneg` (q = 6). -/
def q6F_zneg_000_b : List QF := [
  (-6, 1), (-491493, 81920), (-245733, 40960), (-491439, 81920),
  (-122853, 20480), (-245679, 40960), (-61413, 10240), (-49125, 8192),
  (-122799, 20480), (-245571, 40960), (-30693, 5120), (-245517, 40960),
  (-24549, 4096), (-245463, 40960)]

/-- 13 cells, about 2353 transcendental evaluations (field mode). -/
theorem q6F_zneg_000 :
    cellsOK (fieldUB q6D 6 vLogRF .zneg) (kzQ 6) q6F_zneg_000_b = true := by
  decide +kernel

/-- Breakpoints of cells 13..25 of piece `zneg` (q = 6). -/
def q6F_zneg_001_b : List QF := [
  (-245463, 40960), (-61359, 10240), (-245409, 40960), (-122691, 20480),
  (-49071, 8192), (-15333, 2560), (-245301, 40960), (-122637, 20480),
  (-245247, 40960), (-12261, 2048), (-122583, 20480), (-30639, 5120),
  (-122529, 20480), (-61251, 10240)]

/-- 13 cells, about 2353 transcendental evaluations (field mode). -/
theorem q6F_zneg_001 :
    cellsOK (fieldUB q6D 6 vLogRF .zneg) (kzQ 6) q6F_zneg_001_b = true := by
  decide +kernel

/-- Breakpoints of cells 26..38 of piece `zneg` (q = 6). -/
def q6F_zneg_002_b : List QF := [
  (-61251, 10240), (-24495, 4096), (-7653, 1280), (-122421, 20480),
  (-61197, 10240), (-122367, 20480), (-6117, 1024), (-122313, 20480),
  (-61143, 10240), (-122259, 20480), (-15279, 2560), (-24441, 4096),
  (-61089, 10240), (-122151, 20480)]

/-- 13 cells, about 2353 transcendental evaluations (field mode). -/
theorem q6F_zneg_002 :
    cellsOK (fieldUB q6D 6 vLogRF .zneg) (kzQ 6) q6F_zneg_002_b = true := by
  decide +kernel

/-- Breakpoints of cells 39..51 of piece `zneg` (q = 6). -/
def q6F_zneg_003_b : List QF := [
  (-122151, 20480), (-30531, 5120), (-122097, 20480), (-12207, 2048),
  (-122043, 20480), (-3813, 640), (-121989, 20480), (-60981, 10240),
  (-24387, 4096), (-30477, 5120), (-121881, 20480), (-60927, 10240),
  (-121827, 20480), (-3045, 512)]

/-- 13 cells, about 2353 transcendental evaluations (field mode). -/
theorem q6F_zneg_003 :
    cellsOK (fieldUB q6D 6 vLogRF .zneg) (kzQ 6) q6F_zneg_003_b = true := by
  decide +kernel

/-- Breakpoints of cells 52..64 of piece `zneg` (q = 6). -/
def q6F_zneg_004_b : List QF := [
  (-3045, 512), (-121773, 20480), (-60873, 10240), (-121719, 20480),
  (-30423, 5120), (-24333, 4096), (-60819, 10240), (-121611, 20480),
  (-7599, 1280), (-121557, 20480), (-12153, 2048), (-121503, 20480),
  (-30369, 5120), (-60711, 10240)]

/-- 13 cells, about 2353 transcendental evaluations (field mode). -/
theorem q6F_zneg_004 :
    cellsOK (fieldUB q6D 6 vLogRF .zneg) (kzQ 6) q6F_zneg_004_b = true := by
  decide +kernel

/-- Breakpoints of cells 65..77 of piece `zneg` (q = 6). -/
def q6F_zneg_005_b : List QF := [
  (-60711, 10240), (-15171, 2560), (-60657, 10240), (-6063, 1024),
  (-60603, 10240), (-1893, 320), (-60549, 10240), (-30261, 5120),
  (-12099, 2048), (-15117, 2560), (-60441, 10240), (-30207, 5120),
  (-60387, 10240), (-1509, 256)]

/-- 13 cells, about 2353 transcendental evaluations (field mode). -/
theorem q6F_zneg_005 :
    cellsOK (fieldUB q6D 6 vLogRF .zneg) (kzQ 6) q6F_zneg_005_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
