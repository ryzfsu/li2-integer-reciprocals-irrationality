/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
/-
Generated certificate data
from v13 `v-reference-data.tex` (sha256 e3983e04...cd9b).  elaborated.
-/

import Li2Lean.V.EnergyCertI.Q5Rows
import Li2Lean.V.EnergyCertI.Consts

namespace Li2Lean.V.EnergyCertI

open IK

/-- Breakpoints of cells 234..246 of piece `zneg` (q = 5). -/
def q5F_zneg_018_b : List QF := [
  (-2263, 512), (-1413, 320), (-11293, 2560), (-5641, 1280),
  (-11271, 2560), (-563, 128), (-11249, 2560), (-5619, 1280),
  (-11227, 2560), (-701, 160), (-2241, 512), (-5597, 1280),
  (-11183, 2560), (-2793, 640)]

/-- 13 cells, about 2392 transcendental evaluations (field mode). -/
theorem q5F_zneg_018 :
    cellsOK (fieldUB q5D 5 vLogRF .zneg) (kzQ 5) q5F_zneg_018_b = true := by
  decide +kernel

/-- Breakpoints of cells 247..259 of piece `zneg` (q = 5). -/
def q5F_zneg_019_b : List QF := [
  (-2793, 640), (-11161, 2560), (-1115, 256), (-11139, 2560),
  (-1391, 320), (-11117, 2560), (-5553, 1280), (-2219, 512),
  (-2771, 640), (-11073, 2560), (-5531, 1280), (-11051, 2560),
  (-69, 16), (-11029, 2560)]

/-- 13 cells, about 2392 transcendental evaluations (field mode). -/
theorem q5F_zneg_019 :
    cellsOK (fieldUB q5D 5 vLogRF .zneg) (kzQ 5) q5F_zneg_019_b = true := by
  decide +kernel

/-- Breakpoints of cells 260..272 of piece `zneg` (q = 5). -/
def q5F_zneg_020_b : List QF := [
  (-11029, 2560), (-5509, 1280), (-11007, 2560), (-2749, 640),
  (-2197, 512), (-5487, 1280), (-10963, 2560), (-1369, 320),
  (-10941, 2560), (-1093, 256), (-10919, 2560), (-2727, 640),
  (-10897, 2560), (-5443, 1280)]

/-- 13 cells, about 2392 transcendental evaluations (field mode). -/
theorem q5F_zneg_020 :
    cellsOK (fieldUB q5D 5 vLogRF .zneg) (kzQ 5) q5F_zneg_020_b = true := by
  decide +kernel

/-- Breakpoints of cells 273..285 of piece `zneg` (q = 5). -/
def q5F_zneg_021_b : List QF := [
  (-5443, 1280), (-2175, 512), (-679, 160), (-10853, 2560),
  (-5421, 1280), (-10831, 2560), (-541, 128), (-10809, 2560),
  (-5399, 1280), (-10787, 2560), (-1347, 320), (-2153, 512),
  (-5377, 1280), (-10743, 2560)]

/-- 13 cells, about 2392 transcendental evaluations (field mode). -/
theorem q5F_zneg_021 :
    cellsOK (fieldUB q5D 5 vLogRF .zneg) (kzQ 5) q5F_zneg_021_b = true := by
  decide +kernel

/-- Breakpoints of cells 286..298 of piece `zneg` (q = 5). -/
def q5F_zneg_022_b : List QF := [
  (-10743, 2560), (-2683, 640), (-10721, 2560), (-1071, 256),
  (-10699, 2560), (-167, 40), (-10677, 2560), (-5333, 1280),
  (-2131, 512), (-2661, 640), (-10633, 2560), (-5311, 1280),
  (-10611, 2560), (-265, 64)]

/-- 13 cells, about 2392 transcendental evaluations (field mode). -/
theorem q5F_zneg_022 :
    cellsOK (fieldUB q5D 5 vLogRF .zneg) (kzQ 5) q5F_zneg_022_b = true := by
  decide +kernel

/-- Breakpoints of cells 299..311 of piece `zneg` (q = 5). -/
def q5F_zneg_023_b : List QF := [
  (-265, 64), (-10589, 2560), (-5289, 1280), (-10567, 2560),
  (-2639, 640), (-2109, 512), (-5267, 1280), (-10523, 2560),
  (-657, 160), (-10501, 2560), (-1049, 256), (-10479, 2560),
  (-2617, 640), (-10457, 2560)]

/-- 13 cells, about 2392 transcendental evaluations (field mode). -/
theorem q5F_zneg_023 :
    cellsOK (fieldUB q5D 5 vLogRF .zneg) (kzQ 5) q5F_zneg_023_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
