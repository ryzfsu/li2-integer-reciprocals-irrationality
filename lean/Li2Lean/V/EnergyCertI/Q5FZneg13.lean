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

/-- Breakpoints of cells 1014..1026 of piece `zneg` (q = 5). -/
def q5F_zneg_078_b : List QF := [
  (-547, 512), (-681, 640), (-2713, 2560), (-1351, 1280),
  (-2691, 2560), (-67, 64), (-2669, 2560), (-1329, 1280),
  (-2647, 2560), (-659, 640), (-525, 512), (-1307, 1280),
  (-2603, 2560), (-81, 80)]

/-- 13 cells, about 2392 transcendental evaluations (field mode). -/
theorem q5F_zneg_078 :
    cellsOK (fieldUB q5D 5 vLogRF .zneg) (kzQ 5) q5F_zneg_078_b = true := by
  decide +kernel

/-- Breakpoints of cells 1027..1039 of piece `zneg` (q = 5). -/
def q5F_zneg_079_b : List QF := [
  (-81, 80), (-2581, 2560), (-257, 256), (-2559, 2560),
  (-637, 640), (-2537, 2560), (-1263, 1280), (-503, 512),
  (-313, 320), (-2493, 2560), (-1241, 1280), (-2471, 2560),
  (-123, 128), (-2449, 2560)]

/-- 13 cells, about 2392 transcendental evaluations (field mode). -/
theorem q5F_zneg_079 :
    cellsOK (fieldUB q5D 5 vLogRF .zneg) (kzQ 5) q5F_zneg_079_b = true := by
  decide +kernel

/-- Breakpoints of cells 1040..1052 of piece `zneg` (q = 5). -/
def q5F_zneg_080_b : List QF := [
  (-2449, 2560), (-1219, 1280), (-2427, 2560), (-151, 160),
  (-481, 512), (-1197, 1280), (-2383, 2560), (-593, 640),
  (-2361, 2560), (-235, 256), (-2339, 2560), (-291, 320),
  (-2317, 2560), (-1153, 1280)]

/-- 13 cells, about 2392 transcendental evaluations (field mode). -/
theorem q5F_zneg_080 :
    cellsOK (fieldUB q5D 5 vLogRF .zneg) (kzQ 5) q5F_zneg_080_b = true := by
  decide +kernel

/-- Breakpoints of cells 1053..1065 of piece `zneg` (q = 5). -/
def q5F_zneg_081_b : List QF := [
  (-1153, 1280), (-459, 512), (-571, 640), (-2273, 2560),
  (-1131, 1280), (-2251, 2560), (-7, 8), (-2229, 2560),
  (-1109, 1280), (-2207, 2560), (-549, 640), (-437, 512),
  (-1087, 1280), (-2163, 2560)]

/-- 13 cells, about 2392 transcendental evaluations (field mode). -/
theorem q5F_zneg_081 :
    cellsOK (fieldUB q5D 5 vLogRF .zneg) (kzQ 5) q5F_zneg_081_b = true := by
  decide +kernel

/-- Breakpoints of cells 1066..1078 of piece `zneg` (q = 5). -/
def q5F_zneg_082_b : List QF := [
  (-2163, 2560), (-269, 320), (-2141, 2560), (-213, 256),
  (-2119, 2560), (-527, 640), (-2097, 2560), (-1043, 1280),
  (-415, 512), (-129, 160), (-2053, 2560), (-1021, 1280),
  (-2031, 2560), (-101, 128)]

/-- 13 cells, about 2392 transcendental evaluations (field mode). -/
theorem q5F_zneg_082 :
    cellsOK (fieldUB q5D 5 vLogRF .zneg) (kzQ 5) q5F_zneg_082_b = true := by
  decide +kernel

/-- Breakpoints of cells 1079..1091 of piece `zneg` (q = 5). -/
def q5F_zneg_083_b : List QF := [
  (-101, 128), (-2009, 2560), (-999, 1280), (-1987, 2560),
  (-247, 320), (-393, 512), (-977, 1280), (-1943, 2560),
  (-483, 640), (-1921, 2560), (-191, 256), (-1899, 2560),
  (-59, 80), (-1877, 2560)]

/-- 13 cells, about 2392 transcendental evaluations (field mode). -/
theorem q5F_zneg_083 :
    cellsOK (fieldUB q5D 5 vLogRF .zneg) (kzQ 5) q5F_zneg_083_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
