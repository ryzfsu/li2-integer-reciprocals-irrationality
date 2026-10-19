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

/-- Breakpoints of cells 1092..1117 of piece `x` (q = 6). -/
def q6F_x_042_b : List QF := [
  (202559, 204800), (253261, 256000), (1013293, 1024000), (506771, 512000),
  (1013791, 1024000), (25351, 25600), (1014289, 1024000), (507269, 512000),
  (1014787, 1024000), (253759, 256000), (203057, 204800), (507767, 512000),
  (1015783, 1024000), (31751, 32000), (1016281, 1024000), (101653, 102400),
  (1016779, 1024000), (254257, 256000), (1017277, 1024000), (508763, 512000),
  (40711, 40960), (127253, 128000), (1018273, 1024000), (407359, 409600),
  (509261, 512000), (2037293, 2048000), (1018771, 1024000)]

/-- 26 cells, about 2392 transcendental evaluations (field mode). -/
theorem q6F_x_042 :
    cellsOK (fieldUB q6D 6 vLogRF .x) (kxQ 6) q6F_x_042_b = true := by
  decide +kernel

/-- Breakpoints of cells 1118..1143 of piece `x` (q = 6). -/
def q6F_x_043_b : List QF := [
  (1018771, 1024000), (2037791, 2048000), (50951, 51200), (2038289, 2048000),
  (1019269, 1024000), (509759, 512000), (1019767, 1024000), (63751, 64000),
  (204053, 204800), (510257, 512000), (1020763, 1024000), (255253, 256000),
  (2042273, 2048000), (1021261, 1024000), (2042771, 2048000), (102151, 102400),
  (2043269, 2048000), (1021759, 1024000), (2043767, 2048000), (127751, 128000),
  (408853, 409600), (4088779, 4096000), (1022257, 1024000), (4089277, 4096000),
  (2044763, 2048000), (163591, 163840), (511253, 512000)]

/-- 26 cells, about 2392 transcendental evaluations (field mode). -/
theorem q6F_x_043 :
    cellsOK (fieldUB q6D 6 vLogRF .x) (kxQ 6) q6F_x_043_b = true := by
  decide +kernel

/-- Breakpoints of cells 1144..1164 of piece `x` (q = 6). -/
def q6F_x_044_b : List QF := [
  (511253, 512000), (4090273, 4096000), (2045261, 2048000), (4090771, 4096000),
  (204551, 204800), (4091269, 4096000), (2045759, 2048000), (255751, 256000),
  (2046257, 2048000), (1023253, 1024000), (409351, 409600), (4093759, 4096000),
  (511751, 512000), (4094257, 4096000), (2047253, 2048000), (818951, 819200),
  (1023751, 1024000), (4095253, 4096000), (2047751, 2048000), (4095751, 4096000),
  (8191751, 8192000), (1, 1)]

/-- 21 cells, about 1932 transcendental evaluations (field mode). -/
theorem q6F_x_044 :
    cellsOK (fieldUB q6D 6 vLogRF .x) (kxQ 6) q6F_x_044_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
