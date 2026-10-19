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

/-- Breakpoints of cells 936..948 of piece `zneg` (q = 6). -/
def q6F_zneg_072_b : List QF := [
  (-429, 256), (-8553, 5120), (-4263, 2560), (-8499, 5120),
  (-1059, 640), (-1689, 1024), (-4209, 2560), (-8391, 5120),
  (-2091, 1280), (-8337, 5120), (-831, 512), (-8283, 5120),
  (-129, 80), (-8229, 5120)]

/-- 13 cells, about 2353 transcendental evaluations (field mode). -/
theorem q6F_zneg_072 :
    cellsOK (fieldUB q6D 6 vLogRF .zneg) (kzQ 6) q6F_zneg_072_b = true := by
  decide +kernel

/-- Breakpoints of cells 949..961 of piece `zneg` (q = 6). -/
def q6F_zneg_073_b : List QF := [
  (-8229, 5120), (-4101, 2560), (-1635, 1024), (-2037, 1280),
  (-8121, 5120), (-4047, 2560), (-8067, 5120), (-201, 128),
  (-8013, 5120), (-3993, 2560), (-7959, 5120), (-1983, 1280),
  (-1581, 1024), (-3939, 2560)]

/-- 13 cells, about 2353 transcendental evaluations (field mode). -/
theorem q6F_zneg_073 :
    cellsOK (fieldUB q6D 6 vLogRF .zneg) (kzQ 6) q6F_zneg_073_b = true := by
  decide +kernel

/-- Breakpoints of cells 962..974 of piece `zneg` (q = 6). -/
def q6F_zneg_074_b : List QF := [
  (-3939, 2560), (-7851, 5120), (-489, 320), (-7797, 5120),
  (-777, 512), (-7743, 5120), (-1929, 1280), (-7689, 5120),
  (-3831, 2560), (-1527, 1024), (-951, 640), (-7581, 5120),
  (-3777, 2560), (-7527, 5120)]

/-- 13 cells, about 2353 transcendental evaluations (field mode). -/
theorem q6F_zneg_074 :
    cellsOK (fieldUB q6D 6 vLogRF .zneg) (kzQ 6) q6F_zneg_074_b = true := by
  decide +kernel

/-- Breakpoints of cells 975..987 of piece `zneg` (q = 6). -/
def q6F_zneg_075_b : List QF := [
  (-7527, 5120), (-375, 256), (-7473, 5120), (-3723, 2560),
  (-7419, 5120), (-231, 160), (-1473, 1024), (-3669, 2560),
  (-7311, 5120), (-1821, 1280), (-7257, 5120), (-723, 512),
  (-7203, 5120), (-897, 640)]

/-- 13 cells, about 2353 transcendental evaluations (field mode). -/
theorem q6F_zneg_075 :
    cellsOK (fieldUB q6D 6 vLogRF .zneg) (kzQ 6) q6F_zneg_075_b = true := by
  decide +kernel

/-- Breakpoints of cells 988..1000 of piece `zneg` (q = 6). -/
def q6F_zneg_076_b : List QF := [
  (-897, 640), (-7149, 5120), (-3561, 2560), (-1419, 1024),
  (-1767, 1280), (-7041, 5120), (-3507, 2560), (-6987, 5120),
  (-87, 64), (-6933, 5120), (-3453, 2560), (-6879, 5120),
  (-1713, 1280), (-1365, 1024)]

/-- 13 cells, about 2353 transcendental evaluations (field mode). -/
theorem q6F_zneg_076 :
    cellsOK (fieldUB q6D 6 vLogRF .zneg) (kzQ 6) q6F_zneg_076_b = true := by
  decide +kernel

/-- Breakpoints of cells 1001..1013 of piece `zneg` (q = 6). -/
def q6F_zneg_077_b : List QF := [
  (-1365, 1024), (-3399, 2560), (-6771, 5120), (-843, 640),
  (-6717, 5120), (-669, 512), (-6663, 5120), (-1659, 1280),
  (-6609, 5120), (-3291, 2560), (-1311, 1024), (-51, 40),
  (-6501, 5120), (-3237, 2560)]

/-- 13 cells, about 2353 transcendental evaluations (field mode). -/
theorem q6F_zneg_077 :
    cellsOK (fieldUB q6D 6 vLogRF .zneg) (kzQ 6) q6F_zneg_077_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
