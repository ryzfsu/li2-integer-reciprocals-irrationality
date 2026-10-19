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

/-- Breakpoints of cells 624..636 of piece `zneg` (q = 6). -/
def q6F_zneg_048_b : List QF := [
  (-4251, 1280), (-16977, 5120), (-1695, 512), (-16923, 5120),
  (-33, 10), (-16869, 5120), (-8421, 2560), (-3363, 1024),
  (-4197, 1280), (-16761, 5120), (-8367, 2560), (-16707, 5120),
  (-417, 128), (-16653, 5120)]

/-- 13 cells, about 2353 transcendental evaluations (field mode). -/
theorem q6F_zneg_048 :
    cellsOK (fieldUB q6D 6 vLogRF .zneg) (kzQ 6) q6F_zneg_048_b = true := by
  decide +kernel

/-- Breakpoints of cells 637..649 of piece `zneg` (q = 6). -/
def q6F_zneg_049_b : List QF := [
  (-16653, 5120), (-8313, 2560), (-16599, 5120), (-4143, 1280),
  (-3309, 1024), (-8259, 2560), (-16491, 5120), (-1029, 320),
  (-16437, 5120), (-1641, 512), (-16383, 5120), (-4089, 1280),
  (-16329, 5120), (-8151, 2560)]

/-- 13 cells, about 2353 transcendental evaluations (field mode). -/
theorem q6F_zneg_049 :
    cellsOK (fieldUB q6D 6 vLogRF .zneg) (kzQ 6) q6F_zneg_049_b = true := by
  decide +kernel

/-- Breakpoints of cells 650..662 of piece `zneg` (q = 6). -/
def q6F_zneg_050_b : List QF := [
  (-8151, 2560), (-3255, 1024), (-2031, 640), (-16221, 5120),
  (-8097, 2560), (-16167, 5120), (-807, 256), (-16113, 5120),
  (-8043, 2560), (-16059, 5120), (-501, 160), (-3201, 1024),
  (-7989, 2560), (-15951, 5120)]

/-- 13 cells, about 2353 transcendental evaluations (field mode). -/
theorem q6F_zneg_050 :
    cellsOK (fieldUB q6D 6 vLogRF .zneg) (kzQ 6) q6F_zneg_050_b = true := by
  decide +kernel

/-- Breakpoints of cells 663..675 of piece `zneg` (q = 6). -/
def q6F_zneg_051_b : List QF := [
  (-15951, 5120), (-3981, 1280), (-15897, 5120), (-1587, 512),
  (-15843, 5120), (-1977, 640), (-15789, 5120), (-7881, 2560),
  (-3147, 1024), (-3927, 1280), (-15681, 5120), (-7827, 2560),
  (-15627, 5120), (-195, 64)]

/-- 13 cells, about 2353 transcendental evaluations (field mode). -/
theorem q6F_zneg_051 :
    cellsOK (fieldUB q6D 6 vLogRF .zneg) (kzQ 6) q6F_zneg_051_b = true := by
  decide +kernel

/-- Breakpoints of cells 676..688 of piece `zneg` (q = 6). -/
def q6F_zneg_052_b : List QF := [
  (-195, 64), (-15573, 5120), (-7773, 2560), (-15519, 5120),
  (-3873, 1280), (-3093, 1024), (-7719, 2560), (-15411, 5120),
  (-1923, 640), (-15357, 5120), (-1533, 512), (-15303, 5120),
  (-3819, 1280), (-15249, 5120)]

/-- 13 cells, about 2353 transcendental evaluations (field mode). -/
theorem q6F_zneg_052 :
    cellsOK (fieldUB q6D 6 vLogRF .zneg) (kzQ 6) q6F_zneg_052_b = true := by
  decide +kernel

/-- Breakpoints of cells 689..701 of piece `zneg` (q = 6). -/
def q6F_zneg_053_b : List QF := [
  (-15249, 5120), (-7611, 2560), (-3039, 1024), (-237, 80),
  (-15141, 5120), (-7557, 2560), (-15087, 5120), (-753, 256),
  (-15033, 5120), (-7503, 2560), (-14979, 5120), (-1869, 640),
  (-2985, 1024), (-7449, 2560)]

/-- 13 cells, about 2353 transcendental evaluations (field mode). -/
theorem q6F_zneg_053 :
    cellsOK (fieldUB q6D 6 vLogRF .zneg) (kzQ 6) q6F_zneg_053_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
