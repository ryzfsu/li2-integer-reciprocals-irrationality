/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
/-
Generated certificate data
from v13 `v-reference-data.tex` (sha256 e3983e04...cd9b).  elaborated.
-/

import Li2Lean.V.EnergyCertI.Q7Rows
import Li2Lean.V.EnergyCertI.Consts

namespace Li2Lean.V.EnergyCertI

open IK

/-- Breakpoints of cells 0..12 of piece `zneg` (q = 7). -/
def q7F_zneg_000_b : List QF := [
  (-7, 1), (-17919, 2560), (-8959, 1280), (-17917, 2560),
  (-4479, 640), (-3583, 512), (-8957, 1280), (-2239, 320),
  (-1791, 256), (-4477, 640), (-8953, 1280), (-1119, 160),
  (-8951, 1280), (-895, 128)]

/-- 13 cells, about 2340 transcendental evaluations (field mode). -/
theorem q7F_zneg_000 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_000_b = true := by
  decide +kernel

/-- Breakpoints of cells 13..25 of piece `zneg` (q = 7). -/
def q7F_zneg_001_b : List QF := [
  (-895, 128), (-8949, 1280), (-2237, 320), (-8947, 1280),
  (-4473, 640), (-1789, 256), (-559, 80), (-8943, 1280),
  (-4471, 640), (-8941, 1280), (-447, 64), (-4469, 640),
  (-1117, 160), (-4467, 640)]

/-- 13 cells, about 2340 transcendental evaluations (field mode). -/
theorem q7F_zneg_001 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_001_b = true := by
  decide +kernel

/-- Breakpoints of cells 26..38 of piece `zneg` (q = 7). -/
def q7F_zneg_002_b : List QF := [
  (-4467, 640), (-2233, 320), (-893, 128), (-279, 40),
  (-4463, 640), (-2231, 320), (-4461, 640), (-223, 32),
  (-4459, 640), (-2229, 320), (-4457, 640), (-557, 80),
  (-891, 128), (-2227, 320)]

/-- 13 cells, about 2340 transcendental evaluations (field mode). -/
theorem q7F_zneg_002 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_002_b = true := by
  decide +kernel

/-- Breakpoints of cells 39..51 of piece `zneg` (q = 7). -/
def q7F_zneg_003_b : List QF := [
  (-2227, 320), (-4453, 640), (-1113, 160), (-4451, 640),
  (-445, 64), (-4449, 640), (-139, 20), (-4447, 640),
  (-2223, 320), (-889, 128), (-1111, 160), (-4443, 640),
  (-2221, 320), (-4441, 640)]

/-- 13 cells, about 2340 transcendental evaluations (field mode). -/
theorem q7F_zneg_003 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_003_b = true := by
  decide +kernel

/-- Breakpoints of cells 52..64 of piece `zneg` (q = 7). -/
def q7F_zneg_004_b : List QF := [
  (-4441, 640), (-111, 16), (-4439, 640), (-2219, 320),
  (-4437, 640), (-1109, 160), (-887, 128), (-2217, 320),
  (-4433, 640), (-277, 40), (-4431, 640), (-443, 64),
  (-4429, 640), (-1107, 160)]

/-- 13 cells, about 2340 transcendental evaluations (field mode). -/
theorem q7F_zneg_004 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_004_b = true := by
  decide +kernel

/-- Breakpoints of cells 65..77 of piece `zneg` (q = 7). -/
def q7F_zneg_005_b : List QF := [
  (-1107, 160), (-4427, 640), (-2213, 320), (-553, 80),
  (-2211, 320), (-221, 32), (-2209, 320), (-69, 10),
  (-2207, 320), (-1103, 160), (-441, 64), (-551, 80),
  (-2203, 320), (-1101, 160)]

/-- 13 cells, about 2340 transcendental evaluations (field mode). -/
theorem q7F_zneg_005 :
    cellsOK (fieldUB q7D 7 vLogRF .zneg) (kzQ 7) q7F_zneg_005_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
