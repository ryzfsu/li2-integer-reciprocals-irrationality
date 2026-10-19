/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
/-
Generated certificate data
from v13 `v-reference-data.tex` (sha256 e3983e04...cd9b).  elaborated.
-/

import Li2Lean.V.EnergyCertI.Q4Rows
import Li2Lean.V.EnergyCertI.Consts

namespace Li2Lean.V.EnergyCertI

open IK

/-- Breakpoints of cells 0..11 of piece `zneg` (q = 4). -/
def q4F_zneg_000_b : List QF := [
  (-4, 1), (-327663, 81920), (-163823, 40960), (-81903, 20480),
  (-163789, 40960), (-40943, 10240), (-32751, 8192), (-81869, 20480),
  (-163721, 40960), (-20463, 5120), (-163687, 40960), (-16367, 4096),
  (-163653, 40960)]

/-- 12 cells, about 2232 transcendental evaluations (field mode). -/
theorem q4F_zneg_000 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_000_b = true := by
  decide +kernel

/-- Breakpoints of cells 12..23 of piece `zneg` (q = 4). -/
def q4F_zneg_001_b : List QF := [
  (-163653, 40960), (-40909, 10240), (-163619, 40960), (-81801, 20480),
  (-32717, 8192), (-10223, 2560), (-81767, 20480), (-8175, 2048),
  (-81733, 20480), (-20429, 5120), (-81699, 20480), (-40841, 10240),
  (-16333, 4096)]

/-- 12 cells, about 2232 transcendental evaluations (field mode). -/
theorem q4F_zneg_001 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_001_b = true := by
  decide +kernel

/-- Breakpoints of cells 24..35 of piece `zneg` (q = 4). -/
def q4F_zneg_002_b : List QF := [
  (-16333, 4096), (-5103, 1280), (-81631, 20480), (-40807, 10240),
  (-81597, 20480), (-4079, 1024), (-81563, 20480), (-40773, 10240),
  (-81529, 20480), (-10189, 2560), (-16299, 4096), (-40739, 10240),
  (-81461, 20480)]

/-- 12 cells, about 2232 transcendental evaluations (field mode). -/
theorem q4F_zneg_002 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_002_b = true := by
  decide +kernel

/-- Breakpoints of cells 36..47 of piece `zneg` (q = 4). -/
def q4F_zneg_003_b : List QF := [
  (-81461, 20480), (-20361, 5120), (-81427, 20480), (-8141, 2048),
  (-2543, 640), (-40671, 10240), (-20327, 5120), (-40637, 10240),
  (-2031, 512), (-40603, 10240), (-20293, 5120), (-40569, 10240),
  (-5069, 1280)]

/-- 12 cells, about 2232 transcendental evaluations (field mode). -/
theorem q4F_zneg_003 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_003_b = true := by
  decide +kernel

/-- Breakpoints of cells 48..59 of piece `zneg` (q = 4). -/
def q4F_zneg_004_b : List QF := [
  (-5069, 1280), (-8107, 2048), (-20259, 5120), (-40501, 10240),
  (-10121, 2560), (-40467, 10240), (-4045, 1024), (-40433, 10240),
  (-1263, 320), (-40399, 10240), (-20191, 5120), (-8073, 2048),
  (-10087, 2560)]

/-- 12 cells, about 2232 transcendental evaluations (field mode). -/
theorem q4F_zneg_004 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_004_b = true := by
  decide +kernel

/-- Breakpoints of cells 60..71 of piece `zneg` (q = 4). -/
def q4F_zneg_005_b : List QF := [
  (-10087, 2560), (-40331, 10240), (-20157, 5120), (-40297, 10240),
  (-1007, 256), (-40263, 10240), (-20123, 5120), (-40229, 10240),
  (-10053, 2560), (-8039, 2048), (-20089, 5120), (-40161, 10240),
  (-2509, 640)]

/-- 12 cells, about 2232 transcendental evaluations (field mode). -/
theorem q4F_zneg_005 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_005_b = true := by
  decide +kernel

/-- Breakpoints of cells 72..83 of piece `zneg` (q = 4). -/
def q4F_zneg_006_b : List QF := [
  (-2509, 640), (-40127, 10240), (-4011, 1024), (-40093, 10240),
  (-10019, 2560), (-40059, 10240), (-20021, 5120), (-8005, 2048),
  (-5001, 1280), (-39991, 10240), (-19987, 5120), (-39957, 10240),
  (-1997, 512)]

/-- 12 cells, about 2232 transcendental evaluations (field mode). -/
theorem q4F_zneg_006 :
    cellsOK (fieldUB q4D 4 vLogRF .zneg) (kzQ 4) q4F_zneg_006_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
