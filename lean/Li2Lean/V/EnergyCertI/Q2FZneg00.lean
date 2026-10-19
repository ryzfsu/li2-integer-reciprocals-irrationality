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

/-- Breakpoints of cells 0..11 of piece `zneg` (q = 2). -/
def q2F_zneg_000_b : List QF := [
  (-2, 1), (-81913, 40960), (-40953, 20480), (-81899, 40960),
  (-20473, 10240), (-40939, 20480), (-10233, 5120), (-8185, 4096),
  (-20459, 10240), (-40911, 20480), (-5113, 2560), (-40897, 20480),
  (-4089, 2048)]

/-- 12 cells, about 2280 transcendental evaluations (field mode). -/
theorem q2F_zneg_000 :
    cellsOK (fieldUB q2D 2 vLogRF .zneg) (kzQ 2) q2F_zneg_000_b = true := by
  decide +kernel

/-- Breakpoints of cells 12..23 of piece `zneg` (q = 2). -/
def q2F_zneg_001_b : List QF := [
  (-4089, 2048), (-40883, 20480), (-10219, 5120), (-20431, 10240),
  (-2553, 1280), (-20417, 10240), (-2041, 1024), (-20403, 10240),
  (-5099, 2560), (-20389, 10240), (-10191, 5120), (-4075, 2048),
  (-1273, 640)]

/-- 12 cells, about 2280 transcendental evaluations (field mode). -/
theorem q2F_zneg_001 :
    cellsOK (fieldUB q2D 2 vLogRF .zneg) (kzQ 2) q2F_zneg_001_b = true := by
  decide +kernel

/-- Breakpoints of cells 24..35 of piece `zneg` (q = 2). -/
def q2F_zneg_002_b : List QF := [
  (-1273, 640), (-20361, 10240), (-10177, 5120), (-20347, 10240),
  (-1017, 512), (-20333, 10240), (-10163, 5120), (-20319, 10240),
  (-2539, 1280), (-4061, 2048), (-10149, 5120), (-20291, 10240),
  (-5071, 2560)]

/-- 12 cells, about 2280 transcendental evaluations (field mode). -/
theorem q2F_zneg_002 :
    cellsOK (fieldUB q2D 2 vLogRF .zneg) (kzQ 2) q2F_zneg_002_b = true := by
  decide +kernel

/-- Breakpoints of cells 36..47 of piece `zneg` (q = 2). -/
def q2F_zneg_003_b : List QF := [
  (-5071, 2560), (-20277, 10240), (-2027, 1024), (-20263, 10240),
  (-633, 320), (-20249, 10240), (-10121, 5120), (-4047, 2048),
  (-5057, 2560), (-20221, 10240), (-10107, 5120), (-20207, 10240),
  (-505, 256)]

/-- 12 cells, about 2280 transcendental evaluations (field mode). -/
theorem q2F_zneg_003 :
    cellsOK (fieldUB q2D 2 vLogRF .zneg) (kzQ 2) q2F_zneg_003_b = true := by
  decide +kernel

/-- Breakpoints of cells 48..59 of piece `zneg` (q = 2). -/
def q2F_zneg_004_b : List QF := [
  (-505, 256), (-20193, 10240), (-10093, 5120), (-20179, 10240),
  (-5043, 2560), (-4033, 2048), (-10079, 5120), (-20151, 10240),
  (-1259, 640), (-2013, 1024), (-5029, 2560), (-10051, 5120),
  (-2511, 1280)]

/-- 12 cells, about 2280 transcendental evaluations (field mode). -/
theorem q2F_zneg_004 :
    cellsOK (fieldUB q2D 2 vLogRF .zneg) (kzQ 2) q2F_zneg_004_b = true := by
  decide +kernel

/-- Breakpoints of cells 60..71 of piece `zneg` (q = 2). -/
def q2F_zneg_005_b : List QF := [
  (-2511, 1280), (-10037, 5120), (-1003, 512), (-10023, 5120),
  (-313, 160), (-10009, 5120), (-5001, 2560), (-1999, 1024),
  (-2497, 1280), (-9981, 5120), (-4987, 2560), (-9967, 5120),
  (-249, 128)]

/-- 12 cells, about 2280 transcendental evaluations (field mode). -/
theorem q2F_zneg_005 :
    cellsOK (fieldUB q2D 2 vLogRF .zneg) (kzQ 2) q2F_zneg_005_b = true := by
  decide +kernel

/-- Breakpoints of cells 72..83 of piece `zneg` (q = 2). -/
def q2F_zneg_006_b : List QF := [
  (-249, 128), (-9953, 5120), (-4973, 2560), (-9939, 5120),
  (-2483, 1280), (-1985, 1024), (-4959, 2560), (-9911, 5120),
  (-619, 320), (-9897, 5120), (-989, 512), (-9883, 5120),
  (-2469, 1280)]

/-- 12 cells, about 2280 transcendental evaluations (field mode). -/
theorem q2F_zneg_006 :
    cellsOK (fieldUB q2D 2 vLogRF .zneg) (kzQ 2) q2F_zneg_006_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
