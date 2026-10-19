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

/-- Breakpoints of cells 234..246 of piece `zneg` (q = 6). -/
def q6F_zneg_018_b : List QF := [
  (-13767, 2560), (-27507, 5120), (-687, 128), (-27453, 5120),
  (-13713, 2560), (-27399, 5120), (-6843, 1280), (-5469, 1024),
  (-13659, 2560), (-27291, 5120), (-213, 40), (-27237, 5120),
  (-2721, 512), (-27183, 5120)]

/-- 13 cells, about 2353 transcendental evaluations (field mode). -/
theorem q6F_zneg_018 :
    cellsOK (fieldUB q6D 6 vLogRF .zneg) (kzQ 6) q6F_zneg_018_b = true := by
  decide +kernel

/-- Breakpoints of cells 247..259 of piece `zneg` (q = 6). -/
def q6F_zneg_019_b : List QF := [
  (-27183, 5120), (-6789, 1280), (-27129, 5120), (-13551, 2560),
  (-5415, 1024), (-3381, 640), (-27021, 5120), (-13497, 2560),
  (-26967, 5120), (-1347, 256), (-26913, 5120), (-13443, 2560),
  (-26859, 5120), (-1677, 320)]

/-- 13 cells, about 2353 transcendental evaluations (field mode). -/
theorem q6F_zneg_019 :
    cellsOK (fieldUB q6D 6 vLogRF .zneg) (kzQ 6) q6F_zneg_019_b = true := by
  decide +kernel

/-- Breakpoints of cells 260..272 of piece `zneg` (q = 6). -/
def q6F_zneg_020_b : List QF := [
  (-1677, 320), (-5361, 1024), (-13389, 2560), (-26751, 5120),
  (-6681, 1280), (-26697, 5120), (-2667, 512), (-26643, 5120),
  (-3327, 640), (-26589, 5120), (-13281, 2560), (-5307, 1024),
  (-6627, 1280), (-26481, 5120)]

/-- 13 cells, about 2353 transcendental evaluations (field mode). -/
theorem q6F_zneg_020 :
    cellsOK (fieldUB q6D 6 vLogRF .zneg) (kzQ 6) q6F_zneg_020_b = true := by
  decide +kernel

/-- Breakpoints of cells 273..285 of piece `zneg` (q = 6). -/
def q6F_zneg_021_b : List QF := [
  (-26481, 5120), (-13227, 2560), (-26427, 5120), (-165, 32),
  (-26373, 5120), (-13173, 2560), (-26319, 5120), (-6573, 1280),
  (-5253, 1024), (-13119, 2560), (-26211, 5120), (-3273, 640),
  (-26157, 5120), (-2613, 512)]

/-- 13 cells, about 2353 transcendental evaluations (field mode). -/
theorem q6F_zneg_021 :
    cellsOK (fieldUB q6D 6 vLogRF .zneg) (kzQ 6) q6F_zneg_021_b = true := by
  decide +kernel

/-- Breakpoints of cells 286..298 of piece `zneg` (q = 6). -/
def q6F_zneg_022_b : List QF := [
  (-2613, 512), (-26103, 5120), (-6519, 1280), (-26049, 5120),
  (-13011, 2560), (-5199, 1024), (-1623, 320), (-25941, 5120),
  (-12957, 2560), (-25887, 5120), (-1293, 256), (-25833, 5120),
  (-12903, 2560), (-25779, 5120)]

/-- 13 cells, about 2353 transcendental evaluations (field mode). -/
theorem q6F_zneg_022 :
    cellsOK (fieldUB q6D 6 vLogRF .zneg) (kzQ 6) q6F_zneg_022_b = true := by
  decide +kernel

/-- Breakpoints of cells 299..311 of piece `zneg` (q = 6). -/
def q6F_zneg_023_b : List QF := [
  (-25779, 5120), (-3219, 640), (-5145, 1024), (-12849, 2560),
  (-25671, 5120), (-6411, 1280), (-25617, 5120), (-2559, 512),
  (-25563, 5120), (-399, 80), (-25509, 5120), (-12741, 2560),
  (-5091, 1024), (-6357, 1280)]

/-- 13 cells, about 2353 transcendental evaluations (field mode). -/
theorem q6F_zneg_023 :
    cellsOK (fieldUB q6D 6 vLogRF .zneg) (kzQ 6) q6F_zneg_023_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
