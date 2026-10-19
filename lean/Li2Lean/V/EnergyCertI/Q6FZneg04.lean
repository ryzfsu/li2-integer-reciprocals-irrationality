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

/-- Breakpoints of cells 312..324 of piece `zneg` (q = 6). -/
def q6F_zneg_024_b : List QF := [
  (-6357, 1280), (-25401, 5120), (-12687, 2560), (-25347, 5120),
  (-633, 128), (-25293, 5120), (-12633, 2560), (-25239, 5120),
  (-6303, 1280), (-5037, 1024), (-12579, 2560), (-25131, 5120),
  (-1569, 320), (-25077, 5120)]

/-- 13 cells, about 2353 transcendental evaluations (field mode). -/
theorem q6F_zneg_024 :
    cellsOK (fieldUB q6D 6 vLogRF .zneg) (kzQ 6) q6F_zneg_024_b = true := by
  decide +kernel

/-- Breakpoints of cells 325..337 of piece `zneg` (q = 6). -/
def q6F_zneg_025_b : List QF := [
  (-25077, 5120), (-2505, 512), (-25023, 5120), (-6249, 1280),
  (-24969, 5120), (-12471, 2560), (-4983, 1024), (-3111, 640),
  (-24861, 5120), (-12417, 2560), (-24807, 5120), (-1239, 256),
  (-24753, 5120), (-12363, 2560)]

/-- 13 cells, about 2353 transcendental evaluations (field mode). -/
theorem q6F_zneg_025 :
    cellsOK (fieldUB q6D 6 vLogRF .zneg) (kzQ 6) q6F_zneg_025_b = true := by
  decide +kernel

/-- Breakpoints of cells 338..350 of piece `zneg` (q = 6). -/
def q6F_zneg_026_b : List QF := [
  (-12363, 2560), (-24699, 5120), (-771, 160), (-4929, 1024),
  (-12309, 2560), (-24591, 5120), (-6141, 1280), (-24537, 5120),
  (-2451, 512), (-24483, 5120), (-3057, 640), (-24429, 5120),
  (-12201, 2560), (-4875, 1024)]

/-- 13 cells, about 2353 transcendental evaluations (field mode). -/
theorem q6F_zneg_026 :
    cellsOK (fieldUB q6D 6 vLogRF .zneg) (kzQ 6) q6F_zneg_026_b = true := by
  decide +kernel

/-- Breakpoints of cells 351..363 of piece `zneg` (q = 6). -/
def q6F_zneg_027_b : List QF := [
  (-4875, 1024), (-6087, 1280), (-24321, 5120), (-12147, 2560),
  (-24267, 5120), (-303, 64), (-24213, 5120), (-12093, 2560),
  (-24159, 5120), (-6033, 1280), (-4821, 1024), (-12039, 2560),
  (-24051, 5120), (-3003, 640)]

/-- 13 cells, about 2353 transcendental evaluations (field mode). -/
theorem q6F_zneg_027 :
    cellsOK (fieldUB q6D 6 vLogRF .zneg) (kzQ 6) q6F_zneg_027_b = true := by
  decide +kernel

/-- Breakpoints of cells 364..376 of piece `zneg` (q = 6). -/
def q6F_zneg_028_b : List QF := [
  (-3003, 640), (-23997, 5120), (-2397, 512), (-23943, 5120),
  (-5979, 1280), (-23889, 5120), (-11931, 2560), (-4767, 1024),
  (-93, 20), (-23781, 5120), (-11877, 2560), (-23727, 5120),
  (-1185, 256), (-23673, 5120)]

/-- 13 cells, about 2353 transcendental evaluations (field mode). -/
theorem q6F_zneg_028 :
    cellsOK (fieldUB q6D 6 vLogRF .zneg) (kzQ 6) q6F_zneg_028_b = true := by
  decide +kernel

/-- Breakpoints of cells 377..389 of piece `zneg` (q = 6). -/
def q6F_zneg_029_b : List QF := [
  (-23673, 5120), (-11823, 2560), (-23619, 5120), (-2949, 640),
  (-4713, 1024), (-11769, 2560), (-23511, 5120), (-5871, 1280),
  (-23457, 5120), (-2343, 512), (-23403, 5120), (-1461, 320),
  (-23349, 5120), (-11661, 2560)]

/-- 13 cells, about 2353 transcendental evaluations (field mode). -/
theorem q6F_zneg_029 :
    cellsOK (fieldUB q6D 6 vLogRF .zneg) (kzQ 6) q6F_zneg_029_b = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
