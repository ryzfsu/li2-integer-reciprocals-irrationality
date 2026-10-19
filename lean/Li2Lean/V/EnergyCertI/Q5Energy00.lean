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

/-- 780 transcendental evaluations (energy mode). -/
theorem q5E_selfX_0_40 :
    energyShardOK q5D 5 vLogRE .selfX 0 40 (-28811670653696480874) = true := by
  decide +kernel

/-- 1176 transcendental evaluations (energy mode). -/
theorem q5E_selfV_0_49 :
    energyShardOK q5D 5 vLogRE .selfV 0 49 (-41341108288904296042) = true := by
  decide +kernel

/-- 1488 transcendental evaluations (energy mode). -/
theorem q5E_selfZ_0_32 :
    energyShardOK q5D 5 vLogRE .selfZ 0 32 (-774139004861776397) = true := by
  decide +kernel

/-- 465 transcendental evaluations (energy mode). -/
theorem q5E_selfZ_32_63 :
    energyShardOK q5D 5 vLogRE .selfZ 32 63 (59967029142272546) = true := by
  decide +kernel

/-- 1449 transcendental evaluations (energy mode). -/
theorem q5E_crossVZ_0_23 :
    energyShardOK q5D 5 vLogRE .crossVZ 0 23 (-10535133104076533992) = true := by
  decide +kernel

/-- 1449 transcendental evaluations (energy mode). -/
theorem q5E_crossVZ_23_46 :
    energyShardOK q5D 5 vLogRE .crossVZ 23 46 (-727308423950856000122) = true := by
  decide +kernel

/-- 189 transcendental evaluations (energy mode). -/
theorem q5E_crossVZ_46_49 :
    energyShardOK q5D 5 vLogRE .crossVZ 46 49 (754437490657963840167) = true := by
  decide +kernel

/-- 1312 transcendental evaluations (energy mode). -/
theorem q5E_intPoi_0_4 :
    energyShardOK q5D 5 vLogRE .intPoi 0 4 (227250660341942726) = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
