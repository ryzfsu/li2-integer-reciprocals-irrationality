/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
/-
Generated certificate data
from v13 `v-reference-data.tex` (sha256 e3983e04...cd9b).  elaborated.
-/

import Li2Lean.V.EnergyCertI.Q3Rows
import Li2Lean.V.EnergyCertI.Consts

namespace Li2Lean.V.EnergyCertI

open IK

/-- 820 transcendental evaluations (energy mode). -/
theorem q3E_selfX_0_41 :
    energyShardOK q3D 3 vLogRE .selfX 0 41 (-28675206869031542222) = true := by
  decide +kernel

/-- 1176 transcendental evaluations (energy mode). -/
theorem q3E_selfV_0_49 :
    energyShardOK q3D 3 vLogRE .selfV 0 49 (-41348583825049056700) = true := by
  decide +kernel

/-- 1488 transcendental evaluations (energy mode). -/
theorem q3E_selfZ_0_32 :
    energyShardOK q3D 3 vLogRE .selfZ 0 32 (-2888038275780117707) = true := by
  decide +kernel

/-- 465 transcendental evaluations (energy mode). -/
theorem q3E_selfZ_32_63 :
    energyShardOK q3D 3 vLogRE .selfZ 32 63 (69277132450860779) = true := by
  decide +kernel

/-- 1449 transcendental evaluations (energy mode). -/
theorem q3E_crossVZ_0_23 :
    energyShardOK q3D 3 vLogRE .crossVZ 0 23 (2646186939783378927) = true := by
  decide +kernel

/-- 1449 transcendental evaluations (energy mode). -/
theorem q3E_crossVZ_23_46 :
    energyShardOK q3D 3 vLogRE .crossVZ 23 46 (-154826454581410013315) = true := by
  decide +kernel

/-- 189 transcendental evaluations (energy mode). -/
theorem q3E_crossVZ_46_49 :
    energyShardOK q3D 3 vLogRE .crossVZ 46 49 (162144013248542637282) = true := by
  decide +kernel

/-- 1312 transcendental evaluations (energy mode). -/
theorem q3E_intPoi_0_4 :
    energyShardOK q3D 3 vLogRE .intPoi 0 4 (52436984091027123) = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
