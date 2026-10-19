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

/-- 780 transcendental evaluations (energy mode). -/
theorem q7E_selfX_0_40 :
    energyShardOK q7D 7 vLogRE .selfX 0 40 (-28875128489297047729) = true := by
  decide +kernel

/-- 1128 transcendental evaluations (energy mode). -/
theorem q7E_selfV_0_48 :
    energyShardOK q7D 7 vLogRE .selfV 0 48 (-41316642665153355509) = true := by
  decide +kernel

/-- 1488 transcendental evaluations (energy mode). -/
theorem q7E_selfZ_0_32 :
    energyShardOK q7D 7 vLogRE .selfZ 0 32 (1770207004735533885) = true := by
  decide +kernel

/-- 465 transcendental evaluations (energy mode). -/
theorem q7E_selfZ_32_63 :
    energyShardOK q7D 7 vLogRE .selfZ 32 63 (40128891754537680) = true := by
  decide +kernel

/-- 1449 transcendental evaluations (energy mode). -/
theorem q7E_crossVZ_0_23 :
    energyShardOK q7D 7 vLogRE .crossVZ 0 23 (-32828756647848186629) = true := by
  decide +kernel

/-- 1449 transcendental evaluations (energy mode). -/
theorem q7E_crossVZ_23_46 :
    energyShardOK q7D 7 vLogRE .crossVZ 23 46 (-2375155283663346504730) = true := by
  decide +kernel

/-- 126 transcendental evaluations (energy mode). -/
theorem q7E_crossVZ_46_48 :
    energyShardOK q7D 7 vLogRE .crossVZ 46 48 (2429639957103383862609) = true := by
  decide +kernel

/-- 1296 transcendental evaluations (energy mode). -/
theorem q7E_intPoi_0_4 :
    energyShardOK q7D 7 vLogRE .intPoi 0 4 (381514881570882896) = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
