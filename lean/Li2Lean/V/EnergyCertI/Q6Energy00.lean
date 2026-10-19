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

/-- 861 transcendental evaluations (energy mode). -/
theorem q6E_selfX_0_42 :
    energyShardOK q6D 6 vLogRE .selfX 0 42 (-28847670510885277787) = true := by
  decide +kernel

/-- 1128 transcendental evaluations (energy mode). -/
theorem q6E_selfV_0_48 :
    energyShardOK q6D 6 vLogRE .selfV 0 48 (-41328903187849201394) = true := by
  decide +kernel

/-- 1485 transcendental evaluations (energy mode). -/
theorem q6E_selfZ_0_33 :
    energyShardOK q6D 6 vLogRE .selfZ 0 33 (504352036037531782) = true := by
  decide +kernel

/-- 406 transcendental evaluations (energy mode). -/
theorem q6E_selfZ_33_62 :
    energyShardOK q6D 6 vLogRE .selfZ 33 62 (43292736212840066) = true := by
  decide +kernel

/-- 1488 transcendental evaluations (energy mode). -/
theorem q6E_crossVZ_0_24 :
    energyShardOK q6D 6 vLogRE .crossVZ 0 24 (-22390562531108966073) = true := by
  decide +kernel

/-- 1488 transcendental evaluations (energy mode). -/
theorem q6E_crossVZ_24_48 :
    energyShardOK q6D 6 vLogRE .crossVZ 24 48 (41666457999065193827) = true := by
  decide +kernel

/-- 1288 transcendental evaluations (energy mode). -/
theorem q6E_intPoi_0_4 :
    energyShardOK q6D 6 vLogRE .intPoi 0 4 (250961944560195504) = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
