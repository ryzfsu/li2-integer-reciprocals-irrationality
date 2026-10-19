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

/-- 861 transcendental evaluations (energy mode). -/
theorem q2E_selfX_0_42 :
    energyShardOK q2D 2 vLogRE .selfX 0 42 (-28527138597217836334) = true := by
  decide +kernel

/-- 1176 transcendental evaluations (energy mode). -/
theorem q2E_selfV_0_49 :
    energyShardOK q2D 2 vLogRE .selfV 0 49 (-41314003762645412436) = true := by
  decide +kernel

/-- 1488 transcendental evaluations (energy mode). -/
theorem q2E_selfZ_0_32 :
    energyShardOK q2D 2 vLogRE .selfZ 0 32 (-3053873798366259184) = true := by
  decide +kernel

/-- 465 transcendental evaluations (energy mode). -/
theorem q2E_selfZ_32_63 :
    energyShardOK q2D 2 vLogRE .selfZ 32 63 (54856343251943363) = true := by
  decide +kernel

/-- 1449 transcendental evaluations (energy mode). -/
theorem q2E_crossVZ_0_23 :
    energyShardOK q2D 2 vLogRE .crossVZ 0 23 (4875408042235156026) = true := by
  decide +kernel

/-- 1449 transcendental evaluations (energy mode). -/
theorem q2E_crossVZ_23_46 :
    energyShardOK q2D 2 vLogRE .crossVZ 23 46 (18188865845369762708) = true := by
  decide +kernel

/-- 189 transcendental evaluations (energy mode). -/
theorem q2E_crossVZ_46_49 :
    energyShardOK q2D 2 vLogRE .crossVZ 46 49 (-17281626094082648333) = true := by
  decide +kernel

/-- 1312 transcendental evaluations (energy mode). -/
theorem q2E_intPoi_0_4 :
    energyShardOK q2D 2 vLogRE .intPoi 0 4 (-99260137523217155) = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
