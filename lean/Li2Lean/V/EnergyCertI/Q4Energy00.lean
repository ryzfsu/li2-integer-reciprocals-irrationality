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

/-- 820 transcendental evaluations (energy mode). -/
theorem q4E_selfX_0_41 :
    energyShardOK q4D 4 vLogRE .selfX 0 41 (-28757594321929087777) = true := by
  decide +kernel

/-- 1176 transcendental evaluations (energy mode). -/
theorem q4E_selfV_0_49 :
    energyShardOK q4D 4 vLogRE .selfV 0 49 (-41349836777635692874) = true := by
  decide +kernel

/-- 1488 transcendental evaluations (energy mode). -/
theorem q4E_selfZ_0_32 :
    energyShardOK q4D 4 vLogRE .selfZ 0 32 (-1965724329603976947) = true := by
  decide +kernel

/-- 465 transcendental evaluations (energy mode). -/
theorem q4E_selfZ_32_63 :
    energyShardOK q4D 4 vLogRE .selfZ 32 63 (67857096642567704) = true := by
  decide +kernel

/-- 1449 transcendental evaluations (energy mode). -/
theorem q4E_crossVZ_0_23 :
    energyShardOK q4D 4 vLogRE .crossVZ 0 23 (-2754809324682159871) = true := by
  decide +kernel

/-- 1449 transcendental evaluations (energy mode). -/
theorem q4E_crossVZ_23_46 :
    energyShardOK q4D 4 vLogRE .crossVZ 23 46 (-410824349570290622503) = true := by
  decide +kernel

/-- 189 transcendental evaluations (energy mode). -/
theorem q4E_crossVZ_46_49 :
    energyShardOK q4D 4 vLogRE .crossVZ 46 49 (427106472512558600712) = true := by
  decide +kernel

/-- 1312 transcendental evaluations (energy mode). -/
theorem q4E_intPoi_0_4 :
    energyShardOK q4D 4 vLogRE .intPoi 0 4 (128035668281660454) = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
