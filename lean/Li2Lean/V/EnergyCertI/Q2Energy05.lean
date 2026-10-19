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

/-- 990 transcendental evaluations (energy mode). -/
theorem q2E_pp_105_149 :
    energyShardOK q2D 2 vLogRE .pp 105 149 (-1341488163676611499) = true := by
  decide +kernel

/-- 1 transcendental evaluations (energy mode). -/
theorem q2E_dq_0_1 :
    energyShardOK q2D 2 vLogRE .dq 0 1 (-19544023429413489940) = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
