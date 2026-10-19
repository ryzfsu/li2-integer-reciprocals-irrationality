/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.V.EnergyCertI.Consts
import Li2Lean.V.EnergyCertI.ISoundTrans

namespace Li2Lean.B3

open Li2Lean.V.EnergyCertI
open Li2Lean.V.EnergyCertI.IK

/-- The printed energy-log interval contains the exact reference value. -/
theorem q2_reference_log_interval_sound :
    IV.mem vLogRE (Real.log (3 / 5 : ℝ)) := by
  have hlog := logQ_mem 7 (a := (3, 5)) (by norm_num) (by norm_num)
  rw [vLogRE_eq] at hlog
  simpa [val] using hlog

#print axioms Li2Lean.B3.q2_reference_log_interval_sound

end Li2Lean.B3
