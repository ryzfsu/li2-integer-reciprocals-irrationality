/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
/-
Generated certificate data
from v13 `v-reference-data.tex` (sha256 e3983e04...cd9b).  elaborated.
-/
import Li2Lean.V.EnergyCertI.IFieldEval

namespace Li2Lean.V.EnergyCertI

open IK

/-- `log (3/5)`, field mode (equal to `logQ 3 (3, 5)`). -/
def vLogRF : IV := (-9423069547906768319, -9423069547900118655)

/-- `log (3/5)`, energy mode (equal to `logQ 7 (3, 5)`). -/
def vLogRE : IV := (-9423069547904273726, -9423069547904273714)

theorem vLogRF_eq : logQ 3 (3, 5) = vLogRF := by decide +kernel
theorem vLogRE_eq : logQ 7 (3, 5) = vLogRE := by decide +kernel

/-- printed `K_x` (`v-analytic.tex:352-394`) -/
def kxQ : Nat → QF
  | 2 => (-4621, 1000)
  | 3 => (-1269, 250)
  | 4 => (-676, 125)
  | 5 => (-567, 100)
  | 6 => (-2943, 500)
  | 7 => (-6071, 1000)
  | _ => (0, 1)
/-- printed `K_v` -/
def kvQ : Nat → QF
  | 2 => (-179, 40)
  | 3 => (-579, 125)
  | 4 => (-4727, 1000)
  | 5 => (-4791, 1000)
  | 6 => (-4839, 1000)
  | 7 => (-1219, 250)
  | _ => (0, 1)
/-- printed `K_z` -/
def kzQ : Nat → QF
  | 2 => (-17, 200)
  | 3 => (97, 250)
  | 4 => (779, 1000)
  | 5 => (554001, 500000)
  | 6 => (1391, 1000)
  | 7 => (1639, 1000)
  | _ => (0, 1)
/-- printed `Q_low` -/
def qlowQ : Nat → QF
  | 2 => (-613909, 125000)
  | 3 => (-4863007, 1000000)
  | 4 => (-2388099, 500000)
  | 5 => (-4684191, 1000000)
  | 6 => (-4595191, 1000000)
  | 7 => (-4511619, 1000000)
  | _ => (0, 1)
/-- printed `E_x` -/
def exQ : Nat → QF
  | 2 => (-62821, 10000)
  | 3 => (-8457, 1250)
  | 4 => (-35563, 5000)
  | 5 => (-14767, 2000)
  | 6 => (-76061, 10000)
  | 7 => (-77947, 10000)
  | _ => (0, 1)
/-- printed `E_v` -/
def evQ : Nat → QF
  | 2 => (-8987, 2000)
  | 3 => (-46587, 10000)
  | 4 => (-9511, 2000)
  | 5 => (-3013, 625)
  | 6 => (-3043, 625)
  | 7 => (-49057, 10000)
  | _ => (0, 1)
/-- `vAlpha` (q = 6 corrected to 3.26091) -/
def alphaQ : Nat → QF
  | 2 => (3479, 800)
  | 3 => (396707, 100000)
  | 4 => (368211, 100000)
  | 5 => (8631, 2500)
  | 6 => (326091, 100000)
  | 7 => (309651, 100000)
  | _ => (0, 1)

end Li2Lean.V.EnergyCertI
