/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
/-
Generated certificate data
from v13 `v-reference-data.tex` (sha256 e3983e04...cd9b).  elaborated.
-/

import Li2Lean.V.EnergyCertI.Q7Energy00
import Li2Lean.V.EnergyCertI.Q7Energy01
import Li2Lean.V.EnergyCertI.Q7Energy02
import Li2Lean.V.EnergyCertI.Q7Energy03
import Li2Lean.V.EnergyCertI.Q7Energy04
import Li2Lean.V.EnergyCertI.Q7FArc100
import Li2Lean.V.EnergyCertI.Q7FArc101
import Li2Lean.V.EnergyCertI.Q7FArc102
import Li2Lean.V.EnergyCertI.Q7FArc200
import Li2Lean.V.EnergyCertI.Q7FArc201
import Li2Lean.V.EnergyCertI.Q7FArc202
import Li2Lean.V.EnergyCertI.Q7FArc203
import Li2Lean.V.EnergyCertI.Q7FArc204
import Li2Lean.V.EnergyCertI.Q7FArc205
import Li2Lean.V.EnergyCertI.Q7FVhi00
import Li2Lean.V.EnergyCertI.Q7FVhi01
import Li2Lean.V.EnergyCertI.Q7FVhi02
import Li2Lean.V.EnergyCertI.Q7FVhi03
import Li2Lean.V.EnergyCertI.Q7FVhi04
import Li2Lean.V.EnergyCertI.Q7FVhi05
import Li2Lean.V.EnergyCertI.Q7FVhi06
import Li2Lean.V.EnergyCertI.Q7FVhi07
import Li2Lean.V.EnergyCertI.Q7FVhi08
import Li2Lean.V.EnergyCertI.Q7FVhi09
import Li2Lean.V.EnergyCertI.Q7FVlo00
import Li2Lean.V.EnergyCertI.Q7FVlo01
import Li2Lean.V.EnergyCertI.Q7FVlo02
import Li2Lean.V.EnergyCertI.Q7FVlo03
import Li2Lean.V.EnergyCertI.Q7FVlo04
import Li2Lean.V.EnergyCertI.Q7FVlo05
import Li2Lean.V.EnergyCertI.Q7FVlo06
import Li2Lean.V.EnergyCertI.Q7FVlo07
import Li2Lean.V.EnergyCertI.Q7FVlo08
import Li2Lean.V.EnergyCertI.Q7FVlo09
import Li2Lean.V.EnergyCertI.Q7FX00
import Li2Lean.V.EnergyCertI.Q7FX01
import Li2Lean.V.EnergyCertI.Q7FX02
import Li2Lean.V.EnergyCertI.Q7FX03
import Li2Lean.V.EnergyCertI.Q7FX04
import Li2Lean.V.EnergyCertI.Q7FX05
import Li2Lean.V.EnergyCertI.Q7FX06
import Li2Lean.V.EnergyCertI.Q7FX07
import Li2Lean.V.EnergyCertI.Q7FZneg00
import Li2Lean.V.EnergyCertI.Q7FZneg01
import Li2Lean.V.EnergyCertI.Q7FZneg02
import Li2Lean.V.EnergyCertI.Q7FZneg03
import Li2Lean.V.EnergyCertI.Q7FZneg04
import Li2Lean.V.EnergyCertI.Q7FZneg05
import Li2Lean.V.EnergyCertI.Q7FZneg06
import Li2Lean.V.EnergyCertI.Q7FZneg07
import Li2Lean.V.EnergyCertI.Q7FZneg08
import Li2Lean.V.EnergyCertI.Q7FZneg09
import Li2Lean.V.EnergyCertI.Q7FZneg10
import Li2Lean.V.EnergyCertI.Q7FZneg11
import Li2Lean.V.EnergyCertI.Q7FZneg12
import Li2Lean.V.EnergyCertI.Q7FZneg13
import Li2Lean.V.EnergyCertI.Q7FZneg14
import Li2Lean.V.EnergyCertI.Q7FZneg15
import Li2Lean.V.EnergyCertI.Q7FZpos00

namespace Li2Lean.V.EnergyCertI

open IK

/-- Energy plan (kind, i0, i1, claim · 2^64); entry ↦ theorem `q7E_<kind>_<i0>_<i1>`. -/
def q7EnergyPlan : List (EKind × Nat × Nat × Int) := [
  (.selfX, 0, 40, -28875128489297047729),
  (.selfV, 0, 48, -41316642665153355509),
  (.selfZ, 0, 32, 1770207004735533885),
  (.selfZ, 32, 63, 40128891754537680),
  (.crossVZ, 0, 23, -32828756647848186629),
  (.crossVZ, 23, 46, -2375155283663346504730),
  (.crossVZ, 46, 48, 2429639957103383862609),
  (.intPoi, 0, 4, 381514881570882896),
  (.intPoi, 4, 8, 535237425184382379),
  (.intPoi, 8, 12, 643665064418462959),
  (.intPoi, 12, 16, 720725472979324567),
  (.intPoi, 16, 20, 774956879087949637),
  (.intPoi, 20, 24, 810887133196669378),
  (.intPoi, 24, 28, 831388208187753066),
  (.intPoi, 28, 32, 838619482889075738),
  (.intPoi, 32, 36, 834353853963071308),
  (.intPoi, 36, 40, 820113973696345219),
  (.intPoi, 40, 44, 797316981181697290),
  (.intPoi, 44, 48, 767326693818582727),
  (.intPoi, 48, 52, 731407189719600783),
  (.intPoi, 52, 56, 690775633586810555),
  (.intPoi, 56, 60, 646427547478953382),
  (.intPoi, 60, 64, 597703741413246544),
  (.intPoi, 64, 66, 199616538320186411),
  (.pp, 0, 11, -149614220980363408),
  (.pp, 11, 24, -258594776874354896),
  (.pp, 24, 39, -301933224421594218),
  (.pp, 39, 56, -289124629846960900),
  (.pp, 56, 79, -351471461357053725),
  (.pp, 79, 131, -773854327265080624),
  (.dq, 0, 1, -45996578302510234394)]

theorem q7EnergyClaims_gt_qlow : claimsGt q7EnergyPlan (qlowQ 7) = true := by decide +kernel

theorem q7EnergyPlan_tiles : energyPlanTiles q7D q7EnergyPlan = true := by decide +kernel

theorem q7F_x_chain :
    chainOK (1, 250) (1, 1) [q7F_x_000_b, q7F_x_001_b, q7F_x_002_b, q7F_x_003_b,
      q7F_x_004_b, q7F_x_005_b, q7F_x_006_b, q7F_x_007_b,
      q7F_x_008_b, q7F_x_009_b, q7F_x_010_b, q7F_x_011_b,
      q7F_x_012_b, q7F_x_013_b, q7F_x_014_b, q7F_x_015_b,
      q7F_x_016_b, q7F_x_017_b, q7F_x_018_b, q7F_x_019_b,
      q7F_x_020_b, q7F_x_021_b, q7F_x_022_b, q7F_x_023_b,
      q7F_x_024_b, q7F_x_025_b, q7F_x_026_b, q7F_x_027_b,
      q7F_x_028_b, q7F_x_029_b, q7F_x_030_b, q7F_x_031_b,
      q7F_x_032_b, q7F_x_033_b, q7F_x_034_b, q7F_x_035_b,
      q7F_x_036_b, q7F_x_037_b, q7F_x_038_b, q7F_x_039_b,
      q7F_x_040_b, q7F_x_041_b, q7F_x_042_b, q7F_x_043_b,
      q7F_x_044_b, q7F_x_045_b] = true := by
  decide +kernel

theorem q7F_vlo_chain :
    chainOK (1, 250) (3, 5) [q7F_vlo_000_b, q7F_vlo_001_b, q7F_vlo_002_b, q7F_vlo_003_b,
      q7F_vlo_004_b, q7F_vlo_005_b, q7F_vlo_006_b, q7F_vlo_007_b,
      q7F_vlo_008_b, q7F_vlo_009_b, q7F_vlo_010_b, q7F_vlo_011_b,
      q7F_vlo_012_b, q7F_vlo_013_b, q7F_vlo_014_b, q7F_vlo_015_b,
      q7F_vlo_016_b, q7F_vlo_017_b, q7F_vlo_018_b, q7F_vlo_019_b,
      q7F_vlo_020_b, q7F_vlo_021_b, q7F_vlo_022_b, q7F_vlo_023_b,
      q7F_vlo_024_b, q7F_vlo_025_b, q7F_vlo_026_b, q7F_vlo_027_b,
      q7F_vlo_028_b, q7F_vlo_029_b, q7F_vlo_030_b, q7F_vlo_031_b,
      q7F_vlo_032_b, q7F_vlo_033_b, q7F_vlo_034_b, q7F_vlo_035_b,
      q7F_vlo_036_b, q7F_vlo_037_b, q7F_vlo_038_b, q7F_vlo_039_b,
      q7F_vlo_040_b, q7F_vlo_041_b, q7F_vlo_042_b, q7F_vlo_043_b,
      q7F_vlo_044_b, q7F_vlo_045_b, q7F_vlo_046_b, q7F_vlo_047_b,
      q7F_vlo_048_b, q7F_vlo_049_b, q7F_vlo_050_b, q7F_vlo_051_b,
      q7F_vlo_052_b, q7F_vlo_053_b, q7F_vlo_054_b, q7F_vlo_055_b,
      q7F_vlo_056_b, q7F_vlo_057_b, q7F_vlo_058_b, q7F_vlo_059_b,
      q7F_vlo_060_b, q7F_vlo_061_b, q7F_vlo_062_b, q7F_vlo_063_b,
      q7F_vlo_064_b, q7F_vlo_065_b, q7F_vlo_066_b] = true := by
  decide +kernel

theorem q7F_vhi_chain :
    chainOK (3, 5) (1, 1) [q7F_vhi_000_b, q7F_vhi_001_b, q7F_vhi_002_b, q7F_vhi_003_b,
      q7F_vhi_004_b, q7F_vhi_005_b, q7F_vhi_006_b, q7F_vhi_007_b,
      q7F_vhi_008_b, q7F_vhi_009_b, q7F_vhi_010_b, q7F_vhi_011_b,
      q7F_vhi_012_b, q7F_vhi_013_b, q7F_vhi_014_b, q7F_vhi_015_b,
      q7F_vhi_016_b, q7F_vhi_017_b, q7F_vhi_018_b, q7F_vhi_019_b,
      q7F_vhi_020_b, q7F_vhi_021_b, q7F_vhi_022_b, q7F_vhi_023_b,
      q7F_vhi_024_b, q7F_vhi_025_b, q7F_vhi_026_b, q7F_vhi_027_b,
      q7F_vhi_028_b, q7F_vhi_029_b, q7F_vhi_030_b, q7F_vhi_031_b,
      q7F_vhi_032_b, q7F_vhi_033_b, q7F_vhi_034_b, q7F_vhi_035_b,
      q7F_vhi_036_b, q7F_vhi_037_b, q7F_vhi_038_b, q7F_vhi_039_b,
      q7F_vhi_040_b, q7F_vhi_041_b, q7F_vhi_042_b, q7F_vhi_043_b,
      q7F_vhi_044_b, q7F_vhi_045_b, q7F_vhi_046_b, q7F_vhi_047_b,
      q7F_vhi_048_b, q7F_vhi_049_b, q7F_vhi_050_b, q7F_vhi_051_b,
      q7F_vhi_052_b, q7F_vhi_053_b, q7F_vhi_054_b, q7F_vhi_055_b,
      q7F_vhi_056_b, q7F_vhi_057_b, q7F_vhi_058_b, q7F_vhi_059_b,
      q7F_vhi_060_b, q7F_vhi_061_b, q7F_vhi_062_b, q7F_vhi_063_b,
      q7F_vhi_064_b, q7F_vhi_065_b, q7F_vhi_066_b, q7F_vhi_067_b,
      q7F_vhi_068_b] = true := by
  decide +kernel

theorem q7F_zneg_chain :
    chainOK (-7, 1) (-3, 5) [q7F_zneg_000_b, q7F_zneg_001_b, q7F_zneg_002_b, q7F_zneg_003_b,
      q7F_zneg_004_b, q7F_zneg_005_b, q7F_zneg_006_b, q7F_zneg_007_b,
      q7F_zneg_008_b, q7F_zneg_009_b, q7F_zneg_010_b, q7F_zneg_011_b,
      q7F_zneg_012_b, q7F_zneg_013_b, q7F_zneg_014_b, q7F_zneg_015_b,
      q7F_zneg_016_b, q7F_zneg_017_b, q7F_zneg_018_b, q7F_zneg_019_b,
      q7F_zneg_020_b, q7F_zneg_021_b, q7F_zneg_022_b, q7F_zneg_023_b,
      q7F_zneg_024_b, q7F_zneg_025_b, q7F_zneg_026_b, q7F_zneg_027_b,
      q7F_zneg_028_b, q7F_zneg_029_b, q7F_zneg_030_b, q7F_zneg_031_b,
      q7F_zneg_032_b, q7F_zneg_033_b, q7F_zneg_034_b, q7F_zneg_035_b,
      q7F_zneg_036_b, q7F_zneg_037_b, q7F_zneg_038_b, q7F_zneg_039_b,
      q7F_zneg_040_b, q7F_zneg_041_b, q7F_zneg_042_b, q7F_zneg_043_b,
      q7F_zneg_044_b, q7F_zneg_045_b, q7F_zneg_046_b, q7F_zneg_047_b,
      q7F_zneg_048_b, q7F_zneg_049_b, q7F_zneg_050_b, q7F_zneg_051_b,
      q7F_zneg_052_b, q7F_zneg_053_b, q7F_zneg_054_b, q7F_zneg_055_b,
      q7F_zneg_056_b, q7F_zneg_057_b, q7F_zneg_058_b, q7F_zneg_059_b,
      q7F_zneg_060_b, q7F_zneg_061_b, q7F_zneg_062_b, q7F_zneg_063_b,
      q7F_zneg_064_b, q7F_zneg_065_b, q7F_zneg_066_b, q7F_zneg_067_b,
      q7F_zneg_068_b, q7F_zneg_069_b, q7F_zneg_070_b, q7F_zneg_071_b,
      q7F_zneg_072_b, q7F_zneg_073_b, q7F_zneg_074_b, q7F_zneg_075_b,
      q7F_zneg_076_b, q7F_zneg_077_b, q7F_zneg_078_b, q7F_zneg_079_b,
      q7F_zneg_080_b, q7F_zneg_081_b, q7F_zneg_082_b, q7F_zneg_083_b,
      q7F_zneg_084_b, q7F_zneg_085_b, q7F_zneg_086_b, q7F_zneg_087_b,
      q7F_zneg_088_b, q7F_zneg_089_b, q7F_zneg_090_b, q7F_zneg_091_b] = true := by
  decide +kernel

theorem q7F_zpos_chain :
    chainOK (3, 5) (1, 1) [q7F_zpos_000_b] = true := by
  decide +kernel

theorem q7F_arc1_chain :
    chainOK (0, 1) (1, 1) [q7F_arc1_000_b, q7F_arc1_001_b, q7F_arc1_002_b, q7F_arc1_003_b,
      q7F_arc1_004_b, q7F_arc1_005_b, q7F_arc1_006_b, q7F_arc1_007_b,
      q7F_arc1_008_b, q7F_arc1_009_b, q7F_arc1_010_b, q7F_arc1_011_b,
      q7F_arc1_012_b, q7F_arc1_013_b, q7F_arc1_014_b, q7F_arc1_015_b,
      q7F_arc1_016_b, q7F_arc1_017_b, q7F_arc1_018_b, q7F_arc1_019_b] = true := by
  decide +kernel

theorem q7F_arc2_chain :
    chainOK (0, 1) (1, 1) [q7F_arc2_000_b, q7F_arc2_001_b, q7F_arc2_002_b, q7F_arc2_003_b,
      q7F_arc2_004_b, q7F_arc2_005_b, q7F_arc2_006_b, q7F_arc2_007_b,
      q7F_arc2_008_b, q7F_arc2_009_b, q7F_arc2_010_b, q7F_arc2_011_b,
      q7F_arc2_012_b, q7F_arc2_013_b, q7F_arc2_014_b, q7F_arc2_015_b,
      q7F_arc2_016_b, q7F_arc2_017_b, q7F_arc2_018_b, q7F_arc2_019_b,
      q7F_arc2_020_b, q7F_arc2_021_b, q7F_arc2_022_b, q7F_arc2_023_b,
      q7F_arc2_024_b, q7F_arc2_025_b, q7F_arc2_026_b, q7F_arc2_027_b,
      q7F_arc2_028_b, q7F_arc2_029_b, q7F_arc2_030_b, q7F_arc2_031_b,
      q7F_arc2_032_b, q7F_arc2_033_b, q7F_arc2_034_b, q7F_arc2_035_b,
      q7F_arc2_036_b, q7F_arc2_037_b, q7F_arc2_038_b] = true := by
  decide +kernel

/-- Endpoint disks: directed `E_x, E_v` below the printed values, and these below `K`. -/
theorem q7Endpoint_check :
    (hiLe (exUB fieldMode q7D 7) (exQ 7) && hiLe (evUB fieldMode q7D 7) (evQ 7) &&
      qlt (exQ 7) (kxQ 7) && qlt (evQ 7) (kvQ 7)) = true := by
  decide +kernel

/-- `alpha_le`: `vAlpha q ≤ Qlow - 3/2·log q - Kx - 5/4·Kv - Kz`, `log q ≤ (logQ 3 (q,1)).2 / 2^64`. -/
theorem q7Alpha_check :
    qle (alphaQ 7) (qsub (qsub (qsub (qsub (qlowQ 7) (qmul (3, 2) ((logQ 3 (7, 1)).2, S)))
      (kxQ 7)) (qmul (5, 4) (kvQ 7))) (kzQ 7)) = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
