/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
/-
Generated certificate data
from v13 `v-reference-data.tex` (sha256 e3983e04...cd9b).  elaborated.
-/

import Li2Lean.V.EnergyCertI.Q3Energy00
import Li2Lean.V.EnergyCertI.Q3Energy01
import Li2Lean.V.EnergyCertI.Q3Energy02
import Li2Lean.V.EnergyCertI.Q3Energy03
import Li2Lean.V.EnergyCertI.Q3Energy04
import Li2Lean.V.EnergyCertI.Q3FArc100
import Li2Lean.V.EnergyCertI.Q3FArc101
import Li2Lean.V.EnergyCertI.Q3FArc102
import Li2Lean.V.EnergyCertI.Q3FArc103
import Li2Lean.V.EnergyCertI.Q3FArc200
import Li2Lean.V.EnergyCertI.Q3FArc201
import Li2Lean.V.EnergyCertI.Q3FArc202
import Li2Lean.V.EnergyCertI.Q3FArc203
import Li2Lean.V.EnergyCertI.Q3FArc204
import Li2Lean.V.EnergyCertI.Q3FArc205
import Li2Lean.V.EnergyCertI.Q3FVhi00
import Li2Lean.V.EnergyCertI.Q3FVhi01
import Li2Lean.V.EnergyCertI.Q3FVhi02
import Li2Lean.V.EnergyCertI.Q3FVhi03
import Li2Lean.V.EnergyCertI.Q3FVhi04
import Li2Lean.V.EnergyCertI.Q3FVhi05
import Li2Lean.V.EnergyCertI.Q3FVhi06
import Li2Lean.V.EnergyCertI.Q3FVhi07
import Li2Lean.V.EnergyCertI.Q3FVhi08
import Li2Lean.V.EnergyCertI.Q3FVhi09
import Li2Lean.V.EnergyCertI.Q3FVlo00
import Li2Lean.V.EnergyCertI.Q3FVlo01
import Li2Lean.V.EnergyCertI.Q3FVlo02
import Li2Lean.V.EnergyCertI.Q3FVlo03
import Li2Lean.V.EnergyCertI.Q3FVlo04
import Li2Lean.V.EnergyCertI.Q3FVlo05
import Li2Lean.V.EnergyCertI.Q3FVlo06
import Li2Lean.V.EnergyCertI.Q3FVlo07
import Li2Lean.V.EnergyCertI.Q3FVlo08
import Li2Lean.V.EnergyCertI.Q3FVlo09
import Li2Lean.V.EnergyCertI.Q3FX00
import Li2Lean.V.EnergyCertI.Q3FX01
import Li2Lean.V.EnergyCertI.Q3FX02
import Li2Lean.V.EnergyCertI.Q3FX03
import Li2Lean.V.EnergyCertI.Q3FX04
import Li2Lean.V.EnergyCertI.Q3FX05
import Li2Lean.V.EnergyCertI.Q3FX06
import Li2Lean.V.EnergyCertI.Q3FX07
import Li2Lean.V.EnergyCertI.Q3FZneg00
import Li2Lean.V.EnergyCertI.Q3FZneg01
import Li2Lean.V.EnergyCertI.Q3FZneg02
import Li2Lean.V.EnergyCertI.Q3FZneg03
import Li2Lean.V.EnergyCertI.Q3FZneg04
import Li2Lean.V.EnergyCertI.Q3FZneg05
import Li2Lean.V.EnergyCertI.Q3FZneg06
import Li2Lean.V.EnergyCertI.Q3FZneg07
import Li2Lean.V.EnergyCertI.Q3FZneg08
import Li2Lean.V.EnergyCertI.Q3FZpos00

namespace Li2Lean.V.EnergyCertI

open IK

/-- Energy plan (kind, i0, i1, claim · 2^64); entry ↦ theorem `q3E_<kind>_<i0>_<i1>`. -/
def q3EnergyPlan : List (EKind × Nat × Nat × Int) := [
  (.selfX, 0, 41, -28675206869031542222),
  (.selfV, 0, 49, -41348583825049056700),
  (.selfZ, 0, 32, -2888038275780117707),
  (.selfZ, 32, 63, 69277132450860779),
  (.crossVZ, 0, 23, 2646186939783378927),
  (.crossVZ, 23, 46, -154826454581410013315),
  (.crossVZ, 46, 49, 162144013248542637282),
  (.intPoi, 0, 4, 52436984091027123),
  (.intPoi, 4, 8, 115782682075382200),
  (.intPoi, 8, 12, 178841942848057266),
  (.intPoi, 12, 16, 234998037434776269),
  (.intPoi, 16, 20, 281972155715722520),
  (.intPoi, 20, 24, 318888522750185777),
  (.intPoi, 24, 28, 345551066467107331),
  (.intPoi, 28, 32, 362155610834585279),
  (.intPoi, 32, 36, 369159723044788443),
  (.intPoi, 36, 40, 367228209810731897),
  (.intPoi, 40, 44, 357216936765602637),
  (.intPoi, 44, 48, 340187927445706037),
  (.intPoi, 48, 52, 317382111097905264),
  (.intPoi, 52, 56, 290248994424790060),
  (.intPoi, 56, 60, 260342875338349288),
  (.intPoi, 60, 64, 229280113477871704),
  (.intPoi, 64, 68, 198517671824874579),
  (.intPoi, 68, 72, 146692858809267284),
  (.pp, 0, 10, -227576522956498808),
  (.pp, 10, 21, -361576179906989236),
  (.pp, 21, 33, -411675747315085978),
  (.pp, 33, 47, -423233599707317869),
  (.pp, 47, 64, -383304215215984894),
  (.pp, 64, 85, -428103208573222284),
  (.pp, 85, 122, -1261227154343536876),
  (.pp, 122, 143, -276634794603940973),
  (.dq, 0, 1, -27821356053220193299)]

theorem q3EnergyClaims_gt_qlow : claimsGt q3EnergyPlan (qlowQ 3) = true := by decide +kernel

theorem q3EnergyPlan_tiles : energyPlanTiles q3D q3EnergyPlan = true := by decide +kernel

theorem q3F_x_chain :
    chainOK (1, 250) (1, 1) [q3F_x_000_b, q3F_x_001_b, q3F_x_002_b, q3F_x_003_b,
      q3F_x_004_b, q3F_x_005_b, q3F_x_006_b, q3F_x_007_b,
      q3F_x_008_b, q3F_x_009_b, q3F_x_010_b, q3F_x_011_b,
      q3F_x_012_b, q3F_x_013_b, q3F_x_014_b, q3F_x_015_b,
      q3F_x_016_b, q3F_x_017_b, q3F_x_018_b, q3F_x_019_b,
      q3F_x_020_b, q3F_x_021_b, q3F_x_022_b, q3F_x_023_b,
      q3F_x_024_b, q3F_x_025_b, q3F_x_026_b, q3F_x_027_b,
      q3F_x_028_b, q3F_x_029_b, q3F_x_030_b, q3F_x_031_b,
      q3F_x_032_b, q3F_x_033_b, q3F_x_034_b, q3F_x_035_b,
      q3F_x_036_b, q3F_x_037_b, q3F_x_038_b, q3F_x_039_b,
      q3F_x_040_b, q3F_x_041_b, q3F_x_042_b, q3F_x_043_b,
      q3F_x_044_b, q3F_x_045_b] = true := by
  decide +kernel

theorem q3F_vlo_chain :
    chainOK (1, 250) (3, 5) [q3F_vlo_000_b, q3F_vlo_001_b, q3F_vlo_002_b, q3F_vlo_003_b,
      q3F_vlo_004_b, q3F_vlo_005_b, q3F_vlo_006_b, q3F_vlo_007_b,
      q3F_vlo_008_b, q3F_vlo_009_b, q3F_vlo_010_b, q3F_vlo_011_b,
      q3F_vlo_012_b, q3F_vlo_013_b, q3F_vlo_014_b, q3F_vlo_015_b,
      q3F_vlo_016_b, q3F_vlo_017_b, q3F_vlo_018_b, q3F_vlo_019_b,
      q3F_vlo_020_b, q3F_vlo_021_b, q3F_vlo_022_b, q3F_vlo_023_b,
      q3F_vlo_024_b, q3F_vlo_025_b, q3F_vlo_026_b, q3F_vlo_027_b,
      q3F_vlo_028_b, q3F_vlo_029_b, q3F_vlo_030_b, q3F_vlo_031_b,
      q3F_vlo_032_b, q3F_vlo_033_b, q3F_vlo_034_b, q3F_vlo_035_b,
      q3F_vlo_036_b, q3F_vlo_037_b, q3F_vlo_038_b, q3F_vlo_039_b,
      q3F_vlo_040_b, q3F_vlo_041_b, q3F_vlo_042_b, q3F_vlo_043_b,
      q3F_vlo_044_b, q3F_vlo_045_b, q3F_vlo_046_b, q3F_vlo_047_b,
      q3F_vlo_048_b, q3F_vlo_049_b, q3F_vlo_050_b, q3F_vlo_051_b,
      q3F_vlo_052_b, q3F_vlo_053_b, q3F_vlo_054_b, q3F_vlo_055_b,
      q3F_vlo_056_b, q3F_vlo_057_b, q3F_vlo_058_b, q3F_vlo_059_b,
      q3F_vlo_060_b, q3F_vlo_061_b, q3F_vlo_062_b, q3F_vlo_063_b,
      q3F_vlo_064_b, q3F_vlo_065_b] = true := by
  decide +kernel

theorem q3F_vhi_chain :
    chainOK (3, 5) (1, 1) [q3F_vhi_000_b, q3F_vhi_001_b, q3F_vhi_002_b, q3F_vhi_003_b,
      q3F_vhi_004_b, q3F_vhi_005_b, q3F_vhi_006_b, q3F_vhi_007_b,
      q3F_vhi_008_b, q3F_vhi_009_b, q3F_vhi_010_b, q3F_vhi_011_b,
      q3F_vhi_012_b, q3F_vhi_013_b, q3F_vhi_014_b, q3F_vhi_015_b,
      q3F_vhi_016_b, q3F_vhi_017_b, q3F_vhi_018_b, q3F_vhi_019_b,
      q3F_vhi_020_b, q3F_vhi_021_b, q3F_vhi_022_b, q3F_vhi_023_b,
      q3F_vhi_024_b, q3F_vhi_025_b, q3F_vhi_026_b, q3F_vhi_027_b,
      q3F_vhi_028_b, q3F_vhi_029_b, q3F_vhi_030_b, q3F_vhi_031_b,
      q3F_vhi_032_b, q3F_vhi_033_b, q3F_vhi_034_b, q3F_vhi_035_b,
      q3F_vhi_036_b, q3F_vhi_037_b, q3F_vhi_038_b, q3F_vhi_039_b,
      q3F_vhi_040_b, q3F_vhi_041_b, q3F_vhi_042_b, q3F_vhi_043_b,
      q3F_vhi_044_b, q3F_vhi_045_b, q3F_vhi_046_b, q3F_vhi_047_b,
      q3F_vhi_048_b, q3F_vhi_049_b, q3F_vhi_050_b, q3F_vhi_051_b,
      q3F_vhi_052_b, q3F_vhi_053_b, q3F_vhi_054_b, q3F_vhi_055_b,
      q3F_vhi_056_b, q3F_vhi_057_b, q3F_vhi_058_b, q3F_vhi_059_b,
      q3F_vhi_060_b, q3F_vhi_061_b, q3F_vhi_062_b, q3F_vhi_063_b,
      q3F_vhi_064_b, q3F_vhi_065_b, q3F_vhi_066_b, q3F_vhi_067_b] = true := by
  decide +kernel

theorem q3F_zneg_chain :
    chainOK (-3, 1) (-3, 5) [q3F_zneg_000_b, q3F_zneg_001_b, q3F_zneg_002_b, q3F_zneg_003_b,
      q3F_zneg_004_b, q3F_zneg_005_b, q3F_zneg_006_b, q3F_zneg_007_b,
      q3F_zneg_008_b, q3F_zneg_009_b, q3F_zneg_010_b, q3F_zneg_011_b,
      q3F_zneg_012_b, q3F_zneg_013_b, q3F_zneg_014_b, q3F_zneg_015_b,
      q3F_zneg_016_b, q3F_zneg_017_b, q3F_zneg_018_b, q3F_zneg_019_b,
      q3F_zneg_020_b, q3F_zneg_021_b, q3F_zneg_022_b, q3F_zneg_023_b,
      q3F_zneg_024_b, q3F_zneg_025_b, q3F_zneg_026_b, q3F_zneg_027_b,
      q3F_zneg_028_b, q3F_zneg_029_b, q3F_zneg_030_b, q3F_zneg_031_b,
      q3F_zneg_032_b, q3F_zneg_033_b, q3F_zneg_034_b, q3F_zneg_035_b,
      q3F_zneg_036_b, q3F_zneg_037_b, q3F_zneg_038_b, q3F_zneg_039_b,
      q3F_zneg_040_b, q3F_zneg_041_b, q3F_zneg_042_b, q3F_zneg_043_b,
      q3F_zneg_044_b, q3F_zneg_045_b, q3F_zneg_046_b, q3F_zneg_047_b,
      q3F_zneg_048_b, q3F_zneg_049_b, q3F_zneg_050_b, q3F_zneg_051_b,
      q3F_zneg_052_b, q3F_zneg_053_b, q3F_zneg_054_b, q3F_zneg_055_b,
      q3F_zneg_056_b, q3F_zneg_057_b, q3F_zneg_058_b, q3F_zneg_059_b,
      q3F_zneg_060_b, q3F_zneg_061_b] = true := by
  decide +kernel

theorem q3F_zpos_chain :
    chainOK (3, 5) (1, 1) [q3F_zpos_000_b] = true := by
  decide +kernel

theorem q3F_arc1_chain :
    chainOK (0, 1) (1, 1) [q3F_arc1_000_b, q3F_arc1_001_b, q3F_arc1_002_b, q3F_arc1_003_b,
      q3F_arc1_004_b, q3F_arc1_005_b, q3F_arc1_006_b, q3F_arc1_007_b,
      q3F_arc1_008_b, q3F_arc1_009_b, q3F_arc1_010_b, q3F_arc1_011_b,
      q3F_arc1_012_b, q3F_arc1_013_b, q3F_arc1_014_b, q3F_arc1_015_b,
      q3F_arc1_016_b, q3F_arc1_017_b, q3F_arc1_018_b, q3F_arc1_019_b,
      q3F_arc1_020_b, q3F_arc1_021_b, q3F_arc1_022_b, q3F_arc1_023_b,
      q3F_arc1_024_b, q3F_arc1_025_b, q3F_arc1_026_b, q3F_arc1_027_b] = true := by
  decide +kernel

theorem q3F_arc2_chain :
    chainOK (0, 1) (1, 1) [q3F_arc2_000_b, q3F_arc2_001_b, q3F_arc2_002_b, q3F_arc2_003_b,
      q3F_arc2_004_b, q3F_arc2_005_b, q3F_arc2_006_b, q3F_arc2_007_b,
      q3F_arc2_008_b, q3F_arc2_009_b, q3F_arc2_010_b, q3F_arc2_011_b,
      q3F_arc2_012_b, q3F_arc2_013_b, q3F_arc2_014_b, q3F_arc2_015_b,
      q3F_arc2_016_b, q3F_arc2_017_b, q3F_arc2_018_b, q3F_arc2_019_b,
      q3F_arc2_020_b, q3F_arc2_021_b, q3F_arc2_022_b, q3F_arc2_023_b,
      q3F_arc2_024_b, q3F_arc2_025_b, q3F_arc2_026_b, q3F_arc2_027_b,
      q3F_arc2_028_b, q3F_arc2_029_b, q3F_arc2_030_b, q3F_arc2_031_b,
      q3F_arc2_032_b, q3F_arc2_033_b, q3F_arc2_034_b, q3F_arc2_035_b,
      q3F_arc2_036_b, q3F_arc2_037_b, q3F_arc2_038_b, q3F_arc2_039_b,
      q3F_arc2_040_b, q3F_arc2_041_b] = true := by
  decide +kernel

/-- Endpoint disks: directed `E_x, E_v` below the printed values, and these below `K`. -/
theorem q3Endpoint_check :
    (hiLe (exUB fieldMode q3D 3) (exQ 3) && hiLe (evUB fieldMode q3D 3) (evQ 3) &&
      qlt (exQ 3) (kxQ 3) && qlt (evQ 3) (kvQ 3)) = true := by
  decide +kernel

/-- `alpha_le`: `vAlpha q ≤ Qlow - 3/2·log q - Kx - 5/4·Kv - Kz`, `log q ≤ (logQ 3 (q,1)).2 / 2^64`. -/
theorem q3Alpha_check :
    qle (alphaQ 3) (qsub (qsub (qsub (qsub (qlowQ 3) (qmul (3, 2) ((logQ 3 (3, 1)).2, S)))
      (kxQ 3)) (qmul (5, 4) (kvQ 3))) (kzQ 3)) = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
