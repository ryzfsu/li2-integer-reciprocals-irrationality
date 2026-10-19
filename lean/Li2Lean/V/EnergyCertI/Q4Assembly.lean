/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
/-
Generated certificate data
from v13 `v-reference-data.tex` (sha256 e3983e04...cd9b).  elaborated.
-/

import Li2Lean.V.EnergyCertI.Q4Energy00
import Li2Lean.V.EnergyCertI.Q4Energy01
import Li2Lean.V.EnergyCertI.Q4Energy02
import Li2Lean.V.EnergyCertI.Q4Energy03
import Li2Lean.V.EnergyCertI.Q4Energy04
import Li2Lean.V.EnergyCertI.Q4FArc100
import Li2Lean.V.EnergyCertI.Q4FArc101
import Li2Lean.V.EnergyCertI.Q4FArc102
import Li2Lean.V.EnergyCertI.Q4FArc103
import Li2Lean.V.EnergyCertI.Q4FArc200
import Li2Lean.V.EnergyCertI.Q4FArc201
import Li2Lean.V.EnergyCertI.Q4FArc202
import Li2Lean.V.EnergyCertI.Q4FArc203
import Li2Lean.V.EnergyCertI.Q4FArc204
import Li2Lean.V.EnergyCertI.Q4FArc205
import Li2Lean.V.EnergyCertI.Q4FVhi00
import Li2Lean.V.EnergyCertI.Q4FVhi01
import Li2Lean.V.EnergyCertI.Q4FVhi02
import Li2Lean.V.EnergyCertI.Q4FVhi03
import Li2Lean.V.EnergyCertI.Q4FVhi04
import Li2Lean.V.EnergyCertI.Q4FVhi05
import Li2Lean.V.EnergyCertI.Q4FVhi06
import Li2Lean.V.EnergyCertI.Q4FVhi07
import Li2Lean.V.EnergyCertI.Q4FVhi08
import Li2Lean.V.EnergyCertI.Q4FVhi09
import Li2Lean.V.EnergyCertI.Q4FVlo00
import Li2Lean.V.EnergyCertI.Q4FVlo01
import Li2Lean.V.EnergyCertI.Q4FVlo02
import Li2Lean.V.EnergyCertI.Q4FVlo03
import Li2Lean.V.EnergyCertI.Q4FVlo04
import Li2Lean.V.EnergyCertI.Q4FVlo05
import Li2Lean.V.EnergyCertI.Q4FVlo06
import Li2Lean.V.EnergyCertI.Q4FVlo07
import Li2Lean.V.EnergyCertI.Q4FVlo08
import Li2Lean.V.EnergyCertI.Q4FVlo09
import Li2Lean.V.EnergyCertI.Q4FX00
import Li2Lean.V.EnergyCertI.Q4FX01
import Li2Lean.V.EnergyCertI.Q4FX02
import Li2Lean.V.EnergyCertI.Q4FX03
import Li2Lean.V.EnergyCertI.Q4FX04
import Li2Lean.V.EnergyCertI.Q4FX05
import Li2Lean.V.EnergyCertI.Q4FX06
import Li2Lean.V.EnergyCertI.Q4FX07
import Li2Lean.V.EnergyCertI.Q4FZneg00
import Li2Lean.V.EnergyCertI.Q4FZneg01
import Li2Lean.V.EnergyCertI.Q4FZneg02
import Li2Lean.V.EnergyCertI.Q4FZneg03
import Li2Lean.V.EnergyCertI.Q4FZneg04
import Li2Lean.V.EnergyCertI.Q4FZneg05
import Li2Lean.V.EnergyCertI.Q4FZneg06
import Li2Lean.V.EnergyCertI.Q4FZneg07
import Li2Lean.V.EnergyCertI.Q4FZneg08
import Li2Lean.V.EnergyCertI.Q4FZneg09
import Li2Lean.V.EnergyCertI.Q4FZneg10
import Li2Lean.V.EnergyCertI.Q4FZneg11
import Li2Lean.V.EnergyCertI.Q4FZneg12
import Li2Lean.V.EnergyCertI.Q4FZneg13
import Li2Lean.V.EnergyCertI.Q4FZpos00

namespace Li2Lean.V.EnergyCertI

open IK

/-- Energy plan (kind, i0, i1, claim · 2^64); entry ↦ theorem `q4E_<kind>_<i0>_<i1>`. -/
def q4EnergyPlan : List (EKind × Nat × Nat × Int) := [
  (.selfX, 0, 41, -28757594321929087777),
  (.selfV, 0, 49, -41349836777635692874),
  (.selfZ, 0, 32, -1965724329603976947),
  (.selfZ, 32, 63, 67857096642567704),
  (.crossVZ, 0, 23, -2754809324682159871),
  (.crossVZ, 23, 46, -410824349570290622503),
  (.crossVZ, 46, 49, 427106472512558600712),
  (.intPoi, 0, 4, 128035668281660454),
  (.intPoi, 4, 8, 249232752972589154),
  (.intPoi, 8, 12, 332429709283646948),
  (.intPoi, 12, 16, 398948228451191831),
  (.intPoi, 16, 20, 450984052422905725),
  (.intPoi, 20, 24, 489679099232069663),
  (.intPoi, 24, 28, 515982132442742215),
  (.intPoi, 28, 32, 530804927968552393),
  (.intPoi, 32, 36, 535077905658268915),
  (.intPoi, 36, 40, 529778537542295638),
  (.intPoi, 40, 44, 515973188467067369),
  (.intPoi, 44, 48, 494817247489676681),
  (.intPoi, 48, 52, 467565700607782340),
  (.intPoi, 52, 56, 435563224531417485),
  (.intPoi, 56, 60, 400179041585206495),
  (.intPoi, 60, 64, 362784120858222200),
  (.intPoi, 64, 68, 324458951940022034),
  (.intPoi, 68, 71, 177551646879606941),
  (.pp, 0, 11, -192499273075730722),
  (.pp, 11, 23, -330830236345649667),
  (.pp, 23, 36, -367853811774668149),
  (.pp, 36, 51, -363758002133605074),
  (.pp, 51, 69, -324359677324752997),
  (.pp, 69, 94, -561068674222255714),
  (.pp, 94, 141, -948461765281838535),
  (.dq, 0, 1, -33878295119048910726)]

theorem q4EnergyClaims_gt_qlow : claimsGt q4EnergyPlan (qlowQ 4) = true := by decide +kernel

theorem q4EnergyPlan_tiles : energyPlanTiles q4D q4EnergyPlan = true := by decide +kernel

theorem q4F_x_chain :
    chainOK (1, 250) (1, 1) [q4F_x_000_b, q4F_x_001_b, q4F_x_002_b, q4F_x_003_b,
      q4F_x_004_b, q4F_x_005_b, q4F_x_006_b, q4F_x_007_b,
      q4F_x_008_b, q4F_x_009_b, q4F_x_010_b, q4F_x_011_b,
      q4F_x_012_b, q4F_x_013_b, q4F_x_014_b, q4F_x_015_b,
      q4F_x_016_b, q4F_x_017_b, q4F_x_018_b, q4F_x_019_b,
      q4F_x_020_b, q4F_x_021_b, q4F_x_022_b, q4F_x_023_b,
      q4F_x_024_b, q4F_x_025_b, q4F_x_026_b, q4F_x_027_b,
      q4F_x_028_b, q4F_x_029_b, q4F_x_030_b, q4F_x_031_b,
      q4F_x_032_b, q4F_x_033_b, q4F_x_034_b, q4F_x_035_b,
      q4F_x_036_b, q4F_x_037_b, q4F_x_038_b, q4F_x_039_b,
      q4F_x_040_b, q4F_x_041_b, q4F_x_042_b, q4F_x_043_b,
      q4F_x_044_b, q4F_x_045_b] = true := by
  decide +kernel

theorem q4F_vlo_chain :
    chainOK (1, 250) (3, 5) [q4F_vlo_000_b, q4F_vlo_001_b, q4F_vlo_002_b, q4F_vlo_003_b,
      q4F_vlo_004_b, q4F_vlo_005_b, q4F_vlo_006_b, q4F_vlo_007_b,
      q4F_vlo_008_b, q4F_vlo_009_b, q4F_vlo_010_b, q4F_vlo_011_b,
      q4F_vlo_012_b, q4F_vlo_013_b, q4F_vlo_014_b, q4F_vlo_015_b,
      q4F_vlo_016_b, q4F_vlo_017_b, q4F_vlo_018_b, q4F_vlo_019_b,
      q4F_vlo_020_b, q4F_vlo_021_b, q4F_vlo_022_b, q4F_vlo_023_b,
      q4F_vlo_024_b, q4F_vlo_025_b, q4F_vlo_026_b, q4F_vlo_027_b,
      q4F_vlo_028_b, q4F_vlo_029_b, q4F_vlo_030_b, q4F_vlo_031_b,
      q4F_vlo_032_b, q4F_vlo_033_b, q4F_vlo_034_b, q4F_vlo_035_b,
      q4F_vlo_036_b, q4F_vlo_037_b, q4F_vlo_038_b, q4F_vlo_039_b,
      q4F_vlo_040_b, q4F_vlo_041_b, q4F_vlo_042_b, q4F_vlo_043_b,
      q4F_vlo_044_b, q4F_vlo_045_b, q4F_vlo_046_b, q4F_vlo_047_b,
      q4F_vlo_048_b, q4F_vlo_049_b, q4F_vlo_050_b, q4F_vlo_051_b,
      q4F_vlo_052_b, q4F_vlo_053_b, q4F_vlo_054_b, q4F_vlo_055_b,
      q4F_vlo_056_b, q4F_vlo_057_b, q4F_vlo_058_b, q4F_vlo_059_b,
      q4F_vlo_060_b, q4F_vlo_061_b, q4F_vlo_062_b, q4F_vlo_063_b,
      q4F_vlo_064_b, q4F_vlo_065_b, q4F_vlo_066_b, q4F_vlo_067_b] = true := by
  decide +kernel

theorem q4F_vhi_chain :
    chainOK (3, 5) (1, 1) [q4F_vhi_000_b, q4F_vhi_001_b, q4F_vhi_002_b, q4F_vhi_003_b,
      q4F_vhi_004_b, q4F_vhi_005_b, q4F_vhi_006_b, q4F_vhi_007_b,
      q4F_vhi_008_b, q4F_vhi_009_b, q4F_vhi_010_b, q4F_vhi_011_b,
      q4F_vhi_012_b, q4F_vhi_013_b, q4F_vhi_014_b, q4F_vhi_015_b,
      q4F_vhi_016_b, q4F_vhi_017_b, q4F_vhi_018_b, q4F_vhi_019_b,
      q4F_vhi_020_b, q4F_vhi_021_b, q4F_vhi_022_b, q4F_vhi_023_b,
      q4F_vhi_024_b, q4F_vhi_025_b, q4F_vhi_026_b, q4F_vhi_027_b,
      q4F_vhi_028_b, q4F_vhi_029_b, q4F_vhi_030_b, q4F_vhi_031_b,
      q4F_vhi_032_b, q4F_vhi_033_b, q4F_vhi_034_b, q4F_vhi_035_b,
      q4F_vhi_036_b, q4F_vhi_037_b, q4F_vhi_038_b, q4F_vhi_039_b,
      q4F_vhi_040_b, q4F_vhi_041_b, q4F_vhi_042_b, q4F_vhi_043_b,
      q4F_vhi_044_b, q4F_vhi_045_b, q4F_vhi_046_b, q4F_vhi_047_b,
      q4F_vhi_048_b, q4F_vhi_049_b, q4F_vhi_050_b, q4F_vhi_051_b,
      q4F_vhi_052_b, q4F_vhi_053_b, q4F_vhi_054_b, q4F_vhi_055_b,
      q4F_vhi_056_b, q4F_vhi_057_b, q4F_vhi_058_b, q4F_vhi_059_b,
      q4F_vhi_060_b, q4F_vhi_061_b, q4F_vhi_062_b, q4F_vhi_063_b,
      q4F_vhi_064_b, q4F_vhi_065_b, q4F_vhi_066_b, q4F_vhi_067_b,
      q4F_vhi_068_b, q4F_vhi_069_b] = true := by
  decide +kernel

theorem q4F_zneg_chain :
    chainOK (-4, 1) (-3, 5) [q4F_zneg_000_b, q4F_zneg_001_b, q4F_zneg_002_b, q4F_zneg_003_b,
      q4F_zneg_004_b, q4F_zneg_005_b, q4F_zneg_006_b, q4F_zneg_007_b,
      q4F_zneg_008_b, q4F_zneg_009_b, q4F_zneg_010_b, q4F_zneg_011_b,
      q4F_zneg_012_b, q4F_zneg_013_b, q4F_zneg_014_b, q4F_zneg_015_b,
      q4F_zneg_016_b, q4F_zneg_017_b, q4F_zneg_018_b, q4F_zneg_019_b,
      q4F_zneg_020_b, q4F_zneg_021_b, q4F_zneg_022_b, q4F_zneg_023_b,
      q4F_zneg_024_b, q4F_zneg_025_b, q4F_zneg_026_b, q4F_zneg_027_b,
      q4F_zneg_028_b, q4F_zneg_029_b, q4F_zneg_030_b, q4F_zneg_031_b,
      q4F_zneg_032_b, q4F_zneg_033_b, q4F_zneg_034_b, q4F_zneg_035_b,
      q4F_zneg_036_b, q4F_zneg_037_b, q4F_zneg_038_b, q4F_zneg_039_b,
      q4F_zneg_040_b, q4F_zneg_041_b, q4F_zneg_042_b, q4F_zneg_043_b,
      q4F_zneg_044_b, q4F_zneg_045_b, q4F_zneg_046_b, q4F_zneg_047_b,
      q4F_zneg_048_b, q4F_zneg_049_b, q4F_zneg_050_b, q4F_zneg_051_b,
      q4F_zneg_052_b, q4F_zneg_053_b, q4F_zneg_054_b, q4F_zneg_055_b,
      q4F_zneg_056_b, q4F_zneg_057_b, q4F_zneg_058_b, q4F_zneg_059_b,
      q4F_zneg_060_b, q4F_zneg_061_b, q4F_zneg_062_b, q4F_zneg_063_b,
      q4F_zneg_064_b, q4F_zneg_065_b, q4F_zneg_066_b, q4F_zneg_067_b,
      q4F_zneg_068_b, q4F_zneg_069_b, q4F_zneg_070_b, q4F_zneg_071_b,
      q4F_zneg_072_b, q4F_zneg_073_b, q4F_zneg_074_b, q4F_zneg_075_b,
      q4F_zneg_076_b, q4F_zneg_077_b, q4F_zneg_078_b, q4F_zneg_079_b,
      q4F_zneg_080_b, q4F_zneg_081_b, q4F_zneg_082_b, q4F_zneg_083_b,
      q4F_zneg_084_b, q4F_zneg_085_b, q4F_zneg_086_b, q4F_zneg_087_b,
      q4F_zneg_088_b, q4F_zneg_089_b, q4F_zneg_090_b, q4F_zneg_091_b] = true := by
  decide +kernel

theorem q4F_zpos_chain :
    chainOK (3, 5) (1, 1) [q4F_zpos_000_b] = true := by
  decide +kernel

theorem q4F_arc1_chain :
    chainOK (0, 1) (1, 1) [q4F_arc1_000_b, q4F_arc1_001_b, q4F_arc1_002_b, q4F_arc1_003_b,
      q4F_arc1_004_b, q4F_arc1_005_b, q4F_arc1_006_b, q4F_arc1_007_b,
      q4F_arc1_008_b, q4F_arc1_009_b, q4F_arc1_010_b, q4F_arc1_011_b,
      q4F_arc1_012_b, q4F_arc1_013_b, q4F_arc1_014_b, q4F_arc1_015_b,
      q4F_arc1_016_b, q4F_arc1_017_b, q4F_arc1_018_b, q4F_arc1_019_b,
      q4F_arc1_020_b, q4F_arc1_021_b, q4F_arc1_022_b, q4F_arc1_023_b] = true := by
  decide +kernel

theorem q4F_arc2_chain :
    chainOK (0, 1) (1, 1) [q4F_arc2_000_b, q4F_arc2_001_b, q4F_arc2_002_b, q4F_arc2_003_b,
      q4F_arc2_004_b, q4F_arc2_005_b, q4F_arc2_006_b, q4F_arc2_007_b,
      q4F_arc2_008_b, q4F_arc2_009_b, q4F_arc2_010_b, q4F_arc2_011_b,
      q4F_arc2_012_b, q4F_arc2_013_b, q4F_arc2_014_b, q4F_arc2_015_b,
      q4F_arc2_016_b, q4F_arc2_017_b, q4F_arc2_018_b, q4F_arc2_019_b,
      q4F_arc2_020_b, q4F_arc2_021_b, q4F_arc2_022_b, q4F_arc2_023_b,
      q4F_arc2_024_b, q4F_arc2_025_b, q4F_arc2_026_b, q4F_arc2_027_b,
      q4F_arc2_028_b, q4F_arc2_029_b, q4F_arc2_030_b, q4F_arc2_031_b,
      q4F_arc2_032_b, q4F_arc2_033_b, q4F_arc2_034_b, q4F_arc2_035_b,
      q4F_arc2_036_b, q4F_arc2_037_b, q4F_arc2_038_b, q4F_arc2_039_b,
      q4F_arc2_040_b] = true := by
  decide +kernel

/-- Endpoint disks: directed `E_x, E_v` below the printed values, and these below `K`. -/
theorem q4Endpoint_check :
    (hiLe (exUB fieldMode q4D 4) (exQ 4) && hiLe (evUB fieldMode q4D 4) (evQ 4) &&
      qlt (exQ 4) (kxQ 4) && qlt (evQ 4) (kvQ 4)) = true := by
  decide +kernel

/-- `alpha_le`: `vAlpha q ≤ Qlow - 3/2·log q - Kx - 5/4·Kv - Kz`, `log q ≤ (logQ 3 (q,1)).2 / 2^64`. -/
theorem q4Alpha_check :
    qle (alphaQ 4) (qsub (qsub (qsub (qsub (qlowQ 4) (qmul (3, 2) ((logQ 3 (4, 1)).2, S)))
      (kxQ 4)) (qmul (5, 4) (kvQ 4))) (kzQ 4)) = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
