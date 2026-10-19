/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
/-
Generated certificate data
from v13 `v-reference-data.tex` (sha256 e3983e04...cd9b).  elaborated.
-/

import Li2Lean.V.EnergyCertI.Q5Energy00
import Li2Lean.V.EnergyCertI.Q5Energy01
import Li2Lean.V.EnergyCertI.Q5Energy02
import Li2Lean.V.EnergyCertI.Q5Energy03
import Li2Lean.V.EnergyCertI.Q5Energy04
import Li2Lean.V.EnergyCertI.Q5FArc100
import Li2Lean.V.EnergyCertI.Q5FArc101
import Li2Lean.V.EnergyCertI.Q5FArc102
import Li2Lean.V.EnergyCertI.Q5FArc103
import Li2Lean.V.EnergyCertI.Q5FArc200
import Li2Lean.V.EnergyCertI.Q5FArc201
import Li2Lean.V.EnergyCertI.Q5FArc202
import Li2Lean.V.EnergyCertI.Q5FArc203
import Li2Lean.V.EnergyCertI.Q5FArc204
import Li2Lean.V.EnergyCertI.Q5FArc205
import Li2Lean.V.EnergyCertI.Q5FVhi00
import Li2Lean.V.EnergyCertI.Q5FVhi01
import Li2Lean.V.EnergyCertI.Q5FVhi02
import Li2Lean.V.EnergyCertI.Q5FVhi03
import Li2Lean.V.EnergyCertI.Q5FVhi04
import Li2Lean.V.EnergyCertI.Q5FVhi05
import Li2Lean.V.EnergyCertI.Q5FVhi06
import Li2Lean.V.EnergyCertI.Q5FVhi07
import Li2Lean.V.EnergyCertI.Q5FVhi08
import Li2Lean.V.EnergyCertI.Q5FVhi09
import Li2Lean.V.EnergyCertI.Q5FVlo00
import Li2Lean.V.EnergyCertI.Q5FVlo01
import Li2Lean.V.EnergyCertI.Q5FVlo02
import Li2Lean.V.EnergyCertI.Q5FVlo03
import Li2Lean.V.EnergyCertI.Q5FVlo04
import Li2Lean.V.EnergyCertI.Q5FVlo05
import Li2Lean.V.EnergyCertI.Q5FVlo06
import Li2Lean.V.EnergyCertI.Q5FVlo07
import Li2Lean.V.EnergyCertI.Q5FVlo08
import Li2Lean.V.EnergyCertI.Q5FVlo09
import Li2Lean.V.EnergyCertI.Q5FX00
import Li2Lean.V.EnergyCertI.Q5FX01
import Li2Lean.V.EnergyCertI.Q5FX02
import Li2Lean.V.EnergyCertI.Q5FX03
import Li2Lean.V.EnergyCertI.Q5FX04
import Li2Lean.V.EnergyCertI.Q5FX05
import Li2Lean.V.EnergyCertI.Q5FX06
import Li2Lean.V.EnergyCertI.Q5FX07
import Li2Lean.V.EnergyCertI.Q5FZneg00
import Li2Lean.V.EnergyCertI.Q5FZneg01
import Li2Lean.V.EnergyCertI.Q5FZneg02
import Li2Lean.V.EnergyCertI.Q5FZneg03
import Li2Lean.V.EnergyCertI.Q5FZneg04
import Li2Lean.V.EnergyCertI.Q5FZneg05
import Li2Lean.V.EnergyCertI.Q5FZneg06
import Li2Lean.V.EnergyCertI.Q5FZneg07
import Li2Lean.V.EnergyCertI.Q5FZneg08
import Li2Lean.V.EnergyCertI.Q5FZneg09
import Li2Lean.V.EnergyCertI.Q5FZneg10
import Li2Lean.V.EnergyCertI.Q5FZneg11
import Li2Lean.V.EnergyCertI.Q5FZneg12
import Li2Lean.V.EnergyCertI.Q5FZneg13
import Li2Lean.V.EnergyCertI.Q5FZneg14
import Li2Lean.V.EnergyCertI.Q5FZpos00

namespace Li2Lean.V.EnergyCertI

open IK

/-- Energy plan (kind, i0, i1, claim · 2^64); entry ↦ theorem `q5E_<kind>_<i0>_<i1>`. -/
def q5EnergyPlan : List (EKind × Nat × Nat × Int) := [
  (.selfX, 0, 40, -28811670653696480874),
  (.selfV, 0, 49, -41341108288904296042),
  (.selfZ, 0, 32, -774139004861776397),
  (.selfZ, 32, 63, 59967029142272546),
  (.crossVZ, 0, 23, -10535133104076533992),
  (.crossVZ, 23, 46, -727308423950856000122),
  (.crossVZ, 46, 49, 754437490657963840167),
  (.intPoi, 0, 4, 227250660341942726),
  (.intPoi, 4, 8, 369026621660544538),
  (.intPoi, 8, 12, 463459462583513272),
  (.intPoi, 12, 16, 534463733819664759),
  (.intPoi, 16, 20, 587227851880753879),
  (.intPoi, 20, 24, 624419325897810440),
  (.intPoi, 24, 28, 647853326916937979),
  (.intPoi, 28, 32, 658989969022148635),
  (.intPoi, 32, 36, 659135425618522031),
  (.intPoi, 36, 40, 649523000291385694),
  (.intPoi, 40, 44, 631372910850771250),
  (.intPoi, 44, 48, 605951208970652414),
  (.intPoi, 48, 52, 574532329478951512),
  (.intPoi, 52, 56, 538421689456138669),
  (.intPoi, 56, 60, 498885167413320675),
  (.intPoi, 60, 64, 457026579804604043),
  (.intPoi, 64, 68, 415075317156660420),
  (.intPoi, 68, 69, 38726814175714526),
  (.pp, 0, 11, -175545301089016949),
  (.pp, 11, 23, -289159598460680063),
  (.pp, 23, 36, -320480497861865201),
  (.pp, 36, 52, -337803968144204141),
  (.pp, 52, 71, -302285962648152416),
  (.pp, 71, 99, -631723806881494613),
  (.pp, 99, 137, -595815225094322797),
  (.dq, 0, 1, -38663558699897852709)]

theorem q5EnergyClaims_gt_qlow : claimsGt q5EnergyPlan (qlowQ 5) = true := by decide +kernel

theorem q5EnergyPlan_tiles : energyPlanTiles q5D q5EnergyPlan = true := by decide +kernel

theorem q5F_x_chain :
    chainOK (1, 250) (1, 1) [q5F_x_000_b, q5F_x_001_b, q5F_x_002_b, q5F_x_003_b,
      q5F_x_004_b, q5F_x_005_b, q5F_x_006_b, q5F_x_007_b,
      q5F_x_008_b, q5F_x_009_b, q5F_x_010_b, q5F_x_011_b,
      q5F_x_012_b, q5F_x_013_b, q5F_x_014_b, q5F_x_015_b,
      q5F_x_016_b, q5F_x_017_b, q5F_x_018_b, q5F_x_019_b,
      q5F_x_020_b, q5F_x_021_b, q5F_x_022_b, q5F_x_023_b,
      q5F_x_024_b, q5F_x_025_b, q5F_x_026_b, q5F_x_027_b,
      q5F_x_028_b, q5F_x_029_b, q5F_x_030_b, q5F_x_031_b,
      q5F_x_032_b, q5F_x_033_b, q5F_x_034_b, q5F_x_035_b,
      q5F_x_036_b, q5F_x_037_b, q5F_x_038_b, q5F_x_039_b,
      q5F_x_040_b, q5F_x_041_b, q5F_x_042_b, q5F_x_043_b,
      q5F_x_044_b, q5F_x_045_b] = true := by
  decide +kernel

theorem q5F_vlo_chain :
    chainOK (1, 250) (3, 5) [q5F_vlo_000_b, q5F_vlo_001_b, q5F_vlo_002_b, q5F_vlo_003_b,
      q5F_vlo_004_b, q5F_vlo_005_b, q5F_vlo_006_b, q5F_vlo_007_b,
      q5F_vlo_008_b, q5F_vlo_009_b, q5F_vlo_010_b, q5F_vlo_011_b,
      q5F_vlo_012_b, q5F_vlo_013_b, q5F_vlo_014_b, q5F_vlo_015_b,
      q5F_vlo_016_b, q5F_vlo_017_b, q5F_vlo_018_b, q5F_vlo_019_b,
      q5F_vlo_020_b, q5F_vlo_021_b, q5F_vlo_022_b, q5F_vlo_023_b,
      q5F_vlo_024_b, q5F_vlo_025_b, q5F_vlo_026_b, q5F_vlo_027_b,
      q5F_vlo_028_b, q5F_vlo_029_b, q5F_vlo_030_b, q5F_vlo_031_b,
      q5F_vlo_032_b, q5F_vlo_033_b, q5F_vlo_034_b, q5F_vlo_035_b,
      q5F_vlo_036_b, q5F_vlo_037_b, q5F_vlo_038_b, q5F_vlo_039_b,
      q5F_vlo_040_b, q5F_vlo_041_b, q5F_vlo_042_b, q5F_vlo_043_b,
      q5F_vlo_044_b, q5F_vlo_045_b, q5F_vlo_046_b, q5F_vlo_047_b,
      q5F_vlo_048_b, q5F_vlo_049_b, q5F_vlo_050_b, q5F_vlo_051_b,
      q5F_vlo_052_b, q5F_vlo_053_b, q5F_vlo_054_b, q5F_vlo_055_b,
      q5F_vlo_056_b, q5F_vlo_057_b, q5F_vlo_058_b, q5F_vlo_059_b,
      q5F_vlo_060_b, q5F_vlo_061_b, q5F_vlo_062_b, q5F_vlo_063_b,
      q5F_vlo_064_b, q5F_vlo_065_b] = true := by
  decide +kernel

theorem q5F_vhi_chain :
    chainOK (3, 5) (1, 1) [q5F_vhi_000_b, q5F_vhi_001_b, q5F_vhi_002_b, q5F_vhi_003_b,
      q5F_vhi_004_b, q5F_vhi_005_b, q5F_vhi_006_b, q5F_vhi_007_b,
      q5F_vhi_008_b, q5F_vhi_009_b, q5F_vhi_010_b, q5F_vhi_011_b,
      q5F_vhi_012_b, q5F_vhi_013_b, q5F_vhi_014_b, q5F_vhi_015_b,
      q5F_vhi_016_b, q5F_vhi_017_b, q5F_vhi_018_b, q5F_vhi_019_b,
      q5F_vhi_020_b, q5F_vhi_021_b, q5F_vhi_022_b, q5F_vhi_023_b,
      q5F_vhi_024_b, q5F_vhi_025_b, q5F_vhi_026_b, q5F_vhi_027_b,
      q5F_vhi_028_b, q5F_vhi_029_b, q5F_vhi_030_b, q5F_vhi_031_b,
      q5F_vhi_032_b, q5F_vhi_033_b, q5F_vhi_034_b, q5F_vhi_035_b,
      q5F_vhi_036_b, q5F_vhi_037_b, q5F_vhi_038_b, q5F_vhi_039_b,
      q5F_vhi_040_b, q5F_vhi_041_b, q5F_vhi_042_b, q5F_vhi_043_b,
      q5F_vhi_044_b, q5F_vhi_045_b, q5F_vhi_046_b, q5F_vhi_047_b,
      q5F_vhi_048_b, q5F_vhi_049_b, q5F_vhi_050_b, q5F_vhi_051_b,
      q5F_vhi_052_b, q5F_vhi_053_b, q5F_vhi_054_b, q5F_vhi_055_b,
      q5F_vhi_056_b, q5F_vhi_057_b, q5F_vhi_058_b, q5F_vhi_059_b,
      q5F_vhi_060_b, q5F_vhi_061_b, q5F_vhi_062_b, q5F_vhi_063_b,
      q5F_vhi_064_b, q5F_vhi_065_b, q5F_vhi_066_b, q5F_vhi_067_b,
      q5F_vhi_068_b] = true := by
  decide +kernel

theorem q5F_zneg_chain :
    chainOK (-5, 1) (-3, 5) [q5F_zneg_000_b, q5F_zneg_001_b, q5F_zneg_002_b, q5F_zneg_003_b,
      q5F_zneg_004_b, q5F_zneg_005_b, q5F_zneg_006_b, q5F_zneg_007_b,
      q5F_zneg_008_b, q5F_zneg_009_b, q5F_zneg_010_b, q5F_zneg_011_b,
      q5F_zneg_012_b, q5F_zneg_013_b, q5F_zneg_014_b, q5F_zneg_015_b,
      q5F_zneg_016_b, q5F_zneg_017_b, q5F_zneg_018_b, q5F_zneg_019_b,
      q5F_zneg_020_b, q5F_zneg_021_b, q5F_zneg_022_b, q5F_zneg_023_b,
      q5F_zneg_024_b, q5F_zneg_025_b, q5F_zneg_026_b, q5F_zneg_027_b,
      q5F_zneg_028_b, q5F_zneg_029_b, q5F_zneg_030_b, q5F_zneg_031_b,
      q5F_zneg_032_b, q5F_zneg_033_b, q5F_zneg_034_b, q5F_zneg_035_b,
      q5F_zneg_036_b, q5F_zneg_037_b, q5F_zneg_038_b, q5F_zneg_039_b,
      q5F_zneg_040_b, q5F_zneg_041_b, q5F_zneg_042_b, q5F_zneg_043_b,
      q5F_zneg_044_b, q5F_zneg_045_b, q5F_zneg_046_b, q5F_zneg_047_b,
      q5F_zneg_048_b, q5F_zneg_049_b, q5F_zneg_050_b, q5F_zneg_051_b,
      q5F_zneg_052_b, q5F_zneg_053_b, q5F_zneg_054_b, q5F_zneg_055_b,
      q5F_zneg_056_b, q5F_zneg_057_b, q5F_zneg_058_b, q5F_zneg_059_b,
      q5F_zneg_060_b, q5F_zneg_061_b, q5F_zneg_062_b, q5F_zneg_063_b,
      q5F_zneg_064_b, q5F_zneg_065_b, q5F_zneg_066_b, q5F_zneg_067_b,
      q5F_zneg_068_b, q5F_zneg_069_b, q5F_zneg_070_b, q5F_zneg_071_b,
      q5F_zneg_072_b, q5F_zneg_073_b, q5F_zneg_074_b, q5F_zneg_075_b,
      q5F_zneg_076_b, q5F_zneg_077_b, q5F_zneg_078_b, q5F_zneg_079_b,
      q5F_zneg_080_b, q5F_zneg_081_b, q5F_zneg_082_b, q5F_zneg_083_b,
      q5F_zneg_084_b, q5F_zneg_085_b, q5F_zneg_086_b] = true := by
  decide +kernel

theorem q5F_zpos_chain :
    chainOK (3, 5) (1, 1) [q5F_zpos_000_b] = true := by
  decide +kernel

theorem q5F_arc1_chain :
    chainOK (0, 1) (1, 1) [q5F_arc1_000_b, q5F_arc1_001_b, q5F_arc1_002_b, q5F_arc1_003_b,
      q5F_arc1_004_b, q5F_arc1_005_b, q5F_arc1_006_b, q5F_arc1_007_b,
      q5F_arc1_008_b, q5F_arc1_009_b, q5F_arc1_010_b, q5F_arc1_011_b,
      q5F_arc1_012_b, q5F_arc1_013_b, q5F_arc1_014_b, q5F_arc1_015_b,
      q5F_arc1_016_b, q5F_arc1_017_b, q5F_arc1_018_b, q5F_arc1_019_b,
      q5F_arc1_020_b, q5F_arc1_021_b] = true := by
  decide +kernel

theorem q5F_arc2_chain :
    chainOK (0, 1) (1, 1) [q5F_arc2_000_b, q5F_arc2_001_b, q5F_arc2_002_b, q5F_arc2_003_b,
      q5F_arc2_004_b, q5F_arc2_005_b, q5F_arc2_006_b, q5F_arc2_007_b,
      q5F_arc2_008_b, q5F_arc2_009_b, q5F_arc2_010_b, q5F_arc2_011_b,
      q5F_arc2_012_b, q5F_arc2_013_b, q5F_arc2_014_b, q5F_arc2_015_b,
      q5F_arc2_016_b, q5F_arc2_017_b, q5F_arc2_018_b, q5F_arc2_019_b,
      q5F_arc2_020_b, q5F_arc2_021_b, q5F_arc2_022_b, q5F_arc2_023_b,
      q5F_arc2_024_b, q5F_arc2_025_b, q5F_arc2_026_b, q5F_arc2_027_b,
      q5F_arc2_028_b, q5F_arc2_029_b, q5F_arc2_030_b, q5F_arc2_031_b,
      q5F_arc2_032_b, q5F_arc2_033_b, q5F_arc2_034_b, q5F_arc2_035_b,
      q5F_arc2_036_b, q5F_arc2_037_b, q5F_arc2_038_b, q5F_arc2_039_b] = true := by
  decide +kernel

/-- Endpoint disks: directed `E_x, E_v` below the printed values, and these below `K`. -/
theorem q5Endpoint_check :
    (hiLe (exUB fieldMode q5D 5) (exQ 5) && hiLe (evUB fieldMode q5D 5) (evQ 5) &&
      qlt (exQ 5) (kxQ 5) && qlt (evQ 5) (kvQ 5)) = true := by
  decide +kernel

/-- `alpha_le`: `vAlpha q ≤ Qlow - 3/2·log q - Kx - 5/4·Kv - Kz`, `log q ≤ (logQ 3 (q,1)).2 / 2^64`. -/
theorem q5Alpha_check :
    qle (alphaQ 5) (qsub (qsub (qsub (qsub (qlowQ 5) (qmul (3, 2) ((logQ 3 (5, 1)).2, S)))
      (kxQ 5)) (qmul (5, 4) (kvQ 5))) (kzQ 5)) = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
