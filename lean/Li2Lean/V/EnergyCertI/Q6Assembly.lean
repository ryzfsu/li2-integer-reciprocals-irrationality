/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
/-
Generated certificate data
from v13 `v-reference-data.tex` (sha256 e3983e04...cd9b).  elaborated.
-/

import Li2Lean.V.EnergyCertI.Q6Energy00
import Li2Lean.V.EnergyCertI.Q6Energy01
import Li2Lean.V.EnergyCertI.Q6Energy02
import Li2Lean.V.EnergyCertI.Q6Energy03
import Li2Lean.V.EnergyCertI.Q6Energy04
import Li2Lean.V.EnergyCertI.Q6FArc100
import Li2Lean.V.EnergyCertI.Q6FArc101
import Li2Lean.V.EnergyCertI.Q6FArc102
import Li2Lean.V.EnergyCertI.Q6FArc200
import Li2Lean.V.EnergyCertI.Q6FArc201
import Li2Lean.V.EnergyCertI.Q6FArc202
import Li2Lean.V.EnergyCertI.Q6FArc203
import Li2Lean.V.EnergyCertI.Q6FArc204
import Li2Lean.V.EnergyCertI.Q6FArc205
import Li2Lean.V.EnergyCertI.Q6FVhi00
import Li2Lean.V.EnergyCertI.Q6FVhi01
import Li2Lean.V.EnergyCertI.Q6FVhi02
import Li2Lean.V.EnergyCertI.Q6FVhi03
import Li2Lean.V.EnergyCertI.Q6FVhi04
import Li2Lean.V.EnergyCertI.Q6FVhi05
import Li2Lean.V.EnergyCertI.Q6FVhi06
import Li2Lean.V.EnergyCertI.Q6FVhi07
import Li2Lean.V.EnergyCertI.Q6FVhi08
import Li2Lean.V.EnergyCertI.Q6FVhi09
import Li2Lean.V.EnergyCertI.Q6FVlo00
import Li2Lean.V.EnergyCertI.Q6FVlo01
import Li2Lean.V.EnergyCertI.Q6FVlo02
import Li2Lean.V.EnergyCertI.Q6FVlo03
import Li2Lean.V.EnergyCertI.Q6FVlo04
import Li2Lean.V.EnergyCertI.Q6FVlo05
import Li2Lean.V.EnergyCertI.Q6FVlo06
import Li2Lean.V.EnergyCertI.Q6FVlo07
import Li2Lean.V.EnergyCertI.Q6FVlo08
import Li2Lean.V.EnergyCertI.Q6FVlo09
import Li2Lean.V.EnergyCertI.Q6FX00
import Li2Lean.V.EnergyCertI.Q6FX01
import Li2Lean.V.EnergyCertI.Q6FX02
import Li2Lean.V.EnergyCertI.Q6FX03
import Li2Lean.V.EnergyCertI.Q6FX04
import Li2Lean.V.EnergyCertI.Q6FX05
import Li2Lean.V.EnergyCertI.Q6FX06
import Li2Lean.V.EnergyCertI.Q6FX07
import Li2Lean.V.EnergyCertI.Q6FZneg00
import Li2Lean.V.EnergyCertI.Q6FZneg01
import Li2Lean.V.EnergyCertI.Q6FZneg02
import Li2Lean.V.EnergyCertI.Q6FZneg03
import Li2Lean.V.EnergyCertI.Q6FZneg04
import Li2Lean.V.EnergyCertI.Q6FZneg05
import Li2Lean.V.EnergyCertI.Q6FZneg06
import Li2Lean.V.EnergyCertI.Q6FZneg07
import Li2Lean.V.EnergyCertI.Q6FZneg08
import Li2Lean.V.EnergyCertI.Q6FZneg09
import Li2Lean.V.EnergyCertI.Q6FZneg10
import Li2Lean.V.EnergyCertI.Q6FZneg11
import Li2Lean.V.EnergyCertI.Q6FZneg12
import Li2Lean.V.EnergyCertI.Q6FZneg13
import Li2Lean.V.EnergyCertI.Q6FZneg14
import Li2Lean.V.EnergyCertI.Q6FZpos00

namespace Li2Lean.V.EnergyCertI

open IK

/-- Energy plan (kind, i0, i1, claim · 2^64); entry ↦ theorem `q6E_<kind>_<i0>_<i1>`. -/
def q6EnergyPlan : List (EKind × Nat × Nat × Int) := [
  (.selfX, 0, 42, -28847670510885277787),
  (.selfV, 0, 48, -41328903187849201394),
  (.selfZ, 0, 33, 504352036037531782),
  (.selfZ, 33, 62, 43292736212840066),
  (.crossVZ, 0, 24, -22390562531108966073),
  (.crossVZ, 24, 48, 41666457999065193827),
  (.intPoi, 0, 4, 250961944560195504),
  (.intPoi, 4, 8, 441950503088846314),
  (.intPoi, 8, 12, 550043052990228166),
  (.intPoi, 12, 16, 628116332234208291),
  (.intPoi, 16, 20, 684547154218891055),
  (.intPoi, 20, 24, 723371502867661712),
  (.intPoi, 24, 28, 747151295305072274),
  (.intPoi, 28, 32, 757815411804873463),
  (.intPoi, 32, 36, 756959720058989380),
  (.intPoi, 36, 40, 746008339003462556),
  (.intPoi, 40, 44, 726302360134910642),
  (.intPoi, 44, 48, 699168475709062645),
  (.intPoi, 48, 52, 665889028860292222),
  (.intPoi, 52, 56, 627729646118590056),
  (.intPoi, 56, 60, 585868261483214000),
  (.intPoi, 60, 64, 541106592787622117),
  (.intPoi, 64, 68, 424278474370743786),
  (.pp, 0, 11, -149123136728204567),
  (.pp, 11, 23, -257696854280082557),
  (.pp, 23, 37, -310375705683315191),
  (.pp, 37, 53, -305339707149143636),
  (.pp, 53, 73, -301419925605454383),
  (.pp, 73, 105, -685249769965688312),
  (.pp, 105, 135, -340157871938346253),
  (.dq, 0, 1, -42621153227233062795)]

theorem q6EnergyClaims_gt_qlow : claimsGt q6EnergyPlan (qlowQ 6) = true := by decide +kernel

theorem q6EnergyPlan_tiles : energyPlanTiles q6D q6EnergyPlan = true := by decide +kernel

theorem q6F_x_chain :
    chainOK (1, 250) (1, 1) [q6F_x_000_b, q6F_x_001_b, q6F_x_002_b, q6F_x_003_b,
      q6F_x_004_b, q6F_x_005_b, q6F_x_006_b, q6F_x_007_b,
      q6F_x_008_b, q6F_x_009_b, q6F_x_010_b, q6F_x_011_b,
      q6F_x_012_b, q6F_x_013_b, q6F_x_014_b, q6F_x_015_b,
      q6F_x_016_b, q6F_x_017_b, q6F_x_018_b, q6F_x_019_b,
      q6F_x_020_b, q6F_x_021_b, q6F_x_022_b, q6F_x_023_b,
      q6F_x_024_b, q6F_x_025_b, q6F_x_026_b, q6F_x_027_b,
      q6F_x_028_b, q6F_x_029_b, q6F_x_030_b, q6F_x_031_b,
      q6F_x_032_b, q6F_x_033_b, q6F_x_034_b, q6F_x_035_b,
      q6F_x_036_b, q6F_x_037_b, q6F_x_038_b, q6F_x_039_b,
      q6F_x_040_b, q6F_x_041_b, q6F_x_042_b, q6F_x_043_b,
      q6F_x_044_b] = true := by
  decide +kernel

theorem q6F_vlo_chain :
    chainOK (1, 250) (3, 5) [q6F_vlo_000_b, q6F_vlo_001_b, q6F_vlo_002_b, q6F_vlo_003_b,
      q6F_vlo_004_b, q6F_vlo_005_b, q6F_vlo_006_b, q6F_vlo_007_b,
      q6F_vlo_008_b, q6F_vlo_009_b, q6F_vlo_010_b, q6F_vlo_011_b,
      q6F_vlo_012_b, q6F_vlo_013_b, q6F_vlo_014_b, q6F_vlo_015_b,
      q6F_vlo_016_b, q6F_vlo_017_b, q6F_vlo_018_b, q6F_vlo_019_b,
      q6F_vlo_020_b, q6F_vlo_021_b, q6F_vlo_022_b, q6F_vlo_023_b,
      q6F_vlo_024_b, q6F_vlo_025_b, q6F_vlo_026_b, q6F_vlo_027_b,
      q6F_vlo_028_b, q6F_vlo_029_b, q6F_vlo_030_b, q6F_vlo_031_b,
      q6F_vlo_032_b, q6F_vlo_033_b, q6F_vlo_034_b, q6F_vlo_035_b,
      q6F_vlo_036_b, q6F_vlo_037_b, q6F_vlo_038_b, q6F_vlo_039_b,
      q6F_vlo_040_b, q6F_vlo_041_b, q6F_vlo_042_b, q6F_vlo_043_b,
      q6F_vlo_044_b, q6F_vlo_045_b, q6F_vlo_046_b, q6F_vlo_047_b,
      q6F_vlo_048_b, q6F_vlo_049_b, q6F_vlo_050_b, q6F_vlo_051_b,
      q6F_vlo_052_b, q6F_vlo_053_b, q6F_vlo_054_b, q6F_vlo_055_b,
      q6F_vlo_056_b, q6F_vlo_057_b, q6F_vlo_058_b, q6F_vlo_059_b,
      q6F_vlo_060_b, q6F_vlo_061_b, q6F_vlo_062_b, q6F_vlo_063_b,
      q6F_vlo_064_b, q6F_vlo_065_b, q6F_vlo_066_b] = true := by
  decide +kernel

theorem q6F_vhi_chain :
    chainOK (3, 5) (1, 1) [q6F_vhi_000_b, q6F_vhi_001_b, q6F_vhi_002_b, q6F_vhi_003_b,
      q6F_vhi_004_b, q6F_vhi_005_b, q6F_vhi_006_b, q6F_vhi_007_b,
      q6F_vhi_008_b, q6F_vhi_009_b, q6F_vhi_010_b, q6F_vhi_011_b,
      q6F_vhi_012_b, q6F_vhi_013_b, q6F_vhi_014_b, q6F_vhi_015_b,
      q6F_vhi_016_b, q6F_vhi_017_b, q6F_vhi_018_b, q6F_vhi_019_b,
      q6F_vhi_020_b, q6F_vhi_021_b, q6F_vhi_022_b, q6F_vhi_023_b,
      q6F_vhi_024_b, q6F_vhi_025_b, q6F_vhi_026_b, q6F_vhi_027_b,
      q6F_vhi_028_b, q6F_vhi_029_b, q6F_vhi_030_b, q6F_vhi_031_b,
      q6F_vhi_032_b, q6F_vhi_033_b, q6F_vhi_034_b, q6F_vhi_035_b,
      q6F_vhi_036_b, q6F_vhi_037_b, q6F_vhi_038_b, q6F_vhi_039_b,
      q6F_vhi_040_b, q6F_vhi_041_b, q6F_vhi_042_b, q6F_vhi_043_b,
      q6F_vhi_044_b, q6F_vhi_045_b, q6F_vhi_046_b, q6F_vhi_047_b,
      q6F_vhi_048_b, q6F_vhi_049_b, q6F_vhi_050_b, q6F_vhi_051_b,
      q6F_vhi_052_b, q6F_vhi_053_b, q6F_vhi_054_b, q6F_vhi_055_b,
      q6F_vhi_056_b, q6F_vhi_057_b, q6F_vhi_058_b, q6F_vhi_059_b,
      q6F_vhi_060_b, q6F_vhi_061_b, q6F_vhi_062_b, q6F_vhi_063_b,
      q6F_vhi_064_b, q6F_vhi_065_b, q6F_vhi_066_b, q6F_vhi_067_b,
      q6F_vhi_068_b, q6F_vhi_069_b] = true := by
  decide +kernel

theorem q6F_zneg_chain :
    chainOK (-6, 1) (-3, 5) [q6F_zneg_000_b, q6F_zneg_001_b, q6F_zneg_002_b, q6F_zneg_003_b,
      q6F_zneg_004_b, q6F_zneg_005_b, q6F_zneg_006_b, q6F_zneg_007_b,
      q6F_zneg_008_b, q6F_zneg_009_b, q6F_zneg_010_b, q6F_zneg_011_b,
      q6F_zneg_012_b, q6F_zneg_013_b, q6F_zneg_014_b, q6F_zneg_015_b,
      q6F_zneg_016_b, q6F_zneg_017_b, q6F_zneg_018_b, q6F_zneg_019_b,
      q6F_zneg_020_b, q6F_zneg_021_b, q6F_zneg_022_b, q6F_zneg_023_b,
      q6F_zneg_024_b, q6F_zneg_025_b, q6F_zneg_026_b, q6F_zneg_027_b,
      q6F_zneg_028_b, q6F_zneg_029_b, q6F_zneg_030_b, q6F_zneg_031_b,
      q6F_zneg_032_b, q6F_zneg_033_b, q6F_zneg_034_b, q6F_zneg_035_b,
      q6F_zneg_036_b, q6F_zneg_037_b, q6F_zneg_038_b, q6F_zneg_039_b,
      q6F_zneg_040_b, q6F_zneg_041_b, q6F_zneg_042_b, q6F_zneg_043_b,
      q6F_zneg_044_b, q6F_zneg_045_b, q6F_zneg_046_b, q6F_zneg_047_b,
      q6F_zneg_048_b, q6F_zneg_049_b, q6F_zneg_050_b, q6F_zneg_051_b,
      q6F_zneg_052_b, q6F_zneg_053_b, q6F_zneg_054_b, q6F_zneg_055_b,
      q6F_zneg_056_b, q6F_zneg_057_b, q6F_zneg_058_b, q6F_zneg_059_b,
      q6F_zneg_060_b, q6F_zneg_061_b, q6F_zneg_062_b, q6F_zneg_063_b,
      q6F_zneg_064_b, q6F_zneg_065_b, q6F_zneg_066_b, q6F_zneg_067_b,
      q6F_zneg_068_b, q6F_zneg_069_b, q6F_zneg_070_b, q6F_zneg_071_b,
      q6F_zneg_072_b, q6F_zneg_073_b, q6F_zneg_074_b, q6F_zneg_075_b,
      q6F_zneg_076_b, q6F_zneg_077_b, q6F_zneg_078_b, q6F_zneg_079_b,
      q6F_zneg_080_b, q6F_zneg_081_b, q6F_zneg_082_b, q6F_zneg_083_b,
      q6F_zneg_084_b, q6F_zneg_085_b, q6F_zneg_086_b, q6F_zneg_087_b] = true := by
  decide +kernel

theorem q6F_zpos_chain :
    chainOK (3, 5) (1, 1) [q6F_zpos_000_b] = true := by
  decide +kernel

theorem q6F_arc1_chain :
    chainOK (0, 1) (1, 1) [q6F_arc1_000_b, q6F_arc1_001_b, q6F_arc1_002_b, q6F_arc1_003_b,
      q6F_arc1_004_b, q6F_arc1_005_b, q6F_arc1_006_b, q6F_arc1_007_b,
      q6F_arc1_008_b, q6F_arc1_009_b, q6F_arc1_010_b, q6F_arc1_011_b,
      q6F_arc1_012_b, q6F_arc1_013_b, q6F_arc1_014_b, q6F_arc1_015_b,
      q6F_arc1_016_b, q6F_arc1_017_b, q6F_arc1_018_b, q6F_arc1_019_b,
      q6F_arc1_020_b] = true := by
  decide +kernel

theorem q6F_arc2_chain :
    chainOK (0, 1) (1, 1) [q6F_arc2_000_b, q6F_arc2_001_b, q6F_arc2_002_b, q6F_arc2_003_b,
      q6F_arc2_004_b, q6F_arc2_005_b, q6F_arc2_006_b, q6F_arc2_007_b,
      q6F_arc2_008_b, q6F_arc2_009_b, q6F_arc2_010_b, q6F_arc2_011_b,
      q6F_arc2_012_b, q6F_arc2_013_b, q6F_arc2_014_b, q6F_arc2_015_b,
      q6F_arc2_016_b, q6F_arc2_017_b, q6F_arc2_018_b, q6F_arc2_019_b,
      q6F_arc2_020_b, q6F_arc2_021_b, q6F_arc2_022_b, q6F_arc2_023_b,
      q6F_arc2_024_b, q6F_arc2_025_b, q6F_arc2_026_b, q6F_arc2_027_b,
      q6F_arc2_028_b, q6F_arc2_029_b, q6F_arc2_030_b, q6F_arc2_031_b,
      q6F_arc2_032_b, q6F_arc2_033_b, q6F_arc2_034_b, q6F_arc2_035_b,
      q6F_arc2_036_b, q6F_arc2_037_b, q6F_arc2_038_b] = true := by
  decide +kernel

/-- Endpoint disks: directed `E_x, E_v` below the printed values, and these below `K`. -/
theorem q6Endpoint_check :
    (hiLe (exUB fieldMode q6D 6) (exQ 6) && hiLe (evUB fieldMode q6D 6) (evQ 6) &&
      qlt (exQ 6) (kxQ 6) && qlt (evQ 6) (kvQ 6)) = true := by
  decide +kernel

/-- `alpha_le`: `vAlpha q ≤ Qlow - 3/2·log q - Kx - 5/4·Kv - Kz`, `log q ≤ (logQ 3 (q,1)).2 / 2^64`. -/
theorem q6Alpha_check :
    qle (alphaQ 6) (qsub (qsub (qsub (qsub (qlowQ 6) (qmul (3, 2) ((logQ 3 (6, 1)).2, S)))
      (kxQ 6)) (qmul (5, 4) (kvQ 6))) (kzQ 6)) = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
