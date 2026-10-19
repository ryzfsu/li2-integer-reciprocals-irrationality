/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
/-
Generated certificate data
from v13 `v-reference-data.tex` (sha256 e3983e04...cd9b).  elaborated.
-/

import Li2Lean.V.EnergyCertI.Q2Energy00
import Li2Lean.V.EnergyCertI.Q2Energy01
import Li2Lean.V.EnergyCertI.Q2Energy02
import Li2Lean.V.EnergyCertI.Q2Energy03
import Li2Lean.V.EnergyCertI.Q2Energy04
import Li2Lean.V.EnergyCertI.Q2Energy05
import Li2Lean.V.EnergyCertI.Q2FArc100
import Li2Lean.V.EnergyCertI.Q2FArc101
import Li2Lean.V.EnergyCertI.Q2FArc102
import Li2Lean.V.EnergyCertI.Q2FArc103
import Li2Lean.V.EnergyCertI.Q2FArc104
import Li2Lean.V.EnergyCertI.Q2FArc200
import Li2Lean.V.EnergyCertI.Q2FArc201
import Li2Lean.V.EnergyCertI.Q2FArc202
import Li2Lean.V.EnergyCertI.Q2FArc203
import Li2Lean.V.EnergyCertI.Q2FArc204
import Li2Lean.V.EnergyCertI.Q2FArc205
import Li2Lean.V.EnergyCertI.Q2FArc206
import Li2Lean.V.EnergyCertI.Q2FVhi00
import Li2Lean.V.EnergyCertI.Q2FVhi01
import Li2Lean.V.EnergyCertI.Q2FVhi02
import Li2Lean.V.EnergyCertI.Q2FVhi03
import Li2Lean.V.EnergyCertI.Q2FVhi04
import Li2Lean.V.EnergyCertI.Q2FVhi05
import Li2Lean.V.EnergyCertI.Q2FVhi06
import Li2Lean.V.EnergyCertI.Q2FVhi07
import Li2Lean.V.EnergyCertI.Q2FVhi08
import Li2Lean.V.EnergyCertI.Q2FVhi09
import Li2Lean.V.EnergyCertI.Q2FVhi10
import Li2Lean.V.EnergyCertI.Q2FVhi11
import Li2Lean.V.EnergyCertI.Q2FVlo00
import Li2Lean.V.EnergyCertI.Q2FVlo01
import Li2Lean.V.EnergyCertI.Q2FVlo02
import Li2Lean.V.EnergyCertI.Q2FVlo03
import Li2Lean.V.EnergyCertI.Q2FVlo04
import Li2Lean.V.EnergyCertI.Q2FVlo05
import Li2Lean.V.EnergyCertI.Q2FVlo06
import Li2Lean.V.EnergyCertI.Q2FVlo07
import Li2Lean.V.EnergyCertI.Q2FVlo08
import Li2Lean.V.EnergyCertI.Q2FVlo09
import Li2Lean.V.EnergyCertI.Q2FVlo10
import Li2Lean.V.EnergyCertI.Q2FVlo11
import Li2Lean.V.EnergyCertI.Q2FX00
import Li2Lean.V.EnergyCertI.Q2FX01
import Li2Lean.V.EnergyCertI.Q2FX02
import Li2Lean.V.EnergyCertI.Q2FX03
import Li2Lean.V.EnergyCertI.Q2FX04
import Li2Lean.V.EnergyCertI.Q2FX05
import Li2Lean.V.EnergyCertI.Q2FX06
import Li2Lean.V.EnergyCertI.Q2FX07
import Li2Lean.V.EnergyCertI.Q2FX08
import Li2Lean.V.EnergyCertI.Q2FZneg00
import Li2Lean.V.EnergyCertI.Q2FZneg01
import Li2Lean.V.EnergyCertI.Q2FZneg02
import Li2Lean.V.EnergyCertI.Q2FZneg03
import Li2Lean.V.EnergyCertI.Q2FZneg04
import Li2Lean.V.EnergyCertI.Q2FZneg05
import Li2Lean.V.EnergyCertI.Q2FZneg06
import Li2Lean.V.EnergyCertI.Q2FZneg07
import Li2Lean.V.EnergyCertI.Q2FZpos00

namespace Li2Lean.V.EnergyCertI

open IK

/-- Energy plan (kind, i0, i1, claim · 2^64); entry ↦ theorem `q2E_<kind>_<i0>_<i1>`. -/
def q2EnergyPlan : List (EKind × Nat × Nat × Int) := [
  (.selfX, 0, 42, -28527138597217836334),
  (.selfV, 0, 49, -41314003762645412436),
  (.selfZ, 0, 32, -3053873798366259184),
  (.selfZ, 32, 63, 54856343251943363),
  (.crossVZ, 0, 23, 4875408042235156026),
  (.crossVZ, 23, 46, 18188865845369762708),
  (.crossVZ, 46, 49, -17281626094082648333),
  (.intPoi, 0, 4, -99260137523217155),
  (.intPoi, 4, 8, -108003985377251161),
  (.intPoi, 8, 12, -70343310481803459),
  (.intPoi, 12, 16, -24164714825104229),
  (.intPoi, 16, 20, 21154030375864264),
  (.intPoi, 20, 24, 61397791663798973),
  (.intPoi, 24, 28, 94511624234271177),
  (.intPoi, 28, 32, 119524584104139352),
  (.intPoi, 32, 36, 136085420454546499),
  (.intPoi, 36, 40, 144260166338550179),
  (.intPoi, 40, 44, 144456781837304433),
  (.intPoi, 44, 48, 137411948201818742),
  (.intPoi, 48, 52, 124225636368392604),
  (.intPoi, 52, 56, 106391447325188056),
  (.intPoi, 56, 60, 85794461709259987),
  (.intPoi, 60, 64, 64644766034291439),
  (.intPoi, 64, 68, 45286049657651683),
  (.intPoi, 68, 72, 29898920820970096),
  (.intPoi, 72, 75, 13022429640804483),
  (.pp, 0, 10, -261130279562642897),
  (.pp, 10, 21, -456957052653278306),
  (.pp, 21, 33, -536604127279699257),
  (.pp, 33, 46, -531037533113726980),
  (.pp, 46, 61, -474296244051638753),
  (.pp, 61, 79, -379600629812918517),
  (.pp, 79, 105, -1040600529796196978),
  (.pp, 105, 149, -1341488163676611499),
  (.dq, 0, 1, -19544023429413489940)]

theorem q2EnergyClaims_gt_qlow : claimsGt q2EnergyPlan (qlowQ 2) = true := by decide +kernel

theorem q2EnergyPlan_tiles : energyPlanTiles q2D q2EnergyPlan = true := by decide +kernel

theorem q2F_x_chain :
    chainOK (1, 250) (1, 1) [q2F_x_000_b, q2F_x_001_b, q2F_x_002_b, q2F_x_003_b,
      q2F_x_004_b, q2F_x_005_b, q2F_x_006_b, q2F_x_007_b,
      q2F_x_008_b, q2F_x_009_b, q2F_x_010_b, q2F_x_011_b,
      q2F_x_012_b, q2F_x_013_b, q2F_x_014_b, q2F_x_015_b,
      q2F_x_016_b, q2F_x_017_b, q2F_x_018_b, q2F_x_019_b,
      q2F_x_020_b, q2F_x_021_b, q2F_x_022_b, q2F_x_023_b,
      q2F_x_024_b, q2F_x_025_b, q2F_x_026_b, q2F_x_027_b,
      q2F_x_028_b, q2F_x_029_b, q2F_x_030_b, q2F_x_031_b,
      q2F_x_032_b, q2F_x_033_b, q2F_x_034_b, q2F_x_035_b,
      q2F_x_036_b, q2F_x_037_b, q2F_x_038_b, q2F_x_039_b,
      q2F_x_040_b, q2F_x_041_b, q2F_x_042_b, q2F_x_043_b,
      q2F_x_044_b, q2F_x_045_b, q2F_x_046_b, q2F_x_047_b,
      q2F_x_048_b] = true := by
  decide +kernel

theorem q2F_vlo_chain :
    chainOK (1, 250) (3, 5) [q2F_vlo_000_b, q2F_vlo_001_b, q2F_vlo_002_b, q2F_vlo_003_b,
      q2F_vlo_004_b, q2F_vlo_005_b, q2F_vlo_006_b, q2F_vlo_007_b,
      q2F_vlo_008_b, q2F_vlo_009_b, q2F_vlo_010_b, q2F_vlo_011_b,
      q2F_vlo_012_b, q2F_vlo_013_b, q2F_vlo_014_b, q2F_vlo_015_b,
      q2F_vlo_016_b, q2F_vlo_017_b, q2F_vlo_018_b, q2F_vlo_019_b,
      q2F_vlo_020_b, q2F_vlo_021_b, q2F_vlo_022_b, q2F_vlo_023_b,
      q2F_vlo_024_b, q2F_vlo_025_b, q2F_vlo_026_b, q2F_vlo_027_b,
      q2F_vlo_028_b, q2F_vlo_029_b, q2F_vlo_030_b, q2F_vlo_031_b,
      q2F_vlo_032_b, q2F_vlo_033_b, q2F_vlo_034_b, q2F_vlo_035_b,
      q2F_vlo_036_b, q2F_vlo_037_b, q2F_vlo_038_b, q2F_vlo_039_b,
      q2F_vlo_040_b, q2F_vlo_041_b, q2F_vlo_042_b, q2F_vlo_043_b,
      q2F_vlo_044_b, q2F_vlo_045_b, q2F_vlo_046_b, q2F_vlo_047_b,
      q2F_vlo_048_b, q2F_vlo_049_b, q2F_vlo_050_b, q2F_vlo_051_b,
      q2F_vlo_052_b, q2F_vlo_053_b, q2F_vlo_054_b, q2F_vlo_055_b,
      q2F_vlo_056_b, q2F_vlo_057_b, q2F_vlo_058_b, q2F_vlo_059_b,
      q2F_vlo_060_b, q2F_vlo_061_b, q2F_vlo_062_b, q2F_vlo_063_b,
      q2F_vlo_064_b, q2F_vlo_065_b, q2F_vlo_066_b, q2F_vlo_067_b,
      q2F_vlo_068_b, q2F_vlo_069_b] = true := by
  decide +kernel

theorem q2F_vhi_chain :
    chainOK (3, 5) (1, 1) [q2F_vhi_000_b, q2F_vhi_001_b, q2F_vhi_002_b, q2F_vhi_003_b,
      q2F_vhi_004_b, q2F_vhi_005_b, q2F_vhi_006_b, q2F_vhi_007_b,
      q2F_vhi_008_b, q2F_vhi_009_b, q2F_vhi_010_b, q2F_vhi_011_b,
      q2F_vhi_012_b, q2F_vhi_013_b, q2F_vhi_014_b, q2F_vhi_015_b,
      q2F_vhi_016_b, q2F_vhi_017_b, q2F_vhi_018_b, q2F_vhi_019_b,
      q2F_vhi_020_b, q2F_vhi_021_b, q2F_vhi_022_b, q2F_vhi_023_b,
      q2F_vhi_024_b, q2F_vhi_025_b, q2F_vhi_026_b, q2F_vhi_027_b,
      q2F_vhi_028_b, q2F_vhi_029_b, q2F_vhi_030_b, q2F_vhi_031_b,
      q2F_vhi_032_b, q2F_vhi_033_b, q2F_vhi_034_b, q2F_vhi_035_b,
      q2F_vhi_036_b, q2F_vhi_037_b, q2F_vhi_038_b, q2F_vhi_039_b,
      q2F_vhi_040_b, q2F_vhi_041_b, q2F_vhi_042_b, q2F_vhi_043_b,
      q2F_vhi_044_b, q2F_vhi_045_b, q2F_vhi_046_b, q2F_vhi_047_b,
      q2F_vhi_048_b, q2F_vhi_049_b, q2F_vhi_050_b, q2F_vhi_051_b,
      q2F_vhi_052_b, q2F_vhi_053_b, q2F_vhi_054_b, q2F_vhi_055_b,
      q2F_vhi_056_b, q2F_vhi_057_b, q2F_vhi_058_b, q2F_vhi_059_b,
      q2F_vhi_060_b, q2F_vhi_061_b, q2F_vhi_062_b, q2F_vhi_063_b,
      q2F_vhi_064_b, q2F_vhi_065_b, q2F_vhi_066_b, q2F_vhi_067_b,
      q2F_vhi_068_b, q2F_vhi_069_b, q2F_vhi_070_b] = true := by
  decide +kernel

theorem q2F_zneg_chain :
    chainOK (-2, 1) (-3, 5) [q2F_zneg_000_b, q2F_zneg_001_b, q2F_zneg_002_b, q2F_zneg_003_b,
      q2F_zneg_004_b, q2F_zneg_005_b, q2F_zneg_006_b, q2F_zneg_007_b,
      q2F_zneg_008_b, q2F_zneg_009_b, q2F_zneg_010_b, q2F_zneg_011_b,
      q2F_zneg_012_b, q2F_zneg_013_b, q2F_zneg_014_b, q2F_zneg_015_b,
      q2F_zneg_016_b, q2F_zneg_017_b, q2F_zneg_018_b, q2F_zneg_019_b,
      q2F_zneg_020_b, q2F_zneg_021_b, q2F_zneg_022_b, q2F_zneg_023_b,
      q2F_zneg_024_b, q2F_zneg_025_b, q2F_zneg_026_b, q2F_zneg_027_b,
      q2F_zneg_028_b, q2F_zneg_029_b, q2F_zneg_030_b, q2F_zneg_031_b,
      q2F_zneg_032_b, q2F_zneg_033_b, q2F_zneg_034_b, q2F_zneg_035_b,
      q2F_zneg_036_b, q2F_zneg_037_b, q2F_zneg_038_b, q2F_zneg_039_b,
      q2F_zneg_040_b, q2F_zneg_041_b, q2F_zneg_042_b, q2F_zneg_043_b,
      q2F_zneg_044_b, q2F_zneg_045_b, q2F_zneg_046_b, q2F_zneg_047_b,
      q2F_zneg_048_b, q2F_zneg_049_b, q2F_zneg_050_b, q2F_zneg_051_b,
      q2F_zneg_052_b] = true := by
  decide +kernel

theorem q2F_zpos_chain :
    chainOK (3, 5) (1, 1) [q2F_zpos_000_b] = true := by
  decide +kernel

theorem q2F_arc1_chain :
    chainOK (0, 1) (1, 1) [q2F_arc1_000_b, q2F_arc1_001_b, q2F_arc1_002_b, q2F_arc1_003_b,
      q2F_arc1_004_b, q2F_arc1_005_b, q2F_arc1_006_b, q2F_arc1_007_b,
      q2F_arc1_008_b, q2F_arc1_009_b, q2F_arc1_010_b, q2F_arc1_011_b,
      q2F_arc1_012_b, q2F_arc1_013_b, q2F_arc1_014_b, q2F_arc1_015_b,
      q2F_arc1_016_b, q2F_arc1_017_b, q2F_arc1_018_b, q2F_arc1_019_b,
      q2F_arc1_020_b, q2F_arc1_021_b, q2F_arc1_022_b, q2F_arc1_023_b,
      q2F_arc1_024_b, q2F_arc1_025_b, q2F_arc1_026_b, q2F_arc1_027_b,
      q2F_arc1_028_b, q2F_arc1_029_b, q2F_arc1_030_b] = true := by
  decide +kernel

theorem q2F_arc2_chain :
    chainOK (0, 1) (1, 1) [q2F_arc2_000_b, q2F_arc2_001_b, q2F_arc2_002_b, q2F_arc2_003_b,
      q2F_arc2_004_b, q2F_arc2_005_b, q2F_arc2_006_b, q2F_arc2_007_b,
      q2F_arc2_008_b, q2F_arc2_009_b, q2F_arc2_010_b, q2F_arc2_011_b,
      q2F_arc2_012_b, q2F_arc2_013_b, q2F_arc2_014_b, q2F_arc2_015_b,
      q2F_arc2_016_b, q2F_arc2_017_b, q2F_arc2_018_b, q2F_arc2_019_b,
      q2F_arc2_020_b, q2F_arc2_021_b, q2F_arc2_022_b, q2F_arc2_023_b,
      q2F_arc2_024_b, q2F_arc2_025_b, q2F_arc2_026_b, q2F_arc2_027_b,
      q2F_arc2_028_b, q2F_arc2_029_b, q2F_arc2_030_b, q2F_arc2_031_b,
      q2F_arc2_032_b, q2F_arc2_033_b, q2F_arc2_034_b, q2F_arc2_035_b,
      q2F_arc2_036_b, q2F_arc2_037_b, q2F_arc2_038_b, q2F_arc2_039_b,
      q2F_arc2_040_b, q2F_arc2_041_b, q2F_arc2_042_b] = true := by
  decide +kernel

/-- Endpoint disks: directed `E_x, E_v` below the printed values, and these below `K`. -/
theorem q2Endpoint_check :
    (hiLe (exUB fieldMode q2D 2) (exQ 2) && hiLe (evUB fieldMode q2D 2) (evQ 2) &&
      qlt (exQ 2) (kxQ 2) && qlt (evQ 2) (kvQ 2)) = true := by
  decide +kernel

/-- `alpha_le`: `vAlpha q ≤ Qlow - 3/2·log q - Kx - 5/4·Kv - Kz`, `log q ≤ (logQ 3 (q,1)).2 / 2^64`. -/
theorem q2Alpha_check :
    qle (alphaQ 2) (qsub (qsub (qsub (qsub (qlowQ 2) (qmul (3, 2) ((logQ 3 (2, 1)).2, S)))
      (kxQ 2)) (qmul (5, 4) (kvQ 2))) (kzQ 2)) = true := by
  decide +kernel

end Li2Lean.V.EnergyCertI
