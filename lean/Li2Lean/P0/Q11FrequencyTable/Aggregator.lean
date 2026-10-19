/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.Q11FrequencyTable.Rows000
import Li2Lean.P0.Q11FrequencyTable.Rows001
import Li2Lean.P0.Q11FrequencyTable.Rows002
import Li2Lean.P0.Q11FrequencyTable.Rows003
import Li2Lean.P0.Q11FrequencyTable.Rows004
import Li2Lean.P0.Q11FrequencyTable.Rows005
import Li2Lean.P0.Q11FrequencyTable.Rows006
import Li2Lean.P0.Q11FrequencyTable.Rows007
import Li2Lean.P0.Q11FrequencyTable.Rows008
import Li2Lean.P0.Q11FrequencyTable.Rows009
import Li2Lean.P0.Q11FrequencyTable.Rows010
import Li2Lean.P0.Q11FrequencyTable.Rows011
import Li2Lean.P0.Q11FrequencyTable.Rows012
import Li2Lean.P0.Q11FrequencyTable.Rows013
import Li2Lean.P0.Q11FrequencyTable.Rows014
import Li2Lean.P0.Q11FrequencyTable.Rows015
import Li2Lean.P0.Q11FrequencyTable.Rows016
import Li2Lean.P0.Q11FrequencyTable.Rows017
import Li2Lean.P0.Q11FrequencyTable.Rows018
import Li2Lean.P0.Q11FrequencyTable.Rows019
import Li2Lean.P0.Q11FrequencyTable.Rows020
import Li2Lean.P0.Q11FrequencyTable.Rows021
import Li2Lean.P0.Q11FrequencyTable.Rows022
import Li2Lean.P0.Q11FrequencyTable.Rows023
import Li2Lean.P0.Q11FrequencyTable.Rows024
import Li2Lean.P0.Q11FrequencyTable.Rows025
import Li2Lean.P0.Q11FrequencyTable.Rows026
import Li2Lean.P0.Q11FrequencyTable.Rows027
import Li2Lean.P0.Q11FrequencyTable.Rows028
import Li2Lean.P0.Q11FrequencyTable.Rows029
import Li2Lean.P0.Q11FrequencyTable.Rows030
import Li2Lean.P0.Q11FrequencyTable.Rows031
import Li2Lean.P0.Q11FrequencyTable.Rows032
import Li2Lean.P0.Q11FrequencyTable.Rows033
import Li2Lean.P0.Q11FrequencyTable.Rows034
import Li2Lean.P0.Q11FrequencyTable.Rows035
import Li2Lean.P0.Q11FrequencyTable.Rows036
import Li2Lean.P0.Q11FrequencyTable.Rows037
import Li2Lean.P0.Q11FrequencyTable.Rows038
import Li2Lean.P0.Q11FrequencyTable.Rows039
import Li2Lean.P0.Q11FrequencyTable.Rows040
import Li2Lean.P0.Q11FrequencyTable.Rows041
import Li2Lean.P0.Q11FrequencyTable.Rows042
import Li2Lean.P0.Q11FrequencyTable.Rows043
import Li2Lean.P0.Q11FrequencyTable.Rows044
import Li2Lean.P0.Q11FrequencyTable.Rows045
import Li2Lean.P0.Q11FrequencyTable.Rows046
import Li2Lean.P0.Q11FrequencyTable.Rows047
import Li2Lean.P0.Q11FrequencyTable.Rows048
import Li2Lean.P0.Q11FrequencyTable.Rows049
import Li2Lean.P0.Q11FrequencyTable.Rows050
import Li2Lean.P0.Q11FrequencyTable.Rows051
import Li2Lean.P0.Q11FrequencyTable.Rows052
import Li2Lean.P0.Q11FrequencyTable.Rows053
import Li2Lean.P0.Q11FrequencyTable.Rows054
import Li2Lean.P0.Q11FrequencyTable.Rows055
import Li2Lean.P0.Q11FrequencyTable.Rows056
import Li2Lean.P0.Q11FrequencyTable.Rows057
import Li2Lean.P0.Q11FrequencyTable.Rows058
import Li2Lean.P0.Q11FrequencyTable.Rows059
import Li2Lean.P0.Q11FrequencyTable.Rows060
import Li2Lean.P0.Q11FrequencyTable.Rows061
import Li2Lean.P0.Q11FrequencyTable.Rows062
import Li2Lean.P0.Q11FrequencyTable.Rows063

/-! The q = 11 frequency certificate table from v13 `p0-analytic.tex:767-800`
and `certificate-algorithm.tex:29-42`.  The finite arithmetic layer reuses
`P0/CA/Receipt/Checks.lean` (`chainCheck`, `penaltyMass`) and
`Kit/ReceiptChain.lean` (`ExactChain`); it does not assert the analytic
cellwise lower bound, which is a separate producer obligation. -/
namespace Li2Lean.P0.Q11Data

open Li2Lean.F_L8
open Li2Lean.P0.CA.Receipt

def q11FrequencyRows : List ReceiptCell :=
  q11FrequencyRowsRows000 ++ q11FrequencyRowsRows001 ++ q11FrequencyRowsRows002 ++ q11FrequencyRowsRows003 ++ q11FrequencyRowsRows004 ++ q11FrequencyRowsRows005 ++ q11FrequencyRowsRows006 ++ q11FrequencyRowsRows007 ++ q11FrequencyRowsRows008 ++ q11FrequencyRowsRows009 ++ q11FrequencyRowsRows010 ++ q11FrequencyRowsRows011 ++ q11FrequencyRowsRows012 ++ q11FrequencyRowsRows013 ++ q11FrequencyRowsRows014 ++ q11FrequencyRowsRows015 ++ q11FrequencyRowsRows016 ++ q11FrequencyRowsRows017 ++ q11FrequencyRowsRows018 ++ q11FrequencyRowsRows019 ++ q11FrequencyRowsRows020 ++ q11FrequencyRowsRows021 ++ q11FrequencyRowsRows022 ++ q11FrequencyRowsRows023 ++ q11FrequencyRowsRows024 ++ q11FrequencyRowsRows025 ++ q11FrequencyRowsRows026 ++ q11FrequencyRowsRows027 ++ q11FrequencyRowsRows028 ++ q11FrequencyRowsRows029 ++ q11FrequencyRowsRows030 ++ q11FrequencyRowsRows031 ++ q11FrequencyRowsRows032 ++ q11FrequencyRowsRows033 ++ q11FrequencyRowsRows034 ++ q11FrequencyRowsRows035 ++ q11FrequencyRowsRows036 ++ q11FrequencyRowsRows037 ++ q11FrequencyRowsRows038 ++ q11FrequencyRowsRows039 ++ q11FrequencyRowsRows040 ++ q11FrequencyRowsRows041 ++ q11FrequencyRowsRows042 ++ q11FrequencyRowsRows043 ++ q11FrequencyRowsRows044 ++ q11FrequencyRowsRows045 ++ q11FrequencyRowsRows046 ++ q11FrequencyRowsRows047 ++ q11FrequencyRowsRows048 ++ q11FrequencyRowsRows049 ++ q11FrequencyRowsRows050 ++ q11FrequencyRowsRows051 ++ q11FrequencyRowsRows052 ++ q11FrequencyRowsRows053 ++ q11FrequencyRowsRows054 ++ q11FrequencyRowsRows055 ++ q11FrequencyRowsRows056 ++ q11FrequencyRowsRows057 ++ q11FrequencyRowsRows058 ++ q11FrequencyRowsRows059 ++ q11FrequencyRowsRows060 ++ q11FrequencyRowsRows061 ++ q11FrequencyRowsRows062 ++ q11FrequencyRowsRows063

theorem q11FrequencyRows_length : q11FrequencyRows.length = 16384 := by
  simp only [q11FrequencyRows, List.length_append, q11FrequencyRowsRows000_length, q11FrequencyRowsRows001_length, q11FrequencyRowsRows002_length, q11FrequencyRowsRows003_length, q11FrequencyRowsRows004_length, q11FrequencyRowsRows005_length, q11FrequencyRowsRows006_length, q11FrequencyRowsRows007_length, q11FrequencyRowsRows008_length, q11FrequencyRowsRows009_length, q11FrequencyRowsRows010_length, q11FrequencyRowsRows011_length, q11FrequencyRowsRows012_length, q11FrequencyRowsRows013_length, q11FrequencyRowsRows014_length, q11FrequencyRowsRows015_length, q11FrequencyRowsRows016_length, q11FrequencyRowsRows017_length, q11FrequencyRowsRows018_length, q11FrequencyRowsRows019_length, q11FrequencyRowsRows020_length, q11FrequencyRowsRows021_length, q11FrequencyRowsRows022_length, q11FrequencyRowsRows023_length, q11FrequencyRowsRows024_length, q11FrequencyRowsRows025_length, q11FrequencyRowsRows026_length, q11FrequencyRowsRows027_length, q11FrequencyRowsRows028_length, q11FrequencyRowsRows029_length, q11FrequencyRowsRows030_length, q11FrequencyRowsRows031_length, q11FrequencyRowsRows032_length, q11FrequencyRowsRows033_length, q11FrequencyRowsRows034_length, q11FrequencyRowsRows035_length, q11FrequencyRowsRows036_length, q11FrequencyRowsRows037_length, q11FrequencyRowsRows038_length, q11FrequencyRowsRows039_length, q11FrequencyRowsRows040_length, q11FrequencyRowsRows041_length, q11FrequencyRowsRows042_length, q11FrequencyRowsRows043_length, q11FrequencyRowsRows044_length, q11FrequencyRowsRows045_length, q11FrequencyRowsRows046_length, q11FrequencyRowsRows047_length, q11FrequencyRowsRows048_length, q11FrequencyRowsRows049_length, q11FrequencyRowsRows050_length, q11FrequencyRowsRows051_length, q11FrequencyRowsRows052_length, q11FrequencyRowsRows053_length, q11FrequencyRowsRows054_length, q11FrequencyRowsRows055_length, q11FrequencyRowsRows056_length, q11FrequencyRowsRows057_length, q11FrequencyRowsRows058_length, q11FrequencyRowsRows059_length, q11FrequencyRowsRows060_length, q11FrequencyRowsRows061_length, q11FrequencyRowsRows062_length, q11FrequencyRowsRows063_length]

theorem q11FrequencyRows_chain :
    ExactChain q11FrequencyRows (1 / 2 : ℚ) (81 / 10 : ℚ) := by
  unfold q11FrequencyRows
  exact (exactChain_append (List.ne_nil_of_length_pos (by rw [q11FrequencyRowsRows063_length]; norm_num)) (exactChain_append (List.ne_nil_of_length_pos (by rw [q11FrequencyRowsRows062_length]; norm_num)) (exactChain_append (List.ne_nil_of_length_pos (by rw [q11FrequencyRowsRows061_length]; norm_num)) (exactChain_append (List.ne_nil_of_length_pos (by rw [q11FrequencyRowsRows060_length]; norm_num)) (exactChain_append (List.ne_nil_of_length_pos (by rw [q11FrequencyRowsRows059_length]; norm_num)) (exactChain_append (List.ne_nil_of_length_pos (by rw [q11FrequencyRowsRows058_length]; norm_num)) (exactChain_append (List.ne_nil_of_length_pos (by rw [q11FrequencyRowsRows057_length]; norm_num)) (exactChain_append (List.ne_nil_of_length_pos (by rw [q11FrequencyRowsRows056_length]; norm_num)) (exactChain_append (List.ne_nil_of_length_pos (by rw [q11FrequencyRowsRows055_length]; norm_num)) (exactChain_append (List.ne_nil_of_length_pos (by rw [q11FrequencyRowsRows054_length]; norm_num)) (exactChain_append (List.ne_nil_of_length_pos (by rw [q11FrequencyRowsRows053_length]; norm_num)) (exactChain_append (List.ne_nil_of_length_pos (by rw [q11FrequencyRowsRows052_length]; norm_num)) (exactChain_append (List.ne_nil_of_length_pos (by rw [q11FrequencyRowsRows051_length]; norm_num)) (exactChain_append (List.ne_nil_of_length_pos (by rw [q11FrequencyRowsRows050_length]; norm_num)) (exactChain_append (List.ne_nil_of_length_pos (by rw [q11FrequencyRowsRows049_length]; norm_num)) (exactChain_append (List.ne_nil_of_length_pos (by rw [q11FrequencyRowsRows048_length]; norm_num)) (exactChain_append (List.ne_nil_of_length_pos (by rw [q11FrequencyRowsRows047_length]; norm_num)) (exactChain_append (List.ne_nil_of_length_pos (by rw [q11FrequencyRowsRows046_length]; norm_num)) (exactChain_append (List.ne_nil_of_length_pos (by rw [q11FrequencyRowsRows045_length]; norm_num)) (exactChain_append (List.ne_nil_of_length_pos (by rw [q11FrequencyRowsRows044_length]; norm_num)) (exactChain_append (List.ne_nil_of_length_pos (by rw [q11FrequencyRowsRows043_length]; norm_num)) (exactChain_append (List.ne_nil_of_length_pos (by rw [q11FrequencyRowsRows042_length]; norm_num)) (exactChain_append (List.ne_nil_of_length_pos (by rw [q11FrequencyRowsRows041_length]; norm_num)) (exactChain_append (List.ne_nil_of_length_pos (by rw [q11FrequencyRowsRows040_length]; norm_num)) (exactChain_append (List.ne_nil_of_length_pos (by rw [q11FrequencyRowsRows039_length]; norm_num)) (exactChain_append (List.ne_nil_of_length_pos (by rw [q11FrequencyRowsRows038_length]; norm_num)) (exactChain_append (List.ne_nil_of_length_pos (by rw [q11FrequencyRowsRows037_length]; norm_num)) (exactChain_append (List.ne_nil_of_length_pos (by rw [q11FrequencyRowsRows036_length]; norm_num)) (exactChain_append (List.ne_nil_of_length_pos (by rw [q11FrequencyRowsRows035_length]; norm_num)) (exactChain_append (List.ne_nil_of_length_pos (by rw [q11FrequencyRowsRows034_length]; norm_num)) (exactChain_append (List.ne_nil_of_length_pos (by rw [q11FrequencyRowsRows033_length]; norm_num)) (exactChain_append (List.ne_nil_of_length_pos (by rw [q11FrequencyRowsRows032_length]; norm_num)) (exactChain_append (List.ne_nil_of_length_pos (by rw [q11FrequencyRowsRows031_length]; norm_num)) (exactChain_append (List.ne_nil_of_length_pos (by rw [q11FrequencyRowsRows030_length]; norm_num)) (exactChain_append (List.ne_nil_of_length_pos (by rw [q11FrequencyRowsRows029_length]; norm_num)) (exactChain_append (List.ne_nil_of_length_pos (by rw [q11FrequencyRowsRows028_length]; norm_num)) (exactChain_append (List.ne_nil_of_length_pos (by rw [q11FrequencyRowsRows027_length]; norm_num)) (exactChain_append (List.ne_nil_of_length_pos (by rw [q11FrequencyRowsRows026_length]; norm_num)) (exactChain_append (List.ne_nil_of_length_pos (by rw [q11FrequencyRowsRows025_length]; norm_num)) (exactChain_append (List.ne_nil_of_length_pos (by rw [q11FrequencyRowsRows024_length]; norm_num)) (exactChain_append (List.ne_nil_of_length_pos (by rw [q11FrequencyRowsRows023_length]; norm_num)) (exactChain_append (List.ne_nil_of_length_pos (by rw [q11FrequencyRowsRows022_length]; norm_num)) (exactChain_append (List.ne_nil_of_length_pos (by rw [q11FrequencyRowsRows021_length]; norm_num)) (exactChain_append (List.ne_nil_of_length_pos (by rw [q11FrequencyRowsRows020_length]; norm_num)) (exactChain_append (List.ne_nil_of_length_pos (by rw [q11FrequencyRowsRows019_length]; norm_num)) (exactChain_append (List.ne_nil_of_length_pos (by rw [q11FrequencyRowsRows018_length]; norm_num)) (exactChain_append (List.ne_nil_of_length_pos (by rw [q11FrequencyRowsRows017_length]; norm_num)) (exactChain_append (List.ne_nil_of_length_pos (by rw [q11FrequencyRowsRows016_length]; norm_num)) (exactChain_append (List.ne_nil_of_length_pos (by rw [q11FrequencyRowsRows015_length]; norm_num)) (exactChain_append (List.ne_nil_of_length_pos (by rw [q11FrequencyRowsRows014_length]; norm_num)) (exactChain_append (List.ne_nil_of_length_pos (by rw [q11FrequencyRowsRows013_length]; norm_num)) (exactChain_append (List.ne_nil_of_length_pos (by rw [q11FrequencyRowsRows012_length]; norm_num)) (exactChain_append (List.ne_nil_of_length_pos (by rw [q11FrequencyRowsRows011_length]; norm_num)) (exactChain_append (List.ne_nil_of_length_pos (by rw [q11FrequencyRowsRows010_length]; norm_num)) (exactChain_append (List.ne_nil_of_length_pos (by rw [q11FrequencyRowsRows009_length]; norm_num)) (exactChain_append (List.ne_nil_of_length_pos (by rw [q11FrequencyRowsRows008_length]; norm_num)) (exactChain_append (List.ne_nil_of_length_pos (by rw [q11FrequencyRowsRows007_length]; norm_num)) (exactChain_append (List.ne_nil_of_length_pos (by rw [q11FrequencyRowsRows006_length]; norm_num)) (exactChain_append (List.ne_nil_of_length_pos (by rw [q11FrequencyRowsRows005_length]; norm_num)) (exactChain_append (List.ne_nil_of_length_pos (by rw [q11FrequencyRowsRows004_length]; norm_num)) (exactChain_append (List.ne_nil_of_length_pos (by rw [q11FrequencyRowsRows003_length]; norm_num)) (exactChain_append (List.ne_nil_of_length_pos (by rw [q11FrequencyRowsRows002_length]; norm_num)) (exactChain_append (List.ne_nil_of_length_pos (by rw [q11FrequencyRowsRows001_length]; norm_num)) (chainCheck_sound q11FrequencyRowsRows000_chain) (chainCheck_sound q11FrequencyRowsRows001_chain)) (chainCheck_sound q11FrequencyRowsRows002_chain)) (chainCheck_sound q11FrequencyRowsRows003_chain)) (chainCheck_sound q11FrequencyRowsRows004_chain)) (chainCheck_sound q11FrequencyRowsRows005_chain)) (chainCheck_sound q11FrequencyRowsRows006_chain)) (chainCheck_sound q11FrequencyRowsRows007_chain)) (chainCheck_sound q11FrequencyRowsRows008_chain)) (chainCheck_sound q11FrequencyRowsRows009_chain)) (chainCheck_sound q11FrequencyRowsRows010_chain)) (chainCheck_sound q11FrequencyRowsRows011_chain)) (chainCheck_sound q11FrequencyRowsRows012_chain)) (chainCheck_sound q11FrequencyRowsRows013_chain)) (chainCheck_sound q11FrequencyRowsRows014_chain)) (chainCheck_sound q11FrequencyRowsRows015_chain)) (chainCheck_sound q11FrequencyRowsRows016_chain)) (chainCheck_sound q11FrequencyRowsRows017_chain)) (chainCheck_sound q11FrequencyRowsRows018_chain)) (chainCheck_sound q11FrequencyRowsRows019_chain)) (chainCheck_sound q11FrequencyRowsRows020_chain)) (chainCheck_sound q11FrequencyRowsRows021_chain)) (chainCheck_sound q11FrequencyRowsRows022_chain)) (chainCheck_sound q11FrequencyRowsRows023_chain)) (chainCheck_sound q11FrequencyRowsRows024_chain)) (chainCheck_sound q11FrequencyRowsRows025_chain)) (chainCheck_sound q11FrequencyRowsRows026_chain)) (chainCheck_sound q11FrequencyRowsRows027_chain)) (chainCheck_sound q11FrequencyRowsRows028_chain)) (chainCheck_sound q11FrequencyRowsRows029_chain)) (chainCheck_sound q11FrequencyRowsRows030_chain)) (chainCheck_sound q11FrequencyRowsRows031_chain)) (chainCheck_sound q11FrequencyRowsRows032_chain)) (chainCheck_sound q11FrequencyRowsRows033_chain)) (chainCheck_sound q11FrequencyRowsRows034_chain)) (chainCheck_sound q11FrequencyRowsRows035_chain)) (chainCheck_sound q11FrequencyRowsRows036_chain)) (chainCheck_sound q11FrequencyRowsRows037_chain)) (chainCheck_sound q11FrequencyRowsRows038_chain)) (chainCheck_sound q11FrequencyRowsRows039_chain)) (chainCheck_sound q11FrequencyRowsRows040_chain)) (chainCheck_sound q11FrequencyRowsRows041_chain)) (chainCheck_sound q11FrequencyRowsRows042_chain)) (chainCheck_sound q11FrequencyRowsRows043_chain)) (chainCheck_sound q11FrequencyRowsRows044_chain)) (chainCheck_sound q11FrequencyRowsRows045_chain)) (chainCheck_sound q11FrequencyRowsRows046_chain)) (chainCheck_sound q11FrequencyRowsRows047_chain)) (chainCheck_sound q11FrequencyRowsRows048_chain)) (chainCheck_sound q11FrequencyRowsRows049_chain)) (chainCheck_sound q11FrequencyRowsRows050_chain)) (chainCheck_sound q11FrequencyRowsRows051_chain)) (chainCheck_sound q11FrequencyRowsRows052_chain)) (chainCheck_sound q11FrequencyRowsRows053_chain)) (chainCheck_sound q11FrequencyRowsRows054_chain)) (chainCheck_sound q11FrequencyRowsRows055_chain)) (chainCheck_sound q11FrequencyRowsRows056_chain)) (chainCheck_sound q11FrequencyRowsRows057_chain)) (chainCheck_sound q11FrequencyRowsRows058_chain)) (chainCheck_sound q11FrequencyRowsRows059_chain)) (chainCheck_sound q11FrequencyRowsRows060_chain)) (chainCheck_sound q11FrequencyRowsRows061_chain)) (chainCheck_sound q11FrequencyRowsRows062_chain)) (chainCheck_sound q11FrequencyRowsRows063_chain))

theorem q11FrequencyRows_penalty :
    penaltyMass (1217 / 200 : ℚ) 0 q11FrequencyRows =
      (437939106871569 / 409600000000000 : ℚ) := by
  rw [q11FrequencyRows, penaltyMass_append, penaltyMass_append, penaltyMass_append, penaltyMass_append, penaltyMass_append, penaltyMass_append, penaltyMass_append, penaltyMass_append, penaltyMass_append, penaltyMass_append, penaltyMass_append, penaltyMass_append, penaltyMass_append, penaltyMass_append, penaltyMass_append, penaltyMass_append, penaltyMass_append, penaltyMass_append, penaltyMass_append, penaltyMass_append, penaltyMass_append, penaltyMass_append, penaltyMass_append, penaltyMass_append, penaltyMass_append, penaltyMass_append, penaltyMass_append, penaltyMass_append, penaltyMass_append, penaltyMass_append, penaltyMass_append, penaltyMass_append, penaltyMass_append, penaltyMass_append, penaltyMass_append, penaltyMass_append, penaltyMass_append, penaltyMass_append, penaltyMass_append, penaltyMass_append, penaltyMass_append, penaltyMass_append, penaltyMass_append, penaltyMass_append, penaltyMass_append, penaltyMass_append, penaltyMass_append, penaltyMass_append, penaltyMass_append, penaltyMass_append, penaltyMass_append, penaltyMass_append, penaltyMass_append, penaltyMass_append, penaltyMass_append, penaltyMass_append, penaltyMass_append, penaltyMass_append, penaltyMass_append, penaltyMass_append, penaltyMass_append, penaltyMass_append, penaltyMass_append]
  rw [q11FrequencyRowsRows000_penalty, q11FrequencyRowsRows001_penalty, q11FrequencyRowsRows002_penalty, q11FrequencyRowsRows003_penalty, q11FrequencyRowsRows004_penalty, q11FrequencyRowsRows005_penalty, q11FrequencyRowsRows006_penalty, q11FrequencyRowsRows007_penalty, q11FrequencyRowsRows008_penalty, q11FrequencyRowsRows009_penalty, q11FrequencyRowsRows010_penalty, q11FrequencyRowsRows011_penalty, q11FrequencyRowsRows012_penalty, q11FrequencyRowsRows013_penalty, q11FrequencyRowsRows014_penalty, q11FrequencyRowsRows015_penalty, q11FrequencyRowsRows016_penalty, q11FrequencyRowsRows017_penalty, q11FrequencyRowsRows018_penalty, q11FrequencyRowsRows019_penalty, q11FrequencyRowsRows020_penalty, q11FrequencyRowsRows021_penalty, q11FrequencyRowsRows022_penalty, q11FrequencyRowsRows023_penalty, q11FrequencyRowsRows024_penalty, q11FrequencyRowsRows025_penalty, q11FrequencyRowsRows026_penalty, q11FrequencyRowsRows027_penalty, q11FrequencyRowsRows028_penalty, q11FrequencyRowsRows029_penalty, q11FrequencyRowsRows030_penalty, q11FrequencyRowsRows031_penalty, q11FrequencyRowsRows032_penalty, q11FrequencyRowsRows033_penalty, q11FrequencyRowsRows034_penalty, q11FrequencyRowsRows035_penalty, q11FrequencyRowsRows036_penalty, q11FrequencyRowsRows037_penalty, q11FrequencyRowsRows038_penalty, q11FrequencyRowsRows039_penalty, q11FrequencyRowsRows040_penalty, q11FrequencyRowsRows041_penalty, q11FrequencyRowsRows042_penalty, q11FrequencyRowsRows043_penalty, q11FrequencyRowsRows044_penalty, q11FrequencyRowsRows045_penalty, q11FrequencyRowsRows046_penalty, q11FrequencyRowsRows047_penalty, q11FrequencyRowsRows048_penalty, q11FrequencyRowsRows049_penalty, q11FrequencyRowsRows050_penalty, q11FrequencyRowsRows051_penalty, q11FrequencyRowsRows052_penalty, q11FrequencyRowsRows053_penalty, q11FrequencyRowsRows054_penalty, q11FrequencyRowsRows055_penalty, q11FrequencyRowsRows056_penalty, q11FrequencyRowsRows057_penalty, q11FrequencyRowsRows058_penalty, q11FrequencyRowsRows059_penalty, q11FrequencyRowsRows060_penalty, q11FrequencyRowsRows061_penalty, q11FrequencyRowsRows062_penalty, q11FrequencyRowsRows063_penalty]
  norm_num

theorem q11FrequencyRows_penalty_le_budget :
    penaltyMass (1217 / 200 : ℚ) 0 q11FrequencyRows ≤
      (1069189 / 1000000 : ℚ) := by
  rw [q11FrequencyRows_penalty]
  norm_num

end Li2Lean.P0.Q11Data
