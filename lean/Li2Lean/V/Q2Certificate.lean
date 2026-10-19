/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Mathlib
import Li2Lean.Kit.IntervalChecker
import Li2Lean.P0.ActualReferencePinnedData

/-!
The q = 2 signed V reference-data interface.

This module is a transcription and decoder for the q = 2 blocks in
`source/chapters/v-reference-data.tex:1-11,12-83`.  It records the printed
integer data and the exact scale conventions.  The decoder is deliberately
separate from the analytic field estimates: these declarations certify shape,
row counts, and accumulation only; they do not claim the paper's numerical
energy bounds.

The q = 2 signed determinant is the negative base `a = -2`.  The positive
`a = 2` Li2(1/2) implementation remains the regression reference.  The
Boolean/checking style follows the frozen `P0/ActualReferencePinnedData`
qBeq/qListBeq pattern; no similar irrationality formalization is used.
-/

namespace Li2Lean.V.Q2Certificate

/-! ## Printed table headers -/

inductive ChainAxis where
  | x
  | y
  | z
  deriving DecidableEq, Repr

structure ChainHeader where
  q : ℕ
  axis : ChainAxis
  entryCount : ℕ
  startUnits : ℤ
  correctionIndex : ℕ
  correctionUnits : ℤ
  deriving DecidableEq, Repr

structure PoissonHeader where
  q : ℕ
  totalRows : ℕ
  prefixRows : ℕ
  deriving DecidableEq, Repr

abbrev ChainEntry := ℤ × ℤ
/- Explicit right association keeps `e.1`, `e.2.1`, and `e.2.2`
   unambiguous under Lean's product notation. -/
abbrev PoissonEntry := ℤ × (ℤ × ℤ)

def q2XHeader : ChainHeader :=
  { q := 2, axis := .x, entryCount := 41, startUnits := 3349365000000,
    correctionIndex := 0, correctionUnits := 0 }

def q2YHeader : ChainHeader :=
  { q := 2, axis := .y, entryCount := 48, startUnits := 480367989919,
    correctionIndex := 1, correctionUnits := 10081 }

def q2ZHeader : ChainHeader :=
  { q := 2, axis := .z, entryCount := 62, startUnits := -100000000000000,
    correctionIndex := 0, correctionUnits := 0 }

def q2PoissonHeader : PoissonHeader :=
  { q := 2, totalRows := 149, prefixRows := 75 }

/-! ## Raw transcription -/

def q2XEntries : List ChainEntry := [
  (1727789, 904764),
  (1905814, 711734),
  (2075677, 286937),
  (4624699, 2447859),
  (2529220, -2005912),
  (2659559, 74649),
  (2778512, 56594),
  (2885565, 43329),
  (2980263, 33330),
  (3062199, 25792),
  (3131021, 19868),
  (19467262, 13206641),
  (3228206, -13157141),
  (3186436, 336),
  (3131021, -423),
  (3062199, -1053),
  (2980263, -1592),
  (2885565, -1972),
  (2778512, -2210),
  (2659559, -2400),
  (2529220, -2556),
  (2388048, -2629),
  (2236651, -2632),
  (2075677, -2616),
  (1905814, -2625),
  (1727789, -2659),
  (1542367, -2693),
  (1350340, -2849),
  (1152529, -3266),
  (949785, -4562),
  (742973, -5487),
  (532979, -24509),
  (320703, 20464),
  (4075, -2499124),
  (11603, 73573),
  (17365, 82752),
  (20484, 76534),
  (20484, 66626),
  (17365, 54610),
  (11604, 21958),
  (4074, 54225),
]

def q2YEntries : List ChainEntry := [
  (742973, 1385843),
  (949785, 680059),
  (1152529, 209735),
  (1350340, 128408),
  (1542367, 75603),
  (1727789, 50189),
  (1905814, 35139),
  (2075677, 26034),
  (2236651, 20335),
  (2388048, 16778),
  (2529220, 14604),
  (2659559, 13425),
  (2778512, 12980),
  (2885565, 13054),
  (2980263, 13531),
  (3062199, 14320),
  (3131021, 15294),
  (16211108, 11164507),
  (3256154, -11054943),
  (3228206, 16310),
  (3186436, 19197),
  (3131021, 24778),
  (3062199, 19543),
  (2980263, 18296),
  (2885565, 16770),
  (2778512, 15360),
  (2659559, 13983),
  (2529220, 12669),
  (2388048, 11386),
  (2236651, 10131),
  (2075677, 8937),
  (1905814, 7774),
  (1727789, 6583),
  (1542367, 5377),
  (1350340, 4050),
  (1152529, 2463),
  (949785, -131),
  (742973, -2258),
  (532979, -25599),
  (320703, 26042),
  (4075, -2927729),
  (11603, 86195),
  (17365, 96969),
  (20484, 89696),
  (20484, 78091),
  (17365, 64014),
  (11604, 25747),
  (4074, 63559),
]

def q2ZEntries : List ChainEntry := [
  (5704, 244590),
  (16245, -24961),
  (24311, -10122),
  (28678, -25136),
  (28677, -30658),
  (24312, -35202),
  (16244, -38047),
  (5704, -33807),
  (448985, 1148248),
  (746170, -11922),
  (1040162, 7481),
  (1329699, -2526),
  (1613542, -4230),
  (1890475, -6119),
  (2159314, -7630),
  (2418905, -9040),
  (2668139, -10408),
  (2905947, -11807),
  (3131312, -13194),
  (3343268, -14608),
  (3540907, -16105),
  (3723384, -17629),
  (3889916, -19173),
  (4039792, -20794),
  (4172368, -22487),
  (4287077, -24221),
  (4383430, -26007),
  (4461010, -27859),
  (4519490, -29766),
  (4558614, -31723),
  (4578219, -33734),
  (4578219, -35765),
  (4558614, -37788),
  (4519490, -39788),
  (4461010, -41748),
  (4383430, -43637),
  (4287077, -45399),
  (4172368, -46965),
  (4039792, -48254),
  (3889916, -49200),
  (3723384, -49730),
  (3540907, -49748),
  (3343268, -49123),
  (3131312, -47768),
  (2905947, -45635),
  (2668139, -42681),
  (2418905, -38860),
  (2159314, -34222),
  (1890475, -28926),
  (1613542, -23184),
  (1329699, -17235),
  (1040162, -11410),
  (746170, -5884),
  (448985, -2342),
  (5704, -5971),
  (16244, 172),
  (24312, 144),
  (28677, 104),
  (28678, 57),
  (24311, 23),
  (16245, -24),
  (5704, 28),
]

def q2PoissonPrefix : List PoissonEntry := [
  (44433733, 38967338, 63870),
  (-1298766, 1432967, 213587),
  (-1344956, 1389706, -12589),
  (-1389706, 1344956, 48627),
  (-1432967, 1298766, 23616),
  (-1474695, 1251185, 24942),
  (-1514843, 1202264, 20256),
  (-1553368, 1152057, 18160),
  (-1590231, 1100615, 15953),
  (-1625391, 1047995, 14237),
  (-1658810, 994252, 12744),
  (-1690453, 939446, 11446),
  (-1720285, 883632, 10308),
  (-1748277, 826873, 9288),
  (-1774394, 769228, 8392),
  (-1798613, 710760, 7582),
  (-1820906, 651531, 6854),
  (-1841248, 591603, 6179),
  (-1859618, 531042, 5554),
  (-1875999, 469913, 4983),
  (-1890369, 408281, 4450),
  (-1902716, 346211, 3961),
  (-1913024, 283770, 3494),
  (-1921285, 221026, 3056),
  (-1927488, 158045, 2636),
  (-1931627, 94895, 2239),
  (-1933698, 31643, 1862),
  (-1933698, -31643, 1497),
  (-1931627, -94895, 1146),
  (-1927488, -158045, 799),
  (-1921285, -221026, 469),
  (-1913024, -283770, 138),
  (-1902716, -346211, -177),
  (-1890369, -408281, -496),
  (-1875999, -469913, -804),
  (-1859618, -531042, -1117),
  (-1841248, -591603, -1425),
  (-1820906, -651531, -1735),
  (-1798613, -710760, -2046),
  (-1774394, -769228, -2354),
  (-1748277, -826873, -2663),
  (-1720285, -883632, -2973),
  (-1690453, -939446, -3290),
  (-1658810, -994252, -3613),
  (-1625391, -1047995, -3941),
  (-1590231, -1100615, -4270),
  (-1553368, -1152057, -4601),
  (-1514843, -1202264, -4933),
  (-1474695, -1251185, -5276),
  (-1432967, -1298766, -5623),
  (-1389706, -1344956, -5977),
  (-1344956, -1389706, -6332),
  (-1298766, -1432967, -6685),
  (-1251185, -1474695, -7038),
  (-1202264, -1514843, -7399),
  (-1152057, -1553368, -7767),
  (-1100615, -1590231, -8140),
  (-1047995, -1625391, -8506),
  (-994252, -1658810, -8866),
  (-939446, -1690453, -9218),
  (-883632, -1720285, -9571),
  (-826873, -1748277, -9924),
  (-769228, -1774394, -10273),
  (-710760, -1798613, -10606),
  (-651531, -1820906, -10923),
  (-591603, -1841248, -11241),
  (-531042, -1859618, -11546),
  (-469913, -1875999, -11823),
  (-408281, -1890369, -12225),
  (-346211, -1902716, -12281),
  (-283770, -1913024, -13037),
  (-221026, -1921285, -12682),
  (-158045, -1927488, -14794),
  (-94895, -1931627, -10897),
  (-31643, -1933698, -46425),
]

/-! ## Exact decoder -/

def scaleLength (e : ChainEntry) : ℤ := 500000 * e.1

def scaleMass (e : ChainEntry) : ℤ := 500000 * e.2

def correctedLength (h : ChainHeader) (position : ℕ) (e : ChainEntry) : ℤ :=
  scaleLength e + if position = h.correctionIndex then h.correctionUnits else 0

structure ChainPoint where
  coordinateUnits : ℤ
  massUnits : ℤ
  deriving DecidableEq, Repr

def decodeChainAux (h : ChainHeader) : ℕ → ℤ → ℤ → List ChainEntry → List ChainPoint
  | _, _, _, [] => []
  | position, length, mass, e :: es =>
      let length' := length + correctedLength h position e
      let mass' := mass + scaleMass e
      { coordinateUnits := length', massUnits := mass' } ::
        decodeChainAux h (position + 1) length' mass' es

def decodeChain (h : ChainHeader) (entries : List ChainEntry) : List ChainPoint :=
  decodeChainAux h 1 h.startUnits 0 entries

def decodeChainLength (h : ChainHeader) (entries : List ChainEntry) : ℕ :=
  (decodeChain h entries).length

def chainPointToRat (p : ChainPoint) : ℚ × ℚ :=
  ((p.coordinateUnits : ℚ) / 50000000000000,
    (p.massUnits : ℚ) / 50000000000000)

def decodeChainRat (h : ChainHeader) (entries : List ChainEntry) : List (ℚ × ℚ) :=
  (decodeChain h entries).map chainPointToRat

structure PoissonPoint where
  xUnits : ℤ
  yUnits : ℤ
  massUnits : ℤ
  deriving DecidableEq, Repr

def decodePoissonAux : ℤ → ℤ → ℤ → List PoissonEntry → List PoissonPoint
  | _, _, _, [] => []
  | x, y, mass, e :: es =>
      let x' := x + 500000 * e.1
      let y' := y + 500000 * e.2.1
      let mass' := mass + 500000 * e.2.2
      { xUnits := x', yUnits := y', massUnits := mass' } ::
        decodePoissonAux x' y' mass' es

def decodePoisson (entries : List PoissonEntry) : List PoissonPoint :=
  decodePoissonAux 0 0 0 entries

def poissonPointToRat (p : PoissonPoint) : ℚ × ℚ × ℚ :=
  ((p.xUnits : ℚ) / 50000000000000,
    (p.yUnits : ℚ) / 50000000000000,
    (p.massUnits : ℚ) / 50000000000000)

def decodePoissonRat (entries : List PoissonEntry) : List (ℚ × ℚ × ℚ) :=
  (decodePoisson entries).map poissonPointToRat

def conjugatePoisson (p : PoissonPoint) : PoissonPoint :=
  { xUnits := p.xUnits, yUnits := -p.yUnits, massUnits := p.massUnits }

def poissonFull (points : List PoissonPoint) : List PoissonPoint :=
  points ++ (points.dropLast.map conjugatePoisson).reverse

/-! ## Generic shape lemmas -/

theorem decodeChainAux_length (h : ChainHeader) (position : ℕ) (length mass : ℤ)
    (entries : List ChainEntry) :
    (decodeChainAux h position length mass entries).length = entries.length := by
  induction entries generalizing position length mass with
  | nil => rfl
  | cons e es ih =>
      simp only [decodeChainAux, List.length_cons]
      rw [ih]

theorem decodeChain_length (h : ChainHeader) (entries : List ChainEntry) :
    (decodeChain h entries).length = entries.length := by
  exact decodeChainAux_length h 1 h.startUnits 0 entries

theorem decodePoissonAux_length (x y mass : ℤ) (entries : List PoissonEntry) :
    (decodePoissonAux x y mass entries).length = entries.length := by
  induction entries generalizing x y mass with
  | nil => rfl
  | cons e es ih =>
      simp only [decodePoissonAux, List.length_cons]
      rw [ih]

theorem decodePoisson_length (entries : List PoissonEntry) :
    (decodePoisson entries).length = entries.length := by
  exact decodePoissonAux_length 0 0 0 entries

theorem poissonFull_length (points : List PoissonPoint) (h : points ≠ []) :
    (poissonFull points).length = 2 * points.length - 1 := by
  rw [poissonFull, List.length_append, List.length_reverse]
  rw [List.length_map, List.length_dropLast]
  have hlen : 0 < points.length := by
    cases points with
    | nil => contradiction
    | cons _ _ => simp
  omega

/-! ## q = 2 source checks -/

theorem q2XEntries_count : q2XEntries.length = q2XHeader.entryCount := by
  rfl

theorem q2YEntries_count : q2YEntries.length = q2YHeader.entryCount := by
  rfl

theorem q2ZEntries_count : q2ZEntries.length = q2ZHeader.entryCount := by
  rfl

theorem q2XDecoded_count : decodeChainLength q2XHeader q2XEntries = 41 := by
  change (decodeChain q2XHeader q2XEntries).length = 41
  rw [decodeChain_length, q2XEntries_count]
  rfl

theorem q2YDecoded_count : decodeChainLength q2YHeader q2YEntries = 48 := by
  change (decodeChain q2YHeader q2YEntries).length = 48
  rw [decodeChain_length, q2YEntries_count]
  rfl

theorem q2ZDecoded_count : decodeChainLength q2ZHeader q2ZEntries = 62 := by
  change (decodeChain q2ZHeader q2ZEntries).length = 62
  rw [decodeChain_length, q2ZEntries_count]
  rfl

theorem q2PoissonPrefix_count : q2PoissonPrefix.length = q2PoissonHeader.prefixRows := by
  rfl

theorem q2PoissonDecoded_count :
    (decodePoisson q2PoissonPrefix).length = q2PoissonHeader.prefixRows := by
  rw [decodePoisson_length, q2PoissonPrefix_count]

theorem q2PoissonFull_count :
    (poissonFull (decodePoisson q2PoissonPrefix)).length = q2PoissonHeader.totalRows := by
  have hne : decodePoisson q2PoissonPrefix ≠ [] := by
    intro h
    have hc := q2PoissonDecoded_count
    rw [h] at hc
    simp [q2PoissonHeader] at hc
  rw [poissonFull_length _ hne]
  rw [q2PoissonDecoded_count]
  simp [q2PoissonHeader]

/-! The headers are the paper's printed scaling metadata, not an analytic
certificate.  This theorem exposes the q = 2 regression data for consumers. -/
theorem q2Header_regression :
    q2XHeader.entryCount = 41 ∧ q2YHeader.entryCount = 48 ∧
      q2ZHeader.entryCount = 62 ∧ q2PoissonHeader.totalRows = 149 := by
  norm_num [q2XHeader, q2YHeader, q2ZHeader, q2PoissonHeader]

/-! The seed row below transcribes the q = 2 entry of the published seed
table (`source/chapters/nonvanishing.tex:179-198`).  The
determinant-to-row equality is supplied by the existing `NegativeTwoSeed`
module when that dependency is integrated; this declaration alone is only a
finite data interface. -/

def q2SeedPrime : ℕ := 11

def q2SeedCoefficients : List ℕ := [4, 2, 7, 3, 9]

theorem q2SeedPrime_prime : Nat.Prime q2SeedPrime := by
  norm_num [q2SeedPrime]

theorem q2SeedPrime_gt_seven : 7 < q2SeedPrime := by
  norm_num [q2SeedPrime]

theorem q2SeedCoefficients_length : q2SeedCoefficients.length = 5 := rfl

theorem q2SeedConstantCoefficient : q2SeedCoefficients.head? = some 4 := rfl

theorem q2SeedConstant_is_pUnit : Nat.Coprime q2SeedPrime 4 := by
  norm_num [q2SeedPrime]

def q2SeedCoefficientsRat : List ℚ := [4, 2, 7, 3, 9]

theorem q2SeedCoefficients_qcheck :
    Li2Lean.P0.ActualReferencePinnedData.qListBeq
      (q2SeedCoefficients.map (fun n => (n : ℚ))) q2SeedCoefficientsRat = true := by
  decide +kernel

theorem q2SeedCoefficients_qcheck_eq :
    q2SeedCoefficients.map (fun n => (n : ℚ)) = q2SeedCoefficientsRat := by
  exact Li2Lean.P0.ActualReferencePinnedData.qListBeq_eq q2SeedCoefficients_qcheck

end Li2Lean.V.Q2Certificate
