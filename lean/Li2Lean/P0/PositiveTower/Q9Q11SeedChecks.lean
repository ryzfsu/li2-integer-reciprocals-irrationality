/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/

import Mathlib.Data.ZMod.Basic

set_option maxRecDepth 100000

/-!
# Integer seed checks for the q = 9, 10, 11 P0 tower rows

This module is the finite, kernel-checkable part of the q-specific tower
port. It evaluates the printed numerator/denominator tables in `Int` and
`Nat`: no `Rat`, `gcd`, logarithm, or `native_decide` occurs here. The
analytic/Frobenius fields are supplied by named row certificates when
assembling
`P0ActualTowerProducer`.

The auxiliary primes are the v13 choices `41`, `59`, and `197`, and the
printed seed residues are `2`, `26`, and `174` respectively.
-/

namespace Li2Lean.P0.PositiveTower

/-! The q-specific fixed-point tables are kept local so this certificate
module does not import the full `Mathlib` umbrella merely to read data. -/

private def num9 : List (List Int) :=
  [[-26, -45, -459, -7263, -32796, -620001, -14880321, -57395619],
    [-485, -459, -567, -6804, -97929, -413181, -7439931, -172186398],
    [-7289, -7263, -6804, -6561, -91125, -1232739, -4957686, -86089797],
    [-49207, -32796, -97929, -91125, -72171, -1141614, -14781933, -57362823],
    [-49, 7, -865, -20531, -61805, -182564, -420635851, -1892864467],
    [-457, -865, 355, -38467, -92275, -3893257, -105155719, -11357156527],
    [-41209, -20531, -38467, 64411, -515183, -17423489, -420430541, -8517530809],
    [-23183, -61805, -92275, -515183, 14009, -10757021, -208927313, -3783565759]]

private def den9 : List (List Nat) :=
  [[1, 2, 1, 2, 1, 2, 5, 2],
    [2, 1, 2, 1, 2, 1, 2, 5],
    [3, 2, 1, 2, 1, 2, 1, 2],
    [2, 1, 2, 1, 2, 1, 2, 1],
    [16, 16, 16, 48, 16, 5, 1200, 560],
    [16, 16, 16, 48, 16, 80, 240, 2800],
    [144, 48, 48, 144, 48, 240, 720, 1680],
    [8, 16, 16, 48, 2, 80, 240, 560]]

private def res9 : List (List Nat) :=
  [[15, 39, 33, 38, 4, 21, 11, 38],
    [24, 33, 24, 2, 10, 17, 26, 39],
    [3, 38, 2, 20, 18, 4, 34, 38],
    [17, 4, 10, 18, 15, 31, 1, 31],
    [20, 3, 10, 19, 4, 10, 0, 3],
    [15, 10, 35, 28, 1, 10, 18, 18],
    [33, 19, 28, 0, 15, 1, 1, 36],
    [8, 4, 1, 15, 14, 28, 35, 2]]

private def inv9 : List (List Nat) :=
  [[28, 6, 31, 21, 6, 3, 32, 18],
    [35, 29, 29, 31, 9, 13, 10, 31],
    [4, 30, 25, 37, 4, 3, 6, 15],
    [13, 38, 13, 33, 7, 22, 32, 11],
    [34, 22, 18, 10, 17, 19, 7, 12],
    [4, 21, 8, 36, 38, 26, 23, 6],
    [5, 25, 26, 39, 25, 15, 22, 26],
    [34, 24, 40, 33, 4, 20, 1, 35]]

private def num10 : List (List Int) :=
  [[-29, -25, -570, -4985, -49990, -1049985, -5599994, -59999995],
    [-599, -570, -350, -9400, -74700, -699800, -6999850, -71999880],
    [-3333, -4985, -9400, -4500, -140000, -1045000, -9330000, -89997500],
    [-149999, -49990, -74700, -140000, -55000, -1950000, -13925000, -119950000],
    [-55, 4, -1081, -4727, -189611, -19912853, -53101643, -398262716],
    [-284, -1081, 889, -17827, -566671, -3317908, -26550281, -955829005],
    [-2107, -4727, -17827, 9937, -531017, -19818313, -17694245, -1194755059],
    [-568943, -189611, -566671, -531017, 1382089, -36981541, -105634453, -3184774451]]

private def den10 : List (List Nat) :=
  [[1, 1, 1, 1, 1, 2, 1, 1],
    [2, 1, 1, 1, 1, 1, 1, 1],
    [1, 1, 1, 1, 1, 1, 1, 1],
    [4, 1, 1, 1, 1, 1, 1, 1],
    [18, 9, 18, 9, 36, 360, 90, 63],
    [9, 18, 36, 18, 72, 45, 36, 126],
    [6, 9, 18, 18, 36, 180, 18, 126],
    [144, 36, 72, 36, 144, 180, 72, 252]]

private def res10 : List (List Nat) :=
  [[30, 34, 20, 30, 42, 19, 50, 55],
    [25, 20, 4, 40, 53, 58, 28, 3],
    [30, 30, 40, 43, 7, 8, 24, 38],
    [39, 42, 53, 7, 47, 9, 3, 9],
    [33, 7, 35, 32, 25, 10, 6, 7],
    [34, 35, 46, 29, 20, 41, 43, 25],
    [52, 32, 29, 44, 11, 47, 28, 24],
    [27, 25, 20, 11, 55, 24, 7, 48]]

private def inv10 : List (List Nat) :=
  [[58, 48, 43, 29, 0, 50, 38, 39],
    [57, 32, 40, 49, 10, 13, 58, 23],
    [16, 5, 0, 50, 18, 9, 4, 2],
    [22, 43, 27, 12, 9, 26, 6, 56],
    [15, 28, 43, 28, 18, 7, 20, 14],
    [19, 18, 56, 56, 46, 6, 56, 43],
    [15, 58, 7, 17, 44, 40, 21, 4],
    [36, 19, 18, 6, 20, 0, 18, 36]]

private def num11 : List (List Int) :=
  [[-32, -55, -693, -13277, -73194, -1691019, -9920735, -233846041],
    [-725, -693, -847, -12584, -218889, -1127115, -24801491, -140307486],
    [-13309, -13277, -12584, -11979, -206305, -3368761, -49590398, -350762423],
    [-109807, -73194, -218889, -206305, -161051, -3162456, -49384093, -233772847],
    [-61, 9, -1321, -37963, -104642, -6446853, -283664111, -312030715],
    [-691, -1321, 136, -71963, -417247, -1611383, -70915037, -9360912203],
    [-76109, -37963, -71963, 60103, -589889, -19264633, -18905879, -7020558217],
    [-418629, -104642, -417247, -589889, 3063163, -1205657, -282408407, -4678995737]]

private def den11 : List (List Nat) :=
  [[1, 2, 1, 2, 1, 2, 1, 2],
    [2, 1, 2, 1, 2, 1, 2, 1],
    [3, 2, 1, 2, 1, 2, 3, 2],
    [2, 1, 2, 1, 2, 1, 2, 1],
    [20, 20, 20, 60, 15, 80, 300, 28],
    [20, 20, 5, 60, 40, 15, 60, 700],
    [180, 60, 60, 90, 30, 120, 12, 420],
    [80, 15, 40, 30, 240, 4, 120, 210]]

private def res11 : List (List Nat) :=
  [[165, 71, 95, 158, 90, 113, 185, 124],
    [130, 95, 69, 24, 186, 119, 109, 51],
    [29, 158, 24, 19, 151, 68, 6, 107],
    [158, 90, 186, 151, 146, 182, 32, 158],
    [125, 30, 62, 152, 129, 108, 160, 160],
    [192, 62, 106, 45, 64, 189, 86, 22],
    [143, 152, 45, 79, 83, 64, 34, 164],
    [128, 129, 64, 83, 156, 45, 108, 191]]

private def inv11 : List (List Nat) :=
  [[76, 44, 124, 182, 186, 148, 49, 162],
    [160, 68, 155, 11, 173, 35, 73, 181],
    [144, 80, 68, 54, 9, 188, 185, 194],
    [160, 35, 45, 68, 160, 114, 181, 135],
    [105, 177, 51, 62, 191, 79, 70, 117],
    [59, 84, 88, 59, 102, 68, 111, 159],
    [170, 175, 29, 100, 5, 29, 67, 44],
    [104, 136, 115, 100, 25, 170, 17, 91]]

/-! ## Small Nat/Int Boolean kernels -/

private def cellNat (L : List (List Nat)) (i j : Nat) : Nat :=
  (L.getD i []).getD j 0

private def cellInt (L : List (List Int)) (i j : Nat) : Int :=
  (L.getD i []).getD j 0

private def intModEq (p : Nat) (n : Int) (r d : Nat) : Bool :=
  decide (n % (p : Int) = ((r * d : Nat) : Int) % (p : Int))

private def rowEntryChecks (p : Nat) (nums : List (List Int))
    (dens res : List (List Nat)) (i : Nat) : Bool :=
  (List.range 8).all fun j =>
    intModEq p (cellInt nums i j) (cellNat res i j) (cellNat dens i j)

private def seedEntryChecks (p : Nat) (nums : List (List Int))
    (dens res : List (List Nat)) : Bool :=
  (List.range 8).all fun i => rowEntryChecks p nums dens res i

private def denominatorRowChecks (p : Nat) (dens : List (List Nat))
    (i : Nat) : Bool :=
  (List.range 8).all fun j => decide (cellNat dens i j % p ≠ 0)

private def denominatorChecks (p : Nat) (dens : List (List Nat)) : Bool :=
  (List.range 8).all fun i => denominatorRowChecks p dens i

private def dotMod (p : Nat) (left right : List (List Nat))
    (i j : Nat) : Nat :=
  ((List.range 8).foldl
      (fun acc k => acc + cellNat left i k * cellNat right k j) 0) % p

private def inverseCellCheck (p : Nat) (left right : List (List Nat))
    (i j : Nat) : Bool :=
  decide (dotMod p left right i j = if i = j then 1 else 0)

private def inverseRowChecks (p : Nat) (left right : List (List Nat))
    (i : Nat) : Bool :=
  (List.range 8).all fun j => inverseCellCheck p left right i j

private def inverseChecks (p : Nat) (left right : List (List Nat)) : Bool :=
  (List.range 8).all fun i => inverseRowChecks p left right i

/-! ## q = 9 -/

def q9Prime : Nat := 41
def q9SeedResidue : Nat := 2

theorem q9_prime : Nat.Prime q9Prime := by decide
theorem q9_prime_gt_ten : 10 < q9Prime := by decide
theorem q9_prime_does_not_divide_base : ¬ (q9Prime : Int) ∣ (9 : Int) := by
  decide
theorem q9_prime_does_not_divide_shift : ¬ (q9Prime : Int) ∣ ((9 : Int) - 1) := by
  decide

def q9SeedEntryCheck : Bool :=
  seedEntryChecks q9Prime num9 den9 res9

def q9InverseCheck : Bool := inverseChecks q9Prime res9 inv9
def q9DenominatorCheck : Bool := denominatorChecks q9Prime den9

theorem q9_seed_entries : q9SeedEntryCheck = true := by
  decide +kernel

theorem q9_inverse_mod : q9InverseCheck = true := by
  decide +kernel

theorem q9_denominators_are_units_mod_prime : q9DenominatorCheck = true := by
  decide +kernel

theorem q9_seed_residue_nonzero : (q9SeedResidue : ZMod q9Prime) ≠ 0 := by
  change (2 : ZMod 41) ≠ 0
  decide

/-! ## q = 10 -/

def q10Prime : Nat := 59
def q10SeedResidue : Nat := 26

theorem q10_prime : Nat.Prime q10Prime := by decide
theorem q10_prime_gt_ten : 10 < q10Prime := by decide
theorem q10_prime_does_not_divide_base : ¬ (q10Prime : Int) ∣ (10 : Int) := by
  decide
theorem q10_prime_does_not_divide_shift : ¬ (q10Prime : Int) ∣ ((10 : Int) - 1) := by
  decide

def q10SeedEntryCheck : Bool :=
  seedEntryChecks q10Prime num10 den10 res10

def q10InverseCheck : Bool := inverseChecks q10Prime res10 inv10
def q10DenominatorCheck : Bool := denominatorChecks q10Prime den10

theorem q10_seed_entries : q10SeedEntryCheck = true := by
  decide +kernel

theorem q10_inverse_mod : q10InverseCheck = true := by
  decide +kernel

theorem q10_denominators_are_units_mod_prime : q10DenominatorCheck = true := by
  decide +kernel

theorem q10_seed_residue_nonzero : (q10SeedResidue : ZMod q10Prime) ≠ 0 := by
  change (26 : ZMod 59) ≠ 0
  decide

/-! ## q = 11 -/

def q11Prime : Nat := 197
def q11SeedResidue : Nat := 174

theorem q11_prime : Nat.Prime q11Prime := by decide
theorem q11_prime_gt_ten : 10 < q11Prime := by decide
theorem q11_prime_does_not_divide_base : ¬ (q11Prime : Int) ∣ (11 : Int) := by
  decide
theorem q11_prime_does_not_divide_shift : ¬ (q11Prime : Int) ∣ ((11 : Int) - 1) := by
  decide

def q11SeedEntryCheck : Bool :=
  seedEntryChecks q11Prime num11 den11 res11

def q11InverseCheck : Bool := inverseChecks q11Prime res11 inv11
def q11DenominatorCheck : Bool := denominatorChecks q11Prime den11

theorem q11_seed_entries : q11SeedEntryCheck = true := by
  decide +kernel

theorem q11_inverse_mod : q11InverseCheck = true := by
  decide +kernel

theorem q11_denominators_are_units_mod_prime : q11DenominatorCheck = true := by
  decide +kernel

theorem q11_seed_residue_nonzero : (q11SeedResidue : ZMod q11Prime) ≠ 0 := by
  change (174 : ZMod 197) ≠ 0
  decide

/-! The complete q11 arithmetic input used by the M4 tower assembly.  Keeping
this as one theorem lets the assembly consume the same v13 table checks
without restating any of the finite obligations. -/
theorem q11_tower_arithmetic_inputs :
    Nat.Prime q11Prime ∧
      10 < q11Prime ∧
      ¬ (q11Prime : Int) ∣ (11 : Int) ∧
      ¬ (q11Prime : Int) ∣ ((11 : Int) - 1) ∧
      q11SeedEntryCheck = true ∧
      q11InverseCheck = true ∧
      q11DenominatorCheck = true ∧
      (q11SeedResidue : ZMod q11Prime) ≠ 0 := by
  exact ⟨q11_prime, q11_prime_gt_ten,
    q11_prime_does_not_divide_base,
    q11_prime_does_not_divide_shift,
    q11_seed_entries, q11_inverse_mod,
    q11_denominators_are_units_mod_prime,
    q11_seed_residue_nonzero⟩

/-! The three rows have the exact v13 prime/residue choices. -/

theorem q9_q10_q11_prime_residue_table :
    (q9Prime, q9SeedResidue) = (41, 2) ∧
      (q10Prime, q10SeedResidue) = (59, 26) ∧
      (q11Prime, q11SeedResidue) = (197, 174) := by
  decide

end Li2Lean.P0.PositiveTower

#print axioms Li2Lean.P0.PositiveTower.q9_seed_entries
#print axioms Li2Lean.P0.PositiveTower.q9_inverse_mod
#print axioms Li2Lean.P0.PositiveTower.q10_seed_entries
#print axioms Li2Lean.P0.PositiveTower.q10_inverse_mod
#print axioms Li2Lean.P0.PositiveTower.q11_seed_entries
#print axioms Li2Lean.P0.PositiveTower.q11_inverse_mod
#print axioms Li2Lean.P0.PositiveTower.q11_tower_arithmetic_inputs
