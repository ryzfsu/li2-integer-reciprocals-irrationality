/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/

import Li2Lean.P0.P0PositiveTowerSeeds
import Li2Lean.P0.PositiveTower.SeedTablesQ6Q7

set_option maxRecDepth 100000

/-! q = 6, 7, 8 finite seed boundary.

The tables are integer numerator/denominator data.  The three Boolean checks
below are closed Nat/Int computations: no Rat arithmetic, gcd, powers, or
well-founded recursion is used by the kernel.  The bridge lemmas
are named proof obligations for the tower producer; they connect the table to
the actual source matrix and will be filled by the per-q tower workers.
-/

namespace Li2Lean.P0.PositiveTower.Q6Q8

noncomputable section

open Li2Lean.P0.PositiveBase
open Li2Lean.P0.PositiveTower
open SeedTables
open SeedTablesQ6Q7

def q6q8Prime : Nat -> Nat
  | 6 => 13
  | 7 => 11
  | 8 => 247229
  | _ => 0

def q6q8Num : Nat -> List (List Int)
  | 6 => num6
  | 7 => num7
  | 8 => SeedTables.num8
  | _ => []

def q6q8Den : Nat -> List (List Nat)
  | 6 => den6
  | 7 => den7
  | 8 => SeedTables.den8
  | _ => []

def q6q8Res : Nat -> List (List Nat)
  | 6 => res6
  | 7 => res7
  | 8 => SeedTables.res8
  | _ => []

def q6q8Inv : Nat -> List (List Nat)
  | 6 => inv6
  | 7 => inv7
  | 8 => SeedTables.inv8
  | _ => []

def getI (L : List (List Int)) (i j : Nat) : Int :=
  (L.getD i []).getD j 0

def getN (L : List (List Nat)) (i j : Nat) : Nat :=
  (L.getD i []).getD j 0

/-! ## Kernel-cheap integer checks -/

def residueCheck (q : Nat) : Bool :=
  let p := q6q8Prime q
  (List.range 8).all fun i => (List.range 8).all fun j =>
    getN (q6q8Den q) i j % p != 0 &&
      (getI (q6q8Num q) i j -
          (getN (q6q8Res q) i j : Int) * (getN (q6q8Den q) i j : Int)) %
            (p : Int) == 0

def inverseCheck (q : Nat) : Bool :=
  let p := q6q8Prime q
  (List.range 8).all fun i => (List.range 8).all fun j =>
    ((List.range 8).foldl
      (fun s k => s + getN (q6q8Res q) i k * getN (q6q8Inv q) k j) 0) % p ==
      (if i = j then 1 else 0)

def baseCheck (q : Nat) : Bool :=
  let p := q6q8Prime q
  10 < p && q % p != 0 && (q - 1) % p != 0

theorem residue_check_q6 : residueCheck 6 = true := by decide
theorem residue_check_q7 : residueCheck 7 = true := by decide
theorem residue_check_q8 : residueCheck 8 = true := by decide

theorem inverse_check_q6 : inverseCheck 6 = true := by decide
theorem inverse_check_q7 : inverseCheck 7 = true := by decide
theorem inverse_check_q8 : inverseCheck 8 = true := by decide

theorem base_check_q6 : baseCheck 6 = true := by decide
theorem base_check_q7 : baseCheck 7 = true := by decide
theorem base_check_q8 : baseCheck 8 = true := by decide

theorem prime_q6 : Nat.Prime (q6q8Prime 6) := by norm_num [q6q8Prime]
theorem prime_q7 : Nat.Prime (q6q8Prime 7) := by norm_num [q6q8Prime]
theorem prime_q8 : Nat.Prime (q6q8Prime 8) := by norm_num [q6q8Prime]

theorem prime_gt_ten_q6 : 10 < q6q8Prime 6 := by norm_num [q6q8Prime]
theorem prime_gt_ten_q7 : 10 < q6q8Prime 7 := by norm_num [q6q8Prime]
theorem prime_gt_ten_q8 : 10 < q6q8Prime 8 := by norm_num [q6q8Prime]

/-! ## Matrix forms and named source bridge obligations -/

def residueMatrix (q : Nat) :
    Matrix (Fin 8) (Fin 8) (ZMod (q6q8Prime q)) :=
  fun i j => (getN (q6q8Res q) i j : ZMod (q6q8Prime q))

def inverseMatrix (q : Nat) :
    Matrix (Fin 8) (Fin 8) (ZMod (q6q8Prime q)) :=
  fun i j => (getN (q6q8Inv q) i j : ZMod (q6q8Prime q))

def seedMatrix (q : Nat) : Matrix (Fin 8) (Fin 8) Rat :=
  fun i j => (p0MatrixQ (q : Rat) 4 i j).eval 0

private theorem tower_q6_seed_entry_row0 (j : Fin 8) :
    seedMatrix 6 (0 : Fin 8) j =
      (getI (q6q8Num 6) (0 : Fin 8) j : Rat) /
        (getN (q6q8Den 6) (0 : Fin 8) j : Rat) := by
  fin_cases j <;>
    norm_num [seedMatrix, q6q8Num, q6q8Den, num6, den6, Nat.choose,
      Finset.sum_range_succ, getI, getN,
      p0MatrixQ, p0CQ, p0BQ, p0BQQ, p0TQ, p0UQ, p0Q, p0AQ]

private theorem tower_q6_seed_entry_row1 (j : Fin 8) :
    seedMatrix 6 (1 : Fin 8) j =
      (getI (q6q8Num 6) (1 : Fin 8) j : Rat) /
        (getN (q6q8Den 6) (1 : Fin 8) j : Rat) := by
  fin_cases j <;>
    norm_num [seedMatrix, q6q8Num, q6q8Den, num6, den6, Nat.choose,
      Finset.sum_range_succ, getI, getN,
      p0MatrixQ, p0CQ, p0BQ, p0BQQ, p0TQ, p0UQ, p0Q, p0AQ]

private theorem tower_q6_seed_entry_row2 (j : Fin 8) :
    seedMatrix 6 (2 : Fin 8) j =
      (getI (q6q8Num 6) (2 : Fin 8) j : Rat) /
        (getN (q6q8Den 6) (2 : Fin 8) j : Rat) := by
  fin_cases j <;>
    norm_num [seedMatrix, q6q8Num, q6q8Den, num6, den6, Nat.choose,
      Finset.sum_range_succ, getI, getN,
      p0MatrixQ, p0CQ, p0BQ, p0BQQ, p0TQ, p0UQ, p0Q, p0AQ]

private theorem tower_q6_seed_entry_row3 (j : Fin 8) :
    seedMatrix 6 (3 : Fin 8) j =
      (getI (q6q8Num 6) (3 : Fin 8) j : Rat) /
        (getN (q6q8Den 6) (3 : Fin 8) j : Rat) := by
  fin_cases j <;>
    norm_num [seedMatrix, q6q8Num, q6q8Den, num6, den6, Nat.choose,
      Finset.sum_range_succ, getI, getN,
      p0MatrixQ, p0CQ, p0BQ, p0BQQ, p0TQ, p0UQ, p0Q, p0AQ]

private theorem tower_q6_seed_entry_row4 (j : Fin 8) :
    seedMatrix 6 (4 : Fin 8) j =
      (getI (q6q8Num 6) (4 : Fin 8) j : Rat) /
        (getN (q6q8Den 6) (4 : Fin 8) j : Rat) := by
  fin_cases j <;>
    norm_num [seedMatrix, q6q8Num, q6q8Den, num6, den6, Nat.choose,
      Finset.sum_range_succ, getI, getN,
      p0MatrixQ, p0CQ, p0BQ, p0BQQ, p0TQ, p0UQ, p0Q, p0AQ]

private theorem tower_q6_seed_entry_row5 (j : Fin 8) :
    seedMatrix 6 (5 : Fin 8) j =
      (getI (q6q8Num 6) (5 : Fin 8) j : Rat) /
        (getN (q6q8Den 6) (5 : Fin 8) j : Rat) := by
  fin_cases j <;>
    norm_num [seedMatrix, q6q8Num, q6q8Den, num6, den6, Nat.choose,
      Finset.sum_range_succ, getI, getN,
      p0MatrixQ, p0CQ, p0BQ, p0BQQ, p0TQ, p0UQ, p0Q, p0AQ]

private theorem tower_q6_seed_entry_row6 (j : Fin 8) :
    seedMatrix 6 (6 : Fin 8) j =
      (getI (q6q8Num 6) (6 : Fin 8) j : Rat) /
        (getN (q6q8Den 6) (6 : Fin 8) j : Rat) := by
  fin_cases j <;>
    norm_num [seedMatrix, q6q8Num, q6q8Den, num6, den6, Nat.choose,
      Finset.sum_range_succ, getI, getN,
      p0MatrixQ, p0CQ, p0BQ, p0BQQ, p0TQ, p0UQ, p0Q, p0AQ]

private theorem tower_q6_seed_entry_row7 (j : Fin 8) :
    seedMatrix 6 (7 : Fin 8) j =
      (getI (q6q8Num 6) (7 : Fin 8) j : Rat) /
        (getN (q6q8Den 6) (7 : Fin 8) j : Rat) := by
  fin_cases j <;>
    norm_num [seedMatrix, q6q8Num, q6q8Den, num6, den6, Nat.choose,
      Finset.sum_range_succ, getI, getN,
      p0MatrixQ, p0CQ, p0BQ, p0BQQ, p0TQ, p0UQ, p0Q, p0AQ]

theorem tower_q6_seed_entry_table (i j : Fin 8) :
    seedMatrix 6 i j =
      (getI (q6q8Num 6) i j : Rat) /
        (getN (q6q8Den 6) i j : Rat) := by
  fin_cases i
  · exact tower_q6_seed_entry_row0 j
  · exact tower_q6_seed_entry_row1 j
  · exact tower_q6_seed_entry_row2 j
  · exact tower_q6_seed_entry_row3 j
  · exact tower_q6_seed_entry_row4 j
  · exact tower_q6_seed_entry_row5 j
  · exact tower_q6_seed_entry_row6 j
  · exact tower_q6_seed_entry_row7 j

private theorem tower_q7_seed_entry_row0 (j : Fin 8) :
    seedMatrix 7 (0 : Fin 8) j =
      (getI (q6q8Num 7) (0 : Fin 8) j : Rat) /
        (getN (q6q8Den 7) (0 : Fin 8) j : Rat) := by
  fin_cases j <;>
    norm_num [seedMatrix, q6q8Num, q6q8Den, num7, den7, Nat.choose,
      Finset.sum_range_succ, Finset.sum_range_zero, getI, getN,
      p0MatrixQ, p0CQ, p0BQ, p0BQQ, p0TQ, p0UQ, p0Q, p0AQ]

private theorem tower_q7_seed_entry_row1 (j : Fin 8) :
    seedMatrix 7 (1 : Fin 8) j =
      (getI (q6q8Num 7) (1 : Fin 8) j : Rat) /
        (getN (q6q8Den 7) (1 : Fin 8) j : Rat) := by
  fin_cases j <;>
    norm_num [seedMatrix, q6q8Num, q6q8Den, num7, den7, Nat.choose,
      Finset.sum_range_succ, Finset.sum_range_zero, getI, getN,
      p0MatrixQ, p0CQ, p0BQ, p0BQQ, p0TQ, p0UQ, p0Q, p0AQ]

private theorem tower_q7_seed_entry_row2 (j : Fin 8) :
    seedMatrix 7 (2 : Fin 8) j =
      (getI (q6q8Num 7) (2 : Fin 8) j : Rat) /
        (getN (q6q8Den 7) (2 : Fin 8) j : Rat) := by
  fin_cases j <;>
    norm_num [seedMatrix, q6q8Num, q6q8Den, num7, den7, Nat.choose,
      Finset.sum_range_succ, Finset.sum_range_zero, getI, getN,
      p0MatrixQ, p0CQ, p0BQ, p0BQQ, p0TQ, p0UQ, p0Q, p0AQ]

private theorem tower_q7_seed_entry_row3 (j : Fin 8) :
    seedMatrix 7 (3 : Fin 8) j =
      (getI (q6q8Num 7) (3 : Fin 8) j : Rat) /
        (getN (q6q8Den 7) (3 : Fin 8) j : Rat) := by
  fin_cases j <;>
    norm_num [seedMatrix, q6q8Num, q6q8Den, num7, den7, Nat.choose,
      Finset.sum_range_succ, Finset.sum_range_zero, getI, getN,
      p0MatrixQ, p0CQ, p0BQ, p0BQQ, p0TQ, p0UQ, p0Q, p0AQ]

private theorem tower_q7_seed_entry_row4 (j : Fin 8) :
    seedMatrix 7 (4 : Fin 8) j =
      (getI (q6q8Num 7) (4 : Fin 8) j : Rat) /
        (getN (q6q8Den 7) (4 : Fin 8) j : Rat) := by
  fin_cases j <;>
    norm_num [seedMatrix, q6q8Num, q6q8Den, num7, den7, Nat.choose,
      Finset.sum_range_succ, Finset.sum_range_zero, getI, getN,
      p0MatrixQ, p0CQ, p0BQ, p0BQQ, p0TQ, p0UQ, p0Q, p0AQ]

private theorem tower_q7_seed_entry_row5 (j : Fin 8) :
    seedMatrix 7 (5 : Fin 8) j =
      (getI (q6q8Num 7) (5 : Fin 8) j : Rat) /
        (getN (q6q8Den 7) (5 : Fin 8) j : Rat) := by
  fin_cases j <;>
    norm_num [seedMatrix, q6q8Num, q6q8Den, num7, den7, Nat.choose,
      Finset.sum_range_succ, Finset.sum_range_zero, getI, getN,
      p0MatrixQ, p0CQ, p0BQ, p0BQQ, p0TQ, p0UQ, p0Q, p0AQ]

private theorem tower_q7_seed_entry_row6 (j : Fin 8) :
    seedMatrix 7 (6 : Fin 8) j =
      (getI (q6q8Num 7) (6 : Fin 8) j : Rat) /
        (getN (q6q8Den 7) (6 : Fin 8) j : Rat) := by
  fin_cases j <;>
    norm_num [seedMatrix, q6q8Num, q6q8Den, num7, den7, Nat.choose,
      Finset.sum_range_succ, Finset.sum_range_zero, getI, getN,
      p0MatrixQ, p0CQ, p0BQ, p0BQQ, p0TQ, p0UQ, p0Q, p0AQ]

private theorem tower_q7_seed_entry_row7 (j : Fin 8) :
    seedMatrix 7 (7 : Fin 8) j =
      (getI (q6q8Num 7) (7 : Fin 8) j : Rat) /
        (getN (q6q8Den 7) (7 : Fin 8) j : Rat) := by
  fin_cases j <;>
    norm_num [seedMatrix, q6q8Num, q6q8Den, num7, den7, Nat.choose,
      Finset.sum_range_succ, Finset.sum_range_zero, getI, getN,
      p0MatrixQ, p0CQ, p0BQ, p0BQQ, p0TQ, p0UQ, p0Q, p0AQ]

theorem tower_q7_seed_entry_table (i j : Fin 8) :
    seedMatrix 7 i j =
      (getI (q6q8Num 7) i j : Rat) /
        (getN (q6q8Den 7) i j : Rat) := by
  fin_cases i
  · exact tower_q7_seed_entry_row0 j
  · exact tower_q7_seed_entry_row1 j
  · exact tower_q7_seed_entry_row2 j
  · exact tower_q7_seed_entry_row3 j
  · exact tower_q7_seed_entry_row4 j
  · exact tower_q7_seed_entry_row5 j
  · exact tower_q7_seed_entry_row6 j
  · exact tower_q7_seed_entry_row7 j

private theorem tower_q8_seed_entry_row0 (j : Fin 8) :
    seedMatrix 8 (0 : Fin 8) j =
      (getI (q6q8Num 8) (0 : Fin 8) j : Rat) /
        (getN (q6q8Den 8) (0 : Fin 8) j : Rat) := by
  fin_cases j <;>
    norm_num [seedMatrix, q6q8Num, q6q8Den, getI, getN,
      SeedTables.num8, SeedTables.den8, Nat.choose,
      Finset.sum_range_succ, Finset.sum_range_zero,
      p0MatrixQ, p0CQ, p0BQ, p0BQQ, p0TQ, p0UQ, p0Q, p0AQ]

private theorem tower_q8_seed_entry_row1 (j : Fin 8) :
    seedMatrix 8 (1 : Fin 8) j =
      (getI (q6q8Num 8) (1 : Fin 8) j : Rat) /
        (getN (q6q8Den 8) (1 : Fin 8) j : Rat) := by
  fin_cases j <;>
    norm_num [seedMatrix, q6q8Num, q6q8Den, getI, getN,
      SeedTables.num8, SeedTables.den8, Nat.choose,
      Finset.sum_range_succ, Finset.sum_range_zero,
      p0MatrixQ, p0CQ, p0BQ, p0BQQ, p0TQ, p0UQ, p0Q, p0AQ]

private theorem tower_q8_seed_entry_row2 (j : Fin 8) :
    seedMatrix 8 (2 : Fin 8) j =
      (getI (q6q8Num 8) (2 : Fin 8) j : Rat) /
        (getN (q6q8Den 8) (2 : Fin 8) j : Rat) := by
  fin_cases j <;>
    norm_num [seedMatrix, q6q8Num, q6q8Den, getI, getN,
      SeedTables.num8, SeedTables.den8, Nat.choose,
      Finset.sum_range_succ, Finset.sum_range_zero,
      p0MatrixQ, p0CQ, p0BQ, p0BQQ, p0TQ, p0UQ, p0Q, p0AQ]

private theorem tower_q8_seed_entry_row3 (j : Fin 8) :
    seedMatrix 8 (3 : Fin 8) j =
      (getI (q6q8Num 8) (3 : Fin 8) j : Rat) /
        (getN (q6q8Den 8) (3 : Fin 8) j : Rat) := by
  fin_cases j <;>
    norm_num [seedMatrix, q6q8Num, q6q8Den, getI, getN,
      SeedTables.num8, SeedTables.den8, Nat.choose,
      Finset.sum_range_succ, Finset.sum_range_zero,
      p0MatrixQ, p0CQ, p0BQ, p0BQQ, p0TQ, p0UQ, p0Q, p0AQ]

private theorem tower_q8_seed_entry_row4 (j : Fin 8) :
    seedMatrix 8 (4 : Fin 8) j =
      (getI (q6q8Num 8) (4 : Fin 8) j : Rat) /
        (getN (q6q8Den 8) (4 : Fin 8) j : Rat) := by
  fin_cases j <;>
    norm_num [seedMatrix, q6q8Num, q6q8Den, getI, getN,
      SeedTables.num8, SeedTables.den8, Nat.choose,
      Finset.sum_range_succ, Finset.sum_range_zero,
      p0MatrixQ, p0CQ, p0BQ, p0BQQ, p0TQ, p0UQ, p0Q, p0AQ]

private theorem tower_q8_seed_entry_row5 (j : Fin 8) :
    seedMatrix 8 (5 : Fin 8) j =
      (getI (q6q8Num 8) (5 : Fin 8) j : Rat) /
        (getN (q6q8Den 8) (5 : Fin 8) j : Rat) := by
  fin_cases j <;>
    norm_num [seedMatrix, q6q8Num, q6q8Den, getI, getN,
      SeedTables.num8, SeedTables.den8, Nat.choose,
      Finset.sum_range_succ, Finset.sum_range_zero,
      p0MatrixQ, p0CQ, p0BQ, p0BQQ, p0TQ, p0UQ, p0Q, p0AQ]

private theorem tower_q8_seed_entry_row6 (j : Fin 8) :
    seedMatrix 8 (6 : Fin 8) j =
      (getI (q6q8Num 8) (6 : Fin 8) j : Rat) /
        (getN (q6q8Den 8) (6 : Fin 8) j : Rat) := by
  fin_cases j <;>
    norm_num [seedMatrix, q6q8Num, q6q8Den, getI, getN,
      SeedTables.num8, SeedTables.den8, Nat.choose,
      Finset.sum_range_succ, Finset.sum_range_zero,
      p0MatrixQ, p0CQ, p0BQ, p0BQQ, p0TQ, p0UQ, p0Q, p0AQ]

private theorem tower_q8_seed_entry_row7 (j : Fin 8) :
    seedMatrix 8 (7 : Fin 8) j =
      (getI (q6q8Num 8) (7 : Fin 8) j : Rat) /
        (getN (q6q8Den 8) (7 : Fin 8) j : Rat) := by
  fin_cases j <;>
    norm_num [seedMatrix, q6q8Num, q6q8Den, getI, getN,
      SeedTables.num8, SeedTables.den8, Nat.choose,
      Finset.sum_range_succ, Finset.sum_range_zero,
      p0MatrixQ, p0CQ, p0BQ, p0BQQ, p0TQ, p0UQ, p0Q, p0AQ]

theorem tower_q8_seed_entry_table (i j : Fin 8) :
    seedMatrix 8 i j =
      (getI (q6q8Num 8) i j : Rat) /
        (getN (q6q8Den 8) i j : Rat) := by
  fin_cases i
  · exact tower_q8_seed_entry_row0 j
  · exact tower_q8_seed_entry_row1 j
  · exact tower_q8_seed_entry_row2 j
  · exact tower_q8_seed_entry_row3 j
  · exact tower_q8_seed_entry_row4 j
  · exact tower_q8_seed_entry_row5 j
  · exact tower_q8_seed_entry_row6 j
  · exact tower_q8_seed_entry_row7 j

theorem tower_q6_inverse_mod :
    residueMatrix 6 * inverseMatrix 6 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem tower_q7_inverse_mod :
    residueMatrix 7 * inverseMatrix 7 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem tower_q8_inverse_mod :
    residueMatrix 8 * inverseMatrix 8 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-! These are the exact determinant/residue interfaces consumed by the
parametric tower assembly.  They are intentionally separate from the finite
Bool checks: a check is not silently treated as a proof about p0MatrixQ. -/

theorem tower_q6_seed_residue_bridge :
    (residueMatrix 6).det = (2 : ZMod (q6q8Prime 6)) := by
  let L : Matrix (Fin 8) (Fin 8) (ZMod (q6q8Prime 6)) := !![
    1, 0, 0, 0, 0, 0, 0, 0;
    9, 1, 0, 0, 0, 0, 0, 0;
    12, 3, 1, 0, 0, 0, 0, 0;
    10, 10, 1, 1, 0, 0, 0, 0;
    5, 0, 1, 12, 1, 0, 0, 0;
    1, 7, 8, 10, 7, 1, 0, 0;
    2, 1, 11, 4, 3, 7, 1, 0;
    9, 10, 0, 0, 5, 1, 12, 1
  ]
  let U : Matrix (Fin 8) (Fin 8) (ZMod (q6q8Prime 6)) := !![
    9, 11, 10, 8, 0, 7, 4, 0;
    0, 2, 5, 12, 8, 8, 12, 11;
    0, 0, 1, 1, 12, 2, 4, 2;
    0, 0, 0, 4, 8, 6, 2, 5;
    0, 0, 0, 0, 11, 4, 7, 11;
    0, 0, 0, 0, 0, 10, 10, 3;
    0, 0, 0, 0, 0, 0, 8, 10;
    0, 0, 0, 0, 0, 0, 0, 12
  ]
  have hLU : residueMatrix 6 = L * U := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [L, U, residueMatrix, listMat, getN, q6q8Res,
        q6q8Prime, SeedTablesQ6Q7.res6, Matrix.mul_apply,
        Fin.sum_univ_succ, List.getD] <;> decide
  have hL : L.IsLowerTriangular := by
    decide
  have hU : U.IsUpperTriangular := by
    decide
  have hLd : L.det = 1 := by
    rw [Matrix.det_of_isLowerTriangular L hL]
    norm_num [L, Fin.prod_univ_succ] <;> decide
  have hUd : U.det = 2 := by
    rw [Matrix.det_of_isUpperTriangular hU]
    norm_num [U, Fin.prod_univ_succ] <;> decide
  rw [hLU, Matrix.det_mul, hLd, hUd]
  norm_num [q6q8Prime]

theorem tower_q7_seed_residue_bridge :
    (residueMatrix 7).det = (8 : ZMod (q6q8Prime 7)) := by
  let L : Matrix (Fin 8) (Fin 8) (ZMod (q6q8Prime 7)) := !![
    1, 0, 0, 0, 0, 0, 0, 0;
    1, 1, 0, 0, 0, 0, 0, 0;
    6, 4, 1, 0, 0, 0, 0, 0;
    0, 1, 10, 1, 0, 0, 0, 0;
    9, 1, 3, 7, 1, 0, 0, 0;
    2, 1, 4, 9, 0, 1, 0, 0;
    8, 4, 8, 4, 3, 6, 1, 0;
    1, 9, 8, 6, 5, 7, 3, 1
  ]
  let U : Matrix (Fin 8) (Fin 8) (ZMod (q6q8Prime 7)) := !![
    2, 10, 2, 6, 3, 5, 6, 6;
    0, 3, 8, 4, 6, 1, 1, 3;
    0, 0, 10, 5, 10, 3, 10, 2;
    0, 0, 0, 9, 4, 2, 3, 8;
    0, 0, 0, 0, 1, 2, 3, 4;
    0, 0, 0, 0, 0, 2, 1, 4;
    0, 0, 0, 0, 0, 0, 9, 0;
    0, 0, 0, 0, 0, 0, 0, 9
  ]
  have hLU : residueMatrix 7 = L * U := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [L, U, residueMatrix, listMat, getN, q6q8Res,
        q6q8Prime, SeedTablesQ6Q7.res7, Matrix.mul_apply,
        Fin.sum_univ_succ, List.getD] <;> decide
  have hL : L.IsLowerTriangular := by
    decide
  have hU : U.IsUpperTriangular := by
    decide
  have hLd : L.det = 1 := by
    rw [Matrix.det_of_isLowerTriangular L hL]
    norm_num [L, Fin.prod_univ_succ] <;> decide
  have hUd : U.det = 8 := by
    rw [Matrix.det_of_isUpperTriangular hU]
    norm_num [U, Fin.prod_univ_succ] <;> decide
  rw [hLU, Matrix.det_mul, hLd, hUd]
  norm_num [q6q8Prime]

theorem tower_q8_seed_residue_bridge :
    (residueMatrix 8).det = (112247 : ZMod (q6q8Prime 8)) := by
  let L : Matrix (Fin 8) (Fin 8) (ZMod (q6q8Prime 8)) := !![
    1, 0, 0, 0, 0, 0, 0, 0;
    145121, 1, 0, 0, 0, 0, 0, 0;
    100399, 177640, 1, 0, 0, 0, 0, 0;
    239835, 166208, 200164, 1, 0, 0, 0, 0;
    221892, 19691, 138015, 128331, 1, 0, 0, 0;
    162773, 204724, 33564, 223143, 139579, 1, 0, 0;
    208764, 122460, 57164, 218327, 203005, 236469, 1, 0;
    85602, 57484, 213094, 41228, 166686, 89280, 5662, 1
  ]
  let U : Matrix (Fin 8) (Fin 8) (ZMod (q6q8Prime 8)) := !![
    247206, 247209, 246869, 244681, 226757, 75203, 114264, 25771;
    0, 182541, 78017, 156217, 182920, 160394, 180464, 235;
    0, 0, 19643, 10787, 237688, 231020, 103463, 68702;
    0, 0, 0, 238321, 51266, 157187, 222828, 211299;
    0, 0, 0, 0, 107253, 25085, 102933, 165216;
    0, 0, 0, 0, 0, 109371, 3956, 182800;
    0, 0, 0, 0, 0, 0, 181242, 88959;
    0, 0, 0, 0, 0, 0, 0, 125960
  ]
  have hLU : residueMatrix 8 = L * U := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      decide
  have hL : L.IsLowerTriangular := by
    decide
  have hU : U.IsUpperTriangular := by
    decide
  have hLd : L.det = 1 := by
    rw [Matrix.det_of_isLowerTriangular L hL]
    norm_num [L, Fin.prod_univ_succ]
  have hUd : U.det = 112247 := by
    rw [Matrix.det_of_isUpperTriangular hU]
    norm_num [U, Fin.prod_univ_succ, q6q8Prime] <;> decide
  rw [hLU, Matrix.det_mul, hLd, hUd]
  norm_num

private theorem source_det_bridge_at (q : Nat) (hq : InRange (q : Int)) :
    (seedMatrix q).det =
      p0SourceEvalQ (family (q : Int) hq) 4 0 := by
  unfold seedMatrix p0SourceEvalQ
  change Matrix.det ((Polynomial.evalRingHom (0 : Rat)).mapMatrix
      (p0MatrixQ (q : Rat) 4)) =
    (p0CanonicalPolynomial (q : Int) 4).eval 0
  have hdet :
      Matrix.det ((Polynomial.evalRingHom (0 : Rat)).mapMatrix
        (p0MatrixQ (q : Rat) 4)) =
        ((p0MatrixQ (q : Rat) 4).det).eval 0 := by
    exact (RingHom.map_det
      (Polynomial.evalRingHom (0 : Rat)) (p0MatrixQ (q : Rat) 4)).symm
  rw [hdet]
  simp [p0CanonicalPolynomial]

theorem tower_q6_source_det_bridge :
    (seedMatrix 6).det =
      p0SourceEvalQ (family (6 : Int) (by norm_num [InRange])) 4 0 := by
  exact source_det_bridge_at 6 (by norm_num [InRange])

theorem tower_q7_source_det_bridge :
    (seedMatrix 7).det =
      p0SourceEvalQ (family (7 : Int) (by norm_num [InRange])) 4 0 := by
  exact source_det_bridge_at 7 (by norm_num [InRange])

theorem tower_q8_source_det_bridge :
    (seedMatrix 8).det =
      p0SourceEvalQ (family (8 : Int) (by norm_num [InRange])) 4 0 := by
  exact source_det_bridge_at 8 (by norm_num [InRange])

end
end Li2Lean.P0.PositiveTower.Q6Q8

#print axioms Li2Lean.P0.PositiveTower.Q6Q8.residue_check_q6
#print axioms Li2Lean.P0.PositiveTower.Q6Q8.inverse_check_q6
