/- 
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/

/-
Source-only seed interfaces for the positive P0 tower at q = 8, 9, 10, 11.

The source objects are the v13 P0 pencil at M = 4.  The numerical table is
kept in SeedTables.lean; this file deliberately records finite-place,
unit, nonzero, determinant, and inverse obligations as fields instead of
claiming that a LU calculation has been formalized.

v13 anchors:
* nonvanishing.tex:11-65: the base-dependent seed prime and unit statement;
* nonvanishing.tex:67-122: the M = 4 scaled source matrix and Frobenius blocks.
-/

import Mathlib
import Li2Lean.P0.PositiveBaseParam
import Li2Lean.P0.Nonvanishing
import Li2Lean.Kit.ReducedRational
import Li2Lean.P0.PositiveTower.SeedTables

namespace Li2Lean.P0.PositiveTower

noncomputable section

open Li2Lean.P0.PositiveBase
open SeedTables

/-! ## The actual v13 source objects -/

/-- The actual M = 4 P0 source matrix at T = 0 for an integer base q. -/
def sourceMatrix (q : ℕ) : Matrix (Fin 8) (Fin 8) ℚ :=
  fun r c => (p0MatrixQ (q : ℚ) 4 r c).eval 0

/-- The determinant value of the actual v13 M = 4 source matrix. -/
def sourceDeterminant (q : ℕ) : ℚ := (sourceMatrix q).det

/-- The canonical v13 seed determinant value at M = 4. -/
def seedEval (q : ℕ) : ℚ :=
  (p0CanonicalPolynomial (q : ℤ) 4).eval 0

/-- The table's auxiliary prime, with the four requested rows pinned. -/
def towerPrime : ℕ → ℕ
  | 8 => 247229
  | 9 => 41
  | 10 => 59
  | 11 => 197
  | _ => 0

/-- The printed v13 seed constant modulo the corresponding auxiliary prime. -/
def seedResidue : ℕ → ℕ
  | 8 => 112247
  | 9 => 2
  | 10 => 26
  | 11 => 174
  | _ => 0

/-- The table rows covered by this source-only file. -/
def targetBases : List ℕ := [8, 9, 10, 11]

/-- The base-dependent prime table agrees with the four source rows. -/
theorem towerPrime_8 : towerPrime 8 = 247229 := rfl
theorem towerPrime_9 : towerPrime 9 = 41 := rfl
theorem towerPrime_10 : towerPrime 10 = 59 := rfl
theorem towerPrime_11 : towerPrime 11 = 197 := rfl

/-- The seed-residue table agrees with the four source rows. -/
theorem seedResidue_8 : seedResidue 8 = 112247 := rfl
theorem seedResidue_9 : seedResidue 9 = 2 := rfl
theorem seedResidue_10 : seedResidue 10 = 26 := rfl
theorem seedResidue_11 : seedResidue 11 = 174 := rfl

def getN (L : List (List Nat)) (i j : ℕ) : Nat :=
  (L.getD i []).getD j 0

/-- Interpret one of the generated residue tables as an 8 by 8 matrix. -/
def listMat (p : ℕ) (L : List (List Nat)) :
    Matrix (Fin 8) (Fin 8) (ZMod p) :=
  fun i j => (getN L i j : ZMod p)

def residueMatrix8 : Matrix (Fin 8) (Fin 8) (ZMod 247229) :=
  listMat 247229 res8

def residueMatrix9 : Matrix (Fin 8) (Fin 8) (ZMod 41) :=
  listMat 41 res9

def residueMatrix10 : Matrix (Fin 8) (Fin 8) (ZMod 59) :=
  listMat 59 res10

def residueMatrix11 : Matrix (Fin 8) (Fin 8) (ZMod 197) :=
  listMat 197 res11

def inverseMatrix8 : Matrix (Fin 8) (Fin 8) (ZMod 247229) :=
  listMat 247229 inv8

def inverseMatrix9 : Matrix (Fin 8) (Fin 8) (ZMod 41) :=
  listMat 41 inv9

def inverseMatrix10 : Matrix (Fin 8) (Fin 8) (ZMod 59) :=
  listMat 59 inv10

def inverseMatrix11 : Matrix (Fin 8) (Fin 8) (ZMod 197) :=
  listMat 197 inv11

def sourceMatrix8 : Matrix (Fin 8) (Fin 8) ℚ := sourceMatrix 8

def sourceMatrix9 : Matrix (Fin 8) (Fin 8) ℚ := sourceMatrix 9

def sourceMatrix10 : Matrix (Fin 8) (Fin 8) ℚ := sourceMatrix 10

def sourceMatrix11 : Matrix (Fin 8) (Fin 8) ℚ := sourceMatrix 11

/-! ## Explicit finite-place interface -/

/-
The matrix and inverse are parameters, so a proof object in Prop cannot hide
Type-valued data.  The table and source equalities below force every concrete
instance to use the actual v13 objects and the printed inverse table.
-/
structure PositiveSeedInterface
    (q p seed : ℕ)
    (source : Matrix (Fin 8) (Fin 8) ℚ)
    (residue inverse : Matrix (Fin 8) (Fin 8) (ZMod p)) : Prop where
  table_prime : towerPrime q = p
  table_seed_residue : seedResidue q = seed
  prime : Nat.Prime p
  prime_gt_ten : 10 < p
  base_unit : ¬ (p : ℤ) ∣ (q : ℤ)
  shifted_base_unit : ¬ (p : ℤ) ∣ ((q : ℤ) - 1)
  source_is_v13 :
    source = sourceMatrix q
  residue_is_table :
    residue = listMat p (match q with
      | 8 => res8
      | 9 => res9
      | 10 => res10
      | 11 => res11
      | _ => [])
  inverse_is_table :
    inverse = listMat p (match q with
      | 8 => inv8
      | 9 => inv9
      | 10 => inv10
      | 11 => inv11
      | _ => [])
  seed_matrix_det :
    residue.det = (seed : ZMod p)
  inverse_check :
    residue * inverse = 1
  residue_det_nonzero :
    residue.det ≠ 0
  seed_residue_nonzero :
    (seed : ZMod p) ≠ 0
  seed_unit :
    Nat.Coprime (seedEval q).den p
  source_det_eq_seed_eval :
    source.det = seedEval q
  source_det_nonzero :
    source.det ≠ 0
  source_entry_representative :
    ∀ r c, ∃ z : ContourKit.ReducedRational p,
      z.value = source r c ∧ z.residue = residue r c
  determinant_representative :
    ∃ z : ContourKit.ReducedRational p,
      z.value = source.det ∧ z.residue = residue.det

/-- q = 8, p = 247229, seed residue 112247. -/
abbrev Q8SeedInterface :=
  PositiveSeedInterface 8 247229 112247
    sourceMatrix8 residueMatrix8 inverseMatrix8

/-- q = 9, p = 41, seed residue 2. -/
abbrev Q9SeedInterface :=
  PositiveSeedInterface 9 41 2
    sourceMatrix9 residueMatrix9 inverseMatrix9

/-- q = 10, p = 59, seed residue 26. -/
abbrev Q10SeedInterface :=
  PositiveSeedInterface 10 59 26
    sourceMatrix10 residueMatrix10 inverseMatrix10

/-- q = 11, p = 197, seed residue 174. -/
abbrev Q11SeedInterface :=
  PositiveSeedInterface 11 197 174
    sourceMatrix11 residueMatrix11 inverseMatrix11

/-! ## Generic consequences of the explicit fields -/

theorem PositiveSeedInterface.seed_residue_ne_zero
    {q p seed : ℕ}
    {source : Matrix (Fin 8) (Fin 8) ℚ}
    {residue inverse : Matrix (Fin 8) (Fin 8) (ZMod p)}
    (h : PositiveSeedInterface q p seed source residue inverse) :
    residue.det ≠ 0 := by
  exact h.residue_det_nonzero

theorem PositiveSeedInterface.seed_value_ne_zero
    {q p seed : ℕ}
    {source : Matrix (Fin 8) (Fin 8) ℚ}
    {residue inverse : Matrix (Fin 8) (Fin 8) (ZMod p)}
    (h : PositiveSeedInterface q p seed source residue inverse) :
    source.det ≠ 0 :=
  h.source_det_nonzero

theorem PositiveSeedInterface.inverse_is_right_inverse
    {q p seed : ℕ}
    {source : Matrix (Fin 8) (Fin 8) ℚ}
    {residue inverse : Matrix (Fin 8) (Fin 8) (ZMod p)}
    (h : PositiveSeedInterface q p seed source residue inverse) :
    residue * inverse = 1 :=
  h.inverse_check

theorem PositiveSeedInterface.determinant_representative_nonzero
    {q p seed : ℕ}
    {source : Matrix (Fin 8) (Fin 8) ℚ}
    {residue inverse : Matrix (Fin 8) (Fin 8) (ZMod p)}
    (h : PositiveSeedInterface q p seed source residue inverse) :
    source.det ≠ 0 := by
  obtain ⟨z, hzvalue, hzresidue⟩ := h.determinant_representative
  have hz : z.residue ≠ 0 := by
    rw [hzresidue, h.seed_matrix_det]
    exact h.seed_residue_nonzero
  have hzvalue' := ContourKit.ReducedRational.value_ne_zero z hz
  rw [hzvalue] at hzvalue'
  exact hzvalue'

/-
The q-parameterized source constructor has the frozen a = 2 regression
definitionally: it is exactly the same M = 4 p0MatrixQ source expression
specialized at q = 2.  No existing a = 2 module is rewritten here.
-/
theorem sourceMatrix_two_regression :
    sourceMatrix 2 =
      fun r c => (p0MatrixQ (2 : ℚ) 4 r c).eval 0 := rfl

end

end Li2Lean.P0.PositiveTower

