/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

The q = 2 finite-place certificates for the actual signed V seed.  The
representatives below are made from the actual rational source matrix, and
their residues are compared through the public ReducedRational API.
-/

import Li2Lean.B3.Q2SeedT0LU
import Li2Lean.V.NegativeTwoSeed
import Li2Lean.P0.PositiveTower.LocalRing

namespace Li2Lean.B3

noncomputable section

open Li2Lean
open Li2Lean.P0.PositiveTower

private abbrev q2Prime : ℕ := vSeedPrime 2

private theorem q2Prime_eq_eleven : q2Prime = 11 := by
  rfl

local instance q2PrimeFact : Fact (Nat.Prime q2Prime) :=
  ⟨q2SeedPrime_prime⟩

local instance q2PrimeFactExact : Fact (Nat.Prime (vSeedPrime 2)) :=
  ⟨q2SeedPrime_prime⟩

local instance q11Fact : Fact (Nat.Prime 11) :=
  ⟨by norm_num⟩

private theorem q2_inv_2 : (2 : Q2SeedRing)⁻¹ = 6 := by
  apply ZMod.inv_eq_of_mul_eq_one
  decide
private theorem q2_inv_3 : (3 : Q2SeedRing)⁻¹ = 4 := by
  apply ZMod.inv_eq_of_mul_eq_one
  decide
private theorem q2_inv_4 : (4 : Q2SeedRing)⁻¹ = 3 := by
  apply ZMod.inv_eq_of_mul_eq_one
  decide
private theorem q2_inv_5 : (5 : Q2SeedRing)⁻¹ = 9 := by
  apply ZMod.inv_eq_of_mul_eq_one
  decide
private theorem q2_inv_6 : (6 : Q2SeedRing)⁻¹ = 2 := by
  apply ZMod.inv_eq_of_mul_eq_one
  decide
private theorem q2_inv_7 : (7 : Q2SeedRing)⁻¹ = 8 := by
  apply ZMod.inv_eq_of_mul_eq_one
  decide
private theorem q2_inv_8 : (8 : Q2SeedRing)⁻¹ = 7 := by
  apply ZMod.inv_eq_of_mul_eq_one
  decide
private theorem q2_inv_9 : (9 : Q2SeedRing)⁻¹ = 5 := by
  apply ZMod.inv_eq_of_mul_eq_one
  decide
private theorem q2_inv_10 : (10 : Q2SeedRing)⁻¹ = 10 := by
  apply ZMod.inv_eq_of_mul_eq_one
  decide
private theorem q2_inv_15 : (15 : Q2SeedRing)⁻¹ = 3 := by
  apply ZMod.inv_eq_of_mul_eq_one
  decide
private theorem q2_inv_18 : (18 : Q2SeedRing)⁻¹ = 8 := by
  apply ZMod.inv_eq_of_mul_eq_one
  decide
private theorem q2_inv_20 : (20 : Q2SeedRing)⁻¹ = 5 := by
  apply ZMod.inv_eq_of_mul_eq_one
  decide
private theorem q2_inv_24 : (24 : Q2SeedRing)⁻¹ = 6 := by
  apply ZMod.inv_eq_of_mul_eq_one
  decide
private theorem q2_inv_36 : (36 : Q2SeedRing)⁻¹ = 4 := by
  apply ZMod.inv_eq_of_mul_eq_one
  decide
private theorem q2_inv_45 : (45 : Q2SeedRing)⁻¹ = 1 := by
  apply ZMod.inv_eq_of_mul_eq_one
  decide
private theorem q2_inv_90 : (90 : Q2SeedRing)⁻¹ = 6 := by
  apply ZMod.inv_eq_of_mul_eq_one
  decide
private theorem q2_inv_105 : (105 : Q2SeedRing)⁻¹ = 2 := by
  apply ZMod.inv_eq_of_mul_eq_one
  decide
private theorem q2_inv_120 : (120 : Q2SeedRing)⁻¹ = 10 := by
  apply ZMod.inv_eq_of_mul_eq_one
  decide
private theorem q2_inv_144 : (144 : Q2SeedRing)⁻¹ = 1 := by
  apply ZMod.inv_eq_of_mul_eq_one
  decide
private theorem q2_inv_350 : (350 : Q2SeedRing)⁻¹ = 5 := by
  apply ZMod.inv_eq_of_mul_eq_one
  decide
private theorem q2_inv_420 : (420 : Q2SeedRing)⁻¹ = 6 := by
  apply ZMod.inv_eq_of_mul_eq_one
  decide
private theorem q2_inv_1008 : (1008 : Q2SeedRing)⁻¹ = 8 := by
  apply ZMod.inv_eq_of_mul_eq_one
  decide
private theorem q2_inv_1260 : (1260 : Q2SeedRing)⁻¹ = 2 := by
  apply ZMod.inv_eq_of_mul_eq_one
  decide
private theorem q2_inv_1680 : (1680 : Q2SeedRing)⁻¹ = 7 := by
  apply ZMod.inv_eq_of_mul_eq_one
  decide
private theorem q2_inv_1800 : (1800 : Q2SeedRing)⁻¹ = 8 := by
  apply ZMod.inv_eq_of_mul_eq_one
  decide
private theorem q2_inv_2520 : (2520 : Q2SeedRing)⁻¹ = 1 := by
  apply ZMod.inv_eq_of_mul_eq_one
  decide
private theorem q2_inv_3150 : (3150 : Q2SeedRing)⁻¹ = 3 := by
  apply ZMod.inv_eq_of_mul_eq_one
  decide
private theorem q2_inv_3360 : (3360 : Q2SeedRing)⁻¹ = 9 := by
  apply ZMod.inv_eq_of_mul_eq_one
  decide
private theorem q2_inv_4200 : (4200 : Q2SeedRing)⁻¹ = 5 := by
  apply ZMod.inv_eq_of_mul_eq_one
  decide
private theorem q2_inv_7560 : (7560 : Q2SeedRing)⁻¹ = 4 := by
  apply ZMod.inv_eq_of_mul_eq_one
  decide
private theorem q2_inv_8820 : (8820 : Q2SeedRing)⁻¹ = 5 := by
  apply ZMod.inv_eq_of_mul_eq_one
  decide
private theorem q2_inv_constant :
    (2333772000000000 : Q2SeedRing)⁻¹ = 10 := by
  apply ZMod.inv_eq_of_mul_eq_one
  decide

theorem q2_seed_residue_det_eq_four :
    q2SeedMatrixResidue.det = (4 : Q2SeedRing) := by
  have h := Li2Lean.vTwoSeed_det_zero
  rw [Li2Lean.vTwoSeed_matrix_explicit] at h
  have hM : q2SeedMatrixResidue = !![
      5, 0, 1, 5, 1, 7, 0, 2, 3;
      3, 1, 0, 9, 1, 9, 8, 0, 7;
      5, 5, 9, 0, 4, 9, 4, 6, 0;
      2, 1, 1, 4, 0, 3, 4, 3, 10;
      8, 1, 8, 2, 2, 5, 6, 0, 1;
      8, 8, 3, 7, 10, 4, 0, 5, 9;
      4, 2, 7, 3, 2, 8, 5, 10, 5;
      9, 2, 10, 2, 9, 3, 1, 9, 3;
      6, 4, 3, 9, 2, 8, 7, 5, 10
    ] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [hM]
  exact h

private theorem q2_source_entry_residue_cast (r c : Fin 9) :
    ((q2SourceMatrixAtZero r c : ℚ) : Q2SeedRing) =
      q2SeedMatrixResidue r c := by
  rw [q2_source_eq_explicit]
  fin_cases r <;> fin_cases c <;>
    norm_num [q2SourceMatrixAtZeroExplicit, q2SeedMatrixResidue,
      Rat.cast_def, div_eq_mul_inv, q2_inv_2, q2_inv_3, q2_inv_4,
      q2_inv_5, q2_inv_6, q2_inv_7, q2_inv_8, q2_inv_9, q2_inv_10,
      q2_inv_15, q2_inv_18, q2_inv_20, q2_inv_24, q2_inv_36, q2_inv_45,
      q2_inv_90, q2_inv_105, q2_inv_120, q2_inv_144, q2_inv_350,
      q2_inv_420, q2_inv_1008, q2_inv_1260, q2_inv_1680, q2_inv_1800,
      q2_inv_2520, q2_inv_3150, q2_inv_3360, q2_inv_4200, q2_inv_7560,
      q2_inv_8820, q2_inv_constant] <;> decide

private theorem q2_source_entry_good (r c : Fin 9) :
    q2SourceMatrixAtZero r c ∈ GoodP q2Prime := by
  change Nat.Coprime (q2SourceMatrixAtZero r c).den 11
  rw [q2_source_eq_explicit]
  fin_cases r <;> fin_cases c <;>
    norm_num [q2SourceMatrixAtZeroExplicit, GoodP, q2Prime, vSeedPrime]

theorem q2_source_entry_representative :
    ∀ r c, ∃ z : ContourKit.ReducedRational q2Prime,
      z.value = q2SourceMatrixAtZero r c ∧
      z.residue = q2SeedMatrixResidue r c := by
  intro r c
  let x := q2SourceMatrixAtZero r c
  have hx : x ∈ GoodP q2Prime := q2_source_entry_good r c
  let z : ContourKit.ReducedRational q2Prime := reducedOfP q2Prime x hx
  refine ⟨z, ?_, ?_⟩
  · rfl
  · calc
      z.residue = (x : ZMod q2Prime) := by
        dsimp [z]
        exact reducedOfP_residue q2Prime x hx
      _ = q2SeedMatrixResidue r c := by
        exact q2_source_entry_residue_cast r c

theorem q2_determinant_good :
    q2SourceMatrixAtZero.det ∈ GoodP q2Prime := by
  rw [q2_source_eq_explicit, q2_lu0_det]
  change Nat.Coprime
    ((158649262379640306631463 / 2333772000000000 : ℚ).den) 11
  norm_num [GoodP, q2Prime, vSeedPrime]

theorem q2_determinant_residue_cast :
    ((q2SourceMatrixAtZero.det : ℚ) : Q2SeedRing) =
      q2SeedMatrixResidue.det := by
  rw [q2_source_eq_explicit, q2_lu0_det]
  have h := q2_seed_residue_det_eq_four
  rw [h]
  norm_num [q2SeedMatrixResidue, Rat.cast_def, div_eq_mul_inv,
    q2_inv_constant] <;> decide

theorem q2_determinant_representative :
    ∃ z : ContourKit.ReducedRational q2Prime,
      z.value = q2SourceMatrixAtZero.det ∧
      z.residue = q2SeedMatrixResidue.det := by
  let x := q2SourceMatrixAtZero.det
  have hx : x ∈ GoodP q2Prime := q2_determinant_good
  let z : ContourKit.ReducedRational q2Prime := reducedOfP q2Prime x hx
  refine ⟨z, ?_, ?_⟩
  · rfl
  · calc
      z.residue = (x : ZMod q2Prime) := by
        dsimp [z]
        exact reducedOfP_residue q2Prime x hx
      _ = q2SeedMatrixResidue.det := by
        exact q2_determinant_residue_cast

#print axioms q2_seed_residue_det_eq_four
#print axioms q2_source_entry_representative
#print axioms q2_determinant_representative

end
end Li2Lean.B3
