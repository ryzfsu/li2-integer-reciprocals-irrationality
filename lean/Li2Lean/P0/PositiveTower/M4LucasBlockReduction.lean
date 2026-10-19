/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.PositiveTower.M4SourceEntries
import Li2Lean.P0.PositiveTower.BlockDeterminantReduction
import Li2Lean.P0.NonvanishingScaledLucas

namespace Li2Lean.P0.PositiveTower

open Li2Lean
open Li2Lean.P0
open EntryGoodness
open Matrix
open Li2Lean.P0.ScaledLucas

noncomputable section

variable {p : ℕ} [Fact (Nat.Prime p)]

/-- The M=4 seed residue matrix used by the Lucas block reduction. -/
def m4SeedResidueMatrix (a : ℤ) (p : ℕ) :
    Matrix (Fin (2 * 4)) (Fin (2 * 4)) (ZMod p) :=
  fun A B => m4SourceResidue a A B p

/-- The good-valued scaled matrix reindexed by the `(A,v)` decomposition. -/
noncomputable def m4TowerScaledMatrixGood
    {a : ℤ} (hp10 : 10 < p) (hunit : Nat.Coprime (a - 1).natAbs p)
    (k : ℕ) (r : ℚ) (hbound : r.den < p ^ k) :
    Matrix (Fin ((2 * 4) * p ^ k)) (Fin ((2 * 4) * p ^ k)) (GoodP p) :=
  Matrix.reindex (m4RowEquiv (p := p) k).symm (m4RowEquiv (p := p) k).symm
    (towerScaledMatrixGood (p := p) (a := a) hp10 hunit k r hbound)

theorem m4_lucas_block_reduction
    (a : ℤ) (hp10 : 10 < p)
    (hunit : Nat.Coprime (a - 1).natAbs p)
    (k : ℕ) (r : ℚ) (hbound : r.den < p ^ k) (hk : 0 < k) :
    LucasBlockReduction (p := p) (M := 4) (Q := p ^ k)
      (m4TowerScaledMatrixGood hp10 hunit k r hbound)
      (m4SeedResidueMatrix a p) (a : ZMod p) := by
  unfold LucasBlockReduction m4TowerScaledMatrixGood
  ext row col
  obtain ⟨⟨A, v⟩, rfl⟩ := finProdFinEquiv.surjective row
  obtain ⟨⟨B, w⟩, rfl⟩ := finProdFinEquiv.surjective col
  rw [ScaledLucas.rbm_apply]
  exact m4_scaled_entry a hp10 hunit k r hbound hk A B v w

#print axioms m4_lucas_block_reduction

end
end Li2Lean.P0.PositiveTower
