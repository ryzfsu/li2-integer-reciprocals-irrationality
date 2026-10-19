/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Li2Lean.P0.PositiveTower.BlockDeterminant
import Li2Lean.P0.PositiveTower.LocalRing

/-!
# Generic Lucas block determinant reduction

The entrywise Lucas calculation is supplied by the construction-specific
matrix producer. This module performs the matrix-level reduction once that
calculation identifies the reduced matrix with the residue block matrix.
The first theorem keeps the accumulated `a`-unit factor explicit; the
prime-power specialization cancels that factor and leaves the seed residue.
-/

namespace Li2Lean.P0.PositiveTower

noncomputable section

open Matrix

variable {p M Q : ℕ} [Fact (Nat.Prime p)]

/-! The narrow entry-to-matrix interface used by the determinant step. -/

def LucasBlockReduction
    (G : Matrix (Fin ((2 * M) * Q)) (Fin ((2 * M) * Q)) (GoodP p))
    (S : Matrix (Fin (2 * M)) (Fin (2 * M)) (ZMod p)) (a : ZMod p) : Prop :=
  (residueHomP p).mapMatrix G = residueBlockMatrix S a Q

theorem det_of_lucas_block
    (G : Matrix (Fin ((2 * M) * Q)) (Fin ((2 * M) * Q)) (GoodP p))
    (S : Matrix (Fin (2 * M)) (Fin (2 * M)) (ZMod p)) (a : ZMod p)
    (hLucas : LucasBlockReduction G S a) :
    residueHomP p (Matrix.det G) =
      a ^ (M * Q * (Q - 1)) * (Matrix.det S) ^ Q := by
  have hdet : residueHomP p (Matrix.det G) =
      Matrix.det ((residueHomP p).mapMatrix G) := by
    exact RingHom.map_det (residueHomP p) G
  calc
    residueHomP p (Matrix.det G) =
        Matrix.det ((residueHomP p).mapMatrix G) := hdet
    _ = (residueBlockMatrix S a Q).det := by
      exact congrArg Matrix.det hLucas
    _ = a ^ (M * Q * (Q - 1)) * (Matrix.det S) ^ Q := by
      exact det_p0ResidueBlockMatrix_eq S a Q

theorem det_of_lucas_block_prime_power
    (k : ℕ)
    (G : Matrix (Fin ((2 * M) * (p ^ k))) (Fin ((2 * M) * (p ^ k))) (GoodP p))
    (S : Matrix (Fin (2 * M)) (Fin (2 * M)) (ZMod p)) (a : ZMod p)
    (ha : a ≠ 0)
    (hLucas : LucasBlockReduction (Q := p ^ k) G S a) :
    residueHomP p (Matrix.det G) = (Matrix.det S) ^ (p ^ k) := by
  have hdet : residueHomP p (Matrix.det G) =
      (residueBlockMatrix S a (p ^ k)).det := by
    calc
      residueHomP p (Matrix.det G) =
          ((residueHomP p).mapMatrix G).det :=
        RingHom.map_det (residueHomP p) G
      _ = (residueBlockMatrix S a (p ^ k)).det := by
        exact congrArg Matrix.det hLucas
  rw [hdet]
  exact det_residueBlockMatrix_tower M k S a ha

end
end Li2Lean.P0.PositiveTower

#print axioms Li2Lean.P0.PositiveTower.det_of_lucas_block
#print axioms Li2Lean.P0.PositiveTower.det_of_lucas_block_prime_power
