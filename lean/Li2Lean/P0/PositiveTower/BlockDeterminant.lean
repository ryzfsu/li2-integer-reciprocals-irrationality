/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.PencilAlgebra

/-!
# Residue block determinant at any prime and nonzero base

Port `PencilAlgebra.p0_tower_scalar_unit` and
`PencilAlgebra.det_p0ResidueBlockMatrix_83` to any prime and seed index.
Source: v13 `chapters/nonvanishing.tex:200-258`, determinant reduction after
entrywise Lucas congruence. The entrywise congruence remains a separate input.
-/
namespace Li2Lean.P0.PositiveTower
variable {p : ℕ} [Fact (Nat.Prime p)]

/-- The scalar accumulated by all residue blocks is one at each prime-power
level, for every nonzero residue base. -/
theorem tower_scalar_unit (x : ZMod p) (hx : x ≠ 0) (M k : ℕ) :
    x ^ (M * p ^ k * (p ^ k - 1)) = 1 := by
  have hrepr : ∃ d, p ^ k = (p - 1) * d + 1 := by
    induction k with
    | zero => exact ⟨0, by simp⟩
    | succ k ih =>
      obtain ⟨d, hd⟩ := ih
      refine ⟨p * d + 1, ?_⟩
      rw [pow_succ, hd]
      calc
        ((p - 1) * d + 1) * p = (p - 1) * (p * d) + p := by ring
        _ = (p - 1) * (p * d) + ((p - 1) + 1) := by
          rw [Nat.sub_add_cancel (Fact.out : Nat.Prime p).one_lt.le]
        _ = (p - 1) * (p * d + 1) + 1 := by ring
  have hdiv : p - 1 ∣ p ^ k - 1 := by
    obtain ⟨d, hd⟩ := hrepr
    exact ⟨d, by omega⟩
  obtain ⟨d, hd⟩ := hdiv
  have hfermat : x ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hx
  calc
    x ^ (M * p ^ k * (p ^ k - 1)) =
        (x ^ (p - 1)) ^ (M * p ^ k * d) := by
      rw [← pow_mul, hd]
      congr 1
      ring
    _ = 1 := by rw [hfermat, one_pow]

/-- Once entrywise Lucas identifies the residue blocks, their determinant
is the prime-power Frobenius of the literal seed determinant. -/
theorem det_residueBlockMatrix_tower (M k : ℕ)
    (S : Matrix (Fin (2 * M)) (Fin (2 * M)) (ZMod p))
    (x : ZMod p) (hx : x ≠ 0) :
    (residueBlockMatrix S x (p ^ k)).det = S.det ^ (p ^ k) := by
  rw [det_p0ResidueBlockMatrix_eq, tower_scalar_unit x hx M k, one_mul]

end Li2Lean.P0.PositiveTower
