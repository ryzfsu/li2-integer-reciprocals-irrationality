/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.Nonvanishing
import Li2Lean.P0.PositiveTower.SeedArgument
import Li2Lean.P0.PositiveTower.ScaledMatrix
import Li2Lean.P0.PositiveTower.PencilEvaluation

namespace Li2Lean.P0.PositiveTower

noncomputable section

open Li2Lean
open EntryGoodness

variable {p : ℕ} [Fact (Nat.Prime p)]

/-! The finite Lucas calculation is intentionally an input here.  This theorem
packages it into the exact reduced-rational `frobenius` field consumed by the
existing P0 certificate. -/
theorem frobenius_field_of_residue_det
    {F : P0Family} {M p : ℕ}
    [Fact (Nat.Prime p)]
    (hM : M = 4)
    (hp10 : 10 < p)
    (hunit : Nat.Coprime (F.a - 1).natAbs p)
    (seed : ContourKit.ReducedRational p)
    (hseed_value : seed.value = p0SourceEvalQ F M 0)
    (hgood : ∀ (k : ℕ) (r : ℚ), r.den < p ^ k →
      p0SourceEvalQ F (M * p ^ k) r ∈ GoodP p ∧
      p0SourceEvalQ F M ((p ^ k : ℕ) ^ 2 * r) ∈ GoodP p)
    (htransport : ∀ (k : ℕ) (r : ℚ) (hk : r.den < p ^ k),
      ((p0SourceEvalQ F M ((p ^ k : ℕ) ^ 2 * r) : ℚ) : ZMod p) =
        seed.residue)
    (hdet : ∀ (k : ℕ) (r : ℚ) (hk : r.den < p ^ k),
      residueHomP p
          (Matrix.det (towerScaledMatrixGood (p := p) (a := F.a)
            hp10 hunit k r hk)) = seed.residue ^ (p ^ k)) :
    ∀ r : ℚ, ∃ k₁, ∀ k : ℕ, k₁ ≤ k →
      ∃ lhs rhs : ContourKit.ReducedRational p,
        lhs.value = (p ^ k : ℚ) ^ (3 * M * p ^ k) *
          p0SourceEvalQ F (M * p ^ k) r ∧
        rhs.value = (p0SourceEvalQ F M ((p ^ k : ℕ) ^ 2 * r)) ^ (p ^ k) ∧
        lhs.residue = rhs.residue ∧
        (∀ s : ContourKit.ReducedRational p,
          s.value = p0SourceEvalQ F M ((p ^ k : ℕ) ^ 2 * r) →
          rhs.residue = s.residue ^ (p ^ k)) := by
  subst M
  intro r
  refine ⟨r.den, ?_⟩
  intro k hk
  have hden : r.den < p ^ k := by
    exact lt_of_lt_of_le
      (Nat.lt_pow_self (Fact.out : Nat.Prime p).one_lt)
      (Nat.pow_le_pow_right (Fact.out : Nat.Prime p).pos hk)
  obtain ⟨hscaled, hseed⟩ := hgood k r hden
  have hseedCop : Nat.Coprime
      (p0SourceEvalQ F 4 ((p ^ k : ℕ) ^ 2 * r)).den p := by
    have hseed' := hseed
    change Nat.Coprime
      (p0SourceEvalQ F 4 ((p ^ k : ℕ) ^ 2 * r)).den p at hseed'
    exact hseed'
  let lhsVal : ℚ :=
    (p ^ k : ℚ) ^ (3 * 4 * p ^ k) *
      p0SourceEvalQ F (4 * p ^ k) r
  let rhsVal : ℚ :=
    (p0SourceEvalQ F 4 ((p ^ k : ℕ) ^ 2 * r)) ^ (p ^ k)
  have hfactor : ((p : ℚ) ^ k) ^ (3 * 4 * p ^ k) ∈ GoodP p := by
    exact (GoodP p).pow_mem
      ((GoodP p).pow_mem (EntryGoodness.natRat_good (p := p) p) k) _
  have hlhsGood : lhsVal ∈ GoodP p := by
    exact (GoodP p).mul_mem hfactor hscaled
  have hrhsGood : rhsVal ∈ GoodP p := by
    exact (GoodP p).pow_mem hseed _
  have hlhsCop : Nat.Coprime lhsVal.den p := by
    change Nat.Coprime lhsVal.den p at hlhsGood
    exact hlhsGood
  have hrhsCop : Nat.Coprime rhsVal.den p := by
    change Nat.Coprime rhsVal.den p at hrhsGood
    exact hrhsGood
  let lhs : ContourKit.ReducedRational p := reducedOfP p lhsVal hlhsCop
  let rhs : ContourKit.ReducedRational p := reducedOfP p rhsVal hrhsCop
  have hdetValue :
      ((Matrix.det (towerScaledMatrixGood (p := p) (a := F.a)
        hp10 hunit k r hden) : GoodP p) : ℚ) = lhsVal := by
    rw [towerScaledMatrixGood_det_value]
    rw [towerScaledMatrixQ_eq_eval]
    have hqrat : qRatP p k = (p : ℚ) ^ k := by
      simp [qRatP, Nat.cast_pow]
    rw [hqrat]
    have hsp := scaledPencil_det_source_eval F (4 * p ^ k) (p ^ k)
      (by simp) (by exact pow_ne_zero _ (Fact.out : Nat.Prime p).ne_zero) r
    convert hsp using 1 <;> simp [qRatP, Nat.cast_pow] <;> ring
  have hlhsResidue :
      lhs.residue = residueHomP p
        (Matrix.det (towerScaledMatrixGood (p := p) (a := F.a)
          hp10 hunit k r hden)) := by
    change (reducedOfP p lhsVal hlhsCop).residue = _
    rw [reducedOfP_residue]
    change (lhsVal : ZMod p) = _
    rw [show lhsVal =
        ((Matrix.det (towerScaledMatrixGood (p := p) (a := F.a)
          hp10 hunit k r hden) : GoodP p) : ℚ) by
      exact hdetValue.symm]
    rfl
  have hseedResidue :
      rhs.residue = seed.residue ^ (p ^ k) := by
    change (reducedOfP p rhsVal hrhsCop).residue = _
    rw [reducedOfP_residue]
    change (rhsVal : ZMod p) = _
    rw [show rhsVal =
        (p0SourceEvalQ F 4 ((p ^ k : ℕ) ^ 2 * r)) ^ (p ^ k) by rfl]
    rw [Rat.cast_pow, htransport k r hden]
  refine ⟨lhs, rhs, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · exact hlhsResidue.trans (hdet k r hden) |>.trans hseedResidue.symm
  · intro s hs
    have hsres : s.residue =
        (reducedOfP p (p0SourceEvalQ F 4 ((p ^ k : ℕ) ^ 2 * r))
          hseedCop).residue := by
      apply residue_eq_of_value_eq
      change s.value = p0SourceEvalQ F 4 ((p ^ k : ℕ) ^ 2 * r)
      exact hs
    have hbase :
        (reducedOfP p (p0SourceEvalQ F 4 ((p ^ k : ℕ) ^ 2 * r))
          hseedCop).residue =
          seed.residue := htransport k r hden
    calc
      rhs.residue = seed.residue ^ (p ^ k) := hseedResidue
      _ = (reducedOfP p (p0SourceEvalQ F 4 ((p ^ k : ℕ) ^ 2 * r)) hseedCop).residue ^ (p ^ k) := by
        rw [hbase]
      _ = s.residue ^ (p ^ k) := by rw [hsres]

end
end Li2Lean.P0.PositiveTower

#print axioms Li2Lean.P0.PositiveTower.frobenius_field_of_residue_det
