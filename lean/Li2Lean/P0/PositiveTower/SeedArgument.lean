/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/

import Li2Lean.LayerInterfaces
import Li2Lean.P0.PositiveTower.LocalResidue
import Li2Lean.P0.PositiveTower.EntryGoodness
import Li2Lean.P0.PositiveTower.PencilEvaluation

/-!
# Generic P0 seed argument

The source polynomial at a level divisible by four has coefficients in the
prime-local rational ring.  Consequently a prime-square scaled rational point
has the same residue as the zero point once its denominator is below the prime
power.  This is the general `(p, a, M)` form of the fixed `a = 2`, `M = 32`,
`p = 83` seed argument.
-/

namespace Li2Lean.P0.PositiveTower

noncomputable section

open Li2Lean
open EntryGoodness

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

private lemma base_sub_one_coprime {F : P0Family}
    (ha : ¬ (p : ℤ) ∣ F.a * (F.a - 1)) :
    Nat.Coprime (F.a - 1).natAbs p := by
  apply Nat.Coprime.symm
  apply (Fact.out : Nat.Prime p).coprime_iff_not_dvd.2
  intro hdiv
  apply ha
  have hdiv_int : (p : ℤ) ∣ F.a - 1 := by
    apply Int.dvd_natAbs.mp
    exact_mod_cast hdiv
  exact dvd_mul_of_dvd_right hdiv_int F.a

private def sourceRowIndex (M : ℕ) (r : Fin (2 * M)) : ℕ :=
  M / 4 + (if r.val < M then r.val else r.val - M)

private lemma sourceRowIndex_lt_two_mul (M : ℕ) (r : Fin (2 * M)) :
    sourceRowIndex M r < 2 * M := by
  have hr : r.val < 2 * M := r.isLt
  have hdiv : M / 4 ≤ M := Nat.div_le_self M 4
  unfold sourceRowIndex
  split_ifs <;> omega

private lemma sourceEntry_bound {M p : ℕ}
    (hcut : 2 * M + M / 2 < p)
    (r c : Fin (2 * M)) :
    max (sourceRowIndex M r) c.val + M / 2 < p := by
  have hi : sourceRowIndex M r < 2 * M := sourceRowIndex_lt_two_mul M r
  have hj : c.val < 2 * M := c.isLt
  have hmax : max (sourceRowIndex M r) c.val < 2 * M :=
    max_lt_iff.mpr ⟨hi, hj⟩
  omega

private lemma source_C_good {F : P0Family} {M : ℕ}
    (hunit : Nat.Coprime (F.a - 1).natAbs p)
    (hcut : 2 * M + M / 2 < p)
    (i j : ℕ) (hbound : max i j + M / 2 < p) :
    p0CQ (F.a : ℚ) (M / 2) i j ∈ GoodP p := by
  have h := q_mul_p0CQ_good (p := p) (a := F.a)
    0 (M / 2) i j (by simpa [qRatP] using hbound)
  simpa [qRatP] using h

private lemma source_B_good {F : P0Family} {M : ℕ}
    (hunit : Nat.Coprime (F.a - 1).natAbs p)
    (hcut : 2 * M + M / 2 < p)
    (i j : ℕ) (hbound : max i j + M / 2 < p) :
    p0BQ (F.a : ℚ) (M / 2) i j ∈ GoodP p := by
  have hi : i < p := by omega
  have hj : j < p := by omega
  have hg : M / 2 < p := by omega
  have h := q_sq_mul_p0BQ_good (p := p) (a := F.a) hunit
    0 (M / 2) i j (by simpa using hg) (by simpa using hi) (by simpa using hj)
  simpa [qRatP] using h

private lemma source_A_good {F : P0Family} {M : ℕ}
    (i j : ℕ) : p0AQ (F.a : ℚ) (M / 2) i j ∈ GoodP p :=
  p0AQ_good (p := p) (a := F.a) (M / 2) i j

private def sourceMatrixGood {F : P0Family} (M : ℕ)
    (hunit : Nat.Coprime (F.a - 1).natAbs p)
    (hcut : 2 * M + M / 2 < p) :
    Matrix (Fin (2 * M)) (Fin (2 * M)) (Polynomial (GoodP p)) :=
  fun r c =>
    let i := sourceRowIndex M r
    if hr : r.val < M then
      Polynomial.C ⟨p0CQ (F.a : ℚ) (M / 2) i c.val,
        source_C_good hunit hcut i c.val (sourceEntry_bound hcut r c)⟩
    else
      Polynomial.C ⟨p0BQ (F.a : ℚ) (M / 2) i c.val,
        source_B_good hunit hcut i c.val (sourceEntry_bound hcut r c)⟩ -
        Polynomial.X * Polynomial.C ⟨p0AQ (F.a : ℚ) (M / 2) i c.val,
          source_A_good i c.val⟩

private theorem sourceMatrixGood_map {F : P0Family} {M : ℕ}
    (hunit : Nat.Coprime (F.a - 1).natAbs p)
    (hcut : 2 * M + M / 2 < p) :
    (Polynomial.mapRingHom (GoodP p).subtype).mapMatrix
        (sourceMatrixGood M hunit hcut) = p0MatrixQ (F.a : ℚ) M := by
  ext r c
  by_cases hr : r.val < M <;>
    simp [sourceMatrixGood, sourceRowIndex, p0MatrixQ, hr]

private def sourcePolynomialGood {F : P0Family} {M : ℕ}
    (hunit : Nat.Coprime (F.a - 1).natAbs p)
    (hcut : 2 * M + M / 2 < p) : Polynomial (GoodP p) :=
  Matrix.det (sourceMatrixGood M hunit hcut)

private theorem sourcePolynomialGood_map {F : P0Family} {M : ℕ}
    (hM : 4 ∣ M)
    (hunit : Nat.Coprime (F.a - 1).natAbs p)
    (hcut : 2 * M + M / 2 < p) :
    Polynomial.mapRingHom (GoodP p).subtype
        (sourcePolynomialGood (p := p) (M := M) hunit hcut) =
      p0CanonicalPolynomial F.a M := by
  calc
    Polynomial.mapRingHom (GoodP p).subtype
          (sourcePolynomialGood (p := p) (M := M) hunit hcut) =
        Matrix.det ((Polynomial.mapRingHom (GoodP p).subtype).mapMatrix
          (sourceMatrixGood M hunit hcut)) :=
      RingHom.map_det _ _
    _ = (p0MatrixQ (F.a : ℚ) M).det := by
      rw [sourceMatrixGood_map hunit hcut]
    _ = p0CanonicalPolynomial F.a M := by
      simp [p0CanonicalPolynomial, hM]

private theorem source_eval_good {F : P0Family} {M : ℕ}
    (hM : 4 ∣ M)
    (hunit : Nat.Coprime (F.a - 1).natAbs p)
    (hcut : 2 * M + M / 2 < p)
    {x : ℚ} (hx : x ∈ GoodP p) :
    p0SourceEvalQ F M x ∈ GoodP p := by
  let P := sourcePolynomialGood (p := p) (M := M) hunit hcut
  let xg : GoodP p := ⟨x, hx⟩
  have hEval : p0SourceEvalQ F M x =
      ((P.eval xg : GoodP p) : ℚ) := by
    change (p0CanonicalPolynomial F.a M).eval x = _
    rw [← sourcePolynomialGood_map hM hunit hcut]
    simpa [P, xg] using
      (Polynomial.eval_map_apply (p := P) (GoodP p).subtype xg)
  change Nat.Coprime (p0SourceEvalQ F M x).den p
  rw [hEval]
  exact (P.eval xg).property

private theorem source_eval_residue_scaled {F : P0Family} {M : ℕ}
    (hM : 4 ∣ M)
    (hunit : Nat.Coprime (F.a - 1).natAbs p)
    (hcut : 2 * M + M / 2 < p)
    (r : ℚ) (k : ℕ) (hbound : r.den < p ^ k) :
    residueHomP p
        ⟨p0SourceEvalQ F M (((p ^ k : ℕ) : ℚ) ^ 2 * r),
          source_eval_good hM hunit hcut
            (powP_sq_mul_rat_den_coprime k r hbound)⟩ =
      residueHomP p
        ⟨p0SourceEvalQ F M 0,
          source_eval_good hM hunit hcut (GoodP p).zero_mem⟩ := by
  let P := sourcePolynomialGood (p := p) (M := M) hunit hcut
  let x : ℚ := ((p ^ k : ℕ) : ℚ) ^ 2 * r
  let xg : GoodP p :=
    ⟨x, powP_sq_mul_rat_den_coprime k r hbound⟩
  let zg : GoodP p := ⟨0, (GoodP p).zero_mem⟩
  have hxzero : residueHomP p xg = 0 := by
    change (x : ZMod p) = 0
    exact powP_sq_mul_rat_cast_eq_zero k r hbound
  have hzzero : residueHomP p zg = 0 := by
    change ((0 : ℚ) : ZMod p) = 0
    simp
  have hpoly : residueHomP p (P.eval xg) =
      residueHomP p (P.eval zg) := by
    calc
      residueHomP p (P.eval xg) =
          (P.map (residueHomP p)).eval (residueHomP p xg) :=
        (Polynomial.eval_map_apply (p := P) (residueHomP p) xg).symm
      _ = (P.map (residueHomP p)).eval 0 := by rw [hxzero]
      _ = (P.map (residueHomP p)).eval (residueHomP p zg) := by
        rw [hzzero]
      _ = residueHomP p (P.eval zg) :=
        Polynomial.eval_map_apply (p := P) (residueHomP p) zg
  have hxEval : p0SourceEvalQ F M x =
      ((P.eval xg : GoodP p) : ℚ) := by
    change (p0CanonicalPolynomial F.a M).eval x = _
    rw [← sourcePolynomialGood_map hM hunit hcut]
    simpa [P, xg] using
      (Polynomial.eval_map_apply (p := P) (GoodP p).subtype xg)
  have hzEval : p0SourceEvalQ F M 0 =
      ((P.eval zg : GoodP p) : ℚ) := by
    change (p0CanonicalPolynomial F.a M).eval 0 = _
    rw [← sourcePolynomialGood_map hM hunit hcut]
    simpa [P, zg] using
      (Polynomial.eval_map_apply (p := P) (GoodP p).subtype zg)
  change ((p0SourceEvalQ F M x : ℚ) : ZMod p) =
    ((p0SourceEvalQ F M 0 : ℚ) : ZMod p)
  rw [hxEval, hzEval]
  exact hpoly

/-- The generic prime/base/level seed argument for the P0 tower.

The cutoff is deliberately `k₀ = r.den`: the source matrix is already
`p`-integral, while `powP_sq_mul_rat_den_coprime` absorbs the only remaining
denominator. -/
theorem seed_argument_of_seed_value {F : P0Family} {M p : ℕ}
    [hp : Fact (Nat.Prime p)]
    (hM : 4 ∣ M)
    (hp_cutoff : 2 * M + M / 2 < p)
    (ha : ¬ (p : ℤ) ∣ F.a * (F.a - 1))
    (seed : ContourKit.ReducedRational p)
    (hseed_value : seed.value = p0SourceEvalQ F M 0) :
    ∀ r : ℚ, ∃ k₀, ∀ k, k₀ ≤ k →
      ∃ s : ContourKit.ReducedRational p,
        s.value = p0SourceEvalQ F M ((p ^ k : ℕ) ^ 2 * r) ∧
        s.residue = seed.residue := by
  have hunit : Nat.Coprime (F.a - 1).natAbs p :=
    base_sub_one_coprime ha
  intro r
  refine ⟨r.den, ?_⟩
  intro k hdk
  have hbound : r.den < p ^ k := by
    exact lt_of_lt_of_le
      (Nat.lt_pow_self (Fact.out : Nat.Prime p).one_lt)
      (Nat.pow_le_pow_right (Fact.out : Nat.Prime p).pos hdk)
  let x : ℚ := ((p ^ k : ℕ) : ℚ) ^ 2 * r
  have hxgood : x ∈ GoodP p := by
    change Nat.Coprime x.den p
    simpa [x] using (powP_sq_mul_rat_den_coprime k r hbound)
  have hsource : p0SourceEvalQ F M x ∈ GoodP p :=
    source_eval_good hM hunit hp_cutoff hxgood
  have hzero : p0SourceEvalQ F M 0 ∈ GoodP p :=
    source_eval_good hM hunit hp_cutoff (GoodP p).zero_mem
  change Nat.Coprime (p0SourceEvalQ F M x).den p at hsource
  change Nat.Coprime (p0SourceEvalQ F M 0).den p at hzero
  let s := reducedOfP p (p0SourceEvalQ F M x) hsource
  let s₀ := reducedOfP p (p0SourceEvalQ F M 0) hzero
  refine ⟨s, ?_, ?_⟩
  · change p0SourceEvalQ F M x =
      p0SourceEvalQ F M ((p ^ k : ℕ) ^ 2 * r)
    congr 1
  · have hres : s.residue = s₀.residue := by
      change (reducedOfP p (p0SourceEvalQ F M x) hsource).residue =
        (reducedOfP p (p0SourceEvalQ F M 0) hzero).residue
      rw [reducedOfP_residue, reducedOfP_residue]
      have hmod := source_eval_residue_scaled hM hunit hp_cutoff r k hbound
      change ((p0SourceEvalQ F M (((p ^ k : ℕ) : ℚ) ^ 2 * r) : ℚ) :
        ZMod p) = ((p0SourceEvalQ F M 0 : ℚ) : ZMod p) at hmod
      simpa [x] using hmod
    have hseed : seed.residue = s₀.residue := by
      apply residue_eq_of_value_eq
      simpa [s₀, reducedOfP] using hseed_value
    exact hres.trans hseed.symm

/-! Public wrappers for the prime-local source evaluation facts. -/

theorem source_eval_good_public {F : P0Family} {M : ℕ}
    (hM : 4 ∣ M)
    (hunit : Nat.Coprime (F.a - 1).natAbs p)
    (hcut : 2 * M + M / 2 < p)
    {x : ℚ} (hx : x ∈ GoodP p) :
    p0SourceEvalQ F M x ∈ GoodP p :=
  source_eval_good hM hunit hcut hx

theorem source_eval_residue_scaled_public {F : P0Family} {M : ℕ}
    (hM : 4 ∣ M)
    (hunit : Nat.Coprime (F.a - 1).natAbs p)
    (hcut : 2 * M + M / 2 < p)
    (r : ℚ) (k : ℕ) (hbound : r.den < p ^ k) :
    residueHomP p
        ⟨p0SourceEvalQ F M (((p ^ k : ℕ) : ℚ) ^ 2 * r),
          source_eval_good hM hunit hcut
            (powP_sq_mul_rat_den_coprime k r hbound)⟩ =
      residueHomP p
        ⟨p0SourceEvalQ F M 0,
          source_eval_good hM hunit hcut (GoodP p).zero_mem⟩ :=
  source_eval_residue_scaled hM hunit hcut r k hbound

theorem source_eval_residue_to_seed_public {F : P0Family} {M p : ℕ}
    [hp : Fact (Nat.Prime p)]
    (hM : 4 ∣ M)
    (hunit : Nat.Coprime (F.a - 1).natAbs p)
    (hcut : 2 * M + M / 2 < p)
    (seed : ContourKit.ReducedRational p)
    (hseed_residue : seed.residue =
      ((p0SourceEvalQ F M 0 : ℚ) : ZMod p))
    (r : ℚ) (k : ℕ) (hbound : r.den < p ^ k) :
    ((p0SourceEvalQ F M (((p ^ k : ℕ) : ℚ) ^ 2 * r) : ℚ) : ZMod p) =
      seed.residue := by
  have hmod := source_eval_residue_scaled_public hM hunit hcut r k hbound
  change ((p0SourceEvalQ F M (((p ^ k : ℕ) : ℚ) ^ 2 * r) : ℚ) : ZMod p) =
      ((p0SourceEvalQ F M 0 : ℚ) : ZMod p) at hmod
  exact hmod.trans hseed_residue.symm

end
end Li2Lean.P0.PositiveTower
