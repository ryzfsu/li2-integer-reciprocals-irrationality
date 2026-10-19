/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Li2Lean.P0.PositiveTower.FrobeniusFieldPackaging
import Li2Lean.P0.PositiveTower.M4LucasBlockReduction

/-!
# Unconditional GoodP-based Frobenius field packaging for P0

This module removes the unscaled `hgood` assumption from
`FrobeniusFieldPackaging.frobenius_field_of_residue_det` by reading the left
reduced rational directly from the `GoodP p`-valued determinant
`Matrix.det (towerScaledMatrixGood ...)` via `towerScaledMatrixGood_det_value`,
and the right reduced rational from `source_eval_good_public` and
`source_eval_residue_scaled_public`.

It then discharges the determinant-residue hypothesis `hdet` at `M = 4` by
combining `m4_lucas_block_reduction` (`M4LucasBlockReduction.lean`),
`det_of_lucas_block_prime_power` (`BlockDeterminantReduction.lean`), and the
seed determinant bridge at `T = 0`.

Source: v13 `chapters/nonvanishing.tex:200-258`.
-/

namespace Li2Lean.P0.PositiveTower

noncomputable section

open Li2Lean
open Li2Lean.P0
open EntryGoodness
open Matrix

variable {p : ℕ} [Fact (Nat.Prime p)]

/-- Residue transport at M = 4 for sufficiently p-adically small arguments. -/
theorem source_eval_residue_transport_mod_p
    {F : P0Family} {p : ℕ} [Fact (Nat.Prime p)]
    (hp10 : 10 < p)
    (hunit : Nat.Coprime (F.a - 1).natAbs p)
    (k : ℕ) (r : ℚ) (hk : r.den < p ^ k) :
    ((p0SourceEvalQ F 4 ((p ^ k : ℕ) ^ 2 * r) : ℚ) : ZMod p) =
      ((p0SourceEvalQ F 4 0 : ℚ) : ZMod p) := by
  have hcut : 2 * 4 + 4 / 2 < p := by omega
  have hmod := source_eval_residue_scaled_public
    (F := F) (M := 4) (p := p) (by decide) hunit hcut r k hk
  change ((p0SourceEvalQ F 4 (((p ^ k : ℕ) : ℚ) ^ 2 * r) : ℚ) : ZMod p) =
    ((p0SourceEvalQ F 4 0 : ℚ) : ZMod p) at hmod
  simpa only [Nat.cast_pow] using hmod

/-- Residue transport to a seed with the same rational value at zero. -/
theorem source_eval_residue_transport_to_seed
    {F : P0Family} {p : ℕ} [Fact (Nat.Prime p)]
    (hp10 : 10 < p)
    (hunit : Nat.Coprime (F.a - 1).natAbs p)
    (seed : ContourKit.ReducedRational p)
    (hseed_value : seed.value = p0SourceEvalQ F 4 0)
    (k : ℕ) (r : ℚ) (hk : r.den < p ^ k) :
    ((p0SourceEvalQ F 4 ((p ^ k : ℕ) ^ 2 * r) : ℚ) : ZMod p) =
      seed.residue := by
  have hcut : 2 * 4 + 4 / 2 < p := by omega
  have hzero : p0SourceEvalQ F 4 0 ∈ GoodP p :=
    source_eval_good_public (F := F) (M := 4) (p := p)
      (by decide) hunit hcut (GoodP p).zero_mem
  have hzeroCop : Nat.Coprime (p0SourceEvalQ F 4 0).den p := by
    change Nat.Coprime (p0SourceEvalQ F 4 0).den p at hzero
    exact hzero
  have hseed_res : seed.residue = ((p0SourceEvalQ F 4 0 : ℚ) : ZMod p) := by
    have heq : seed.residue =
        (reducedOfP p (p0SourceEvalQ F 4 0) hzeroCop).residue := by
      apply residue_eq_of_value_eq
      change seed.value = p0SourceEvalQ F 4 0
      exact hseed_value
    rw [heq, reducedOfP_residue]
  exact (source_eval_residue_transport_mod_p
    (F := F) (p := p) hp10 hunit k r hk).trans hseed_res.symm

/-- Frobenius packaging from only the determinant residue hypothesis;
no integrality claim is imposed on the unscaled source evaluation. -/
theorem frobenius_field_of_residue_det_unconditional
    {F : P0Family} {M p : ℕ}
    [Fact (Nat.Prime p)]
    (hM : M = 4)
    (hp10 : 10 < p)
    (hunit : Nat.Coprime (F.a - 1).natAbs p)
    (seed : ContourKit.ReducedRational p)
    (hseed_value : seed.value = p0SourceEvalQ F M 0)
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
  have hcut : 2 * 4 + 4 / 2 < p := by omega
  intro r
  refine ⟨r.den, ?_⟩
  intro k hk
  have hden : r.den < p ^ k := by
    exact lt_of_lt_of_le
      (Nat.lt_pow_self (Fact.out : Nat.Prime p).one_lt)
      (Nat.pow_le_pow_right (Fact.out : Nat.Prime p).pos hk)
  have hseed : p0SourceEvalQ F 4 ((p ^ k : ℕ) ^ 2 * r) ∈ GoodP p := by
    have hseed' :
        p0SourceEvalQ F 4 ((((p ^ k : ℕ) : ℚ) ^ 2) * r) ∈ GoodP p :=
      source_eval_good_public (F := F) (M := 4) (p := p)
        (by decide) hunit hcut (powP_sq_mul_rat_den_coprime k r hden)
    simpa only [Nat.cast_pow] using hseed'
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
  have hlhsGood : lhsVal ∈ GoodP p := by
    rw [← hdetValue]
    exact (Matrix.det (towerScaledMatrixGood (p := p) (a := F.a)
      hp10 hunit k r hden)).property
  have hrhsGood : rhsVal ∈ GoodP p := (GoodP p).pow_mem hseed _
  have hlhsCop : Nat.Coprime lhsVal.den p := by
    change Nat.Coprime lhsVal.den p at hlhsGood
    exact hlhsGood
  have hrhsCop : Nat.Coprime rhsVal.den p := by
    change Nat.Coprime rhsVal.den p at hrhsGood
    exact hrhsGood
  let lhs : ContourKit.ReducedRational p := reducedOfP p lhsVal hlhsCop
  let rhs : ContourKit.ReducedRational p := reducedOfP p rhsVal hrhsCop
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
  have htransport_k :
      ((p0SourceEvalQ F 4 ((p ^ k : ℕ) ^ 2 * r) : ℚ) : ZMod p) =
        seed.residue :=
    source_eval_residue_transport_to_seed
      (F := F) (p := p) hp10 hunit seed hseed_value k r hden
  have hseedResidue : rhs.residue = seed.residue ^ (p ^ k) := by
    change (reducedOfP p rhsVal hrhsCop).residue = _
    rw [reducedOfP_residue]
    change (rhsVal : ZMod p) = _
    rw [show rhsVal =
        (p0SourceEvalQ F 4 ((p ^ k : ℕ) ^ 2 * r)) ^ (p ^ k) by rfl]
    rw [Rat.cast_pow, htransport_k]
  refine ⟨lhs, rhs, rfl, rfl, ?_, ?_⟩
  · exact (hlhsResidue.trans (hdet k r hden)).trans hseedResidue.symm
  · intro s hs
    have hsres : s.residue =
        (reducedOfP p (p0SourceEvalQ F 4 ((p ^ k : ℕ) ^ 2 * r))
          hseedCop).residue := by
      apply residue_eq_of_value_eq
      change s.value = p0SourceEvalQ F 4 ((p ^ k : ℕ) ^ 2 * r)
      exact hs
    have hbase :
        (reducedOfP p (p0SourceEvalQ F 4 ((p ^ k : ℕ) ^ 2 * r))
          hseedCop).residue = seed.residue := by
      rw [reducedOfP_residue]
      exact htransport_k
    calc
      rhs.residue = seed.residue ^ (p ^ k) := hseedResidue
      _ = (reducedOfP p (p0SourceEvalQ F 4 ((p ^ k : ℕ) ^ 2 * r))
            hseedCop).residue ^ (p ^ k) := by rw [hbase]
      _ = s.residue ^ (p ^ k) := by rw [hsres]

/-! ## Discharging `hdet` at `M = 4` from `m4_lucas_block_reduction` and the `T = 0` seed determinant bridge -/

private def m4RowIdx (r : Fin (2 * 4)) : ℕ :=
  4 / 4 + (if r.val < 4 then r.val else r.val - 4)

private lemma m4RowIdx_lt (r : Fin (2 * 4)) :
    m4RowIdx r < 2 * 4 := by
  have hr : r.val < 2 * 4 := r.isLt
  unfold m4RowIdx
  split_ifs <;> omega

private lemma m4Entry_bound {p : ℕ} (hp10 : 10 < p)
    (r c : Fin (2 * 4)) :
    max (m4RowIdx r) c.val + 4 / 2 < p := by
  have hi : m4RowIdx r < 2 * 4 := m4RowIdx_lt r
  have hj : c.val < 2 * 4 := c.isLt
  have hmax : max (m4RowIdx r) c.val < 2 * 4 :=
    max_lt_iff.mpr ⟨hi, hj⟩
  omega

private lemma m4_C_good {F : P0Family}
    (hunit : Nat.Coprime (F.a - 1).natAbs p)
    (i j : ℕ) (hbound : max i j + 4 / 2 < p) :
    p0CQ (F.a : ℚ) (4 / 2) i j ∈ GoodP p := by
  have h := EntryGoodness.q_mul_p0CQ_good (p := p) (a := F.a)
    0 (4 / 2) i j (by simpa [qRatP] using hbound)
  simpa [qRatP] using h

private lemma m4_B_good {F : P0Family}
    (hunit : Nat.Coprime (F.a - 1).natAbs p)
    (hp10 : 10 < p)
    (i j : ℕ) (hbound : max i j + 4 / 2 < p) :
    p0BQ (F.a : ℚ) (4 / 2) i j ∈ GoodP p := by
  have hi : i < p := by omega
  have hj : j < p := by omega
  have hg : 4 / 2 < p := by omega
  have h := EntryGoodness.q_sq_mul_p0BQ_good (p := p) (a := F.a) hunit
    0 (4 / 2) i j (by simpa using hg) (by simpa using hi) (by simpa using hj)
  simpa [qRatP] using h

private def m4SeedMatrixGood (F : P0Family)
    (hp10 : 10 < p)
    (hunit : Nat.Coprime (F.a - 1).natAbs p) :
    Matrix (Fin (2 * 4)) (Fin (2 * 4)) (GoodP p) :=
  fun r c =>
    let i := m4RowIdx r
    if hr : r.val < 4 then
      ⟨p0CQ (F.a : ℚ) (4 / 2) i c.val,
        m4_C_good hunit i c.val (m4Entry_bound hp10 r c)⟩
    else
      ⟨p0BQ (F.a : ℚ) (4 / 2) i c.val,
        m4_B_good hunit hp10 i c.val (m4Entry_bound hp10 r c)⟩

private lemma m4SeedMatrixGood_coe_apply (F : P0Family)
    (hp10 : 10 < p)
    (hunit : Nat.Coprime (F.a - 1).natAbs p)
    (r c : Fin (2 * 4)) :
    ((m4SeedMatrixGood (p := p) F hp10 hunit r c : GoodP p) : ℚ) =
      (p0MatrixQ (F.a : ℚ) 4 r c).eval 0 := by
  by_cases hr : r.val < 4 <;>
    simp [m4SeedMatrixGood, m4RowIdx, p0MatrixQ, hr]

private lemma m4SeedMatrixGood_map (F : P0Family)
    (hp10 : 10 < p)
    (hunit : Nat.Coprime (F.a - 1).natAbs p) :
    (GoodP p).subtype.mapMatrix (m4SeedMatrixGood (p := p) F hp10 hunit) =
      (Polynomial.evalRingHom (0 : ℚ)).mapMatrix (p0MatrixQ (F.a : ℚ) 4) := by
  ext r c
  simpa [RingHom.mapMatrix_apply, Matrix.map_apply] using
    m4SeedMatrixGood_coe_apply (p := p) F hp10 hunit r c

private lemma m4SeedMatrixGood_det_coe (F : P0Family)
    (hp10 : 10 < p)
    (hunit : Nat.Coprime (F.a - 1).natAbs p) :
    ((Matrix.det (m4SeedMatrixGood (p := p) F hp10 hunit) : GoodP p) : ℚ) =
      p0SourceEvalQ F 4 0 := by
  change (GoodP p).subtype
      (Matrix.det (m4SeedMatrixGood (p := p) F hp10 hunit)) =
    p0SourceEvalQ F 4 0
  rw [RingHom.map_det (GoodP p).subtype
    (m4SeedMatrixGood (p := p) F hp10 hunit)]
  rw [m4SeedMatrixGood_map (p := p) F hp10 hunit]
  rw [← RingHom.map_det (Polynomial.evalRingHom (0 : ℚ))
    (p0MatrixQ (F.a : ℚ) 4)]
  simp [p0SourceEvalQ, p0CanonicalPolynomial]

private lemma m4SeedMatrixGood_residue_map (F : P0Family)
    (hp10 : 10 < p)
    (hunit : Nat.Coprime (F.a - 1).natAbs p) :
    (residueHomP p).mapMatrix (m4SeedMatrixGood (p := p) F hp10 hunit) =
      m4SeedResidueMatrix F.a p := by
  ext r c
  change (((m4SeedMatrixGood (p := p) F hp10 hunit r c : GoodP p) : ℚ) : ZMod p) =
    m4SourceResidue F.a r c p
  rw [m4SeedMatrixGood_coe_apply]
  unfold m4SourceResidue
  dsimp
  rw [Rat.cast_def, div_eq_mul_inv]

/-- The `M = 4` seed residue matrix determinant equals the `ZMod p` cast of `p0SourceEvalQ F 4 0`. -/
theorem m4SeedResidueMatrix_det_eq_source_eval_zero (F : P0Family)
    (hp10 : 10 < p)
    (hunit : Nat.Coprime (F.a - 1).natAbs p) :
    Matrix.det (m4SeedResidueMatrix F.a p) =
      ((p0SourceEvalQ F 4 0 : ℚ) : ZMod p) := by
  rw [← m4SeedMatrixGood_residue_map (p := p) F hp10 hunit]
  rw [← RingHom.map_det (residueHomP p)
    (m4SeedMatrixGood (p := p) F hp10 hunit)]
  change (((Matrix.det (m4SeedMatrixGood (p := p) F hp10 hunit) : GoodP p) : ℚ) :
    ZMod p) = ((p0SourceEvalQ F 4 0 : ℚ) : ZMod p)
  rw [m4SeedMatrixGood_det_coe (p := p) F hp10 hunit]

/-- Compute `m4SourceResidue` at `(i, j)` from a rational quotient `n / d`
and a modular check `n = r * d (mod p)`.  This theorem must live in this
module because its proof uses the private `m4SeedMatrixGood` lemmas above. -/
theorem m4SourceResidue_eq_of_div (F : P0Family)
    (hp10 : 10 < p)
    (hunit : Nat.Coprime (F.a - 1).natAbs p)
    (i j : Fin (2 * 4)) (n : ℤ) (d r : ℕ)
    (hval : (p0MatrixQ (F.a : ℚ) 4 i j).eval 0 = (n : ℚ) / (d : ℚ))
    (hd : (d : ZMod p) ≠ 0)
    (hmod : (n : ZMod p) = (r : ZMod p) * (d : ZMod p)) :
    m4SourceResidue F.a i j p = (r : ZMod p) := by
  have hxgood : (p0MatrixQ (F.a : ℚ) 4 i j).eval 0 ∈ GoodP p := by
    rw [← m4SeedMatrixGood_coe_apply (p := p) F hp10 hunit i j]
    exact (m4SeedMatrixGood (p := p) F hp10 hunit i j).property
  have hcop : Nat.Coprime ((p0MatrixQ (F.a : ℚ) 4 i j).eval 0).den p := hxgood
  let z₁ : ContourKit.ReducedRational p :=
    reducedOfP p ((p0MatrixQ (F.a : ℚ) 4 i j).eval 0) hcop
  have hdZ : ((d : ℤ) : ZMod p) ≠ 0 := by simpa using hd
  have hd0 : (d : ℤ) ≠ 0 := by
    intro h0
    exact hdZ (by rw [h0, Int.cast_zero])
  let z₂ : ContourKit.ReducedRational p :=
    { value := (n : ℚ) / (d : ℚ)
      numerator := n
      denominator := (d : ℤ)
      denominator_ne_zero := hd0
      denominator_residue_ne_zero := hdZ
      value_eq := by rw [Int.cast_natCast]
      residue := (r : ZMod p)
      residue_eq := by
        rw [Int.cast_natCast, hmod, mul_assoc, mul_inv_cancel₀ hd, mul_one] }
  have heq : z₁.residue = z₂.residue :=
    Li2Lean.P0.PositiveTower.residue_eq_of_value_eq (p := p)
      (by change (p0MatrixQ (F.a : ℚ) 4 i j).eval 0 = (n : ℚ) / (d : ℚ); exact hval)
  exact heq

/-- Discharging `hdet` from `m4_lucas_block_reduction`, `det_of_lucas_block_prime_power`,
and `m4SeedResidueMatrix_det_eq_source_eval_zero`. -/
theorem towerScaledMatrixGood_det_residue_eq_seed_pow
    {F : P0Family}
    (hp10 : 10 < p)
    (hunit : Nat.Coprime (F.a - 1).natAbs p)
    (ha0 : (F.a : ZMod p) ≠ 0)
    (seed : ContourKit.ReducedRational p)
    (hseed_value : seed.value = p0SourceEvalQ F 4 0)
    (k : ℕ) (r : ℚ) (hk : r.den < p ^ k) :
    residueHomP p
        (Matrix.det (towerScaledMatrixGood (p := p) (a := F.a)
          hp10 hunit k r hk)) = seed.residue ^ (p ^ k) := by
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · exfalso
      have hden_pos : 0 < r.den := r.den_pos
      simp at hk
    · exact hpos
  have hreindex :
      Matrix.det (m4TowerScaledMatrixGood (p := p) (a := F.a) hp10 hunit k r hk) =
        Matrix.det (towerScaledMatrixGood (p := p) (a := F.a) hp10 hunit k r hk) := by
    unfold m4TowerScaledMatrixGood
    exact Matrix.det_reindex_self (m4RowEquiv (p := p) k).symm
      (towerScaledMatrixGood (p := p) (a := F.a) hp10 hunit k r hk)
  have hlucas := m4_lucas_block_reduction (p := p) F.a hp10 hunit k r hk hk0
  have hblock := det_of_lucas_block_prime_power (p := p) (M := 4) k
    (m4TowerScaledMatrixGood (p := p) (a := F.a) hp10 hunit k r hk)
    (m4SeedResidueMatrix F.a p) (F.a : ZMod p) ha0 hlucas
  rw [hreindex] at hblock
  have hcut : 2 * 4 + 4 / 2 < p := by omega
  have hzero : p0SourceEvalQ F 4 0 ∈ GoodP p :=
    source_eval_good_public (F := F) (M := 4) (p := p)
      (by decide) hunit hcut (GoodP p).zero_mem
  have hzeroCop : Nat.Coprime (p0SourceEvalQ F 4 0).den p := by
    change Nat.Coprime (p0SourceEvalQ F 4 0).den p at hzero
    exact hzero
  have hseed_res : seed.residue = ((p0SourceEvalQ F 4 0 : ℚ) : ZMod p) := by
    have heq : seed.residue =
        (reducedOfP p (p0SourceEvalQ F 4 0) hzeroCop).residue := by
      apply residue_eq_of_value_eq
      change seed.value = p0SourceEvalQ F 4 0
      exact hseed_value
    rw [heq, reducedOfP_residue]
  rw [hblock, m4SeedResidueMatrix_det_eq_source_eval_zero (p := p) F hp10 hunit,
    hseed_res]

lemma base_sub_one_coprime_of_not_dvd {F : P0Family}
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

lemma base_cast_ne_zero_of_not_dvd {F : P0Family}
    (ha : ¬ (p : ℤ) ∣ F.a * (F.a - 1)) :
    (F.a : ZMod p) ≠ 0 := by
  intro hz
  apply ha
  have hdiv : (p : ℤ) ∣ F.a :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd F.a p).mp hz
  exact dvd_mul_of_dvd_left hdiv (F.a - 1)

/-- Full unconditional Frobenius field at `M = 4` discharging `hdet` via `m4_lucas_block_reduction`
and `m4SeedResidueMatrix_det_eq_source_eval_zero`. -/
theorem frobenius_field_m4_unconditional
    {F : P0Family} {M p : ℕ}
    [Fact (Nat.Prime p)]
    (hM : M = 4)
    (hp10 : 10 < p)
    (ha : ¬ (p : ℤ) ∣ F.a * (F.a - 1))
    (seed : ContourKit.ReducedRational p)
    (hseed_value : seed.value = p0SourceEvalQ F M 0) :
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
  have hunit : Nat.Coprime (F.a - 1).natAbs p :=
    base_sub_one_coprime_of_not_dvd (p := p) ha
  have ha0 : (F.a : ZMod p) ≠ 0 :=
    base_cast_ne_zero_of_not_dvd (p := p) ha
  exact frobenius_field_of_residue_det_unconditional rfl hp10 hunit seed hseed_value
    (fun k r hk => towerScaledMatrixGood_det_residue_eq_seed_pow
      (p := p) hp10 hunit ha0 seed hseed_value k r hk)

end
end Li2Lean.P0.PositiveTower

#print axioms Li2Lean.P0.PositiveTower.source_eval_residue_transport_mod_p
#print axioms Li2Lean.P0.PositiveTower.source_eval_residue_transport_to_seed
#print axioms Li2Lean.P0.PositiveTower.frobenius_field_of_residue_det_unconditional
#print axioms Li2Lean.P0.PositiveTower.m4SeedResidueMatrix_det_eq_source_eval_zero
#print axioms Li2Lean.P0.PositiveTower.towerScaledMatrixGood_det_residue_eq_seed_pow
#print axioms Li2Lean.P0.PositiveTower.frobenius_field_m4_unconditional
