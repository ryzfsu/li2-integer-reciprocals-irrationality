/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com)
-/

import Li2Lean.B3.VScaledEntryResidue
import Li2Lean.P0.PositiveTower.BlockDeterminant

/-!
# Unit constant coefficient of the scaled signed-V Frobenius polynomial

Unit constant coefficient of the scaled polynomial
(v13 `nonvanishing.tex:247-257).

Revision 2026-10-18.  Changes from the preceding construction:
* the seed step `vSeedResidueMatrix_det_eq` is now the entry-residue theorem
  `vSeedResidueMatrix_det_eq_cast` (honest `Fin 9` transport); the `k = 0`
  specialisation through `vResidueRowPerm (p ^ 0)`, `vSeedResidue_rhs_zero`,
  `vResidueRowPermSign*` and `set_option maxRecDepth` are all removed, so this
  file needs only the pencil-index names provided by this construction;
* no `let`-bound ring homomorphism: `goodEvalZeroResidue` is a top-level
  definition with an `apply` lemma, and every `rfl` compares terms over the same
  index type;
* `residue_ne_zero_of_padic_unit` is reproved from `x.reduced` and
  `padicValNat_dvd_iff` / `padicValInt_dvd_iff` (the r3 name
  `Rat.num_or_den_zero_padicVal` is not a Mathlib lemma).

Integration revision h3-integration-20261018: only the two `padicVal*_dvd_iff`
calls in `residue_ne_zero_of_padic_unit` changed (`p` is now pinned).  It
requires the entry-residue construction (`VScaledEntryResidue`) with
`vSeedResidueMatrix (q p₀ : ℕ) [Fact (Nat.Prime p₀)]` and the pencil-index
(`VPencilIndex`, the release branch, included in the release).

The sign `ε = sign (vResidueRowPerm (p ^ k))` is kept symbolic; only `ε ≠ 0` is
used.  `VActualScaledCoefficientCarrier.coefficientwise_frobenius` (which omits
`ε`, false at p = 11, 23) is NOT used.
-/

namespace Li2Lean.B3

noncomputable section

open scoped BigOperators
open Matrix
open Li2Lean.P0.PositiveTower

variable {p : ℕ} [Fact (Nat.Prime p)]

/-! ## Units of `GoodP p` -/

theorem goodP_unit_of_residue_ne_zero {x : ℚ} (hx : x ∈ GoodP p)
    (hr : (x : ZMod p) ≠ 0) : x ≠ 0 ∧ padicValRat p x = 0 := by
  have hp : Nat.Prime p := Fact.out
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hr (by simp)
  have hnd_den : ¬ p ∣ x.den := hp.coprime_iff_not_dvd.mp (Nat.Coprime.symm hx)
  have hden0 : padicValNat p x.den = 0 := padicValNat.eq_zero_of_not_dvd hnd_den
  have hnd_num : ¬ (p : ℤ) ∣ x.num := by
    intro hdvd
    have hnum_zmod : (x.num : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd x.num p).mpr hdvd
    apply hr
    rw [Rat.cast_def, hnum_zmod, zero_div]
  have hnum0 : padicValInt p x.num = 0 := padicValInt.eq_zero_of_not_dvd hnd_num
  refine ⟨hx0, ?_⟩
  rw [padicValRat_def, hnum0, hden0]
  simp

theorem residue_ne_zero_of_padic_unit {x : ℚ} (hx0 : x ≠ 0)
    (hv : padicValRat p x = 0) : x ∈ GoodP p ∧ (x : ZMod p) ≠ 0 := by
  have hp : Nat.Prime p := Fact.out
  have hnum_ne : x.num ≠ 0 := Rat.num_ne_zero.mpr hx0
  rw [padicValRat_def] at hv
  -- `p` cannot divide the denominator: otherwise it does not divide the
  -- numerator (`x.reduced`), so `v(num) = 0 < 1 ≤ v(den)`.
  have hnd_den : ¬ p ∣ x.den := by
    intro hdvd
    have hnd_abs : ¬ p ∣ x.num.natAbs := by
      intro habs
      have h1 : p ∣ 1 := by
        have h := Nat.dvd_gcd habs hdvd
        rwa [Nat.Coprime.gcd_eq_one x.reduced] at h
      exact hp.not_dvd_one h1
    have hnum0 : padicValInt p x.num = 0 :=
      padicValInt.eq_zero_of_not_dvd (fun h => hnd_abs (Int.natCast_dvd.mp h))
    -- integration fix: the r3 call `padicValNat_dvd_iff 1 x.den` left `p` to be
    -- inferred from a postponed `simpa`; `one_le_padicValNat_of_dvd` fixes it.
    have hden1 : 1 ≤ padicValNat p x.den :=
      one_le_padicValNat_of_dvd (p := p) x.den_nz hdvd
    omega
  have hden0 : padicValNat p x.den = 0 := padicValNat.eq_zero_of_not_dvd hnd_den
  have hnum0 : padicValInt p x.num = 0 := by omega
  have hnd_num : ¬ (p : ℤ) ∣ x.num := by
    intro hdvd
    -- integration fix: pin `p` explicitly (see `hden1`).
    have h := (padicValInt_dvd_iff (p := p) 1 x.num).mp (by rw [pow_one]; exact hdvd)
    rcases h with h | h
    · exact hnum_ne h
    · omega
  have hx_good : x ∈ GoodP p := Nat.Coprime.symm (hp.coprime_iff_not_dvd.mpr hnd_den)
  have hnum_zmod : (x.num : ZMod p) ≠ 0 := by
    intro hz
    exact hnd_num ((ZMod.intCast_zmod_eq_zero_iff_dvd x.num p).mp hz)
  have hden_zmod : (x.den : ZMod p) ≠ 0 := natCast_ne_zero_of_coprime hx_good
  refine ⟨hx_good, ?_⟩
  rw [Rat.cast_def]
  exact div_ne_zero hnum_zmod hden_zmod

/-! ## Reduction of the constant term -/

/-- `P ↦ res(P(0))` on `Polynomial (GoodP p)`. -/
def goodEvalZeroResidue : Polynomial (GoodP p) →+* ZMod p :=
  (residueHomP p).comp (Polynomial.evalRingHom 0)

theorem goodEvalZeroResidue_apply (P : Polynomial (GoodP p)) :
    goodEvalZeroResidue P = residueHomP p (P.eval 0) := by
  simp only [goodEvalZeroResidue, RingHom.comp_apply, Polynomial.coe_evalRingHom]

theorem vFrobeniusScaled_coeff_zero_residue (hp11 : 11 ≤ p) (q k : ℕ) :
    (((V.vFrobeniusScaledPolynomial q p k).coeff 0 : ℚ) : ZMod p) =
      (Equiv.Perm.sign (vResidueRowPerm (p ^ k)) : ZMod p) *
        ((((-(q : ℤ)) : ℤ) : ZMod p) ^ (4 * p ^ k * (p ^ k - 1)) *
          (vSeedResidueMatrix q p).det ^ (p ^ k)) := by
  -- (1) the constant coefficient is the residue of `(det G).eval 0`
  have hcoeff : (((V.vFrobeniusScaledPolynomial q p k).coeff 0 : ℚ) : ZMod p) =
      goodEvalZeroResidue (vScaledPencilGood hp11 q k).det := by
    rw [goodEvalZeroResidue_apply, vFrobeniusScaledPolynomial_eq_map_det_good hp11 q k,
      Polynomial.coeff_map, Polynomial.coeff_zero_eq_eval_zero]
    rfl
  -- (2) entrywise reduction, reindexed to `Fin 9 × Fin (p ^ k)`
  have hsub :
      ((goodEvalZeroResidue (p := p)).mapMatrix (vScaledPencilGood hp11 q k)).submatrix
          (vRowEquiv (p ^ k)) (vColEquiv (p ^ k)) =
        vResidueBlockMatrix (vSeedResidueMatrix q p) (((-(q : ℤ)) : ℤ) : ZMod p) (p ^ k) := by
    ext ⟨A, u⟩ ⟨B, v⟩
    rw [Matrix.submatrix_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
      vResidueBlockMatrix_apply, goodEvalZeroResidue_apply]
    exact vScaledPencilGood_entry_residue hp11 q k A B u v
  -- (3) block determinant and permutation sign
  have hdet_sub := det_submatrix_vRow_vCol (p ^ k)
    ((goodEvalZeroResidue (p := p)).mapMatrix (vScaledPencilGood hp11 q k))
  rw [hsub, det_vResidueBlockMatrix] at hdet_sub
  have hsign_sq :
      (Equiv.Perm.sign (vResidueRowPerm (p ^ k)) : ZMod p) *
        (Equiv.Perm.sign (vResidueRowPerm (p ^ k)) : ZMod p) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
    simp
  rw [hcoeff, RingHom.map_det]
  calc
    ((goodEvalZeroResidue (p := p)).mapMatrix (vScaledPencilGood hp11 q k)).det =
        (Equiv.Perm.sign (vResidueRowPerm (p ^ k)) : ZMod p) *
          ((Equiv.Perm.sign (vResidueRowPerm (p ^ k)) : ZMod p) *
            ((goodEvalZeroResidue (p := p)).mapMatrix (vScaledPencilGood hp11 q k)).det) := by
      rw [← mul_assoc, hsign_sq, one_mul]
    _ = (Equiv.Perm.sign (vResidueRowPerm (p ^ k)) : ZMod p) *
          ((((-(q : ℤ)) : ℤ) : ZMod p) ^ (4 * p ^ k * (p ^ k - 1)) *
            (vSeedResidueMatrix q p).det ^ (p ^ k)) := by
      rw [← hdet_sub]

/-- `k = 0` instance, now a direct corollary of the entry-residue calculation. -/
theorem vSeedResidueMatrix_det_eq (hp11 : 11 ≤ p) (q : ℕ) :
    (vSeedResidueMatrix q p).det =
      (((V.vPolynomial 1 (-(q : ℤ))).coeff 0 : ℚ) : ZMod p) :=
  vSeedResidueMatrix_det_eq_cast hp11 q

theorem vScaledConstantUnit (hp11 : 11 ≤ p) (q : ℕ)
    (hqp : ¬ (p : ℤ) ∣ (q : ℤ))
    (h0 : (V.vPolynomial 1 (-(q : ℤ))).coeff 0 ≠ 0)
    (hu : padicValRat p ((V.vPolynomial 1 (-(q : ℤ))).coeff 0) = 0) (k : ℕ) :
    (V.vFrobeniusScaledPolynomial q p k).coeff 0 ≠ 0 ∧
      padicValRat p ((V.vFrobeniusScaledPolynomial q p k).coeff 0) = 0 := by
  have hseed_res : (((V.vPolynomial 1 (-(q : ℤ))).coeff 0 : ℚ) : ZMod p) ≠ 0 :=
    (residue_ne_zero_of_padic_unit (p := p) h0 hu).2
  have hdet_ne : (vSeedResidueMatrix q p).det ≠ 0 := by
    rw [vSeedResidueMatrix_det_eq hp11 q]
    exact hseed_res
  have hd_ne : (((-(q : ℤ)) : ℤ) : ZMod p) ≠ 0 := by
    intro hz
    have hdvd := (ZMod.intCast_zmod_eq_zero_iff_dvd (-(q : ℤ)) p).mp hz
    exact hqp (dvd_neg.mp hdvd)
  have hsign_sq :
      (Equiv.Perm.sign (vResidueRowPerm (p ^ k)) : ZMod p) *
        (Equiv.Perm.sign (vResidueRowPerm (p ^ k)) : ZMod p) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
    simp
  have hsign_ne : (Equiv.Perm.sign (vResidueRowPerm (p ^ k)) : ZMod p) ≠ 0 :=
    left_ne_zero_of_mul_eq_one hsign_sq
  have hres_ne : (((V.vFrobeniusScaledPolynomial q p k).coeff 0 : ℚ) : ZMod p) ≠ 0 := by
    rw [vFrobeniusScaled_coeff_zero_residue hp11 q k,
      tower_scalar_unit _ hd_ne 4 k, one_mul]
    exact mul_ne_zero hsign_ne (pow_ne_zero (p ^ k) hdet_ne)
  exact goodP_unit_of_residue_ne_zero (vFrobeniusScaled_coeff_good hp11 q k 0) hres_ne

end
end Li2Lean.B3

#print axioms Li2Lean.B3.vFrobeniusScaled_coeff_zero_residue
#print axioms Li2Lean.B3.vScaledConstantUnit
