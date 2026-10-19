/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B3.VScaledPencilGood
import Li2Lean.B3.VPencilIndex

/-!
# Entry residues of the scaled signed-V pencil at `X = 0`

Seed entry residues of the scaled pencil at `X = 0`
(v13 `nonvanishing.tex:221-246).

Revision 2026-10-18.
Revision h3-laneB-kernel-20261018 variant A: kernel firewall for the seed
determinant block (abstract transport lemmas, term-mode instantiation).
The seed matrix `Matrix (Fin 9) (Fin 9) _` is related to
`V.vSourceMatrix 1 a : Matrix (Fin (V.vMatrixSize 1)) _ _` by definitional
unfolding.  Any `rfl`/`rw` that crosses the two index types forces the kernel to
compare two `Matrix.det` terms with different `Fintype`/`DecidableEq` instances
(kernel deep recursion in `vSeedMatrixGood_det_coe` and in the determinant
transport).  This file never identifies the two index types:

* `vSeedEquiv : Fin 9 ≃ Fin (V.vMatrixSize 1)` is `finCongr` of a propositional
  size equation;
* the seed matrix is `(V.vSourceMatrix 1 a).submatrix vSeedEquiv vSeedEquiv`
  evaluated at `0`, an honest `Fin 9` matrix;
* its determinant is moved to `V.vPolynomial 1 a` only by
  `Matrix.det_submatrix_equiv_self` and `RingHom.map_det`;
* every reduction to `ZMod p` goes through the `GoodP p` lift and
  `residueHomP p`; no rational is cast into `ZMod p` without a `GoodP` proof
  in the determinant step.

The scaled-entry leaves and the unified entry theorem are unchanged from the
the release copy, except for the seed `apply`
lemmas and the `eval`/`map` bridge in `vScaledPencilGood_entry_residue`.
-/

namespace Li2Lean.B3

noncomputable section

open scoped BigOperators
open Matrix
open Li2Lean.P0.ScaledLucas
open Li2Lean.P0.PositiveTower
open Li2Lean.P0.PositiveTower.EntryGoodness

attribute [local irreducible] Matrix.det

/-! ## Honest `Fin 9` seed index -/

/-- `vMatrixSize 1 = 9` as a propositional equation (never used by `rfl` on
matrices). -/
theorem vSeedSize_eq : V.vMatrixSize 1 = 9 := by
  simp [V.vMatrixSize, V.vM, V.vS]

/-- The seed reindexing `Fin 9 ≃ Fin (V.vMatrixSize 1)`. -/
def vSeedEquiv : Fin 9 ≃ Fin (V.vMatrixSize 1) :=
  finCongr vSeedSize_eq.symm

@[simp]
theorem vSeedEquiv_val (A : Fin 9) : (vSeedEquiv A).val = A.val := rfl
  -- Verified certificate computation.
  -- `by simp [vSeedEquiv]` (`finCongr_apply`, `Fin.coe_cast`).

theorem vSeed_val_lt (r : Fin (V.vMatrixSize 1)) : r.val < 9 := by
  have h := r.isLt
  simp only [V.vMatrixSize, V.vM, V.vS] at h
  omega

/-! ## Seed entries at `T = 0`, stated on `Fin (V.vMatrixSize 1)` -/

theorem vSource1_eval0_C (q : ℕ) (r c : Fin (V.vMatrixSize 1)) (hr : r.val < 4) :
    (V.vSourceMatrix 1 (-(q : ℤ)) r c).eval 0 =
      V.vCEntry (-(q : ℤ)) (r.val + 2) (c.val + 1) := by
  have hr' : r.val < V.vM 1 := by simp only [V.vM]; omega
  have hi : V.vIIndexNat 1 r.val = r.val + 2 := by
    simp only [V.vIIndexNat]; omega
  have hj : V.vJIndex 1 c = c.val + 1 := by
    simp only [V.vJIndex]; omega
  simp only [V.vSourceMatrix, hr', ↓reduceIte, Polynomial.eval_C, hi, hj]

theorem vSource1_eval0_B (q : ℕ) (r c : Fin (V.vMatrixSize 1))
    (hr1 : ¬ r.val < 4) (hr2 : r.val < 8) :
    (V.vSourceMatrix 1 (-(q : ℤ)) r c).eval 0 =
      V.vBEntry (-(q : ℤ)) (r.val - 2) (c.val + 1) := by
  have hr1' : ¬ r.val < V.vM 1 := by simp only [V.vM]; omega
  have hr2' : r.val < 2 * V.vM 1 := by simp only [V.vM]; omega
  have hi : 2 * 1 + (r.val - V.vM 1) = r.val - 2 := by
    simp only [V.vM]; omega
  have hj : V.vJIndex 1 c = c.val + 1 := by
    simp only [V.vJIndex]; omega
  simp only [V.vSourceMatrix, hr1', hr2', ↓reduceIte, Polynomial.eval_sub,
    Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X, zero_mul, sub_zero,
    hi, hj]
  -- Verified certificate computation.
  -- to `hi`'s LHS (`2 + (r.val - V.vM 1)`).

theorem vSource1_eval0_V (q : ℕ) (r c : Fin (V.vMatrixSize 1)) (hr2 : ¬ r.val < 8) :
    (V.vSourceMatrix 1 (-(q : ℤ)) r c).eval 0 = V.vVEntry (c.val + 1) 1 := by
  have h9 := vSeed_val_lt r
  have hr1' : ¬ r.val < V.vM 1 := by simp only [V.vM]; omega
  have hr2' : ¬ r.val < 2 * V.vM 1 := by simp only [V.vM]; omega
  have hell : 1 + (r.val - 2 * V.vM 1) = 1 := by simp only [V.vM]; omega
  have hj : V.vJIndex 1 c = c.val + 1 := by
    simp only [V.vJIndex]; omega
  simp only [V.vSourceMatrix, hr1', hr2', ↓reduceIte, Polynomial.eval_C, hell, hj]

/-! ## Goodness of seed-level entries (`Q = 1`, i.e. `k = 0`) -/

variable {p : ℕ} [Fact (Nat.Prime p)]

@[simp]
theorem residueHomP_mk (x : ℚ) (hx : x ∈ GoodP p) :
    residueHomP p ⟨x, hx⟩ = (x : ZMod p) := rfl

theorem vMomentT_seed_good (a : ℤ) {B : ℕ} (hB : B < p) :
    V.vMomentT a B ∈ GoodP p := by
  simpa [qRatP] using q_mul_vMomentT_good (p := p) a 0 B (by simpa using hB)

theorem vMomentB_seed_good (a : ℤ) {B : ℕ} (hB : B < p) :
    V.vMomentB a B ∈ GoodP p := by
  simpa [qRatP] using q_sq_mul_vMomentB_good (p := p) a 0 B (by simpa using hB)

theorem vCEntry_seed_good (a : ℤ) {i₀ j₀ : ℕ} (hi₀ : i₀ < p) (hj₀ : j₀ < p) :
    V.vCEntry a i₀ j₀ ∈ GoodP p := by
  simpa [qRatP] using
    q_mul_vCEntry_good (p := p) a 0 i₀ j₀ (by simpa using max_lt hi₀ hj₀)

theorem vBEntry_seed_good (a : ℤ) {i₀ j₀ : ℕ} (hi₀ : i₀ < p) (hj₀ : j₀ < p) :
    V.vBEntry a i₀ j₀ ∈ GoodP p := by
  simpa [qRatP] using
    q_sq_mul_vBEntry_good (p := p) a 0 i₀ j₀ (by simpa using max_lt hi₀ hj₀)

theorem vVEntry_seed_good {j₀ : ℕ} (hj₀ : j₀ + 1 < p) :
    V.vVEntry j₀ 1 ∈ GoodP p := by
  simpa [qRatP] using
    q_mul_vVEntry_good (p := p) 0 j₀ 1 (by omega) (by simpa using hj₀)

theorem vSource1_eval0_good (hp11 : 11 ≤ p) (q : ℕ) (r c : Fin (V.vMatrixSize 1)) :
    (V.vSourceMatrix 1 (-(q : ℤ)) r c).eval 0 ∈ GoodP p := by
  have hr9 := vSeed_val_lt r
  have hc9 := vSeed_val_lt c
  by_cases h1 : r.val < 4
  · rw [vSource1_eval0_C q r c h1]
    exact vCEntry_seed_good _ (by omega) (by omega)
  · by_cases h2 : r.val < 8
    · rw [vSource1_eval0_B q r c h1 h2]
      exact vBEntry_seed_good _ (by omega) (by omega)
    · rw [vSource1_eval0_V q r c h2]
      exact vVEntry_seed_good (by omega)

/-! ## The `Fin 9` seed matrix, its determinant, and its `GoodP` lift

Kernel firewall (revision h3-laneB-kernel-20261018, variant A).

The index type `Fin 9` is closed, so `Finset.univ : Finset (Equiv.Perm (Fin 9))`
is a closed term.  Whenever the kernel has to decide a non-syntactic
definitional equality whose sides contain the concrete seed determinant (for
instance `evalRingHom 0 X ≡ eval 0 X`, `residueHomP p ⟨X, h⟩ ≡ (X : ZMod p)`,
or an instance-path mismatch under `Matrix.det`), lazy delta reduction may
unfold `Polynomial.eval₂`/`Rat.cast` into a match on the value `X` and then
whnf `X`, i.e. expand the `9!`-term Leibniz sum.  That nested sum is the
kernel deep recursion.  At the variable size `V.vMatrixSize (p ^ k)` the same
unfolding is stuck at once, which is why the master `rfl` glue works there.

Hence: every transport step below is proved once over an arbitrary index type
and an arbitrary matrix (all unfolding is stuck on free variables), and each
concrete seed theorem is a single term-mode application whose inferred type is
the stated type up to beta reduction.  No `rw`, `simp` or `rfl` touches a
concrete determinant. -/

section SeedFirewall

/-- Abstract `eval 0` / reindex transport of a determinant. -/
theorem det_eval_zero_reindex {n ι : Type*} [Fintype n] [DecidableEq n]
    [Fintype ι] [DecidableEq ι] (e : n ≃ ι) (M : Matrix ι ι (Polynomial ℚ))
    (P : Polynomial ℚ) (hP : P = M.det) (S : Matrix n n ℚ)
    (hS : ∀ A B, S A B = (M (e A) (e B)).eval 0) :
    S.det = P.coeff 0 := by
  subst hP
  have hSmap : S = (Polynomial.evalRingHom (0 : ℚ)).mapMatrix (M.submatrix e e) := by
    ext A B
    rw [hS A B]
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.submatrix_apply,
      Polynomial.coe_evalRingHom]
  rw [hSmap, ← RingHom.map_det, Matrix.det_submatrix_equiv_self e M,
    Polynomial.coe_evalRingHom, Polynomial.coeff_zero_eq_eval_zero]

/-- Abstract `GoodP p` lift of a determinant. -/
theorem goodP_det_coe_of_apply {n : Type*} [Fintype n] [DecidableEq n]
    (N : Matrix n n (GoodP p)) (S : Matrix n n ℚ)
    (hN : ∀ A B, ((N A B : GoodP p) : ℚ) = S A B) :
    ((N.det : GoodP p) : ℚ) = S.det := by
  have hmap : (GoodP p).subtype.mapMatrix N = S := by
    ext A B
    exact hN A B
  have h := RingHom.map_det (GoodP p).subtype N
  rw [hmap] at h
  exact h
  -- Verified certificate computation.
  -- `simpa only [Subring.coe_subtype] using h`.

/-- Membership transported along a coercion equation (abstract). -/
theorem goodP_mem_of_coe_eq (x : GoodP p) (c : ℚ) (h : (x : ℚ) = c) :
    c ∈ GoodP p := by
  rw [← h]
  exact x.2

/-- Abstract residue of a `GoodP p` determinant. -/
theorem residue_det_of_good {n : Type*} [Fintype n] [DecidableEq n]
    (N : Matrix n n (GoodP p)) (R : Matrix n n (ZMod p))
    (hR : ∀ A B, R A B = residueHomP p (N A B))
    (c : ℚ) (hc : c ∈ GoodP p) (hN : ((N.det : GoodP p) : ℚ) = c) :
    R.det = residueHomP p ⟨c, hc⟩ := by
  have hmap : R = (residueHomP p).mapMatrix N := by
    ext A B
    exact hR A B
  have hGood : N.det = ⟨c, hc⟩ := Subtype.ext hN
  rw [hmap, ← RingHom.map_det, hGood]

/-- Abstract rational-cast form of `residue_det_of_good`. -/
theorem residue_det_cast_of_good {n : Type*} [Fintype n] [DecidableEq n]
    (N : Matrix n n (GoodP p)) (R : Matrix n n (ZMod p))
    (hR : ∀ A B, R A B = residueHomP p (N A B))
    (c : ℚ) (hc : c ∈ GoodP p) (hN : ((N.det : GoodP p) : ℚ) = c) :
    R.det = ((c : ℚ) : ZMod p) :=
  (residue_det_of_good N R hR c hc hN).trans (residueHomP_mk c hc)

end SeedFirewall

/-- The seed matrix at `T = 0`, reindexed honestly to `Fin 9`. -/
def vSeedSourceMatrix9 (q : ℕ) : Matrix (Fin 9) (Fin 9) ℚ :=
  fun A B => (V.vSourceMatrix 1 (-(q : ℤ)) (vSeedEquiv A) (vSeedEquiv B)).eval 0

theorem vSeedSourceMatrix9_apply (q : ℕ) (A B : Fin 9) :
    vSeedSourceMatrix9 q A B =
      (V.vSourceMatrix 1 (-(q : ℤ)) (vSeedEquiv A) (vSeedEquiv B)).eval 0 := rfl

theorem vSeedSourceMatrix9_eq_map (q : ℕ) :
    vSeedSourceMatrix9 q =
      (Polynomial.evalRingHom (0 : ℚ)).mapMatrix
        ((V.vSourceMatrix 1 (-(q : ℤ))).submatrix vSeedEquiv vSeedEquiv) := by
  ext A B
  simp only [vSeedSourceMatrix9, RingHom.mapMatrix_apply, Matrix.map_apply,
    Matrix.submatrix_apply, Polynomial.coe_evalRingHom]

/-- Seed determinant: one application of `det_eval_zero_reindex`; the inferred
type is the stated type (no delta under `Matrix.det`). -/
theorem vSeedSourceMatrix9_det (q : ℕ) :
    (vSeedSourceMatrix9 q).det = (V.vPolynomial 1 (-(q : ℤ))).coeff 0 :=
  det_eval_zero_reindex vSeedEquiv (V.vSourceMatrix 1 (-(q : ℤ)))
    (V.vPolynomial 1 (-(q : ℤ))) (V.vPolynomial.eq_1 1 (-(q : ℤ)))
    (vSeedSourceMatrix9 q) (vSeedSourceMatrix9_apply q)
  -- Verified certificate computation.
  -- `V.vPolynomial n a = (V.vSourceMatrix n a).det`; alternatives in order:
  -- `V.vPolynomial.eq_def 1 (-(q : ℤ))`, `(rfl : V.vPolynomial 1 _ = _)`.

/-- `GoodP p`-valued `9 × 9` seed matrix at `X = 0` (`Q = 1`). -/
def vSeedMatrixGood (hp11 : 11 ≤ p) (q : ℕ) : Matrix (Fin 9) (Fin 9) (GoodP p) :=
  fun A B => ⟨vSeedSourceMatrix9 q A B, vSource1_eval0_good hp11 q _ _⟩

theorem vSeedMatrixGood_coe_apply (hp11 : 11 ≤ p) (q : ℕ) (A B : Fin 9) :
    ((vSeedMatrixGood hp11 q A B : GoodP p) : ℚ) = vSeedSourceMatrix9 q A B := rfl

theorem vSeedMatrixGood_map (hp11 : 11 ≤ p) (q : ℕ) :
    (GoodP p).subtype.mapMatrix (vSeedMatrixGood hp11 q) = vSeedSourceMatrix9 q := by
  ext A B
  rfl

theorem vSeedMatrixGood_det_coe (hp11 : 11 ≤ p) (q : ℕ) :
    (((vSeedMatrixGood hp11 q).det : GoodP p) : ℚ) =
      (V.vPolynomial 1 (-(q : ℤ))).coeff 0 :=
  Eq.trans
    (goodP_det_coe_of_apply (vSeedMatrixGood hp11 q) (vSeedSourceMatrix9 q)
      (vSeedMatrixGood_coe_apply hp11 q))
    (vSeedSourceMatrix9_det q)

theorem vSeedConstant_good (hp11 : 11 ≤ p) (q : ℕ) :
    (V.vPolynomial 1 (-(q : ℤ))).coeff 0 ∈ GoodP p :=
  goodP_mem_of_coe_eq _ _ (vSeedMatrixGood_det_coe hp11 q)

/-! ## The seed residue matrix -/

/-- Seed residue matrix.  The skeleton signature `(q p : ℕ)` is kept as the
call shape `vSeedResidueMatrix q p`; the primality instance is an explicit
instance binder.  The binder is named `p₀` to avoid shadowing the section
variable. -/
def vSeedResidueMatrix (q p₀ : ℕ) [Fact (Nat.Prime p₀)] :
    Matrix (Fin 9) (Fin 9) (ZMod p₀) :=
  fun A B => ((vSeedSourceMatrix9 q A B : ℚ) : ZMod p₀)

theorem vSeedResidueMatrix_eq_map_good (hp11 : 11 ≤ p) (q : ℕ) :
    vSeedResidueMatrix q p = (residueHomP p).mapMatrix (vSeedMatrixGood hp11 q) := by
  ext A B
  rfl

theorem vSeedResidueMatrix_apply (hp11 : 11 ≤ p) (q : ℕ) (A B : Fin 9) :
    vSeedResidueMatrix q p A B = residueHomP p (vSeedMatrixGood hp11 q A B) := rfl

theorem vSeedResidueMatrix_det_eq_residueHomP (hp11 : 11 ≤ p) (q : ℕ) :
    (vSeedResidueMatrix q p).det =
      residueHomP p ⟨(V.vPolynomial 1 (-(q : ℤ))).coeff 0, vSeedConstant_good hp11 q⟩ :=
  residue_det_of_good (vSeedMatrixGood hp11 q) (vSeedResidueMatrix q p)
    (vSeedResidueMatrix_apply hp11 q) _ (vSeedConstant_good hp11 q)
    (vSeedMatrixGood_det_coe hp11 q)

/-- Rational-cast form used by the constant-unit calculation.  The `residueHomP ⟨c, _⟩ = (c : ZMod p)`
step is the abstract `residueHomP_mk` instance, never a kernel defeq on the
concrete constant. -/
theorem vSeedResidueMatrix_det_eq_cast (hp11 : 11 ≤ p) (q : ℕ) :
    (vSeedResidueMatrix q p).det =
      (((V.vPolynomial 1 (-(q : ℤ))).coeff 0 : ℚ) : ZMod p) :=
  Eq.trans (vSeedResidueMatrix_det_eq_residueHomP hp11 q)
    (residueHomP_mk _ (vSeedConstant_good hp11 q))


/-- `eval 0` commutes with `map (GoodP p).subtype` (coefficient route; no
`eval_map_apply`). -/
theorem goodP_eval_zero_map_subtype (P : Polynomial (GoodP p)) :
    (P.map (GoodP p).subtype).eval 0 = ((P.eval 0 : GoodP p) : ℚ) := by
  rw [Polynomial.eval_map, Polynomial.eval₂_at_zero, Polynomial.coeff_zero_eq_eval_zero]
  rfl

/-! ## Private denominator helpers (from `P0/PositiveTower/GenericCResidue.lean`) -/

private lemma qdiff_cast_zero_generic (k i j : ℕ) (hij : i ≠ j)
    (hmod : i % p ^ k ≠ j % p ^ k)
    (hbound : max i j < p * p ^ k) :
    ((qRatP p k / ((j : ℚ) - (i : ℚ)) : ℚ) : ZMod p) = 0 := by
  rcases Nat.lt_or_gt_of_ne hij with hlt | hlt
  · have hcast : (j : ℚ) - (i : ℚ) = ((j - i : ℕ) : ℚ) := by
      rw [Nat.cast_sub hlt.le]
    rw [hcast]
    apply qdiv_cast_zero_generic k (j - i) (Nat.sub_pos_of_lt hlt)
    · exact lt_of_le_of_lt (Nat.sub_le _ _)
        (lt_of_le_of_lt (Nat.le_max_right _ _) hbound)
    · intro hdvd
      apply hmod
      exact (Nat.modEq_iff_dvd' hlt.le).mpr hdvd
  · have hcast : (j : ℚ) - (i : ℚ) = -((i - j : ℕ) : ℚ) := by
      rw [Nat.cast_sub hlt.le]
      ring
    rw [hcast, div_neg, Rat.cast_neg]
    rw [qdiv_cast_zero_generic k (i - j) (Nat.sub_pos_of_lt hlt)]
    · simp
    · exact lt_of_le_of_lt (Nat.sub_le _ _)
        (lt_of_le_of_lt (Nat.le_max_left _ _) hbound)
    · intro hdvd
      apply hmod
      exact ((Nat.modEq_iff_dvd' hlt.le).mpr hdvd).symm

private lemma qdiff_cast_unit_generic (k i j v : ℕ)
    (hij : i ≠ j) (hi : i < p) (hj : j < p) :
    ((qRatP p k /
      (((j * p ^ k + v : ℕ) : ℚ) - ((i * p ^ k + v : ℕ) : ℚ)) : ℚ) : ZMod p) =
      ((((j : ℤ) - (i : ℤ) : ℤ) : ZMod p))⁻¹ := by
  rcases Nat.lt_or_gt_of_ne hij with hlt | hlt
  · have hcast :
        (((j * p ^ k + v : ℕ) : ℚ) - ((i * p ^ k + v : ℕ) : ℚ)) =
          (((j - i) * p ^ k : ℕ) : ℚ) := by
      push_cast
      rw [Nat.cast_sub hlt.le]
      ring
    rw [hcast, qdiv_cast_unit_generic k (j - i) (by omega) (by omega)]
    congr 1
    simp [Nat.cast_sub hlt.le]
  · have hcast :
        (((j * p ^ k + v : ℕ) : ℚ) - ((i * p ^ k + v : ℕ) : ℚ)) =
          -(((i - j) * p ^ k : ℕ) : ℚ) := by
      push_cast
      rw [Nat.cast_sub hlt.le]
      ring
    rw [hcast, div_neg, Rat.cast_neg,
      qdiv_cast_unit_generic k (i - j) (by omega) (by omega)]
    rw [show ((j : ℤ) - (i : ℤ) : ℤ) = -((i - j : ℕ) : ℤ) by
      rw [Nat.cast_sub hlt.le]
      ring]
    push_cast
    rw [inv_neg]

/-! ## Squared denominator helpers and second-moment residue (`vMomentB_scaled_residue`) -/

private lemma q_sq_div_sq_eq (k d : ℕ) :
    qRatP p k ^ 2 / (d : ℚ) ^ 2 =
      (qRatP p k / (d : ℚ)) * (qRatP p k / (d : ℚ)) := by
  rw [sq, sq, div_mul_div_comm]

private lemma qsq_div_sq_cast_unit_generic (k c : ℕ) (hc0 : 0 < c) (hcp : c < p) :
    ((qRatP p k ^ 2 / ((c * p ^ k : ℕ) : ℚ) ^ 2 : ℚ) : ZMod p) =
      (((c : ZMod p)⁻¹) ^ 2) := by
  have hq : 0 < p ^ k := pow_pos (Fact.out : Nat.Prime p).pos k
  have hgood : qRatP p k / ((c * p ^ k : ℕ) : ℚ) ∈ GoodP p :=
    q_div_good k (c * p ^ k) (Nat.mul_pos hc0 hq)
      (Nat.mul_lt_mul_of_pos_right hcp hq)
  rw [q_sq_div_sq_eq,
    Rat.cast_mul_of_ne_zero (natCast_ne_zero_of_coprime hgood)
      (natCast_ne_zero_of_coprime hgood),
    qdiv_cast_unit_generic k c hc0 hcp, sq]

private lemma qsq_div_sq_cast_zero_generic (k n : ℕ) (hn0 : 0 < n)
    (hnlt : n < p * p ^ k) (hnd : ¬ p ^ k ∣ n) :
    ((qRatP p k ^ 2 / (n : ℚ) ^ 2 : ℚ) : ZMod p) = 0 := by
  have hgood : qRatP p k / (n : ℚ) ∈ GoodP p :=
    q_div_good k n hn0 hnlt
  rw [q_sq_div_sq_eq,
    Rat.cast_mul_of_ne_zero (natCast_ne_zero_of_coprime hgood)
      (natCast_ne_zero_of_coprime hgood),
    qdiv_cast_zero_generic k n hn0 hnlt hnd, mul_zero]

theorem qMomentB_decomp (p : ℕ) (a : ℤ) (k N : ℕ) :
    qRatP p k ^ 2 * V.vMomentB a N =
      ∑ r ∈ Finset.range N,
        (a : ℚ) ^ (N - (r + 1)) * (qRatP p k ^ 2 / ((r + 1 : ℕ) : ℚ) ^ 2) := by
  unfold V.vMomentB
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [div_eq_mul_inv]
  ring

theorem qMomentB_term_good (a : ℤ) (k N r : ℕ)
    (hN : N < p * p ^ k) (hr : r ∈ Finset.range N) :
    (a : ℚ) ^ (N - (r + 1)) *
        (qRatP p k ^ 2 / ((r + 1 : ℕ) : ℚ) ^ 2) ∈ GoodP p := by
  have hrlt : r < N := Finset.mem_range.mp hr
  exact (GoodP p).mul_mem
    ((GoodP p).pow_mem (intRat_good a) _)
    (q_sq_div_sq_good k (r + 1) (by omega) (by omega))

theorem vMomentB_scaled_residue_sum (p : ℕ)
    [Fact (Nat.Prime p)] (a : ℤ) (k B v : ℕ)
    (hB : B < p) (hv : v < p ^ k) :
    ((qRatP p k ^ 2 * V.vMomentB a (B * p ^ k + v) : ℚ) : ZMod p) =
      (a : ZMod p) ^ v *
        ∑ c ∈ Finset.range B,
          (a : ZMod p) ^ (B - (c + 1)) *
            (((c + 1 : ℕ) : ZMod p)⁻¹) ^ 2 := by
  have hq : 0 < p ^ k := pow_pos (Fact.out : Nat.Prime p).pos k
  have hN : B * p ^ k + v < p * p ^ k := by
    calc
      B * p ^ k + v < B * p ^ k + p ^ k := Nat.add_lt_add_left hv _
      _ = (B + 1) * p ^ k := by ring
      _ ≤ p * p ^ k := Nat.mul_le_mul_right _ hB
  have hpow_good : ∀ m : ℕ, (a : ℚ) ^ m ∈ GoodP p :=
    fun m => (GoodP p).pow_mem (intRat_good a) m
  rw [qMomentB_decomp,
    ratCast_sum_good (Finset.range (B * p ^ k + v)) _
      (fun r hr => qMomentB_term_good a k (B * p ^ k + v) r hN hr)]
  rw [Li2Lean.P0.ScaledLucas.block_sum (p ^ k) B v (p ^ k - 1) _ (by omega)]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c hc
    have hc' : c < B := Finset.mem_range.mp hc
    have hlt : c * p ^ k + (p ^ k - 1) < B * p ^ k :=
      Li2Lean.P0.ScaledLucas.ar_lt c (p ^ k - 1) (p ^ k) B hc' (by omega)
    have hqdiv : qRatP p k ^ 2 /
        ((c * p ^ k + (p ^ k - 1) + 1 : ℕ) : ℚ) ^ 2 ∈ GoodP p :=
      q_sq_div_sq_good k _ (by omega) (by omega)
    rw [Rat.cast_mul_of_ne_zero
        (natCast_ne_zero_of_coprime (hpow_good _))
        (natCast_ne_zero_of_coprime hqdiv),
      Li2Lean.P0.ScaledLucas.ar_shift B c (p ^ k) v hc' hq,
      Li2Lean.P0.ScaledLucas.ar_last c (p ^ k) hq,
      cast_int_pow_frob p a k (B - (c + 1)) v,
      qsq_div_sq_cast_unit_generic k (c + 1) (by omega) (by omega)]
    ring
  · intro c hc t ht htt
    have hlt : c * p ^ k + t < B * p ^ k :=
      Li2Lean.P0.ScaledLucas.ar_lt c t (p ^ k) B hc ht
    have ht1 : t + 1 < p ^ k := by omega
    have hqdiv : qRatP p k ^ 2 /
        ((c * p ^ k + t + 1 : ℕ) : ℚ) ^ 2 ∈ GoodP p :=
      q_sq_div_sq_good k _ (by omega) (by omega)
    have hnd : ¬ p ^ k ∣ c * p ^ k + t + 1 :=
      Li2Lean.P0.ScaledLucas.not_dvd_of_rem (m := c) (x := t + 1)
        (by ring) (by omega) ht1
    rw [Rat.cast_mul_of_ne_zero
        (natCast_ne_zero_of_coprime (hpow_good _))
        (natCast_ne_zero_of_coprime hqdiv),
      qsq_div_sq_cast_zero_generic k (c * p ^ k + t + 1) (by omega) (by omega) hnd,
      mul_zero]
  · intro t ht
    have ht1 : t + 1 < p ^ k := by omega
    have hqdiv : qRatP p k ^ 2 /
        ((B * p ^ k + t + 1 : ℕ) : ℚ) ^ 2 ∈ GoodP p :=
      q_sq_div_sq_good k _ (by omega) (by omega)
    have hnd : ¬ p ^ k ∣ B * p ^ k + t + 1 :=
      Li2Lean.P0.ScaledLucas.not_dvd_of_rem (m := B) (x := t + 1)
        (by ring) (by omega) ht1
    rw [Rat.cast_mul_of_ne_zero
        (natCast_ne_zero_of_coprime (hpow_good _))
        (natCast_ne_zero_of_coprime hqdiv),
      qsq_div_sq_cast_zero_generic k (B * p ^ k + t + 1) (by omega) (by omega) hnd,
      mul_zero]

theorem vMomentB_seed_residue_sum (p : ℕ) [Fact (Nat.Prime p)]
    (a : ℤ) (B : ℕ) (hB : B < p) :
    ((V.vMomentB a B : ℚ) : ZMod p) =
      ∑ c ∈ Finset.range B,
        (a : ZMod p) ^ (B - (c + 1)) *
          (((c + 1 : ℕ) : ZMod p)⁻¹) ^ 2 := by
  have h0 := vMomentB_scaled_residue_sum p a 0 B 0 hB (by simp)
  simpa [qRatP] using h0

theorem vMomentB_scaled_residue (a : ℤ) (k B v : ℕ)
    (hB : B < p) (hv : v < p ^ k) :
    ((qRatP p k ^ 2 * V.vMomentB a (B * p ^ k + v) : ℚ) : ZMod p) =
      (a : ZMod p) ^ v * ((V.vMomentB a B : ℚ) : ZMod p) := by
  rw [vMomentB_scaled_residue_sum p a k B v hB hv,
    vMomentB_seed_residue_sum p a B hB]

theorem vMomentB_scaled_residue_good (a : ℤ) (k B v : ℕ)
    (hB : B < p) (hv : v < p ^ k) :
    residueHomP p ⟨qRatP p k ^ 2 * V.vMomentB a (B * p ^ k + v),
        q_sq_mul_vMomentB_good a k (B * p ^ k + v)
          (Li2Lean.P0.ScaledLucas.ar_lt B v (p ^ k) p hB hv)⟩ =
      (a : ZMod p) ^ v *
        residueHomP p ⟨V.vMomentB a B, vMomentB_seed_good a hB⟩ :=
  vMomentB_scaled_residue a k B v hB hv

/-! ## Natural-index entry residue leaves -/

theorem vC_entry_residue_offres (a : ℤ) (k i₀ j₀ u v : ℕ)
    (hi₀ : i₀ < p) (hj₀ : j₀ < p)
    (hu : u < p ^ k) (hv : v < p ^ k) (huv : u ≠ v) :
    ((qRatP p k * V.vCEntry a (i₀ * p ^ k + u) (j₀ * p ^ k + v) : ℚ) : ZMod p) = 0 := by
  have hmod : (i₀ * p ^ k + u) % p ^ k ≠ (j₀ * p ^ k + v) % p ^ k := by
    rw [Li2Lean.P0.ScaledLucas.mod_of_decomp hu,
      Li2Lean.P0.ScaledLucas.mod_of_decomp hv]
    exact huv
  have hij : i₀ * p ^ k + u ≠ j₀ * p ^ k + v := fun h => hmod (congrArg (· % p ^ k) h)
  have hi : i₀ * p ^ k + u < p * p ^ k :=
    Li2Lean.P0.ScaledLucas.ar_lt i₀ u (p ^ k) p hi₀ hu
  have hj : j₀ * p ^ k + v < p * p ^ k :=
    Li2Lean.P0.ScaledLucas.ar_lt j₀ v (p ^ k) p hj₀ hv
  have hsplit : qRatP p k * V.vCEntry a (i₀ * p ^ k + u) (j₀ * p ^ k + v) =
      ((a : ℚ) ^ (i₀ * p ^ k + u) - (a : ℚ) ^ (j₀ * p ^ k + v)) *
        (qRatP p k / (((j₀ * p ^ k + v : ℕ) : ℚ) - ((i₀ * p ^ k + u : ℕ) : ℚ))) := by
    unfold V.vCEntry
    rw [if_neg hij]
    ring
  have g1 : (a : ℚ) ^ (i₀ * p ^ k + u) - (a : ℚ) ^ (j₀ * p ^ k + v) ∈ GoodP p :=
    (GoodP p).sub_mem ((GoodP p).pow_mem (intRat_good a) _)
      ((GoodP p).pow_mem (intRat_good a) _)
  have g2 : qRatP p k / (((j₀ * p ^ k + v : ℕ) : ℚ) - ((i₀ * p ^ k + u : ℕ) : ℚ)) ∈ GoodP p :=
    q_div_diff_good k (i₀ * p ^ k + u) (j₀ * p ^ k + v) hij (max_lt hi hj)
  rw [hsplit,
    Rat.cast_mul_of_ne_zero (natCast_ne_zero_of_coprime g1)
      (natCast_ne_zero_of_coprime g2),
    qdiff_cast_zero_generic k (i₀ * p ^ k + u) (j₀ * p ^ k + v) hij hmod (max_lt hi hj),
    mul_zero]

theorem vC_entry_residue_sameres (a : ℤ) (k i₀ j₀ u : ℕ)
    (hi₀ : i₀ < p) (hj₀ : j₀ < p) (hu : u < p ^ k) :
    ((qRatP p k * V.vCEntry a (i₀ * p ^ k + u) (j₀ * p ^ k + u) : ℚ) : ZMod p) =
      (a : ZMod p) ^ u * ((V.vCEntry a i₀ j₀ : ℚ) : ZMod p) := by
  by_cases hi₀j₀ : i₀ = j₀
  · subst hi₀j₀
    simp [V.vCEntry]
  · have hq : 0 < p ^ k := pow_pos (Fact.out : Nat.Prime p).pos k
    have hij : i₀ * p ^ k + u ≠ j₀ * p ^ k + u := by
      intro h
      apply hi₀j₀
      exact Nat.eq_of_mul_eq_mul_right hq (by omega)
    have hi : i₀ * p ^ k + u < p * p ^ k :=
      Li2Lean.P0.ScaledLucas.ar_lt i₀ u (p ^ k) p hi₀ hu
    have hj : j₀ * p ^ k + u < p * p ^ k :=
      Li2Lean.P0.ScaledLucas.ar_lt j₀ u (p ^ k) p hj₀ hu
    have hsplit : qRatP p k * V.vCEntry a (i₀ * p ^ k + u) (j₀ * p ^ k + u) =
        ((a : ℚ) ^ (i₀ * p ^ k + u) - (a : ℚ) ^ (j₀ * p ^ k + u)) *
          (qRatP p k / (((j₀ * p ^ k + u : ℕ) : ℚ) - ((i₀ * p ^ k + u : ℕ) : ℚ))) := by
      unfold V.vCEntry
      rw [if_neg hij]
      ring
    have g1 : (a : ℚ) ^ (i₀ * p ^ k + u) ∈ GoodP p :=
      (GoodP p).pow_mem (intRat_good a) _
    have g2 : (a : ℚ) ^ (j₀ * p ^ k + u) ∈ GoodP p :=
      (GoodP p).pow_mem (intRat_good a) _
    have g3 : qRatP p k / (((j₀ * p ^ k + u : ℕ) : ℚ) - ((i₀ * p ^ k + u : ℕ) : ℚ)) ∈ GoodP p :=
      q_div_diff_good k (i₀ * p ^ k + u) (j₀ * p ^ k + u) hij (max_lt hi hj)
    rw [hsplit,
      Rat.cast_mul_of_ne_zero (natCast_ne_zero_of_coprime ((GoodP p).sub_mem g1 g2))
        (natCast_ne_zero_of_coprime g3),
      Rat.cast_sub_of_ne_zero (natCast_ne_zero_of_coprime g1)
        (natCast_ne_zero_of_coprime g2),
      cast_int_pow_frob p a k i₀ u,
      cast_int_pow_frob p a k j₀ u,
      qdiff_cast_unit_generic k i₀ j₀ u hi₀j₀ hi₀ hj₀]
    have hseed : ((V.vCEntry a i₀ j₀ : ℚ) : ZMod p) =
        ((a : ZMod p) ^ i₀ - (a : ZMod p) ^ j₀) *
          ((((j₀ : ℤ) - (i₀ : ℤ) : ℤ) : ZMod p))⁻¹ := by
      unfold V.vCEntry
      rw [if_neg hi₀j₀]
      have s1 : (a : ℚ) ^ i₀ ∈ GoodP p := (GoodP p).pow_mem (intRat_good a) i₀
      have s2 : (a : ℚ) ^ j₀ ∈ GoodP p := (GoodP p).pow_mem (intRat_good a) j₀
      have s3 : (((j₀ : ℚ) - (i₀ : ℚ))⁻¹) ∈ GoodP p := by
        have hb0 : max i₀ j₀ < p * p ^ 0 := by simpa using max_lt hi₀ hj₀
        have hr0 := q_div_diff_good (p := p) 0 i₀ j₀ hi₀j₀ hb0
        simpa [qRatP, one_div] using hr0
      rw [div_eq_mul_inv,
        Rat.cast_mul_of_ne_zero (natCast_ne_zero_of_coprime ((GoodP p).sub_mem s1 s2))
          (natCast_ne_zero_of_coprime s3),
        Rat.cast_sub_of_ne_zero (natCast_ne_zero_of_coprime s1)
          (natCast_ne_zero_of_coprime s2)]
      have hpow_i : (((a : ℚ) ^ i₀ : ℚ) : ZMod p) = (a : ZMod p) ^ i₀ := by
        simpa using cast_int_pow_frob p a 0 i₀ 0
      have hpow_j : (((a : ℚ) ^ j₀ : ℚ) : ZMod p) = (a : ZMod p) ^ j₀ := by
        simpa using cast_int_pow_frob p a 0 j₀ 0
      have hden0 : ((((j₀ : ℚ) - (i₀ : ℚ))⁻¹ : ℚ) : ZMod p) =
          ((((j₀ : ℤ) - (i₀ : ℤ) : ℤ) : ZMod p))⁻¹ := by
        simpa [qRatP] using qdiff_cast_unit_generic (p := p) 0 i₀ j₀ 0 hi₀j₀ hi₀ hj₀
      rw [hpow_i, hpow_j, hden0]
    rw [hseed]
    ring

theorem vB_entry_residue_diag (a : ℤ) (k i₀ u : ℕ)
    (hi₀ : i₀ < p) (hu : u < p ^ k) :
    ((qRatP p k ^ 2 * V.vBEntry a (i₀ * p ^ k + u) (i₀ * p ^ k + u) : ℚ) : ZMod p) =
      (a : ZMod p) ^ u * ((V.vBEntry a i₀ i₀ : ℚ) : ZMod p) := by
  unfold V.vBEntry
  simp only [↓reduceIte]
  exact vMomentB_scaled_residue a k i₀ u hi₀ hu

theorem vB_entry_residue_sameres_offdiag (a : ℤ) (k i₀ j₀ u : ℕ)
    (hi₀ : i₀ < p) (hj₀ : j₀ < p) (hi₀j₀ : i₀ ≠ j₀) (hu : u < p ^ k) :
    ((qRatP p k ^ 2 * V.vBEntry a (i₀ * p ^ k + u) (j₀ * p ^ k + u) : ℚ) : ZMod p) =
      (a : ZMod p) ^ u * ((V.vBEntry a i₀ j₀ : ℚ) : ZMod p) := by
  have hq : 0 < p ^ k := pow_pos (Fact.out : Nat.Prime p).pos k
  have hij : i₀ * p ^ k + u ≠ j₀ * p ^ k + u := by
    intro h
    apply hi₀j₀
    exact Nat.eq_of_mul_eq_mul_right hq (by omega)
  have hi : i₀ * p ^ k + u < p * p ^ k :=
    Li2Lean.P0.ScaledLucas.ar_lt i₀ u (p ^ k) p hi₀ hu
  have hj : j₀ * p ^ k + u < p * p ^ k :=
    Li2Lean.P0.ScaledLucas.ar_lt j₀ u (p ^ k) p hj₀ hu
  have hsplit : qRatP p k ^ 2 * V.vBEntry a (i₀ * p ^ k + u) (j₀ * p ^ k + u) =
      (qRatP p k * V.vMomentT a (i₀ * p ^ k + u) -
        qRatP p k * V.vMomentT a (j₀ * p ^ k + u)) *
        (qRatP p k / (((j₀ * p ^ k + u : ℕ) : ℚ) - ((i₀ * p ^ k + u : ℕ) : ℚ))) := by
    unfold V.vBEntry
    rw [if_neg hij]
    ring
  have g1 := q_mul_vMomentT_good (p := p) a k (i₀ * p ^ k + u) hi
  have g2 := q_mul_vMomentT_good (p := p) a k (j₀ * p ^ k + u) hj
  have g3 := q_div_diff_good (p := p) k (i₀ * p ^ k + u) (j₀ * p ^ k + u) hij (max_lt hi hj)
  have ht_i : ((qRatP p k * V.vMomentT a (i₀ * p ^ k + u) : ℚ) : ZMod p) =
      (a : ZMod p) ^ u * ((V.vMomentT a i₀ : ℚ) : ZMod p) :=
    (vMomentT_scaled_residue (p := p) a k i₀ u hi₀ hu).2
  have ht_j : ((qRatP p k * V.vMomentT a (j₀ * p ^ k + u) : ℚ) : ZMod p) =
      (a : ZMod p) ^ u * ((V.vMomentT a j₀ : ℚ) : ZMod p) :=
    (vMomentT_scaled_residue (p := p) a k j₀ u hj₀ hu).2
  rw [hsplit,
    Rat.cast_mul_of_ne_zero (natCast_ne_zero_of_coprime ((GoodP p).sub_mem g1 g2))
      (natCast_ne_zero_of_coprime g3),
    Rat.cast_sub_of_ne_zero (natCast_ne_zero_of_coprime g1)
      (natCast_ne_zero_of_coprime g2),
    ht_i, ht_j,
    qdiff_cast_unit_generic (p := p) k i₀ j₀ u hi₀j₀ hi₀ hj₀]
  have hseed : ((V.vBEntry a i₀ j₀ : ℚ) : ZMod p) =
      (((V.vMomentT a i₀ : ℚ) : ZMod p) - ((V.vMomentT a j₀ : ℚ) : ZMod p)) *
        ((((j₀ : ℤ) - (i₀ : ℤ) : ℤ) : ZMod p))⁻¹ := by
    unfold V.vBEntry
    rw [if_neg hi₀j₀]
    have s1 := vMomentT_seed_good (p := p) a hi₀
    have s2 := vMomentT_seed_good (p := p) a hj₀
    have s3 : (((j₀ : ℚ) - (i₀ : ℚ))⁻¹) ∈ GoodP p := by
      have hb0 : max i₀ j₀ < p * p ^ 0 := by simpa using max_lt hi₀ hj₀
      have hr0 := q_div_diff_good (p := p) 0 i₀ j₀ hi₀j₀ hb0
      simpa [qRatP, one_div] using hr0
    rw [div_eq_mul_inv,
      Rat.cast_mul_of_ne_zero (natCast_ne_zero_of_coprime ((GoodP p).sub_mem s1 s2))
        (natCast_ne_zero_of_coprime s3),
      Rat.cast_sub_of_ne_zero (natCast_ne_zero_of_coprime s1)
        (natCast_ne_zero_of_coprime s2)]
    have hden0 : ((((j₀ : ℚ) - (i₀ : ℚ))⁻¹ : ℚ) : ZMod p) =
        ((((j₀ : ℤ) - (i₀ : ℤ) : ℤ) : ZMod p))⁻¹ := by
      simpa [qRatP] using qdiff_cast_unit_generic (p := p) 0 i₀ j₀ 0 hi₀j₀ hi₀ hj₀
    rw [hden0]
  rw [hseed]
  ring

theorem vB_entry_residue_offres (a : ℤ) (k i₀ j₀ u v : ℕ)
    (hi₀ : i₀ < p) (hj₀ : j₀ < p)
    (hu : u < p ^ k) (hv : v < p ^ k) (huv : u ≠ v) :
    ((qRatP p k ^ 2 * V.vBEntry a (i₀ * p ^ k + u) (j₀ * p ^ k + v) : ℚ) : ZMod p) = 0 := by
  have hmod : (i₀ * p ^ k + u) % p ^ k ≠ (j₀ * p ^ k + v) % p ^ k := by
    rw [Li2Lean.P0.ScaledLucas.mod_of_decomp hu,
      Li2Lean.P0.ScaledLucas.mod_of_decomp hv]
    exact huv
  have hij : i₀ * p ^ k + u ≠ j₀ * p ^ k + v := fun h => hmod (congrArg (· % p ^ k) h)
  have hi : i₀ * p ^ k + u < p * p ^ k :=
    Li2Lean.P0.ScaledLucas.ar_lt i₀ u (p ^ k) p hi₀ hu
  have hj : j₀ * p ^ k + v < p * p ^ k :=
    Li2Lean.P0.ScaledLucas.ar_lt j₀ v (p ^ k) p hj₀ hv
  have hsplit : qRatP p k ^ 2 * V.vBEntry a (i₀ * p ^ k + u) (j₀ * p ^ k + v) =
      (qRatP p k * V.vMomentT a (i₀ * p ^ k + u) -
        qRatP p k * V.vMomentT a (j₀ * p ^ k + v)) *
        (qRatP p k / (((j₀ * p ^ k + v : ℕ) : ℚ) - ((i₀ * p ^ k + u : ℕ) : ℚ))) := by
    unfold V.vBEntry
    rw [if_neg hij]
    ring
  have g1 := q_mul_vMomentT_good (p := p) a k (i₀ * p ^ k + u) hi
  have g2 := q_mul_vMomentT_good (p := p) a k (j₀ * p ^ k + v) hj
  have g3 := q_div_diff_good (p := p) k (i₀ * p ^ k + u) (j₀ * p ^ k + v) hij (max_lt hi hj)
  rw [hsplit,
    Rat.cast_mul_of_ne_zero (natCast_ne_zero_of_coprime ((GoodP p).sub_mem g1 g2))
      (natCast_ne_zero_of_coprime g3),
    qdiff_cast_zero_generic k (i₀ * p ^ k + u) (j₀ * p ^ k + v) hij hmod (max_lt hi hj),
    mul_zero]

/-- V-block entry residue proved directly from `qdiv_cast_unit_generic` and
`qdiv_cast_zero_generic` (`EntryGoodness`), without `residueOf`. -/
theorem vV_entry_residue (hp11 : 11 ≤ p) (k j₀ u v : ℕ)
    (hj₀ : j₀ < 10) (hu : u < p ^ k) (hv : v < p ^ k) :
    ((qRatP p k * V.vVEntry (j₀ * p ^ k + v) (p ^ k - u) : ℚ) : ZMod p) =
      if u = v then ((V.vVEntry j₀ 1 : ℚ) : ZMod p) else 0 := by
  have hdiv : qRatP p k * V.vVEntry (j₀ * p ^ k + v) (p ^ k - u) =
      qRatP p k / ((j₀ * p ^ k + v + (p ^ k - u) : ℕ) : ℚ) := by
    unfold V.vVEntry
    rw [← div_eq_mul_inv]
  rw [hdiv]
  by_cases huv : u = v
  · subst huv
    rw [if_pos rfl]
    have hhit : j₀ * p ^ k + u + (p ^ k - u) = (j₀ + 1) * p ^ k := by
      have h1 : u + (p ^ k - u) = p ^ k := by omega
      calc
        j₀ * p ^ k + u + (p ^ k - u) = j₀ * p ^ k + (u + (p ^ k - u)) := by omega
        _ = j₀ * p ^ k + p ^ k := by rw [h1]
        _ = (j₀ + 1) * p ^ k := by ring
    have hseed : ((V.vVEntry j₀ 1 : ℚ) : ZMod p) = ((j₀ + 1 : ℕ) : ZMod p)⁻¹ := by
      have h0 := qdiv_cast_unit_generic (p := p) 0 (j₀ + 1) (by omega) (by omega)
      simpa [qRatP, V.vVEntry, one_div] using h0
    rw [hhit, qdiv_cast_unit_generic (p := p) k (j₀ + 1) (by omega) (by omega), hseed]
  · rw [if_neg huv]
    have hpos : 0 < j₀ * p ^ k + v + (p ^ k - u) := by omega
    have hlt : j₀ * p ^ k + v + (p ^ k - u) < p * p ^ k := by
      have h1 : j₀ * p ^ k + v + (p ^ k - u) < (j₀ + 2) * p ^ k := by
        have : (j₀ + 2) * p ^ k = j₀ * p ^ k + p ^ k + p ^ k := by ring
        omega
      have h2 : (j₀ + 2) * p ^ k ≤ p * p ^ k :=
        Nat.mul_le_mul_right (p ^ k) (by omega)
      exact lt_of_lt_of_le h1 h2
    have hnd : ¬ p ^ k ∣ j₀ * p ^ k + v + (p ^ k - u) := by
      rcases lt_or_gt_of_ne huv with hlt_uv | hgt_uv
      · have hrem_pos : 0 < v - u := by omega
        have hrem_lt : v - u < p ^ k := by omega
        have hdecomp : j₀ * p ^ k + v + (p ^ k - u) =
            (j₀ + 1) * p ^ k + (v - u) := by
          have : (j₀ + 1) * p ^ k = j₀ * p ^ k + p ^ k := by ring
          omega
        exact Li2Lean.P0.ScaledLucas.not_dvd_of_rem (m := j₀ + 1) (x := v - u)
          hdecomp hrem_pos hrem_lt
      · have hrem_pos : 0 < v + (p ^ k - u) := by omega
        have hrem_lt : v + (p ^ k - u) < p ^ k := by omega
        have hdecomp : j₀ * p ^ k + v + (p ^ k - u) =
            j₀ * p ^ k + (v + (p ^ k - u)) := by omega
        exact Li2Lean.P0.ScaledLucas.not_dvd_of_rem (m := j₀) (x := v + (p ^ k - u))
          hdecomp hrem_pos hrem_lt
    exact qdiv_cast_zero_generic (p := p) k (j₀ * p ^ k + v + (p ^ k - u)) hpos hlt hnd

/-! ## Unified `9 × 9`-block entry residue at `X = 0` -/

private theorem vScaledPencilMatrix_eval_zero_C (q Q : ℕ)
    (r c : Fin (V.vMatrixSize Q)) (hr : r.val < V.vM Q) :
    ((vScaledPencilMatrix q Q r c).eval 0) =
      (Q : ℚ) * V.vCEntry (-(q : ℤ)) (V.vIIndexNat Q r.val) (V.vJIndex Q c) := by
  unfold vScaledPencilMatrix
  simp [hr]

private theorem vScaledPencilMatrix_eval_zero_B (q Q : ℕ)
    (r c : Fin (V.vMatrixSize Q)) (hr1 : ¬ r.val < V.vM Q) (hr2 : r.val < 2 * V.vM Q) :
    ((vScaledPencilMatrix q Q r c).eval 0) =
      (Q : ℚ) ^ 2 * V.vBEntry (-(q : ℤ)) (2 * Q + (r.val - V.vM Q)) (V.vJIndex Q c) := by
  unfold vScaledPencilMatrix
  simp [hr1, hr2]

private theorem vScaledPencilMatrix_eval_zero_V (q Q : ℕ)
    (r c : Fin (V.vMatrixSize Q)) (hr2 : ¬ r.val < 2 * V.vM Q) :
    ((vScaledPencilMatrix q Q r c).eval 0) =
      (Q : ℚ) * V.vVEntry (V.vJIndex Q c) (1 + (r.val - 2 * V.vM Q)) := by
  have hr1 : ¬ r.val < V.vM Q := by omega
  unfold vScaledPencilMatrix
  simp [hr1, hr2]

/-! ## Seed `apply` lemmas in the `Fin 9` index -/

private theorem vSeedSourceMatrix9_apply_C (q : ℕ) (A B : Fin 9) (hA : A.val < 4) :
    vSeedSourceMatrix9 q A B = V.vCEntry (-(q : ℤ)) (A.val + 2) (B.val + 1) := by
  rw [vSeedSourceMatrix9_apply,
    vSource1_eval0_C q _ _ (by rw [vSeedEquiv_val]; exact hA)]
  simp only [vSeedEquiv_val]

private theorem vSeedSourceMatrix9_apply_B (q : ℕ) (A B : Fin 9)
    (hA1 : ¬ A.val < 4) (hA2 : A.val < 8) :
    vSeedSourceMatrix9 q A B = V.vBEntry (-(q : ℤ)) (A.val - 2) (B.val + 1) := by
  rw [vSeedSourceMatrix9_apply,
    vSource1_eval0_B q _ _ (by rw [vSeedEquiv_val]; exact hA1)
      (by rw [vSeedEquiv_val]; exact hA2)]
  simp only [vSeedEquiv_val]

private theorem vSeedSourceMatrix9_apply_V (q : ℕ) (A B : Fin 9) (hA2 : ¬ A.val < 8) :
    vSeedSourceMatrix9 q A B = V.vVEntry (B.val + 1) 1 := by
  rw [vSeedSourceMatrix9_apply,
    vSource1_eval0_V q _ _ (by rw [vSeedEquiv_val]; exact hA2)]
  simp only [vSeedEquiv_val]

-- `hp11` is unused in the three lemmas below; kept for the r3 call shape.
private theorem vSeedResidueMatrix_apply_C (_hp11 : 11 ≤ p) (q : ℕ)
    (A B : Fin 9) (hA : A.val < 4) :
    vSeedResidueMatrix q p A B =
      ((V.vCEntry (-(q : ℤ)) (A.val + 2) (B.val + 1) : ℚ) : ZMod p) := by
  show ((vSeedSourceMatrix9 q A B : ℚ) : ZMod p) = _
  rw [vSeedSourceMatrix9_apply_C q A B hA]

private theorem vSeedResidueMatrix_apply_B (_hp11 : 11 ≤ p) (q : ℕ)
    (A B : Fin 9) (hA1 : ¬ A.val < 4) (hA2 : A.val < 8) :
    vSeedResidueMatrix q p A B =
      ((V.vBEntry (-(q : ℤ)) (A.val - 2) (B.val + 1) : ℚ) : ZMod p) := by
  show ((vSeedSourceMatrix9 q A B : ℚ) : ZMod p) = _
  rw [vSeedSourceMatrix9_apply_B q A B hA1 hA2]

private theorem vSeedResidueMatrix_apply_V (_hp11 : 11 ≤ p) (q : ℕ)
    (A B : Fin 9) (hA2 : ¬ A.val < 8) :
    vSeedResidueMatrix q p A B =
      ((V.vVEntry (B.val + 1) 1 : ℚ) : ZMod p) := by
  show ((vSeedSourceMatrix9 q A B : ℚ) : ZMod p) = _
  rw [vSeedSourceMatrix9_apply_V q A B hA2]

theorem vScaledPencil_entry_residue (hp11 : 11 ≤ p) (q k : ℕ)
    (A B : Fin 9) (u v : Fin (p ^ k)) :
    ((((vScaledPencilMatrix q (p ^ k)) (vRowEquiv (p ^ k) (A, u))
        (vColEquiv (p ^ k) (B, v))).eval 0 : ℚ) : ZMod p) =
      if u = v then
        vBlockRowScale (((-(q : ℤ)) : ℤ) : ZMod p) u.val A *
          vSeedResidueMatrix q p A B else 0 := by
  let Q : ℕ := p ^ k
  have hQ : 0 < Q := pow_pos (Fact.out : Nat.Prime p).pos k
  have hA9 : A.val < 9 := A.isLt
  have hB9 : B.val < 9 := B.isLt
  have hu : u.val < Q := u.isLt
  have hv : v.val < Q := v.isLt
  have hj_col : V.vJIndex Q (vColEquiv Q (B, v)) = (B.val + 1) * Q + v.val := by
    unfold V.vJIndex
    rw [vColEquiv_val]
    ring
  by_cases hA4 : A.val < 4
  · have hA8 : A.val < 8 := by omega
    have hr_val : (vRowEquiv Q (A, u)).val = A.val * Q + u.val := by
      rw [vRowEquiv_val, if_pos hA8]
    have hr_lt : (vRowEquiv Q (A, u)).val < V.vM Q := by
      rw [hr_val, V.vM_eq]
      exact Li2Lean.P0.ScaledLucas.ar_lt A.val u.val Q 4 hA4 hu
    have hi_row : V.vIIndexNat Q (vRowEquiv Q (A, u)).val = (A.val + 2) * Q + u.val := by
      unfold V.vIIndexNat
      rw [hr_val]
      ring
    rw [vScaledPencilMatrix_eval_zero_C q Q _ _ hr_lt, hi_row, hj_col,
      vSeedResidueMatrix_apply_C hp11 q A B hA4]
    change ((qRatP p k * V.vCEntry (-(q : ℤ))
        ((A.val + 2) * p ^ k + u.val) ((B.val + 1) * p ^ k + v.val) : ℚ) : ZMod p) = _
    by_cases huv : u = v
    · subst huv
      rw [if_pos rfl]
      unfold vBlockRowScale
      rw [if_pos hA8]
      exact vC_entry_residue_sameres (-(q : ℤ)) k (A.val + 2) (B.val + 1) u.val
        (by omega) (by omega) u.isLt
    · rw [if_neg huv]
      exact vC_entry_residue_offres (-(q : ℤ)) k (A.val + 2) (B.val + 1) u.val v.val
        (by omega) (by omega) u.isLt v.isLt (Fin.val_ne_of_ne huv)
  · by_cases hA8 : A.val < 8
    · have hr_val : (vRowEquiv Q (A, u)).val = A.val * Q + u.val := by
        rw [vRowEquiv_val, if_pos hA8]
      have hr_ge : ¬ (vRowEquiv Q (A, u)).val < V.vM Q := by
        rw [hr_val, V.vM_eq]
        have h4Q : 4 * Q ≤ A.val * Q := Nat.mul_le_mul_right Q (by omega)
        omega
      have hr_lt2 : (vRowEquiv Q (A, u)).val < 2 * V.vM Q := by
        rw [hr_val, V.vM_eq, ← Nat.mul_assoc]
        exact Li2Lean.P0.ScaledLucas.ar_lt A.val u.val Q 8 hA8 hu
      have hi_row : 2 * Q + ((vRowEquiv Q (A, u)).val - V.vM Q) = (A.val - 2) * Q + u.val := by
        rw [hr_val, V.vM_eq]
        have h1 : A.val * Q + u.val - 4 * Q = (A.val - 4) * Q + u.val := by
          rw [Nat.sub_mul]
          have h4Q : 4 * Q ≤ A.val * Q := Nat.mul_le_mul_right Q (by omega)
          omega
        rw [h1]
        have h2 : (A.val - 2) * Q = 2 * Q + (A.val - 4) * Q := by
          have hA2 : A.val - 2 = 2 + (A.val - 4) := by omega
          rw [hA2, Nat.add_mul]
        omega
      rw [vScaledPencilMatrix_eval_zero_B q Q _ _ hr_ge hr_lt2, hi_row, hj_col,
        vSeedResidueMatrix_apply_B hp11 q A B hA4 hA8]
      change ((qRatP p k ^ 2 * V.vBEntry (-(q : ℤ))
          ((A.val - 2) * p ^ k + u.val) ((B.val + 1) * p ^ k + v.val) : ℚ) : ZMod p) = _
      by_cases huv : u = v
      · subst huv
        rw [if_pos rfl]
        unfold vBlockRowScale
        rw [if_pos hA8]
        by_cases hdiag : A.val - 2 = B.val + 1
        · rw [hdiag]
          exact vB_entry_residue_diag (-(q : ℤ)) k (B.val + 1) u.val (by omega) u.isLt
        · exact vB_entry_residue_sameres_offdiag (-(q : ℤ)) k (A.val - 2) (B.val + 1) u.val
            (by omega) (by omega) hdiag u.isLt
      · rw [if_neg huv]
        exact vB_entry_residue_offres (-(q : ℤ)) k (A.val - 2) (B.val + 1) u.val v.val
          (by omega) (by omega) u.isLt v.isLt (Fin.val_ne_of_ne huv)
    · have hr_val : (vRowEquiv Q (A, u)).val = 8 * Q + (Q - 1 - u.val) := by
        rw [vRowEquiv_val, if_neg hA8]
      have hr_ge2 : ¬ (vRowEquiv Q (A, u)).val < 2 * V.vM Q := by
        rw [hr_val, V.vM_eq]
        have h8Q : 2 * (4 * Q) = 8 * Q := by ring
        omega
      have hell_row : 1 + ((vRowEquiv Q (A, u)).val - 2 * V.vM Q) = Q - u.val := by
        rw [hr_val, V.vM_eq]
        have h8Q : 2 * (4 * Q) = 8 * Q := by ring
        omega
      rw [vScaledPencilMatrix_eval_zero_V q Q _ _ hr_ge2, hj_col, hell_row,
        vSeedResidueMatrix_apply_V hp11 q A B hA8]
      change ((qRatP p k * V.vVEntry
          ((B.val + 1) * p ^ k + v.val) (p ^ k - u.val) : ℚ) : ZMod p) = _
      have hv_res := vV_entry_residue (p := p) hp11 k (B.val + 1) u.val v.val
        (by omega) u.isLt v.isLt
      by_cases huv : u = v
      · have huv_val : u.val = v.val := congrArg Fin.val huv
        rw [if_pos huv_val] at hv_res
        rw [if_pos huv]
        unfold vBlockRowScale
        rw [if_neg hA8, one_mul]
        exact hv_res
      · have huv_val : u.val ≠ v.val := Fin.val_ne_of_ne huv
        rw [if_neg huv_val] at hv_res
        rw [if_neg huv]
        exact hv_res

/-- `GoodP p` / `residueHomP p` formulation of the unified entry residue
(consumed by the constant-unit calculation). -/
theorem vScaledPencilGood_entry_residue (hp11 : 11 ≤ p) (q k : ℕ)
    (A B : Fin 9) (u v : Fin (p ^ k)) :
    residueHomP p ((vScaledPencilGood hp11 q k
        (vRowEquiv (p ^ k) (A, u)) (vColEquiv (p ^ k) (B, v))).eval 0) =
      if u = v then
        vBlockRowScale (((-(q : ℤ)) : ℤ) : ZMod p) u.val A *
          vSeedResidueMatrix q p A B else 0 := by
  have hmap := congrFun (congrFun (vScaledPencilGood_map hp11 q k)
    (vRowEquiv (p ^ k) (A, u))) (vColEquiv (p ^ k) (B, v))
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Polynomial.coe_mapRingHom] at hmap
  rw [← vScaledPencil_entry_residue hp11 q k A B u v, ← hmap,
    goodP_eval_zero_map_subtype]
  rfl

end
end Li2Lean.B3

#print axioms Li2Lean.B3.vSeedSourceMatrix9_det
#print axioms Li2Lean.B3.vSeedResidueMatrix_det_eq_cast
#print axioms Li2Lean.B3.vMomentB_scaled_residue
#print axioms Li2Lean.B3.vScaledPencil_entry_residue
#print axioms Li2Lean.B3.vScaledPencilGood_entry_residue
