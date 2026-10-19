/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com)
-/

-- Intended repository path: `Li2Lean/B3/H3RowResidueZMod.lean`.

import Li2Lean.B3.ActualFrobeniusProducer
import Li2Lean.B3.VScaledPencilGood

/-!
# Seed residue rows through `ZMod p` (generic part)

`VActualSeedBoundary.row_residue` is a statement modulo the seed prime
`p = vSeedPrime q`.  This file reduces it to finite `ZMod p` data, so that no
rational 9 by 9 determinant at `T ≠ 0` and no rational interpolation is ever
formed:

1. every coefficient of `G = V.vPolynomial 1 (-q)` lies in `GoodP p`
   (at `k = 0`), hence the residue of `G(t)` is
   `∑ⱼ c̄ⱼ tʲ` with `c̄ⱼ = vSeedCoeffResidue q j` (`seed_eval_residue_sum`);
2. `M_t = M_0 - t A` entrywise (`seedSource_eval_eq`), and with integer row
   scalings `d_r`, `diag(d) M_t = N0 - t AN` over `ℤ`; so
   `(∏ d) G(t) = det (N0 - t AN)` (`seed_scaled_det`), and the residue of the
   right side is the determinant of a small `ZMod p` matrix, certified by
   `E * N̄ = L * U` with `E` upper and `L` lower unitriangular
   (`seed_point_residue`);
3. the five values at `t = 0..4` and an explicit inverse `W` of the `ZMod p`
   Vandermonde matrix give the five residues (`vSeedRowResidue_of_zmod`).

Only the per-base data and Boolean checks live in the files
`H3RowResQNZMod.lean`.  Source: v13 `nonvanishing.tex:146-198`.
-/

namespace Li2Lean.B3

noncomputable section

open Li2Lean
open Li2Lean.P0.PositiveTower
open scoped BigOperators
open Matrix

/-! ## 1. The `X`-coefficient block and evaluation at an arbitrary point -/

/-- The diagonal `A` block of `V.vSourceMatrix 1 a`, placed in rows `4..7`.
The index type is `Fin (V.vMatrixSize 1)` (not `Fin 9`) so that `r.val` is the
same term as in the body of `V.vSourceMatrix`; callers pass `Fin 9` indices,
which elaborate by unfolding `V.vMatrixSize 1 = 9` exactly as on master. -/
def seedAEntry (a : ℤ) (r c : Fin (V.vMatrixSize 1)) : ℚ :=
  if r.val < 4 then 0
  else if r.val < 8 then V.vAEntry a (2 + (r.val - 4)) (1 + c.val)
  else 0

/-- Only the `B - X A` rows depend on `X`, linearly. -/
theorem seedSource_eval_eq (a : ℤ) (r c : Fin (V.vMatrixSize 1)) (t : ℚ) :
    (V.vSourceMatrix 1 a r c).eval t =
      (V.vSourceMatrix 1 a r c).eval 0 - t * seedAEntry a r c := by
  unfold V.vSourceMatrix seedAEntry
  simp only [V.vM, V.vJIndex]
  -- VERIFIED (master 7d5cd808, `V/VFamily.lean:122-133`): the B - X A row is
  -- `C (vBEntry a i j) - X * C (vAEntry a i j)` with `i := 2 * n + (r - vM n)`,
  -- `j := vJIndex n c = n + c`, `vM n = 4 * n`; at `n = 1` `simp` (`mul_one`,
  -- `Nat.reduceMul`) gives `4`, `8`, `2 + (↑r - 4)`, `1 + ↑c`, the exact terms of
  -- `seedAEntry`.  `eval_sub/eval_mul/eval_X/eval_C` are `@[simp]`.
  -- FIXED: the planned alternative is now executed automatically (`first`); the
  -- primary branch is the original 3-way case split written with `<;>`.
  by_cases h1 : r.val < 4
  · simp [h1]
  · by_cases h2 : r.val < 8
    · simp [h1, h2]
      ring
    · simp [h1, h2]

/-- Rational evaluation of the source matrix at `T = t`. -/
def seedSourceAtT (a : ℤ) (t : ℚ) : Matrix (Fin 9) (Fin 9) ℚ :=
  fun r c => (V.vSourceMatrix 1 a r c).eval t

/-- Same proof as `q3SourceMatrixAtT_det_eq_poly_eval` (master), uniform in `a`. -/
theorem seedSourceAtT_det (a : ℤ) (t : ℚ) :
    (seedSourceAtT a t).det = (V.vPolynomial 1 a).eval t := by
  unfold seedSourceAtT V.vPolynomial
  calc
    Matrix.det (fun r c => (V.vSourceMatrix 1 a r c).eval t) =
        ((Polynomial.evalRingHom t).mapMatrix (V.vSourceMatrix 1 a)).det := by
      congr 1
    _ = (Polynomial.evalRingHom t) ((V.vSourceMatrix 1 a).det) :=
      (RingHom.map_det (Polynomial.evalRingHom t) (V.vSourceMatrix 1 a)).symm

/-! ## 2. Integer row scaling: `(∏ d) G(t) = det (N0 - t AN)` -/

theorem seed_scaled_det (a : ℤ) (M0 : Matrix (Fin 9) (Fin 9) ℚ)
    (hsrc : ∀ r c : Fin 9, (V.vSourceMatrix 1 a r c).eval 0 = M0 r c)
    (d : Fin 9 → ℕ) (N0 AN : Matrix (Fin 9) (Fin 9) ℤ)
    (hN0 : ∀ r c : Fin 9, (d r : ℚ) * M0 r c = (N0 r c : ℚ))
    (hAN : ∀ r c : Fin 9, (d r : ℚ) * seedAEntry a r c = (AN r c : ℚ)) (t : ℕ) :
    ((∏ r, d r : ℕ) : ℚ) * (V.vPolynomial 1 a).eval (t : ℚ) =
      (((N0 - (t : ℤ) • AN).det : ℤ) : ℚ) := by
  have hmat : Matrix.diagonal (fun r => (d r : ℚ)) * seedSourceAtT a (t : ℚ) =
      (Int.castRingHom ℚ).mapMatrix (N0 - (t : ℤ) • AN) := by
    ext r c
    rw [Matrix.diagonal_mul]
    simp only [seedSourceAtT, RingHom.mapMatrix_apply, Matrix.map_apply,
      Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, eq_intCast, Int.cast_sub,
      Int.cast_mul, Int.cast_natCast]
    rw [seedSource_eval_eq a r c (t : ℚ), hsrc r c, mul_sub, hN0 r c,
      mul_left_comm, hAN r c]
  have hdet := congrArg Matrix.det hmat
  rw [Matrix.det_mul, Matrix.det_diagonal, ← RingHom.map_det, seedSourceAtT_det] at hdet
  rw [Nat.cast_prod]
  -- VERIFIED names/arguments (Mathlib 25e572b8): `Matrix.diagonal_mul (d M i j)`,
  -- `RingHom.mapMatrix_apply`, `Matrix.map_apply`, `Matrix.sub_apply`,
  -- `Matrix.smul_apply`, `eq_intCast (f n)` (root, `@[simp]`),
  -- `Matrix.det_mul (M N)`, `Matrix.det_diagonal {d}`,
  -- `RingHom.map_det (f M) : f M.det = (f.mapMatrix M).det`,
  -- `Nat.cast_prod (f s)`.
  -- FIXED: `hdet` and the goal differ only by beta (`det_diagonal` leaves
  -- `(fun r => ↑(d r)) i`) and by `Int.castRingHom ℚ x` vs `↑x` (defeq), so
  -- `exact hdet` is a definitional alternative if `simpa` normalizes differently.
  first
    | simpa using hdet
    | exact hdet

/-! ## 3. Rational to residue -/

theorem ratCast_mul_natCast_of_eq {p : ℕ} [Fact (Nat.Prime p)] {x : ℚ} {D : ℕ} {n : ℤ}
    (h : (D : ℚ) * x = n) (hD : (D : ZMod p) ≠ 0) :
    (x : ZMod p) * (D : ZMod p) = (n : ZMod p) := by
  have hD0 : ((D : ℤ) : ℚ) ≠ 0 := by
    intro h0
    apply hD
    have : D = 0 := by exact_mod_cast h0
    simp [this]
  have hx : x = (n : ℚ) / ((D : ℤ) : ℚ) := by
    rw [eq_div_iff hD0]
    push_cast
    rw [mul_comm]
    exact h
  have hDz : ((D : ℤ) : ZMod p) ≠ 0 := by exact_mod_cast hD
  have hcast : (x : ZMod p) = (n : ZMod p) / ((D : ℤ) : ZMod p) := by
    rw [hx, Rat.intCast_div_eq_divInt, Rat.cast_divInt_of_ne_zero n hDz]
  rw [hcast, Int.cast_natCast]
  exact div_mul_cancel₀ _ hD
  -- VERIFIED (Mathlib 25e572b8): `Rat.intCast_div_eq_divInt (n d : ℤ) :
  -- (n : ℚ) / d = n /. d` (Data/Rat/Defs.lean:245);
  -- `Rat.cast_divInt_of_ne_zero (a : ℤ) {b : ℤ} (b0 : (b : α) ≠ 0)`
  -- (Data/Rat/Cast/Defs.lean:144); `eq_div_iff (hb : b ≠ 0) : c = a / b ↔ c * b = a`
  -- (GroupWithZero/Units/Basic.lean:347); `div_mul_cancel₀ (a) (h : b ≠ 0) :
  -- a / b * b = a` (same file :336); `Int.cast_natCast (n : ℕ) : ((n : ℤ) : R) = n`.
  -- FIXED: `push_cast` replaced by the single deterministic rewrite
  -- `Int.cast_natCast` (the only cast left in `↑n / ↑↑D * ↑D = ↑n`).

/-- Residue of the seed polynomial at a natural point. -/
def seedEvalRes (q t : ℕ) [Fact (Nat.Prime (vSeedPrime q))] : ZMod (vSeedPrime q) :=
  (((V.vPolynomial 1 (-(q : ℤ))).eval (t : ℚ) : ℚ) : ZMod (vSeedPrime q))

private theorem zsmul_matrix_entry (t : ℤ) (A : Matrix (Fin 9) (Fin 9) ℤ)
    (i j : Fin 9) :
    (t • A) i j = t * A i j := by
  induction t using Int.induction_on with
  | zero => simp
  | succ k ih =>
      rw [add_zsmul]
      simp only [one_zsmul, Matrix.add_apply]
      rw [ih]
      ring
  | pred k ih =>
      rw [sub_zsmul]
      simp only [one_zsmul, Matrix.add_apply]
      rw [ih]
      have hneg : (-A) i j = -(A i j) := by
        change (-A i j) = _
        rfl
      rw [hneg]
      ring

/-- One evaluation point: residue of `G(t)` times `∏ d` is `det U`. -/
theorem seed_point_residue {q : ℕ} [Fact (Nat.Prime (vSeedPrime q))]
    (M0 : Matrix (Fin 9) (Fin 9) ℚ)
    (hsrc : ∀ r c : Fin 9, (V.vSourceMatrix 1 (-(q : ℤ)) r c).eval 0 = M0 r c)
    (d : Fin 9 → ℕ) (N0 AN : Matrix (Fin 9) (Fin 9) ℤ)
    (hN0 : ∀ r c : Fin 9, (d r : ℚ) * M0 r c = (N0 r c : ℚ))
    (hAN : ∀ r c : Fin 9, (d r : ℚ) * seedAEntry (-(q : ℤ)) r c = (AN r c : ℚ))
    (hD : ((∏ r, d r : ℕ) : ZMod (vSeedPrime q)) ≠ 0)
    (t : ℕ) (E Nbar L U : Matrix (Fin 9) (Fin 9) (ZMod (vSeedPrime q)))
    (hNbar : ∀ i j, ((N0 i j - (t : ℤ) * AN i j : ℤ) : ZMod (vSeedPrime q)) = Nbar i j)
    (hE : E.det = 1) (hLU : E * Nbar = L * U) (hL : L.det = 1)
    (δ : ZMod (vSeedPrime q)) (hU : U.det = δ) :
    seedEvalRes q t * ((∏ r, d r : ℕ) : ZMod (vSeedPrime q)) = δ := by
  have h1 := seed_scaled_det (-(q : ℤ)) M0 hsrc d N0 AN hN0 hAN t
  have h2 := ratCast_mul_natCast_of_eq (p := vSeedPrime q) h1 hD
  unfold seedEvalRes
  rw [h2]
  have hmap : (Int.castRingHom (ZMod (vSeedPrime q))).mapMatrix (N0 - (t : ℤ) • AN) = Nbar := by
    ext i j
    rw [← hNbar i j]
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sub_apply]
    rw [map_sub]
    rw [zsmul_matrix_entry]
    simp
  have hdet : (((N0 - (t : ℤ) • AN).det : ℤ) : ZMod (vSeedPrime q)) = Nbar.det := by
    rw [← hmap, ← RingHom.map_det]
    -- FIXED: `Int.castRingHom R x` is definitionally `↑x`; `rfl` alternative.
    first
      | simp
      | rfl
  have hEN := congrArg Matrix.det hLU
  rw [Matrix.det_mul, Matrix.det_mul, hE, hL, hU, one_mul, one_mul] at hEN
  rw [hdet, hEN]

/-- At `k = 0`, the seed coefficients are `p`-integral. -/
theorem seedRow_coeff_good {p : ℕ} [Fact (Nat.Prime p)] (hp11 : 11 ≤ p) (q i : ℕ) :
    (V.vPolynomial 1 (-(q : ℤ))).coeff i ∈ GoodP p := by
  have h := vFrobeniusScaled_coeff_good hp11 q 0 i
  have h0 : V.vFrobeniusScaledPolynomial q p 0 = V.vPolynomial 1 (-(q : ℤ)) := by
    simp [V.vFrobeniusScaledPolynomial]
  rwa [h0] at h
  -- VERIFIED (master 7d5cd808): `vFrobeniusScaled_coeff_good {p} [Fact p.Prime]
  -- (hp11 : 11 ≤ p) (q k i : ℕ)` (`B3/VScaledPencilGood.lean:144`);
  -- `V.vFrobeniusScaledPolynomial q p k := let Q := p ^ k; C (Q ^ (13 Q)) *
  -- (vPolynomial Q (-q)).comp (C ((Q ^ 2)⁻¹) * X)` (`V/NonvanishingPlan.lean:83`);
  -- at `k = 0` every needed rewrite (`pow_zero`, `Nat.cast_one`, `one_pow`,
  -- `inv_one`, `map_one`, `one_mul`, `Polynomial.comp_X`) is `@[simp]`.
  -- The assembly uses this coefficient-goodness theorem directly.

private theorem rat_cast_num_den {p : ℕ} [Fact (Nat.Prime p)] (r : ℚ) :
    ((r : ℚ) : ZMod p) = (r.num : ZMod p) * (r.den : ZMod p)⁻¹ := by
  rw [Rat.cast_def, div_eq_mul_inv]

private theorem eval_residue_sum_of_good {p : ℕ} [Fact (Nat.Prime p)]
    {P : Polynomial ℚ} (hdeg : P.natDegree < 5)
    (hc : ∀ i, P.coeff i ∈ GoodP p) (t : ℕ) :
    ((P.eval (t : ℚ) : ℚ) : ZMod p) =
      ∑ j : Fin 5, (P.coeff j.val).num * ((P.coeff j.val).den : ZMod p)⁻¹ *
        ((t : ZMod p)) ^ (j : ℕ) := by
  have ht : ((t : ℚ)) ∈ GoodP p := natCast_mem (GoodP p) t
  let cG : ℕ → GoodP p := fun i => ⟨P.coeff i, hc i⟩
  let tG : GoodP p := ⟨(t : ℚ), ht⟩
  let x : GoodP p := ∑ i ∈ Finset.range 5, cG i * tG ^ i
  have hx : ((x : GoodP p) : ℚ) = P.eval (t : ℚ) := by
    rw [Polynomial.eval_eq_sum_range' hdeg]
    simp [x, cG, tG]
  have hres : ((P.eval (t : ℚ) : ℚ) : ZMod p) = residueHomP p x := by
    rw [← hx]
    rfl
  rw [hres]
  simp only [x, map_sum, map_mul, map_pow]
  rw [Finset.sum_range]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hcj : residueHomP p (cG j) =
      (P.coeff j.val).num * ((P.coeff j.val).den : ZMod p)⁻¹ := by
    have hcoeff : residueHomP p (cG j) = ((P.coeff j.val : ℚ) : ZMod p) := by
      change ((cG j : ℚ) : ZMod p) = _
      rfl
    rw [hcoeff]
    exact rat_cast_num_den (p := p) (P.coeff j.val)
  have htj : residueHomP p tG = (t : ZMod p) := by
    change (((t : ℚ)) : ZMod p) = _
    exact Rat.cast_natCast t
  rw [hcj, htj]

theorem seed_eval_residue_sum {q : ℕ} [Fact (Nat.Prime (vSeedPrime q))]
    (hp11 : 11 ≤ vSeedPrime q) (t : ℕ) :
    seedEvalRes q t =
      ∑ j : Fin 5, vSeedCoeffResidue q j.val * ((t : ZMod (vSeedPrime q))) ^ (j : ℕ) := by
  have hdeg : (V.vPolynomial 1 (-(q : ℤ))).natDegree < 5 := by
    have h : (V.vPolynomial 1 (-(q : ℤ))).natDegree ≤ V.vM 1 :=
      V.vPolynomial_natDegree_le 1 (-(q : ℤ))
    simp only [V.vM] at h
    omega
  have hc : ∀ i, (V.vPolynomial 1 (-(q : ℤ))).coeff i ∈ GoodP (vSeedPrime q) :=
    fun i => seedRow_coeff_good hp11 q i
  have hsum := eval_residue_sum_of_good (p := vSeedPrime q)
    (P := V.vPolynomial 1 (-(q : ℤ))) hdeg hc t
  simpa only [seedEvalRes, vSeedCoeffResidue] using hsum

/-- The `ZMod p` Vandermonde matrix at `t = 0, 1, 2, 3, 4`. -/
def seedVandermonde (p : ℕ) : Matrix (Fin 5) (Fin 5) (ZMod p) :=
  Matrix.of fun t j => ((t : ℕ) : ZMod p) ^ (j : ℕ)

private theorem seed_row_of_point {q : ℕ} [Fact (Nat.Prime (vSeedPrime q))]
    (hp11 : 11 ≤ vSeedPrime q) (D Dinv : ZMod (vSeedPrime q)) (hDinv : D * Dinv = 1)
    (t : ℕ) (δ : ZMod (vSeedPrime q)) (h : seedEvalRes q t * D = δ) :
    (∑ j : Fin 5, ((t : ZMod (vSeedPrime q))) ^ (j : ℕ) * vSeedCoeffResidue q j.val) =
      δ * Dinv := by
  rw [seed_eval_residue_sum hp11 t] at h
  calc
    (∑ j : Fin 5, ((t : ZMod (vSeedPrime q))) ^ (j : ℕ) * vSeedCoeffResidue q j.val) =
        (∑ j : Fin 5, vSeedCoeffResidue q j.val * ((t : ZMod (vSeedPrime q))) ^ (j : ℕ)) *
          (D * Dinv) := by
      rw [hDinv, mul_one]
      exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
    _ = δ * Dinv := by rw [← mul_assoc, h]

/-- Main reduction: five `ZMod p` evaluation residues and an inverse
Vandermonde matrix determine `row_residue`. -/
theorem vSeedRowResidue_of_zmod {q : ℕ} [Fact (Nat.Prime (vSeedPrime q))]
    (hp11 : 11 ≤ vSeedPrime q)
    (D Dinv : ZMod (vSeedPrime q)) (hDinv : D * Dinv = 1)
    (δ0 δ1 δ2 δ3 δ4 : ZMod (vSeedPrime q))
    (h0 : seedEvalRes q 0 * D = δ0) (h1 : seedEvalRes q 1 * D = δ1)
    (h2 : seedEvalRes q 2 * D = δ2) (h3 : seedEvalRes q 3 * D = δ3)
    (h4 : seedEvalRes q 4 * D = δ4)
    (W : Matrix (Fin 5) (Fin 5) (ZMod (vSeedPrime q)))
    (hW : W * seedVandermonde (vSeedPrime q) = 1)
    (hrow : W *ᵥ ![δ0 * Dinv, δ1 * Dinv, δ2 * Dinv, δ3 * Dinv, δ4 * Dinv] =
      fun i => (vSeedResidueRow q i : ZMod (vSeedPrime q))) :
    ∀ i : Fin 5, vSeedCoeffResidue q i.val =
      (vSeedResidueRow q i : ZMod (vSeedPrime q)) := by
  let c : Fin 5 → ZMod (vSeedPrime q) := fun i => vSeedCoeffResidue q i.val
  have hV : seedVandermonde (vSeedPrime q) *ᵥ c =
      ![δ0 * Dinv, δ1 * Dinv, δ2 * Dinv, δ3 * Dinv, δ4 * Dinv] := by
    funext t
    fin_cases t
    -- FIXED: each case first states the unfolded `mulVec`/`dotProduct` row
    -- with `show` (definitional: `Matrix.mulVec M v i = ∑ j, M i j * v j`,
    -- `seedVandermonde` is `Matrix.of`, `Fin.val ⟨k, _⟩ = k`, `![…] ⟨k, _⟩`
    -- reduces by `Fin.cons`), so `exact` never has to unify through a
    -- `simp`-normal form; `simpa` is kept only as a second alternative.
    · first
        | exact seed_row_of_point hp11 D Dinv hDinv 0 δ0 h0
        | (show (∑ j : Fin 5, (((0 : ℕ) : ZMod (vSeedPrime q))) ^ (j : ℕ) * c j) = δ0 * Dinv
           exact seed_row_of_point hp11 D Dinv hDinv 0 δ0 h0)
        | simpa [Matrix.mulVec, dotProduct, seedVandermonde, c] using
            seed_row_of_point hp11 D Dinv hDinv 0 δ0 h0
    · first
        | exact seed_row_of_point hp11 D Dinv hDinv 1 δ1 h1
        | (show (∑ j : Fin 5, (((1 : ℕ) : ZMod (vSeedPrime q))) ^ (j : ℕ) * c j) = δ1 * Dinv
           exact seed_row_of_point hp11 D Dinv hDinv 1 δ1 h1)
        | simpa [Matrix.mulVec, dotProduct, seedVandermonde, c] using
            seed_row_of_point hp11 D Dinv hDinv 1 δ1 h1
    · first
        | exact seed_row_of_point hp11 D Dinv hDinv 2 δ2 h2
        | (show (∑ j : Fin 5, (((2 : ℕ) : ZMod (vSeedPrime q))) ^ (j : ℕ) * c j) = δ2 * Dinv
           exact seed_row_of_point hp11 D Dinv hDinv 2 δ2 h2)
        | simpa [Matrix.mulVec, dotProduct, seedVandermonde, c] using
            seed_row_of_point hp11 D Dinv hDinv 2 δ2 h2
    · first
        | exact seed_row_of_point hp11 D Dinv hDinv 3 δ3 h3
        | (show (∑ j : Fin 5, (((3 : ℕ) : ZMod (vSeedPrime q))) ^ (j : ℕ) * c j) = δ3 * Dinv
           exact seed_row_of_point hp11 D Dinv hDinv 3 δ3 h3)
        | simpa [Matrix.mulVec, dotProduct, seedVandermonde, c] using
            seed_row_of_point hp11 D Dinv hDinv 3 δ3 h3
    · first
        | exact seed_row_of_point hp11 D Dinv hDinv 4 δ4 h4
        | (show (∑ j : Fin 5, (((4 : ℕ) : ZMod (vSeedPrime q))) ^ (j : ℕ) * c j) = δ4 * Dinv
           exact seed_row_of_point hp11 D Dinv hDinv 4 δ4 h4)
        | simpa [Matrix.mulVec, dotProduct, seedVandermonde, c] using
            seed_row_of_point hp11 D Dinv hDinv 4 δ4 h4
  have hc : c = fun i => (vSeedResidueRow q i : ZMod (vSeedPrime q)) := by
    calc
      c = (W * seedVandermonde (vSeedPrime q)) *ᵥ c := by rw [hW, Matrix.one_mulVec]
      _ = W *ᵥ (seedVandermonde (vSeedPrime q) *ᵥ c) := (Matrix.mulVec_mulVec _ _ _).symm
      -- VERIFIED (Mathlib 25e572b8, `Data/Matrix/Mul.lean:909`):
      -- `mulVec_mulVec (v) (M) (N) : M *ᵥ N *ᵥ v = (M * N) *ᵥ v` (`*ᵥ` is
      -- right associative); `one_mulVec (v) : 1 *ᵥ v = v` (:1023).
      _ = _ := by rw [hV, hrow]
  intro i
  exact congrFun hc i

end
end Li2Lean.B3
