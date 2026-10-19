/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.IntegerizationFormalMoments

namespace Li2Lean.P0.PoleMatrixCore

open Polynomial Matrix
open Li2Lean.P0.Integerization

noncomputable section

/-- Rescale the pencil variable by `(a - 1)^g`, retaining the variable `T`. -/
def tScale (g : ℕ) : BivPoly →+* BivPoly :=
  Polynomial.eval₂RingHom
    (Polynomial.eval₂RingHom (Polynomial.C.comp Polynomial.C)
      ((Polynomial.X - 1) ^ g * Polynomial.C Polynomial.X))
    Polynomial.X

@[simp] theorem tScale_ratConst (g : ℕ) (r : ℚ) :
    tScale g (ratConst r) = ratConst r := by
  simp [tScale, ratConst]

@[simp] theorem tScale_aVar (g : ℕ) : tScale g aVar = aVar := by
  simp [tScale, aVar]

@[simp] theorem tScale_T (g : ℕ) :
    tScale g (Polynomial.C Polynomial.X) =
      (aVar - ratConst 1) ^ g * Polynomial.C Polynomial.X := by
  simp [tScale, aVar, ratConst]

/-- The lower block after rescaling is `B - (a - 1)^g T A`. -/
def poleMatrix (m : ℕ) :
    Matrix (Fin (2 * m)) (Fin (2 * m)) BivPoly := fun r c =>
  let i := m / 4 + (if r.val < m then r.val else r.val - m)
  let j := c.val
  if r.val < m then formalC (m / 2) i j
  else formalB (m / 2) i j -
    Polynomial.C Polynomial.X * (aVar - ratConst 1) ^ (m / 2) *
      formalA (m / 2) i j

private theorem tScale_formalU (k g i : ℕ) :
    tScale k (formalU g i) = formalU g i := by
  simp [formalU, tScale_ratConst, tScale_aVar]

private theorem tScale_formalQNum (k g s : ℕ) :
    tScale k (formalQNum g s) = formalQNum g s := by
  simp [formalQNum, tScale_ratConst, tScale_aVar]

private theorem tScale_formalTScaled (k g i : ℕ) :
    tScale k (formalTScaled g i) = formalTScaled g i := by
  simp [formalTScaled, tScale_formalU, tScale_formalQNum,
    tScale_ratConst, tScale_aVar]

private theorem tScale_formalBScaled (k g i : ℕ) :
    tScale k (formalBScaled g i) = formalBScaled g i := by
  simp [formalBScaled, tScale_formalU, tScale_formalQNum,
    tScale_ratConst, tScale_aVar]

private theorem tScale_formalA (k g i j : ℕ) :
    tScale k (formalA g i j) = formalA g i j := by
  by_cases h : i = j <;> simp [formalA, h, tScale_formalU]

private theorem tScale_formalB (k g i j : ℕ) :
    tScale k (formalB g i j) = formalB g i j := by
  by_cases h : i = j
  · simp [formalB, h, tScale_formalBScaled]
  · simp [formalB, h, tScale_formalTScaled, tScale_ratConst]

private theorem tScale_formalC (k g i j : ℕ) :
    tScale k (formalC g i j) = formalC g i j := by
  by_cases h : i = j
  · simp [formalC, h, tScale_formalU, tScale_ratConst]
  · simp [formalC, h, tScale_formalU, tScale_ratConst]

/-- The rescaled matrix is exactly the image of the formal matrix under `tScale`.

The pencil coefficient maps to `(a - 1)^g * T`; omitting the `T` factor would
specialize the pencil and would not preserve the determinant.
-/
theorem tScale_formalMatrix (m : ℕ) :
    (tScale (m / 2)).mapMatrix (formalMatrix m) = poleMatrix m := by
  classical
  ext r c
  by_cases hr : r.val < m
  · simp [formalMatrix, poleMatrix, hr, tScale_formalC]
  · simp [formalMatrix, poleMatrix, hr, tScale_formalB, tScale_formalA,
      tScale_T]
    ring_nf

theorem det_poleMatrix_eq (m : ℕ) :
    Matrix.det (poleMatrix m) =
      tScale (m / 2) (formalCanonicalPolynomial m) := by
  calc
    Matrix.det (poleMatrix m) =
        Matrix.det ((tScale (m / 2)).mapMatrix (formalMatrix m)) := by
          rw [tScale_formalMatrix]
    _ = tScale (m / 2) (Matrix.det (formalMatrix m)) :=
      (RingHom.map_det (tScale (m / 2)) (formalMatrix m)).symm
    _ = tScale (m / 2) (formalCanonicalPolynomial m) := rfl

#print axioms tScale_formalMatrix
#print axioms det_poleMatrix_eq

end

end Li2Lean.P0.PoleMatrixCore
