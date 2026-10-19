/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.Pole.PoleDivisorAssembly

namespace Li2Lean.P0.Pole
open Polynomial Matrix Finset Li2Lean.P0.Integerization
open Li2Lean.P0.PoleMatrixCore
noncomputable section
set_option maxHeartbeats 200000

private theorem sum_range_truncate {R : Type*} [AddCommMonoid R]
    (n u : ℕ) (hu : u < n) (f : ℕ → R) :
    (∑ a ∈ range n, if a ≤ u then f a else 0) = ∑ a ∈ range (u+1), f a := by
  symm
  calc
    (∑ a ∈ range (u+1), f a) =
        ∑ a ∈ range (u+1), if a ≤ u then f a else 0 := by
      apply sum_congr rfl
      intro a ha
      simp [show a ≤ u by have := mem_range.mp ha; omega]
    _ = ∑ a ∈ range n, if a ≤ u then f a else 0 := by
      apply sum_subset (range_mono (by omega))
      intro a _ ha
      simp only [mem_range, not_lt] at ha
      simp [show ¬ a ≤ u by omega]

private theorem sum_fdw {R : Type*} [CommRing R] [Algebra ℚ R]
    (n u : ℕ) (hu : u < n) (f : ℕ → R) :
    (∑ a : Fin n, algebraMap ℚ R (if a.val ≤ u then fdw u a.val else 0) * f a.val) =
      ∑ a ∈ range (u+1), algebraMap ℚ R (fdw u a) * f a := by
  simp_rw [apply_ite, map_zero, ite_mul, zero_mul]
  exact (Fin.sum_univ_eq_sum_range
    (fun a => if a ≤ u then algebraMap ℚ R (fdw u a) * f a else 0) n).trans
      (sum_range_truncate n u hu _)

/-- The shifted row and column forward-difference transform. -/
def shiftedPoleDifference (m : ℕ) : Matrix (Fin (2*m)) (Fin (2*m)) BivPoly :=
  shiftB.mapMatrix
    ((algebraMap ℚ BivPoly).mapMatrix (poleRowDiffMatrix m) * poleMatrix m *
      (algebraMap ℚ BivPoly).mapMatrix (forwardDiffMatrix (2*m)).transpose)

private theorem ratConst_eq_algebraMap (a : ℚ) :
    ratConst a = algebraMap ℚ BivPoly a := by rfl

private theorem pole_row_top (m : ℕ) (r c : Fin (2*m)) (hr : r.val < m) :
    ((algebraMap ℚ BivPoly).mapMatrix (poleRowDiffMatrix m) * poleMatrix m) r c =
      ∑ a ∈ range (r.val+1), ratConst (fdw r.val a) *
        formalC (m/2) (m/4+a) c.val := by
  rw [Matrix.mul_apply]
  have ht : ∀ a : Fin (2*m),
      (algebraMap ℚ BivPoly).mapMatrix (poleRowDiffMatrix m) r a * poleMatrix m a c =
        algebraMap ℚ BivPoly (if a.val ≤ r.val then fdw r.val a.val else 0) *
          formalC (m/2) (m/4+a.val) c.val := by
    intro a
    by_cases ha : a.val ≤ r.val
    · have ham : a.val < m := by omega
      simp [poleRowDiffMatrix, poleMatrix, hr, ham, ha]
    · by_cases ham : a.val < m
      · simp [poleRowDiffMatrix, poleMatrix, hr, ham, ha]
      · simp [poleRowDiffMatrix, hr, ham, ha]
  simp_rw [ht]
  simpa only [← ratConst_eq_algebraMap] using
    sum_fdw (R := BivPoly) (2*m) r.val (by omega)
      (fun a => formalC (m/2) (m/4+a) c.val)

private theorem sum_range_block {R : Type*} [AddCommMonoid R]
    (m : ℕ) (f g : ℕ → R) :
    (∑ i ∈ range (2*m), if i < m then f i else g (i-m)) =
      (∑ i ∈ range m, f i) + ∑ i ∈ range m, g i := by
  rw [show 2*m=m+m by omega, sum_range_add]
  congr 1
  · apply sum_congr rfl
    intro i hi
    simp [mem_range.mp hi]
  · apply sum_congr rfl
    intro i hi
    simp

private theorem pole_row_lower (m : ℕ) (r c : Fin (2*m)) (hr : ¬ r.val < m) :
    ((algebraMap ℚ BivPoly).mapMatrix (poleRowDiffMatrix m) * poleMatrix m) r c =
      ∑ a ∈ range (r.val-m+1), ratConst (fdw (r.val-m) a) *
        (formalB (m/2) (m/4+a) c.val -
          C X * (aVar-ratConst 1)^(m/2) * formalA (m/2) (m/4+a) c.val) := by
  let L : ℕ → BivPoly := fun a =>
    formalB (m/2) (m/4+a) c.val -
      C X * (aVar-ratConst 1)^(m/2) * formalA (m/2) (m/4+a) c.val
  rw [Matrix.mul_apply]
  have ht : ∀ a : Fin (2*m),
      (algebraMap ℚ BivPoly).mapMatrix (poleRowDiffMatrix m) r a * poleMatrix m a c =
        if a.val < m then 0 else
          if a.val-m ≤ r.val-m then ratConst (fdw (r.val-m) (a.val-m)) * L (a.val-m)
          else 0 := by
    intro a
    by_cases ha : a.val < m
    · simp [poleRowDiffMatrix, poleMatrix, hr, ha, show ¬m ≤ a.val by omega]
    · have ham : m ≤ a.val := by omega
      by_cases har : a.val-m ≤ r.val-m
      · simp [poleRowDiffMatrix, poleMatrix, hr, ha, ham, har, L,
          ratConst_eq_algebraMap]
      · simp [poleRowDiffMatrix, poleMatrix, hr, ha, ham, har]
  simp_rw [ht]
  rw [Fin.sum_univ_eq_sum_range
    (fun a => if a < m then (0 : BivPoly) else
      if a-m ≤ r.val-m then ratConst (fdw (r.val-m) (a-m)) * L (a-m) else 0)]
  rw [sum_range_block m (fun _ => (0 : BivPoly))
    (fun a => if a ≤ r.val-m then ratConst (fdw (r.val-m) a) * L a else 0)]
  simp only [sum_const_zero, zero_add]
  exact sum_range_truncate m (r.val-m) (by omega) _

private theorem pole_difference_top (m : ℕ) (r c : Fin (2*m)) (hr : r.val < m) :
    shiftedPoleDifference m r c = fdwShiftFormalC (m/2) (m/4) r.val c.val := by
  change shiftB (((algebraMap ℚ BivPoly).mapMatrix (poleRowDiffMatrix m) *
    poleMatrix m * (algebraMap ℚ BivPoly).mapMatrix
      (forwardDiffMatrix (2*m)).transpose) r c) = _
  rw [Matrix.mul_apply]
  simp_rw [pole_row_top m r _ hr]
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.transpose_apply,
    forwardDiffMatrix]
  have ht : ∀ b : Fin (2*m),
      (∑ a ∈ range (r.val+1), ratConst (fdw r.val a) * formalC (m/2) (m/4+a) b.val) *
        algebraMap ℚ BivPoly (if b.val ≤ c.val then fdw c.val b.val else 0) =
      algebraMap ℚ BivPoly (if b.val ≤ c.val then fdw c.val b.val else 0) *
        (∑ a ∈ range (r.val+1), ratConst (fdw r.val a) * formalC (m/2) (m/4+a) b.val) := by
    intro b
    exact mul_comm _ _
  simp_rw [ht]
  rw [sum_fdw (R := BivPoly) (2*m) c.val c.isLt
    (fun b => ∑ a ∈ range (r.val+1), ratConst (fdw r.val a) * formalC (m/2) (m/4+a) b)]
  · simp only [map_sum, map_mul, ← ratConst_eq_algebraMap, shiftB_ratConst,
      mul_sum, fdwShiftFormalC]
    rw [sum_comm]
    apply sum_congr rfl
    intro a ha
    apply sum_congr rfl
    intro b hb
    simp only [ratConst, map_mul]
    ring

private theorem pole_difference_lower (m : ℕ) (r c : Fin (2*m)) (hr : ¬ r.val < m) :
    shiftedPoleDifference m r c = fdwShiftFormalB (m/2) (m/4) (r.val-m) c.val := by
  change shiftB (((algebraMap ℚ BivPoly).mapMatrix (poleRowDiffMatrix m) *
    poleMatrix m * (algebraMap ℚ BivPoly).mapMatrix
      (forwardDiffMatrix (2*m)).transpose) r c) = _
  rw [Matrix.mul_apply]
  simp_rw [pole_row_lower m r _ hr]
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.transpose_apply,
    forwardDiffMatrix]
  simp_rw [mul_comm _ (algebraMap ℚ BivPoly _)]
  rw [sum_fdw (R := BivPoly) (2*m) c.val c.isLt
    (fun b => ∑ a ∈ range (r.val-m+1), ratConst (fdw (r.val-m) a) *
      (formalB (m/2) (m/4+a) b - C X * (aVar-ratConst 1)^(m/2) *
        formalA (m/2) (m/4+a) b))]
  · simp only [map_sum, map_mul, ← ratConst_eq_algebraMap, shiftB_ratConst,
      mul_sum, fdwShiftFormalB]
    rw [sum_comm]
    apply sum_congr rfl
    intro a ha
    apply sum_congr rfl
    intro b hb
    simp only [ratConst, map_mul]
    ring

private theorem sum_min_twice (h n : ℕ) (hn : h ≤ n) :
    2 * (∑ i ∈ range n, min i h) + h*(h+1) = 2*n*h := by
  have hsplit : n = h+(n-h) := by omega
  rw [hsplit, sum_range_add]
  have ha : (∑ i ∈ range h, min i h) = ∑ i ∈ range h, i := by
    apply sum_congr rfl
    intro i hi
    exact min_eq_left (by have := mem_range.mp hi; omega)
  have hb : (∑ i ∈ range (n-h), min (h+i) h) = (n-h)*h := by
    simp only [min_eq_right (Nat.le_add_right h _), sum_const, card_range, smul_eq_mul]
  rw [ha, hb]
  have hs := sum_range_id_mul_two h
  by_cases hh : h=0
  · simp [hh]
  · have hsub : h-1+1=h := by omega
    nlinarith

private theorem sum_min_succ (h n : ℕ) (hn : h ≤ n) :
    (∑ i ∈ range n, min (i+1) h) = (∑ i ∈ range n, min i h) + h := by
  have h1 := sum_range_succ (fun i => min i h) n
  have h2 := sum_range_succ' (fun i => min i h) n
  rw [min_eq_right hn] at h1
  simpa using h2.symm.trans h1

private theorem sum_top_indicator (h : ℕ) :
    (∑ i ∈ range (4*h), if h ≤ i then 1 else 0) = 3*h := by
  rw [show 4*h=h+3*h by omega, sum_range_add]
  have hz : (∑ i ∈ range h, if h ≤ i then 1 else 0) = 0 := by
    apply sum_eq_zero
    intro i hi
    simp [show ¬ h ≤ i by have := mem_range.mp hi; omega]
  rw [hz]
  simp
/-- Exponents for the separable order bound on the actual scaled matrix. -/
def poleConcreteRowOrder (h : ℕ) (r : Fin (2*(4*h))) : ℕ :=
  if r.val < 4*h then (if h ≤ r.val then 1 else 0)
  else min (r.val-4*h+1) h

def poleConcreteColumnOrder (h : ℕ) (c : Fin (2*(4*h))) : ℕ := min c.val h

/-- Multiply precisely the top `4*h` rows by `X^h`. -/
def poleScaledDifference (h : ℕ) :
    Matrix (Fin (2*(4*h))) (Fin (2*(4*h))) BivPoly :=
  fun r c => (X : BivPoly)^(if r.val < 4*h then h else 0) *
    shiftedPoleDifference (4*h) r c

private theorem poleConcrete_entry_order (h : ℕ) (r c : Fin (2*(4*h))) :
    (X : BivPoly)^(poleConcreteRowOrder h r + poleConcreteColumnOrder h c) ∣
      poleScaledDifference h r c := by
  have hhalf : 4*h/2=2*h := by omega
  have hquarter : 4*h/4=h := by omega
  by_cases hr : r.val < 4*h
  · simp only [poleScaledDifference, ite_eq_left hr, pole_difference_top (4*h) r c hr,
      hhalf, hquarter, poleConcreteRowOrder, poleConcreteColumnOrder]
    by_cases hu : h ≤ r.val
    · simp only [ite_eq_left hu]
      by_cases hv : h ≤ c.val
      · rw [min_eq_right hv, show 1+h=h+1 by omega, pow_add, pow_one]
        exact mul_dvd_mul_left _ (fdwShiftFormalC_X_dvd_of_le (2*h) h r.val c.val
          (by omega))
      · have hvh : c.val < h := by omega
        rw [min_eq_left (by omega)]
        exact (pow_dvd_pow (X : BivPoly) (show 1+c.val ≤ h by omega)).trans
          (dvd_mul_right _ _)
    · simp only [ite_eq_right hu, zero_add]
      exact (pow_dvd_pow (X : BivPoly) (min_le_right _ _)).trans (dvd_mul_right _ _)
  · simp only [poleScaledDifference, ite_eq_right hr, pow_zero, one_mul,
      pole_difference_lower (4*h) r c hr, hhalf, hquarter,
      poleConcreteRowOrder, poleConcreteColumnOrder]
    have h1 := min_le_left (r.val-4*h+1) h
    have h2 := min_le_right (r.val-4*h+1) h
    have h3 := min_le_left c.val h
    have h4 := min_le_right c.val h
    have he : min (r.val-4*h+1) h + min c.val h ≤
        min (2*h) (r.val-4*h+c.val+1) := le_min (by omega) (by omega)
    exact (pow_dvd_pow (X : BivPoly) he).trans
      (fdwShiftFormalB_X_pow_dvd (2*h) h (r.val-4*h) c.val)

private theorem poleConcrete_order_sum (h : ℕ) :
    (∑ r, poleConcreteRowOrder h r) + (∑ c, poleConcreteColumnOrder h c) =
      11*h^2+3*h := by
  unfold poleConcreteRowOrder poleConcreteColumnOrder
  rw [Fin.sum_univ_eq_sum_range
    (fun r => if r < 4*h then (if h ≤ r then 1 else 0) else min (r-4*h+1) h)]
  rw [sum_range_block (4*h) (fun r => if h ≤ r then 1 else 0)
    (fun r => min (r+1) h), sum_top_indicator]
  rw [Fin.sum_univ_eq_sum_range (fun c => min c h)]
  rw [sum_min_succ h (4*h) (by omega)]
  have h1 := sum_min_twice h (4*h) (by omega)
  have h2 := sum_min_twice h (2*(4*h)) (by omega)
  nlinarith

private theorem poleConcrete_scale_sum (h : ℕ) :
    (∑ r : Fin (2*(4*h)), if r.val < 4*h then h else 0) = 4*h^2 := by
  rw [Fin.sum_univ_eq_sum_range (fun r => if r < 4*h then h else 0)]
  rw [sum_range_block (4*h) (fun _ => h) (fun _ => 0)]
  simp
  ring

private theorem poleConcrete_det (h : ℕ) :
    (poleScaledDifference h).det =
      (X : BivPoly)^(4*h^2) * shiftB (Matrix.det
        ((algebraMap ℚ BivPoly).mapMatrix (poleRowDiffMatrix (4*h)) *
          poleMatrix (4*h) * (algebraMap ℚ BivPoly).mapMatrix
            (forwardDiffMatrix (2*(4*h))).transpose)) := by
  change (Matrix.of (fun r c =>
    (X : BivPoly)^(if r.val < 4*h then h else 0) * shiftedPoleDifference (4*h) r c)).det = _
  rw [Matrix.det_mul_column, prod_pow_eq_pow_sum, poleConcrete_scale_sum]
  rw [shiftedPoleDifference, ← RingHom.map_det]

/-- The concrete, unconditional shifted pole determinant divisor. -/
theorem shifted_pole_det_X_pow_dvd (h : ℕ) :
    (X : BivPoly)^(7*h^2+3*h) ∣ shiftB ((poleMatrix (4*h)).det) := by
  have hd := separable_order_dvd_det (poleScaledDifference h)
    (poleConcreteRowOrder h) (poleConcreteColumnOrder h) (poleConcrete_entry_order h)
  rw [poleConcrete_order_sum, poleConcrete_det, det_poleForwardDifferenceTransform] at hd
  rw [show 11*h^2+3*h=4*h^2+(7*h^2+3*h) by ring, pow_add] at hd
  exact (mul_dvd_mul_iff_left (pow_ne_zero _ (by simp))).mp hd

/-- Undoing the shift gives the divisor on the literal pole matrix. -/
theorem pole_det_aSubOne_pow_dvd (h : ℕ) :
    (aVar-ratConst 1)^(7*h^2+3*h) ∣ (poleMatrix (4*h)).det := by
  have hd := map_dvd unshiftB (shifted_pole_det_X_pow_dvd h)
  simp only [map_pow, unshiftB_shiftB] at hd
  simpa [aVar, ratConst] using hd

#print axioms pole_det_aSubOne_pow_dvd

#print axioms shifted_pole_det_X_pow_dvd

end
end Li2Lean.P0.Pole
