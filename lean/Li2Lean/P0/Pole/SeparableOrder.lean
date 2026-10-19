/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Mathlib

namespace Li2Lean.P0.Pole

open Polynomial

/-- A row and column power in every entry contributes to the determinant's
total order by the sum of the row and column exponents. -/
theorem separable_order_dvd_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : Type*} [CommRing R] (N : Matrix ι ι R[X]) (e f : ι → ℕ)
    (hN : ∀ r c, X ^ (e r + f c) ∣ N r c) :
    X ^ ((∑ r, e r) + ∑ c, f c) ∣ N.det := by
  classical
  rw [Matrix.det_apply]
  apply Finset.dvd_sum
  intro σ hσ
  let d : R[X] := X ^ ((∑ r, e r) + ∑ c, f c)
  have hprod : d ∣ ∏ i : ι, N (σ i) i := by
    choose q hq using fun i : ι => hN (σ i) i
    have hfactor :
        (∏ i : ι, (Polynomial.X : R[X]) ^ (e (σ i) + f i)) =
          (Polynomial.X : R[X]) ^ ((∑ r, e r) + ∑ c, f c) := by
      calc
        (∏ i : ι, (Polynomial.X : R[X]) ^ (e (σ i) + f i)) =
            (Polynomial.X : R[X]) ^ (∑ i, (e (σ i) + f i)) := by
              simpa using
                (Finset.prod_pow_eq_pow_sum Finset.univ
                  (fun i : ι => e (σ i) + f i) (Polynomial.X : R[X]))
        _ = (Polynomial.X : R[X]) ^ ((∑ r, e r) + ∑ c, f c) := by
          congr 1
          calc
            ∑ i, (e (σ i) + f i) = (∑ i, e (σ i)) + ∑ i, f i :=
              Finset.sum_add_distrib
            _ = (∑ r, e r) + ∑ c, f c := by rw [Equiv.sum_comp σ e]
    refine ⟨∏ i : ι, q i, ?_⟩
    calc
      ∏ i : ι, N (σ i) i = ∏ i : ι, (X ^ (e (σ i) + f i) * q i) := by
        apply Finset.prod_congr rfl
        intro i hi
        exact hq i
      _ = (∏ i : ι, X ^ (e (σ i) + f i)) * ∏ i : ι, q i :=
        Finset.prod_mul_distrib
      _ = d * ∏ i : ι, q i := by rw [hfactor]
  rcases hprod with ⟨q, hq⟩
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
  · rw [hs, one_smul]
    exact ⟨q, by simpa [d] using hq⟩
  · rw [hs, Units.neg_smul, one_smul]
    exact ⟨-q, by rw [hq]; simp [d, mul_neg]⟩

end Li2Lean.P0.Pole
