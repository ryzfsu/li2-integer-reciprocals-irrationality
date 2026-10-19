/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.V.VLiteralVandermondeBridge
import Li2Lean.V.CauchyVandermonde

namespace Li2Lean.V

noncomputable section

open MeasureTheory Set

/-! The mixed `D_{zv}` determinant from v13 `v-analytic.tex:150-156`.
The column index is the paper's `J=[n,10n)`, represented by the existing
`vLiteralContourColumnIndex`; rows are the concatenated z and v variables. -/
theorem v13_D_zv_eval (n : ℕ) (z : Fin (4 * n) → ℂ)
    (v : Fin (5 * n) → ℂ) :
    (Matrix.of fun (b : Fin (4 * n) ⊕ Fin (5 * n))
        (c : Fin (4 * n) ⊕ Fin (5 * n)) =>
      (Sum.elim z v b) ^
        (Sum.elim (fun k => n + k.val)
          (fun l => n + 4 * n + l.val) c)).det =
      (∏ d : Fin (4 * n), z d ^ n) *
        (∏ b : Fin (5 * n), v b ^ n) *
        Literal.vContourVandermonde z *
        Literal.vContourVandermonde v *
        (∏ d : Fin (4 * n), ∏ b : Fin (5 * n), (v b - z d)) := by
  classical
  let h5ColumnIndex : (Fin (4 * n) ⊕ Fin (5 * n)) → ℕ :=
    Sum.elim (fun k => n + k.val) (fun l => n + 4 * n + l.val)
  let h5FlatIndex : (Fin (4 * n) ⊕ Fin (5 * n)) → ℕ :=
    Sum.elim (fun k => k.val) (fun l => 4 * n + l.val)
  let e : (Fin (4 * n) ⊕ Fin (5 * n)) ≃ Fin (4 * n + 5 * n) :=
    finSumFinEquiv
  let w : Fin (4 * n + 5 * n) → ℂ := Fin.append z v
  let A : Matrix (Fin (4 * n) ⊕ Fin (5 * n))
      (Fin (4 * n) ⊕ Fin (5 * n)) ℂ :=
    Matrix.of fun b c => (Sum.elim z v b) ^ (h5ColumnIndex c)
  let P : Matrix (Fin (4 * n) ⊕ Fin (5 * n))
      (Fin (4 * n) ⊕ Fin (5 * n)) ℂ :=
    Matrix.of fun b c => (Sum.elim z v b) ^ (h5FlatIndex c)
  have hcol (c : Fin (4 * n) ⊕ Fin (5 * n)) :
      h5ColumnIndex c = n + h5FlatIndex c := by
    cases c <;> simp [h5ColumnIndex, h5FlatIndex] <;> omega
  have hfactor : A = Matrix.diagonal (fun b => (Sum.elim z v b) ^ n) * P := by
    ext b c
    simp only [A, P, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.of_apply]
    rw [Finset.sum_eq_single b]
    · simp only [Matrix.diagonal_apply]
      simp [hcol, pow_add]
    · intro b' hb' hne
      split_ifs with h
      · exact (hne h.symm).elim
      · simp
    · simp
  have hPdet : P.det =
      Literal.vContourVandermonde (Fin.append z v) := by
    have hdet := Matrix.det_reindex_self e P
    rw [show Matrix.reindex e e P = Matrix.vandermonde w by
      ext i j
      cases hs : e.symm i with
      | inl k =>
          have hi : i = e (Sum.inl k) := by
            simpa [hs] using (e.apply_symm_apply i).symm
          cases hc : e.symm j with
          | inl l =>
              have hj : j = e (Sum.inl l) := by
                simpa [hc] using (e.apply_symm_apply j).symm
              subst i
              subst j
              simp [P, w, e, h5FlatIndex, Matrix.reindex_apply,
                Matrix.vandermonde_apply]
          | inr l =>
              have hj : j = e (Sum.inr l) := by
                simpa [hc] using (e.apply_symm_apply j).symm
              subst i
              subst j
              simp [P, w, e, h5FlatIndex, Matrix.reindex_apply,
                Matrix.vandermonde_apply]
      | inr k =>
          have hi : i = e (Sum.inr k) := by
            simpa [hs] using (e.apply_symm_apply i).symm
          cases hc : e.symm j with
          | inl l =>
              have hj : j = e (Sum.inl l) := by
                simpa [hc] using (e.apply_symm_apply j).symm
              subst i
              subst j
              simp [P, w, e, h5FlatIndex, Matrix.reindex_apply,
                Matrix.vandermonde_apply]
          | inr l =>
              have hj : j = e (Sum.inr l) := by
                simpa [hc] using (e.apply_symm_apply j).symm
              subst i
              subst j
              simp [P, w, e, h5FlatIndex, Matrix.reindex_apply,
                Matrix.vandermonde_apply]] at hdet
    rw [← hdet, ← vContourVandermonde_eq_det]
  rw [show (Matrix.of fun (b : Fin (4 * n) ⊕ Fin (5 * n))
        (c : Fin (4 * n) ⊕ Fin (5 * n)) =>
      (Sum.elim z v b) ^ (h5ColumnIndex c)) = A by rfl]
  rw [hfactor, Matrix.det_mul, Matrix.det_diagonal, hPdet]
  rw [show Literal.vContourVandermonde (Fin.append z v) =
      Literal.vContourVandermonde z * Literal.vContourVandermonde v *
        (∏ d : Fin (4 * n), ∏ b : Fin (5 * n), (v b - z d)) by
      rw [vContourVandermonde_eq_det, Matrix.det_vandermonde,
        vContourVandermonde_eq_det z, vContourVandermonde_eq_det v,
        Matrix.det_vandermonde, Matrix.det_vandermonde]
      exact P0.CauchyDeterminant.vandermonde_append_product z v]
  have hprod :
      (∏ i : Fin (4 * n) ⊕ Fin (5 * n), (Sum.elim z v i) ^ n) =
        (∏ d : Fin (4 * n), z d ^ n) *
          (∏ b : Fin (5 * n), v b ^ n) := by
    simp
  rw [hprod]
  ring



theorem v13_D_z_eval (q n : ℕ) (z : Fin (4*n) → ℂ)
    (hz : ∀ d, z d ≠ 0) :
    (Matrix.of fun (k : Fin (4*n)) (d : Fin (4*n)) =>
      (-(q : ℂ)) ^ (2*n + (k : ℕ)) *
        z d ^ (-(2*n + (k : ℕ) : ℤ) - 1)).det =
      (-1 : ℂ) ^ (Nat.choose (4*n) 2) *
        (-(q : ℂ)) ^ (∑ k : Fin (4*n), (2*n + (k : ℕ))) *
        Literal.vContourVandermonde z *
        (∏ d : Fin (4*n), z d ^ (-(6*n : ℤ))) := by
  classical
  have hcount (m : ℕ) :
      (∑ i : Fin m, (Finset.Ioi i).card) = Nat.choose m 2 := by
    induction m with
    | zero => simp
    | succ m ih =>
        rw [Fin.sum_univ_succ]
        have htail :
            (∑ i : Fin m, (Finset.Ioi i.succ).card) =
              ∑ i : Fin m, (Finset.Ioi i).card := by
          apply Finset.sum_congr rfl
          intro i hi
          simp only [Fin.card_Ioi, Fin.val_succ]
          omega
        rw [htail, ih]
        simpa [Fin.card_Ioi] using (Nat.choose_succ_succ m 1).symm

  let W : Matrix (Fin (4*n)) (Fin (4*n)) ℂ :=
    (Matrix.projVandermonde (fun _ : Fin (4*n) => (1 : ℂ)) z).transpose
  have hW : W.det =
      (-1 : ℂ) ^ (Nat.choose (4*n) 2) *
        Literal.vContourVandermonde z := by
    dsimp only [W]
    rw [Matrix.det_transpose, Matrix.det_projVandermonde,
      vContourVandermonde_eq_det, Matrix.det_vandermonde]
    simp only [one_mul]
    calc
      (∏ i : Fin (4*n), ∏ j ∈ Finset.Ioi i, (z i - z j)) =
          ∏ i : Fin (4*n), ((-1 : ℂ) ^ (Finset.Ioi i).card *
            (∏ j ∈ Finset.Ioi i, (z j - z i))) := by
        apply Finset.prod_congr rfl
        intro i hi
        simpa only [neg_sub] using
          (Finset.prod_neg (s := Finset.Ioi i)
            (fun j : Fin (4*n) => z j - z i))
      _ = (-1 : ℂ) ^ (Nat.choose (4*n) 2) *
          (∏ i : Fin (4*n), ∏ j ∈ Finset.Ioi i, (z j - z i)) := by
        rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hcount]

  have hentry (k d : Fin (4*n)) :
      z d ^ (-(2*n + (k : ℕ) : ℤ) - 1) =
        z d ^ (-(6*n : ℤ)) * z d ^ k.rev.val := by
    have he :
        -(2*n + (k : ℕ) : ℤ) - 1 = -(6*n : ℤ) + (k.rev.val : ℤ) := by
      have hk := k.isLt
      dsimp only [Fin.rev]
      omega
    rw [he, zpow_add₀ (hz d), zpow_natCast]

  have hfactor :
      (Matrix.of fun (k : Fin (4*n)) (d : Fin (4*n)) =>
        (-(q : ℂ)) ^ (2*n + (k : ℕ)) *
          z d ^ (-(2*n + (k : ℕ) : ℤ) - 1)) =
      Matrix.of fun (k : Fin (4*n)) (d : Fin (4*n)) =>
        (-(q : ℂ)) ^ (2*n + (k : ℕ)) *
          (z d ^ (-(6*n : ℤ)) * W k d) := by
    ext k d
    simp only [Matrix.of_apply]
    rw [hentry]
    simp [W, Matrix.projVandermonde_apply]

  let C : Matrix (Fin (4*n)) (Fin (4*n)) ℂ :=
    Matrix.of fun k d => z d ^ (-(6*n : ℤ)) * W k d
  have hC : C.det =
      (∏ d : Fin (4*n), z d ^ (-(6*n : ℤ))) * W.det := by
    dsimp [C]
    exact Matrix.det_mul_row (fun d => z d ^ (-(6*n : ℤ))) W
  calc
    (Matrix.of fun (k : Fin (4*n)) (d : Fin (4*n)) =>
        (-(q : ℂ)) ^ (2*n + (k : ℕ)) *
          z d ^ (-(2*n + (k : ℕ) : ℤ) - 1)).det =
      (∏ k : Fin (4*n), (-(q : ℂ)) ^ (2*n + (k : ℕ))) * C.det := by
        rw [hfactor]
        simpa [C] using
          (Matrix.det_mul_column
            (fun k : Fin (4*n) => (-(q : ℂ)) ^ (2*n + (k : ℕ))) C)
    _ = (∏ k : Fin (4*n), (-(q : ℂ)) ^ (2*n + (k : ℕ))) *
          ((∏ d : Fin (4*n), z d ^ (-(6*n : ℤ))) * W.det) := by rw [hC]
    _ = (-1 : ℂ) ^ (Nat.choose (4*n) 2) *
          (-(q : ℂ)) ^ (∑ k : Fin (4*n), (2*n + (k : ℕ))) *
          Literal.vContourVandermonde z *
          (∏ d : Fin (4*n), z d ^ (-(6*n : ℤ))) := by
        rw [hW, Finset.prod_pow_eq_pow_sum]
        ac_rfl


end

end Li2Lean.V
