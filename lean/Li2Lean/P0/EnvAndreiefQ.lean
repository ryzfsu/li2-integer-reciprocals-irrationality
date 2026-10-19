/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.EnvPinnedQ
import Li2Lean.P0.EnvAndreief

/-!
# Andreief antisymmetrization of the contour rows and the pointwise envelope

For the reduced matrix `pinnedDQ` (contour rows `I_m \ S`, frequency rows `R`, columns
`J_m \ S`), `continuous_andreief` gives

  `d! det pinnedDQ = ∫ det(φ_{a_k}(u_l)) · det[ψ(u_l); K_{R,J\S}] dμ^d`,

and pointwise `|det(φ_{a_k}(u_l))| = ∏_l |F(z_l)| |z_l'|/(2π) · |det K_{I\S,-Z}|`,
`|det[ψ(u_l); K_{R,J\S}]| = |det K_{(-Z,R),J\S}|` (paper v13 `p0-analytic.tex` ll. 41-58,
the absolute integrand `Q_m` with measure `∏|dz|/(2π)` and factor `1/d!`).
-/

open Finset MeasureTheory

namespace Li2Lean.P0.Env

noncomputable section
open Li2Lean.P0.PositiveBase

/-- The contour row coefficient matrix `(φ_{a_k}(u_l))`. -/
def phiMatQ (q m : ℕ) (S : Finset ℕ) (hSI : S ⊆ Iset m) (u : Fin (m - S.card) → ℝ) :
    Matrix (Fin (m - S.card)) (Fin (m - S.card)) ℂ :=
  Matrix.of fun k l => qPhiC q m (aLab m S hSI k) (u l)

/-- The matrix `[ψ(u_l); K_{R,J\S}]`. -/
def psiMatQ (q m : ℕ) (S : Finset ℕ) (h4 : 4 ∣ m) (hSI : S ⊆ Iset m) (R : Fin m → ℕ)
    (u : Fin (m - S.card) → ℝ) :
    Matrix (Fin (m - S.card) ⊕ Fin m) (Fin (m - S.card) ⊕ Fin m) ℂ :=
  rowRepl (pinnedDQ q m S h4 hSI R) (fun l y => qPsiC m (jLab m S h4 hSI y) (u l))


theorem pinnedD_andreiefQ (q m : ℕ) (hm : 0 < m) (h4 : 4 ∣ m) (S : Finset ℕ) (hSI : S ⊆ Iset m)
    (R : Fin m → ℕ) :
    (∫ u : Fin (m - S.card) → ℝ, (phiMatQ q m S hSI u).det * (psiMatQ q m S h4 hSI R u).det
        ∂(Measure.pi fun _ => contourParameterMeasure)) =
      ((m - S.card).factorial : ℂ) * (pinnedDQ q m S h4 hSI R).det := by
  have haLab : ∀ k, aLab m S hSI k ≤ 2 * m := fun k => by
    have := (mem_Iset_iff m _).mp (Finset.mem_sdiff.mp (aLab_mem m S hSI k)).1
    omega
  have hjLab : ∀ y, jLab m S h4 hSI y ≤ 2 * m := fun y => (jLab_lt m S h4 hSI y).le
  exact continuous_andreief contourParameterMeasure (pinnedDQ q m S h4 hSI R)
    (fun k u => qPhiC q m (aLab m S hSI k) u) (fun u y => qPsiC m (jLab m S h4 hSI y) u)
    (fun k y => integrable_qPhiC_qPsiC q m hm (aLab m S hSI k) (jLab m S h4 hSI y) (haLab k) (hjLab y))
    (fun k y => by
      simp only [pinnedDQ, Matrix.of_apply, Sum.elim_inl]
      exact qContPart_eq_integral q m hm (aLab m S hSI k) (jLab m S h4 hSI y) (haLab k) (hjLab y) (dvd_trans (by norm_num) h4))

theorem norm_det_phiMatQ (q m : ℕ) (S : Finset ℕ) (hSI : S ⊆ Iset m)
    (u : Fin (m - S.card) → ℝ) :
    ‖(phiMatQ q m S hSI u).det‖ =
      (∏ l, ‖p0EntireQ (q : ℤ) (m / 2) (p0EllipsePoint m (u l))‖ * contourArcDensity m (u l)) *
        ‖contourQLeftMinor S hSI (fun l => p0EllipsePoint m (u l))‖ := by
  set c : Fin (m - S.card) → ℂ := fun l =>
    (Complex.ofReal (2 * Real.pi) * Complex.I)⁻¹ * p0EntireQ (q : ℤ) (m / 2) (p0EllipsePoint m (u l)) *
      p0EllipseTangent m (u l)
  have h : phiMatQ q m S hSI u = Matrix.of fun k l => c l *
      (Matrix.of fun k l => (((aLab m S hSI k : ℕ) : ℂ) + -p0EllipsePoint m (u l))⁻¹ :
        Matrix (Fin (m - S.card)) (Fin (m - S.card)) ℂ) k l := by
    ext k l
    simp only [phiMatQ, qPhiC, Matrix.of_apply, c]
    rw [show ((aLab m S hSI k : ℕ) : ℂ) + -p0EllipsePoint m (u l) =
      -(p0EllipsePoint m (u l) - ((aLab m S hSI k : ℕ) : ℂ)) by ring, inv_neg]
    ring
  rw [h, Matrix.det_mul_row, norm_mul, contourQLeftMinor_eq, norm_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro l _
  simp only [c, norm_mul, norm_twoPiI_inv, contourArcDensity]
  ring

theorem norm_det_psiMatQ (q m : ℕ) (S : Finset ℕ) (h4 : 4 ∣ m) (hSI : S ⊆ Iset m)
    (R : Fin m → ℕ) (hR : StrictMono R) (u : Fin (m - S.card) → ℝ) :
    ‖(psiMatQ q m S h4 hSI R u).det‖ =
      ‖(contourQMinors S h4 hSI R hR (fun l => p0EllipsePoint m (u l))).2.2‖ := by
  rw [contourQRight_eq]
  set rightM : Matrix (Fin ((m - S.card) + m)) (Fin ((m - S.card) + m)) ℂ :=
    Matrix.of fun i j : Fin ((m - S.card) + m) =>
        ((if hi : i.val < m - S.card then -(fun l => p0EllipsePoint m (u l)) ⟨i.val, hi⟩ else
            (R ⟨i.val - (m - S.card), by omega⟩ : ℂ)) +
          ((orderedElem (Jset m \ S)
            (Fin.cast (contourQJComplement_card S h4 hSI).symm j) : ℕ) : ℂ))⁻¹
  let sg : Fin (m - S.card) ⊕ Fin m → ℂ := Sum.elim (fun _ => -1) (fun _ => 1)
  have h : psiMatQ q m S h4 hSI R u = Matrix.of fun x y => sg x *
      (rightM.submatrix finSumFinEquiv finSumFinEquiv) x y := by
    ext x y
    rcases x with l | k
    · have hl : (finSumFinEquiv (Sum.inl l : Fin (m - S.card) ⊕ Fin m)).val < m - S.card := by
        simp
      simp only [psiMatQ, rowRepl, Matrix.of_apply, Sum.elim_inl, sg, Matrix.submatrix_apply,
        rightM, dif_pos hl, qPsiC, jLab]
      have hfin : (⟨(finSumFinEquiv (Sum.inl l : Fin (m - S.card) ⊕ Fin m)).val, hl⟩ :
          Fin (m - S.card)) = l := by ext; simp
      rw [hfin]
      rw [show -p0EllipsePoint m (u l) + ((orderedElem (Jset m \ S)
          (Fin.cast (contourQJComplement_card S h4 hSI).symm (finSumFinEquiv y)) : ℕ) : ℂ) =
          -(p0EllipsePoint m (u l) - ((orderedElem (Jset m \ S)
          (Fin.cast (contourQJComplement_card S h4 hSI).symm (finSumFinEquiv y)) : ℕ) : ℂ))
          by ring, inv_neg]
      ring
    · have hk : ¬ (finSumFinEquiv (Sum.inr k : Fin (m - S.card) ⊕ Fin m)).val < m - S.card := by
        simp
      simp only [psiMatQ, rowRepl, Matrix.of_apply, Sum.elim_inr, sg, Matrix.submatrix_apply,
        rightM, dif_neg hk, pinnedDQ, cauchyKernel, jLab]
      have hfin : (⟨(finSumFinEquiv (Sum.inr k : Fin (m - S.card) ⊕ Fin m)).val - (m - S.card),
          by simp⟩ : Fin m) = k := by ext; simp
      rw [hfin]
      push_cast
      ring
  have hsg : ∀ x, ‖sg x‖ = 1 := by rintro (_ | _) <;> simp [sg]
  rw [h, Matrix.det_mul_column, Matrix.det_submatrix_equiv_self, norm_mul, norm_prod,
    Finset.prod_eq_one (fun x _ => hsg x), one_mul]

/-- The pointwise envelope of the Andreief integrand. -/
theorem norm_andreief_integrandQ (q m : ℕ) (S : Finset ℕ) (h4 : 4 ∣ m) (hSI : S ⊆ Iset m)
    (R : Fin m → ℕ) (hR : StrictMono R) (u : Fin (m - S.card) → ℝ) :
    ‖(phiMatQ q m S hSI u).det * (psiMatQ q m S h4 hSI R u).det‖ =
      (∏ l, ‖p0EntireQ (q : ℤ) (m / 2) (p0EllipsePoint m (u l))‖) *
        ‖contourQLeftMinor S hSI (fun l => p0EllipsePoint m (u l))‖ *
        ‖(contourQMinors S h4 hSI R hR (fun l => p0EllipsePoint m (u l))).2.2‖ *
        ∏ l, contourArcDensity m (u l) := by
  rw [norm_mul, norm_det_phiMatQ, norm_det_psiMatQ q m S h4 hSI R hR, Finset.prod_mul_distrib]
  ring

/-- Contour bound for the reduced matrix. -/
theorem norm_det_pinnedD_leQ (q m : ℕ) (hm : 0 < m) (h4 : 4 ∣ m) (S : Finset ℕ)
    (hSI : S ⊆ Iset m) (R : Fin m → ℕ) (hR : StrictMono R) :
    ‖(pinnedDQ q m S h4 hSI R).det‖ ≤ ((m - S.card).factorial : ℝ)⁻¹ *
      ∫ u : Fin (m - S.card) → ℝ,
        (∏ l, ‖p0EntireQ (q : ℤ) (m / 2) (p0EllipsePoint m (u l))‖) *
        ‖contourQLeftMinor S hSI (fun l => p0EllipsePoint m (u l))‖ *
        ‖(contourQMinors S h4 hSI R hR (fun l => p0EllipsePoint m (u l))).2.2‖ *
        ∏ l, contourArcDensity m (u l)
      ∂(ContourKit.productMeasure contourParameterMeasure) := by
  have hA := pinnedD_andreiefQ q m hm h4 S hSI R
  have hfac : ((m - S.card).factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero _
  have hdet : (pinnedDQ q m S h4 hSI R).det = ((m - S.card).factorial : ℂ)⁻¹ *
      ∫ u : Fin (m - S.card) → ℝ, (phiMatQ q m S hSI u).det * (psiMatQ q m S h4 hSI R u).det
        ∂(Measure.pi fun _ => contourParameterMeasure) := by
    rw [hA]; field_simp
  rw [hdet, norm_mul, norm_inv, Complex.norm_natCast]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  unfold ContourKit.productMeasure
  apply integral_congr_ae
  filter_upwards [] with u
  exact norm_andreief_integrandQ q m S h4 hSI R hR u

end

end Li2Lean.P0.Env
