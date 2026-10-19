/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.Q11Reference
import Li2Lean.P0.Q11ContourRows
import Li2Lean.P0.CA.Contour.Arith
import Li2Lean.P0.CA.Contour.Checker
import Li2Lean.P0.CA.Contour.Taylor

namespace Li2Lean.P0.Q11Data
open Li2Lean.P0.CA.Contour

noncomputable def q11Wform (theta : Real) : Real := q11Weta (gammaPoint theta)
noncomputable def q11W1 (theta : Real) : Real := deriv q11Wform theta
noncomputable def q11W2 (theta : Real) : Real := deriv q11W1 theta

theorem q11_local_taylor_lower
    {a b theta theta0 M2 : Real}
    (hab : Set.Icc a b ⊆ Set.Ioo 0 Real.pi)
    (htheta : theta ∈ Set.Icc a b)
    (h0 : theta0 ∈ Set.Icc a b)
    (hM2_nonneg : 0 ≤ M2)
    (hderiv0 : ∀ x ∈ Set.Ioo 0 Real.pi,
      HasDerivAt q11Wform (q11W1 x) x)
    (hderiv1 : ∀ x ∈ Set.Ioo 0 Real.pi,
      HasDerivAt q11W1 (q11W2 x) x)
    (hW2_local : ∀ x ∈ Set.Icc a b, |q11W2 x| ≤ M2) :
    q11Wform theta0 + q11W1 theta0 * (theta - theta0) -
        (M2 / 2) * (theta - theta0)^2 ≤ q11Wform theta := by
  let g : Real → Real := fun x =>
    q11Wform x - q11Wform theta0 - q11W1 theta0 * (x - theta0) +
      (M2 / 2) * (x - theta0)^2
  let gp : Real → Real := fun x =>
    q11W1 x - q11W1 theta0 + M2 * (x - theta0)
  have hsub : ∀ {x y : Real}, x ∈ Set.Icc a b → y ∈ Set.Icc a b →
      Set.Icc x y ⊆ Set.Ioo 0 Real.pi := by
    intro x y hx hy z hz
    exact hab ⟨le_trans hx.1 hz.1, le_trans hz.2 hy.2⟩
  have hg_deriv : ∀ x ∈ Set.Ioo 0 Real.pi, HasDerivAt g (gp x) x := by
    intro x hx
    have h1 := hderiv0 x hx
    have h2 := ((hasDerivAt_id x).sub_const theta0).const_mul (q11W1 theta0)
    have h3 := (((hasDerivAt_id x).sub_const theta0).pow 2).const_mul (M2 / 2)
    have h := ((h1.sub_const (q11Wform theta0)).sub h2).add h3
    refine h.congr_deriv ?_
    simp only [gp, id]
    ring
  have hg0 : g theta0 = 0 := by simp [g]
  have hLip : ∀ {x y : Real}, x ∈ Set.Icc a b → y ∈ Set.Icc a b →
      |q11W1 x - q11W1 y| ≤ M2 * |x - y| := by
    intro x y hx hy
    have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := q11W1) (f' := q11W2) (C := M2) (s := Set.Icc a b)
      (fun z hz => (hderiv1 z (hab hz)).hasDerivWithinAt)
      (fun z hz => by
        simpa only [Real.norm_eq_abs] using hW2_local z hz)
      (convex_Icc a b) hy hx
    simpa only [Real.norm_eq_abs] using h
  rcases le_total theta0 theta with hle | hge
  · have hD := hsub h0 htheta
    have hmono : MonotoneOn g (Set.Icc theta0 theta) := by
      apply monotoneOn_of_hasDerivWithinAt_nonneg (f' := gp)
        (convex_Icc theta0 theta)
      · intro x hx
        exact (hg_deriv x (hD hx)).continuousAt.continuousWithinAt
      · intro x hx
        rw [interior_Icc] at hx
        exact (hg_deriv x (hD (Set.Ioo_subset_Icc_self hx))).hasDerivWithinAt
      · intro x hx
        rw [interior_Icc] at hx
        have hxAB : x ∈ Set.Icc a b :=
          (Set.Icc_subset_Icc h0.1 htheta.2) (Set.Ioo_subset_Icc_self hx)
        have hL := hLip hxAB h0
        have hdist : |x - theta0| = x - theta0 :=
          abs_of_nonneg (by linarith [hx.1])
        rw [hdist] at hL
        have hneg := neg_abs_le (q11W1 x - q11W1 theta0)
        dsimp [gp]
        linarith
    have h := hmono ⟨le_rfl, hle⟩ ⟨hle, le_rfl⟩ hle
    dsimp [g] at h
    linarith
  · have hD := hsub htheta h0
    have hanti : AntitoneOn g (Set.Icc theta theta0) := by
      apply antitoneOn_of_hasDerivWithinAt_nonpos (f' := gp)
        (convex_Icc theta theta0)
      · intro x hx
        exact (hg_deriv x (hD hx)).continuousAt.continuousWithinAt
      · intro x hx
        rw [interior_Icc] at hx
        exact (hg_deriv x (hD (Set.Ioo_subset_Icc_self hx))).hasDerivWithinAt
      · intro x hx
        rw [interior_Icc] at hx
        have hxAB : x ∈ Set.Icc a b :=
          (Set.Icc_subset_Icc htheta.1 h0.2) (Set.Ioo_subset_Icc_self hx)
        have hL := hLip hxAB h0
        have hdist : |x - theta0| = -(x - theta0) :=
          abs_of_nonpos (by linarith [hx.2])
        rw [hdist] at hL
        have hpos := le_abs_self (q11W1 x - q11W1 theta0)
        dsimp [gp]
        linarith
    have h := hanti ⟨le_rfl, hge⟩ ⟨hge, le_rfl⟩ hge
    dsimp [g] at h
    linarith

end Li2Lean.P0.Q11Data

#print axioms Li2Lean.P0.Q11Data.q11_local_taylor_lower
