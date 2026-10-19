/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B4.RectangleDoublePoleVendor
import Li2Lean.Vendor.PNT.ResidueCalcOnRectangles

/-!
# Finite principal-part rectangle identity

This is the residue algebra needed by the v13 Hermite--Pade contour route
(`hp-tail.tex:256-410`).  The caller supplies the already identified
Hermite partial-fraction boundary decomposition.  Simple poles are evaluated
with the vendored PrimeNumberTheoremAnd rectangle theorem; double poles use
the explicit FTC lemma in `RectangleDoublePole`.  No general residue theorem
or unrelated irrationality construction is used here.
-/

open Complex Set MeasureTheory intervalIntegral Topology

namespace Li2Lean.B4.RectanglePrincipalParts

noncomputable section

def doublePart (u p : ℕ → ℂ) (j : ℕ) : ℂ → ℂ :=
  fun s => u j / (s - p j) ^ 2

def simplePart (v p : ℕ → ℂ) (j : ℕ) : ℂ → ℂ :=
  fun s => v j / (s - p j)

def principalPart (u v p : ℕ → ℂ) (j : ℕ) : ℂ → ℂ :=
  doublePart u p j + simplePart v p j

def principalParts (S : Finset ℕ) (u v p : ℕ → ℂ) : ℂ → ℂ :=
  fun s => ∑ j ∈ S, principalPart u v p j s

private lemma rectangleIntegral'_add
    {f g : ℂ → ℂ} {z w : ℂ}
    (hf : RectangleBorderIntegrable f z w)
    (hg : RectangleBorderIntegrable g z w) :
    RectangleIntegral' (f + g) z w =
      RectangleIntegral' f z w + RectangleIntegral' g z w := by
  rw [RectangleIntegral'.eq_1, RectangleBorderIntegrable.add hf hg,
    smul_add, ← RectangleIntegral'.eq_1, ← RectangleIntegral'.eq_1]

private lemma rectangleBorderIntegrable_add
    {f g : ℂ → ℂ} {z w : ℂ}
    (hf : RectangleBorderIntegrable f z w)
    (hg : RectangleBorderIntegrable g z w) :
    RectangleBorderIntegrable (f + g) z w :=
  ⟨hf.1.add hg.1, hf.2.1.add hg.2.1,
    hf.2.2.1.add hg.2.2.1, hf.2.2.2.add hg.2.2.2⟩

private lemma rectangleIntegral'_doublePart_eq_zero
    {c p z w : ℂ}
    (hz_re : z.re ≠ p.re) (hw_re : w.re ≠ p.re)
    (hz_im : z.im ≠ p.im) (hw_im : w.im ≠ p.im) :
    RectangleIntegral' (fun s => c / (s - p) ^ 2) z w = 0 := by
  rw [RectangleIntegral'.eq_1,
    Li2Lean.B4.RectangleDoublePole.vendor_rectangleIntegral_doublePole_eq_zero
      c p z w hz_re hw_re hz_im hw_im, smul_zero]

private lemma rectangleIntegral'_principalPart_eq_simple
    {u v p : ℕ → ℂ} {j : ℕ} {z w : ℂ}
    (hz_re : z.re ≠ (p j).re) (hw_re : w.re ≠ (p j).re)
    (hz_im : z.im ≠ (p j).im) (hw_im : w.im ≠ (p j).im)
    (hz_le : z.re ≤ w.re) (hi_le : z.im ≤ w.im)
    (hp : Rectangle z w ∈ 𝓝 (p j))
    (hdoubleInt : RectangleBorderIntegrable (doublePart u p j) z w)
    (hsimpleInt : RectangleBorderIntegrable (simplePart v p j) z w) :
    RectangleIntegral' (principalPart u v p j) z w = v j := by
  have hdouble := rectangleIntegral'_doublePart_eq_zero
    (c := u j) (p := p j) (z := z) (w := w)
    hz_re hw_re hz_im hw_im
  have hsimple := ResidueTheoremInRectangle hz_le hi_le hp
    (c := v j) (p := p j)
  have hadd : principalPart u v p j =
      (doublePart u p j) + (simplePart v p j) := rfl
  rw [hadd]
  rw [rectangleIntegral'_add hdoubleInt hsimpleInt]
  have hdouble' : RectangleIntegral' (doublePart u p j) z w = 0 := by
    change RectangleIntegral' (fun s => u j / (s - p j) ^ 2) z w = 0
    exact hdouble
  have hsimple' : RectangleIntegral' (simplePart v p j) z w = v j := by
    change RectangleIntegral' (fun s => v j / (s - p j)) z w = v j
    exact hsimple
  rw [hdouble', hsimple', zero_add]

private lemma principalParts_integrable
    (S : Finset ℕ) (u v p : ℕ → ℂ) (z w : ℂ)
    (hdoubleInt : ∀ j ∈ S,
      RectangleBorderIntegrable (doublePart u p j) z w)
    (hsimpleInt : ∀ j ∈ S,
      RectangleBorderIntegrable (simplePart v p j) z w) :
    RectangleBorderIntegrable (principalParts S u v p) z w := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simp [principalParts, RectangleBorderIntegrable]
  | @insert j S hj ih =>
      have hdouble := hdoubleInt j (Finset.mem_insert_self j S)
      have hsimple := hsimpleInt j (Finset.mem_insert_self j S)
      have hterm : RectangleBorderIntegrable (principalPart u v p j) z w := by
        exact rectangleBorderIntegrable_add hdouble hsimple
      have hdoubleS : ∀ k ∈ S,
          RectangleBorderIntegrable (doublePart u p k) z w := by
        intro k hk
        exact hdoubleInt k (Finset.mem_insert_of_mem hk)
      have hsimpleS : ∀ k ∈ S,
          RectangleBorderIntegrable (simplePart v p k) z w := by
        intro k hk
        exact hsimpleInt k (Finset.mem_insert_of_mem hk)
      have ih' := ih hdoubleS hsimpleS
      have hsum : principalParts (insert j S) u v p =
          principalPart u v p j + principalParts S u v p := by
        funext s
        simp [principalParts, Finset.sum_insert, hj]
      rw [hsum]
      exact rectangleBorderIntegrable_add hterm ih'

theorem rectangleIntegral'_principalParts_eq_sum
    (S : Finset ℕ) (u v p : ℕ → ℂ) (z w : ℂ)
    (hz_le : z.re ≤ w.re) (hi_le : z.im ≤ w.im)
    (hgeom : ∀ j ∈ S, Rectangle z w ∈ 𝓝 (p j))
    (hdoubleCorner : ∀ j ∈ S,
      z.re ≠ (p j).re ∧ w.re ≠ (p j).re ∧
        z.im ≠ (p j).im ∧ w.im ≠ (p j).im)
    (hdoubleInt : ∀ j ∈ S,
      RectangleBorderIntegrable (doublePart u p j) z w)
    (hsimpleInt : ∀ j ∈ S,
      RectangleBorderIntegrable (simplePart v p j) z w) :
    RectangleIntegral' (principalParts S u v p) z w =
      ∑ j ∈ S, v j := by
  classical
  revert hgeom hdoubleCorner hdoubleInt hsimpleInt
  induction S using Finset.induction_on with
  | empty =>
      intro hgeom hdoubleCorner hdoubleInt hsimpleInt
      have hzero : principalParts ∅ u v p = 0 := by
        funext s
        simp [principalParts]
      rw [hzero]
      simp [RectangleIntegral, HIntegral, VIntegral]
  | @insert j S hj ih =>
      intro hgeom hdoubleCorner hdoubleInt hsimpleInt
      have hdouble := hdoubleInt j (Finset.mem_insert_self j S)
      have hsimple := hsimpleInt j (Finset.mem_insert_self j S)
      have htermInt : RectangleBorderIntegrable (principalPart u v p j) z w :=
        rectangleBorderIntegrable_add hdouble hsimple
      have hdoubleS : ∀ k ∈ S,
          RectangleBorderIntegrable (doublePart u p k) z w := by
        intro k hk
        exact hdoubleInt k (Finset.mem_insert_of_mem hk)
      have hsimpleS : ∀ k ∈ S,
          RectangleBorderIntegrable (simplePart v p k) z w := by
        intro k hk
        exact hsimpleInt k (Finset.mem_insert_of_mem hk)
      have hgeomj := hgeom j (Finset.mem_insert_self j S)
      have hcornerj := hdoubleCorner j (Finset.mem_insert_self j S)
      have hterm := rectangleIntegral'_principalPart_eq_simple
        (u := u) (v := v) (p := p) (j := j) (z := z) (w := w)
        hcornerj.1 hcornerj.2.1 hcornerj.2.2.1 hcornerj.2.2.2
        hz_le hi_le hgeomj hdouble hsimple
      have hrest := ih
        (fun k hk => hgeom k (Finset.mem_insert_of_mem hk))
        (fun k hk => hdoubleCorner k (Finset.mem_insert_of_mem hk))
        hdoubleS hsimpleS
      have hsumInt := principalParts_integrable S u v p z w
        hdoubleS hsimpleS
      have hadd := rectangleIntegral'_add htermInt hsumInt
      have hsum : principalParts (insert j S) u v p =
          principalPart u v p j + principalParts S u v p := by
        funext s
        simp [principalParts, Finset.sum_insert, hj]
      rw [hsum, hadd, hterm, hrest]
      simp [Finset.sum_insert, hj]

/-- Boundary decomposition form of the v13 contour identity.  The
`hdecomp` hypothesis is the Hermite partial-fraction identity on the rectangle
border (`hp-tail.tex:256-266`); the proof then applies Cauchy--Goursat to its
entire remainder, the explicit double-pole FTC cancellation, and the
simple-pole rectangle theorem. -/
theorem rectangleIntegral'_of_boundary_decomposition
    (S : Finset ℕ) (F E : ℂ → ℂ) (u v p : ℕ → ℂ) (z w : ℂ)
    (hdecomp : Set.EqOn F (E + principalParts S u v p) (RectangleBorder z w))
    (hE : HolomorphicOn E (Rectangle z w))
    (hEInt : RectangleBorderIntegrable E z w)
    (hz_le : z.re ≤ w.re) (hi_le : z.im ≤ w.im)
    (hgeom : ∀ j ∈ S, Rectangle z w ∈ 𝓝 (p j))
    (hdoubleCorner : ∀ j ∈ S,
      z.re ≠ (p j).re ∧ w.re ≠ (p j).re ∧
        z.im ≠ (p j).im ∧ w.im ≠ (p j).im)
    (hdoubleInt : ∀ j ∈ S,
      RectangleBorderIntegrable (doublePart u p j) z w)
    (hsimpleInt : ∀ j ∈ S,
      RectangleBorderIntegrable (simplePart v p j) z w) :
    RectangleIntegral' F z w = ∑ j ∈ S, v j := by
  rw [RectangleIntegral'_congr hdecomp]
  have hpartsInt := principalParts_integrable S u v p z w
    hdoubleInt hsimpleInt
  have hadd := rectangleIntegral'_add hEInt hpartsInt
  have hzero : RectangleIntegral' E z w = 0 := by
    rw [RectangleIntegral'.eq_1,
      hE.vanishesOnRectangle (by rfl), smul_zero]
  have hparts := rectangleIntegral'_principalParts_eq_sum S u v p z w
    hz_le hi_le hgeom hdoubleCorner hdoubleInt hsimpleInt
  rw [hadd, hzero, hparts, zero_add]

end

end Li2Lean.B4.RectanglePrincipalParts
