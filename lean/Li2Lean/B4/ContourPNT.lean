/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Mathlib
import Li2Lean.Kit.PNTAdapter
import Li2Lean.B4.ResidueTailAlgebra

/-!
  Small B4 contour/PNT interfaces for the v13 Hermite--Padé tail.

  The finite-boundary facts here are independent of the analytic saddle
  producer.  In particular, an infinite support line is never identified
  with a finite contour boundary: the phase bound remains an explicit input.
-/

open MeasureTheory
open Set
open Filter Topology

namespace Li2Lean.B4

noncomputable section

open Li2Lean.B4.Residues

/-- The four sides of a closed complex rectangle. -/
def hpTailRectangleBoundary (left right bottom top : ℝ) : Set ℂ :=
    ((fun y : ℝ => (left : ℂ) + Complex.I * (y : ℂ)) '' Icc bottom top) ∪
    ((fun y : ℝ => (right : ℂ) + Complex.I * (y : ℂ)) '' Icc bottom top) ∪
    ((fun x : ℝ => (x : ℂ) + Complex.I * (bottom : ℂ)) '' Icc left right) ∪
    ((fun x : ℝ => (x : ℂ) + Complex.I * (top : ℂ)) '' Icc left right)

private lemma hpTail_left_edge_continuous (left : ℝ) :
    Continuous (fun y : ℝ => (left : ℂ) + Complex.I * (y : ℂ)) := by
  fun_prop

private lemma hpTail_right_edge_continuous (right : ℝ) :
    Continuous (fun y : ℝ => (right : ℂ) + Complex.I * (y : ℂ)) := by
  fun_prop

private lemma hpTail_bottom_edge_continuous (bottom : ℝ) :
    Continuous (fun x : ℝ => (x : ℂ) + Complex.I * (bottom : ℂ)) := by
  fun_prop

private lemma hpTail_top_edge_continuous (top : ℝ) :
    Continuous (fun x : ℝ => (x : ℂ) + Complex.I * (top : ℂ)) := by
  fun_prop

lemma hpTailRectangleBoundary_isCompact
    {left right bottom top : ℝ} (hlr : left ≤ right) (hbt : bottom ≤ top) :
    IsCompact (hpTailRectangleBoundary left right bottom top) := by
  have hleft :
      IsCompact ((fun y : ℝ => (left : ℂ) + Complex.I * (y : ℂ)) '' Icc bottom top) :=
    (isCompact_Icc (a := bottom) (b := top)).image
      (hpTail_left_edge_continuous left)
  have hright :
      IsCompact ((fun y : ℝ => (right : ℂ) + Complex.I * (y : ℂ)) '' Icc bottom top) :=
    (isCompact_Icc (a := bottom) (b := top)).image
      (hpTail_right_edge_continuous right)
  have hbottom :
      IsCompact ((fun x : ℝ => (x : ℂ) + Complex.I * (bottom : ℂ)) '' Icc left right) :=
    (isCompact_Icc (a := left) (b := right)).image
      (hpTail_bottom_edge_continuous bottom)
  have htop :
      IsCompact ((fun x : ℝ => (x : ℂ) + Complex.I * (top : ℂ)) '' Icc left right) :=
    (isCompact_Icc (a := left) (b := right)).image
      (hpTail_top_edge_continuous top)
  exact hleft.union hright |>.union hbottom |>.union htop

lemma hpTailRectangleBoundary_nonempty
    {left right bottom top : ℝ} (hlr : left ≤ right) (hbt : bottom ≤ top) :
    (hpTailRectangleBoundary left right bottom top).Nonempty := by
  unfold hpTailRectangleBoundary
  have hleft :
      ((fun y : ℝ => (left : ℂ) + Complex.I * (y : ℂ)) '' Icc bottom top).Nonempty :=
    ⟨(left : ℂ) + Complex.I * (bottom : ℂ),
      ⟨bottom, ⟨le_rfl, hbt⟩, rfl⟩⟩
  exact hleft.mono (by intro z hz; exact Or.inl (Or.inl (Or.inl hz)))

/-- A continuous real phase attains a maximum on the finite boundary. -/
lemma hpTailRectangleBoundary_exists_max
    {left right bottom top : ℝ} (hlr : left ≤ right) (hbt : bottom ≤ top)
    (phase : ℂ → ℝ)
    (hphase : ContinuousOn phase (hpTailRectangleBoundary left right bottom top)) :
    ∃ z ∈ hpTailRectangleBoundary left right bottom top,
      ∀ w ∈ hpTailRectangleBoundary left right bottom top, phase w ≤ phase z := by
  have hcompact := hpTailRectangleBoundary_isCompact hlr hbt
  have hnonempty := hpTailRectangleBoundary_nonempty hlr hbt
  obtain ⟨z, hz, hmax⟩ := hcompact.exists_isMaxOn hnonempty hphase
  exact ⟨z, hz, fun w hw => hmax hw⟩

/-- The finite contour phase certificate consumed by the tail estimate. -/
structure HpTailBoundaryPhaseCertificate
    (left right bottom top : ℝ) (phase : ℂ → ℝ) where
  bounds : left ≤ right ∧ bottom ≤ top
  continuous : ContinuousOn phase (hpTailRectangleBoundary left right bottom top)
  maximum : ∃ z ∈ hpTailRectangleBoundary left right bottom top,
    ∀ w ∈ hpTailRectangleBoundary left right bottom top, phase w ≤ phase z

lemma HpTailBoundaryPhaseCertificate.max_value
    {left right bottom top : ℝ} {phase : ℂ → ℝ}
    (h : HpTailBoundaryPhaseCertificate left right bottom top phase) :
    ∃ z ∈ hpTailRectangleBoundary left right bottom top,
      ∀ w ∈ hpTailRectangleBoundary left right bottom top, phase w ≤ phase z :=
  h.maximum

/-- The four oriented edges of the residue rectangle. -/
inductive HpTailRectEdge
  | bottom | right | top | left
  deriving DecidableEq

/-- Counterclockwise affine parameterization of a rectangle with vertical
sides `left`, `right` and horizontal sides `bottom`, `top`. -/
def hpTailRectEdgeMap (left right bottom top : ℝ) : HpTailRectEdge → ℝ → ℂ
  | .bottom, t => ((left + (right - left) * t : ℝ) : ℂ)
      + (bottom : ℂ) * Complex.I
  | .right, t => (right : ℂ) + Complex.I * (((bottom + (top - bottom) * t) : ℝ) : ℂ)
  | .top, t => ((right - (right - left) * t : ℝ) : ℂ) + Complex.I * (top : ℂ)
  | .left, t => (left : ℂ) + Complex.I * (((top - (top - bottom) * t) : ℝ) : ℂ)

/-- Constant oriented velocity of each affine rectangle edge. -/
def hpTailRectEdgeVelocity (left right bottom top : ℝ) (e : HpTailRectEdge) : ℂ :=
  hpTailRectEdgeMap left right bottom top e 1 -
    hpTailRectEdgeMap left right bottom top e 0

/-- The four-edge complex contour integral, with each edge parameterized on
`[0,1]` in counterclockwise order. -/
def hpTailRectIntegral (left right bottom top : ℝ) (f : ℂ → ℂ) : ℂ :=
    (∫ t : ℝ in (0 : ℝ)..1,
      f (hpTailRectEdgeMap left right bottom top .bottom t) *
        hpTailRectEdgeVelocity left right bottom top .bottom) +
    (∫ t : ℝ in (0 : ℝ)..1,
      f (hpTailRectEdgeMap left right bottom top .right t) *
        hpTailRectEdgeVelocity left right bottom top .right) +
    (∫ t : ℝ in (0 : ℝ)..1,
      f (hpTailRectEdgeMap left right bottom top .top t) *
        hpTailRectEdgeVelocity left right bottom top .top) +
    (∫ t : ℝ in (0 : ℝ)..1,
      f (hpTailRectEdgeMap left right bottom top .left t) *
        hpTailRectEdgeVelocity left right bottom top .left)

/-- The literal numerator product in v13 `hp-tail.tex:14-18`. -/
def hpTailPhi (n : ℕ) (w : ℂ) : ℂ :=
  (∏ r ∈ Finset.Icc (n + 1) (3 * n + 1), (w - (r : ℂ))) /
    ∏ j ∈ Finset.range (n + 1), (w - (j : ℂ)) ^ 2

/-- The exponential kernel for the `+` branch in v13
`hp-tail.tex:257-265`; the `-` branch is obtained by conjugation. -/
def hpTailKernelPlus (q : ℕ) (n : ℕ) (w : ℂ) : ℂ :=
  hpTailPhi n w * Complex.exp
    ((-((Real.log (q : ℝ)) : ℂ) + (Real.pi : ℂ) * Complex.I) * w)

/-- The residue sum defining `F_n^+(-1/q)` from the explicit `B_n,C_n`
polynomials in `ResidueTailAlgebra`. -/
def hpTailBranchValuePlus (q n : ℕ) : ℂ :=
  let z : ℚ := -((1 : ℚ) / (q : ℚ))
  ((Polynomial.eval z (hpBpoly n) : ℚ) : ℂ) +
    ((Polynomial.eval z (hpCpoly n) : ℚ) : ℂ) *
      (-((Real.log (q : ℝ)) : ℂ) + (Real.pi : ℂ) * Complex.I)

/-- The actual residue theorem obligation: the explicit branch value equals
the oriented four-edge contour integral of the actual Hermite--Padé kernel.
This record exposes the producer obligation; it does not assume a bound on an
unrelated function value. -/
structure HpTailResidueRectangleCertificate (q n : ℕ) (height : ℝ) : Prop where
  q_gt_one : 1 < q
  n_pos : 0 < n
  height_pos : 0 < height
  residue_identity :
    hpTailBranchValuePlus q n =
      (1 / (2 * Real.pi * Complex.I)) *
        hpTailRectIntegral (-1 / 2) ((n : ℝ) + 1 / 2)
          (-((n : ℝ) * height)) ((n : ℝ) * height)
          (hpTailKernelPlus q n)

/-- PNT rate for one constant rational profile on an interval. -/
lemma hpTail_constant_profile_prime_rate
    (hpnt : Li2Lean.hPNT) (a b c : ℚ) (ha : 0 < a) (hab : a < b) :
    Tendsto
      (fun x : ℝ => (c : ℝ) *
        (Chebyshev.theta ((b : ℝ) * x) - Chebyshev.theta ((a : ℝ) * x)) / x)
      atTop
      (𝓝 (∫ t : ℝ,
        (Li2Lean.constantPrimeAffineProfile a b c ha hab).eval t)) := by
  exact Li2Lean.hPNT_constant_profile_theta_rate hpnt a b c ha hab

/-- Explicit residue/contour consumer contract for a fixed integer base.  The
analytic producer must provide the equality and the quantitative bound. -/
structure HpTailResidueContourCertificate (a : ℤ) where
  q : ℝ
  hq : 1 < q
  contour : ℕ → (ℂ → ℂ)
  residueValue : ℕ → ℂ
  residueIdentity : ∀ n, residueValue n = (contour n) 0
  contourBound : ∀ ε : ℝ, 0 < ε → ∃ n₀, ∀ n, n₀ ≤ n →
    ‖residueValue n‖ ≤ Real.exp (ε * (n : ℝ))

end

end Li2Lean.B4
