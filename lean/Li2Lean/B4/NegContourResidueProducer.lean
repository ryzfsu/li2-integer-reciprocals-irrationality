/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Mathlib
import Li2Lean.B4.ContourPNT
import Li2Lean.B4.ContourDecomposition
import Li2Lean.B4.RectanglePrincipalParts
import Li2Lean.B4.ResidueCertificateAllN_M0c

/-!
# Construction-bound P1 producer for the v13 B4 contour

This file records the residue producer at the exact construction used in
`hp-tail.tex:256-266`.  The remaining analytic work is exposed as named
boundary hypotheses in `HpTailRectangleDecomposition`; no arbitrary sequence
or arbitrary function is quantified over.  Once those hypotheses are supplied,
the vendored rectangle theorem, the explicit double-pole FTC cancellation,
and the simple-pole residue theorem give the `HpTailResidueRectangleCertificate`
used by the negative-tail consumers.

The algebraic certificate is the all-`n` M0 theorem from
`ResidueCertificateAllN_M0c.lean`, implementing `hp-tail.tex:12-27`.
-/

open Complex Set MeasureTheory intervalIntegral Topology
open scoped BigOperators

namespace Li2Lean.B4.NegContourResidueProducer

noncomputable section

open Li2Lean.B4
open Li2Lean.B4.Residues
open Li2Lean.B4.ResidueTailBridge
open Li2Lean.B4.ContourDecomposition
open Li2Lean.B4.RectanglePrincipalParts

/-- The phase `lambda = -log q + pi*I` from `hp-tail.tex:257-266`. -/
def hpTailLambda (q : ℕ) : ℂ :=
  -((Real.log (q : ℝ)) : ℂ) + (Real.pi : ℂ) * Complex.I

/-- Pole locations and the coefficients after multiplying by the exponential.
These are fixed to the v13 `u_{n,j},v_{n,j}` construction. -/
def hpTailNatPole : ℕ → ℂ := fun j => (j : ℂ)

def hpTailUPrime (q n : ℕ) : ℕ → ℂ :=
  fun j => (hpResidueU n j : ℂ) * expAffine (hpTailLambda q) j

def hpTailVPrime (q n : ℕ) : ℕ → ℂ :=
  fun j => expAffine (hpTailLambda q) j *
    (hpTailLambda q * (hpResidueU n j : ℂ) + (hpResidueV n j : ℂ))

/-- The entire remainder after the first two dslope terms at every pole.
This is the construction-specific holomorphic part of the v13 contour. -/
def hpTailEntireRemainder (q n : ℕ) : ℂ → ℂ := fun s =>
  ∑ j ∈ Finset.range (n + 1),
    ((hpResidueU n j : ℂ) * expDoubleRemainder (hpTailLambda q) j s +
      (hpResidueV n j : ℂ) * expSimpleRemainder (hpTailLambda q) j s)

/-! ## Algebraic P1 identities

These lemmas are the construction-specific part of the producer.  They use
the all-`n` M0 certificate and contain no analytic estimate. -/

/-- M0 evaluated over `ℂ` gives the Hermite partial fractions off the poles,
v13 `hp-tail.tex:12-23`. -/
theorem hpTailPhi_pf (n : ℕ) (hcert : ExplicitResidueCertificate n)
    {s : ℂ} (hs : ∀ j ∈ Finset.range (n + 1), s ≠ (j : ℂ)) :
    hpTailPhi n s =
      ∑ j ∈ Finset.range (n + 1),
        ((hpResidueU n j : ℂ) / (s - j) ^ 2 +
          (hpResidueV n j : ℂ) / (s - j)) := by
  have hev := congrArg (Polynomial.aeval s) hcert.polynomial_identity
  simp only [hpNumerator, hpOffPoly, hpPole, map_prod, map_sum, map_mul,
    map_add, map_pow, map_sub, Polynomial.aeval_X, Polynomial.aeval_C] at hev
  have hoff : ∀ j ∈ Finset.range (n + 1),
      (∏ i ∈ (Finset.range (n + 1)).erase j, (s - (i : ℂ))) ≠ 0 := by
    intro j _
    exact Finset.prod_ne_zero_iff.mpr fun i hi =>
      sub_ne_zero.mpr (hs i (Finset.mem_of_mem_erase hi))
  have hden : ∀ j ∈ Finset.range (n + 1),
      ∏ i ∈ Finset.range (n + 1), (s - (i : ℂ)) ^ 2 =
        (s - (j : ℂ)) ^ 2 *
          (∏ i ∈ (Finset.range (n + 1)).erase j, (s - (i : ℂ))) ^ 2 := by
    intro j hj
    calc
      ∏ i ∈ Finset.range (n + 1), (s - (i : ℂ)) ^ 2 =
          (∏ i ∈ Finset.range (n + 1), (s - (i : ℂ))) ^ 2 := by
            rw [Finset.prod_pow]
      _ = ((s - (j : ℂ)) *
          ∏ i ∈ (Finset.range (n + 1)).erase j, (s - (i : ℂ))) ^ 2 := by
            rw [← Finset.mul_prod_erase (Finset.range (n + 1))
              (fun i => s - (i : ℂ)) hj]
      _ = (s - (j : ℂ)) ^ 2 *
          (∏ i ∈ (Finset.range (n + 1)).erase j, (s - (i : ℂ))) ^ 2 := by
            ring
  unfold hpTailPhi
  rw [show (∏ r ∈ Finset.Icc (n + 1) (3 * n + 1), (s - (r : ℂ))) = _ by
        simpa using hev, Finset.sum_div]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [hden j hj]
  have hsj : s - (j : ℂ) ≠ 0 := sub_ne_zero.mpr (hs j hj)
  field_simp [hsj, hoff j hj]

/-- The exponential phase at an integer node, v13 `hp-tail.tex:257-266`. -/
theorem exp_hpTailLambda_mul_nat (q j : ℕ) (hq : 0 < q) :
    Complex.exp (hpTailLambda q * (j : ℂ)) =
      (((-((1 : ℚ) / (q : ℚ))) ^ j : ℚ) : ℂ) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have h1 : Complex.exp (hpTailLambda q) = -(1 / (q : ℂ)) := by
    rw [hpTailLambda, Complex.exp_add, Complex.exp_neg,
      Complex.exp_pi_mul_I, ← Complex.ofReal_exp, Real.exp_log hqR]
    push_cast
    ring
  rw [mul_comm, Complex.exp_nat_mul, h1]
  push_cast
  ring

/-- The finite residue sum is the concrete branch value `B_n+lambda*C_n`,
v13 `hp-tail.tex:256-266`. -/
theorem hpTailResidueSum_eq_branch (q n : ℕ) (hq : 0 < q) :
    (∑ j ∈ Finset.range (n + 1), hpTailVPrime q n j) =
      hpTailBranchValuePlus q n := by
  unfold hpTailBranchValuePlus hpBpoly hpCpoly hpTailVPrime
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_monomial,
    Rat.cast_sum, Rat.cast_mul, Rat.cast_pow]
  simp only [expAffine]
  simp_rw [exp_hpTailLambda_mul_nat q _ hq]
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [hpTailLambda]
  push_cast
  ring

/-- The first divided difference at a node is `lambda*exp(lambda*j)`. -/
theorem expSimpleRemainder_hpTailLambda_self (q j : ℕ) :
    expSimpleRemainder (hpTailLambda q) j j =
      hpTailLambda q * expAffine (hpTailLambda q) j := by
  unfold expSimpleRemainder
  rw [dslope_same]
  have h : HasDerivAt (expAffine (hpTailLambda q))
      (Complex.exp (hpTailLambda q * j) * (hpTailLambda q * 1)) j :=
    ((hasDerivAt_id (j : ℂ)).const_mul (hpTailLambda q)).cexp
  rw [h.deriv, expAffine]
  ring

/-- Dslope expansion of the actual kernel into the principal parts and the
entire remainder, v13 `hp-tail.tex:256-266`. -/
theorem hpTailKernel_decomp_of (q n : ℕ) (hcert : ExplicitResidueCertificate n)
    {s : ℂ} (hs : ∀ j ∈ Finset.range (n + 1), s ≠ (j : ℂ)) :
    hpTailKernelPlus q n s =
      (hpTailEntireRemainder q n +
        principalParts (Finset.range (n + 1))
          (hpTailUPrime q n) (hpTailVPrime q n) hpTailNatPole) s := by
  rw [show hpTailKernelPlus q n s = hpTailPhi n s *
      expAffine (hpTailLambda q) s by rfl,
    hpTailPhi_pf n hcert hs, Finset.sum_mul]
  simp only [Pi.add_apply, hpTailEntireRemainder, principalParts,
    principalPart, doublePart, simplePart, hpTailUPrime, hpTailVPrime,
    hpTailNatPole]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hsj := hs j hj
  have h2 := exp_double_pole_decomp (hpTailLambda q) j s hsj
  have h1 := exp_simple_pole_decomp (hpTailLambda q) j s hsj
  rw [expSimpleRemainder_hpTailLambda_self] at h2
  have hsplit :
      ((hpResidueU n j : ℂ) / (s - j) ^ 2 +
          (hpResidueV n j : ℂ) / (s - j)) *
          expAffine (hpTailLambda q) s =
        (hpResidueU n j : ℂ) *
            (expAffine (hpTailLambda q) s / ((s - j) * (s - j))) +
          (hpResidueV n j : ℂ) *
            (expAffine (hpTailLambda q) s / (s - j)) := by
    field_simp [sub_ne_zero.mpr hsj]
  rw [hsplit, h2, h1]
  ring

/-- The explicit hypotheses still needed from the v13 boundary calculation.

`boundary_decomposition` is asserted only on the rectangle border, where all
integer poles are absent.  The fields are fixed to the concrete kernel and
the concrete coefficients above; in particular this cannot be instantiated
by an unrelated `B` sequence.  The field `edge_parameterization` is the
four-side change of variables from the oriented edge integral in
`ContourPNT` to the vendored PNT rectangle integral. -/
structure HpTailRectangleDecomposition (q n : ℕ) (height : ℝ) : Prop where
  explicit_residue : ExplicitResidueCertificate n
  boundary_decomposition :
    Set.EqOn (hpTailKernelPlus q n)
      (hpTailEntireRemainder q n +
        principalParts (Finset.range (n + 1))
          (hpTailUPrime q n) (hpTailVPrime q n) hpTailNatPole)
      (RectangleBorder
        (Complex.ofReal (-1 / 2) - Complex.ofReal ((n : ℝ) * height) * Complex.I)
        (Complex.ofReal ((n : ℝ) + 1 / 2) +
          Complex.ofReal ((n : ℝ) * height) * Complex.I))
  entire_holomorphic :
    HolomorphicOn (hpTailEntireRemainder q n)
      (Complex.Rectangle
        (Complex.ofReal (-1 / 2) - Complex.ofReal ((n : ℝ) * height) * Complex.I)
        (Complex.ofReal ((n : ℝ) + 1 / 2) +
          Complex.ofReal ((n : ℝ) * height) * Complex.I))
  entire_border_integrable :
    RectangleBorderIntegrable (hpTailEntireRemainder q n)
      (Complex.ofReal (-1 / 2) - Complex.ofReal ((n : ℝ) * height) * Complex.I)
      (Complex.ofReal ((n : ℝ) + 1 / 2) +
        Complex.ofReal ((n : ℝ) * height) * Complex.I)
  real_corner_order :
    (Complex.ofReal (-1 / 2) - Complex.ofReal ((n : ℝ) * height) * Complex.I).re ≤
      (Complex.ofReal ((n : ℝ) + 1 / 2) +
        Complex.ofReal ((n : ℝ) * height) * Complex.I).re
  imag_corner_order :
    (Complex.ofReal (-1 / 2) - Complex.ofReal ((n : ℝ) * height) * Complex.I).im ≤
      (Complex.ofReal ((n : ℝ) + 1 / 2) +
        Complex.ofReal ((n : ℝ) * height) * Complex.I).im
  pole_interior : ∀ j, j ∈ Finset.range (n + 1) →
    Complex.Rectangle
      (Complex.ofReal (-1 / 2) - Complex.ofReal ((n : ℝ) * height) * Complex.I)
      (Complex.ofReal ((n : ℝ) + 1 / 2) +
        Complex.ofReal ((n : ℝ) * height) * Complex.I) ∈ 𝓝 (hpTailNatPole j)
  corner_avoidance : ∀ j, j ∈ Finset.range (n + 1) →
    ((Complex.ofReal (-1 / 2) - Complex.ofReal ((n : ℝ) * height) * Complex.I).re ≠
        (hpTailNatPole j).re) ∧
      ((Complex.ofReal ((n : ℝ) + 1 / 2) +
          Complex.ofReal ((n : ℝ) * height) * Complex.I).re ≠
        (hpTailNatPole j).re) ∧
      ((Complex.ofReal (-1 / 2) - Complex.ofReal ((n : ℝ) * height) * Complex.I).im ≠
        (hpTailNatPole j).im) ∧
      ((Complex.ofReal ((n : ℝ) + 1 / 2) +
          Complex.ofReal ((n : ℝ) * height) * Complex.I).im ≠
        (hpTailNatPole j).im)
  double_border_integrable : ∀ j, j ∈ Finset.range (n + 1) →
    RectangleBorderIntegrable
      (doublePart (hpTailUPrime q n) hpTailNatPole j)
      (Complex.ofReal (-1 / 2) - Complex.ofReal ((n : ℝ) * height) * Complex.I)
      (Complex.ofReal ((n : ℝ) + 1 / 2) +
        Complex.ofReal ((n : ℝ) * height) * Complex.I)
  simple_border_integrable : ∀ j, j ∈ Finset.range (n + 1) →
    RectangleBorderIntegrable
      (simplePart (hpTailVPrime q n) hpTailNatPole j)
      (Complex.ofReal (-1 / 2) - Complex.ofReal ((n : ℝ) * height) * Complex.I)
      (Complex.ofReal ((n : ℝ) + 1 / 2) +
        Complex.ofReal ((n : ℝ) * height) * Complex.I)
  residue_sum :
    (∑ j ∈ Finset.range (n + 1), hpTailVPrime q n j) =
      hpTailBranchValuePlus q n
  edge_parameterization :
    hpTailRectIntegral (-1 / 2) ((n : ℝ) + 1 / 2)
        (-((n : ℝ) * height)) ((n : ℝ) * height)
        (hpTailKernelPlus q n) =
      RectangleIntegral (hpTailKernelPlus q n)
        (Complex.ofReal (-1 / 2) - Complex.ofReal ((n : ℝ) * height) * Complex.I)
        (Complex.ofReal ((n : ℝ) + 1 / 2) +
          Complex.ofReal ((n : ℝ) * height) * Complex.I)

/-- Compiling rectangle decomposition: the vendored Cauchy--Goursat plus
double-pole FTC and simple-pole residue lemmas reduce the contour to the
explicit residue sum.  This is the P1 identity in `hp-tail.tex:256-266`. -/
theorem hpTailRectangleResidue_of_decomposition
    (q n : ℕ) (height : ℝ)
    (h : HpTailRectangleDecomposition q n height) :
    RectangleIntegral'
        (hpTailKernelPlus q n)
        (Complex.ofReal (-1 / 2) - Complex.ofReal ((n : ℝ) * height) * Complex.I)
        (Complex.ofReal ((n : ℝ) + 1 / 2) +
          Complex.ofReal ((n : ℝ) * height) * Complex.I) =
      hpTailBranchValuePlus q n := by
  have hres := rectangleIntegral'_of_boundary_decomposition
    (Finset.range (n + 1))
    (hpTailKernelPlus q n) (hpTailEntireRemainder q n)
    (hpTailUPrime q n) (hpTailVPrime q n) hpTailNatPole
    (Complex.ofReal (-1 / 2) - Complex.ofReal ((n : ℝ) * height) * Complex.I)
    (Complex.ofReal ((n : ℝ) + 1 / 2) +
      Complex.ofReal ((n : ℝ) * height) * Complex.I)
    h.boundary_decomposition h.entire_holomorphic h.entire_border_integrable
    h.real_corner_order h.imag_corner_order h.pole_interior h.corner_avoidance
    h.double_border_integrable h.simple_border_integrable
  rw [h.residue_sum] at hres
  exact hres

/-- Conditional P1 producer for the concrete v13 Hermite--Padé kernel.

The only unresolved inputs are the explicitly named rectangle decomposition
and four-side parameterization fields above.  The theorem itself is
construction-bound and supplies the exact `HpTailResidueRectangleCertificate`
shape used by the negative contour consumers. -/
theorem hpTailResidueRectangleCertificate_of
    (q n : ℕ) (height : ℝ)
    (hq : 1 < q) (hn : 0 < n) (hh : 0 < height)
    (h : HpTailRectangleDecomposition q n height) :
    HpTailResidueRectangleCertificate q n height where
  q_gt_one := hq
  n_pos := hn
  height_pos := hh
  residue_identity := by
    have hres := hpTailRectangleResidue_of_decomposition q n height h
    rw [h.edge_parameterization]
    rw [RectangleIntegral'.eq_1, smul_eq_mul] at hres
    exact hres.symm

end

end Li2Lean.B4.NegContourResidueProducer

#print axioms Li2Lean.B4.NegContourResidueProducer.hpTailRectangleResidue_of_decomposition
#print axioms Li2Lean.B4.NegContourResidueProducer.hpTailResidueRectangleCertificate_of
