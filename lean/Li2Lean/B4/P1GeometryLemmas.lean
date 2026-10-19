/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B4.HpNegContourResidueProvider

open Complex Set MeasureTheory intervalIntegral Topology
open scoped BigOperators

namespace Li2Lean.B4.NegContourResidueProducer

noncomputable section

open Li2Lean.B4
open Li2Lean.B4.Residues
open Li2Lean.B4.ResidueTailBridge
open Li2Lean.B4.ContourDecomposition
open Li2Lean.B4.RectanglePrincipalParts

/-! The following lemmas discharge only the literal geometry of the v13
rectangle.  They are deliberately separate from the analytic fields in
`HpTailRectangleDecompositionAssumptions`: no boundary estimate, continuity,
or edge change of variables is inferred here. -/

theorem hpTail_real_corner_order (n : ℕ) :
    (Complex.ofReal (-1 / 2) - Complex.ofReal ((n : ℝ) * (1 / 5 : ℝ)) * Complex.I).re ≤
      (Complex.ofReal ((n : ℝ) + 1 / 2) +
        Complex.ofReal ((n : ℝ) * (1 / 5 : ℝ)) * Complex.I).re := by
  norm_num [Complex.sub_re, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im]
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
  linarith

theorem hpTail_imag_corner_order (n : ℕ) :
    (Complex.ofReal (-1 / 2) - Complex.ofReal ((n : ℝ) * (1 / 5 : ℝ)) * Complex.I).im ≤
      (Complex.ofReal ((n : ℝ) + 1 / 2) +
        Complex.ofReal ((n : ℝ) * (1 / 5 : ℝ)) * Complex.I).im := by
  norm_num [Complex.sub_im, Complex.add_im, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im]

theorem hpTail_pole_interior (n : ℕ) (hn : 0 < n) {j : ℕ}
    (hj : j ∈ Finset.range (n + 1)) :
    Complex.Rectangle
      (Complex.ofReal (-1 / 2) - Complex.ofReal ((n : ℝ) * (1 / 5 : ℝ)) * Complex.I)
      (Complex.ofReal ((n : ℝ) + 1 / 2) +
        Complex.ofReal ((n : ℝ) * (1 / 5 : ℝ)) * Complex.I) ∈
      𝓝 (hpTailNatPole j) := by
  rw [rectangle_mem_nhds_iff, mem_reProdIm]
  rcases Finset.mem_range.mp hj with hjn
  simp only [hpTailNatPole, Complex.natCast_re, Complex.natCast_im,
    Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im]
  ring_nf
  change (j : ℝ) ∈ Set.uIoo (-1 / 2) (1 / 2 + (n : ℝ)) ∧
    (0 : ℝ) ∈ Set.uIoo ((n : ℝ) * (-1 / 5)) ((n : ℝ) * (1 / 5))
  constructor
  · have hleft : (-1 / 2 : ℝ) ≤ (1 / 2 : ℝ) + (n : ℝ) := by
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
      linarith
    rw [uIoo_of_le hleft]
    constructor
    · have hj0 : (0 : ℝ) ≤ j := by positivity
      linarith
    · have hjnle : (j : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast (Nat.le_of_lt_succ hjn)
      linarith
  · have hbottom : (n : ℝ) * (-1 / 5) ≤ (n : ℝ) * (1 / 5) := by
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
      nlinarith
    rw [uIoo_of_le hbottom]
    constructor
    · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      nlinarith
    · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      nlinarith

theorem hpTail_corner_avoidance (n : ℕ) (hn : 0 < n) {j : ℕ}
    (hj : j ∈ Finset.range (n + 1)) :
    ((Complex.ofReal (-1 / 2) - Complex.ofReal ((n : ℝ) * (1 / 5 : ℝ)) * Complex.I).re ≠
        (hpTailNatPole j).re) ∧
      ((Complex.ofReal ((n : ℝ) + 1 / 2) +
          Complex.ofReal ((n : ℝ) * (1 / 5 : ℝ)) * Complex.I).re ≠
        (hpTailNatPole j).re) ∧
      ((Complex.ofReal (-1 / 2) - Complex.ofReal ((n : ℝ) * (1 / 5 : ℝ)) * Complex.I).im ≠
        (hpTailNatPole j).im) ∧
      ((Complex.ofReal ((n : ℝ) + 1 / 2) +
          Complex.ofReal ((n : ℝ) * (1 / 5 : ℝ)) * Complex.I).im ≠
        (hpTailNatPole j).im) := by
  rcases Finset.mem_range.mp hj with hjn
  have hjnle : (j : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (Nat.le_of_lt_succ hjn)
  have hj0 : (0 : ℝ) ≤ (j : ℝ) := by positivity
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  simp only [hpTailNatPole, Complex.natCast_re, Complex.natCast_im,
    Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im]
  constructor
  · intro heq
    have hj0 : (0 : ℝ) ≤ (j : ℝ) := by positivity
    linarith
  constructor
  · intro heq
    have hjnle : (j : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast (Nat.le_of_lt_succ hjn)
    linarith
  constructor <;> intro heq <;> nlinarith

theorem hpTail_pole_not_on_border (n : ℕ) (hn : 0 < n) {j : ℕ}
    (hj : j ∈ Finset.range (n + 1)) :
    hpTailNatPole j ∉ RectangleBorder
      (Complex.ofReal (-1 / 2) -
        Complex.ofReal ((n : ℝ) * (1 / 5 : ℝ)) * Complex.I)
      (Complex.ofReal ((n : ℝ) + 1 / 2) +
        Complex.ofReal ((n : ℝ) * (1 / 5 : ℝ)) * Complex.I) := by
  have hcorner := hpTail_corner_avoidance n hn hj
  have hcornerRev :
      (hpTailNatPole j).re ≠
          (Complex.ofReal (-1 / 2) -
            Complex.ofReal ((n : ℝ) * (1 / 5 : ℝ)) * Complex.I).re ∧
        (hpTailNatPole j).re ≠
          (Complex.ofReal ((n : ℝ) + 1 / 2) +
            Complex.ofReal ((n : ℝ) * (1 / 5 : ℝ)) * Complex.I).re ∧
        (hpTailNatPole j).im ≠
          (Complex.ofReal (-1 / 2) -
            Complex.ofReal ((n : ℝ) * (1 / 5 : ℝ)) * Complex.I).im ∧
        (hpTailNatPole j).im ≠
          (Complex.ofReal ((n : ℝ) + 1 / 2) +
            Complex.ofReal ((n : ℝ) * (1 / 5 : ℝ)) * Complex.I).im := by
    exact ⟨ne_comm.mpr hcorner.1, ne_comm.mpr hcorner.2.1,
      ne_comm.mpr hcorner.2.2.1, ne_comm.mpr hcorner.2.2.2⟩
  have hdis := rectangleBorder_disjoint_singleton hcornerRev
  intro hp
  exact (Set.disjoint_left.mp hdis hp (Set.mem_singleton _))

theorem hpTail_entire_holomorphic (q n : ℕ) (U : Set ℂ) :
    HolomorphicOn (hpTailEntireRemainder q n) U := by
  have hsum : hpTailEntireRemainder q n =
      ∑ j ∈ Finset.range (n + 1), fun s : ℂ =>
        (hpResidueU n j : ℂ) * expDoubleRemainder (hpTailLambda q) (j : ℂ) s +
          (hpResidueV n j : ℂ) * expSimpleRemainder (hpTailLambda q) (j : ℂ) s := by
    funext s
    simp [hpTailEntireRemainder]
  rw [hsum]
  refine Finset.sum_induction
    (f := fun j : ℕ => fun s : ℂ =>
      (hpResidueU n j : ℂ) * expDoubleRemainder (hpTailLambda q) (j : ℂ) s +
        (hpResidueV n j : ℂ) * expSimpleRemainder (hpTailLambda q) (j : ℂ) s)
    (s := Finset.range (n + 1))
    (p := fun f : ℂ → ℂ => DifferentiableOn ℂ f U)
    ?_ ?_ ?_
  · intro f g hf hg
    exact hf.add hg
  · exact differentiableOn_const (0 : ℂ)
  · intro j hj
    exact
      (DifferentiableOn.const_mul
        (expDoubleRemainder_differentiable (hpTailLambda q) (j : ℂ)).differentiableOn
        (hpResidueU n j : ℂ)).add
      (DifferentiableOn.const_mul
        (expSimpleRemainder_differentiable (hpTailLambda q) (j : ℂ)).differentiableOn
        (hpResidueV n j : ℂ))

theorem hpTail_entire_border_integrable (q n : ℕ) :
    RectangleBorderIntegrable (hpTailEntireRemainder q n)
      (Complex.ofReal (-1 / 2) -
        Complex.ofReal ((n : ℝ) * (1 / 5 : ℝ)) * Complex.I)
      (Complex.ofReal ((n : ℝ) + 1 / 2) +
        Complex.ofReal ((n : ℝ) * (1 / 5 : ℝ)) * Complex.I) := by
  apply HolomorphicOn.rectangleBorderIntegrable
  exact hpTail_entire_holomorphic q n _

theorem hpTail_double_part_border_integrable (q n : ℕ) (hn : 0 < n)
    {j : ℕ} (hj : j ∈ Finset.range (n + 1)) :
    RectangleBorderIntegrable
      (doublePart (hpTailUPrime q n) hpTailNatPole j)
      (Complex.ofReal (-1 / 2) -
        Complex.ofReal ((n : ℝ) * (1 / 5 : ℝ)) * Complex.I)
      (Complex.ofReal ((n : ℝ) + 1 / 2) +
        Complex.ofReal ((n : ℝ) * (1 / 5 : ℝ)) * Complex.I) := by
  let z := Complex.ofReal (-1 / 2) -
    Complex.ofReal ((n : ℝ) * (1 / 5 : ℝ)) * Complex.I
  let w := Complex.ofReal ((n : ℝ) + 1 / 2) +
    Complex.ofReal ((n : ℝ) * (1 / 5 : ℝ)) * Complex.I
  change RectangleBorderIntegrable
    (fun s => hpTailUPrime q n j / (s - hpTailNatPole j) ^ 2) z w
  have hp : hpTailNatPole j ∉ RectangleBorder z w := by
    exact hpTail_pole_not_on_border n hn hj
  have hden : ContinuousOn (fun s : ℂ => (s - hpTailNatPole j) ^ 2)
      (Rectangle z w \ {hpTailNatPole j}) :=
    (continuousOn_id.sub continuousOn_const).pow 2
  have hne : ∀ s ∈ Rectangle z w \ {hpTailNatPole j},
      (s - hpTailNatPole j) ^ 2 ≠ 0 := by
    intro s hs hzero
    apply hs.2
    simp only [Set.mem_singleton_iff]
    exact sub_eq_zero.mp ((pow_eq_zero_iff (by norm_num)).mp hzero)
  apply ContinuousOn.rectangleBorderNoPIntegrable
  · exact ContinuousOn.div continuousOn_const hden hne
  · exact hp

theorem hpTail_simple_part_border_integrable (q n : ℕ) (hn : 0 < n)
    {j : ℕ} (hj : j ∈ Finset.range (n + 1)) :
    RectangleBorderIntegrable
      (simplePart (hpTailVPrime q n) hpTailNatPole j)
      (Complex.ofReal (-1 / 2) -
        Complex.ofReal ((n : ℝ) * (1 / 5 : ℝ)) * Complex.I)
      (Complex.ofReal ((n : ℝ) + 1 / 2) +
        Complex.ofReal ((n : ℝ) * (1 / 5 : ℝ)) * Complex.I) := by
  let z := Complex.ofReal (-1 / 2) -
    Complex.ofReal ((n : ℝ) * (1 / 5 : ℝ)) * Complex.I
  let w := Complex.ofReal ((n : ℝ) + 1 / 2) +
    Complex.ofReal ((n : ℝ) * (1 / 5 : ℝ)) * Complex.I
  change RectangleBorderIntegrable
    (fun s => hpTailVPrime q n j / (s - hpTailNatPole j)) z w
  have hp : hpTailNatPole j ∉ RectangleBorder z w := by
    exact hpTail_pole_not_on_border n hn hj
  have hden : ContinuousOn (fun s : ℂ => s - hpTailNatPole j)
      (Rectangle z w \ {hpTailNatPole j}) :=
    continuousOn_id.sub continuousOn_const
  have hne : ∀ s ∈ Rectangle z w \ {hpTailNatPole j},
      s - hpTailNatPole j ≠ 0 := by
    intro s hs hzero
    apply hs.2
    simp only [Set.mem_singleton_iff]
    exact sub_eq_zero.mp hzero
  apply ContinuousOn.rectangleBorderNoPIntegrable
  · exact ContinuousOn.div continuousOn_const hden hne
  · exact hp

theorem hpTail_boundary_decomposition (q n : ℕ) (hn : 0 < n) :
    Set.EqOn (hpTailKernelPlus q n)
      (hpTailEntireRemainder q n +
        principalParts (Finset.range (n + 1))
          (hpTailUPrime q n) (hpTailVPrime q n) hpTailNatPole)
      (RectangleBorder
        (Complex.ofReal (-1 / 2) - Complex.ofReal ((n : ℝ) * (1 / 5 : ℝ)) * Complex.I)
        (Complex.ofReal ((n : ℝ) + 1 / 2) +
          Complex.ofReal ((n : ℝ) * (1 / 5 : ℝ)) * Complex.I)) := by
  intro s hs
  apply hpTailKernel_decomp_of q n (explicitResidueCertificate_all n)
  intro j hj
  intro hsj
  have hcorner := hpTail_corner_avoidance n hn hj
  have hcornerRev :
      (hpTailNatPole j).re ≠
          (Complex.ofReal (-1 / 2) -
            Complex.ofReal ((n : ℝ) * (1 / 5 : ℝ)) * Complex.I).re ∧
        (hpTailNatPole j).re ≠
          (Complex.ofReal ((n : ℝ) + 1 / 2) +
            Complex.ofReal ((n : ℝ) * (1 / 5 : ℝ)) * Complex.I).re ∧
        (hpTailNatPole j).im ≠
          (Complex.ofReal (-1 / 2) -
            Complex.ofReal ((n : ℝ) * (1 / 5 : ℝ)) * Complex.I).im ∧
        (hpTailNatPole j).im ≠
          (Complex.ofReal ((n : ℝ) + 1 / 2) +
            Complex.ofReal ((n : ℝ) * (1 / 5 : ℝ)) * Complex.I).im := by
    exact ⟨ne_comm.mpr hcorner.1, ne_comm.mpr hcorner.2.1,
      ne_comm.mpr hcorner.2.2.1, ne_comm.mpr hcorner.2.2.2⟩
  have hdis : Disjoint
      (RectangleBorder
        (Complex.ofReal (-1 / 2) - Complex.ofReal ((n : ℝ) * (1 / 5 : ℝ)) * Complex.I)
        (Complex.ofReal ((n : ℝ) + 1 / 2) +
          Complex.ofReal ((n : ℝ) * (1 / 5 : ℝ)) * Complex.I))
      {hpTailNatPole j} :=
    rectangleBorder_disjoint_singleton hcornerRev
  exact (Set.disjoint_left.1 hdis hs (by simpa [hsj, hpTailNatPole]))

theorem hpTailRectangleDecompositionAssumptions_of_edge_parameterization
    (q n : ℕ) (hn : 0 < n)
    (edge_parameterization :
      hpTailRectIntegral (-1 / 2) ((n : ℝ) + 1 / 2)
          (-((n : ℝ) * (1 / 5 : ℝ))) ((n : ℝ) * (1 / 5 : ℝ))
          (hpTailKernelPlus q n) =
        RectangleIntegral (hpTailKernelPlus q n)
          (Complex.ofReal (-1 / 2) -
            Complex.ofReal ((n : ℝ) * (1 / 5 : ℝ)) * Complex.I)
          (Complex.ofReal ((n : ℝ) + 1 / 2) +
            Complex.ofReal ((n : ℝ) * (1 / 5 : ℝ)) * Complex.I)) :
    HpTailRectangleDecompositionAssumptions q n (1 / 5 : ℝ) := by
  refine ⟨hpTail_boundary_decomposition q n hn,
    hpTail_entire_holomorphic q n _, hpTail_entire_border_integrable q n,
    hpTail_real_corner_order n, hpTail_imag_corner_order n, ?_, ?_, ?_, ?_,
    edge_parameterization⟩
  · intro j hj
    exact hpTail_pole_interior n hn hj
  · intro j hj
    exact hpTail_corner_avoidance n hn hj
  · intro j hj
    exact hpTail_double_part_border_integrable q n hn hj
  · intro j hj
    exact hpTail_simple_part_border_integrable q n hn hj

end

end Li2Lean.B4.NegContourResidueProducer

#print axioms Li2Lean.B4.NegContourResidueProducer.hpTail_real_corner_order
#print axioms Li2Lean.B4.NegContourResidueProducer.hpTail_imag_corner_order
#print axioms Li2Lean.B4.NegContourResidueProducer.hpTail_pole_interior
#print axioms Li2Lean.B4.NegContourResidueProducer.hpTail_corner_avoidance
#print axioms Li2Lean.B4.NegContourResidueProducer.hpTail_pole_not_on_border
#print axioms Li2Lean.B4.NegContourResidueProducer.hpTail_entire_holomorphic
#print axioms Li2Lean.B4.NegContourResidueProducer.hpTail_entire_border_integrable
#print axioms Li2Lean.B4.NegContourResidueProducer.hpTail_double_part_border_integrable
#print axioms Li2Lean.B4.NegContourResidueProducer.hpTail_simple_part_border_integrable
#print axioms Li2Lean.B4.NegContourResidueProducer.hpTail_boundary_decomposition
#print axioms Li2Lean.B4.NegContourResidueProducer.hpTailRectangleDecompositionAssumptions_of_edge_parameterization
