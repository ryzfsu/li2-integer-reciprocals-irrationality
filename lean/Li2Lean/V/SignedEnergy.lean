/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Mathlib
import Li2Lean.P0.DualL6Variations
import Li2Lean.Kit.CircleSmoothing

/-!
The signed-energy interface for the V family.  The mathematical objects are
the ones in this project's paper v13, not a construction imported from a
different irrationality formalization.  The generic L6 lemma is reused from
the Li2(1/2) implementation; the signed inversion identity remains an
explicit v13 certificate field until its measure-theoretic proof is added.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Li2Lean.V

noncomputable section

/-! ## v13 energy and fields (`v-analytic.tex:18-48`) -/

/-- The three positive measures in the v13 signed construction. -/
structure SignedVMeasures where
  q : ℕ
  q_lower : 2 ≤ q
  q_upper : q ≤ 7
  μx : Measure ℂ
  μv : Measure ℂ
  μz : Measure ℂ
  mass_x : μx Set.univ = (1 : ℝ≥0∞)
  mass_v : μv Set.univ = (5 / 4 : ℝ≥0∞)
  mass_z : μz Set.univ = (1 : ℝ≥0∞)
  finite_x : μx Set.univ ≠ ⊤
  finite_v : μv Set.univ ≠ ⊤
  finite_z : μz Set.univ ≠ ⊤

/-- The paper's logarithmic interaction `I(σ,η)=∫ log|u-w|`. -/
noncomputable def vLogInteraction (μ ν : Measure ℂ) : ℝ :=
  -li2LogInteraction μ ν

/-- The cross kernel `log|q+uv|` from v13 `v-analytic.tex:18-21`. -/
noncomputable def vCrossKernel (q : ℕ) (u v : ℂ) : ℝ :=
  Real.log ‖(q : ℂ) + u * v‖

/-- The cross interaction `D_q` from v13 `v-analytic.tex:19-21`. -/
noncomputable def vCrossInteraction (q : ℕ) (μ ν : Measure ℂ) : ℝ :=
  ∫ p : ℂ × ℂ, vCrossKernel q p.1 p.2 ∂(μ.prod ν)

/-- The quadratic signed energy `Q_q` from v13 `v-analytic.tex:18-25`. -/
noncomputable def signedVQuadratic (M : SignedVMeasures) : ℝ :=
  vLogInteraction M.μx M.μx +
    vLogInteraction M.μv M.μv +
    vLogInteraction M.μz M.μz +
    vLogInteraction M.μv M.μz -
    vCrossInteraction M.q M.μx M.μv

/-- The hatted fields from v13 `v-analytic.tex:34-43`. -/
noncomputable def signedVFieldX (M : SignedVMeasures) (w : ℂ) : ℝ :=
  2 * (∫ t : ℂ, Real.log ‖w - t‖ ∂M.μx) -
    ∫ t : ℂ, vCrossKernel M.q w t ∂M.μv

noncomputable def signedVFieldV (M : SignedVMeasures) (w : ℂ) : ℝ :=
  2 * (∫ t : ℂ, Real.log ‖w - t‖ ∂M.μv) +
    (∫ t : ℂ, Real.log ‖w - t‖ ∂M.μz) -
    ∫ t : ℂ, vCrossKernel M.q t w ∂M.μx

noncomputable def signedVFieldZ (M : SignedVMeasures) (w : ℂ) : ℝ :=
  2 * (∫ t : ℂ, Real.log ‖w - t‖ ∂M.μz) +
    ∫ t : ℂ, Real.log ‖w - t‖ ∂M.μv

/-- One-body terms in v13 `v-analytic.tex:44-48`. -/
noncomputable def signedVFullFieldX (M : SignedVMeasures) (w : ℂ) : ℝ :=
  signedVFieldX M w + (3 / 4 : ℝ) * Real.log ‖w‖

noncomputable def signedVFullFieldV (M : SignedVMeasures) (w : ℂ) : ℝ :=
  signedVFieldV M w + (1 / 4 : ℝ) * Real.log ‖w‖

noncomputable def signedVFullFieldZ (M : SignedVMeasures) (w : ℂ) : ℝ :=
  signedVFieldZ M w - (5 / 4 : ℝ) * Real.log ‖w‖

/-! ## L6 certificate reused from the 1/2 implementation -/

/--
All hypotheses needed by the reusable finite-measure L6 positivity theorem.
The kernel and integrability obligations are deliberately explicit because
the v13 reference includes line and circle supported measures.
-/
structure L6PairCertificate where
  left : Measure ℂ
  right : Measure ℂ
  left_finite : left Set.univ ≠ ⊤
  right_finite : right Set.univ ≠ ⊤
  equal_mass : left Set.univ = right Set.univ
  left_atomless : ∀ z : ℂ, left {z} = 0
  right_atomless : ∀ z : ℂ, right {z} = 0
  int_ll : Integrable (fun p : ℂ × ℂ => li2LogKernel p.1 p.2) (left.prod left)
  int_rr : Integrable (fun p : ℂ × ℂ => li2LogKernel p.1 p.2) (right.prod right)
  int_lr : Integrable (fun p : ℂ × ℂ => li2LogKernel p.1 p.2) (left.prod right)

/-- The nonnegative quadratic remainder supplied by the generic L6 theorem. -/
theorem l6PairCertificate_nonneg (c : L6PairCertificate) :
    0 ≤ li2LogInteraction c.left c.left +
      li2LogInteraction c.right c.right -
        2 * li2LogInteraction c.left c.right := by
  letI : IsFiniteMeasure c.left :=
    ⟨lt_top_iff_ne_top.mpr c.left_finite⟩
  letI : IsFiniteMeasure c.right :=
    ⟨lt_top_iff_ne_top.mpr c.right_finite⟩
  exact P0.L6Variations.l6FiniteLogPairDifference_nonneg_of_atomless
    c.left c.right c.equal_mass c.left_atomless c.right_atomless
    c.int_ll c.int_rr c.int_lr

/-! ## v13 inversion and three-square bridge (`v-analytic.tex:220-301`) -/

/-- `R_q(v)=-q/v`, with an arbitrary value at zero for the limiting argument. -/
noncomputable def vReflection (q : ℕ) (v : ℂ) : ℂ :=
  if v = 0 then 0 else -(q : ℂ) / v

/-- The nonzero branch of the v13 inversion map (`v-analytic.tex:244`). -/
theorem vReflection_apply (q : ℕ) {v : ℂ} (hv : v ≠ 0) :
    vReflection q v = -(q : ℂ) / v := by
  simp [vReflection, hv]

/-- Pointwise product identity for `R_q(v)=-q/v` (`v-analytic.tex:244`). -/
theorem vReflection_mul (q : ℕ) {v : ℂ} (hv : v ≠ 0) :
    vReflection q v * v = -(q : ℂ) := by
  rw [vReflection_apply q hv]
  field_simp

/-- Pointwise difference identity for two reflected points
(`v-analytic.tex:247`). -/
theorem vReflection_sub (q : ℕ) {v w : ℂ} (hv : v ≠ 0) (hw : w ≠ 0) :
    vReflection q v - vReflection q w =
      (q : ℂ) * (v - w) / (v * w) := by
  rw [vReflection_apply q hv, vReflection_apply q hw]
  field_simp
  ring

/-- Factorization underlying the cross-kernel identity
(`v-analytic.tex:246`). -/
theorem vCross_factorization (q : ℕ) {v x : ℂ} (hv : v ≠ 0) :
    (q : ℂ) + x * v = (x - vReflection q v) * v := by
  rw [vReflection_apply q hv]
  field_simp
  ring

/-- Logarithmic cross-kernel factorization, with the collision excluded
(`v-analytic.tex:246`). -/
theorem vCross_log_factorization (q : ℕ) {v x : ℂ} (hv : v ≠ 0)
    (hcollision : x - vReflection q v ≠ 0) :
    Real.log ‖(q : ℂ) + x * v‖ =
      Real.log ‖x - vReflection q v‖ + Real.log ‖v‖ := by
  rw [vCross_factorization q hv, norm_mul]
  rw [Real.log_mul (norm_ne_zero_iff.mpr hcollision) (norm_ne_zero_iff.mpr hv)]

/-- Logarithmic distance identity for two reflected points, with positive `q`
and distinct inputs (`v-analytic.tex:247-248`). -/
theorem vReflection_log_distance (q : ℕ) (hq : 0 < q) {v w : ℂ}
    (hv : v ≠ 0) (hw : w ≠ 0) (hneq : v ≠ w) :
    Real.log ‖vReflection q v - vReflection q w‖ =
      Real.log (q : ℝ) + Real.log ‖v - w‖ -
        Real.log ‖v‖ - Real.log ‖w‖ := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  have hsub : v - w ≠ 0 := sub_ne_zero.mpr hneq
  rw [vReflection_sub q hv hw, norm_div]
  simp only [norm_mul]
  rw [Real.log_div
    (mul_ne_zero (norm_ne_zero_iff.mpr hq0) (norm_ne_zero_iff.mpr hsub))
    (mul_ne_zero (norm_ne_zero_iff.mpr hv) (norm_ne_zero_iff.mpr hw))]
  rw [Real.log_mul (norm_ne_zero_iff.mpr hq0) (norm_ne_zero_iff.mpr hsub)]
  rw [Real.log_mul (norm_ne_zero_iff.mpr hv) (norm_ne_zero_iff.mpr hw)]
  simp only [norm_natCast]
  ring

/-- The norm change under `R_q(v) = -q/v`. -/
theorem vReflection_log_norm (q : ℕ) (hq : 0 < q) {v : ℂ}
    (hv : v ≠ 0) :
    Real.log ‖vReflection q v‖ = Real.log (q : ℝ) - Real.log ‖v‖ := by
  rw [vReflection_apply q hv, norm_div, norm_neg, Complex.norm_natCast]
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  rw [Real.log_div hq0 (norm_ne_zero_iff.mpr hv)]

/-! ### Finite-pairing bookkeeping for the v13 inversion -/

/-- The diagonal convention is only for finite algebra. Atomless product
measures do not see the diagonal, but a finite atomic sum does. -/
def vFiniteLogKernel {n : ℕ} (x : Fin n → ℂ) (i j : Fin n) : ℝ :=
  if i = j then Real.log ‖x i‖ else Real.log ‖x i - x j‖

/-- A weighted finite logarithmic pairing with an explicit diagonal value. -/
def vFiniteLogPairing {n : ℕ} (x : Fin n → ℂ) (a : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, a i * a j * vFiniteLogKernel x i j

/-- The usual finite cross pairing between two disjoint point families. -/
def vFiniteLogCrossPairing {n m : ℕ}
    (x : Fin n → ℂ) (a : Fin n → ℝ)
    (y : Fin m → ℂ) (b : Fin m → ℝ) : ℝ :=
  ∑ i, ∑ j, a i * b j * Real.log ‖x i - y j‖

/-- The finite pairing for the v13 cross kernel `log |q+xv|`. -/
def vFiniteV13CrossPairing {n m : ℕ} (q : ℕ)
    (x : Fin n → ℂ) (a : Fin n → ℝ)
    (v : Fin m → ℂ) (b : Fin m → ℝ) : ℝ :=
  ∑ i, ∑ j, a i * b j * Real.log ‖(q : ℂ) + x i * v j‖

private theorem vFiniteDoubleSum_separable {n m : ℕ}
    (f : Fin n → ℝ) (g : Fin m → ℝ) :
    (∑ i, ∑ j, f i * g j) = (∑ i, f i) * (∑ j, g j) := by
  calc
    (∑ i, ∑ j, f i * g j) = ∑ i, f i * (∑ j, g j) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.mul_sum]
    _ = (∑ i, f i) * (∑ j, g j) := by rw [Finset.sum_mul]

private theorem vFiniteDoubleSum_logShift {n m : ℕ}
    (a : Fin n → ℝ) (b : Fin m → ℝ)
    (K : Fin n → Fin m → ℝ) (l : Fin n → ℝ) (r : Fin m → ℝ)
    (C : ℝ) :
    (∑ i, ∑ j, a i * b j * (C + K i j - l i - r j)) =
      (∑ i, a i) * (∑ j, b j) * C +
        (∑ i, ∑ j, a i * b j * K i j) -
        (∑ i, a i * l i) * (∑ j, b j) -
        (∑ i, a i) * (∑ j, b j * r j) := by
  have hC : (∑ i, ∑ j, a i * b j * C) =
      (∑ i, a i) * (∑ j, b j) * C := by
    calc
      (∑ i, ∑ j, a i * b j * C) =
          ∑ i, ∑ j, a i * (b j * C) := by
            apply Finset.sum_congr rfl
            intro i hi
            apply Finset.sum_congr rfl
            intro j hj
            ring
      _ = (∑ i, a i) * (∑ j, b j * C) := vFiniteDoubleSum_separable a (fun j => b j * C)
      _ = (∑ i, a i) * (∑ j, b j) * C := by
            rw [← Finset.sum_mul]
            ring
  have hl : (∑ i, ∑ j, a i * b j * l i) =
      (∑ i, a i * l i) * (∑ j, b j) := by
    calc
      (∑ i, ∑ j, a i * b j * l i) =
          ∑ i, ∑ j, (a i * l i) * b j := by
            apply Finset.sum_congr rfl
            intro i hi
            apply Finset.sum_congr rfl
            intro j hj
            ring
      _ = (∑ i, a i * l i) * (∑ j, b j) := vFiniteDoubleSum_separable
        (fun i => a i * l i) b
  have hr : (∑ i, ∑ j, a i * b j * r j) =
      (∑ i, a i) * (∑ j, b j * r j) := by
    calc
      (∑ i, ∑ j, a i * b j * r j) =
          ∑ i, ∑ j, a i * (b j * r j) := by
            apply Finset.sum_congr rfl
            intro i hi
            apply Finset.sum_congr rfl
            intro j hj
            ring
      _ = (∑ i, a i) * (∑ j, b j * r j) := vFiniteDoubleSum_separable
        a (fun j => b j * r j)
  calc
    (∑ i, ∑ j, a i * b j * (C + K i j - l i - r j)) =
        ∑ i, ∑ j, ((a i * b j * C) + (a i * b j * K i j) -
          (a i * b j * l i) - (a i * b j * r j)) := by
            apply Finset.sum_congr rfl
            intro i hi
            apply Finset.sum_congr rfl
            intro j hj
            ring
    _ = _ := by
          simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
          rw [hC, hl, hr]

private theorem vFiniteLogKernel_reflection {n : ℕ} (q : ℕ) (hq : 0 < q)
    (x : Fin n → ℂ) (hx0 : ∀ i, x i ≠ 0)
    (hinj : Function.Injective x) (i j : Fin n) :
    vFiniteLogKernel (fun i => vReflection q (x i)) i j =
      Real.log (q : ℝ) + vFiniteLogKernel x i j -
        Real.log ‖x i‖ - Real.log ‖x j‖ := by
  unfold vFiniteLogKernel
  split_ifs with hij
  · subst j
    rw [vReflection_log_norm q hq (hx0 i)]
    ring
  · have hneq : x i ≠ x j := by
      intro h
      exact hij (hinj h)
    rw [vReflection_log_distance q hq (hx0 i) (hx0 j) hneq]

/-- Reflection preserves the regularized finite self-pairing of zero-mass
weights. The diagonal value is part of the finite algebra convention. -/
theorem vFiniteLogPairing_reflection {n : ℕ} (q : ℕ) (hq : 0 < q)
    (x : Fin n → ℂ) (a : Fin n → ℝ)
    (hx0 : ∀ i, x i ≠ 0) (hinj : Function.Injective x)
    (hmass : ∑ i, a i = 0) :
    vFiniteLogPairing (fun i => vReflection q (x i)) a =
      vFiniteLogPairing x a := by
  unfold vFiniteLogPairing
  calc
    (∑ i, ∑ j, a i * a j *
        vFiniteLogKernel (fun i => vReflection q (x i)) i j) =
      ∑ i, ∑ j, a i * a j *
        (Real.log (q : ℝ) + vFiniteLogKernel x i j -
          Real.log ‖x i‖ - Real.log ‖x j‖) := by
            apply Finset.sum_congr rfl
            intro i hi
            apply Finset.sum_congr rfl
            intro j hj
            rw [vFiniteLogKernel_reflection q hq x hx0 hinj]
    _ = _ := by
          rw [vFiniteDoubleSum_logShift a a
            (fun i j => vFiniteLogKernel x i j)
            (fun i => Real.log ‖x i‖) (fun i => Real.log ‖x i‖)
            (Real.log (q : ℝ))]
          simp [hmass]

/-- The pairwise distance inversion formula preserves cross pairings when
both signed weight families have zero total mass. -/
theorem vFiniteLogCrossPairing_reflection {n m : ℕ}
    (q : ℕ) (hq : 0 < q)
    (x : Fin n → ℂ) (a : Fin n → ℝ)
    (y : Fin m → ℂ) (b : Fin m → ℝ)
    (hx0 : ∀ i, x i ≠ 0) (hy0 : ∀ j, y j ≠ 0)
    (hxy : ∀ i j, x i ≠ y j)
    (hmassa : ∑ i, a i = 0) (hmassb : ∑ j, b j = 0) :
    vFiniteLogCrossPairing (fun i => vReflection q (x i)) a
      (fun j => vReflection q (y j)) b =
      vFiniteLogCrossPairing x a y b := by
  unfold vFiniteLogCrossPairing
  calc
    (∑ i, ∑ j, a i * b j *
        Real.log ‖vReflection q (x i) - vReflection q (y j)‖) =
      ∑ i, ∑ j, a i * b j *
        (Real.log (q : ℝ) + Real.log ‖x i - y j‖ -
          Real.log ‖x i‖ - Real.log ‖y j‖) := by
            apply Finset.sum_congr rfl
            intro i hi
            apply Finset.sum_congr rfl
            intro j hj
            have hneq : x i ≠ y j := hxy i j
            rw [vReflection_log_distance q hq (hx0 i) (hy0 j) hneq]
    _ = _ := by
          rw [vFiniteDoubleSum_logShift a b
            (fun i j => Real.log ‖x i - y j‖)
            (fun i => Real.log ‖x i‖) (fun j => Real.log ‖y j‖)
            (Real.log (q : ℝ))]
          simp [hmassa, hmassb]

/-- The cross-kernel inversion formula, summed against a zero-mass left
family, removes the one-variable `log |v|` term. -/
theorem vFiniteV13CrossPairing_eq_reflected {n m : ℕ}
    (q : ℕ)
    (x : Fin n → ℂ) (a : Fin n → ℝ)
    (v : Fin m → ℂ) (b : Fin m → ℝ)
    (hv0 : ∀ j, v j ≠ 0)
    (hcollision : ∀ i j, x i - vReflection q (v j) ≠ 0)
    (hmassa : ∑ i, a i = 0) :
    vFiniteV13CrossPairing q x a v b =
      vFiniteLogCrossPairing x a (fun j => vReflection q (v j)) b := by
  unfold vFiniteV13CrossPairing vFiniteLogCrossPairing
  calc
    (∑ i, ∑ j, a i * b j * Real.log ‖(q : ℂ) + x i * v j‖) =
      ∑ i, ∑ j, a i * b j *
        (Real.log ‖x i - vReflection q (v j)‖ + Real.log ‖v j‖) := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          rw [vCross_log_factorization q (hv0 j) (hcollision i j)]
    _ = _ := by
          calc
            (∑ i, ∑ j, a i * b j *
                (Real.log ‖x i - vReflection q (v j)‖ + Real.log ‖v j‖)) =
              ∑ i, ∑ j, a i * b j *
                (0 + Real.log ‖x i - vReflection q (v j)‖ - 0 -
                  (-Real.log ‖v j‖)) := by
                    apply Finset.sum_congr rfl
                    intro i hi
                    apply Finset.sum_congr rfl
                    intro j hj
                    ring
            _ = _ := by
                  rw [vFiniteDoubleSum_logShift a b
                    (fun i j => Real.log ‖x i - vReflection q (v j)‖)
                    (fun _ => 0) (fun j => -Real.log ‖v j‖) 0]
                  simp [hmassa]

/-- The v13 reflection is supplied with its measurable representative. -/
structure VReflectionCertificate (q : ℕ) where
  measurable : Measurable (vReflection q)
  mass_preserving : ∀ μ : Measure ℂ, μ Set.univ ≠ ⊤ →
    (Measure.map (vReflection q) μ) Set.univ = μ Set.univ

/-! ### The signed three-square algebra (`v-analytic.tex:255-269`)

The measure-theoretic reflection identities and the identification of these
five real quantities with the corresponding logarithmic pairings are kept in
the certificate below.  This small algebraic interface is unconditional:
once those v13 identities are supplied, the displayed quadratic remainder is
literally the negative half of the four nonnegative square terms.
-/

/-- The five real quantities in the v13 transformed quadratic form:
the three self energies and the two adjacent pairings. -/
structure SignedVQuadraticData where
  xSelf : ℝ
  vSelf : ℝ
  zSelf : ℝ
  xvPair : ℝ
  vzPair : ℝ

/-- The transformed quadratic form in v13 `v-analytic.tex:259-264`. -/
def signedVQuadraticForm (d : SignedVQuadraticData) : ℝ :=
  -d.xSelf - d.vSelf - d.zSelf + d.xvPair + d.vzPair

/-- The sum of the four squares displayed in v13 `v-analytic.tex:267-269`.
The first two are difference squares; the last two are the endpoint norms. -/
def signedVThreeSquareForm (d : SignedVQuadraticData) : ℝ :=
  (d.xSelf + d.vSelf - 2 * d.xvPair) +
    (d.vSelf + d.zSelf - 2 * d.vzPair) + d.xSelf + d.zSelf

/-- Exact algebraic equality between the transformed quadratic form and the
negative half of the v13 three-square expression. -/
theorem signedVQuadraticForm_eq_neg_half_threeSquare
    (d : SignedVQuadraticData) :
    signedVQuadraticForm d = -(signedVThreeSquareForm d) / 2 := by
  simp [signedVQuadraticForm, signedVThreeSquareForm]
  ring

/-- The signed quadratic form expressed directly in v13 logarithmic
pairings. Here `D` is the `log |q+xv|` cross pairing. -/
def v13SignedPairingData (Ixx Ivv Izz Ivz D : ℝ) : SignedVQuadraticData where
  xSelf := -Ixx
  vSelf := -Ivv
  zSelf := -Izz
  xvPair := -D
  vzPair := Ivz

/-- The v13 signed quadratic expression is the negative half of the four
square expression after the reflection pairings have been identified. -/
theorem v13SignedPairings_eq_neg_half_threeSquare
    (Ixx Ivv Izz Ivz D : ℝ) :
    Ixx + Ivv + Izz + Ivz - D =
      -(signedVThreeSquareForm (v13SignedPairingData Ixx Ivv Izz Ivz D)) / 2 := by
  calc
    Ixx + Ivv + Izz + Ivz - D =
        signedVQuadraticForm (v13SignedPairingData Ixx Ivv Izz Ivz D) := by
          simp [signedVQuadraticForm, v13SignedPairingData]
          ring
    _ = _ := signedVQuadraticForm_eq_neg_half_threeSquare _

/-- The v13 signed quadratic expression is nonpositive when its four
reflected zero-mass squares are nonnegative. -/
theorem v13SignedPairings_nonpos
    (Ixx Ivv Izz Ivz D : ℝ)
    (hxv : 0 ≤ -Ixx - Ivv + 2 * D)
    (hvz : 0 ≤ -Ivv - Izz - 2 * Ivz)
    (hx : 0 ≤ -Ixx) (hz : 0 ≤ -Izz) :
    Ixx + Ivv + Izz + Ivz - D ≤ 0 := by
  rw [v13SignedPairings_eq_neg_half_threeSquare]
  have hs : 0 ≤ signedVThreeSquareForm
      (v13SignedPairingData Ixx Ivv Izz Ivz D) := by
    simp [signedVThreeSquareForm, v13SignedPairingData]
    linarith
  rw [neg_div]
  exact neg_nonpos.mpr (div_nonneg hs (by norm_num))

/-- Nonpositivity of the transformed quadratic form from the four L6-square
nonnegativity facts.  This is the purely algebraic part of the v13
concavity proof; the facts themselves are supplied by the reusable L6
certificate and the v13 reflection pushforwards. -/
theorem signedVQuadraticForm_nonpos
    (d : SignedVQuadraticData)
    (hxv : 0 ≤ d.xSelf + d.vSelf - 2 * d.xvPair)
    (hvz : 0 ≤ d.vSelf + d.zSelf - 2 * d.vzPair)
    (hx : 0 ≤ d.xSelf) (hz : 0 ≤ d.zSelf) :
    signedVQuadraticForm d ≤ 0 := by
  rw [signedVQuadraticForm_eq_neg_half_threeSquare]
  have hs : 0 ≤ signedVThreeSquareForm d := by
    simp [signedVThreeSquareForm]
    linarith
  rw [neg_div]
  exact neg_nonpos.mpr (div_nonneg hs (show (0 : ℝ) ≤ 2 by norm_num))

/-- The four L6 squares used by the v13 signed-energy decomposition. -/
structure SignedVSquareCertificate (μ ν : SignedVMeasures) where
  first : L6PairCertificate
  second : L6PairCertificate
  third : L6PairCertificate
  fourth : L6PairCertificate
  data : SignedVQuadraticData
  remainder : ℝ
  remainder_eq : remainder = signedVQuadraticForm data
  first_square_eq :
    li2LogInteraction first.left first.left +
      li2LogInteraction first.right first.right -
        2 * li2LogInteraction first.left first.right =
      data.xSelf + data.vSelf - 2 * data.xvPair
  second_square_eq :
    li2LogInteraction second.left second.left +
      li2LogInteraction second.right second.right -
        2 * li2LogInteraction second.left second.right =
      data.vSelf + data.zSelf - 2 * data.vzPair
  third_square_eq :
    li2LogInteraction third.left third.left +
      li2LogInteraction third.right third.right -
        2 * li2LogInteraction third.left third.right = data.xSelf
  fourth_square_eq :
    li2LogInteraction fourth.left fourth.left +
      li2LogInteraction fourth.right fourth.right -
        2 * li2LogInteraction fourth.left fourth.right = data.zSelf

/--
The signed quadratic remainder is nonpositive once the v13 reflection
identity has supplied the four pair certificates.  The pair choices and the
identity are intentionally fields: they are the remaining v13 proof work,
not an assumed conclusion about arbitrary measures.
-/
theorem signedV_square_remainder_nonpos
    (μ ν : SignedVMeasures) (c : SignedVSquareCertificate μ ν) :
    c.remainder ≤ 0 := by
  have h1 := l6PairCertificate_nonneg c.first
  have h2 := l6PairCertificate_nonneg c.second
  have h3 := l6PairCertificate_nonneg c.third
  have h4 := l6PairCertificate_nonneg c.fourth
  have hxv : 0 ≤ c.data.xSelf + c.data.vSelf - 2 * c.data.xvPair := by
    rw [← c.first_square_eq]
    exact h1
  have hvz : 0 ≤ c.data.vSelf + c.data.zSelf - 2 * c.data.vzPair := by
    rw [← c.second_square_eq]
    exact h2
  have hx : 0 ≤ c.data.xSelf := by
    rw [← c.third_square_eq]
    exact h3
  have hz : 0 ≤ c.data.zSelf := by
    rw [← c.fourth_square_eq]
    exact h4
  rw [c.remainder_eq]
  exact signedVQuadraticForm_nonpos c.data hxv hvz hx hz

/-! ## Duality interface and smoothing target (`v-analytic.tex:220-301,493-631`) -/

/-- The residual form of the v13 quadratic duality inequality. -/
noncomputable def signedVDualResidual (μ ν : SignedVMeasures) : ℝ :=
  signedVQuadratic μ + signedVQuadratic ν -
    (∫ w : ℂ, signedVFieldX ν w ∂μ.μx) -
    (∫ w : ℂ, signedVFieldV ν w ∂μ.μv) -
    (∫ w : ℂ, signedVFieldZ ν w ∂μ.μz)

/-- A conditional bridge from the v13 three-square identity to the field bound. -/
structure SignedVDualityCertificate (μ ν : SignedVMeasures) where
  square : SignedVSquareCertificate μ ν
  residual_eq : signedVDualResidual μ ν = square.remainder

theorem signedV_duality_residual_nonpos
    (μ ν : SignedVMeasures) (c : SignedVDualityCertificate μ ν) :
    signedVDualResidual μ ν ≤ 0 := by
  rw [c.residual_eq]
  exact
    signedV_square_remainder_nonpos μ ν c.square

/--
The all-`m` smoothing estimate required by v13.  This is an interface, not a
numerical certificate: its fields must later be discharged from the v13
reference tables and smoothing argument (`v-analytic.tex:337-631`).
-/
def signedVSmoothingBound (q : ℕ) (G : ℕ → Polynomial ℝ)
    (alpha tau cLog cLinear cConst : ℝ) : Prop :=
  ∀ n : ℕ, 64 ≤ 4 * n →
    |(G (4 * n)).eval (li2InvValue (-(q : ℤ)))| ≤
      Real.exp (-alpha * (4 * n : ℝ) ^ 2 +
        cLog * (4 * n : ℝ) * Real.log (4 * n : ℝ) +
        cLinear * (4 * n : ℝ) + cConst)

structure SignedVSmoothingParameters where
  alpha : ℝ
  tau : ℝ
  cLog : ℝ
  cLinear : ℝ
  cConst : ℝ
  alpha_gt_tau : tau < alpha

structure SignedVSmoothingCertificate where
  q : ℕ
  q_lower : 2 ≤ q
  q_upper : q ≤ 7
  G : ℕ → Polynomial ℝ
  parameters : SignedVSmoothingParameters
  analytic_bound : signedVSmoothingBound q G parameters.alpha parameters.tau
    parameters.cLog parameters.cLinear parameters.cConst

end

end Li2Lean.V
