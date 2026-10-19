/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.ContourOffDiag
import Li2Lean.P0.PositiveBaseParam

/-!
# `ContourIdentity q` for every integer base (compiled Generated, the release date)

Target: `Li2Lean.P0.PositiveBase.ContourIdentity` (master
`Li2Lean/P0/PositiveBaseParam.lean:51`).  Only `q = 2` is proved in the release,
through `contourIdentity_two_iff` (PositiveBaseParam.lean:71) and
`p0ContourIdentityStatement_proved` (ContourOffDiag.lean:656).

Where q = 2 is hard-wired in the release (and nowhere else in the chain):
* `ResidueLeaf.lean:23-37`  `p0Entire_exp_nat`/`p0Entire_nat_eq_U`
  (`exp (i log 2) = 2^i`);
* `ResidueLeaf.lean:73-140` `p0Entire_hasDerivAt_nat`/`p0C_diag_eq_neg_derivative`
  (derivative constant `log 2`);
* `ContourOffDiag.lean:497-625` `p0EllipseIntegral_offdiag` is stated for
  `p0Entire g` and closes with `p0Entire_nat_eq_U`.
The ellipse layer (`p0EllipseIntegral_simplePole`, `_doublePole`,
`_dslope_eq_zero`, `_add`, `_const_mul`, path integrability) is q-free and
reused verbatim.

Route: factor `F_{g,q}(z) = exp(z log(q/2)) * F_{g,2}(z)` and reuse the PUBLIC
q = 2 leaf lemmas `p0Entire_nat_eq_U` and `p0Entire_deriv_nat`.  The
off-diagonal ellipse lemma is restated for an arbitrary entire `F`.
The result needs only `0 < q`; `InRange q` is used for nothing else.

Placement: new file `Li2Lean/P0/PositiveBaseContour.lean`.  Both imports are
already in the closure of `AllN/ProducerAssembly.lean` (via
`FinalEnvelopeWiring -> EnvMain -> EnvContour -> ContourOffDiag` and directly
`PositiveBaseParam`), so ProducerAssembly / PositiveBaseEnvelope may import it
without a cycle [Verified: `lake build Li2Lean.P0.PositiveBaseContour`].
-/

open MeasureTheory Filter Topology

namespace Li2Lean.P0.PositiveBase

noncomputable section

open Li2Lean Li2Lean.P0

/-! ## 1. Off-diagonal ellipse identity for an arbitrary entire function

Verbatim copy of `p0EllipseIntegral_offdiag` (ContourOffDiag.lean:497-625)
with `p0Entire g` replaced by a parameter `F`, and the last two lines
(`rw [p0Entire_nat_eq_U, p0Entire_nat_eq_U]; ring`) replaced by `ring`.
Upstream option: generalize the master lemma itself and derive the q = 2
statement as a corollary (saves the copy). -/

theorem p0EllipseIntegral_offdiag_of_entire (m i j : ℕ) (hm : 0 < m)
    (hi' : i < 2 * m) (hj' : j < 2 * m) (hij : i ≠ j)
    (F : ℂ → ℂ) (hF : Differentiable ℂ F) :
    p0EllipseIntegral m (fun z => F z / ((z - (i : ℂ)) * (z - (j : ℂ)))) =
      (F (i : ℂ) - F (j : ℂ)) / ((i : ℂ) - (j : ℂ)) := by
  let a : ℂ := (i : ℂ)
  let b : ℂ := (j : ℂ)
  have hab : a ≠ b := by
    dsimp [a, b]
    exact_mod_cast hij
  have hpi : IntervalIntegrable
      (fun u => (ellipsePoint m u - a)⁻¹ * ellipseTangent m u)
      volume 0 (2 * Real.pi) := by
    simpa [a] using p0EllipseIntegral_simplePole_path_integrable m i hm hi'
  have hpj : IntervalIntegrable
      (fun u => (ellipsePoint m u - b)⁻¹ * ellipseTangent m u)
      volume 0 (2 * Real.pi) := by
    simpa [b] using p0EllipseIntegral_simplePole_path_integrable m j hm hj'
  have hdi : IntervalIntegrable
      (fun u => dslope F a (ellipsePoint m u) * ellipseTangent m u)
      volume 0 (2 * Real.pi) :=
    p0EllipseIntegral_dslope_path_integrable m F a hF
  have hdj : IntervalIntegrable
      (fun u => dslope F b (ellipsePoint m u) * ellipseTangent m u)
      volume 0 (2 * Real.pi) :=
    p0EllipseIntegral_dslope_path_integrable m F b hF
  let ci : ℂ := F a / (a - b)
  let cj : ℂ := -(F b / (a - b))
  let cd : ℂ := (a - b)⁻¹
  let H1 : ℂ → ℂ := fun z => ci * (z - a)⁻¹
  let H2 : ℂ → ℂ := fun z => cj * (z - b)⁻¹
  let H3 : ℂ → ℂ := fun z => cd * (dslope F a z - dslope F b z)
  have hH1 : IntervalIntegrable
      (fun u => H1 (ellipsePoint m u) * ellipseTangent m u)
      volume 0 (2 * Real.pi) :=
    (hpi.const_mul ci).congr (by intro u _; dsimp [H1]; ring)
  have hH2 : IntervalIntegrable
      (fun u => H2 (ellipsePoint m u) * ellipseTangent m u)
      volume 0 (2 * Real.pi) :=
    (hpj.const_mul cj).congr (by intro u _; dsimp [H2]; ring)
  have hdsub : IntervalIntegrable
      (fun u => (dslope F a (ellipsePoint m u) -
        dslope F b (ellipsePoint m u)) * ellipseTangent m u)
      volume 0 (2 * Real.pi) :=
    (hdi.sub hdj).congr (by intro u _; ring)
  have hH3 : IntervalIntegrable
      (fun u => H3 (ellipsePoint m u) * ellipseTangent m u)
      volume 0 (2 * Real.pi) :=
    (hdsub.const_mul cd).congr (by intro u _; dsimp [H3]; ring)
  have hH23 : IntervalIntegrable
      (fun u => (H2 (ellipsePoint m u) + H3 (ellipsePoint m u)) *
        ellipseTangent m u)
      volume 0 (2 * Real.pi) :=
    (hH2.add hH3).congr (by intro u _; ring)
  have hdecomp :
      p0EllipseIntegral m (fun z => F z / ((z - a) * (z - b))) =
      p0EllipseIntegral m (fun z => H1 z + (H2 z + H3 z)) := by
    unfold p0EllipseIntegral
    apply congrArg (fun x : ℂ =>
      (Complex.ofReal (2 * Real.pi) * Complex.I)⁻¹ * x)
    apply intervalIntegral.integral_congr
    intro u _
    have hia0 : ellipsePoint m u - a ≠ 0 :=
      sub_ne_zero.mpr (p0EllipsePoint_ne_nat hm hi' u)
    have hja0 : ellipsePoint m u - b ≠ 0 :=
      sub_ne_zero.mpr (p0EllipsePoint_ne_nat hm hj' u)
    have hia0p : p0EllipsePoint m u - a ≠ 0 := by
      simpa [ellipsePoint] using hia0
    have hja0p : p0EllipsePoint m u - b ≠ 0 := by
      simpa [ellipsePoint] using hja0
    have hiap : p0EllipsePoint m u ≠ a := sub_ne_zero.mp hia0p
    have hjap : p0EllipsePoint m u ≠ b := sub_ne_zero.mp hja0p
    change F (ellipsePoint m u) /
        ((ellipsePoint m u - a) * (ellipsePoint m u - b)) *
          ellipseTangent m u = _
    simp only [ellipsePoint, ellipseTangent]
    dsimp [H1, H2, H3, ci, cj, cd]
    rw [dslope_of_ne _ hiap, slope_def_field,
      dslope_of_ne _ hjap, slope_def_field]
    field_simp [hia0p, hja0p, hab]
    ring
  rw [hdecomp,
    p0EllipseIntegral_add m H1 (fun z => H2 z + H3 z) hH1 hH23,
    p0EllipseIntegral_add m H2 H3 hH2 hH3,
    p0EllipseIntegral_const_mul, p0EllipseIntegral_const_mul,
    p0EllipseIntegral_const_mul]
  have hsub :
      p0EllipseIntegral m (fun z => dslope F a z - dslope F b z) = 0 := by
    apply (p0EllipseIntegral_sub m (dslope F a) (dslope F b) hdi hdj).trans
    rw [p0EllipseIntegral_dslope_eq_zero m F a hF,
      p0EllipseIntegral_dslope_eq_zero m F b hF]
    ring
  rw [hsub, mul_zero, p0EllipseIntegral_simplePole m i hm hi',
    p0EllipseIntegral_simplePole m j hm hj']
  dsimp [ci, cj, a, b]
  have hden : (i : ℂ) - (j : ℂ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hij)
  field_simp [hden]
  ring
  -- [Verified] the `simpa [a]`/`simpa [b]` coercion steps are copied from the
  -- master proof (:520-529), where the pole is a `let`; if `simpa` leaves a
  -- `((i : ℕ) : ℂ)` vs `a` mismatch, use `show` with `a` unfolded.

/-! ## 2. The base-q source as a shift of the base-2 source -/

/-- `exp (z * log (q/2))`; `|.| = (q/2)^{Re z}` is the one-body shift. -/
def qShiftFactor (q : ℤ) (z : ℂ) : ℂ :=
  Complex.exp (z * Complex.ofReal (Real.log ((q : ℝ) / 2)))

theorem log_q_eq_log_two_add (q : ℤ) (hq : 0 < q) :
    Real.log (q : ℝ) = Real.log 2 + Real.log ((q : ℝ) / 2) := by
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [Real.log_div hqR (by norm_num)]
  ring

theorem p0EntireQ_eq_shift_mul (q : ℤ) (hq : 0 < q) (g : ℕ) (z : ℂ) :
    p0EntireQ q g z = qShiftFactor q z * p0Entire g z := by
  unfold p0EntireQ qShiftFactor p0Entire
  rw [log_q_eq_log_two_add q hq, Complex.ofReal_add, mul_add, Complex.exp_add]
  ring

/-! The norm factor used by the q-contour envelope.  This is the absolute
value form of the v13 source shift in `p0-analytic.tex:700-747`. -/
theorem norm_p0EntireQ_eq (q : ℤ) (hq : 0 < q) (g : ℕ) (z : ℂ) :
    ‖p0EntireQ q g z‖ =
      ‖p0Entire g z‖ * Real.exp (logShift q * z.re) := by
  rw [p0EntireQ_eq_shift_mul q hq g z, norm_mul]
  unfold qShiftFactor
  rw [Complex.norm_exp]
  rw [mul_comm]
  congr 1
  simp [Complex.mul_re, logShift, mul_comm]

theorem qShiftFactor_nat (q : ℤ) (hq : 0 < q) (i : ℕ) :
    qShiftFactor q (i : ℂ) = ((q : ℂ) / 2) ^ i := by
  have hpos : (0 : ℝ) < (q : ℝ) / 2 := by
    have : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
    positivity
  have hbase : Complex.exp (Complex.ofReal (Real.log ((q : ℝ) / 2))) =
      (q : ℂ) / 2 := by
    rw [← Complex.ofReal_exp, Real.exp_log hpos]
    push_cast
    ring
  unfold qShiftFactor
  rw [Complex.exp_nat_mul, hbase]

theorem p0EntireQ_differentiable (q : ℤ) (g : ℕ) :
    Differentiable ℂ (p0EntireQ q g) := by
  unfold p0EntireQ
  fun_prop

/-- Base-q analogue of `p0Entire_nat_eq_U` (ResidueLeaf.lean:32). -/
theorem p0EntireQ_nat_eq_U (q : ℤ) (hq : 0 < q) (g i : ℕ) :
    p0EntireQ q g (i : ℂ) = p0UComplex q g i := by
  rw [p0EntireQ_eq_shift_mul q hq, qShiftFactor_nat q hq, p0Entire_nat_eq_U]
  unfold p0U p0UComplex
  rw [div_pow]
  field_simp
  -- [Verified] goal after `field_simp`: `q^i * C = q^i * C` up to `ring`

theorem hasDerivAt_qShiftFactor (q : ℤ) (z : ℂ) :
    HasDerivAt (qShiftFactor q)
      (qShiftFactor q z * Complex.ofReal (Real.log ((q : ℝ) / 2))) z := by
  unfold qShiftFactor
  convert
    (Complex.hasDerivAt_exp
      (z * Complex.ofReal (Real.log ((q : ℝ) / 2)))).comp z
      ((hasDerivAt_id z).mul_const
        (Complex.ofReal (Real.log ((q : ℝ) / 2)))) using 1 <;>
    simp [Function.comp_def]
  -- same `convert ... <;> simp` shape as ResidueLeaf.lean:83-88

/-- Base-q analogue of `p0Entire_deriv_nat` (ResidueLeaf.lean:136). -/
theorem p0EntireQ_deriv_nat (q : ℤ) (hq : 0 < q) (g i : ℕ) :
    deriv (p0EntireQ q g) (i : ℂ) =
      p0UComplex q g i * (Complex.ofReal (Real.log (q : ℝ)) +
        ∑ r ∈ Finset.range g, (((i + r + 1 : ℕ) : ℂ)⁻¹)) := by
  have hfun : p0EntireQ q g = fun z => qShiftFactor q z * p0Entire g z := by
    funext z
    exact p0EntireQ_eq_shift_mul q hq g z
  have hF2 : Differentiable ℂ (p0Entire g) := by
    unfold p0Entire
    fun_prop
  have hD2 : HasDerivAt (p0Entire g) (deriv (p0Entire g) (i : ℂ)) (i : ℂ) :=
    (hF2 (i : ℂ)).hasDerivAt
  have hprod := (hasDerivAt_qShiftFactor q (i : ℂ)).mul hD2
  rw [hfun]
  change deriv (qShiftFactor q * p0Entire g) (i : ℂ) = _
  rw [hprod.deriv, p0Entire_deriv_nat, p0Entire_nat_eq_U,
    qShiftFactor_nat q hq, log_q_eq_log_two_add q hq]
  unfold p0U p0UComplex
  push_cast
  rw [div_pow]
  field_simp
  ring
  -- [Verified] `hfun ▸` inside `deriv`: if `rw [hfun]` fails on the bound
  -- function, use `show deriv (fun z => _) _ = _` first.

/-- Base-q analogue of `p0C_diag_eq_neg_derivative` (ResidueLeaf.lean:128). -/
theorem p0CComplex_diag_eq_neg_derivative (q : ℤ) (hq : 0 < q) (g i : ℕ) :
    p0CComplex q g i i =
      -deriv (p0EntireQ q g) (i : ℂ) +
        Complex.ofReal (Real.log (q : ℝ)) * p0UComplex q g i := by
  rw [p0CComplex, if_pos rfl, p0EntireQ_deriv_nat q hq]
  ring

/-! ## 3. The contour identity for every positive base -/

theorem contourIdentity_of_pos (q : ℤ) (hq : 0 < q) :
    ∀ g i j : ℕ, i < 4 * g → j < 4 * g →
      p0CComplex q g i j =
        -p0EllipseIntegral (2 * g) (fun z =>
          p0EntireQ q g z / ((z - (i : ℂ)) * (z - (j : ℂ)))) +
          if i = j then Complex.ofReal (Real.log (q : ℝ)) *
            p0UComplex q g i else 0 := by
  intro g i j hi hj
  have hm : 0 < 2 * g := by omega
  have hi' : i < 2 * (2 * g) := by omega
  have hj' : j < 2 * (2 * g) := by omega
  have hF := p0EntireQ_differentiable q g
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl,
      p0EllipseIntegral_doublePole (2 * g) i (p0EntireQ q g) hm hi' hF]
    exact p0CComplex_diag_eq_neg_derivative q hq g i
  · rw [if_neg hij, add_zero,
      p0EllipseIntegral_offdiag_of_entire (2 * g) i j hm hi' hj' hij
        (p0EntireQ q g) hF,
      p0EntireQ_nat_eq_U q hq, p0EntireQ_nat_eq_U q hq,
      p0CComplex, if_neg hij]
    have hijC : (i : ℂ) ≠ (j : ℂ) := by exact_mod_cast hij
    have h1 : (i : ℂ) - (j : ℂ) ≠ 0 := sub_ne_zero.mpr hijC
    have h2 : (j : ℂ) - (i : ℂ) ≠ 0 := sub_ne_zero.mpr hijC.symm
    field_simp [h1, h2]
    ring

/-- `ContourIdentity q` holds for every integer `q` (its `InRange q` premise
supplies `0 < q`). -/
theorem contourIdentity_all (q : ℤ) : ContourIdentity q := by
  intro hq
  exact contourIdentity_of_pos q (by have := hq.1; omega)

/-- Regression: the new proof reproduces the master q = 2 statement. -/
example : P0ContourIdentityStatement :=
  contourIdentity_two_iff.mp (contourIdentity_all 2)

end

end Li2Lean.P0.PositiveBase
