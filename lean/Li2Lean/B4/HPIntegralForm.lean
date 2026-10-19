/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Mathlib
import Li2Lean.Statement
import Li2Lean.B4.Integerization
import Li2Lean.B4.ResidueTailAlgebra
import Li2Lean.B4.FinalGlue

open Filter Topology Polynomial
open scoped BigOperators

namespace Li2Lean.B4.TailAnalytic

noncomputable section

open Li2Lean.B4.Residues

/-!
Concrete v13 Hermite--Pade objects for the fixed-base closure.  These names
and fields follow Part 7/8 of the B4-tail construction source; the
construction is the literal `hpBpoly`/`hpWpoly`/`hpVpoly` residue algebra,
not an arbitrary `TailData` family.

The definitions implement v13 `hp-tail.tex:26-27,43-46,55,176-194`.
Decay and determinant/nonvanishing inputs remain separate producer
obligations from `hp-tail.tex:477-560`.
-/

/-- Real evaluation of `B_n(z) = sum_{j <= n} v_{n,j} z^j`.
This is the concrete form of v13 `hp-tail.tex:26`. -/
def hpBR (n : ℕ) (z : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1), (hpResidueV n j : ℝ) * z ^ j

/-- Real evaluation of `C_n(z) = sum_{j <= n} u_{n,j} z^j`.
This is the concrete form of v13 `hp-tail.tex:27`. -/
def hpCR (n : ℕ) (z : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1), (hpResidueU n j : ℝ) * z ^ j

/-- The residual tail `R_n(z)`, indexed by `k = 3n+2+m`, as in
v13 `hp-tail.tex:37-40`. -/
def hpRR (n : ℕ) (z : ℝ) : ℝ :=
  ∑' m : ℕ,
    (hpPhiValue n (3 * n + 2 + m) : ℝ) * z ^ (3 * n + 2 + m)

/-- The Casoratian remainder `E_n`, v13 `hp-tail.tex:43-46`. -/
def hpER (n : ℕ) (z : ℝ) : ℝ :=
  hpBR (n + 1) z * hpRR n z - hpBR n z * hpRR (n + 1) z

/-- The central binomial factor `b_n`, v13 `hp-tail.tex:55`. -/
def hpbN (n : ℕ) : ℕ := (2 * n + 1).choose n

/-- The common denominator factor `d_N^2 / b_n^2`, with `N = 2n+1`,
v13 `hp-tail.tex:188-194`. -/
def hpDR (n : ℕ) : ℝ :=
  (Nat.lcmUpto (2 * n + 1) : ℝ) ^ 2 / (hpbN n : ℝ) ^ 2

/-- The actual fixed-base form `L_n(a)`, v13 `hp-tail.tex:188-194`.
The use of `hpWpoly` and `hpVpoly` pins this definition to the three-form
construction in `ResidueTailAlgebra`. -/
def hpLR (a : ℤ) (n : ℕ) : ℝ :=
  (a : ℝ) ^ (2 * n + 1) * hpDR n *
    ( ((Polynomial.eval ((a : ℚ)⁻¹) (hpWpoly n) : ℚ) : ℝ) +
      ((Polynomial.eval ((a : ℚ)⁻¹) (hpVpoly n) : ℚ) : ℝ) *
        li2InvValue a )

/-- Actual integer-affine output for the v13 form.  This is the corrected
Part 7 interface from the B4 source; it keeps the integerization result as an
explicit producer input. -/
structure HPIntegerForm (a : ℤ) where
  X : ℕ → ℤ
  Y : ℕ → ℤ
  form : ∀ n,
    hpLR a n = (X n : ℝ) + (Y n : ℝ) * li2InvValue a

/-- The same output in existential packaging, used by the producer assembly.
It is the `HPIntegralForm` interface requested for the actual `hpBpoly`
construction. -/
def HPIntegralForm (a : ℤ) : Prop :=
  ∃ X Y : ℕ → ℤ, ∀ n,
    hpLR a n = (X n : ℝ) + (Y n : ℝ) * li2InvValue a

theorem hpIntegerForm_iff_integralForm {a : ℤ} :
    Nonempty (HPIntegerForm a) ↔ HPIntegralForm a := by
  constructor
  · rintro ⟨F⟩
    exact ⟨F.X, F.Y, F.form⟩
  · rintro ⟨X, Y, hXY⟩
    exact ⟨{ X := X, Y := Y, form := hXY }⟩

/-- The integer-affine form can be consumed by the existing final criterion.
This is v13 `hp-tail.tex:561-566`; it leaves decay and no-adjacent-zero as
the explicit hypotheses proved by the analytic and determinant producers. -/
theorem fixed_a_irrational_of_parts {a : ℤ} (hI : HPIntegerForm a)
    (hsmall : Tendsto (hpLR a) atTop (𝓝 0))
    (hnoE : ∀ n, ¬ (hpLR a n = 0 ∧ hpLR a (n + 1) = 0)) :
    Irrational (li2InvValue a) := by
  exact Li2Lean.B4.irrational_of_integer_affine_forms_tendsto_zero
    hI.X hI.Y (hpLR a) hI.form hsmall hnoE

/-- Existential form of the same final bridge, matching `HPIntegralForm`.
No decay or nonvanishing claim is inferred from integrality alone. -/
theorem hpIntegralForm_irrational_of_parts {a : ℤ}
    (hI : HPIntegralForm a)
    (hsmall : Tendsto (hpLR a) atTop (𝓝 0))
    (hnoE : ∀ n, ¬ (hpLR a n = 0 ∧ hpLR a (n + 1) = 0)) :
    Irrational (li2InvValue a) := by
  obtain ⟨X, Y, hXY⟩ := hI
  exact Li2Lean.B4.irrational_of_integer_affine_forms_tendsto_zero
    X Y (hpLR a) hXY hsmall hnoE

/-! ## Explicit integerization input for the actual residue construction -/

/-- The coefficient and degree inputs needed to instantiate the frozen 1/2
integerization kit on the actual Casoratian polynomials.  These fields are
exactly the v13 coefficient identities of `hp-tail.tex:176-187`; the record
does not hide them in a generic affine-form witness. -/
structure HPIntegerizationInput (n N b : ℕ) where
  Q : Polynomial ℤ
  b_pos : 0 < b
  W_degree : (hpWpoly n).natDegree ≤ N
  V_degree : (hpVpoly n).natDegree ≤ N
  W_coeff : ∀ k, k ≤ N →
    (hpWpoly n).coeff k / (b : ℚ) ^ 2 =
      -hpLi2ProductCoeff Q k
  V_coeff : ∀ k, k ≤ N →
    (hpVpoly n).coeff k / (b : ℚ) ^ 2 = (Q.coeff k : ℚ)

/-- Reuse the compiled B4 integerization theorem for `W_n,V_n`.
The output is a pair of integer polynomials with the exact v13 scale; all
remaining work to turn these into the pointwise `HPIntegerForm` is therefore
visible as a separate construction bridge. -/
theorem hp_integerization_input_certificate {n N b : ℕ}
    (I : HPIntegerizationInput n N b) :
    ∃ WZ VZ : Polynomial ℤ,
      Polynomial.map (Int.castRingHom ℚ) WZ =
        Polynomial.C (hpIntegerizationScale (hpDenominator N) b) * hpWpoly n ∧
      Polynomial.map (Int.castRingHom ℚ) VZ =
        Polynomial.C (hpIntegerizationScale (hpDenominator N) b) * hpVpoly n := by
  exact hp_exact_integerization I.b_pos (hpWpoly n) (hpVpoly n) I.Q
    I.W_degree I.V_degree I.W_coeff I.V_coeff

end

end Li2Lean.B4.TailAnalytic

#print axioms Li2Lean.B4.TailAnalytic.hpIntegerForm_iff_integralForm
#print axioms Li2Lean.B4.TailAnalytic.fixed_a_irrational_of_parts
#print axioms Li2Lean.B4.TailAnalytic.hp_integerization_input_certificate
