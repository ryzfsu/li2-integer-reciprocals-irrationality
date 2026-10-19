/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B4.HPIntegralForm
import Li2Lean.B4.Nonvanishing
import Li2Lean.B4.DenominatorRate

open Filter Topology Polynomial

namespace Li2Lean.B4.TailAnalytic

noncomputable section

open Li2Lean.B4.Residues

/-!
The inputs and consumers here are fixed to the v13 `A_n,B_n,C_n,R_n,E_n`
construction.  The remaining fields are the three actual analytic/algebraic
bridges in `hp-tail.tex:37-46,477-550`; no arbitrary sequence or form occurs.
-/

/-- The real value of the v13 polynomial `A_n` at the rational base `1/a`.
This is `hp-tail.tex:31-32`. -/
def hpARealAt (a : ℤ) (n : ℕ) : ℝ :=
  ((Polynomial.eval ((a : ℚ)⁻¹) (hpApoly n) : ℚ) : ℝ)

/-- The real value of the v13 polynomial `B_n` at `1/a`, `hp-tail.tex:26`. -/
def hpBRealAt (a : ℤ) (n : ℕ) : ℝ :=
  ((Polynomial.eval ((a : ℚ)⁻¹) (hpBpoly n) : ℚ) : ℝ)

/-- The real value of the v13 polynomial `C_n` at `1/a`, `hp-tail.tex:27`. -/
def hpCRealAt (a : ℤ) (n : ℕ) : ℝ :=
  ((Polynomial.eval ((a : ℚ)⁻¹) (hpCpoly n) : ℚ) : ℝ)

/-- The three-form first column `A_n+B_n(-log(1-z))+C_n Li₂(z)` at
`z=1/a`; this is the concrete `R_n` side of `hp-tail.tex:38-46`. -/
def hpTailCombinationAt (a : ℤ) (n : ℕ) : ℝ :=
  hpARealAt a n + hpBRealAt a n * (-Real.log (1 - (a : ℝ)⁻¹)) +
    hpCRealAt a n * li2InvValue a

/-- The v13 three-form determinant evaluated at the fixed rational base.
This is the determinant in `hp-tail.tex:506-518`. -/
def hpThreeFormDeterminantAt (a : ℤ) (n : ℕ) : ℝ :=
  hpThreeFormDeterminant (hpARealAt a) (hpBRealAt a) (hpCRealAt a) n

/-- The tail-series, beta nonvanishing, and explicit determinant formula for
the actual v13 construction at the fixed base `1/a`.

* `tail_representation` is `hp-tail.tex:37-46`;
* `remainder_ne_zero` is the beta-integral nonvanishing at `:198-221,552`;
* `delta_identity` is the explicit determinant calculation at `:506-550`.

These are producer obligations, not universal form hypotheses. -/
structure HPNoAdjacentV13Input (a : ℤ) : Prop where
  tail_representation : ∀ n,
    hpTailCombinationAt a n = hpRR n ((a : ℝ)⁻¹)
  remainder_ne_zero : ∀ n, hpRR n ((a : ℝ)⁻¹) ≠ 0
  delta_identity : ∀ n,
    hpThreeFormDeterminantAt a n =
      (hpDeltaNormalForm n).eval ((a : ℝ)⁻¹)

/-- If two consecutive adjacent minors with the concrete remainder column
vanish, the v13 determinant vanishes.  This is the row-dependence step in
`hp-tail.tex:556-559`. -/
private theorem hp_three_form_det_eq_zero_of_adjacent_minors
    (A B C R : ℕ → ℝ) (ell li : ℝ) (n : ℕ)
    (hrep : ∀ m, A m + B m * ell + C m * li = R m)
    (hmid : R (n + 1) ≠ 0)
    (h0 : B (n + 1) * R n - B n * R (n + 1) = 0)
    (h1 : B (n + 2) * R (n + 1) - B (n + 1) * R (n + 2) = 0) :
    hpThreeFormDeterminant A B C n = 0 := by
  let t : ℝ := B (n + 1) / R (n + 1)
  have hb0 : B n = R n * t := by
    dsimp [t]
    field_simp [hmid]
    nlinarith [h0]
  have hb1 : B (n + 1) = R (n + 1) * t := by
    dsimp [t]
    field_simp [hmid]
  have hb2 : B (n + 2) = R (n + 2) * t := by
    dsimp [t]
    field_simp [hmid]
    nlinarith [h1]
  have hdet := hpThreeFormDeterminant_replace_first_column
    A B C R ell li n hrep
  unfold hpThreeFormDeterminant at hdet ⊢
  rw [hb0, hb1, hb2] at hdet ⊢
  ring_nf at hdet ⊢
  exact hdet

private theorem hpDR_pos (n : ℕ) : 0 < hpDR n := by
  have hd : 0 < hpDenominator (2 * n + 1) := by
    unfold hpDenominator Li2Lean.P0.Integerization.denominatorLcm
    apply Nat.pos_of_ne_zero
    rw [Finset.lcm_ne_zero_iff]
    intro r hr
    exact Nat.ne_of_gt (Finset.mem_Icc.mp hr).1
  have hb : 0 < hpbN n := by
    unfold hpbN
    exact Nat.choose_pos (by omega)
  have hd' : 0 < (Nat.lcmUpto (2 * n + 1) : ℝ) := by
    rw [← hpDenominator_eq_lcmUpto]
    exact_mod_cast hd
  have hb' : 0 < (hpbN n : ℝ) := by exact_mod_cast hb
  unfold hpDR
  positivity

private theorem hpLR_scalar_ne_zero {a : ℤ} (ha : a ≠ 0) (n : ℕ) :
    (a : ℝ) ^ (2 * n + 1) * hpDR n ≠ 0 := by
  apply mul_ne_zero
  · exact pow_ne_zero _ (by exact_mod_cast ha)
  · exact ne_of_gt (hpDR_pos n)

private theorem hpLR_eq_scalar_mul_E (a : ℤ) (n : ℕ) :
    hpLR a n =
      ((a : ℝ) ^ (2 * n + 1) * hpDR n) *
        (((Polynomial.eval ((a : ℚ)⁻¹) (hpWpoly n) : ℚ) : ℝ) +
          ((Polynomial.eval ((a : ℚ)⁻¹) (hpVpoly n) : ℚ) : ℝ) *
            li2InvValue a) := by
  rfl

private theorem hpE_eq_remainder_minor (a : ℤ) (n : ℕ)
    (I : HPNoAdjacentV13Input a) :
    (((Polynomial.eval ((a : ℚ)⁻¹) (hpWpoly n) : ℚ) : ℝ) +
        ((Polynomial.eval ((a : ℚ)⁻¹) (hpVpoly n) : ℚ) : ℝ) *
          li2InvValue a) =
      hpBRealAt a (n + 1) * hpRR n ((a : ℝ)⁻¹) -
        hpBRealAt a n * hpRR (n + 1) ((a : ℝ)⁻¹) := by
  rw [← I.tail_representation n, ← I.tail_representation (n + 1)]
  unfold hpTailCombinationAt hpARealAt hpBRealAt hpCRealAt hpWpoly hpVpoly
  simp only [Polynomial.eval_sub, Polynomial.eval_mul]
  push_cast
  ring

/-- No adjacent zero for the actual integer form `hpLR(a)`, conditional only
on the concrete v13 tail-series, beta nonvanishing, and Delta producer
obligations. This is the determinant argument of `hp-tail.tex:477-566`. -/
theorem hpLR_no_adjacent_zero_of_v13_input
    {a : ℤ} (ha : (12 : ℤ) ≤ a ∨ a ≤ -8)
    (I : HPNoAdjacentV13Input a) :
    ∀ n, ¬ (hpLR a n = 0 ∧ hpLR a (n + 1) = 0) := by
  intro n hpair
  let z : ℝ := (a : ℝ)⁻¹
  have ha0 : a ≠ 0 := by
    rcases ha with hp | hn <;> omega
  have har : (a : ℝ) ≠ 0 := by exact_mod_cast ha0
  have hz0 : 0 < |z| := abs_pos.mpr (inv_ne_zero har)
  have haabs : (1 : ℝ) < |(a : ℝ)| := by
    rcases ha with hp | hn
    · rw [abs_of_pos (by exact_mod_cast (show 0 < a by omega))]
      exact_mod_cast (by omega : (1 : ℤ) < a)
    · rw [abs_of_neg (by exact_mod_cast (show a < 0 by omega))]
      exact_mod_cast (by omega : (1 : ℤ) < -a)
  have hz1 : |z| < 1 := by
    dsimp [z]
    rw [abs_inv]
    exact (inv_lt_one₀ (abs_pos.mpr har)).2 haabs
  have hdelta : hpThreeFormDeterminantAt a n ≠ 0 := by
    rw [I.delta_identity]
    exact hpDeltaNormalForm_eval_ne_zero n hz0 hz1
  have hrep : ∀ m,
      hpARealAt a m + hpBRealAt a m * (-Real.log (1 - z)) +
        hpCRealAt a m * li2InvValue a = hpRR m z := by
    intro m
    simpa [z, hpTailCombinationAt] using I.tail_representation m
  have hdetAfterReplace :
      hpThreeFormDeterminant (hpARealAt a) (hpBRealAt a) (hpCRealAt a) n =
        hpThreeFormDeterminant (fun m => hpRR m z) (hpBRealAt a)
          (hpCRealAt a) n := by
    exact hpThreeFormDeterminant_replace_first_column
      (hpARealAt a) (hpBRealAt a) (hpCRealAt a) (fun m => hpRR m z)
      (-Real.log (1 - z)) (li2InvValue a) n hrep
  have hdetR :
      hpThreeFormDeterminant (fun m => hpRR m z) (hpBRealAt a)
        (hpCRealAt a) n ≠ 0 := by
    rw [← hdetAfterReplace]
    exact hdelta
  have hminor0 :
      hpBRealAt a (n + 1) * hpRR n z - hpBRealAt a n * hpRR (n + 1) z = 0 := by
    have hE := (hpLR_eq_scalar_mul_E a n).symm.trans hpair.1
    have hE' :
        (((Polynomial.eval ((a : ℚ)⁻¹) (hpWpoly n) : ℚ) : ℝ) +
            ((Polynomial.eval ((a : ℚ)⁻¹) (hpVpoly n) : ℚ) : ℝ) *
              li2InvValue a) = 0 := by
      rcases mul_eq_zero.mp hE with hs | hform
      · exact (hpLR_scalar_ne_zero ha0 n hs).elim
      · exact hform
    rw [hpE_eq_remainder_minor a n I] at hE'
    simpa [z] using hE'
  have hminor1 :
      hpBRealAt a (n + 2) * hpRR (n + 1) z -
        hpBRealAt a (n + 1) * hpRR (n + 2) z = 0 := by
    have hE := (hpLR_eq_scalar_mul_E a (n + 1)).symm.trans hpair.2
    have hE' :
        (((Polynomial.eval ((a : ℚ)⁻¹) (hpWpoly (n + 1)) : ℚ) : ℝ) +
            ((Polynomial.eval ((a : ℚ)⁻¹) (hpVpoly (n + 1)) : ℚ) : ℝ) *
              li2InvValue a) = 0 := by
      rcases mul_eq_zero.mp hE with hs | hform
      · exact (hpLR_scalar_ne_zero ha0 (n + 1) hs).elim
      · exact hform
    rw [hpE_eq_remainder_minor a (n + 1) I] at hE'
    simpa [z] using hE'
  have hdet0 := hp_three_form_det_eq_zero_of_adjacent_minors
    (hpARealAt a) (hpBRealAt a) (hpCRealAt a) (fun m => hpRR m z)
    (-Real.log (1 - z)) (li2InvValue a) n hrep
    (I.remainder_ne_zero (n + 1)) hminor0 hminor1
  have hdetR0 := hdetAfterReplace.symm.trans hdet0
  exact hdetR hdetR0

end

end Li2Lean.B4.TailAnalytic

#print axioms Li2Lean.B4.TailAnalytic.hpLR_no_adjacent_zero_of_v13_input
