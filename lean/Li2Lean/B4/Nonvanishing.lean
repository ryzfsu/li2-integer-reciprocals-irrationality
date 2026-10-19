/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Mathlib

namespace Li2Lean.B4

/-! The determinant and its arithmetic normal form in this file follow the
three-form construction in v13 `hp-tail.tex`; no P0 seed or Lucas transport
is used here.
-/

/-- The alternating three-form determinant for rows `n,n+1,n+2`, as in v13
`hp-tail.tex:506-518`.
-/
def hpThreeFormDeterminant {R : Type*} [CommRing R]
    (A B C : ℕ → R) (n : ℕ) : R :=
  A n * B (n + 1) * C (n + 2) +
    B n * C (n + 1) * A (n + 2) +
    C n * A (n + 1) * B (n + 2) -
    C n * B (n + 1) * A (n + 2) -
    B n * A (n + 1) * C (n + 2) -
    A n * C (n + 1) * B (n + 2)

/-- The adjacent two-form minor `B_m C_{m+1}-C_m B_{m+1}` from v13
`hp-tail.tex:489-505`.
-/
def hpAdjacentMinor {R : Type*} [CommRing R]
    (B C : ℕ → R) (m : ℕ) : R :=
  B m * C (m + 1) - C m * B (m + 1)

/-- Expansion of the v13 three-form determinant along its first column;
`hp-tail.tex:514-518`.
-/
theorem hpThreeFormDeterminant_expand_first_column
    {R : Type*} [CommRing R] (A B C : ℕ → R) (n : ℕ) :
    hpThreeFormDeterminant A B C n =
      A n * hpAdjacentMinor B C (n + 1) -
        A (n + 1) * (B n * C (n + 2) - C n * B (n + 2)) +
        A (n + 2) * hpAdjacentMinor B C n := by
  unfold hpThreeFormDeterminant hpAdjacentMinor
  ring

/-- Replacing the first column by the remainder column preserves the
three-form determinant when the same two formal-series columns are subtracted
from every row; this is the column operation in v13 `hp-tail.tex:512-514`.
-/
theorem hpThreeFormDeterminant_replace_first_column
    {R : Type*} [CommRing R] (A B C Rem : ℕ → R) (L Q : R) (n : ℕ)
    (h : ∀ m, A m + B m * L + C m * Q = Rem m) :
    hpThreeFormDeterminant A B C n =
      hpThreeFormDeterminant Rem B C n := by
  have hA (m : ℕ) : A m = Rem m - B m * L - C m * Q := by
    calc
      A m = (A m + B m * L + C m * Q) - B m * L - C m * Q := by ring
      _ = Rem m - B m * L - C m * Q := by rw [h m]
  unfold hpThreeFormDeterminant
  rw [hA n, hA (n + 1), hA (n + 2)]
  ring

/-- The rational increment `delta_m=h_{m+1}-h_m` displayed in v13
`hp-tail.tex:481-483` and evaluated at `hp-tail.tex:154-157`.
-/
def hpDeltaIncrement (m : ℕ) : ℚ :=
  2 * (27 * (m : ℚ) ^ 2 + 54 * (m : ℚ) + 23) /
    (3 * ((m + 1 : ℕ) : ℚ) * (3 * (m : ℚ) + 2) * (3 * (m : ℚ) + 4))

/-- The factorial factor `U_m` from v13 `hp-tail.tex:481`.
-/
def hpUFactor (m : ℕ) : ℚ :=
  (Nat.factorial (3 * m + 1) : ℚ) / (Nat.factorial m : ℚ) ^ 3

/-- The factorial factor `K_n` from v13 `hp-tail.tex:482`.
-/
def hpKFactor (n : ℕ) : ℚ :=
  (Nat.factorial (2 * n + 1) : ℚ) ^ 3 /
    (Nat.factorial (3 * n + 2) : ℚ) ^ 2

/-- Numerator in the explicit v13 formula for `theta_n`,
`hp-tail.tex:536-540`.
-/
def hpThetaNumerator (n : ℕ) : ℚ :=
  1728 * (n : ℚ) ^ 4 + 11520 * (n : ℚ) ^ 3 + 28140 * (n : ℚ) ^ 2 +
    29965 * (n : ℚ) + 11770

/-- Denominator in the explicit v13 formula for `theta_n`,
`hp-tail.tex:536-540`.
-/
def hpThetaDenominator (n : ℕ) : ℚ :=
  18 * (3 * (n : ℚ) + 4) ^ 2 *
    (27 * (n : ℚ) ^ 2 + 108 * (n : ℚ) + 104)

/-- The rational number `theta_n` in v13 `hp-tail.tex:529-540`.
-/
def hpTheta (n : ℕ) : ℚ := hpThetaNumerator n / hpThetaDenominator n

/-- The scalar multiplying the v13 determinant normal form in
`hp-tail.tex:541-544`.
-/
def hpDeltaScale (n : ℕ) : ℚ :=
  -(hpKFactor n * hpUFactor (n + 1) * hpUFactor (n + 2) *
    hpDeltaIncrement (n + 1))

/-- The polynomial normal form on the right side of v13 `hp-tail.tex:542-544`,
viewed over the reals for evaluation at `z`.
-/
noncomputable def hpDeltaNormalForm (n : ℕ) : Polynomial ℝ :=
  Polynomial.C (hpDeltaScale n : ℝ) * Polynomial.X ^ (3 * n + 2) *
    (1 - Polynomial.C (hpTheta n : ℝ) * Polynomial.X)

/-- The explicit v13 `delta_m` is strictly positive;
`hp-tail.tex:154-157` and `hp-tail.tex:549`.
-/
theorem hpDeltaIncrement_pos (m : ℕ) : 0 < hpDeltaIncrement m := by
  unfold hpDeltaIncrement
  positivity

/-- Positivity of `U_m` in v13 `hp-tail.tex:481`.
-/
theorem hpUFactor_pos (m : ℕ) : 0 < hpUFactor m := by
  have hnumNat : 0 < Nat.factorial (3 * m + 1) := Nat.factorial_pos _
  have hdenNat : 0 < Nat.factorial m := Nat.factorial_pos _
  have hnum : 0 < (Nat.factorial (3 * m + 1) : ℚ) := by exact_mod_cast hnumNat
  have hden : 0 < (Nat.factorial m : ℚ) := by exact_mod_cast hdenNat
  unfold hpUFactor
  positivity

/-- Positivity of `K_n` in v13 `hp-tail.tex:482`.
-/
theorem hpKFactor_pos (n : ℕ) : 0 < hpKFactor n := by
  have hnumNat : 0 < Nat.factorial (2 * n + 1) := Nat.factorial_pos _
  have hdenNat : 0 < Nat.factorial (3 * n + 2) := Nat.factorial_pos _
  have hnum : 0 < (Nat.factorial (2 * n + 1) : ℚ) := by exact_mod_cast hnumNat
  have hden : 0 < (Nat.factorial (3 * n + 2) : ℚ) := by exact_mod_cast hdenNat
  unfold hpKFactor
  positivity

/-- The v13 theta numerator is positive for every natural index;
`hp-tail.tex:536-547`.
-/
theorem hpThetaNumerator_pos (n : ℕ) : 0 < hpThetaNumerator n := by
  unfold hpThetaNumerator
  positivity

/-- The v13 theta denominator is positive for every natural index;
`hp-tail.tex:536-547`.
-/
theorem hpThetaDenominator_pos (n : ℕ) : 0 < hpThetaDenominator n := by
  unfold hpThetaDenominator
  positivity

/-- Positivity of the explicit v13 `theta_n`;
`hp-tail.tex:545-547`.
-/
theorem hpTheta_pos (n : ℕ) : 0 < hpTheta n := by
  unfold hpTheta
  exact div_pos (hpThetaNumerator_pos n) (hpThetaDenominator_pos n)

/-- The denominator minus the numerator is exactly the positive polynomial
shown in v13 `hp-tail.tex:545-548`; hence `theta_n < 1`.
-/
theorem hpTheta_lt_one (n : ℕ) : hpTheta n < 1 := by
  have hden : 0 < hpThetaDenominator n := hpThetaDenominator_pos n
  have hgap :
      0 < (2646 * (n : ℚ) ^ 4 + 17640 * (n : ℚ) ^ 3 +
        43140 * (n : ℚ) ^ 2 + 46067 * (n : ℚ) + 18182) := by
    positivity
  unfold hpTheta
  rw [div_lt_one hden]
  unfold hpThetaNumerator hpThetaDenominator
  nlinarith [hgap]

/-- The v13 linear factor `1-theta_n z` cannot vanish for `|z|<1`, since
`0<theta_n<1`; `hp-tail.tex:545-550`.
-/
theorem hpThetaFactor_ne_zero (n : ℕ) {z : ℝ} (hz : |z| < 1) :
    1 - (hpTheta n : ℝ) * z ≠ 0 := by
  have ht : 0 < (hpTheta n : ℝ) := by exact_mod_cast hpTheta_pos n
  have htlt : (hpTheta n : ℝ) < 1 := by exact_mod_cast hpTheta_lt_one n
  have hgap : 0 < 1 - (hpTheta n : ℝ) := sub_pos.mpr htlt
  have hzgap : 0 < 1 - |z| := sub_pos.mpr hz
  have hterm : 0 < (hpTheta n : ℝ) * (1 - |z|) := mul_pos ht hzgap
  have hprod : (hpTheta n : ℝ) * |z| < 1 := by nlinarith
  intro hzero
  have hprodAbs : |(hpTheta n : ℝ) * z| < 1 := by
    rw [abs_mul, abs_of_pos ht]
    exact hprod
  have hmul : (hpTheta n : ℝ) * z = 1 := by linarith
  rw [hmul] at hprodAbs
  norm_num at hprodAbs

/-- The v13 determinant normal form is nonzero at every real `z` with
`0<|z|<1`; this is the scalar-factor conclusion of `hp-tail.tex:541-550`.
-/
theorem hpDeltaNormalForm_eval_ne_zero (n : ℕ) {z : ℝ}
    (hz0 : 0 < |z|) (hz1 : |z| < 1) :
    (hpDeltaNormalForm n).eval z ≠ 0 := by
  have hscaleQ : hpDeltaScale n ≠ 0 := by
    have hk : 0 < hpKFactor n := hpKFactor_pos n
    have hu1 : 0 < hpUFactor (n + 1) := hpUFactor_pos _
    have hu2 : 0 < hpUFactor (n + 2) := hpUFactor_pos _
    have hd : 0 < hpDeltaIncrement (n + 1) := hpDeltaIncrement_pos _
    have hprod :
        0 < hpKFactor n * hpUFactor (n + 1) * hpUFactor (n + 2) *
          hpDeltaIncrement (n + 1) := by
      exact mul_pos (mul_pos (mul_pos hk hu1) hu2) hd
    unfold hpDeltaScale
    exact ne_of_lt (by linarith)
  have hscale : (hpDeltaScale n : ℝ) ≠ 0 := by exact_mod_cast hscaleQ
  have hz : z ≠ 0 := by
    intro h
    simp [h] at hz0
  have hfactor : 1 - (hpTheta n : ℝ) * z ≠ 0 := hpThetaFactor_ne_zero n hz1
  have heval :
      (hpDeltaNormalForm n).eval z =
        (hpDeltaScale n : ℝ) * z ^ (3 * n + 2) *
          (1 - (hpTheta n : ℝ) * z) := by
    simp [hpDeltaNormalForm]
  rw [heval]
  exact mul_ne_zero (mul_ne_zero hscale (pow_ne_zero _ hz)) hfactor

/-- In particular, the v13 determinant normal-form polynomial is not the
zero polynomial; `hp-tail.tex:541-550`.
-/
theorem hpDeltaNormalForm_ne_zero (n : ℕ) : hpDeltaNormalForm n ≠ 0 := by
  intro hzero
  have heval := congrArg (fun p : Polynomial ℝ => p.eval (1 / 2)) hzero
  have hne := hpDeltaNormalForm_eval_ne_zero n (z := (1 / 2 : ℝ))
    (by norm_num) (by norm_num)
  have hevalZero : (hpDeltaNormalForm n).eval (1 / 2 : ℝ) = 0 := by
    simpa using heval
  exact hne hevalZero

end Li2Lean.B4
