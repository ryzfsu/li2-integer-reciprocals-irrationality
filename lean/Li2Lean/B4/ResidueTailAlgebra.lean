/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B4.Residues

open Finset Polynomial

namespace Li2Lean.B4.Residues

noncomputable section

/-- The explicit double-pole residue in v13, equation (hp-residues),
`hp-tail.tex:20-22`. The statement is intended for `j ≤ n`. -/
def hpResidueU (n j : ℕ) : ℚ :=
  - ((Nat.factorial (3 * n + 1 - j) : ℚ) /
      ((Nat.factorial j : ℚ) ^ 2 * (Nat.factorial (n - j) : ℚ) ^ 3))

/-- The explicit simple-pole residue in v13, equation (hp-residues),
`hp-tail.tex:20-22`. -/
def hpResidueV (n j : ℕ) : ℚ :=
  hpResidueU n j *
    (3 * hpHarmonic (n - j) - 2 * hpHarmonic j - hpHarmonic (3 * n + 1 - j))

/-- The finite partial-fraction coefficient at order `z^k`; this is exactly
the coefficient of `B_n(-log(1-z)) + C_n Li₂(z)` from `hp-tail.tex:34-35`. -/
def hpResidueConvolution (n k : ℕ) : ℚ :=
  ∑ j ∈ Finset.range (n + 1),
    if j < k then
      hpResidueV n j / (k - j : ℚ) + hpResidueU n j / (k - j : ℚ) ^ 2
    else 0

/-- Coefficient form of `A_n`, with its displayed minus sign;
`hp-tail.tex:31-32`. -/
def hpApoly (n : ℕ) : ℚ[X] :=
  ∑ r ∈ Finset.range n,
    Polynomial.monomial (r + 1) (-hpResidueConvolution n (r + 1))

/-- Coefficient form of `B_n`; `hp-tail.tex:26`. -/
def hpBpoly (n : ℕ) : ℚ[X] :=
  ∑ j ∈ Finset.range (n + 1), Polynomial.monomial j (hpResidueV n j)

/-- Coefficient form of `C_n`; `hp-tail.tex:27`. -/
def hpCpoly (n : ℕ) : ℚ[X] :=
  ∑ j ∈ Finset.range (n + 1), Polynomial.monomial j (hpResidueU n j)

/-- The coefficient contributed by the three-form expression at degree `k`.
The first summand is `A_n`; the convolution summand is the two other forms. -/
def hpThreeFormCoeff (n k : ℕ) : ℚ :=
  (hpApoly n).coeff k + hpResidueConvolution n k

theorem hpApoly_coeff (n k : ℕ) :
    (hpApoly n).coeff k =
      if 1 ≤ k ∧ k ≤ n then -hpResidueConvolution n k else 0 := by
  classical
  simp [hpApoly, Polynomial.coeff_monomial]
  split_ifs with hk
  · rcases hk with ⟨hk0, hkn⟩
    have hk' : k - 1 < n := by omega
    rw [Finset.sum_eq_single (k - 1)]
    · simp [Nat.sub_add_cancel hk0]
    · intro x hx hne
      by_cases heq : x + 1 = k
      · exfalso
        apply hne
        omega
      · simp [Polynomial.coeff_monomial, heq]
    · intro hmem
      exact False.elim (hmem (Finset.mem_range.mpr hk'))
  · by_cases hk0 : k = 0
    · simp [hk0, hpApoly]
    · have hk1 : 1 ≤ k := by omega
      by_cases hkn : k ≤ n
      · exfalso
        exact hk ⟨hk1, hkn⟩
      · have hsum :
            (∑ x ∈ Finset.range n,
              if x + 1 = k then hpResidueConvolution n (x + 1) else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro x hx
          have hne : x + 1 ≠ k := by
            intro heq
            have hxlt : x < n := Finset.mem_range.mp hx
            apply hkn
            omega
          simp [hne]
        rw [hsum]
        simp

/-- The value of the rational function `Phi_n` at an integer outside its
pole set.  This is the right-hand side of `hp-tail.tex:14-15`. -/
def hpPhiValue (n k : ℕ) : ℚ :=
  (hpNumerator n).eval (k : ℚ) /
    ∏ j ∈ Finset.range (n + 1), ((k : ℚ) - (j : ℚ)) ^ 2

theorem hpPhiValue_eq_zero_of_middle (n k : ℕ)
    (hlo : n < k) (hhi : k ≤ 3 * n + 1) :
    hpPhiValue n k = 0 := by
  classical
  unfold hpPhiValue hpNumerator
  rw [Polynomial.eval_prod]
  apply div_eq_zero_iff.mpr
  left
  apply Finset.prod_eq_zero (by
    have hmem : k ∈ Finset.Icc (n + 1) (3 * n + 1) := by
      simp only [Finset.mem_Icc]
      omega
    exact hmem)
  simp

/-- The exact residual identity needed for the high tail.  Its hypothesis is
the coefficient comparison obtained from the repeated-pole decomposition;
the theorem itself is purely algebraic and is the Lean boundary for the
analytic residue calculation (`hp-tail.tex:34-40`). -/
theorem hpTailCoeff_of_partial_fraction
    (n k : ℕ)
    (hpartial : 3 * n + 2 ≤ k →
      hpResidueConvolution n k = hpPhiValue n k) :
    3 * n + 2 ≤ k → hpThreeFormCoeff n k = hpPhiValue n k := by
  intro hk
  rw [hpThreeFormCoeff, hpApoly_coeff n k]
  have hnot : ¬ (1 ≤ k ∧ k ≤ n) := by
    intro h
    omega
  rw [if_neg hnot]
  simp [hpartial hk]

/-- The middle coefficients vanish once the partial-fraction coefficients
are identified with `Phi_n`; this is the finite coefficient form of the
first cancellation in `hp-tail.tex:36-37`. -/
theorem hpThreeFormCoeff_eq_zero_of_middle
    (n k : ℕ)
    (hlo : n < k) (hhi : k ≤ 3 * n + 1)
    (hpartial : hpResidueConvolution n k = hpPhiValue n k) :
    hpThreeFormCoeff n k = 0 := by
  rw [hpThreeFormCoeff, hpApoly_coeff n k]
  have hnot : ¬ (1 ≤ k ∧ k ≤ n) := by
    intro h
    omega
  rw [if_neg hnot]
  rw [hpartial, hpPhiValue_eq_zero_of_middle n k hlo hhi]
  simp

/-- Formal Casoratian cancellation.  Substituting the three-form expressions
for `R_n` and `R_(n+1)` leaves only the polynomial part and the `Li₂` part;
the logarithm coefficient is identically zero (`hp-tail.tex:42-52`). -/
def hpWpoly (n : ℕ) : ℚ[X] :=
  hpBpoly (n + 1) * hpApoly n - hpBpoly n * hpApoly (n + 1)

def hpVpoly (n : ℕ) : ℚ[X] :=
  hpBpoly (n + 1) * hpCpoly n - hpBpoly n * hpCpoly (n + 1)

theorem hpCasoratian_decomp (n : ℕ) (z ell li : ℚ) :
    Polynomial.eval z (hpBpoly (n + 1)) *
        (Polynomial.eval z (hpApoly n) + Polynomial.eval z (hpBpoly n) * ell +
          Polynomial.eval z (hpCpoly n) * li) -
      Polynomial.eval z (hpBpoly n) *
        (Polynomial.eval z (hpApoly (n + 1)) + Polynomial.eval z (hpBpoly (n + 1)) * ell +
          Polynomial.eval z (hpCpoly (n + 1)) * li) =
      Polynomial.eval z (hpWpoly n) + Polynomial.eval z (hpVpoly n) * li := by
  simp [hpWpoly, hpVpoly, Polynomial.eval_sub, Polynomial.eval_mul]
  ring

theorem hpBpoly_coeff_of_le (n j : ℕ) (hj : j ≤ n) :
    (hpBpoly n).coeff j = hpResidueV n j := by
  classical
  simp [hpBpoly, Polynomial.coeff_monomial, hj]

theorem hpCpoly_coeff_of_le (n j : ℕ) (hj : j ≤ n) :
    (hpCpoly n).coeff j = hpResidueU n j := by
  classical
  simp [hpCpoly, Polynomial.coeff_monomial, hj]

/-- The low coefficients cancel, v13 `hp-tail.tex:36`. -/
theorem hpThreeFormCoeff_eq_zero_of_le (n k : ℕ)
    (hk0 : 1 ≤ k) (hkn : k ≤ n) :
    hpThreeFormCoeff n k = 0 := by
  rw [hpThreeFormCoeff, hpApoly_coeff n k]
  simp [hk0, hkn]

/-- Above degree `n`, the finite polynomial `A_n` no longer contributes;
this is the tail side of v13 `hp-tail.tex:36-40`. -/
theorem hpApoly_coeff_eq_zero_of_lt (n k : ℕ) (hkn : n < k) :
    (hpApoly n).coeff k = 0 := by
  rw [hpApoly_coeff]
  simp [hkn]

end

end Li2Lean.B4.Residues
