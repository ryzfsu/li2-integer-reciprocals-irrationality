/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.V.VLiteralVandermondeBridge
import Li2Lean.P0.CellBound.LogQ

namespace Li2Lean.V

open scoped BigOperators

noncomputable section

/-! C5 finite-product bookkeeping for the literal signed-V integrand.

The strict upper-triangular convention here is the same convention used by
`vContourVandermonde`: its factor at `(i,j)` is `u j - u i` when `i < j`.
The analytic estimate is deliberately separated from the later smoothing and
measure-energy arguments.

| P0 lemma | signed-V lemma | status |
|---|---|---|
| `P0.CellBound.LogQ.sum_offdiag_symm` | `c5_strict_pair_eq_half_odFin` | adapted for the signed-V orientation |
| `P0.CellBound.LogQ.log_norm_det_vandermonde` | `c5_log_norm_vandermonde` | reused through an adapted wrapper |
| `Real.log_prod`, `norm_prod`, and finite-product identities | `c5_log_norm_finset_prod` and `c5_log_norm_finset_prod_finset` | reused |
| no P0 signed-V contour formula | `c5_vContourPhi_log_norm` | new |
-/

def c5PairLog {d : ℕ} (u : Fin d → ℂ) : ℝ :=
  ∑ i : Fin d, ∑ j ∈ Finset.Ioi i, Real.log ‖u j - u i‖

def c5CrossLog {d e : ℕ} (u : Fin d → ℂ) (v : Fin e → ℂ) : ℝ :=
  ∑ i : Fin d, ∑ j : Fin e, Real.log ‖u i - v j‖

def c5DenominatorLog {d e : ℕ} (u : Fin d → ℂ) (v : Fin e → ℂ)
    (q : ℕ) : ℝ :=
  ∑ i : Fin d, ∑ j : Fin e,
    Real.log ‖(q : ℂ) + u i * v j‖

theorem c5_strict_pair_eq_half_odFin {d : ℕ} (u : Fin d → ℂ) :
    c5PairLog u = (1 / 2 : ℝ) * Li2Lean.P0.CellBound.LogQ.odFin u := by
  unfold c5PairLog Li2Lean.P0.CellBound.LogQ.odFin
  have hs := Li2Lean.P0.CellBound.LogQ.sum_offdiag_symm
    (fun i j : Fin d => Real.log ‖u i - u j‖)
    (fun i j => by rw [norm_sub_rev])
  rw [hs]
  have hrev : (∑ i : Fin d, ∑ j ∈ Finset.Ioi i,
      Real.log ‖u i - u j‖) =
      ∑ i : Fin d, ∑ j ∈ Finset.Ioi i,
        Real.log ‖u j - u i‖ := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [norm_sub_rev]
  rw [hrev]
  ring

private theorem c5_injective_of_strict {d : ℕ} {u : Fin d → ℂ}
    (hu : ∀ i j, i < j → u i ≠ u j) : Function.Injective u := by
  intro i j hij
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact (hu i j hlt) hij
  · exact (hu j i hgt) hij.symm

theorem c5_log_norm_vandermonde {d : ℕ} (u : Fin d → ℂ)
    (hu : ∀ i j, i < j → u i ≠ u j) :
    Real.log ‖Literal.vContourVandermonde u‖ = c5PairLog u := by
  rw [vContourVandermonde_eq_det]
  rw [Li2Lean.P0.CellBound.LogQ.log_norm_det_vandermonde u
    (c5_injective_of_strict hu)]
  rw [c5_strict_pair_eq_half_odFin]

theorem c5_log_norm_finset_prod {α : Type*} (s : Finset α)
    (f : α → ℂ) (hf : ∀ a ∈ s, f a ≠ 0) :
    Real.log ‖∏ a ∈ s, f a‖ =
      ∑ a ∈ s, Real.log ‖f a‖ := by
  rw [norm_prod, Real.log_prod]
  intro a ha
  exact norm_ne_zero_iff.mpr (hf a ha)

theorem c5_log_norm_finset_prod_finset {α β : Type*}
    (s : Finset α) (t : Finset β) (f : α → β → ℂ)
    (hf : ∀ a ∈ s, ∀ b ∈ t, f a b ≠ 0) :
    Real.log ‖∏ a ∈ s, ∏ b ∈ t, f a b‖ =
      ∑ a ∈ s, ∑ b ∈ t, Real.log ‖f a b‖ := by
  rw [c5_log_norm_finset_prod s (fun a => ∏ b ∈ t, f a b)]
  · apply Finset.sum_congr rfl
    intro a ha
    exact c5_log_norm_finset_prod t (f a) (fun b hb => hf a ha b hb)
  · intro a ha
    exact Finset.prod_ne_zero_iff.mpr (fun b hb => hf a ha b hb)

theorem c5_log_norm_pow_prod {d : ℕ} (u : Fin d → ℂ) (k : ℕ)
    (hu : ∀ i, u i ≠ 0) :
    Real.log ‖∏ i : Fin d, (u i) ^ k‖ =
      (k : ℝ) * ∑ i : Fin d, Real.log ‖u i‖ := by
  have hprod := c5_log_norm_finset_prod (Finset.univ : Finset (Fin d))
    (fun i => u i ^ k) (fun i hi => pow_ne_zero k (hu i))
  rw [hprod]
  have hsum : (k : ℝ) * ∑ i : Fin d, Real.log ‖u i‖ =
      ∑ i : Fin d, (k : ℝ) * Real.log ‖u i‖ := by
    simpa using (Finset.mul_sum (Finset.univ : Finset (Fin d))
      (fun i => Real.log ‖u i‖) (k : ℝ))
  rw [hsum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [norm_pow, Real.log_pow]

theorem c5_log_norm_zpow_prod {d : ℕ} (u : Fin d → ℂ) (k : ℤ)
    (hu : ∀ i, u i ≠ 0) :
    Real.log ‖∏ i : Fin d, (u i) ^ k‖ =
      (k : ℝ) * ∑ i : Fin d, Real.log ‖u i‖ := by
  have hprod := c5_log_norm_finset_prod (Finset.univ : Finset (Fin d))
    (fun i => u i ^ k) (fun i hi => zpow_ne_zero k (hu i))
  rw [hprod]
  have hsum : (k : ℝ) * ∑ i : Fin d, Real.log ‖u i‖ =
      ∑ i : Fin d, (k : ℝ) * Real.log ‖u i‖ := by
    simpa using (Finset.mul_sum (Finset.univ : Finset (Fin d))
      (fun i => Real.log ‖u i‖) (k : ℝ))
  rw [hsum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [norm_zpow, Real.log_zpow]

theorem c5_log_norm_mul {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) :
    Real.log ‖a * b‖ = Real.log ‖a‖ + Real.log ‖b‖ := by
  rw [norm_mul, Real.log_mul (norm_ne_zero_iff.mpr ha)
    (norm_ne_zero_iff.mpr hb)]

theorem c5_log_norm_div {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) :
    Real.log ‖a / b‖ = Real.log ‖a‖ - Real.log ‖b‖ := by
  rw [norm_div, Real.log_div (norm_ne_zero_iff.mpr ha)
    (norm_ne_zero_iff.mpr hb)]

private theorem c5_vandermonde_ne_zero {d : ℕ} (u : Fin d → ℂ)
    (hu : ∀ i j, i < j → u i ≠ u j) :
    Literal.vContourVandermonde u ≠ 0 := by
  unfold Literal.vContourVandermonde
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  split_ifs with hij
  · exact sub_ne_zero.mpr (hu i j hij).symm
  · simp

private theorem c5_cross_ne_zero {d e : ℕ} (u : Fin d → ℂ)
    (v : Fin e → ℂ) (h : ∀ (i : Fin d) (j : Fin e), u i ≠ v j) :
    (∏ i : Fin d, Finset.univ.prod (fun j : Fin e => u i - v j)) ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  exact sub_ne_zero.mpr (h i j)

private theorem c5_denominator_ne_zero {q d e : ℕ} (u : Fin d → ℂ)
    (v : Fin e → ℂ)
    (h : ∀ (i : Fin d) (j : Fin e), (q : ℂ) + u i * v j ≠ 0) :
    (∏ i : Fin d, Finset.univ.prod
      (fun j : Fin e => (q : ℂ) + u i * v j)) ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  exact h i j

theorem c5_log_norm_cross_prod {d e : ℕ} (u : Fin d → ℂ)
    (v : Fin e → ℂ) (h : ∀ (i : Fin d) (j : Fin e), u i - v j ≠ 0) :
    Real.log (‖(∏ i : Fin d, Finset.univ.prod
      (fun j : Fin e => u i - v j))‖) =
      c5CrossLog u v := by
  have hlog := c5_log_norm_finset_prod_finset
    (Finset.univ : Finset (Fin d)) (Finset.univ : Finset (Fin e))
    (fun i j => u i - v j) (fun i hi j hj => h i j)
  simpa [c5CrossLog] using hlog

theorem c5_log_norm_denominator_prod {q d e : ℕ} (u : Fin d → ℂ)
    (v : Fin e → ℂ)
    (h : ∀ (i : Fin d) (j : Fin e), (q : ℂ) + u i * v j ≠ 0) :
    Real.log (‖(∏ i : Fin d, Finset.univ.prod
      (fun j : Fin e => (q : ℂ) + u i * v j))‖) =
      c5DenominatorLog u v q := by
  have hlog := c5_log_norm_finset_prod_finset
    (Finset.univ : Finset (Fin d)) (Finset.univ : Finset (Fin e))
    (fun i j => (q : ℂ) + u i * v j) (fun i hi j hj => h i j)
  simpa [c5DenominatorLog] using hlog

theorem c5_vContourPhi_log_norm
    (q n : ℕ) (x : Fin (4 * n) → ℝ)
    (v : Fin (5 * n) → ℝ) (z : Fin (4 * n) → ℂ)
    (hx : ∀ i j, i < j → (x i : ℂ) ≠ (x j : ℂ))
    (hv : ∀ i j, i < j → (v i : ℂ) ≠ (v j : ℂ))
    (hz : ∀ i j, i < j → z i ≠ z j)
    (hxv : ∀ i b, z i ≠ (v b : ℂ))
    (hx0 : ∀ i, (x i : ℂ) ≠ 0)
    (hv0 : ∀ b, (v b : ℂ) ≠ 0)
    (hz0 : ∀ i, z i ≠ 0)
    (hden : ∀ i b, (q : ℂ) + (x i : ℂ) * (v b : ℂ) ≠ 0) :
    Real.log ‖Literal.vContourPhi q n x v z‖ =
      2 * c5PairLog (fun i => (x i : ℂ)) +
      2 * c5PairLog (fun i => (v i : ℂ)) +
      2 * c5PairLog z +
      c5CrossLog z (fun b => (v b : ℂ)) -
      c5DenominatorLog (fun i => (x i : ℂ))
        (fun b => (v b : ℂ)) q +
      (3 * n : ℝ) * (∑ i : Fin (4 * n), Real.log |x i|) +
      (n : ℝ) * (∑ b : Fin (5 * n), Real.log |v b|) -
      (5 * n : ℝ) * (∑ i : Fin (4 * n), Real.log ‖z i‖) := by
  let X : Fin (4 * n) → ℂ := fun i => (x i : ℂ)
  let V : Fin (5 * n) → ℂ := fun b => (v b : ℂ)
  have hXvdm : Literal.vContourVandermonde X ≠ 0 :=
    c5_vandermonde_ne_zero X (by simpa [X] using hx)
  have hVvdm : Literal.vContourVandermonde V ≠ 0 :=
    c5_vandermonde_ne_zero V (by simpa [V] using hv)
  have hZvdm : Literal.vContourVandermonde z ≠ 0 :=
    c5_vandermonde_ne_zero z hz
  have hcross : (∏ i : Fin (4 * n), Finset.univ.prod
      (fun b : Fin (5 * n) => z i - V b)) ≠ 0 :=
    c5_cross_ne_zero z V (by simpa [V] using hxv)
  have hden0 : (∏ i : Fin (4 * n), Finset.univ.prod
      (fun b : Fin (5 * n) => (q : ℂ) + X i * V b)) ≠ 0 :=
    c5_denominator_ne_zero X V (by simpa [X, V] using hden)
  have hxpow : (∏ i : Fin (4 * n), X i ^ (3 * n)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i hi => pow_ne_zero _ (hx0 i))
  have hvpow : (∏ b : Fin (5 * n), V b ^ n) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun b hb => pow_ne_zero _ (hv0 b))
  have hzpow : (∏ i : Fin (4 * n), z i ^ (-(5 * n : ℤ))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i hi => zpow_ne_zero _ (hz0 i))
  have hnum :
      Literal.vContourVandermonde X ^ 2 *
          Literal.vContourVandermonde V ^ 2 *
          Literal.vContourVandermonde z ^ 2 *
          (∏ i : Fin (4 * n), Finset.univ.prod
            (fun b : Fin (5 * n) => z i - V b)) *
          (∏ i : Fin (4 * n), X i ^ (3 * n)) *
          (∏ b : Fin (5 * n), V b ^ n) *
          (∏ i : Fin (4 * n), z i ^ (-(5 * n : ℤ))) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
      (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hXvdm)
        (pow_ne_zero _ hVvdm)) (pow_ne_zero _ hZvdm)) hcross) hxpow) hvpow) hzpow
  have hdx := c5_log_norm_vandermonde X (by simpa [X] using hx)
  have hdv := c5_log_norm_vandermonde V (by simpa [V] using hv)
  have hdz := c5_log_norm_vandermonde z hz
  have hcrosslog := c5_log_norm_cross_prod z V (by
    intro i j
    exact sub_ne_zero.mpr (by simpa [V] using hxv i j))
  have hdenlog := c5_log_norm_denominator_prod X V
    (by simpa [X, V] using hden)
  have hxlog := c5_log_norm_pow_prod X (3 * n) (by simpa [X] using hx0)
  have hvlog := c5_log_norm_pow_prod V n (by simpa [V] using hv0)
  have hzlog := c5_log_norm_zpow_prod z (-(5 * n : ℤ)) hz0
  let A : ℂ := Literal.vContourVandermonde X ^ 2
  let B : ℂ := Literal.vContourVandermonde V ^ 2
  let C : ℂ := Literal.vContourVandermonde z ^ 2
  let D : ℂ := ∏ i : Fin (4 * n), Finset.univ.prod
    (fun b : Fin (5 * n) => z i - V b)
  let E : ℂ := ∏ i : Fin (4 * n), X i ^ (3 * n)
  let F : ℂ := ∏ b : Fin (5 * n), V b ^ n
  let G : ℂ := ∏ i : Fin (4 * n), z i ^ (-(5 * n : ℤ))
  let H : ℂ := ∏ i : Fin (4 * n), Finset.univ.prod
    (fun b : Fin (5 * n) => (q : ℂ) + X i * V b)
  have hA : A ≠ 0 := by exact pow_ne_zero _ hXvdm
  have hB : B ≠ 0 := by exact pow_ne_zero _ hVvdm
  have hC : C ≠ 0 := by exact pow_ne_zero _ hZvdm
  have hD : D ≠ 0 := hcross
  have hE : E ≠ 0 := hxpow
  have hF : F ≠ 0 := hvpow
  have hG : G ≠ 0 := hzpow
  have hH : H ≠ 0 := hden0
  have hAl : Real.log ‖A‖ = 2 * c5PairLog X := by
    dsimp [A]
    rw [norm_pow, Real.log_pow, hdx]
    norm_num
  have hBl : Real.log ‖B‖ = 2 * c5PairLog V := by
    dsimp [B]
    rw [norm_pow, Real.log_pow, hdv]
    norm_num
  have hCl : Real.log ‖C‖ = 2 * c5PairLog z := by
    dsimp [C]
    rw [norm_pow, Real.log_pow, hdz]
    norm_num
  have hDl : Real.log ‖D‖ = c5CrossLog z V := by
    exact hcrosslog
  have hEl : Real.log ‖E‖ = (3 * n : ℝ) * ∑ i : Fin (4 * n),
      Real.log ‖X i‖ := by
    simpa [E, Nat.cast_mul] using hxlog
  have hFl : Real.log ‖F‖ = (n : ℝ) * ∑ b : Fin (5 * n),
      Real.log ‖V b‖ := by
    exact hvlog
  have hGl : Real.log ‖G‖ = (-(5 * n : ℤ) : ℝ) * ∑ i : Fin (4 * n),
      Real.log ‖z i‖ := by
    simpa [G] using hzlog
  have hHl : Real.log ‖H‖ = c5DenominatorLog X V q := by
    exact hdenlog
  change Real.log ‖((((((A * B) * C) * D) * E) * F) * G) / H‖ = _
  calc
    Real.log ‖((((((A * B) * C) * D) * E) * F) * G) / H‖ =
        Real.log ‖((((((A * B) * C) * D) * E) * F) * G)‖ -
          Real.log ‖H‖ := c5_log_norm_div (by
            exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
              (mul_ne_zero (mul_ne_zero hA hB) hC) hD) hE) hF) hG) hH
    _ = (Real.log ‖(((((A * B) * C) * D) * E) * F)‖ + Real.log ‖G‖) -
          Real.log ‖H‖ := by
      rw [c5_log_norm_mul (by
        exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
          (mul_ne_zero hA hB) hC) hD) hE) hF) hG]
    _ = (Real.log ‖((((A * B) * C) * D) * E)‖ + Real.log ‖F‖ +
          Real.log ‖G‖) - Real.log ‖H‖ := by
      rw [c5_log_norm_mul (by
        exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hA hB) hC) hD) hE) hF]
    _ = (Real.log ‖(((A * B) * C) * D)‖ + Real.log ‖E‖ +
          Real.log ‖F‖ + Real.log ‖G‖) - Real.log ‖H‖ := by
      rw [c5_log_norm_mul (by
        exact mul_ne_zero (mul_ne_zero (mul_ne_zero hA hB) hC) hD) hE]
    _ = (Real.log ‖((A * B) * C)‖ + Real.log ‖D‖ +
          Real.log ‖E‖ + Real.log ‖F‖ + Real.log ‖G‖) - Real.log ‖H‖ := by
      rw [c5_log_norm_mul (mul_ne_zero (mul_ne_zero hA hB) hC) hD]
    _ = (Real.log ‖(A * B)‖ + Real.log ‖C‖ + Real.log ‖D‖ +
          Real.log ‖E‖ + Real.log ‖F‖ + Real.log ‖G‖) - Real.log ‖H‖ := by
      rw [c5_log_norm_mul (mul_ne_zero hA hB) hC]
    _ = (Real.log ‖A‖ + Real.log ‖B‖ + Real.log ‖C‖ +
          Real.log ‖D‖ + Real.log ‖E‖ + Real.log ‖F‖ +
          Real.log ‖G‖) - Real.log ‖H‖ := by
      rw [c5_log_norm_mul hA hB]
    _ = _ := by
      rw [hAl, hBl, hCl, hDl, hEl, hFl, hGl, hHl]
      simp [X, V, c5CrossLog, c5DenominatorLog, Complex.norm_real,
        Real.norm_eq_abs]
      ring

end

end Li2Lean.V

#print axioms Li2Lean.V.c5_log_norm_vandermonde
#print axioms Li2Lean.V.c5_log_norm_finset_prod
#print axioms Li2Lean.V.c5_vContourPhi_log_norm
