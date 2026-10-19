/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.ConfigFgBound

open MeasureTheory
open scoped BigOperators Interval

namespace Li2Lean.B4

noncomputable section

open Li2Lean.P0.Config

/-!
# Rectangle sum-to-integral interface for the v13 tail

The declarations in this file isolate the finite algebra of the estimate in
`hp-tail.tex:281-316`.  The analytic inputs to the final glue theorem are
explicit absolute bounds for the two right-endpoint cell errors and the two
endpoint shifts.  This is intentional: the v13 passage treats a logarithmic
endpoint cell separately, and the one-sided half-case theorem
`cp_sum_sub_integral` cannot be silently promoted to an absolute estimate.
-/

/-- The logarithmic factor in the product of `hp-tail.tex:281-316`. -/
def hpLog (xi : ℂ) (x : ℝ) : ℝ :=
  Real.log ‖xi - (x : ℂ)‖

/-- The finite numerator and denominator logarithmic sums in `hp-log-em`. -/
def hpProductLogSum (n : ℕ) (xi : ℂ) : ℝ :=
  (∑ r ∈ Finset.Icc (n + 1) (3 * n + 1),
      hpLog xi ((r : ℝ) / (n : ℝ))) -
    2 * (∑ j ∈ Finset.Icc 0 n, hpLog xi ((j : ℝ) / (n : ℝ)))

/-- The two continuum integrals in `hp-log-em`. -/
def hpProductLogIntegral (n : ℕ) (xi : ℂ) : ℝ :=
  (n : ℝ) *
    ((∫ x in (1 : ℝ)..3, hpLog xi x) -
      2 * (∫ x in (0 : ℝ)..1, hpLog xi x))

/-- The error whose absolute value is estimated in `hp-log-em`. -/
def hpProductLogError (n : ℕ) (xi : ℂ) : ℝ :=
  hpProductLogSum n xi - hpProductLogIntegral n xi

/-- A right-endpoint sum on a scaled interval `[a/n,(a+m)/n]`. -/
def hpRightLogSum (n a m : ℕ) (xi : ℂ) : ℝ :=
  ∑ k ∈ Finset.range m,
    hpLog xi (((a + k + 1 : ℕ) : ℝ) / (n : ℝ))

/-- The matching scaled interval integral. -/
def hpScaledLogIntegral (n a m : ℕ) (xi : ℂ) : ℝ :=
  (n : ℝ) *
    (∫ x in (a : ℝ) / (n : ℝ)..((a + m : ℕ) : ℝ) / (n : ℝ),
      hpLog xi x)

/-- Extra points left out of the two right-endpoint sums. -/
def hpNumeratorEndpoint (n : ℕ) (xi : ℂ) : ℝ :=
  hpLog xi (((3 * n + 1 : ℕ) : ℝ) / (n : ℝ))

def hpDenominatorEndpoint (xi : ℂ) : ℝ := hpLog xi 0

/-- Exact finite decomposition of the product sum into right sums and endpoint
shifts.  This is the endpoint bookkeeping in `hp-tail.tex:307-315`. -/
theorem hp_product_log_sum_decomp (n : ℕ) (xi : ℂ) :
    hpProductLogSum n xi =
      hpRightLogSum n n (2 * n) xi + hpNumeratorEndpoint n xi -
        2 * (hpRightLogSum n 0 n xi + hpDenominatorEndpoint xi) := by
  unfold hpProductLogSum hpRightLogSum hpNumeratorEndpoint hpDenominatorEndpoint hpLog
  have hnum :
      Finset.Icc (n + 1) (3 * n + 1) =
        (Finset.Ico (n + 1) (3 * n + 1)).cons (3 * n + 1) (by
          simp [Finset.mem_Ico]) := by
    ext r
    simp only [Finset.mem_Icc, Finset.mem_cons, Finset.mem_Ico]
    omega
  have hden : Finset.Icc 0 n = Finset.range (n + 1) := by
    ext r
    simp only [Finset.mem_Icc, Finset.mem_range]
    omega
  rw [hnum, hden]
  simp only [Finset.sum_cons]
  have hnum_range :
      (∑ x ∈ Finset.Ico (n + 1) (3 * n + 1),
          Real.log ‖xi - ((x : ℝ) / (n : ℝ) : ℂ)‖) =
        ∑ k ∈ Finset.range (2 * n),
          Real.log ‖xi - (((n + k + 1 : ℕ) : ℝ) / (n : ℝ) : ℂ)‖ := by
    rw [Finset.sum_Ico_eq_sum_range]
    have hlen : (3 * n + 1) - (n + 1) = 2 * n := by omega
    rw [hlen]
    apply Finset.sum_congr rfl
    intro k hk
    simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  simp only [Complex.ofReal_div]
  rw [hnum_range]
  have shift_sum (F : ℕ → ℝ) (m : ℕ) :
      (∑ x ∈ Finset.range (m + 1), F x) =
        (∑ k ∈ Finset.range m, F (k + 1)) + F 0 := by
    induction m with
    | zero => simp
    | succ m ih =>
        rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
        ring
  have hden_shift :
      (∑ x ∈ Finset.range (n + 1),
          Real.log ‖xi - (((x : ℝ) / (n : ℝ)) : ℂ)‖) =
        (∑ k ∈ Finset.range n,
          Real.log ‖xi - ((((k + 1 : ℕ) : ℝ) / (n : ℝ)) : ℂ)‖) +
          Real.log ‖xi - (0 : ℂ)‖ := by
    simpa [Complex.ofReal_div] using
      (shift_sum
        (fun x : ℕ => Real.log ‖xi - (((x : ℝ) / (n : ℝ)) : ℂ)‖) n)
  rw [hden_shift]
  simp <;> ring

/-- The continuum part has the same scaled-interval decomposition. -/
theorem hp_product_log_integral_decomp (n : ℕ) (hn : 0 < n) (xi : ℂ) :
    hpProductLogIntegral n xi =
      hpScaledLogIntegral n n (2 * n) xi -
        2 * hpScaledLogIntegral n 0 n xi := by
  unfold hpProductLogIntegral hpScaledLogIntegral
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have h1 : (n : ℝ) / (n : ℝ) = 1 := by field_simp
  have h3 : ((n + 2 * n : ℕ) : ℝ) / (n : ℝ) = 3 := by
    push_cast
    field_simp
    ring
  have h0 : (0 : ℝ) / (n : ℝ) = 0 := by simp
  have h2 : ((0 + n : ℕ) : ℝ) / (n : ℝ) = 1 := by
    simpa using (div_self hnR)
  simp only [Nat.cast_zero, Nat.zero_add]
  rw [h1, h3, h0]
  ring

/-- Exact decomposition of the error into two right-cell errors and the two
endpoint shifts.  The statement is purely algebraic and has no hidden
analytic assumption. -/
theorem hp_product_log_error_decomp (n : ℕ) (hn : 0 < n) (xi : ℂ) :
    hpProductLogError n xi =
      (hpRightLogSum n n (2 * n) xi - hpScaledLogIntegral n n (2 * n) xi) +
        hpNumeratorEndpoint n xi -
        2 * (hpRightLogSum n 0 n xi - hpScaledLogIntegral n 0 n xi) -
        2 * hpDenominatorEndpoint xi := by
  rw [hpProductLogError, hp_product_log_sum_decomp,
    hp_product_log_integral_decomp n hn xi]
  ring

/-- Absolute right-cell error with a common v13 logarithmic allowance. -/
def HpRightErrorBound (C : ℝ) (n a m : ℕ) (xi : ℂ) : Prop :=
  |hpRightLogSum n a m xi - hpScaledLogIntegral n a m xi| ≤
    C * (1 + Real.log ((n + 1 : ℕ) : ℝ))

/-- Absolute endpoint allowance for the two endpoint shifts. -/
def HpEndpointBound (C : ℝ) (n : ℕ) (xi : ℂ) : Prop :=
  |hpNumeratorEndpoint n xi| ≤ C * (1 + Real.log ((n + 1 : ℕ) : ℝ)) ∧
    |hpDenominatorEndpoint xi| ≤ C * (1 + Real.log ((n + 1 : ℕ) : ℝ))

/-- Final glue for the rectangle estimate.  This is the exact linear
combination forced by `hp-tail.tex:281-316`; the first-cell and bounded
variation work enters only through the explicit hypotheses. -/
theorem hp_product_log_error_bound
    (C : ℝ) (hC : 0 ≤ C) (n : ℕ) (hn : 0 < n) (xi : ℂ)
    (hnum : HpRightErrorBound C n n (2 * n) xi)
    (hden : HpRightErrorBound C n 0 n xi)
    (hend : HpEndpointBound C n xi) :
    |hpProductLogError n xi| ≤
      6 * C * (1 + Real.log ((n + 1 : ℕ) : ℝ)) := by
  rw [hp_product_log_error_decomp n hn xi]
  let U : ℝ := hpRightLogSum n n (2 * n) xi - hpScaledLogIntegral n n (2 * n) xi
  let V : ℝ := hpNumeratorEndpoint n xi
  let W : ℝ := hpRightLogSum n 0 n xi - hpScaledLogIntegral n 0 n xi
  let X : ℝ := hpDenominatorEndpoint xi
  have hnum' :
      |hpRightLogSum n n (2 * n) xi - hpScaledLogIntegral n n (2 * n) xi| ≤
        C * (1 + Real.log ((n + 1 : ℕ) : ℝ)) := hnum
  have hden' :
      |hpRightLogSum n 0 n xi - hpScaledLogIntegral n 0 n xi| ≤
        C * (1 + Real.log ((n + 1 : ℕ) : ℝ)) := hden
  have hN : |V| ≤ C * (1 + Real.log ((n + 1 : ℕ) : ℝ)) := hend.1
  have hD : |X| ≤ C * (1 + Real.log ((n + 1 : ℕ) : ℝ)) := hend.2
  have hAdd : |U + V| ≤ |U| + |V| := abs_add_le _ _
  have hSubW : |(U + V) - 2 * W| ≤ |U + V| + 2 * |W| := by
    calc
      |(U + V) - 2 * W| = |(U + V) + -(2 * W)| := by congr 1 <;> ring
      _ ≤ |U + V| + |-(2 * W)| := abs_add_le _ _
      _ = |U + V| + 2 * |W| := by
        rw [abs_neg, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
  have hSubX : |((U + V) - 2 * W) - 2 * X| ≤ |(U + V) - 2 * W| + 2 * |X| := by
    calc
      |((U + V) - 2 * W) - 2 * X| = |((U + V) - 2 * W) + -(2 * X)| := by congr 1 <;> ring
      _ ≤ |(U + V) - 2 * W| + |-(2 * X)| := abs_add_le _ _
      _ = |(U + V) - 2 * W| + 2 * |X| := by
        rw [abs_neg, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
  have hTri : |U + V - 2 * W - 2 * X| ≤ |U| + |V| + 2 * |W| + 2 * |X| := by
    have hEq : U + V - 2 * W - 2 * X = ((U + V) - 2 * W) - 2 * X := by ring
    rw [hEq]
    calc
      |((U + V) - 2 * W) - 2 * X| ≤ |(U + V) - 2 * W| + 2 * |X| := hSubX
      _ ≤ (|U| + |V| + 2 * |W|) + 2 * |X| := by
        have hInner : |(U + V) - 2 * W| ≤ |U| + |V| + 2 * |W| := by
          calc
            |(U + V) - 2 * W| ≤ |U + V| + 2 * |W| := hSubW
            _ ≤ |U| + |V| + 2 * |W| := by linarith [hAdd]
        linarith [hInner]
  have hU : |U| ≤ C * (1 + Real.log ((n + 1 : ℕ) : ℝ)) := by simpa [U] using hnum'
  have hW : |W| ≤ C * (1 + Real.log ((n + 1 : ℕ) : ℝ)) := by simpa [W] using hden'
  calc
    |U + V - 2 * W - 2 * X| ≤ |U| + |V| + 2 * |W| + 2 * |X| := hTri
    _ ≤ 6 * C * (1 + Real.log ((n + 1 : ℕ) : ℝ)) := by
      nlinarith [hU, hN, hW, hD]

/-- Scaled `cpLog` identity used to discharge the right-cell hypotheses. -/
theorem hp_log_scale (n : ℕ) (hn : 0 < n) (xi : ℂ) (u : ℝ)
    (hne : xi - ((u / (n : ℝ)) : ℂ) ≠ 0) :
    hpLog xi (u / (n : ℝ)) =
      cpLog (-((n : ℂ) * xi)) u - Real.log (n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hnorm :
      ‖-((n : ℂ) * xi) + (u : ℂ)‖ =
        (n : ℝ) * ‖xi - ((u / (n : ℝ)) : ℂ)‖ := by
    rw [show -((n : ℂ) * xi) + (u : ℂ) =
        (n : ℂ) * (-(xi - ((u / (n : ℝ)) : ℂ))) by
          push_cast
          field_simp [hnC]
          ring]
    rw [norm_mul, Complex.norm_natCast, norm_neg]
  unfold hpLog cpLog
  simp only [Complex.ofReal_div]
  rw [hnorm, Real.log_mul (by positivity)
    (ne_of_gt (norm_pos_iff.mpr hne))]
  ring

end

end Li2Lean.B4
