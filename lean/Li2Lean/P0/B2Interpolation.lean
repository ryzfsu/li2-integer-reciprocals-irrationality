/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Mathlib

namespace Li2Lean

noncomputable section

/-- The logarithmic interpolation parameter used for positive integer bases. -/
def positiveBaseParameter (q : ℕ) : ℝ := Real.log ((q : ℝ) / 2)

theorem positiveBaseParameter_two : positiveBaseParameter 2 = 0 := by
  norm_num [positiveBaseParameter]

theorem positiveBaseParameter_eleven :
    positiveBaseParameter 11 = Real.log ((11 : ℝ) / 2) := by
  rfl

/-- A concave function dominates the chord joining lower endpoint bounds. -/
theorem concave_chord_lower
    {L : ℝ} {f : ℝ → ℝ} {a0 aL : ℝ}
    (hL : 0 < L)
    (hconc : ConcaveOn ℝ (Set.Icc 0 L) f)
    (h0 : a0 ≤ f 0) (h1 : aL ≤ f L)
    {x : ℝ} (hx0 : 0 ≤ x) (hxL : x ≤ L) :
    a0 + (x / L) * (aL - a0) ≤ f x := by
  by_cases hzero : x = 0
  · subst x
    simpa using h0
  by_cases hlast : x = L
  · subst x
    field_simp
    simpa using h1
  have hxpos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hzero)
  have hxlt : x < L := lt_of_le_of_ne hxL hlast
  have hbpos : 0 < x / L := div_pos hxpos hL
  have hapos : 0 < 1 - x / L := sub_pos.mpr ((div_lt_one hL).2 hxlt)
  have hab : (1 - x / L) + x / L = (1 : ℝ) := by ring
  have hmem0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) L := ⟨le_rfl, hL.le⟩
  have hmemL : L ∈ Set.Icc (0 : ℝ) L := ⟨hL.le, le_rfl⟩
  have hc := (concaveOn_iff_forall_pos.mp hconc).2 hmem0 hmemL
      hapos hbpos hab
  have harg : (1 - x / L) • (0 : ℝ) + (x / L) • L = x := by
    simp only [smul_eq_mul, mul_zero, zero_add]
    field_simp
  rw [harg] at hc
  have hc' : (1 - x / L) * f 0 + (x / L) * f L ≤ f x := by
    simpa only [smul_eq_mul] using hc
  nlinarith

/-- The positive-base parameter lies in the interpolation interval for
`2 ≤ q ≤ 11`. -/
theorem positiveBaseParameter_mem
    {q : ℕ} (hq2 : 2 ≤ q) (hq11 : q ≤ 11) :
    positiveBaseParameter q ∈ Set.Icc (0 : ℝ) (Real.log ((11 : ℝ) / 2)) := by
  unfold positiveBaseParameter
  constructor
  · have hq : (2 : ℝ) ≤ q := by exact_mod_cast hq2
    have hpos : 0 < (2 : ℝ) := by norm_num
    have hratio : (1 : ℝ) ≤ (q : ℝ) / 2 := by
      rw [le_div_iff₀ hpos]
      simpa using hq
    exact Real.log_nonneg hratio
  · have hq : (q : ℝ) ≤ 11 := by exact_mod_cast hq11
    have hratio : (q : ℝ) / 2 ≤ (11 : ℝ) / 2 := by
      exact (div_le_div_of_nonneg_right hq (by norm_num))
    have hqpos : 0 < (q : ℝ) / 2 := by positivity
    have h11pos : 0 < (11 : ℝ) / 2 := by norm_num
    exact Real.strictMonoOn_log.monotoneOn hqpos h11pos hratio

/-- The shared positive-base interpolation step. Endpoint lower bounds for
the fixed variational problem imply the lower bound at every integer base
`2 ≤ q ≤ 11`, with the paper's parameter `lambda = log(q/2)`.

The analytic endpoint certificates and the arithmetic rate are intentionally
separate inputs: this theorem only transports the variational lower bound. -/
theorem positiveBaseInterpolation
    {f : ℝ → ℝ} {alpha2 alpha11 : ℝ}
    (hL : 0 < Real.log ((11 : ℝ) / 2))
    (hconc : ConcaveOn ℝ (Set.Icc (0 : ℝ) (Real.log ((11 : ℝ) / 2))) f)
    (h2 : alpha2 ≤ f 0) (h11 : alpha11 ≤ f (Real.log ((11 : ℝ) / 2)))
    {q : ℕ} (hq2 : 2 ≤ q) (hq11 : q ≤ 11) :
    alpha2 +
        (positiveBaseParameter q / Real.log ((11 : ℝ) / 2)) *
          (alpha11 - alpha2) ≤ f (positiveBaseParameter q) := by
  have hmem := positiveBaseParameter_mem hq2 hq11
  exact concave_chord_lower hL hconc h2 h11 hmem.1 hmem.2

/-- v13's endpoint constants transported to every integer base in the finite
positive range.  The endpoint inequalities are explicit inputs: q=2 and q=11
certificate modules provide them independently. -/
theorem positiveBaseEndpointChord
    {alpha : ℝ → ℝ}
    (hconc : ConcaveOn ℝ (Set.Icc (0 : ℝ) (Real.log ((11 : ℝ) / 2))) alpha)
    (h2 : (248035 / 125000 : ℝ) ≤ alpha 0)
    (h11 : (77597 / 100000 : ℝ) ≤ alpha (Real.log ((11 : ℝ) / 2)))
    {q : ℕ} (hq2 : 2 ≤ q) (hq11 : q ≤ 11) :
    (248035 / 125000 : ℝ) +
        (positiveBaseParameter q / Real.log ((11 : ℝ) / 2)) *
          ((77597 / 100000 : ℝ) - 248035 / 125000) ≤
      alpha (positiveBaseParameter q) := by
  have hL : 0 < Real.log ((11 : ℝ) / 2) := by
    apply Real.log_pos
    norm_num
  exact positiveBaseInterpolation hL hconc h2 h11 hq2 hq11

end

end Li2Lean

#print axioms Li2Lean.concave_chord_lower
#print axioms Li2Lean.positiveBaseParameter_mem
#print axioms Li2Lean.positiveBaseInterpolation
#print axioms Li2Lean.positiveBaseEndpointChord
