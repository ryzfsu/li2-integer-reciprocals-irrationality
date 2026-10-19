/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B4.NegativeContourBottomCellProducer   -- (patched) + BottomBound, Reflection
import Li2Lean.B4.NegativeContourLeftError            -- left error, RealAnalysis
import Li2Lean.B4.NegativeContourRightLogRate         -- right side

open Complex Real Set
open scoped BigOperators Interval

namespace Li2Lean.B4.NegContour

noncomputable section

open Li2Lean.P0.CA.Contour
open Li2Lean.P0.CA.Contour.QI

/-! #### A2.  Tangent certificate from the kernel-checked interval data. -/

theorem hpBottomClosed_phase_eq (q : ℕ) (x : ℝ) :
    hpBottomClosed x - Real.log (q : ℝ) * x + Real.pi / 5 = hpNegBottomH q x := by
  unfold hpBottomClosed hpNegBottomH
  simp only [sub_zero]
  ring

theorem hpNegX0_mem {q : ℕ} (hq : q = 8 ∨ q = 9 ∨ q = 10) :
    (((hpNegX0 q : ℚ) : ℝ)) ∈ hpNegD60 := by
  rcases hq with rfl | rfl | rfl <;>
    simp [hpNegX0, hpNegD60] <;> norm_num      -- [Verified] x0 = 3/100, -1/100, -1/60

/-- `hpNegBottomH q ≤ T_q` on the whole window [-1/60, 61/60].
Inputs: concavity tangent `hpNegBottomH_tangent` (RealAnalysis.lean:103),
enclosures `hpNegHI_mem`/`hpNegH'I_mem` (:181/:194), and the kernel-checked
rational inequality `hpNegTangentCheck_q` (:213-221). -/
theorem hpNegBottomH_le_T {q : ℕ} (hq : q = 8 ∨ q = 9 ∨ q = 10)
    {x : ℝ} (hx : x ∈ hpNegD60) : hpNegBottomH q x ≤ (hpNegT q : ℝ) := by
  have hchk : hpNegTangentCheck q := by
    rcases hq with rfl | rfl | rfl
    · exact hpNegTangentCheck_8
    · exact hpNegTangentCheck_9
    · exact hpNegTangentCheck_10
  set x0 : ℚ := hpNegX0 q with hx0def
  have hx0 : ((x0 : ℚ) : ℝ) ∈ hpNegD60 := hpNegX0_mem hq
  have htan := hpNegBottomH_tangent q hx0 hx
  have hH := (hpNegHI_mem q x0).2               -- H x0 ≤ hi
  have hH' := hpNegH'I_mem q x0                 -- lo ≤ H' x0 ≤ hi
  unfold hpNegTangentCheck at hchk
  simp only [← hx0def] at hchk                  -- [Verified] zeta-reduce the `let`
  set A : ℚ := (hpNegHI q x0).hi
  set lo : ℚ := (hpNegH'I q x0).lo
  set hi : ℚ := (hpNegH'I q x0).hi
  have hchkR : (A : ℝ) + max (max 0 (hi : ℝ) * (61 / 60 - (x0 : ℝ)))
      (max 0 (-(lo : ℝ)) * ((x0 : ℝ) + 1 / 60)) ≤ (hpNegT q : ℝ) := by
    have hcast :
        (A : ℝ) + max (max 0 (hi : ℝ) * (61 / 60 - (x0 : ℝ)))
            (max 0 (-(lo : ℝ)) * ((x0 : ℝ) + 1 / 60)) =
          ((A + max ((max 0 hi) * (61 / 60 - x0))
              ((max 0 (-lo)) * (x0 + 1 / 60)) : ℚ) : ℝ) := by
      norm_num [Rat.cast_max, Rat.cast_neg, Rat.cast_add, Rat.cast_mul]
    rw [hcast]
    exact_mod_cast hchk
  have hslope : hpNegBottomH' q x0 * (x - x0) ≤
      max (max 0 (hi : ℝ) * (61 / 60 - (x0 : ℝ)))
        (max 0 (-(lo : ℝ)) * ((x0 : ℝ) + 1 / 60)) := by
    rcases le_total (x0 : ℝ) x with hle | hle
    · have hd0 : 0 ≤ x - x0 := by linarith
      have hd1 : x - x0 ≤ 61 / 60 - x0 := by linarith [hx.2]
      have hm : hpNegBottomH' q x0 ≤ max 0 (hi : ℝ) := hH'.2.trans (le_max_right _ _)
      have hm0 : 0 ≤ max 0 (hi : ℝ) := le_max_left _ _
      calc hpNegBottomH' q x0 * (x - x0) ≤ max 0 (hi : ℝ) * (x - x0) :=
            mul_le_mul_of_nonneg_right hm hd0
        _ ≤ max 0 (hi : ℝ) * (61 / 60 - x0) := mul_le_mul_of_nonneg_left hd1 hm0
        _ ≤ _ := le_max_left _ _
    · have hd0 : 0 ≤ (x0 : ℝ) - x := by linarith
      have hd1 : (x0 : ℝ) - x ≤ x0 + 1 / 60 := by linarith [hx.1]
      have hm : -hpNegBottomH' q x0 ≤ max 0 (-(lo : ℝ)) :=
        (neg_le_neg hH'.1).trans (le_max_right _ _)
      have hm0 : 0 ≤ max 0 (-(lo : ℝ)) := le_max_left _ _
      calc hpNegBottomH' q x0 * (x - x0) = (-hpNegBottomH' q x0) * ((x0 : ℝ) - x) := by ring
        _ ≤ max 0 (-(lo : ℝ)) * ((x0 : ℝ) - x) := mul_le_mul_of_nonneg_right hm hd0
        _ ≤ max 0 (-(lo : ℝ)) * ((x0 : ℝ) + 1 / 60) := mul_le_mul_of_nonneg_left hd1 hm0
        _ ≤ _ := le_max_right _ _
  linarith

def hpNegBottomTangentCertificate_of_checks {q : ℕ}
    (hq : q = 8 ∨ q = 9 ∨ q = 10) : HpNegBottomTangentCertificate q where
  q_spec := hq
  tangent := fun x hlo hhi => by
    rw [hpBottomClosed_phase_eq]
    exact hpNegBottomH_le_T hq ⟨hlo, hhi⟩

/-! #### Bottom side (unconditional for n ≥ 30). -/

theorem hp_neg_bottom_side_bound_v13 {q n : ℕ} (hq : q = 8 ∨ q = 9 ∨ q = 10)
    (hn : 30 ≤ n) {w : ℂ} (hw : w ∈ hpNegBottomSide n) :
    hpNegBoundaryLog q n w ≤ (n : ℝ) * (hpNegT q : ℝ) +
      18 * (1 + Real.log ((n + 1 : ℕ) : ℝ)) :=
  hp_neg_bottom_side_log_bound_of_cells hq
    (hpNegBottomTangentCertificate_of_checks hq) hp_neg_bottom_cell_input_v13 hn hw

/-! #### Top side by exact reflection (Reflection.lean:118). -/

theorem hp_neg_top_side_bound_v13 {q n : ℕ} (hq : q = 8 ∨ q = 9 ∨ q = 10)
    (hn : 30 ≤ n) {w : ℂ} (hw : w ∈ hpNegTopSide n) :
    hpNegBoundaryLog q n w ≤ (n : ℝ) * (hpNegT q : ℝ) +
      18 * (1 + Real.log ((n + 1 : ℕ) : ℝ)) := by
  have hwb : (starRingEnd ℂ) w ∈ hpNegBottomSide n :=
    hp_neg_top_mem_implies_bottom_mem hw
  have hphi : hpNegPhi n ((starRingEnd ℂ) w) ≠ 0 :=
    hp_neg_bottom_phi_ne_zero (by omega) hwb
  have hrefl : hpNegBoundaryLog q n w =
      hpNegBoundaryLog q n ((starRingEnd ℂ) w) - 2 * Real.pi * ((n : ℝ) / 5) := by
    simpa using hp_neg_boundary_log_bottom_reflection (q := q) (n := n) hwb hphi
  have hbot := hp_neg_bottom_side_bound_v13 hq hn hwb
  have hterm : 0 ≤ 2 * Real.pi * ((n : ℝ) / 5) := by positivity
  linarith

/-! #### Left side. -/

theorem hp_neg_left_phi_ne_zero {n : ℕ} {w : ℂ} (hw : w ∈ hpNegLeftSide n) :
    hpNegPhi n w ≠ 0 := by
  have hre : w.re = -1 / 2 := by
    simpa [hpNegLeftSide, hpRectLower] using hw.1     -- [Verified] shape `-1 / 2`
  have hfactor : ∀ r : ℕ, w - (r : ℂ) ≠ 0 := by
    intro r hz
    have h := congrArg Complex.re hz
    have h' : w.re - (r : ℝ) = 0 := by simpa using h
    have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    linarith
  have hnum : (∏ r ∈ Finset.Icc (n + 1) (3 * n + 1), (w - (r : ℂ))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun r _ => hfactor r)
  have hden : (∏ j ∈ Finset.range (n + 1), ((w - (j : ℂ)) ^ 2)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun j _ => pow_ne_zero 2 (hfactor j))
  rw [hpNegPhi, div_ne_zero_iff]
  exact ⟨hnum, hden⟩

/-- Exact scaling identity (all n > 0, all w with Φ_n(w) ≠ 0):
`L(w) = E_n(w/n) + n · H(w/n) - log n`.  Needs `hp_neg_phi_log_norm_eq_sum`
public (PART 2 (d)). -/
theorem hp_neg_boundary_log_eq_error_add_H {q n : ℕ} (hn : 0 < n) {w : ℂ}
    (hphi : hpNegPhi n w ≠ 0) :
    hpNegBoundaryLog q n w =
      hpProductLogError n (w / (n : ℂ)) + (n : ℝ) * hpNegHfun q (w / (n : ℂ)) -
        Real.log (n : ℝ) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [hp_neg_boundary_log_full_phase hphi, hp_neg_phi_log_norm_eq_sum hn hphi]
  unfold hpProductLogError hpProductLogIntegral hpNegHfun
  have hre : (n : ℝ) * (w / (n : ℂ)).re = w.re := by
    rw [Complex.div_natCast_re]; field_simp
  have him : (n : ℝ) * (w / (n : ℂ)).im = w.im := by
    rw [Complex.div_natCast_im]; field_simp
  rw [← hre, ← him]          -- [Verified] rewrite direction; else finish by `nlinarith`/`ring_nf`
  ring

/-- Lower half of the left side.  v13 hp-tail.tex:344-360. -/
theorem hp_neg_left_lower_bound_v13 {q n : ℕ} (hq : q = 8 ∨ q = 9 ∨ q = 10)
    (hn : 30 ≤ n) {w : ℂ} (hw : w ∈ hpNegLeftSide n) (him : w.im ≤ 0) :
    hpNegBoundaryLog q n w ≤ (n : ℝ) * (hpNegT q : ℝ) +
      18 * (1 + Real.log ((n + 1 : ℕ) : ℝ)) := by
  have hnpos : 0 < n := by omega
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  have hnR30 : (30 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hcoords := hp_neg_left_lower_side_coordinates ⟨hw, him⟩   -- BottomLeft.lean:48
  set x : ℝ := -1 / (2 * (n : ℝ)) with hxdef
  set y : ℝ := w.im / (n : ℝ) with hydef
  have hx_neg : x < 0 := by
    have h2n : (0 : ℝ) < 2 * (n : ℝ) := by positivity
    rw [hxdef]
    exact div_neg_of_neg_of_pos (by norm_num) h2n
  have hy1 : -(1 / 5 : ℝ) ≤ y := by
    rw [hydef, le_div_iff₀ hnR]; linarith [hcoords.2.1]
  have hy2 : y ≤ 0 := div_nonpos_of_nonpos_of_nonneg him hnR.le
  have hxi : w / (n : ℂ) = (x : ℂ) + (y : ℂ) * Complex.I := by
    apply Complex.ext
    · rw [Complex.div_natCast_re, hcoords.1]
      simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re]
      rw [hxdef]
      field_simp [ne_of_gt hnR]
    · rw [Complex.div_natCast_im, hydef]
      simp [Complex.mul_re, Complex.ofReal_re]
  have hxwin : x ∈ hpNegD60 := by
    constructor
    · rw [hxdef, le_div_iff₀ (by positivity)]; nlinarith
    · linarith
  -- (1) scaling identity
  have hphi := hp_neg_left_phi_ne_zero hw
  have hid := hp_neg_boundary_log_eq_error_add_H (q := q) hnpos hphi
  -- (2) phase monotone in depth, then bottom-left corner, then tangent
  have hH : hpNegHfun q (w / (n : ℂ)) ≤ (hpNegT q : ℝ) := by
    rw [hxi]
    calc hpNegHfun q ((x : ℂ) + (y : ℂ) * Complex.I)
        ≤ hpNegHfun q ((x : ℂ) + ((-(1 / 5) : ℝ) : ℂ) * Complex.I) :=
          hpNegHfun_left_le q x hx_neg y hy1 hy2
      _ = hpNegBottomH q x := hpNegHfun_bottom q x
      _ ≤ (hpNegT q : ℝ) := hpNegBottomH_le_T hq hxwin
  -- (3) error bound, proved in the release (LeftError.lean:417)
  have herr := hp_neg_left_product_log_error_bound hn hw
  -- (4) log n ≥ 0
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by linarith)
  have hmul := mul_le_mul_of_nonneg_left hH hnR.le
  rw [hid]
  linarith [(abs_le.mp herr).2]

/-- Whole left side: the upper half by conjugation (Reflection.lean:49). -/
theorem hp_neg_left_bound_v13 {q n : ℕ} (hq : q = 8 ∨ q = 9 ∨ q = 10)
    (hn : 30 ≤ n) {w : ℂ} (hw : w ∈ hpNegLeftSide n) :
    hpNegBoundaryLog q n w ≤ (n : ℝ) * (hpNegT q : ℝ) +
      18 * (1 + Real.log ((n + 1 : ℕ) : ℝ)) := by
  by_cases him : w.im ≤ 0
  · exact hp_neg_left_lower_bound_v13 hq hn hw him
  · push_neg at him
    have hc : (starRingEnd ℂ) w ∈ hpNegLeftSide n := hp_neg_left_mem_implies_left_mem hw
    have hconj := hp_neg_boundary_log_conj q n (hp_neg_left_phi_ne_zero hw)
    have hlow := hp_neg_left_lower_bound_v13 hq hn hc (by simp; linarith)
    have hpos : 0 ≤ 2 * Real.pi * w.im := by positivity
    linarith

/-! #### A4.  Direct assembly: no envelope, no data fields. -/

theorem hpNegBorderBound_of_v13 {q : ℕ} (hq : q = 8 ∨ q = 9 ∨ q = 10) :
    HpNegBorderBound q := by
  intro n hn w hw
  rw [hpNegBorder_eq_union_sides] at hw
  rcases hw with ((hb | hl) | ht) | hr
  · exact hp_neg_bottom_side_bound_v13 hq hn hb
  · exact hp_neg_left_bound_v13 hq hn hl
  · exact hp_neg_top_side_bound_v13 hq hn ht
  · exact hp_neg_right_logarithmic_bound hq hn hr     -- RightLogRate.lean:373

end

end Li2Lean.B4.NegContour

#print axioms Li2Lean.B4.NegContour.hpNegBottomH_le_T
#print axioms Li2Lean.B4.NegContour.hp_neg_left_bound_v13
#print axioms Li2Lean.B4.NegContour.hpNegBorderBound_of_v13
