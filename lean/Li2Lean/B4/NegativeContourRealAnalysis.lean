/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B4.NegativeContourTangent
import Li2Lean.P0.CA.Contour.ClosedForm
import Li2Lean.P0.CA.Contour.Eval
import Li2Lean.P0.CA.Contour.LogAtan
import Li2Lean.P0.CA.Contour.Arith

open MeasureTheory
open scoped BigOperators Interval

namespace Li2Lean.B4.NegContour

noncomputable section

open Li2Lean.P0.CA.Contour
open Li2Lean.P0.CA.Contour.QI

/-! The scaled limiting phase from `hp-tail.tex:307-371`. -/
def hpNegHfun (q : ℕ) (ξ : ℂ) : ℝ :=
  ((∫ x in (1 : ℝ)..3, hpLog ξ x) - 2 * (∫ x in (0 : ℝ)..1, hpLog ξ x)) -
    Real.log (q : ℝ) * ξ.re - Real.pi * ξ.im

/-! Bottom side closed form and its first two derivatives. -/
def hpNegBottomH (q : ℕ) (x : ℝ) : ℝ :=
  3 * Gr (x - 1) (-(1 / 5)) - Gr (x - 3) (-(1 / 5)) - 2 * Gr x (-(1 / 5)) -
    Real.log (q : ℝ) * x + Real.pi / 5

theorem hpNegHfun_bottom (q : ℕ) (x : ℝ) :
    hpNegHfun q ((x : ℂ) + ((-(1 / 5) : ℝ) : ℂ) * Complex.I) = hpNegBottomH q x := by
  unfold hpNegHfun hpNegBottomH hpLog
  rw [integral_log_norm_sub (by norm_num) 1 3,
    integral_log_norm_sub (by norm_num) 0 1]
  simp
  ring

def hpNegBottomH' (q : ℕ) (x : ℝ) : ℝ :=
  3 * (Real.log ((x - 1) ^ 2 + (-(1 / 5) : ℝ) ^ 2) / 2) -
    Real.log ((x - 3) ^ 2 + (-(1 / 5) : ℝ) ^ 2) / 2 -
    2 * (Real.log (x ^ 2 + (-(1 / 5) : ℝ) ^ 2) / 2) - Real.log (q : ℝ)

theorem hasDerivAt_bottomH (q : ℕ) (x : ℝ) :
    HasDerivAt (hpNegBottomH q) (hpNegBottomH' q x) x := by
  have hY : (-(1 / 5) : ℝ) ≠ 0 := by norm_num
  have g1 := (hasDerivAt_Gr hY (x - 1)).comp x ((hasDerivAt_id x).sub_const 1)
  have g3 := (hasDerivAt_Gr hY (x - 3)).comp x ((hasDerivAt_id x).sub_const 3)
  have g0 := hasDerivAt_Gr hY x
  have hl : HasDerivAt (fun v : ℝ => Real.log (q : ℝ) * v) (Real.log q) x := by
    simpa using (hasDerivAt_id x).const_mul (Real.log (q : ℝ))
  have h := (((g1.const_mul 3).sub g3).sub (g0.const_mul 2)).sub hl
  convert h.add_const (Real.pi / 5) using 1
  · funext v
    simp [hpNegBottomH, Function.comp]
  · simp [hpNegBottomH']

def hpNegBottomH'' (x : ℝ) : ℝ :=
  -6 * hpNegP x / (hpNegD 0 x * hpNegD 1 x * hpNegD 3 x)

theorem hasDerivAt_logsq_half (c x : ℝ) :
    HasDerivAt (fun v => Real.log ((v - c) ^ 2 + (-(1 / 5) : ℝ) ^ 2) / 2)
      ((x - c) / hpNegD c x) x := by
  have hpos : 0 < (x - c) ^ 2 + (-(1 / 5) : ℝ) ^ 2 := by positivity
  have h1 : HasDerivAt (fun v : ℝ => (v - c) ^ 2 + (-(1 / 5) : ℝ) ^ 2)
      (2 * (x - c)) x := by
    simpa using (((hasDerivAt_id x).sub_const c).pow 2).add_const
      ((-(1 / 5 : ℝ)) ^ 2)
  convert (h1.log hpos.ne').div_const 2 using 1
  simp only [hpNegD]
  field_simp

theorem hasDerivAt_bottomH' (q : ℕ) (x : ℝ) :
    HasDerivAt (hpNegBottomH' q) (hpNegBottomH'' x) x := by
  have d1 := hasDerivAt_logsq_half 1 x
  have d3 := hasDerivAt_logsq_half 3 x
  have d0 := hasDerivAt_logsq_half 0 x
  have h := (((d1.const_mul 3).sub d3).sub (d0.const_mul 2)).sub_const (Real.log (q : ℝ))
  convert h using 1
  · funext v
    simp [hpNegBottomH']
  · have h0 := hp_neg_D_pos 0 x
    have h1 := hp_neg_D_pos 1 x
    have h3 := hp_neg_D_pos 3 x
    simp only [hpNegBottomH'', sub_zero]
    field_simp
    linear_combination (-1 : ℝ) * hp_neg_concavity_numerator_identity x

theorem bottomH''_nonpos {x : ℝ} (hx1 : -(1 / 60 : ℝ) ≤ x) (hx2 : x ≤ 61 / 60) :
    hpNegBottomH'' x ≤ 0 := by
  have hp := hp_neg_p_pos_on_window hx1 hx2
  have hD := mul_pos (mul_pos (hp_neg_D_pos 0 x) (hp_neg_D_pos 1 x)) (hp_neg_D_pos 3 x)
  unfold hpNegBottomH''
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) hD.le

def hpNegD60 : Set ℝ := Set.Icc (-(1 / 60 : ℝ)) (61 / 60)

theorem bottomH'_antitoneOn (q : ℕ) : AntitoneOn (hpNegBottomH' q) hpNegD60 := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
  · exact fun x _ => (hasDerivAt_bottomH' q x).continuousAt.continuousWithinAt
  · exact fun x _ => (hasDerivAt_bottomH' q x).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    rw [(hasDerivAt_bottomH' q x).deriv]
    exact bottomH''_nonpos hx.1.le hx.2.le

theorem hpNegBottomH_tangent (q : ℕ) {x0 x : ℝ} (hx0 : x0 ∈ hpNegD60)
    (hx : x ∈ hpNegD60) :
    hpNegBottomH q x ≤ hpNegBottomH q x0 + hpNegBottomH' q x0 * (x - x0) := by
  by_cases h : x0 ≤ x
  · let φ : ℝ → ℝ := fun t => hpNegBottomH q t - hpNegBottomH' q x0 * t
    have hφderiv (t : ℝ) : HasDerivAt φ
        (hpNegBottomH' q t - hpNegBottomH' q x0) t := by
      convert (hasDerivAt_bottomH q t).sub
        ((hasDerivAt_id t).const_mul (hpNegBottomH' q x0)) using 1
      · funext v
        simp [φ]
      · simp [φ]
    have hcont : ContinuousOn φ (Set.Icc x0 x) := by
      intro t ht
      exact (hφderiv t).continuousAt.continuousWithinAt
    have hdiff : DifferentiableOn ℝ φ (Set.Ioo x0 x) := by
      intro t ht
      exact (hφderiv t).differentiableAt.differentiableWithinAt
    have hderiv : ∀ t ∈ Set.Ioo x0 x, deriv φ t ≤ 0 := by
      intro t ht
      have htd : t ∈ hpNegD60 := ⟨le_trans hx0.1 (le_of_lt ht.1),
        le_trans (le_of_lt ht.2) hx.2⟩
      have hanti := bottomH'_antitoneOn q hx0 htd (le_of_lt ht.1)
      rw [(hφderiv t).deriv]
      linarith
    have hmono : AntitoneOn φ (Set.Icc x0 x) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
      · exact hcont
      · simpa [interior_Icc] using hdiff
      · simpa [interior_Icc] using hderiv
    have hφ := hmono ⟨le_rfl, h⟩ ⟨h, le_rfl⟩ h
    dsimp [φ] at hφ
    linarith
  · have hle : x ≤ x0 := le_of_not_ge h
    let φ : ℝ → ℝ := fun t => hpNegBottomH q t - hpNegBottomH' q x0 * t
    have hφderiv (t : ℝ) : HasDerivAt φ
        (hpNegBottomH' q t - hpNegBottomH' q x0) t := by
      convert (hasDerivAt_bottomH q t).sub
        ((hasDerivAt_id t).const_mul (hpNegBottomH' q x0)) using 1
      · funext v
        simp [φ]
      · simp [φ]
    have hcont : ContinuousOn φ (Set.Icc x x0) := by
      intro t ht
      exact (hφderiv t).continuousAt.continuousWithinAt
    have hdiff : DifferentiableOn ℝ φ (Set.Ioo x x0) := by
      intro t ht
      exact (hφderiv t).differentiableAt.differentiableWithinAt
    have hderiv : ∀ t ∈ Set.Ioo x x0, 0 ≤ deriv φ t := by
      intro t ht
      have htd : t ∈ hpNegD60 := ⟨le_trans hx.1 (le_of_lt ht.1),
        le_trans (le_of_lt ht.2) hx0.2⟩
      have hanti := bottomH'_antitoneOn q htd hx0 (le_of_lt ht.2)
      rw [(hφderiv t).deriv]
      linarith
    have hmono : MonotoneOn φ (Set.Icc x x0) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      · exact hcont
      · simpa [interior_Icc] using hdiff
      · simpa [interior_Icc] using hderiv
    have hφ := hmono ⟨le_rfl, hle⟩ ⟨hle, le_rfl⟩ hle
    dsimp [φ] at hφ
    linarith

/-! Certified rational enclosures for the tangent checks. -/
def hpNegX0 (q : ℕ) : ℚ :=
  if q = 8 then 3 / 100 else if q = 9 then -(1 / 100) else -(1 / 60)

def hpNegHI (q : ℕ) (x0 : ℚ) : QI :=
  add (sub (sub (sub (smul 3 (edge (x0 - 1) (-(1 / 5))).g)
      (edge (x0 - 3) (-(1 / 5))).g) (smul 2 (edge x0 (-(1 / 5))).g))
      (smul x0 (logI (q : ℚ)))) (smul (1 / 5) PI)

def hpNegH'I (q : ℕ) (x0 : ℚ) : QI :=
  sub (sub (sub (smul 3 (edge (x0 - 1) (-(1 / 5))).l)
      (edge (x0 - 3) (-(1 / 5))).l) (smul 2 (edge x0 (-(1 / 5))).l))
      (logI (q : ℚ))

theorem hpNegHI_mem (q : ℕ) (x0 : ℚ) :
    (hpNegHI q x0).mem (hpNegBottomH q x0) := by
  have e1 := (edge_ok (x0 - 1) (-(1 / 5))).1
  have e3 := (edge_ok (x0 - 3) (-(1 / 5))).1
  have e0 := (edge_ok x0 (-(1 / 5))).1
  have hl := logI_mem (q := (q : ℚ)) (by positivity)
  have h := mem_add (mem_sub (mem_sub (mem_sub (mem_smul 3 e1) e3)
    (mem_smul 2 e0)) (mem_smul x0 hl)) (mem_smul (1 / 5) PI_mem)
  refine mem_of_eq h ?_
  unfold hpNegBottomH
  push_cast
  ring

theorem hpNegH'I_mem (q : ℕ) (x0 : ℚ) :
    (hpNegH'I q x0).mem (hpNegBottomH' q x0) := by
  have e1 := (edge_ok (x0 - 1) (-(1 / 5))).2.1
  have e3 := (edge_ok (x0 - 3) (-(1 / 5))).2.1
  have e0 := (edge_ok x0 (-(1 / 5))).2.1
  have hl := logI_mem (q := (q : ℚ)) (by positivity)
  have h := mem_sub (mem_sub (mem_sub (mem_smul 3 e1) e3)
    (mem_smul 2 e0)) hl
  refine mem_of_eq h ?_
  unfold hpNegBottomH'
  push_cast
  ring

def hpNegTangentCheck (q : ℕ) : Prop :=
  let x0 := hpNegX0 q
  (hpNegHI q x0).hi +
      max (max 0 (hpNegH'I q x0).hi * (61 / 60 - x0))
        (max 0 (-(hpNegH'I q x0).lo) * (x0 + 1 / 60)) ≤ hpNegT q

theorem hpNegTangentCheck_8 : hpNegTangentCheck 8 := by
  unfold hpNegTangentCheck
  decide +kernel

theorem hpNegTangentCheck_9 : hpNegTangentCheck 9 := by
  unfold hpNegTangentCheck
  decide +kernel

theorem hpNegTangentCheck_10 : hpNegTangentCheck 10 := by
  unfold hpNegTangentCheck
  decide +kernel

/-! Lower-left closed form: `Kr` is smooth in the depth, including `y=0`. -/
def Kr (t y : ℝ) : ℝ :=
  t * (Real.log (t ^ 2 + y ^ 2) / 2 - 1) - y * Real.arctan (y / t)

theorem hasDerivAt_Kr_t {t : ℝ} (ht : 0 < t) (y : ℝ) :
    HasDerivAt (fun v => Kr v y) (Real.log (t ^ 2 + y ^ 2) / 2) t := by
  have hpos : 0 < t ^ 2 + y ^ 2 := by positivity
  have hs : HasDerivAt (fun v : ℝ => v ^ 2 + y ^ 2) (2 * t) t := by
    simpa using (hasDerivAt_pow 2 t).add_const (y ^ 2)
  have hlog := hs.log hpos.ne'
  have hA := (hasDerivAt_id t).mul ((hlog.div_const 2).sub_const 1)
  have hq : HasDerivAt (fun v : ℝ => y / v) (-y / t ^ 2) t := by
    convert (hasDerivAt_const t y).div (hasDerivAt_id t) ht.ne' using 1
    · funext v
      simp [id]
    · simp [id]
  have hB := (hq.arctan).const_mul (-y)
  have h := hA.add hB
  convert h using 1
  · funext v
    dsimp [Kr]
    ring
  · simp [id]
    field_simp [ht.ne']
    ring

theorem hasDerivAt_Kr_y {t : ℝ} (ht : 0 < t) (y : ℝ) :
    HasDerivAt (fun v => Kr t v) (-Real.arctan (y / t)) y := by
  have hpos : 0 < t ^ 2 + y ^ 2 := by positivity
  have hs : HasDerivAt (fun v : ℝ => t ^ 2 + v ^ 2) (2 * y) y := by
    simpa using (hasDerivAt_pow 2 y).const_add (t ^ 2)
  have hlog := hs.log hpos.ne'
  have hA := ((hlog.div_const 2).sub_const 1).const_mul t
  have hq : HasDerivAt (fun v : ℝ => v / t) (1 / t) y := by
    simpa using (hasDerivAt_id y).div_const t
  have hB := (hasDerivAt_id y).mul hq.arctan
  have h := hA.sub hB
  convert h using 1
  · funext v
    dsimp [Kr]
  · simp [id]
    field_simp [ht.ne']
    ring

theorem integral_log_norm_sub_left {X y a b : ℝ} (ha : X < a) (hab : a ≤ b) :
    (∫ x in a..b, Real.log ‖((X : ℂ) + (y : ℂ) * Complex.I) - (x : ℂ)‖) =
      Kr (b - X) y - Kr (a - X) y := by
  simp_rw [log_norm_eq]
  have hsq : ∀ x : ℝ, (X - x) ^ 2 + y ^ 2 = (x - X) ^ 2 + y ^ 2 := by
    intro x
    ring
  simp_rw [hsq]
  rw [intervalIntegral.integral_comp_sub_right
    (fun s : ℝ => Real.log (s ^ 2 + y ^ 2) / 2) X]
  have hax : 0 < a - X := sub_pos.mpr ha
  have hle : a - X ≤ b - X := sub_le_sub_right hab X
  have hcont : ContinuousOn (fun s : ℝ => Real.log (s ^ 2 + y ^ 2) / 2)
      (Set.uIcc (a - X) (b - X)) := by
    rw [Set.uIcc_of_le hle]
    apply ContinuousOn.div_const
    apply ContinuousOn.log
    · fun_prop
    · intro s hs
      have hspos : 0 < s := lt_of_lt_of_le hax hs.1
      exact (show 0 < s ^ 2 + y ^ 2 by positivity).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs => hasDerivAt_Kr_t (lt_of_lt_of_le hax
      (by
        rw [Set.uIcc_of_le hle] at hs
        exact hs.1)) y)
    hcont.intervalIntegrable]

def hpNegLeftH (q : ℕ) (x y : ℝ) : ℝ :=
  Kr (3 - x) y - 3 * Kr (1 - x) y + 2 * Kr (-x) y -
    Real.log (q : ℝ) * x - Real.pi * y

theorem hpNegHfun_left (q : ℕ) {x : ℝ} (hx : x < 0) (y : ℝ) :
    hpNegHfun q ((x : ℂ) + (y : ℂ) * Complex.I) = hpNegLeftH q x y := by
  unfold hpNegHfun hpNegLeftH hpLog
  rw [integral_log_norm_sub_left (by linarith) (by norm_num),
    integral_log_norm_sub_left (by linarith) (by norm_num)]
  simp
  ring

theorem leftH_deriv_neg {x y : ℝ} (hx : x < 0) (hy : y ≤ 0) :
    -Real.arctan (y / (3 - x)) + 3 * Real.arctan (y / (1 - x)) -
        2 * Real.arctan (y / -x) - Real.pi < 0 := by
  have h3 : 0 < 3 - x := by linarith
  have h1 : 0 < 1 - x := by linarith
  have h0 : 0 < -x := by linarith
  have h31 : y / (1 - x) ≤ y / (3 - x) := by
    apply (div_le_div_iff₀ h1 h3).2
    nlinarith [mul_le_mul_of_nonpos_left (show 1 - x ≤ 3 - x by linarith) hy]
  have ha31 : Real.arctan (y / (1 - x)) ≤ Real.arctan (y / (3 - x)) :=
    Real.arctan_mono h31
  have ha1 : Real.arctan (y / (1 - x)) ≤ 0 := by
    rw [show y / (1 - x) = -((-y) / (1 - x)) by ring, Real.arctan_neg]
    have hy' : 0 ≤ -y := by linarith
    exact neg_nonpos.mpr ((Real.arctan_nonneg).2 (div_nonneg hy' h1.le))
  have ha0 : Real.arctan (-y / -x) < Real.pi / 2 :=
    Real.arctan_lt_pi_div_two _
  have hneg : Real.arctan (y / -x) = -Real.arctan (-y / -x) := by
    rw [show y / -x = -((-y) / -x) by ring, Real.arctan_neg]
  rw [hneg]
  have hpair : -Real.arctan (y / (3 - x)) +
      Real.arctan (y / (1 - x)) ≤ 0 := by linarith
  nlinarith

theorem hpNegLeftH_antitone (q : ℕ) {x : ℝ} (hx : x < 0) :
    AntitoneOn (hpNegLeftH q x) (Set.Icc (-(1 / 5) : ℝ) 0) := by
  have hleft_deriv (y : ℝ) :
      HasDerivAt (hpNegLeftH q x)
        (-Real.arctan (y / (3 - x)) + 3 * Real.arctan (y / (1 - x)) -
          2 * Real.arctan (y / -x) - Real.pi) y := by
    have h3 : 0 < 3 - x := by linarith
    have h1 : 0 < 1 - x := by linarith
    have h0 : 0 < -x := by linarith
    have hpi := (hasDerivAt_id y).const_mul (Real.pi)
    have h := (((hasDerivAt_Kr_y h3 y).sub
      ((hasDerivAt_Kr_y h1 y).const_mul 3)).add
      ((hasDerivAt_Kr_y h0 y).const_mul 2)).sub hpi
    have hconst := h.add_const (-Real.log (q : ℝ) * x)
    convert hconst using 1
    · funext v
      dsimp [hpNegLeftH, Kr]
      ring
    · simp [id]
      ring
  apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
  · intro y hy
    exact (hleft_deriv y).continuousAt.continuousWithinAt
  · intro y hy
    exact (hleft_deriv y).differentiableAt.differentiableWithinAt
  · intro y hy
    rw [(hleft_deriv y).deriv]
    rw [interior_Icc] at hy
    exact le_of_lt (by
      have h := leftH_deriv_neg hx hy.2.le
      linarith)

theorem hpNegHfun_left_le (q : ℕ) (x : ℝ) (hx : x < 0) (y : ℝ)
    (hy1 : -(1 / 5 : ℝ) ≤ y) (hy2 : y ≤ 0) :
    hpNegHfun q ((x : ℂ) + (y : ℂ) * Complex.I) ≤
      hpNegHfun q ((x : ℂ) + ((-(1 / 5) : ℝ) : ℂ) * Complex.I) := by
  rw [hpNegHfun_left q hx, hpNegHfun_left q hx]
  exact hpNegLeftH_antitone q hx ⟨le_rfl, by norm_num⟩ ⟨hy1, hy2⟩ hy1

end

end Li2Lean.B4.NegContour

#print axioms Li2Lean.B4.NegContour.hpNegHfun_left_le
#print axioms Li2Lean.B4.NegContour.hpNegTangentCheck_9
