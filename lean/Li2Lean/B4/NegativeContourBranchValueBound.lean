/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B4.NegativeContourQSpecificProducers

open Complex Real Set MeasureTheory intervalIntegral
open scoped BigOperators Interval

namespace Li2Lean.B4.NegativeContour

noncomputable section

open Li2Lean.B4
open Li2Lean.B4.NegContour
open Li2Lean.B4.NegContourResidueProducer

private lemma hp_neg_rect_bottom_re {n : ℕ} {t : ℝ} :
    (hpTailRectEdgeMap (-1 / 2) ((n : ℝ) + 1 / 2)
      (-((n : ℝ) / 5)) ((n : ℝ) / 5) HpTailRectEdge.bottom t).re =
      -(1 / 2 : ℝ) + ((n : ℝ) + 1) * t := by
  simp [hpTailRectEdgeMap, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im] <;> norm_num <;> ring <;> aesop

private lemma hp_neg_rect_bottom_im {n : ℕ} {t : ℝ} :
    (hpTailRectEdgeMap (-1 / 2) ((n : ℝ) + 1 / 2)
      (-((n : ℝ) / 5)) ((n : ℝ) / 5) HpTailRectEdge.bottom t).im =
      -((n : ℝ) / 5) := by
  simp [hpTailRectEdgeMap, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im] <;> norm_num <;> ring <;> aesop

private lemma hp_neg_rect_right_re {n : ℕ} {t : ℝ} :
    (hpTailRectEdgeMap (-1 / 2) ((n : ℝ) + 1 / 2)
      (-((n : ℝ) / 5)) ((n : ℝ) / 5) HpTailRectEdge.right t).re =
      (n : ℝ) + 1 / 2 := by
  simp [hpTailRectEdgeMap, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im] <;> norm_num <;> ring <;> aesop

private lemma hp_neg_rect_right_im {n : ℕ} {t : ℝ} :
    (hpTailRectEdgeMap (-1 / 2) ((n : ℝ) + 1 / 2)
      (-((n : ℝ) / 5)) ((n : ℝ) / 5) HpTailRectEdge.right t).im =
      -((n : ℝ) / 5) + ((n : ℝ) * 2 / 5) * t := by
  simp [hpTailRectEdgeMap, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im] <;> norm_num <;> ring <;> aesop

private lemma hp_neg_rect_top_re {n : ℕ} {t : ℝ} :
    (hpTailRectEdgeMap (-1 / 2) ((n : ℝ) + 1 / 2)
      (-((n : ℝ) / 5)) ((n : ℝ) / 5) HpTailRectEdge.top t).re =
      (n : ℝ) + 1 / 2 - ((n : ℝ) + 1) * t := by
  simp [hpTailRectEdgeMap, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im] <;> norm_num <;> ring <;> aesop

private lemma hp_neg_rect_top_im {n : ℕ} {t : ℝ} :
    (hpTailRectEdgeMap (-1 / 2) ((n : ℝ) + 1 / 2)
      (-((n : ℝ) / 5)) ((n : ℝ) / 5) HpTailRectEdge.top t).im =
      (n : ℝ) / 5 := by
  simp [hpTailRectEdgeMap, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im] <;> norm_num <;> ring <;> aesop

private lemma hp_neg_rect_left_re {n : ℕ} {t : ℝ} :
    (hpTailRectEdgeMap (-1 / 2) ((n : ℝ) + 1 / 2)
      (-((n : ℝ) / 5)) ((n : ℝ) / 5) HpTailRectEdge.left t).re =
      -(1 / 2 : ℝ) := by
  simp [hpTailRectEdgeMap, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im] <;> norm_num <;> ring <;> aesop

private lemma hp_neg_rect_left_im {n : ℕ} {t : ℝ} :
    (hpTailRectEdgeMap (-1 / 2) ((n : ℝ) + 1 / 2)
      (-((n : ℝ) / 5)) ((n : ℝ) / 5) HpTailRectEdge.left t).im =
      (n : ℝ) / 5 - ((n : ℝ) * 2 / 5) * t := by
  simp [hpTailRectEdgeMap, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im] <;> norm_num <;> ring <;> aesop

private lemma hp_neg_rect_edge_map_mem_border {n : ℕ}
    {e : HpTailRectEdge} {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    hpTailRectEdgeMap (-1 / 2) ((n : ℝ) + 1 / 2)
      (-((n : ℝ) / 5)) ((n : ℝ) / 5) e t ∈ hpNegBorder n := by
  rw [hpNegBorder_eq_union_sides]
  simp only [Set.mem_union]
  rcases ht with ⟨ht0, ht1⟩
  cases e with
  | bottom =>
      apply Or.inl
      apply Or.inl
      apply Or.inl
      simp only [hpNegBottomSide, Set.mem_setOf_eq, hpRectLower, hpRectUpper]
      rw [hp_neg_rect_bottom_re, hp_neg_rect_bottom_im]
      constructor
      · nlinarith
      constructor
      · nlinarith
      · ring
  | right =>
      apply Or.inr
      simp only [hpNegRightSide, Set.mem_setOf_eq, hpRectLower, hpRectUpper]
      rw [hp_neg_rect_right_re, hp_neg_rect_right_im]
      constructor
      · rfl
      constructor <;> nlinarith
  | top =>
      apply Or.inl
      apply Or.inr
      simp only [hpNegTopSide, Set.mem_setOf_eq, hpRectLower, hpRectUpper]
      rw [hp_neg_rect_top_re, hp_neg_rect_top_im]
      constructor
      · nlinarith
      constructor
      · nlinarith
      · ring
  | left =>
      apply Or.inl
      apply Or.inl
      apply Or.inr
      simp only [hpNegLeftSide, Set.mem_setOf_eq, hpRectLower, hpRectUpper]
      rw [hp_neg_rect_left_re, hp_neg_rect_left_im]
      constructor
      · ring
      constructor <;> nlinarith

private lemma hp_neg_kernel_norm_le_exp {q n : ℕ}
    (boundary : HpNegBorderBound q) (hn : 30 ≤ n)
    {w : ℂ} (hw : w ∈ hpNegBorder n) :
    ‖hpTailKernelPlus q n w‖ ≤
      Real.exp ((n : ℝ) * (hpNegT q : ℝ) +
        18 * (1 + Real.log ((n + 1 : ℕ) : ℝ))) := by
  have hlog : Real.log ‖hpTailKernelPlus q n w‖ ≤
      (n : ℝ) * (hpNegT q : ℝ) +
        18 * (1 + Real.log ((n + 1 : ℕ) : ℝ)) := by
    simpa [hpNegBoundaryLog, hpTailKernelPlus, hpNegLambda,
      hpNegPhi, hpTailPhi] using boundary n hn w hw
  by_cases hz : ‖hpTailKernelPlus q n w‖ = 0
  · simp [hz, (Real.exp_pos _).le]
  · exact (Real.log_le_iff_le_exp
      (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz))).mp hlog

private lemma hp_neg_exp_bound {q n : ℕ}
    (hq : q = 8 ∨ q = 9 ∨ q = 10) (hn : 30 ≤ n) :
    Real.exp ((n : ℝ) * (hpNegT q : ℝ) +
      18 * (1 + Real.log ((n + 1 : ℕ) : ℝ))) ≤
      Real.exp 18 * ((n + 1 : ℕ) : ℝ) ^ 18 * (29 : ℝ) ^ n := by
  have ht : (hpNegT q : ℝ) < Real.log 29 := hp_neg_t_lt_log29 hq
  have hnR : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hnt : (n : ℝ) * (hpNegT q : ℝ) ≤
      (n : ℝ) * Real.log 29 :=
    mul_le_mul_of_nonneg_left (le_of_lt ht) hnR
  have harg : (n : ℝ) * (hpNegT q : ℝ) +
      18 * (1 + Real.log ((n + 1 : ℕ) : ℝ)) ≤
      (n : ℝ) * Real.log 29 +
        18 * (1 + Real.log ((n + 1 : ℕ) : ℝ)) :=
    add_le_add hnt (le_refl _)
  have hx : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  calc
    Real.exp ((n : ℝ) * (hpNegT q : ℝ) +
        18 * (1 + Real.log ((n + 1 : ℕ) : ℝ))) ≤
        Real.exp ((n : ℝ) * Real.log 29 +
          18 * (1 + Real.log ((n + 1 : ℕ) : ℝ))) :=
      Real.exp_le_exp.mpr harg
    _ = Real.exp ((n : ℝ) * Real.log 29) *
        Real.exp (18 * (1 + Real.log ((n + 1 : ℕ) : ℝ))) := by
      rw [Real.exp_add]
    _ = (29 : ℝ) ^ n * (Real.exp 18 *
        ((n + 1 : ℕ) : ℝ) ^ 18) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
      have hsplit : 18 * (1 + Real.log ((n + 1 : ℕ) : ℝ)) =
          18 + 18 * Real.log ((n + 1 : ℕ) : ℝ) := by ring
      rw [hsplit, Real.exp_add]
      have h18 : Real.exp (18 * Real.log ((n + 1 : ℕ) : ℝ)) =
          Real.exp (Real.log ((n + 1 : ℕ) : ℝ)) ^ 18 := by
        convert Real.exp_nat_mul (Real.log ((n + 1 : ℕ) : ℝ)) 18 using 1 <;>
          norm_num
      rw [h18, Real.exp_log hx]
    _ = Real.exp 18 * ((n + 1 : ℕ) : ℝ) ^ 18 * (29 : ℝ) ^ n := by ring

private lemma hp_neg_rect_bottom_velocity {n : ℕ} (hn : 30 ≤ n) :
    ‖hpTailRectEdgeVelocity (-1 / 2) ((n : ℝ) + 1 / 2)
      (-((n : ℝ) / 5)) ((n : ℝ) / 5) HpTailRectEdge.bottom‖ =
        (n : ℝ) + 1 := by
  simp [hpTailRectEdgeVelocity, hpTailRectEdgeMap, Complex.norm_real,
    Real.norm_eq_abs]
  have hcast : (n : ℂ) + (2 : ℂ)⁻¹ - -1 / 2 =
      (((n : ℝ) + 1 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hcast, Complex.norm_real]
  simp only [Real.norm_eq_abs]
  rw [abs_of_nonneg]
  linarith

private lemma hp_neg_rect_right_velocity {n : ℕ} (hn : 30 ≤ n) :
    ‖hpTailRectEdgeVelocity (-1 / 2) ((n : ℝ) + 1 / 2)
      (-((n : ℝ) / 5)) ((n : ℝ) / 5) HpTailRectEdge.right‖ =
        (n : ℝ) * 2 / 5 := by
  simp [hpTailRectEdgeVelocity, hpTailRectEdgeMap]
  have hvel : Complex.I * ((n : ℂ) / 5) +
      Complex.I * ((n : ℂ) / 5) =
      Complex.I * (((n : ℝ) * 2 / 5 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hvel, Complex.norm_mul, Complex.norm_real]
  simp [abs_of_nonneg]

private lemma hp_neg_rect_top_velocity {n : ℕ} (hn : 30 ≤ n) :
    ‖hpTailRectEdgeVelocity (-1 / 2) ((n : ℝ) + 1 / 2)
      (-((n : ℝ) / 5)) ((n : ℝ) / 5) HpTailRectEdge.top‖ =
        (n : ℝ) + 1 := by
  simp [hpTailRectEdgeVelocity, hpTailRectEdgeMap]
  have hcast : (-1 / 2 : ℂ) - ((n : ℂ) + (2 : ℂ)⁻¹) =
      ((-((n : ℝ) + 1) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hcast, Complex.norm_real]
  have hn1 : 0 ≤ (n : ℝ) + 1 := by positivity
  rw [Real.norm_eq_abs]
  have hnon : -((n : ℝ) + 1) ≤ 0 := neg_nonpos.mpr hn1
  rw [abs_of_nonpos hnon]
  ring

private lemma hp_neg_rect_left_velocity {n : ℕ} (hn : 30 ≤ n) :
    ‖hpTailRectEdgeVelocity (-1 / 2) ((n : ℝ) + 1 / 2)
      (-((n : ℝ) / 5)) ((n : ℝ) / 5) HpTailRectEdge.left‖ =
        (n : ℝ) * 2 / 5 := by
  simp [hpTailRectEdgeVelocity, hpTailRectEdgeMap]
  have hvel : -(Complex.I * ((n : ℂ) / 5)) -
      Complex.I * ((n : ℂ) / 5) =
      -(Complex.I * (((n : ℝ) * 2 / 5 : ℝ) : ℂ)) := by
    push_cast
    ring
  rw [hvel, norm_neg, Complex.norm_mul, Complex.norm_real]
  simp [abs_of_nonneg]

private lemma hp_neg_interval_mem {t : ℝ} (ht : t ∈ Ι (0 : ℝ) 1) :
    t ∈ Set.Icc (0 : ℝ) 1 := by
  have ht0 : (0 : ℝ) < t := by simpa using ht.1
  have ht1 : t ≤ (1 : ℝ) := by simpa using ht.2
  exact ⟨le_of_lt ht0, ht1⟩

private lemma hp_neg_bottom_integral_norm_le {q n : ℕ}
    (boundary : HpNegBorderBound q) (hn : 30 ≤ n) :
    ‖∫ t : ℝ in (0 : ℝ)..1,
      hpTailKernelPlus q n
          (hpTailRectEdgeMap (-1 / 2) ((n : ℝ) + 1 / 2)
            (-((n : ℝ) / 5)) ((n : ℝ) / 5) HpTailRectEdge.bottom t) *
        hpTailRectEdgeVelocity (-1 / 2) ((n : ℝ) + 1 / 2)
          (-((n : ℝ) / 5)) ((n : ℝ) / 5) HpTailRectEdge.bottom‖ ≤
      ((n : ℝ) + 1) *
        Real.exp ((n : ℝ) * (hpNegT q : ℝ) +
          18 * (1 + Real.log ((n + 1 : ℕ) : ℝ))) := by
  have hpoint : ∀ t ∈ Ι (0 : ℝ) 1,
      ‖hpTailKernelPlus q n
          (hpTailRectEdgeMap (-1 / 2) ((n : ℝ) + 1 / 2)
            (-((n : ℝ) / 5)) ((n : ℝ) / 5) HpTailRectEdge.bottom t) *
        hpTailRectEdgeVelocity (-1 / 2) ((n : ℝ) + 1 / 2)
          (-((n : ℝ) / 5)) ((n : ℝ) / 5) HpTailRectEdge.bottom‖ ≤
        ((n : ℝ) + 1) *
          Real.exp ((n : ℝ) * (hpNegT q : ℝ) +
            18 * (1 + Real.log ((n + 1 : ℕ) : ℝ))) := by
    intro t ht
    have htcc : t ∈ Set.Icc (0 : ℝ) 1 := hp_neg_interval_mem ht
    have hw := hp_neg_rect_edge_map_mem_border (n := n)
      (e := HpTailRectEdge.bottom) htcc
    have hk := hp_neg_kernel_norm_le_exp boundary hn hw
    calc
      ‖hpTailKernelPlus q n
            (hpTailRectEdgeMap (-1 / 2) ((n : ℝ) + 1 / 2)
              (-((n : ℝ) / 5)) ((n : ℝ) / 5) HpTailRectEdge.bottom t) *
          hpTailRectEdgeVelocity (-1 / 2) ((n : ℝ) + 1 / 2)
            (-((n : ℝ) / 5)) ((n : ℝ) / 5) HpTailRectEdge.bottom‖ =
          ‖hpTailKernelPlus q n
            (hpTailRectEdgeMap (-1 / 2) ((n : ℝ) + 1 / 2)
              (-((n : ℝ) / 5)) ((n : ℝ) / 5) HpTailRectEdge.bottom t)‖ *
            ‖hpTailRectEdgeVelocity (-1 / 2) ((n : ℝ) + 1 / 2)
              (-((n : ℝ) / 5)) ((n : ℝ) / 5) HpTailRectEdge.bottom‖ :=
        norm_mul _ _
      _ = ‖hpTailKernelPlus q n
            (hpTailRectEdgeMap (-1 / 2) ((n : ℝ) + 1 / 2)
              (-((n : ℝ) / 5)) ((n : ℝ) / 5) HpTailRectEdge.bottom t)‖ *
            ((n : ℝ) + 1) := by rw [hp_neg_rect_bottom_velocity hn]
      _ ≤ Real.exp ((n : ℝ) * (hpNegT q : ℝ) +
            18 * (1 + Real.log ((n + 1 : ℕ) : ℝ))) * ((n : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right hk (by positivity)
      _ = ((n : ℝ) + 1) *
          Real.exp ((n : ℝ) * (hpNegT q : ℝ) +
            18 * (1 + Real.log ((n + 1 : ℕ) : ℝ))) := by ring
  have hI := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun t : ℝ =>
      hpTailKernelPlus q n
          (hpTailRectEdgeMap (-1 / 2) ((n : ℝ) + 1 / 2)
            (-((n : ℝ) / 5)) ((n : ℝ) / 5) HpTailRectEdge.bottom t) *
        hpTailRectEdgeVelocity (-1 / 2) ((n : ℝ) + 1 / 2)
          (-((n : ℝ) / 5)) ((n : ℝ) / 5) HpTailRectEdge.bottom)
    (C := ((n : ℝ) + 1) *
      Real.exp ((n : ℝ) * (hpNegT q : ℝ) +
        18 * (1 + Real.log ((n + 1 : ℕ) : ℝ)))) (a := (0 : ℝ)) (b := 1) hpoint
  convert hI using 1 <;> norm_num

private lemma hp_neg_edge_integral_norm_le {q n : ℕ}
    (boundary : HpNegBorderBound q) (hn : 30 ≤ n)
    (e : HpTailRectEdge) (speed : ℝ)
    (hspeed : ‖hpTailRectEdgeVelocity (-1 / 2) ((n : ℝ) + 1 / 2)
      (-((n : ℝ) / 5)) ((n : ℝ) / 5) e‖ = speed) :
    ‖∫ t : ℝ in (0 : ℝ)..1,
      hpTailKernelPlus q n
          (hpTailRectEdgeMap (-1 / 2) ((n : ℝ) + 1 / 2)
            (-((n : ℝ) / 5)) ((n : ℝ) / 5) e t) *
        hpTailRectEdgeVelocity (-1 / 2) ((n : ℝ) + 1 / 2)
          (-((n : ℝ) / 5)) ((n : ℝ) / 5) e‖ ≤
      speed * Real.exp ((n : ℝ) * (hpNegT q : ℝ) +
        18 * (1 + Real.log ((n + 1 : ℕ) : ℝ))) := by
  have hpoint : ∀ t ∈ Ι (0 : ℝ) 1,
      ‖hpTailKernelPlus q n
          (hpTailRectEdgeMap (-1 / 2) ((n : ℝ) + 1 / 2)
            (-((n : ℝ) / 5)) ((n : ℝ) / 5) e t) *
        hpTailRectEdgeVelocity (-1 / 2) ((n : ℝ) + 1 / 2)
          (-((n : ℝ) / 5)) ((n : ℝ) / 5) e‖ ≤
        speed * Real.exp ((n : ℝ) * (hpNegT q : ℝ) +
          18 * (1 + Real.log ((n + 1 : ℕ) : ℝ))) := by
    intro t ht
    have htcc : t ∈ Set.Icc (0 : ℝ) 1 := hp_neg_interval_mem ht
    have hw := hp_neg_rect_edge_map_mem_border (n := n) (e := e) htcc
    have hk := hp_neg_kernel_norm_le_exp boundary hn hw
    have hspeed_nonneg : 0 ≤ speed := by rw [← hspeed]; positivity
    calc
      ‖hpTailKernelPlus q n
            (hpTailRectEdgeMap (-1 / 2) ((n : ℝ) + 1 / 2)
              (-((n : ℝ) / 5)) ((n : ℝ) / 5) e t) *
          hpTailRectEdgeVelocity (-1 / 2) ((n : ℝ) + 1 / 2)
            (-((n : ℝ) / 5)) ((n : ℝ) / 5) e‖ =
          ‖hpTailKernelPlus q n
            (hpTailRectEdgeMap (-1 / 2) ((n : ℝ) + 1 / 2)
              (-((n : ℝ) / 5)) ((n : ℝ) / 5) e t)‖ *
            ‖hpTailRectEdgeVelocity (-1 / 2) ((n : ℝ) + 1 / 2)
              (-((n : ℝ) / 5)) ((n : ℝ) / 5) e‖ := norm_mul _ _
      _ = ‖hpTailKernelPlus q n
            (hpTailRectEdgeMap (-1 / 2) ((n : ℝ) + 1 / 2)
              (-((n : ℝ) / 5)) ((n : ℝ) / 5) e t)‖ * speed := by
        rw [hspeed]
      _ ≤ Real.exp ((n : ℝ) * (hpNegT q : ℝ) +
          18 * (1 + Real.log ((n + 1 : ℕ) : ℝ))) * speed :=
        mul_le_mul_of_nonneg_right hk hspeed_nonneg
      _ = speed * Real.exp ((n : ℝ) * (hpNegT q : ℝ) +
          18 * (1 + Real.log ((n + 1 : ℕ) : ℝ))) := by ring
  have hI := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun t : ℝ =>
      hpTailKernelPlus q n
          (hpTailRectEdgeMap (-1 / 2) ((n : ℝ) + 1 / 2)
            (-((n : ℝ) / 5)) ((n : ℝ) / 5) e t) *
        hpTailRectEdgeVelocity (-1 / 2) ((n : ℝ) + 1 / 2)
          (-((n : ℝ) / 5)) ((n : ℝ) / 5) e)
    (C := speed * Real.exp ((n : ℝ) * (hpNegT q : ℝ) +
      18 * (1 + Real.log ((n + 1 : ℕ) : ℝ)))) (a := (0 : ℝ)) (b := 1) hpoint
  convert hI using 1 <;> norm_num

private lemma hp_neg_right_integral_norm_le {q n : ℕ}
    (boundary : HpNegBorderBound q) (hn : 30 ≤ n) :
    ‖∫ t : ℝ in (0 : ℝ)..1,
      hpTailKernelPlus q n
          (hpTailRectEdgeMap (-1 / 2) ((n : ℝ) + 1 / 2)
            (-((n : ℝ) / 5)) ((n : ℝ) / 5) HpTailRectEdge.right t) *
        hpTailRectEdgeVelocity (-1 / 2) ((n : ℝ) + 1 / 2)
          (-((n : ℝ) / 5)) ((n : ℝ) / 5) HpTailRectEdge.right‖ ≤
      ((n : ℝ) * 2 / 5) * Real.exp ((n : ℝ) * (hpNegT q : ℝ) +
        18 * (1 + Real.log ((n + 1 : ℕ) : ℝ))) := by
  exact hp_neg_edge_integral_norm_le boundary hn HpTailRectEdge.right
    ((n : ℝ) * 2 / 5) (hp_neg_rect_right_velocity hn)

private lemma hp_neg_top_integral_norm_le {q n : ℕ}
    (boundary : HpNegBorderBound q) (hn : 30 ≤ n) :
    ‖∫ t : ℝ in (0 : ℝ)..1,
      hpTailKernelPlus q n
          (hpTailRectEdgeMap (-1 / 2) ((n : ℝ) + 1 / 2)
            (-((n : ℝ) / 5)) ((n : ℝ) / 5) HpTailRectEdge.top t) *
        hpTailRectEdgeVelocity (-1 / 2) ((n : ℝ) + 1 / 2)
          (-((n : ℝ) / 5)) ((n : ℝ) / 5) HpTailRectEdge.top‖ ≤
      ((n : ℝ) + 1) * Real.exp ((n : ℝ) * (hpNegT q : ℝ) +
        18 * (1 + Real.log ((n + 1 : ℕ) : ℝ))) := by
  exact hp_neg_edge_integral_norm_le boundary hn HpTailRectEdge.top
    ((n : ℝ) + 1) (hp_neg_rect_top_velocity hn)

private lemma hp_neg_left_integral_norm_le {q n : ℕ}
    (boundary : HpNegBorderBound q) (hn : 30 ≤ n) :
    ‖∫ t : ℝ in (0 : ℝ)..1,
      hpTailKernelPlus q n
          (hpTailRectEdgeMap (-1 / 2) ((n : ℝ) + 1 / 2)
            (-((n : ℝ) / 5)) ((n : ℝ) / 5) HpTailRectEdge.left t) *
        hpTailRectEdgeVelocity (-1 / 2) ((n : ℝ) + 1 / 2)
          (-((n : ℝ) / 5)) ((n : ℝ) / 5) HpTailRectEdge.left‖ ≤
      ((n : ℝ) * 2 / 5) * Real.exp ((n : ℝ) * (hpNegT q : ℝ) +
        18 * (1 + Real.log ((n + 1 : ℕ) : ℝ))) := by
  exact hp_neg_edge_integral_norm_le boundary hn HpTailRectEdge.left
    ((n : ℝ) * 2 / 5) (hp_neg_rect_left_velocity hn)

private lemma hp_neg_rect_integral_norm_le {q n : ℕ}
    (hq : q = 8 ∨ q = 9 ∨ q = 10)
    (boundary : HpNegBorderBound q) (hn : 30 ≤ n) :
    ‖hpTailRectIntegral (-1 / 2) ((n : ℝ) + 1 / 2)
        (-((n : ℝ) / 5)) ((n : ℝ) / 5)
        (hpTailKernelPlus q n)‖ ≤
      3 * ((n : ℝ) + 1) *
        (Real.exp 18 * ((n + 1 : ℕ) : ℝ) ^ 18 * (29 : ℝ) ^ n) := by
  let M : ℝ := Real.exp ((n : ℝ) * (hpNegT q : ℝ) +
    18 * (1 + Real.log ((n + 1 : ℕ) : ℝ)))
  let E : ℝ := Real.exp 18 * ((n + 1 : ℕ) : ℝ) ^ 18 * (29 : ℝ) ^ n
  let b : ℂ := ∫ t : ℝ in (0 : ℝ)..1,
      hpTailKernelPlus q n
          (hpTailRectEdgeMap (-1 / 2) ((n : ℝ) + 1 / 2)
            (-((n : ℝ) / 5)) ((n : ℝ) / 5) HpTailRectEdge.bottom t) *
        hpTailRectEdgeVelocity (-1 / 2) ((n : ℝ) + 1 / 2)
          (-((n : ℝ) / 5)) ((n : ℝ) / 5) HpTailRectEdge.bottom
  let r : ℂ := ∫ t : ℝ in (0 : ℝ)..1,
      hpTailKernelPlus q n
          (hpTailRectEdgeMap (-1 / 2) ((n : ℝ) + 1 / 2)
            (-((n : ℝ) / 5)) ((n : ℝ) / 5) HpTailRectEdge.right t) *
        hpTailRectEdgeVelocity (-1 / 2) ((n : ℝ) + 1 / 2)
          (-((n : ℝ) / 5)) ((n : ℝ) / 5) HpTailRectEdge.right
  let t : ℂ := ∫ t : ℝ in (0 : ℝ)..1,
      hpTailKernelPlus q n
          (hpTailRectEdgeMap (-1 / 2) ((n : ℝ) + 1 / 2)
            (-((n : ℝ) / 5)) ((n : ℝ) / 5) HpTailRectEdge.top t) *
        hpTailRectEdgeVelocity (-1 / 2) ((n : ℝ) + 1 / 2)
          (-((n : ℝ) / 5)) ((n : ℝ) / 5) HpTailRectEdge.top
  let l : ℂ := ∫ t : ℝ in (0 : ℝ)..1,
      hpTailKernelPlus q n
          (hpTailRectEdgeMap (-1 / 2) ((n : ℝ) + 1 / 2)
            (-((n : ℝ) / 5)) ((n : ℝ) / 5) HpTailRectEdge.left t) *
        hpTailRectEdgeVelocity (-1 / 2) ((n : ℝ) + 1 / 2)
          (-((n : ℝ) / 5)) ((n : ℝ) / 5) HpTailRectEdge.left
  have hb : ‖b‖ ≤ ((n : ℝ) + 1) * M := by
    simpa [b, M] using hp_neg_bottom_integral_norm_le boundary hn
  have hr : ‖r‖ ≤ ((n : ℝ) * 2 / 5) * M := by
    simpa [r, M] using hp_neg_right_integral_norm_le boundary hn
  have ht : ‖t‖ ≤ ((n : ℝ) + 1) * M := by
    simpa [t, M] using hp_neg_top_integral_norm_le boundary hn
  have hl : ‖l‖ ≤ ((n : ℝ) * 2 / 5) * M := by
    simpa [l, M] using hp_neg_left_integral_norm_le boundary hn
  have hsum : ‖b‖ + ‖r‖ + ‖t‖ + ‖l‖ ≤
      2 * (((n : ℝ) + 1) * M) +
        2 * (((n : ℝ) * 2 / 5) * M) := by
    nlinarith [hb, hr, ht, hl]
  have htriangle : ‖b + r + t + l‖ ≤
      ‖b‖ + ‖r‖ + ‖t‖ + ‖l‖ := by
    nlinarith [norm_add_le (b + r + t) l,
      norm_add_le (b + r) t, norm_add_le b r]
  have hgeom : 2 * ((n : ℝ) + 1) + 2 * ((n : ℝ) * 2 / 5) ≤
      3 * ((n : ℝ) + 1) := by
    have hnR : (30 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith
  have hM : 0 ≤ M := by positivity
  have hscaled :
      2 * (((n : ℝ) + 1) * M) +
          2 * (((n : ℝ) * 2 / 5) * M) ≤
        3 * ((n : ℝ) + 1) * M := by
    have h := mul_le_mul_of_nonneg_right hgeom hM
    nlinarith
  have hME : M ≤ E := by
    simpa [M, E] using hp_neg_exp_bound hq hn
  have hscaledE : 3 * ((n : ℝ) + 1) * M ≤
      3 * ((n : ℝ) + 1) * E :=
    mul_le_mul_of_nonneg_left hME (by positivity)
  change ‖b + r + t + l‖ ≤ 3 * ((n : ℝ) + 1) * E
  calc
    ‖b + r + t + l‖ ≤ ‖b‖ + ‖r‖ + ‖t‖ + ‖l‖ := htriangle
    _ ≤ 2 * (((n : ℝ) + 1) * M) +
        2 * (((n : ℝ) * 2 / 5) * M) := hsum
    _ ≤ 3 * ((n : ℝ) + 1) * M := hscaled
    _ ≤ 3 * ((n : ℝ) + 1) * E := hscaledE

private lemma hp_neg_residue_scale_norm :
    ‖(1 / (2 * Real.pi * Complex.I) : ℂ)‖ =
      (1 / (2 * Real.pi) : ℝ) := by
  simp [norm_mul, Complex.norm_real, Complex.norm_I,
    Real.norm_eq_abs, abs_of_pos, Real.pi_pos]

/-- The actual v13 branch-value estimate obtained from the P1 residue identity
and the C3 pointwise border bound on the four parameterized edges. -/
theorem hpNegBranchValueBound_of_v13_contour {q : ℕ}
    (residueProvider : HpNegContourResidueProvider q)
    (boundary : HpNegBorderBound q) :
    HpNegBranchValueBound q := by
  intro n hn
  have hres := residueProvider.residue n (by omega)
  have hcont := hp_neg_rect_integral_norm_le residueProvider.q_spec boundary hn
  calc
    ‖hpTailBranchValuePlus q n‖ =
        ‖(1 / (2 * Real.pi * Complex.I) : ℂ) *
          hpTailRectIntegral (-1 / 2) ((n : ℝ) + 1 / 2)
            (-((n : ℝ) / 5)) ((n : ℝ) / 5)
            (hpTailKernelPlus q n)‖ := by
      rw [hres.residue_identity]
      congr 2 <;> norm_num <;> ring
    _ = ‖(1 / (2 * Real.pi * Complex.I) : ℂ)‖ *
          ‖hpTailRectIntegral (-1 / 2) ((n : ℝ) + 1 / 2)
            (-((n : ℝ) / 5)) ((n : ℝ) / 5)
            (hpTailKernelPlus q n)‖ := norm_mul _ _
    _ = (1 / (2 * Real.pi) : ℝ) *
          ‖hpTailRectIntegral (-1 / 2) ((n : ℝ) + 1 / 2)
            (-((n : ℝ) / 5)) ((n : ℝ) / 5)
            (hpTailKernelPlus q n)‖ := by
      rw [hp_neg_residue_scale_norm]
    _ ≤ (1 / (2 * Real.pi) : ℝ) *
          (3 * ((n : ℝ) + 1) *
            (Real.exp 18 * ((n + 1 : ℕ) : ℝ) ^ 18 * (29 : ℝ) ^ n)) :=
      mul_le_mul_of_nonneg_left hcont (by positivity)
    _ = (1 / (2 * Real.pi)) * (3 * ((n + 1 : ℕ) : ℝ)) *
          (Real.exp 18 * ((n + 1 : ℕ) : ℝ) ^ 18 * (29 : ℝ) ^ n) := by
      norm_num [Nat.cast_add, Nat.cast_one]
      ring

end

end Li2Lean.B4.NegativeContour
