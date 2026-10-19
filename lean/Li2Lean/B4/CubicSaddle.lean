/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Data.Complex.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

namespace Li2Lean.B4

noncomputable section

/-- The v13 cubic phase polynomial; hp-tail.tex:266-270. -/
def hpSaddleCubic (q x : ℝ) : ℝ :=
  (q + 1) * x ^ 3 - 3 * (q + 1) * x ^ 2 + 3 * x - 1

/-- The same v13 cubic over the complex numbers; hp-tail.tex:266-270. -/
def hpSaddleCubicC (q : ℝ) (w : ℂ) : ℂ :=
  ((q + 1 : ℝ) : ℂ) * w ^ 3 - ((3 * (q + 1) : ℝ) : ℂ) * w ^ 2 + 3 * w - 1

/-- Endpoint value used to locate the real v13 root; hp-tail.tex:328-331. -/
theorem hp_saddle_cubic_at_two (q : ℝ) : hpSaddleCubic q 2 = 1 - 4 * q := by
  simp [hpSaddleCubic]
  ring

/-- Right endpoint value of the v13 cubic; hp-tail.tex:328-331. -/
theorem hp_saddle_cubic_at_three (q : ℝ) : hpSaddleCubic q 3 = 8 := by
  simp [hpSaddleCubic]
  ring

/-- The v13 cubic has a real root in (2,3) for every q > 1; hp-tail.tex:328-334. -/
theorem hp_saddle_real_root_exists (q : ℝ) (hq : 1 < q) :
    ∃ r : ℝ, 2 < r ∧ r < 3 ∧ hpSaddleCubic q r = 0 := by
  have hcont : ContinuousOn (fun x : ℝ => hpSaddleCubic q x) (Set.Icc 2 3) := by
    unfold hpSaddleCubic
    fun_prop
  have h2 : hpSaddleCubic q 2 < 0 := by
    rw [hp_saddle_cubic_at_two]
    linarith
  have h3 : 0 < hpSaddleCubic q 3 := by
    rw [hp_saddle_cubic_at_three]
    norm_num
  have hzero : (0 : ℝ) ∈ Set.Icc (hpSaddleCubic q 2) (hpSaddleCubic q 3) :=
    ⟨le_of_lt h2, le_of_lt h3⟩
  have himage := intermediate_value_Icc (a := (2 : ℝ)) (b := 3)
    (by norm_num) hcont hzero
  rcases himage with ⟨r, hr, hroot⟩
  have hroot' : hpSaddleCubic q r = 0 := hroot
  have hrgt : 2 < r := by
    by_contra h
    have hrle : r ≤ 2 := le_of_not_gt h
    have heq : r = 2 := le_antisymm hrle hr.1
    subst r
    rw [hp_saddle_cubic_at_two] at hroot'
    linarith
  have hrlt : r < 3 := by
    by_contra h
    have hrge : 3 ≤ r := le_of_not_gt h
    have heq : r = 3 := le_antisymm hr.2 hrge
    subst r
    rw [hp_saddle_cubic_at_three] at hroot'
    norm_num at hroot'
  exact ⟨r, hrgt, hrlt, hroot'⟩

/-- A selected v13 real root in (2,3); hp-tail.tex:328-334. -/
noncomputable def hpSaddleRealRoot (q : ℝ) (hq : 1 < q) : ℝ :=
  Classical.choose (hp_saddle_real_root_exists q hq)

/-- Specification of the selected real v13 saddle root; hp-tail.tex:328-334. -/
theorem hp_saddle_real_root_spec (q : ℝ) (hq : 1 < q) :
    2 < hpSaddleRealRoot q hq ∧ hpSaddleRealRoot q hq < 3 ∧
      hpSaddleCubic q (hpSaddleRealRoot q hq) = 0 :=
  Classical.choose_spec (hp_saddle_real_root_exists q hq)

/-- Real part of the nonreal v13 roots; hp-tail.tex:330-334. -/
def hpSaddleCenter (q : ℝ) (hq : 1 < q) : ℝ :=
  (3 - hpSaddleRealRoot q hq) / 2

/-- Explicit square of the imaginary part of the v13 lower root, derived from
the cubic and Vieta relations; hp-tail.tex:328-334. -/
def hpSaddleBetaSq (q : ℝ) (hq : 1 < q) : ℝ :=
  3 * (3 - hpSaddleRealRoot q hq) * (hpSaddleRealRoot q hq - 1) ^ 2 /
    (4 * (3 * hpSaddleRealRoot q hq - 1))

/-- Positive imaginary part of the nonreal v13 root; hp-tail.tex:266-270 and
hp-tail.tex:328-334. -/
noncomputable def hpSaddleBeta (q : ℝ) (hq : 1 < q) : ℝ :=
  Real.sqrt (hpSaddleBetaSq q hq)

/-- The real part of the nonreal v13 roots lies in (0,1/2); hp-tail.tex:330-334. -/
theorem hp_saddle_center_bounds (q : ℝ) (hq : 1 < q) :
    0 < hpSaddleCenter q hq ∧ hpSaddleCenter q hq < 1 / 2 := by
  have hr := hp_saddle_real_root_spec q hq
  dsimp [hpSaddleCenter]
  constructor <;> linarith

/-- The explicit v13 imaginary-part square is strictly positive;
hp-tail.tex:266-270 and hp-tail.tex:328-334. -/
theorem hp_saddle_beta_sq_pos (q : ℝ) (hq : 1 < q) :
    0 < hpSaddleBetaSq q hq := by
  have hr := hp_saddle_real_root_spec q hq
  have hleft : 0 < 3 - hpSaddleRealRoot q hq := by linarith [hr.1, hr.2.1]
  have hright : 0 < hpSaddleRealRoot q hq - 1 := by linarith [hr.1]
  have hden : 0 < 4 * (3 * hpSaddleRealRoot q hq - 1) := by
    nlinarith [hr.1]
  unfold hpSaddleBetaSq
  apply div_pos
  · exact mul_pos (mul_pos (by norm_num) hleft) (sq_pos_of_pos hright)
  · exact hden

/-- Positivity of the lower-root height beta_q in v13; hp-tail.tex:266-270. -/
theorem hp_saddle_beta_pos (q : ℝ) (hq : 1 < q) : 0 < hpSaddleBeta q hq := by
  exact Real.sqrt_pos.2 (hp_saddle_beta_sq_pos q hq)

/-- The cubic equation converts the explicit square into the Vieta expression
1/((q+1)R) - u^2; hp-tail.tex:328-334. -/
theorem hp_saddle_beta_sq_vieta (q : ℝ) (hq : 1 < q) :
    hpSaddleBetaSq q hq =
      1 / ((q + 1) * hpSaddleRealRoot q hq) - (hpSaddleCenter q hq) ^ 2 := by
  let r := hpSaddleRealRoot q hq
  have hr := hp_saddle_real_root_spec q hq
  have hroot : hpSaddleCubic q r = 0 := hr.2.2
  have hrel : (q + 1) * r ^ 2 * (3 - r) = 3 * r - 1 := by
    dsimp [hpSaddleCubic] at hroot
    nlinarith [hroot]
  have hq1 : q + 1 ≠ 0 := by linarith
  have hr0 : r ≠ 0 := ne_of_gt (by linarith [hr.1])
  have hden0 : 3 * r - 1 ≠ 0 := by nlinarith [hr.1]
  have hqr0 : (q + 1) * r ≠ 0 := mul_ne_zero hq1 hr0
  have hinv : 1 / ((q + 1) * r) = r * (3 - r) / (3 * r - 1) := by
    rw [div_eq_div_iff hqr0 hden0]
    calc
      (1 : ℝ) * (3 * r - 1) = 3 * r - 1 := by ring
      _ = (q + 1) * r ^ 2 * (3 - r) := hrel.symm
      _ = r * (3 - r) * ((q + 1) * r) := by ring
  change 3 * (3 - r) * (r - 1) ^ 2 / (4 * (3 * r - 1)) =
    1 / ((q + 1) * r) - ((3 - r) / 2) ^ 2
  rw [hinv]
  field_simp [hden0]
  ring

/-- The square of the selected positive height is the explicit v13 value;
hp-tail.tex:266-270 and hp-tail.tex:328-334. -/
theorem hp_saddle_beta_sq (q : ℝ) (hq : 1 < q) :
    hpSaddleBeta q hq ^ 2 = hpSaddleBetaSq q hq := by
  dsimp [hpSaddleBeta]
  exact Real.sq_sqrt (le_of_lt (hp_saddle_beta_sq_pos q hq))

/-- The selected real root is unique among roots in `(2,3)`; this is the
root-selection refinement of `hp-tail.tex:328-334`. -/
theorem hp_saddle_real_root_unique (q : ℝ) (hq : 1 < q)
    {r s : ℝ} (hr : 2 < r) (hr3 : r < 3)
    (hs : 2 < s) (hs3 : s < 3)
    (hrootr : hpSaddleCubic q r = 0)
    (hroots : hpSaddleCubic q s = 0) : r = s := by
  have hdiff (x y : ℝ) (hx : 2 < x) (hxy : x < y) :
      0 < hpSaddleCubic q y - hpSaddleCubic q x := by
    have hq1 : 0 < q + 1 := by linarith
    have hxy0 : 0 < y - x := by linarith
    have hxa : 0 ≤ x - 2 := by linarith
    have hya : 0 ≤ y - 2 := by linarith
    have hxyprod : 0 ≤ (x - 2) * (y - 2) := mul_nonneg hxa hya
    have hquad : 0 ≤ y ^ 2 + y * x + x ^ 2 - 3 * (y + x) := by
      nlinarith [sq_nonneg (x - 2), sq_nonneg (y - 2), hxyprod]
    have hfactor :
        hpSaddleCubic q y - hpSaddleCubic q x =
          (y - x) * ((q + 1) * (y ^ 2 + y * x + x ^ 2 - 3 * (y + x)) + 3) := by
      dsimp [hpSaddleCubic]
      ring
    rw [hfactor]
    have hprod : 0 ≤ (q + 1) * (y ^ 2 + y * x + x ^ 2 - 3 * (y + x)) :=
      mul_nonneg hq1.le hquad
    have hinner : 0 < (q + 1) * (y ^ 2 + y * x + x ^ 2 - 3 * (y + x)) + 3 := by
      nlinarith
    exact mul_pos hxy0 hinner
  by_contra hneq
  rcases lt_or_gt_of_ne hneq with hlt | hgt
  · have h := hdiff r s hr hlt
    rw [hrootr, hroots] at h
    linarith
  · have h := hdiff s r hs hgt
    rw [hroots, hrootr] at h
    linarith

/-- The selected lower nonreal root of the v13 cubic; hp-tail.tex:266-270 and
hp-tail.tex:328-334. -/
def hpSaddleLowerRoot (q : ℝ) (hq : 1 < q) : ℂ :=
  (hpSaddleCenter q hq : ℂ) - Complex.I * (hpSaddleBeta q hq : ℂ)

/-- The selected upper nonreal root of the v13 cubic; hp-tail.tex:328-334. -/
def hpSaddleUpperRoot (q : ℝ) (hq : 1 < q) : ℂ :=
  (hpSaddleCenter q hq : ℂ) + Complex.I * (hpSaddleBeta q hq : ℂ)

/-- The chosen lower root has strictly negative imaginary part, so its sign
really is the lower-branch convention of `hp-tail.tex:266-270`. -/
theorem hp_saddle_lower_root_im_neg (q : ℝ) (hq : 1 < q) :
    (hpSaddleLowerRoot q hq).im < 0 := by
  simp [hpSaddleLowerRoot]
  linarith [hp_saddle_beta_pos q hq]

/-- The conjugate upper root has strictly positive imaginary part;
`hp-tail.tex:328-334`. -/
theorem hp_saddle_upper_root_im_pos (q : ℝ) (hq : 1 < q) :
    0 < (hpSaddleUpperRoot q hq).im := by
  simp [hpSaddleUpperRoot]
  linarith [hp_saddle_beta_pos q hq]

/-- Vieta's sum relation for the cubic roots; `hp-tail.tex:328-334`. -/
private theorem hp_saddle_root_sum (q : ℝ) (hq : 1 < q) :
    hpSaddleRealRoot q hq + 2 * hpSaddleCenter q hq = 3 := by
  simp [hpSaddleCenter]
  ring

/-- The product relation for the conjugate root pair; `hp-tail.tex:328-334`. -/
private theorem hp_saddle_root_pair (q : ℝ) (hq : 1 < q) :
    (q + 1) * hpSaddleRealRoot q hq *
        (hpSaddleCenter q hq ^ 2 + hpSaddleBeta q hq ^ 2) = 1 := by
  have hq1 : q + 1 ≠ 0 := by linarith
  have hr0 : hpSaddleRealRoot q hq ≠ 0 := by
    have hr := hp_saddle_real_root_spec q hq
    linarith [hr.1]
  rw [hp_saddle_beta_sq q hq, hp_saddle_beta_sq_vieta q hq]
  field_simp [hq1, hr0]
  ring

/-- The middle Vieta coefficient for the cubic; `hp-tail.tex:328-334`. -/
private theorem hp_saddle_root_middle (q : ℝ) (hq : 1 < q) :
    (q + 1) * (2 * hpSaddleRealRoot q hq * hpSaddleCenter q hq +
      hpSaddleCenter q hq ^ 2 + hpSaddleBeta q hq ^ 2) = 3 := by
  let r := hpSaddleRealRoot q hq
  let u := hpSaddleCenter q hq
  have hr := hp_saddle_real_root_spec q hq
  have hroot : hpSaddleCubic q r = 0 := hr.2.2
  have hq1 : q + 1 ≠ 0 := by linarith
  have hr0 : r ≠ 0 := by linarith [hr.1]
  have hsum : 2 * u = 3 - r := by
    dsimp [u, hpSaddleCenter]
    ring
  have hrel : (q + 1) * r ^ 2 * (3 - r) = 3 * r - 1 := by
    dsimp [hpSaddleCubic] at hroot
    nlinarith [hroot]
  have hru : 2 * r * u = r * (3 - r) := by
    nlinarith [hsum]
  rw [hp_saddle_beta_sq q hq, hp_saddle_beta_sq_vieta q hq]
  have hden : (q + 1) * r ≠ 0 := mul_ne_zero hq1 hr0
  have hcomb : (q + 1) * r * (3 - r) + 1 / r = 3 := by
    calc
      (q + 1) * r * (3 - r) + 1 / r =
          ((q + 1) * r ^ 2 * (3 - r) + 1) / r := by
        field_simp [hr0]
      _ = ((3 * r - 1) + 1) / r := by rw [hrel]
      _ = 3 := by field_simp [hr0]; ring
  calc
    (q + 1) * (2 * r * u + u ^ 2 +
        (1 / ((q + 1) * r) - u ^ 2)) =
        (q + 1) * (r * (3 - r) + 1 / ((q + 1) * r)) := by
      rw [hru]
      ring
    _ = (q + 1) * r * (3 - r) + 1 / r := by
      field_simp [hden, hr0]
    _ = 3 := hcomb

/-- Factorization of the exact v13 cubic by its real root and conjugate pair;
`hp-tail.tex:266-270`, `hp-tail.tex:328-334`. -/
private theorem hp_saddle_cubic_factor (q : ℝ) (hq : 1 < q) (w : ℂ) :
    hpSaddleCubicC q w =
      ((q + 1 : ℝ) : ℂ) * (w - (hpSaddleRealRoot q hq : ℂ)) *
        ((w - (hpSaddleCenter q hq : ℂ)) ^ 2 +
          (hpSaddleBeta q hq : ℂ) ^ 2) := by
  have hsumR := hp_saddle_root_sum q hq
  have hpairR := hp_saddle_root_pair q hq
  have hmiddleR := hp_saddle_root_middle q hq
  have hsumC : (hpSaddleRealRoot q hq : ℂ) +
      2 * (hpSaddleCenter q hq : ℂ) = 3 := by
    exact_mod_cast hsumR
  have hpairC : ((q + 1 : ℝ) : ℂ) * (hpSaddleRealRoot q hq : ℂ) *
      ((hpSaddleCenter q hq : ℂ) ^ 2 + (hpSaddleBeta q hq : ℂ) ^ 2) = 1 := by
    exact_mod_cast hpairR
  have hmiddleC : ((q + 1 : ℝ) : ℂ) *
      (2 * (hpSaddleRealRoot q hq : ℂ) * (hpSaddleCenter q hq : ℂ) +
        (hpSaddleCenter q hq : ℂ) ^ 2 + (hpSaddleBeta q hq : ℂ) ^ 2) = 3 := by
    exact_mod_cast hmiddleR
  calc
    hpSaddleCubicC q w = ((q + 1 : ℝ) : ℂ) * w ^ 3 -
        3 * ((q + 1 : ℝ) : ℂ) * w ^ 2 + 3 * w - 1 := by
      simp [hpSaddleCubicC]
    _ = ((q + 1 : ℝ) : ℂ) *
        (w - (hpSaddleRealRoot q hq : ℂ)) *
          ((w - (hpSaddleCenter q hq : ℂ)) ^ 2 +
            (hpSaddleBeta q hq : ℂ) ^ 2) := by
      calc
        ((q + 1 : ℝ) : ℂ) * w ^ 3 -
            3 * ((q + 1 : ℝ) : ℂ) * w ^ 2 + 3 * w - 1 =
          ((q + 1 : ℝ) : ℂ) * w ^ 3 -
            ((q + 1 : ℝ) : ℂ) *
              ((hpSaddleRealRoot q hq : ℂ) +
                2 * (hpSaddleCenter q hq : ℂ)) * w ^ 2 +
            ((q + 1 : ℝ) : ℂ) *
              (2 * (hpSaddleRealRoot q hq : ℂ) *
                  (hpSaddleCenter q hq : ℂ) +
                (hpSaddleCenter q hq : ℂ) ^ 2 +
                (hpSaddleBeta q hq : ℂ) ^ 2) * w -
            ((q + 1 : ℝ) : ℂ) * (hpSaddleRealRoot q hq : ℂ) *
              ((hpSaddleCenter q hq : ℂ) ^ 2 +
                (hpSaddleBeta q hq : ℂ) ^ 2) := by
          rw [hsumC, hmiddleC, hpairC] <;> ring
        _ = ((q + 1 : ℝ) : ℂ) *
            (w - (hpSaddleRealRoot q hq : ℂ)) *
              ((w - (hpSaddleCenter q hq : ℂ)) ^ 2 +
                (hpSaddleBeta q hq : ℂ) ^ 2) := by ring

/-- The lower nonreal root used to define `beta_q` in v13 is a root of the
cubic; `hp-tail.tex:266-270`, `hp-tail.tex:328-334`. -/
theorem hp_saddle_lower_root_is_root (q : ℝ) (hq : 1 < q) :
    hpSaddleCubicC q (hpSaddleLowerRoot q hq) = 0 := by
  rw [hp_saddle_cubic_factor q hq]
  have hzero :
      (hpSaddleLowerRoot q hq - (hpSaddleCenter q hq : ℂ)) ^ 2 +
        (hpSaddleBeta q hq : ℂ) ^ 2 = 0 := by
    simp [hpSaddleLowerRoot]
    ring_nf
    norm_num
  rw [hzero]
  ring

/-- The conjugate upper nonreal root in the v13 cubic;
`hp-tail.tex:328-334`. -/
theorem hp_saddle_upper_root_is_root (q : ℝ) (hq : 1 < q) :
    hpSaddleCubicC q (hpSaddleUpperRoot q hq) = 0 := by
  rw [hp_saddle_cubic_factor q hq]
  have hzero :
      (hpSaddleUpperRoot q hq - (hpSaddleCenter q hq : ℂ)) ^ 2 +
        (hpSaddleBeta q hq : ℂ) ^ 2 = 0 := by
    simp [hpSaddleUpperRoot]
    ring_nf
    norm_num
  rw [hzero]
  ring

/-- The open interior of the rectangle Gamma_n^+ in v13
hp-tail.tex:271-279, represented by its four side inequalities. -/
def hpSaddleRectInterior (n : ℕ) (beta : ℝ) (w : ℂ) : Prop :=
  (-1 / 2 : ℝ) < w.re ∧ w.re < (n : ℝ) + 1 / 2 ∧
    -((n : ℝ) * beta) < w.im ∧ w.im < (n : ℝ) * beta

/-- The integer poles enclosed by the v13 rectangle are exactly 0,...,n;
hp-tail.tex:271-275. -/
theorem hp_saddle_rect_integer_poles (n k : ℕ) (beta : ℝ)
    (hheight : 1 / 2 ≤ (n : ℝ) * beta) :
    hpSaddleRectInterior n beta (k : ℂ) ↔ k ≤ n := by
  constructor
  · intro hw
    by_contra hkn
    have hnk : n + 1 ≤ k := Nat.succ_le_of_lt (Nat.lt_of_not_ge hkn)
    have hknR : (n : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hnk
    have hright := hw.2.1
    have hkre : (k : ℂ).re = (k : ℝ) := by simp
    rw [hkre] at hright
    linarith
  · intro hkn
    have hknR : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hkn
    have hheightpos : 0 < (n : ℝ) * beta := by linarith
    have hkre : (k : ℂ).re = (k : ℝ) := by simp
    have hkim : (k : ℂ).im = 0 := by simp
    simp only [hpSaddleRectInterior, hkre, hkim]
    constructor
    · exact lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg k)
    constructor
    · linarith
    constructor <;> linarith

/-- Side lines of the v13 rectangle; hp-tail.tex:271-277. -/
def hpSaddleRectSide (n : ℕ) (beta : ℝ) (w : ℂ) : Prop :=
  (w.re = -1 / 2 ∨ w.re = (n : ℝ) + 1 / 2) ∨
    (w.im = (n : ℝ) * beta ∨ w.im = -((n : ℝ) * beta))

/-- Every enclosed pole has distance at least min(1/2,n beta) from every
side line of the v13 rectangle; hp-tail.tex:274-277. -/
theorem hp_saddle_pole_side_clearance (n k : ℕ) (beta : ℝ)
    (hkn : k ≤ n) (hheight : 0 < (n : ℝ) * beta)
    {w : ℂ} (hw : hpSaddleRectSide n beta w) :
    min (1 / 2 : ℝ) ((n : ℝ) * beta) ≤ ‖(k : ℂ) - w‖ := by
  have hkre : (k : ℂ).re = (k : ℝ) := by simp
  have hkim : (k : ℂ).im = 0 := by simp
  have hknR : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hkn
  have hreal (hside : w.re = -1 / 2 ∨ w.re = (n : ℝ) + 1 / 2) :
      (1 / 2 : ℝ) ≤ |((k : ℂ) - w).re| := by
    rw [Complex.sub_re, hkre]
    rcases hside with hleft | hright
    · rw [hleft]
      have hkR : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
      rw [abs_of_nonneg (by linarith : 0 ≤ (k : ℝ) - (-1 / 2 : ℝ))]
      linarith
    · rw [hright, abs_of_nonpos]
      · linarith
      · linarith
  have himag (hside : w.im = (n : ℝ) * beta ∨ w.im = -((n : ℝ) * beta)) :
      (n : ℝ) * beta = |((k : ℂ) - w).im| := by
    rw [Complex.sub_im, hkim]
    rcases hside with htop | hbottom
    · rw [htop, abs_of_neg (by linarith)]
      ring
    · rw [hbottom]
      rw [show (0 : ℝ) - -((n : ℝ) * beta) = (n : ℝ) * beta by ring]
      rw [abs_of_pos hheight]
  rcases hw with (hleft | hright) | (htop | hbottom)
  · calc
      min (1 / 2 : ℝ) ((n : ℝ) * beta) ≤ 1 / 2 := min_le_left _ _
      _ ≤ |((k : ℂ) - w).re| := hreal (Or.inl hleft)
      _ ≤ ‖(k : ℂ) - w‖ := Complex.abs_re_le_norm _
  · calc
      min (1 / 2 : ℝ) ((n : ℝ) * beta) ≤ 1 / 2 := min_le_left _ _
      _ ≤ |((k : ℂ) - w).re| := hreal (Or.inr hright)
      _ ≤ ‖(k : ℂ) - w‖ := Complex.abs_re_le_norm _
  · calc
      min (1 / 2 : ℝ) ((n : ℝ) * beta) ≤ (n : ℝ) * beta := min_le_right _ _
      _ = |((k : ℂ) - w).im| := himag (Or.inl htop)
      _ ≤ ‖(k : ℂ) - w‖ := Complex.abs_im_le_norm _
  · calc
      min (1 / 2 : ℝ) ((n : ℝ) * beta) ≤ (n : ℝ) * beta := min_le_right _ _
      _ = |((k : ℂ) - w).im| := himag (Or.inr hbottom)
      _ ≤ ‖(k : ℂ) - w‖ := Complex.abs_im_le_norm _

/-- Once n beta >= 1/2, every enclosed pole is at least 1/2 from every
side line of the v13 rectangle; hp-tail.tex:274-275. -/
theorem hp_saddle_pole_clearance_half (n k : ℕ) (beta : ℝ)
    (hkn : k ≤ n) (hheight : 1 / 2 ≤ (n : ℝ) * beta)
    {w : ℂ} (hw : hpSaddleRectSide n beta w) :
    1 / 2 ≤ ‖(k : ℂ) - w‖ := by
  have hpos : 0 < (n : ℝ) * beta := by linarith
  have h := hp_saddle_pole_side_clearance n k beta hkn hpos hw
  exact le_trans (min_eq_left hheight).ge h

/-- Every numerator zero at indices n+1,...,3n+1 is at least 1/2 outside
the v13 rectangle; hp-tail.tex:276-277. -/
theorem hp_saddle_numerator_zero_clearance (n j : ℕ) (beta : ℝ)
    (hj₁ : n + 1 ≤ j) (hj₃ : j ≤ 3 * n + 1)
    {w : ℂ} (hw : -1 / 2 ≤ w.re ∧ w.re ≤ (n : ℝ) + 1 / 2) :
    1 / 2 ≤ ‖(j : ℂ) - w‖ := by
  have hjR : (n : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hj₁
  have hgap : (1 / 2 : ℝ) ≤ (j : ℝ) - w.re := by linarith [hw.2]
  have hnonneg : 0 ≤ (j : ℝ) - w.re := by linarith
  have hjre : (j : ℂ).re = (j : ℝ) := by simp
  calc
    (1 / 2 : ℝ) ≤ (j : ℝ) - w.re := hgap
    _ = |((j : ℂ) - w).re| := by
      rw [Complex.sub_re, hjre, abs_of_nonneg hnonneg]
    _ ≤ ‖(j : ℂ) - w‖ := Complex.abs_re_le_norm _

end

end Li2Lean.B4
