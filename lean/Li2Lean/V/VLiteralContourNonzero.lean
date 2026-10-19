/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

This module proves the v13 signed contour Laurent moment
(`source/chapters/v-analytic.tex:85-104`) from this project's VContour
definitions.  It is split from `VContour.lean` so the measure-splitting and
primitive lemmas remain local to the nonzero-moment interface.
-/

import Li2Lean.V.VLiteralContour

namespace Li2Lean
namespace V
namespace Literal

noncomputable section

open MeasureTheory Set

/- Generic primitive helper used to evaluate each v13 path piece in
   `source/chapters/v-analytic.tex:96-104`; it is not a new contour route. -/
private lemma intervalIntegral_zpow_mul_deriv
    (d : ℤ) (hd : d ≠ 0) {z z' : ℝ → ℂ} {a b : ℝ}
    (hz : ∀ t ∈ uIcc a b, z t ≠ 0)
    (hzc : ContinuousOn z (uIcc a b))
    (hzc' : ContinuousOn z' (uIcc a b))
    (hderiv : ∀ t ∈ uIcc a b, HasDerivAt z (z' t) t) :
    (∫ t in a..b, z t ^ (d - 1) * z' t) =
      (z b ^ d - z a ^ d) / (d : ℂ) := by
  have hpow : ContinuousOn (fun t => z t ^ (d - 1)) (uIcc a b) :=
    hzc.zpow₀ (d - 1) (fun t ht => Or.inl (hz t ht))
  have hInt : IntervalIntegrable (fun t => z t ^ (d - 1) * z' t)
      volume a b := (hpow.mul hzc').intervalIntegrable
  have hprim : ∀ t ∈ uIcc a b,
      HasDerivAt (fun s => z s ^ d / (d : ℂ))
        (z t ^ (d - 1) * z' t) t := by
    intro t ht
    have hp := (hasDerivAt_zpow d (z t) (Or.inl (hz t ht))).comp t (hderiv t ht)
    have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd
    have hdiv := hp.div_const (d : ℂ)
    convert hdiv using 1
    · funext s
      rfl
    · field_simp [hdC]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hprim hInt]
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  field_simp [hdC]

/- The four v13 pieces avoid the origin, as required by the Laurent powers
   in `source/chapters/v-analytic.tex:87-104`. -/
private lemma point_ne_zero (q : ℕ) (hq : 2 ≤ q) (piece : Fin 4)
    {t : ℝ} (ht : t ∈ uIcc (0 : ℝ) 1) :
    vContourPoint q piece t ≠ 0 := by
  have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by simpa [uIcc_of_le] using ht
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hrpos : 0 < vContourRadius := by norm_num [vContourRadius]
  have hrle : vContourRadius ≤ (1 : ℝ) := by norm_num [vContourRadius]
  have hqr : vContourRadius ≤ (q : ℝ) := by linarith
  have hqrmul : 0 ≤ ((q : ℝ) - vContourRadius) * (1 - t) := by
    exact mul_nonneg (sub_nonneg.mpr hqr) (sub_nonneg.mpr ht'.2)
  fin_cases piece
  · have hneg : -(q : ℝ) + ((q : ℝ) - vContourRadius) * t < 0 := by
      nlinarith [hrpos, hqrmul]
    simp [vContourPoint]
    intro hz
    have hz' := congrArg Complex.re hz
    norm_num at hz'
    nlinarith [hneg]
  · have hpos : 0 < vContourRadius + (1 - vContourRadius) * t := by
      have hmul : 0 ≤ (1 - vContourRadius) * t :=
        mul_nonneg (sub_nonneg.mpr hrle) ht'.1
      nlinarith
    simp [vContourPoint]
    intro hz
    have hz' := congrArg Complex.re hz
    norm_num at hz'
    nlinarith [hpos]
  · change Complex.ofReal vContourRadius *
      Complex.exp (Complex.I * (Complex.ofReal Real.pi * t)) ≠ 0
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hrpos))
      (Complex.exp_ne_zero _)
  · change Complex.ofReal vContourRadius *
      Complex.exp (Complex.I * (Complex.ofReal Real.pi +
        Complex.ofReal Real.pi * t)) ≠ 0
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hrpos))
      (Complex.exp_ne_zero _)

/- Negative real segment of `Gamma_q`, v13 `source/chapters/v-analytic.tex:87-94,96-104`. -/
private lemma neg_piece_integral (q : ℕ) (hq : 2 ≤ q) {d : ℤ} (hd : d ≠ 0) :
    (∫ t in (0 : ℝ)..1,
      vContourWeight q (0, t) * vContourPoint q 0 t ^ (d - 1)) =
      ((-(Complex.ofReal vContourRadius)) ^ d - (-(q : ℂ)) ^ d) / (d : ℂ) := by
  let z : ℝ → ℂ := fun t => -(q : ℂ) +
    (Complex.ofReal (q : ℝ) - Complex.ofReal vContourRadius) * t
  let z' : ℝ → ℂ := fun _ => Complex.ofReal (q : ℝ) - Complex.ofReal vContourRadius
  have hz : ∀ t ∈ uIcc (0 : ℝ) 1, z t ≠ 0 := by
    intro t ht
    exact point_ne_zero q hq 0 ht
  have hzc : ContinuousOn z (uIcc (0 : ℝ) 1) := by
    intro t ht
    dsimp [z]
    fun_prop
  have hzc' : ContinuousOn z' (uIcc (0 : ℝ) 1) := continuousOn_const
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt z (z' t) t := by
    intro t ht
    dsimp [z, z']
    convert (hasDerivAt_const t (-(q : ℂ))).add
      ((hasDerivAt_const t (Complex.ofReal (q : ℝ) -
        Complex.ofReal vContourRadius)).mul
        ((hasDerivAt_id (t : ℂ)).comp_ofReal)) using 1
    · funext s
      dsimp [id]
    · push_cast
      ring
  have h := intervalIntegral_zpow_mul_deriv d hd hz hzc hzc' hderiv
  dsimp [z, z'] at h
  calc
    (∫ t in (0 : ℝ)..1,
      vContourWeight q (0, t) * vContourPoint q 0 t ^ (d - 1)) =
        ∫ t in (0 : ℝ)..1,
          (-↑q + (↑q - ↑vContourRadius) * (t : ℂ)) ^ (d - 1) *
            (↑q - ↑vContourRadius) := by
      apply intervalIntegral.integral_congr
      intro t ht
      simp [vContourWeight, vContourComponentWeight, vContourDerivative,
        vContourPoint]
      ring
    _ = ((-↑q + (↑q - ↑vContourRadius) * (1 : ℂ)) ^ d -
          (-↑q + (↑q - ↑vContourRadius) * (0 : ℂ)) ^ d) / (d : ℂ) := h
    _ = ((-(Complex.ofReal vContourRadius)) ^ d - (-(q : ℂ)) ^ d) / (d : ℂ) := by
      congr 1 <;> push_cast <;> ring

/- Positive real segment of `Gamma_q`, v13 `source/chapters/v-analytic.tex:87-94,96-104`. -/
private lemma pos_piece_integral (q : ℕ) (hq : 2 ≤ q) {d : ℤ} (hd : d ≠ 0) :
    (∫ t in (0 : ℝ)..1,
      vContourWeight q (1, t) * vContourPoint q 1 t ^ (d - 1)) =
      ((1 : ℂ) ^ d - (Complex.ofReal vContourRadius) ^ d) / (d : ℂ) := by
  let z : ℝ → ℂ := fun t => Complex.ofReal vContourRadius +
    (1 - Complex.ofReal vContourRadius) * t
  let z' : ℝ → ℂ := fun _ => 1 - Complex.ofReal vContourRadius
  have hz : ∀ t ∈ uIcc (0 : ℝ) 1, z t ≠ 0 := by
    intro t ht
    exact point_ne_zero q hq 1 ht
  have hzc : ContinuousOn z (uIcc (0 : ℝ) 1) := by
    intro t ht
    dsimp [z]
    fun_prop
  have hzc' : ContinuousOn z' (uIcc (0 : ℝ) 1) := continuousOn_const
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt z (z' t) t := by
    intro t ht
    dsimp [z, z']
    convert (hasDerivAt_const t (Complex.ofReal vContourRadius)).add
      ((hasDerivAt_const t (1 - Complex.ofReal vContourRadius)).mul
        ((hasDerivAt_id (t : ℂ)).comp_ofReal)) using 1
    · funext s
      dsimp [id]
    · push_cast
      ring
  have h := intervalIntegral_zpow_mul_deriv d hd hz hzc hzc' hderiv
  dsimp [z, z'] at h
  calc
    (∫ t in (0 : ℝ)..1,
      vContourWeight q (1, t) * vContourPoint q 1 t ^ (d - 1)) =
        ∫ t in (0 : ℝ)..1,
          (↑vContourRadius + (1 - ↑vContourRadius) * (t : ℂ)) ^ (d - 1) *
            (1 - ↑vContourRadius) := by
      apply intervalIntegral.integral_congr
      intro t ht
      simp [vContourWeight, vContourComponentWeight, vContourDerivative,
        vContourPoint]
      ring
    _ = ((↑vContourRadius + (1 - ↑vContourRadius) * (1 : ℂ)) ^ d -
          (↑vContourRadius + (1 - ↑vContourRadius) * (0 : ℂ)) ^ d) / (d : ℂ) := h
    _ = ((1 : ℂ) ^ d - (Complex.ofReal vContourRadius) ^ d) / (d : ℂ) := by
      congr 1 <;> push_cast <;> ring

/- Upper half-circle with weight `c_q-1`, v13 `source/chapters/v-analytic.tex:87-104`. -/
private lemma upper_arc_integral (q : ℕ) (hq : 2 ≤ q) {d : ℤ} (hd : d ≠ 0) :
    (∫ t in (0 : ℝ)..1,
      vContourWeight q (2, t) * vContourPoint q 2 t ^ (d - 1)) =
      (vContourCoefficient q - 1) *
        (((-(Complex.ofReal vContourRadius)) ^ d -
          (Complex.ofReal vContourRadius) ^ d) / (d : ℂ)) := by
  let z : ℝ → ℂ := fun t => Complex.ofReal vContourRadius *
    Complex.exp (Complex.I * (Complex.ofReal Real.pi * t))
  let z' : ℝ → ℂ := fun t => Complex.I * Complex.ofReal Real.pi * z t
  have hz : ∀ t ∈ uIcc (0 : ℝ) 1, z t ≠ 0 := by
    intro t ht
    exact point_ne_zero q hq 2 ht
  have hzc : ContinuousOn z (uIcc (0 : ℝ) 1) := by
    intro t ht
    dsimp [z]
    fun_prop
  have hzc' : ContinuousOn z' (uIcc (0 : ℝ) 1) := by
    intro t ht
    dsimp [z']
    fun_prop
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt z (z' t) t := by
    intro t ht
    dsimp [z, z']
    have harg : HasDerivAt
        (fun s : ℝ => Complex.I * (Complex.ofReal Real.pi * (s : ℂ)))
        (Complex.I * Complex.ofReal Real.pi) t := by
      convert ((hasDerivAt_const t Complex.I).mul
        ((hasDerivAt_const t (Complex.ofReal Real.pi)).mul
          ((hasDerivAt_id (t : ℂ)).comp_ofReal))) using 1
      · funext s
        rfl
      · push_cast
        ring
    have he := harg.cexp
    convert (hasDerivAt_const t (Complex.ofReal vContourRadius)).mul he using 1 <;>
      simp [mul_assoc] <;> ring
  have hcore := intervalIntegral_zpow_mul_deriv d hd hz hzc hzc' hderiv
  have hweight : ∀ t : ℝ,
      vContourWeight q (2, t) * vContourPoint q 2 t ^ (d - 1) =
        (vContourCoefficient q - 1) *
          (z t ^ (d - 1) * z' t) := by
    intro t
    simp [vContourWeight, vContourComponentWeight, vContourDerivative,
      vContourPoint, z, z']
    ring
  calc
    (∫ t in (0 : ℝ)..1,
      vContourWeight q (2, t) * vContourPoint q 2 t ^ (d - 1)) =
        ∫ t in (0 : ℝ)..1,
          (vContourCoefficient q - 1) * (z t ^ (d - 1) * z' t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      exact hweight t
    _ = (vContourCoefficient q - 1) *
          (∫ t in (0 : ℝ)..1, z t ^ (d - 1) * z' t) := by
      rw [intervalIntegral.integral_const_mul]
    _ = (vContourCoefficient q - 1) *
          ((z 1 ^ d - z 0 ^ d) / (d : ℂ)) := by rw [hcore]
    _ = (vContourCoefficient q - 1) *
          (((-(Complex.ofReal vContourRadius)) ^ d -
            (Complex.ofReal vContourRadius) ^ d) / (d : ℂ)) := by
      congr 2
      have h0 : z 0 = Complex.ofReal vContourRadius := by
        dsimp [z]
        simp
      have h1 : z 1 = -(Complex.ofReal vContourRadius) := by
        dsimp [z]
        norm_num
        rw [show Complex.I * (Complex.ofReal Real.pi) =
            (Complex.ofReal Real.pi) * Complex.I by ring]
        rw [Complex.exp_pi_mul_I]
        ring
      rw [h0, h1]

/- Lower half-circle with weight `c_q`, v13 `source/chapters/v-analytic.tex:87-104`. -/
private lemma lower_arc_integral (q : ℕ) (hq : 2 ≤ q) {d : ℤ} (hd : d ≠ 0) :
    (∫ t in (0 : ℝ)..1,
      vContourWeight q (3, t) * vContourPoint q 3 t ^ (d - 1)) =
      vContourCoefficient q *
        (((Complex.ofReal vContourRadius) ^ d -
          (-(Complex.ofReal vContourRadius)) ^ d) / (d : ℂ)) := by
  let z : ℝ → ℂ := fun t => Complex.ofReal vContourRadius *
    Complex.exp (Complex.I * (Complex.ofReal Real.pi +
      Complex.ofReal Real.pi * t))
  let z' : ℝ → ℂ := fun t => Complex.I * Complex.ofReal Real.pi * z t
  have hz : ∀ t ∈ uIcc (0 : ℝ) 1, z t ≠ 0 := by
    intro t ht
    exact point_ne_zero q hq 3 ht
  have hzc : ContinuousOn z (uIcc (0 : ℝ) 1) := by
    intro t ht
    dsimp [z]
    fun_prop
  have hzc' : ContinuousOn z' (uIcc (0 : ℝ) 1) := by
    intro t ht
    dsimp [z']
    fun_prop
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt z (z' t) t := by
    intro t ht
    dsimp [z, z']
    have harg : HasDerivAt
        (fun s : ℝ => Complex.I * (Complex.ofReal Real.pi +
          Complex.ofReal Real.pi * (s : ℂ)))
        (Complex.I * Complex.ofReal Real.pi) t := by
      convert (hasDerivAt_const t Complex.I).mul
        ((hasDerivAt_const t (Complex.ofReal Real.pi)).add
          ((hasDerivAt_const t (Complex.ofReal Real.pi)).mul
            ((hasDerivAt_id (t : ℂ)).comp_ofReal))) using 1
      · funext s
        rfl
      · push_cast
        ring
    have he := harg.cexp
    convert (hasDerivAt_const t (Complex.ofReal vContourRadius)).mul he using 1 <;>
      simp [mul_assoc] <;> ring
  have hcore := intervalIntegral_zpow_mul_deriv d hd hz hzc hzc' hderiv
  have hweight : ∀ t : ℝ,
      vContourWeight q (3, t) * vContourPoint q 3 t ^ (d - 1) =
        vContourCoefficient q * (z t ^ (d - 1) * z' t) := by
    intro t
    simp [vContourWeight, vContourComponentWeight, vContourDerivative,
      vContourPoint, z, z']
    ring
  calc
    (∫ t in (0 : ℝ)..1,
      vContourWeight q (3, t) * vContourPoint q 3 t ^ (d - 1)) =
        ∫ t in (0 : ℝ)..1,
          vContourCoefficient q * (z t ^ (d - 1) * z' t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      exact hweight t
    _ = vContourCoefficient q *
          (∫ t in (0 : ℝ)..1, z t ^ (d - 1) * z' t) := by
      rw [intervalIntegral.integral_const_mul]
    _ = vContourCoefficient q *
          ((z 1 ^ d - z 0 ^ d) / (d : ℂ)) := by rw [hcore]
    _ = vContourCoefficient q *
          (((Complex.ofReal vContourRadius) ^ d -
            (-(Complex.ofReal vContourRadius)) ^ d) / (d : ℂ)) := by
      congr 2
      have h0 : z 0 = -(Complex.ofReal vContourRadius) := by
        dsimp [z]
        norm_num
        rw [show Complex.I * Complex.ofReal Real.pi =
            (Complex.ofReal Real.pi) * Complex.I by ring]
        rw [Complex.exp_pi_mul_I]
        ring
      have h1 : z 1 = Complex.ofReal vContourRadius := by
        dsimp [z]
        norm_num
        rw [show Complex.I * (Complex.ofReal Real.pi +
            Complex.ofReal Real.pi) =
          (2 : ℂ) * (Complex.ofReal Real.pi) * Complex.I by ring]
        rw [Complex.exp_two_pi_mul_I]
        ring
      rw [h0, h1]

/- Integrability of the positive parameter representation used in v13
   `source/chapters/v-analytic.tex:96-104`. -/
private lemma generic_moment_integrable (q : ℕ) (hq : 2 ≤ q) {d : ℤ} (hd : d ≠ 0) :
    Integrable
      (vContourIntegrand q (fun z : ℂ => z ^ (d - 1)))
      vContourParameterMeasure := by
  let g : Fin 4 × ℝ → ℂ := fun p =>
    vContourIntegrand q (fun z : ℂ => z ^ (d - 1)) p
  have hcont : ContinuousOn g
      ((Set.univ : Set (Fin 4)) ×ˢ Set.Icc (0 : ℝ) 1) := by
    apply continuousOn_of_forall_continuousAt
    rintro ⟨piece, t⟩ hp
    have ht : t ∈ Set.Icc (0 : ℝ) 1 := (Set.mem_prod.mp hp).2
    have hpnt : vContourPoint q piece t ≠ 0 :=
      point_ne_zero q hq piece (by simpa [uIcc_of_le] using ht)
    have hpoint : ContinuousAt
        (fun s : ℝ => vContourPoint q piece s) t := by
      fin_cases piece <;> simp [vContourPoint] <;> fun_prop
    have hzpow : ContinuousAt
        (fun s : ℝ => vContourPoint q piece s ^ (d - 1)) t :=
      hpoint.zpow₀ (d - 1) (Or.inl hpnt)
    have hw : ContinuousAt
        (fun s : ℝ => vContourWeight q (piece, s)) t := by
      fin_cases piece <;>
        simp [vContourWeight, vContourComponentWeight, vContourDerivative,
          vContourPoint] <;> fun_prop
    have hs : ({piece} ×ˢ (Set.univ : Set ℝ)) ∈ nhds (piece, t) := by
      apply (isOpen_discrete ({piece} : Set (Fin 4))).prod isOpen_univ |>.mem_nhds
      simp
    have hev : (fun p : Fin 4 × ℝ => g p) =ᶠ[nhds (piece, t)]
        (fun p : Fin 4 × ℝ =>
          vContourWeight q (piece, p.2) *
            vContourPoint q piece p.2 ^ (d - 1)) := by
      filter_upwards [hs] with p hp'
      rcases p with ⟨p1, p2⟩
      have hpiece : p1 = piece := by
        exact Set.mem_singleton_iff.mp (Set.mem_prod.mp hp').1
      subst p1
      dsimp [g]
      rfl
    have hcomp : ContinuousAt
        (fun p : Fin 4 × ℝ =>
          vContourWeight q (piece, p.2) *
            vContourPoint q piece p.2 ^ (d - 1)) (piece, t) := by
      change ContinuousAt
        ((fun s : ℝ => vContourWeight q (piece, s) *
          vContourPoint q piece s ^ (d - 1)) ∘ Prod.snd) (piece, t)
      exact (hw.mul hzpow).comp (x := (piece, t))
        (f := Prod.snd)
        (g := fun s : ℝ => vContourWeight q (piece, s) *
          vContourPoint q piece s ^ (d - 1)) continuousAt_snd
    exact hcomp.congr_of_eventuallyEq hev
  have hcompact : IsCompact ((Set.univ : Set (Fin 4)) ×ˢ Set.Icc (0 : ℝ) 1) :=
    isCompact_univ.prod isCompact_Icc
  have hIntOn : IntegrableOn g
      ((Set.univ : Set (Fin 4)) ×ˢ Set.Icc (0 : ℝ) 1)
      (Measure.count.prod volume) :=
    ContinuousOn.integrableOn_compact hcompact hcont
  have hIntRestrict : Integrable g
      ((Measure.count.prod volume).restrict
        ((Set.univ : Set (Fin 4)) ×ˢ Set.Icc (0 : ℝ) 1)) := hIntOn.integrable
  have hmeasure :
      (Measure.count.prod volume).restrict
          ((Set.univ : Set (Fin 4)) ×ˢ Set.Icc (0 : ℝ) 1) =
        Measure.count.prod (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    rw [← Measure.prod_restrict]
    simp
  rw [hmeasure] at hIntRestrict
  exact hIntRestrict

theorem vContourLaurentMoment_of_ne_zero (q : ℕ) (hq : 2 ≤ q)
    {d : ℤ} (hd : d ≠ 0) :
    vContourLaurentMoment q d =
      (1 - (-(q : ℂ)) ^ d) / (d : ℂ) := by
  let f : ℂ → ℂ := fun z => z ^ (d - 1)
  have hF : Integrable (vContourIntegrand q f) vContourParameterMeasure := by
    exact generic_moment_integrable q hq hd
  change vContourIntegral q f = _
  rw [vContourIntegral_eq_sum_setIntegral q f hF]
  rw [Fin.sum_univ_four]
  have hset (piece : Fin 4) :
      (∫ t in Set.Icc (0 : ℝ) 1,
        vContourWeight q (piece, t) * f (vContourPoint q piece t)) =
      ∫ t in (0 : ℝ)..1,
        vContourWeight q (piece, t) * f (vContourPoint q piece t) := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
    rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [hset 0, hset 1, hset 2, hset 3]
  rw [neg_piece_integral q hq hd, pos_piece_integral q hq hd,
    upper_arc_integral q hq hd, lower_arc_integral q hq hd]
  unfold vContourCoefficient
  have hpi : Complex.ofReal Real.pi ≠ 0 :=
    Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  simp only [one_zpow]
  field_simp [Complex.I_ne_zero, hpi]
  ring

end
end Literal
end V
end Li2Lean

#print axioms Li2Lean.V.Literal.vContourLaurentMoment_of_ne_zero
