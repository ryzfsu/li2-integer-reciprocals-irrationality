/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.EnvDet
import Li2Lean.V.AllMSmoothing

/-!
# Three nested Andreief applications for v13 S0

Route: paper v13 `v-analytic.tex:64-85,103-153,530-631`.
The only adjustment to the existing P0 helper is its carrier: the contour
parameter is `Fin 4 × ℝ`, whereas `Env.continuous_andreief` fixes `ℝ`.
The proof below uses exactly the same double-permutation expansion and
product-integral theorem. The factorial normalization is unchanged.

The three matrix alignments and moment integrability are explicit hypotheses;
this file does not assert their closure for the literal V matrix.
-/

open MeasureTheory

namespace Li2Lean.V

noncomputable section

open Li2Lean.P0.Env

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The existing continuous Andreief proof, with its carrier generalized. -/
theorem continuous_andreief_carrier {q : ℕ} {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [SigmaFinite μ]
    (M : Matrix (Fin q ⊕ ι) (Fin q ⊕ ι) ℂ)
    (a : Fin q → α → ℂ) (v : α → (Fin q ⊕ ι) → ℂ)
    (hint : ∀ k c, Integrable (fun x => a k x * v x c) μ)
    (hM : ∀ k c, M (Sum.inl k) c = ∫ x, a k x * v x c ∂μ) :
    (∫ x : Fin q → α, (Matrix.of fun k l => a k (x l)).det *
      (rowRepl M (fun l => v (x l))).det ∂(Measure.pi fun _ => μ)) =
      (q.factorial : ℂ) * M.det := by
  have hterm : ∀ (σ : Equiv.Perm (Fin q)) (τ : Equiv.Perm (Fin q ⊕ ι)),
      Integrable (fun x : Fin q → α => sgnC σ * sgnC τ *
        (∏ i, M (Sum.inr i) (τ (Sum.inr i))) *
        ∏ l, (a (σ l) (x l) * v (x l) (τ (Sum.inl l))))
        (Measure.pi fun _ => μ) := by
    intro σ τ
    apply Integrable.const_mul
    exact Integrable.fintype_prod (μ := fun _ : Fin q => μ)
      (f := fun l x => a (σ l) x * v x (τ (Sum.inl l))) (fun l => hint _ _)
  simp_rw [andreief_integrand_expand M a v]
  rw [integral_finsetSum _ (fun σ _ => integrable_finsetSum _ (fun τ _ => hterm σ τ))]
  rw [← perm_core M]
  apply Finset.sum_congr rfl
  intro σ _
  rw [integral_finsetSum _ (fun τ _ => hterm σ τ)]
  apply Finset.sum_congr rfl
  intro τ _
  rw [integral_const_mul, integral_fintype_prod_eq_prod (μ := fun _ : Fin q => μ)
    (f := fun l x => a (σ l) x * v x (τ (Sum.inl l)))]
  simp only [← hM]
  ring

/-! A restricted-support version of the carrier theorem.  The interval is
`[0,1]`, so a matrix moment may be established from a kernel identity on the
support of `volume.restrict (Set.Icc 0 1)` rather than on all of `ℝ`. -/
theorem continuous_andreief_carrier_restrict_Icc
    {q : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix (Fin q ⊕ ι) (Fin q ⊕ ι) ℂ)
    (a : Fin q → ℝ → ℂ) (v : ℝ → (Fin q ⊕ ι) → ℂ)
    (hint : ∀ k c, Integrable (fun x => a k x * v x c)
      (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (hM : ∀ k c, M (Sum.inl k) c =
      ∫ x in Set.Icc (0 : ℝ) 1, a k x * v x c) :
    (∫ x : Fin q → ℝ, (Matrix.of fun k l => a k (x l)).det *
      (rowRepl M (fun l => v (x l))).det ∂
        (Measure.pi fun _ => volume.restrict (Set.Icc (0 : ℝ) 1))) =
      (q.factorial : ℂ) * M.det := by
  exact continuous_andreief_carrier
    (μ := volume.restrict (Set.Icc (0 : ℝ) 1)) M a v hint hM

/-! Kernel form of the restricted theorem.  `hKernel` is only required on
the interval, and is converted to an almost-everywhere equality for the
restricted measure.  This is the form used by the v13 S0 rows. -/
theorem continuous_andreief_carrier_restrict_Icc_of_kernel
    {q : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix (Fin q ⊕ ι) (Fin q ⊕ ι) ℂ)
    (a : Fin q → ℝ → ℂ) (v : ℝ → (Fin q ⊕ ι) → ℂ)
    (K : Fin q → ℝ → (Fin q ⊕ ι) → ℂ)
    (hint : ∀ k c, Integrable (fun x => a k x * v x c)
      (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (hKernel : ∀ k c {x : ℝ}, x ∈ Set.Icc (0 : ℝ) 1 →
      K k x c = a k x * v x c)
    (hM : ∀ k c, M (Sum.inl k) c =
      ∫ x in Set.Icc (0 : ℝ) 1, K k x c) :
    (∫ x : Fin q → ℝ, (Matrix.of fun k l => a k (x l)).det *
      (rowRepl M (fun l => v (x l))).det ∂
        (Measure.pi fun _ => volume.restrict (Set.Icc (0 : ℝ) 1))) =
      (q.factorial : ℂ) * M.det := by
  apply continuous_andreief_carrier_restrict_Icc M a v hint
  intro k c
  rw [hM k c]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  exact hKernel k c hx

/-- The two determinant factors of one Andreief application. -/
def andreiefProduct {q : ℕ} {α : Type*}
    (M : Matrix (Fin q ⊕ ι) (Fin q ⊕ ι) ℂ)
    (a : Fin q → α → ℂ) (v : α → (Fin q ⊕ ι) → ℂ)
    (x : Fin q → α) : ℂ :=
  (Matrix.of fun k l => a k (x l)).det * (rowRepl M (fun l => v (x l))).det

/-- A pointwise envelope gives a norm-integral bound with the actual mass.
This also applies to a weighted contour parameter measure. -/
theorem integral_norm_le_mass_mul {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (Φ : α → ℂ) (B : ℝ)
    (hint : Integrable Φ μ) (hbound : ∀ᵐ t ∂μ, ‖Φ t‖ ≤ B) :
    (∫ t, ‖Φ t‖ ∂μ) ≤ μ.real Set.univ * B := by
  calc
    (∫ t, ‖Φ t‖ ∂μ) ≤ ∫ _ : α, B ∂μ :=
      integral_mono_ae hint.norm (integrable_const B) hbound
    _ = μ.real Set.univ * B := by simp [integral_const]

/-- Successive lower/V, contour, and x-row antisymmetrizations. No exchange
of integrals is used: the x and contour factors remain nested over v. -/
theorem nested_andreief {m L h : ℕ} {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μv : Measure α) (μz : Measure β) (μx : Measure γ)
    [SigmaFinite μv] [SigmaFinite μz] [SigmaFinite μx]
    (M0 : Matrix (Fin L ⊕ Fin m) (Fin L ⊕ Fin m) ℂ)
    (a0 : Fin L → α → ℂ) (b0 : α → (Fin L ⊕ Fin m) → ℂ)
    (M1 : (Fin L → α) → Matrix (Fin m ⊕ Fin L) (Fin m ⊕ Fin L) ℂ)
    (a1 : (Fin L → α) → Fin m → β → ℂ)
    (b1 : (Fin L → α) → β → (Fin m ⊕ Fin L) → ℂ)
    (M2 : (Fin L → α) → Matrix (Fin m ⊕ Fin h) (Fin m ⊕ Fin h) ℂ)
    (a2 : (Fin L → α) → Fin m → γ → ℂ)
    (b2 : (Fin L → α) → γ → (Fin m ⊕ Fin h) → ℂ)
    (hint0 : ∀ k c, Integrable (fun t => a0 k t * b0 t c) μv)
    (hmom0 : ∀ k c, M0 (Sum.inl k) c = ∫ t, a0 k t * b0 t c ∂μv)
    (hint1 : ∀ v k c, Integrable (fun t => a1 v k t * b1 v t c) μz)
    (hmom1 : ∀ v k c, M1 v (Sum.inl k) c = ∫ t, a1 v k t * b1 v t c ∂μz)
    (hint2 : ∀ v k c, Integrable (fun t => a2 v k t * b2 v t c) μx)
    (hmom2 : ∀ v k c, M2 v (Sum.inl k) c = ∫ t, a2 v k t * b2 v t c ∂μx)
    (halign1 : ∀ v, (M1 v).det = (rowRepl M0 (fun l => b0 (v l))).det)
    (halign2 : ∀ v, (M2 v).det = (Matrix.of fun k l => a0 k (v l)).det) :
    (∫ v : Fin L → α,
      (∫ x : Fin m → γ, andreiefProduct (M2 v) (a2 v) (b2 v) x
        ∂(Measure.pi fun _ => μx)) *
      (∫ z : Fin m → β, andreiefProduct (M1 v) (a1 v) (b1 v) z
        ∂(Measure.pi fun _ => μz)) ∂(Measure.pi fun _ => μv)) =
      ((m.factorial : ℂ) ^ 2 * (L.factorial : ℂ)) * M0.det := by
  have h0 := continuous_andreief_carrier μv M0 a0 b0 hint0 hmom0
  have h1 := fun v => continuous_andreief_carrier μz (M1 v) (a1 v) (b1 v)
    (hint1 v) (hmom1 v)
  have h2 := fun v => continuous_andreief_carrier μx (M2 v) (a2 v) (b2 v)
    (hint2 v) (hmom2 v)
  change (∫ v : Fin L → α,
    (∫ x : Fin m → γ, (Matrix.of fun k l => a2 v k (x l)).det *
      (rowRepl (M2 v) (fun l => b2 v (x l))).det ∂(Measure.pi fun _ => μx)) *
    (∫ z : Fin m → β, (Matrix.of fun k l => a1 v k (z l)).det *
      (rowRepl (M1 v) (fun l => b1 v (z l))).det ∂(Measure.pi fun _ => μz))
      ∂(Measure.pi fun _ => μv)) = _
  simp_rw [h2, h1, halign2, halign1]
  calc
    _ = ∫ v : Fin L → α, (m.factorial : ℂ) ^ 2 *
        ((Matrix.of fun k l => a0 k (v l)).det *
          (rowRepl M0 (fun l => b0 (v l))).det) ∂(Measure.pi fun _ => μv) := by
      apply integral_congr_ae
      filter_upwards [] with v
      ring
    _ = _ := by rw [integral_const_mul, h0]; ring

/-- Triangle inequality with the exact S0 factorial denominator. -/
theorem s0_multiplicative_of_integral {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (q m L : ℕ) (G : ℂ) (Φ : α → ℂ) (Tq phiMax : ℝ)
    (hG : G = ((q : ℂ) ^ Li2Lean.B3.s0Exponent m /
      ((m.factorial : ℂ) ^ 2 * (L.factorial : ℂ))) * ∫ t, Φ t ∂μ)
    (hbound : (∫ t, ‖Φ t‖ ∂μ) ≤ Tq ^ m * |phiMax|) :
    Li2Lean.B3.s0MultiplicativeBound q m L G Tq phiMax := by
  unfold Li2Lean.B3.s0MultiplicativeBound Li2Lean.B3.s0MagnitudeRhs
  rw [hG, norm_mul, norm_div, norm_pow, Complex.norm_natCast,
    norm_mul, norm_pow, Complex.norm_natCast, Complex.norm_natCast]
  have hfac : 0 ≤ (q : ℝ) ^ Li2Lean.B3.s0Exponent m /
      ((m.factorial : ℝ) ^ 2 * (L.factorial : ℝ)) := by positivity
  calc
    _ ≤ ((q : ℝ) ^ Li2Lean.B3.s0Exponent m /
      ((m.factorial : ℝ) ^ 2 * (L.factorial : ℝ))) *
        (Tq ^ m * |phiMax|) :=
      mul_le_mul_of_nonneg_left ((norm_integral_le_integral_norm _).trans hbound) hfac
    _ = _ := by ring

/-- Connect the exact factorial identity produced by `nested_andreief` to
the existing multiplicative S0 interface. No nonvanishing is required. -/
theorem s0_multiplicative_of_factorial_identity
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (q m L : ℕ) (G D : ℂ) (Φ : α → ℂ) (Tq phiMax : ℝ)
    (hG : G = (q : ℂ) ^ Li2Lean.B3.s0Exponent m * D)
    (hfactorial : (∫ t, Φ t ∂μ) =
      ((m.factorial : ℂ) ^ 2 * (L.factorial : ℂ)) * D)
    (hbound : (∫ t, ‖Φ t‖ ∂μ) ≤ Tq ^ m * |phiMax|) :
    Li2Lean.B3.s0MultiplicativeBound q m L G Tq phiMax := by
  apply s0_multiplicative_of_integral μ q m L G Φ Tq phiMax _ hbound
  rw [hG, hfactorial]
  have hm : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  have hL : (L.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero L
  field_simp

/-- The S0 envelope step from an actual measure mass `Tq^m` and an
integrable pointwise bound, keeping the factorial denominator. -/
theorem s0_multiplicative_of_pointwise {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (q m L : ℕ) (G : ℂ)
    (Φ : α → ℂ) (Tq phiMax : ℝ)
    (hG : G = ((q : ℂ) ^ Li2Lean.B3.s0Exponent m /
      ((m.factorial : ℂ) ^ 2 * (L.factorial : ℂ))) * ∫ t, Φ t ∂μ)
    (hmass : μ.real Set.univ = Tq ^ m)
    (hint : Integrable Φ μ) (hpoint : ∀ᵐ t ∂μ, ‖Φ t‖ ≤ |phiMax|) :
    Li2Lean.B3.s0MultiplicativeBound q m L G Tq phiMax := by
  apply s0_multiplicative_of_integral μ q m L G Φ Tq phiMax hG
  simpa [hmass] using integral_norm_le_mass_mul μ Φ |phiMax| hint hpoint

end

end Li2Lean.V

#print axioms Li2Lean.V.continuous_andreief_carrier
#print axioms Li2Lean.V.nested_andreief
#print axioms Li2Lean.V.integral_norm_le_mass_mul
#print axioms Li2Lean.V.s0_multiplicative_of_integral
#print axioms Li2Lean.V.s0_multiplicative_of_factorial_identity
#print axioms Li2Lean.V.s0_multiplicative_of_pointwise
