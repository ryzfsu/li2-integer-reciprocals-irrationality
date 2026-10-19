/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.EnvMainQ
import Mathlib
import Li2Lean.P0.Contour
import Li2Lean.V.VFamily
import Li2Lean.Statement
import Li2Lean.L0Endpoints
import Li2Lean.L1
import Li2Lean.P0.B2Interpolation
import Li2Lean.P0.PositiveBaseParam
import Li2Lean.P0.PositiveBaseQContourFactor
import Li2Lean.P0.IntegerizerRate
import Li2Lean.P0.Nonvanishing
import Li2Lean.P0.FinalEnvelopeWiring       -- li2_half_irrational_unconditional
import Li2Lean.P0.AlphaUnconditional
import Li2Lean.P0.ActualReferenceDual
import Li2Lean.P0.ReferenceFiniteEnergyAssembly
import Li2Lean.P0.ContourEnergyLowerBound
import Li2Lean.P0.TubeTransferAssembly
import Li2Lean.P0.PositiveBaseFrequencyTail
import Li2Lean.P0.ActualFrequencyTailFactor
import Li2Lean.P0.QSmoothingBudget
import Li2Lean.P0.PositiveBaseFrequencyTailFactor
import Li2Lean.P0.PositiveBaseCutoffAggregation
import Li2Lean.P0.ConfigOneBodyBound
import Li2Lean.P0.ConfigWitnessLinearShift
import Li2Lean.P0.CellBound.Main
import Li2Lean.AllN.B2SmoothingProfile
import Li2Lean.B3.SignedSmoothing
import Li2Lean.B4.FinalGlue
import Li2Lean.B4.Integerization
import Li2Lean.B4.ResidueTailAlgebra

namespace Li2Lean.AllNAssembly

noncomputable section

open Filter Topology
open MeasureTheory
open Li2Lean.P0.PositiveBase

/-! ## B.0 Small real-analysis helpers (sorry-free) -/

/-- `log 0 = 0` in Mathlib, so every log-form determinant bound needs the
nonzero guard; this converts a guarded log bound into an absolute bound. -/
theorem abs_le_exp_of_log_abs_le {x B : ℝ}
    (h : x ≠ 0 → Real.log |x| ≤ B) : |x| ≤ Real.exp B := by
  by_cases hx : x = 0
  · simp [hx, (Real.exp_pos B).le]
  · calc |x| = Real.exp (Real.log |x|) :=
          (Real.exp_log (abs_pos.mpr hx)).symm
      _ ≤ Real.exp B := Real.exp_le_exp.mpr (h hx)

/-! ## B.1 Positive P0 range, 2 ≤ n ≤ 11 -/

/-- The paper-faithful uniform determinant bound, v13 p0-analytic.tex
`eq:p0-q-uniform-det` (Lemma p0-smoothing-transfer):
`log|G_{m,q}(Li2(1/q))| ≤ -α m² + 10 m log m + 58 m + 301 + 40 log m`.
NOTE: `P0.PositiveBase.AnalyticEstimateAt` uses `56 m + 301` and no
`40 log m`; that is STRONGER than the paper and cannot be obtained from it
for all `m ≥ 8` (absorption works only eventually). -/
def P0PaperAnalyticEstimate (alpha : ℝ) (q : ℤ) (F : P0Family) : Prop :=
  ∀ m : ℕ, 8 ≤ m → 4 ∣ m →
    |(F.G m).eval (li2InvValue q)| ≤
      Real.exp (-alpha * (m : ℝ) ^ 2 + 10 * (m : ℝ) * Real.log (m : ℝ) +
        58 * (m : ℝ) + 301 + 40 * Real.log (m : ℝ))

theorem P0PaperAnalyticEstimate.mono {alpha beta : ℝ} {q : ℤ} {F : P0Family}
    (hab : alpha ≤ beta) (h : P0PaperAnalyticEstimate beta q F) :
    P0PaperAnalyticEstimate alpha q F := by
  intro m hm h4
  refine (h m hm h4).trans (Real.exp_le_exp.mpr ?_)
  have hm2 : (0 : ℝ) ≤ (m : ℝ) ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hab hm2]

/-- The v13 chord `L(λ)` at `λ = log(q/2)` (p0-analytic.tex:842-850), in the
exact syntactic form produced by `Li2Lean.positiveBaseEndpointChord`. -/
def p0PositiveChord (q : ℕ) : ℝ :=
  (248035 / 125000 : ℝ) +
    (positiveBaseParameter q / Real.log ((11 : ℝ) / 2)) *
      ((77597 / 100000 : ℝ) - 248035 / 125000)

/-! The positive-base variational profile is the actual P0 energy with the
v13 one-body shifts `phi_q = phi_2 + lambda * Re(z)` and
`psi_q = psi_2 - lambda * t` (PositiveBaseParam.lean:108-114).  The extra
integrability clause records the companion first moment used by that affine
shift; its equivalence with the paper's admissible finite-energy domain is a
separate measure-theoretic producer. -/


/-- Paper route for the analytic producer (p0-analytic.tex:715-878).
The profile is fixed to the actual shifted P0 energy infimum above; only its
concavity, endpoint bounds and determinant estimate remain Prop obligations. -/
structure P0PositiveEnergyProfile where
  alpha : ℝ → ℝ
  concave : ConcaveOn ℝ (Set.Icc (0 : ℝ) (Real.log ((11 : ℝ) / 2))) alpha
  endpoint_two : (248035 / 125000 : ℝ) ≤ alpha 0
  endpoint_eleven : (77597 / 100000 : ℝ) ≤ alpha (Real.log ((11 : ℝ) / 2))
  smoothing : ∀ (q : ℕ) (hq : InRange (q : ℤ)), 3 ≤ q →
    P0PaperAnalyticEstimate (alpha (positiveBaseParameter q)) (q : ℤ)
      (family (q : ℤ) hq)

theorem p0PositiveEnergyProfileActual_concave :
    ConcaveOn ℝ (Set.Icc (0 : ℝ) (Real.log ((11 : ℝ) / 2)))
      p0PositiveEnergyProfileActual := by
  have hnonempty : ∀ lambda : ℝ,
      (p0PositiveEnergyValues lambda).Nonempty :=
    p0PositiveEnergyValues_nonempty
  have hconcave_nonneg :
      ConcaveOn ℝ (Set.Ici (0 : ℝ)) p0PositiveEnergyProfileActual := by
    unfold p0PositiveEnergyProfileActual
    refine ⟨convex_Ici _, ?_⟩
    intro x hx y hy a b ha hb hab
    have hxbound : BddBelow (p0PositiveEnergyValues x) :=
      p0PositiveEnergyValues_bddBelow x hx
    have hybound : BddBelow (p0PositiveEnergyValues y) :=
      p0PositiveEnergyValues_bddBelow y hy
    apply le_csInf (hnonempty (a • x + b • y))
    rintro e ⟨M, hM, rfl⟩
    have hxM : p0PositiveEnergyValue x M ∈ p0PositiveEnergyValues x :=
      ⟨M, hM, rfl⟩
    have hyM : p0PositiveEnergyValue y M ∈ p0PositiveEnergyValues y :=
      ⟨M, hM, rfl⟩
    have hxinf : sInf (p0PositiveEnergyValues x) ≤
        p0PositiveEnergyValue x M := csInf_le hxbound hxM
    have hyinf : sInf (p0PositiveEnergyValues y) ≤
        p0PositiveEnergyValue y M := csInf_le hybound hyM
    have hweighted :
        a • sInf (p0PositiveEnergyValues x) + b • sInf (p0PositiveEnergyValues y) ≤
          a • p0PositiveEnergyValue x M + b • p0PositiveEnergyValue y M := by
      exact add_le_add
        (smul_le_smul_of_nonneg_left hxinf ha)
        (smul_le_smul_of_nonneg_left hyinf hb)
    calc
      a • sInf (p0PositiveEnergyValues x) + b • sInf (p0PositiveEnergyValues y) ≤
          a • p0PositiveEnergyValue x M + b • p0PositiveEnergyValue y M := hweighted
      _ = p0PositiveEnergyValue (a • x + b • y) M := by
        simp only [p0PositiveEnergyValue, smul_eq_mul]
        ring_nf
        linear_combination (P0.p0RegularizedEnergyValue M) * hab
  refine ⟨convex_Icc _ _, ?_⟩
  intro x hx y hy a b ha hb hab
  exact hconcave_nonneg.2 hx.1 hy.1 ha hb hab

theorem p0PositiveEnergyProfileActual_endpoint_two :
    (248035 / 125000 : ℝ) ≤ p0PositiveEnergyProfileActual 0 := by
  unfold p0PositiveEnergyProfileActual
  have hfin₀ : P0.P0FiniteEnergyCondition P0.actualReferenceMeasures :=
    P0.p0ReferenceMeasures_finite_energy
      P0.p0ReferenceFiniteEnergyData_literal
  have hRe : MeasureTheory.Integrable (fun z : ℂ => z.re)
      P0.actualReferenceMeasures.eta := by
    apply MeasureTheory.Integrable.mono' (MeasureTheory.integrable_const (4 : ℝ))
      Complex.continuous_re.aestronglyMeasurable
    filter_upwards [P0.EnergyLowerBound.eta_ae_norm_le
      P0.actualReferenceMeasures] with z hz
    simpa [Real.norm_eq_abs] using
      (Complex.abs_re_le_norm z).trans hz
  have hnonempty : (p0PositiveEnergyValues 0).Nonempty := by
    refine ⟨p0PositiveEnergyValue 0 P0.actualReferenceMeasures, ?_⟩
    exact ⟨P0.actualReferenceMeasures, ⟨hfin₀, hRe⟩, rfl⟩
  refine le_csInf hnonempty ?_
  rintro e ⟨M, ⟨hM, _⟩, rfl⟩
  simp only [p0PositiveEnergyValue, zero_mul, add_zero]
  have hGamma : P0.alphaGamma ≤ P0.p0ExtendedEnergy M := by
    unfold P0.alphaGamma
    exact csInf_le P0.EnergyLowerBound.p0ExtendedEnergy_bddBelow
      (Set.mem_range_self M)
  have htop : ((397 / 200 : ℝ) : WithTop ℝ) <
      (P0.p0RegularizedEnergyValue M : WithTop ℝ) := by
    calc
      ((397 / 200 : ℝ) : WithTop ℝ) < P0.alphaGamma :=
        P0.AlphaUnconditional.alphaGamma_gt_397_200
      _ ≤ P0.p0ExtendedEnergy M := hGamma
      _ = (P0.p0RegularizedEnergyValue M : WithTop ℝ) :=
        P0.p0ExtendedEnergy_eq_value_of_finite M hM
  have hreal : (397 / 200 : ℝ) <
      P0.p0RegularizedEnergyValue M := by
    exact_mod_cast htop
  norm_num at hreal ⊢
  linarith

/-! ## Named q-frequency tail interface for the smoothing producer

The q-dependent finite envelope and its finite-to-infinite passage live in
`PositiveBaseFrequencyTail`.  This adapter is deliberately concrete: it
mentions the actual `qEInfinity`, `qE`, and `qFiniteQSum` definitions rather
than allowing a caller to choose an envelope equal to the desired
conclusion.  The remaining smoothing theorem below is the assembly
obligation that consumes this tail estimate.
-/

def p0Smoothing_qEInfinity_le_tail_hpoint (q m : ℕ) (h4 : 4 ∣ m) : Prop :=
  qEInfinity_le_tail_hpoint q m h4

theorem p0Smoothing_qEInfinity_le_tail
    (q m : ℕ) (hm : 0 < m) (hq : 2 ≤ q) (h4 : 4 ∣ m)
    (hpoint : p0Smoothing_qEInfinity_le_tail_hpoint q m h4) :
    qEInfinity q m h4 ≤
      (1 + (3 / 160 : ℝ) * (1 / 2 : ℝ) ^ m) * qE q m (20 * m) h4 := by
  exact Li2Lean.P0.PositiveBase.qEInfinity_le_tail q m hm hq h4 hpoint

/-! ## Named q-specific smoothing route inputs

The four leaves below are the migration boundary for the positive-base
producer.  Their statements mention the actual q-polynomial, q-envelope,
tail factor, and paper constants; no caller can supply a free envelope or a
conclusion-shaped field.  The assembly theorem keeps those leaves explicit so
the later contour, cell, and tube proofs can replace them independently. -/

namespace P0SmoothingRoute

theorem signed_coefficient_envelope_of_leaves
    (q : ℕ) (hq2 : 2 ≤ q) (hq11 : q ≤ 11)
    (m : ℕ) (hm8 : 8 ≤ m) (h4 : 4 ∣ m) :
    ‖Li2Lean.P0.PositiveBase.qGmBeta q m‖ ≤ qEInfinity q m h4 := by
  exact Li2Lean.P0.Env.norm_qGmBeta_le_qEInfinity q hq2 hq11 m hm8 h4

theorem tail_bound_of_leaves
    (q m : ℕ) (hm : 0 < m) (hq2 : 2 ≤ q) (h4 : 4 ∣ m) :
    qEInfinity q m h4 ≤
      (1 + (3 / 160 : ℝ) * (1 / 2 : ℝ) ^ m) * qE q m (20 * m) h4 := by
  exact _root_.Li2Lean.AllNAssembly.qEInfinity_le_tail q hq2 m hm h4

/-! The positive-base pinned-column factor has at most `exp (2m)` growth.
This is the numerical slack used by the v13 cutoff decomposition. -/
theorem pinned_log_ratio_le_two_m (q m : ℕ) (hq2 : 2 ≤ q) (hq11 : q ≤ 11)
    (S : Finset ℕ) (hSI : S ⊆ Li2Lean.P0.Iset m) :
    (Real.log (q : ℝ) / Li2Lean.P0.ell) ^ S.card ≤ Real.exp (2 * (m : ℝ)) := by
  have hell : 0 < Li2Lean.P0.ell := by
    rw [Li2Lean.P0.ell]
    exact Real.log_pos (by norm_num)
  have hqpos : (0 : ℝ) < (q : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt hq2)
  have hq16 : (q : ℝ) ≤ 16 := by
    exact_mod_cast (show q ≤ 16 by omega)
  have hlogq_le : Real.log (q : ℝ) ≤ Real.log (16 : ℝ) :=
    Real.log_le_log hqpos hq16
  have hlog16 : Real.log (16 : ℝ) = 4 * Real.log 2 := by
    calc
      Real.log (16 : ℝ) = Real.log ((2 : ℝ) ^ 4) := by norm_num
      _ = (4 : ℝ) * Real.log 2 := by rw [Real.log_pow]; norm_num
  have hratio_le : Real.log (q : ℝ) / Li2Lean.P0.ell ≤ 4 := by
    apply (div_le_iff₀ hell).2
    rw [Li2Lean.P0.ell]
    rw [hlog16] at hlogq_le
    nlinarith [hlogq_le]
  have h2leq : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
  have hlog2le : Real.log 2 ≤ Real.log (q : ℝ) :=
    Real.log_le_log (by norm_num) h2leq
  have hratio_ge : (1 : ℝ) ≤ Real.log (q : ℝ) / Li2Lean.P0.ell := by
    apply (le_div_iff₀ hell).2
    simpa [Li2Lean.P0.ell] using hlog2le
  have hexp1 : (2 : ℝ) < Real.exp 1 := Real.exp_one_gt_two
  have hmul : (2 : ℝ) * 2 ≤ Real.exp 1 * Real.exp 1 := by
    exact mul_le_mul hexp1.le hexp1.le (by norm_num) (by positivity)
  have hexp2eq : Real.exp (2 : ℝ) = Real.exp 1 * Real.exp 1 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
  have hexp2 : (4 : ℝ) ≤ Real.exp 2 := by
    calc
      (4 : ℝ) = 2 * 2 := by norm_num
      _ ≤ Real.exp 1 * Real.exp 1 := hmul
      _ = Real.exp 2 := hexp2eq.symm
  have hratio_exp : Real.log (q : ℝ) / Li2Lean.P0.ell ≤ Real.exp 2 :=
    hratio_le.trans hexp2
  have hratio_nonneg : 0 ≤ Real.log (q : ℝ) / Li2Lean.P0.ell :=
    (by linarith [hratio_ge])
  have hp1 :
      (Real.log (q : ℝ) / Li2Lean.P0.ell) ^ S.card ≤ (Real.exp 2) ^ S.card := by
    exact pow_le_pow_left₀ hratio_nonneg hratio_exp _
  have hcard : S.card ≤ m := by
    rw [← Li2Lean.P0.Iset_card m]
    exact Finset.card_le_card hSI
  have hexp2_one : (1 : ℝ) ≤ Real.exp 2 := by
    have h := Real.exp_le_exp.mpr (show (0 : ℝ) ≤ 2 by norm_num)
    simpa using h
  have hp2 : (Real.exp 2) ^ S.card ≤ (Real.exp 2) ^ m := by
    exact pow_le_pow_right₀ hexp2_one hcard
  have hexp_pow : (Real.exp 2) ^ m = Real.exp (2 * (m : ℝ)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  exact hp1.trans (hp2.trans_eq hexp_pow)

/- The finite-head cutoff and its tail-to-envelope aggregation follow v13
   `sec-frequency-tail.tex:709-713`: apply the pointwise head estimate to
   each tuple, pass through the finite q-envelope, and use the printed
   coefficient/count budget. -/
theorem cutoff_bound_of_leaves
    (q : ℕ) (hq2 : 2 ≤ q) (hq11 : q ≤ 11)
    (m : ℕ) (hm8 : 8 ≤ m) (h4 : 4 ∣ m) :
    qE q m (20 * m) h4 ≤
      Real.exp (-(p0PositiveEnergyProfileActual (positiveBaseParameter q)) *
          (m : ℝ) ^ 2 + 304 + 10 * (m : ℝ) * Real.log m +
        (Li2Lean.P0.Config.cStar + 2) * m + 1 / 3 +
        (m : ℝ) * (Real.log 39 + 1) +
        (m : ℝ) * (12783 / 10000)) := by
  have hlam_mem := Li2Lean.positiveBaseParameter_mem hq2 hq11
  have hlam0 : 0 ≤ Li2Lean.positiveBaseParameter q := hlam_mem.1
  have hlam11 : Li2Lean.positiveBaseParameter q ≤
      Real.log ((11 : ℝ) / 2) := hlam_mem.2
  have hpoint : ∀ (S : Finset ℕ) (hSI : S ⊆ Li2Lean.P0.Iset m)
      (r : Li2Lean.P0.FrequencyCutoff.IncreasingTuple (m / 2) m)
      (_hr : r ∈ Li2Lean.P0.FrequencyCutoff.cutoffTuples (m / 2) m (20 * m))
      (u : Fin (m - S.card) → ℝ),
      Li2Lean.P0.PositiveBase.qContourQValue q S h4 hSI r.val r.property.1
          (fun i => Li2Lean.p0EllipsePoint m (u i)) ≤
        Real.exp
          (-(p0PositiveEnergyProfileActual (positiveBaseParameter q)) *
              (m : ℝ) ^ 2 + 304 +
            10 * (m : ℝ) * Real.log m +
            (Li2Lean.P0.Config.cStar + 2) * m + 1 / 3) := by
    intro S hSI r hr u
    let C := Li2Lean.P0.Config.mkTupleConfiguration hm8 h4 S hSI r u
    have hfreq : ∀ a ∈ C.frequency, a ≤ 20 * C.m := by
      intro a ha
      change a ∈ Li2Lean.P0.FrequencyCutoff.tupleSet r at ha
      rcases (Li2Lean.P0.FrequencyCutoff.mem_tupleSet r a).mp ha with ⟨i, rfl⟩
      exact (Li2Lean.P0.FrequencyCutoff.mem_cutoffTuples r).mp hr i
    have hqnonneg :
        0 ≤ Li2Lean.P0.PositiveBase.qContourQValue q S h4 hSI
          r.val r.property.1 (fun i => Li2Lean.p0EllipsePoint m (u i)) :=
      Li2Lean.P0.PositiveBase.qContourQValue_nonneg q hq2 S h4 hSI
        r.val r.property.1 _
    by_cases hqzero :
        Li2Lean.P0.PositiveBase.qContourQValue q S h4 hSI
          r.val r.property.1 (fun i => Li2Lean.p0EllipsePoint m (u i)) = 0
    · rw [hqzero]
      exact (Real.exp_pos _).le
    have hqpos :
        0 < Li2Lean.P0.PositiveBase.qContourQValue q S h4 hSI
          r.val r.property.1 (fun i => Li2Lean.p0EllipsePoint m (u i)) :=
      lt_of_le_of_ne hqnonneg (Ne.symm hqzero)
    have hfactor := Li2Lean.P0.PositiveBase.qContourQValue_eq_mul_contourQValue
      q hq2 S h4 hSI r.val r.property.1
        (fun i => Li2Lean.p0EllipsePoint m (u i))
    have hcontour_nonneg :
        0 ≤ Li2Lean.P0.contourQValue S h4 hSI r.val r.property.1
          (fun i => Li2Lean.p0EllipsePoint m (u i)) := by
      have htwo := Li2Lean.P0.PositiveBase.qContourQValue_nonneg
        2 (by norm_num) S h4 hSI r.val r.property.1
        (fun i => Li2Lean.p0EllipsePoint m (u i))
      rw [Li2Lean.P0.PositiveBase.qContourQValue_two S h4 hSI
        r.val r.property.1 (fun i => Li2Lean.p0EllipsePoint m (u i))] at htwo
      exact htwo
    have hcontour_ne :
        Li2Lean.P0.contourQValue S h4 hSI r.val r.property.1
          (fun i => Li2Lean.p0EllipsePoint m (u i)) ≠ 0 := by
      intro hz
      apply hqzero
      rw [hfactor, hz]
      ring
    have hcontour_pos :
        0 < Li2Lean.P0.contourQValue S h4 hSI r.val r.property.1
          (fun i => Li2Lean.p0EllipsePoint m (u i)) :=
      lt_of_le_of_ne hcontour_nonneg (Ne.symm hcontour_ne)
    have hweight_pos : 0 < Li2Lean.P0.Config.literalConfigQWeight C := by
      change 0 < Li2Lean.P0.Config.literalConfigQWeight
        (Li2Lean.P0.Config.mkTupleConfiguration hm8 h4 S hSI r u)
      rw [Li2Lean.P0.Config.literalConfigQWeight_mkTuple_eq hm8 h4 S hSI r u]
      exact hcontour_pos
    have hcell := Li2Lean.P0.CellBound.configWitnessCellBound C hfreq hweight_pos
    have hshift := Li2Lean.P0.CoefficientAssembly.configTubeWitness_affine_shift_le C hfreq
    have hsumR :
        (∑ a ∈ C.frequency, (a : ℝ)) =
          ∑ i : Fin m, (r.val i : ℝ) := by
      change (∑ a ∈ Li2Lean.P0.FrequencyCutoff.tupleSet r, (a : ℝ)) = _
      classical
      change Finset.sum (Finset.image r.val Finset.univ) (fun a => (a : ℝ)) = _
      rw [Finset.sum_image]
      intro i hi j hj hij
      exact r.property.1.injective hij
    have hsumZ :
        (∑ i : Fin (m - S.card),
            (Li2Lean.p0EllipsePoint m (u i)).re) =
          (C.m : ℝ) * (∑ a : Fin C.contourCount, (C.contour a).re) := by
      dsimp [C, Li2Lean.P0.Config.mkTupleConfiguration]
      simp only [Li2Lean.P0.Config.baseEllipse, Li2Lean.p0EllipsePoint,
        Nat.cast_one, Complex.ofReal_one, one_mul]
      simp [Complex.mul_re, Finset.mul_sum]
      rfl
    have hD :
        (∑ a ∈ S, (a : ℝ)) +
            (∑ i : Fin (m - S.card),
              (Li2Lean.p0EllipsePoint m (u i)).re) -
            (∑ i : Fin m, (r.val i : ℝ)) ≤
          -(m : ℝ) ^ 2 *
            ((∫ t : ℝ, t ∂Li2Lean.P0.Config.frequencyMeasure C.m C.frequency) -
              ∫ z : ℂ, z.re ∂(Li2Lean.P0.CoefficientAssembly.configTubeWitness C).eta) := by
      rw [hsumZ, ← hsumR]
      simpa [C, Li2Lean.P0.Config.mkTupleConfiguration,
        Li2Lean.P0.CoefficientAssembly.configTubeWitness,
        Complex.mul_re, Finset.mul_sum] using hshift
    have hdelta : 0 < (1 / (m : ℝ) ^ 2) := by positivity
    have hdelta_max : (1 / (m : ℝ) ^ 2) ≤ Li2Lean.P0.tubeRadiusMax := by
      unfold Li2Lean.P0.tubeRadiusMax
      have hm' : (8 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm8
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    have hfin := Li2Lean.P0.CoefficientAssembly.configWitnessFiniteEnergy C hfreq
    have hprofile := p0TubePositiveEnergy_ge_profile_actual
      (lambda := Li2Lean.positiveBaseParameter q)
      (δ := 1 / (m : ℝ) ^ 2) hlam0 hlam11 hdelta hdelta_max
      (Li2Lean.P0.CoefficientAssembly.configTubeWitness C) hfin
    have henergy :
        -(m : ℝ) ^ 2 *
            Li2Lean.P0.p0TubeRegularizedEnergyValue
              (Li2Lean.P0.CoefficientAssembly.configTubeWitness C) +
          Li2Lean.positiveBaseParameter q *
            ((∑ a ∈ S, (a : ℝ)) +
              (∑ i : Fin (m - S.card),
                (Li2Lean.p0EllipsePoint m (u i)).re) -
              (∑ i : Fin m, (r.val i : ℝ))) ≤
        -(p0PositiveEnergyProfileActual (Li2Lean.positiveBaseParameter q)) *
            (m : ℝ) ^ 2 + 304 := by
      have hmul := mul_le_mul_of_nonneg_left hD hlam0
      have hprof := hprofile
      unfold p0TubePositiveEnergyValue at hprof
      change p0PositiveEnergyProfileActual (Li2Lean.positiveBaseParameter q) -
          304 * (1 / (m : ℝ) ^ 2) ≤
        Li2Lean.P0.p0TubeRegularizedEnergyValue
            (Li2Lean.P0.CoefficientAssembly.configTubeWitness C) +
          Li2Lean.positiveBaseParameter q *
            ((∫ t : ℝ, t ∂Li2Lean.P0.Config.frequencyMeasure C.m C.frequency) -
              ∫ z : ℂ, z.re ∂
                (Li2Lean.P0.CoefficientAssembly.configTubeWitness C).eta) at hprof
      have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
      have hm2 : (m : ℝ) ^ 2 * (1 / (m : ℝ) ^ 2) = 1 := by
        field_simp
      have hlam_eq : Li2Lean.positiveBaseParameter q =
          Li2Lean.P0.PositiveBase.logShift (q : ℤ) := by
        rfl
      rw [hlam_eq] at hmul
      have hmul' :
          Li2Lean.P0.PositiveBase.logShift (q : ℤ) *
              ((∑ a ∈ S, (a : ℝ)) +
                (∑ i : Fin (m - S.card),
                  (Li2Lean.p0EllipsePoint m (u i)).re) -
                (∑ i : Fin m, (r.val i : ℝ))) ≤
            Li2Lean.P0.PositiveBase.logShift (q : ℤ) *
              (-(m : ℝ) ^ 2 *
                ((∫ t : ℝ, t ∂
                    (Li2Lean.P0.CoefficientAssembly.configTubeWitness C).mu) -
                  ∫ z : ℂ, z.re ∂
                    (Li2Lean.P0.CoefficientAssembly.configTubeWitness C).eta)) := by
        simpa [Li2Lean.P0.CoefficientAssembly.configTubeWitness,
          C, Li2Lean.P0.Config.mkTupleConfiguration] using hmul
      nlinarith
    have hratio := pinned_log_ratio_le_two_m q m hq2 hq11 S hSI
    have hcontour_shift :
        Li2Lean.P0.contourQValue S h4 hSI r.val r.property.1
            (fun i => Li2Lean.p0EllipsePoint m (u i)) *
          Real.exp (Li2Lean.P0.PositiveBase.logShift (q : ℤ) *
            ((∑ a ∈ S, (a : ℝ)) +
              (∑ i : Fin (m - S.card),
                (Li2Lean.p0EllipsePoint m (u i)).re) -
              (∑ i : Fin m, (r.val i : ℝ)))) ≤
        Real.exp (-(p0PositiveEnergyProfileActual
              (Li2Lean.positiveBaseParameter q)) * (m : ℝ) ^ 2 +
            304 + 10 * (m : ℝ) * Real.log m +
            Li2Lean.P0.Config.cStar * (m : ℝ) + 1 / 3) := by
      rw [← Real.exp_log hcontour_pos, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hcell' := hcell
      rw [Li2Lean.P0.Config.literalConfigQWeight_mkTuple_eq hm8 h4 S hSI r u] at hcell'
      change Real.log (Li2Lean.P0.contourQValue S h4 hSI r.val r.property.1
          (fun i => Li2Lean.p0EllipsePoint m (u i))) ≤
        -(m : ℝ) ^ 2 * Li2Lean.P0.p0TubeRegularizedEnergyValue
            (Li2Lean.P0.CoefficientAssembly.configTubeWitness C) +
          10 * (m : ℝ) * Real.log m + Li2Lean.P0.Config.cStar * (m : ℝ) + 1 / 3 at hcell'
      have hlam_eq : Li2Lean.positiveBaseParameter q =
          Li2Lean.P0.PositiveBase.logShift (q : ℤ) := by
        rfl
      rw [← hlam_eq]
      nlinarith [henergy]
    rw [hfactor]
    have hell : 0 < Li2Lean.P0.ell := by
      rw [Li2Lean.P0.ell]
      exact Real.log_pos (by norm_num)
    have hqlog : 0 ≤ Real.log (q : ℝ) := by
      apply Real.log_nonneg
      have hq1 : 1 ≤ q := le_trans (by norm_num) hq2
      exact_mod_cast hq1
    have hprod := mul_le_mul hcontour_shift hratio
      (pow_nonneg (div_nonneg hqlog hell.le) _)
      (by exact (Real.exp_pos _).le : 0 ≤ Real.exp (-(p0PositiveEnergyProfileActual
        (Li2Lean.positiveBaseParameter q)) * (m : ℝ) ^ 2 + 304 +
        10 * (m : ℝ) * Real.log m + Li2Lean.P0.Config.cStar * (m : ℝ) + 1 / 3))
    calc
      _ = (Li2Lean.P0.contourQValue S h4 hSI r.val r.property.1
          (fun i => Li2Lean.p0EllipsePoint m (u i)) *
          Real.exp (Li2Lean.P0.PositiveBase.logShift (q : ℤ) *
            ((∑ a ∈ S, (a : ℝ)) +
              (∑ i : Fin (m - S.card),
                (Li2Lean.p0EllipsePoint m (u i)).re) -
              (∑ i : Fin m, (r.val i : ℝ)))) *
          (Real.log (q : ℝ) / Li2Lean.P0.ell) ^ S.card) := by ring
      _ ≤ Real.exp (-(p0PositiveEnergyProfileActual
              (Li2Lean.positiveBaseParameter q)) * (m : ℝ) ^ 2 + 304 +
            10 * (m : ℝ) * Real.log m +
            Li2Lean.P0.Config.cStar * (m : ℝ) + 1 / 3) *
          Real.exp (2 * (m : ℝ)) := hprod
      _ = Real.exp (-(p0PositiveEnergyProfileActual
              (Li2Lean.positiveBaseParameter q)) * (m : ℝ) ^ 2 + 304 +
            10 * (m : ℝ) * Real.log m +
            (Li2Lean.P0.Config.cStar + 2) * (m : ℝ) + 1 / 3) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hE := Li2Lean.P0.PositiveBase.qE_twentyM_le_of_head
    (q := q) (m := m) hq2 hm8 h4 hpoint
  have hcount := Li2Lean.P0.CoefficientAssembly.two_pow_mul_headTupleCount_le h4
  have hprod :
      (2 : ℝ) ^ m *
          ((Li2Lean.P0.CoefficientAssembly.headTupleCount m : ℝ) *
            Real.exp (-(p0PositiveEnergyProfileActual (positiveBaseParameter q)) *
                (m : ℝ) ^ 2 + 304 + 10 * (m : ℝ) * Real.log m +
              (Li2Lean.P0.Config.cStar + 2) * m + 1 / 3) *
              Real.exp ((m : ℝ) * (12783 / 10000))) ≤
        Real.exp ((m : ℝ) * (Real.log 39 + 1)) *
          (Real.exp (-(p0PositiveEnergyProfileActual (positiveBaseParameter q)) *
                (m : ℝ) ^ 2 + 304 + 10 * (m : ℝ) * Real.log m +
              (Li2Lean.P0.Config.cStar + 2) * m + 1 / 3) *
              Real.exp ((m : ℝ) * (12783 / 10000))) := by
    calc
      _ = ((2 : ℝ) ^ m *
            (Li2Lean.P0.CoefficientAssembly.headTupleCount m : ℝ)) *
            (Real.exp (-(p0PositiveEnergyProfileActual (positiveBaseParameter q)) *
                (m : ℝ) ^ 2 + 304 + 10 * (m : ℝ) * Real.log m +
              (Li2Lean.P0.Config.cStar + 2) * m + 1 / 3) *
              Real.exp ((m : ℝ) * (12783 / 10000))) := by ring_nf
      _ ≤ _ := mul_le_mul_of_nonneg_right hcount (by positivity)
  calc
    qE q m (20 * m) h4 ≤
        Real.exp ((m : ℝ) * (Real.log 39 + 1)) *
          (Real.exp (-(p0PositiveEnergyProfileActual (positiveBaseParameter q)) *
                (m : ℝ) ^ 2 + 304 + 10 * (m : ℝ) * Real.log m +
              (Li2Lean.P0.Config.cStar + 2) * m + 1 / 3) *
              Real.exp ((m : ℝ) * (12783 / 10000))) := hE.trans hprod
    _ ≤ Real.exp (-(p0PositiveEnergyProfileActual (positiveBaseParameter q)) *
          (m : ℝ) ^ 2 + 304 + 10 * (m : ℝ) * Real.log m +
        (Li2Lean.P0.Config.cStar + 2) * m + 1 / 3 +
        (m : ℝ) * (Real.log 39 + 1) +
        (m : ℝ) * (12783 / 10000)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      simp
      linarith

theorem exponent_budget_of_leaves (alpha : ℝ) (m : ℕ) (hm8 : 8 ≤ m) :
    -alpha * (m : ℝ) ^ 2 + 304 + 10 * (m : ℝ) * Real.log m +
        (Li2Lean.P0.Config.cStar + 2) * m + 1 / 3 +
        (m : ℝ) * (Real.log 39 + 1) +
        (m : ℝ) * (12783 / 10000) + 1 / 3 ≤
      -alpha * (m : ℝ) ^ 2 + 10 * (m : ℝ) * Real.log m +
        58 * m + 301 + 40 * Real.log m := by
  have hlin := Li2Lean.P0.CoefficientAssembly.q_cell_linear_budget_lt_58
  have hconst := Li2Lean.P0.CoefficientAssembly.q_smoothing_constant_budget hm8
  have hm : (0 : ℝ) ≤ (m : ℝ) := by positivity
  nlinarith

theorem smoothing_of_inputs
    (q : ℕ) (hq : InRange (q : ℤ)) (h3 : 3 ≤ q)
    (hE : ∀ m : ℕ, 8 ≤ m → ∀ h4 : 4 ∣ m,
      ‖Li2Lean.P0.PositiveBase.qGmBeta q m‖ ≤ qEInfinity q m h4)
    (hT : ∀ m : ℕ, 0 < m → ∀ h4 : 4 ∣ m,
      qEInfinity q m h4 ≤
        (1 + (3 / 160 : ℝ) * (1 / 2 : ℝ) ^ m) * qE q m (20 * m) h4)
    (hS : ∀ m : ℕ, 8 ≤ m → ∀ h4 : 4 ∣ m,
      qE q m (20 * m) h4 ≤
        Real.exp (-(p0PositiveEnergyProfileActual (positiveBaseParameter q)) *
            (m : ℝ) ^ 2 + 304 + 10 * (m : ℝ) * Real.log m +
          (Li2Lean.P0.Config.cStar + 2) * m + 1 / 3 +
          (m : ℝ) * (Real.log 39 + 1) +
          (m : ℝ) * (12783 / 10000)))
    (hB : ∀ alpha : ℝ, ∀ m : ℕ, 8 ≤ m →
      -alpha * (m : ℝ) ^ 2 + 304 + 10 * (m : ℝ) * Real.log m +
          (Li2Lean.P0.Config.cStar + 2) * m + 1 / 3 +
          (m : ℝ) * (Real.log 39 + 1) +
          (m : ℝ) * (12783 / 10000) + 1 / 3 ≤
        -alpha * (m : ℝ) ^ 2 + 10 * (m : ℝ) * Real.log m +
          58 * m + 301 + 40 * Real.log m) :
    P0PaperAnalyticEstimate
      (p0PositiveEnergyProfileActual (positiveBaseParameter q)) (q : ℤ)
      (family (q : ℤ) hq) := by
  intro m hm8 h4
  have hEval :
      ‖Li2Lean.P0.PositiveBase.qGmBeta q m‖ =
        |((family (q : ℤ) hq).G m).eval (li2InvValue (q : ℤ))| := by
    rw [family]
    unfold Li2Lean.P0.PositiveBase.qGmBeta
    rw [← Li2Lean.P0.ofReal_eval_map_rat]
    simp
  rw [← hEval]
  have henv := hE m hm8 h4
  have htail := hT m (by omega) h4
  have hsum := hS m hm8 h4
  have hfactor : 0 ≤ (1 + (3 / 160 : ℝ) * (1 / 2 : ℝ) ^ m) := by
    positivity
  have hmul :
      (1 + (3 / 160 : ℝ) * (1 / 2 : ℝ) ^ m) * qE q m (20 * m) h4 ≤
        (1 + (3 / 160 : ℝ) * (1 / 2 : ℝ) ^ m) *
          Real.exp (-(p0PositiveEnergyProfileActual (positiveBaseParameter q)) *
            (m : ℝ) ^ 2 + 304 + 10 * (m : ℝ) * Real.log m +
            (Li2Lean.P0.Config.cStar + 2) * m + 1 / 3 +
            (m : ℝ) * (Real.log 39 + 1) +
            (m : ℝ) * (12783 / 10000)) :=
    mul_le_mul_of_nonneg_left hsum hfactor
  have htail_exp :=
    Li2Lean.P0.FrequencyLimit.actualFrequencyTailFactor_mul_exp_le m
      (-(p0PositiveEnergyProfileActual (positiveBaseParameter q)) *
        (m : ℝ) ^ 2 + 304 + 10 * (m : ℝ) * Real.log m +
        (Li2Lean.P0.Config.cStar + 2) * m + 1 / 3 +
        (m : ℝ) * (Real.log 39 + 1) +
        (m : ℝ) * (12783 / 10000))
  have hbudget := hB (p0PositiveEnergyProfileActual (positiveBaseParameter q)) m hm8
  exact henv.trans (htail.trans (hmul.trans (by
    simpa [Li2Lean.P0.FrequencyLimit.actualFrequencyTailFactor] using
      (htail_exp.trans (Real.exp_le_exp.mpr hbudget)))))

end P0SmoothingRoute

/-! q = 11 endpoint route input.  The record contains the actual reference
measure and shifted-dual inequalities; it does not contain the endpoint
conclusion itself. -/
structure Q11EndpointRouteInput where
  /-- Documented weaker constant used by the shifted-dual route. -/
  a11 : ℝ
  a11_eq : a11 = 153 / 200
  M₀ : P0.P0AdmissibleMeasures
  dom₀ : p0PositiveEnergyDomain M₀
  qLog_lower : (-635537 / 1000000 : ℝ) ≤
    P0.L6Variations.l6QLog M₀.eta (P0.p0FrequencyMeasure M₀)
  caps : ∀ M : P0.P0AdmissibleMeasures, p0PositiveEnergyDomain M →
    ∃ _hcross : P0.L6Admissible.P0L6CrossEnergy M M₀,
      (-3359 / 500 : ℝ) - 1 / 1000000 ≤
        ∫ z, (P0.p0DualWeta M₀ z - Real.log ((11 : ℝ) / 2) * z.re) ∂M.eta ∧
      (1217 / 200 : ℝ) - 1069189 / 1000000 ≤
        ∫ t, (P0.p0DualWmu M₀ t + Real.log ((11 : ℝ) / 2) * t) ∂M.mu

theorem q11_endpoint_of_input (I : Q11EndpointRouteInput) :
    (77597 / 100000 : ℝ) ≤
      p0PositiveEnergyProfileActual (Real.log ((11 : ℝ) / 2)) := by
  have hprofile :
      (9 / 2 : ℝ) - 2 * P0.ell +
          P0.L6Variations.l6QLog I.M₀.eta
            (P0.p0FrequencyMeasure I.M₀) +
          (-3359 / 500 : ℝ) + (1217 / 200 : ℝ) -
          (1 / 1000000 : ℝ) - (1069189 / 1000000 : ℝ) ≤
        p0PositiveEnergyProfileActual (Real.log ((11 : ℝ) / 2)) := by
    unfold p0PositiveEnergyProfileActual
    refine le_csInf ⟨_, I.M₀, I.dom₀, rfl⟩ ?_
    rintro e ⟨M, hM, rfl⟩
    obtain ⟨hcross, hEta, hMu⟩ := I.caps M hM
    have hWeta := P0.p0DualWeta_integrable M I.M₀ hM.1 hcross
    have hWmu := P0.p0DualWmu_integrable M I.M₀ hM.1 hcross
    rw [integral_sub hWeta (hM.2.const_mul _), integral_const_mul] at hEta
    rw [integral_add hWmu (hM.1.1.const_mul _), integral_const_mul] at hMu
    have hbase := P0.p0Dual_regularizedEnergy_ge_of_caps M I.M₀
      hM.1 I.dom₀.1 hcross
      (-3359 / 500 : ℝ) (1217 / 200 : ℝ)
      (1 / 1000000 - Real.log ((11 : ℝ) / 2) *
        ∫ z : ℂ, z.re ∂M.eta)
      (1069189 / 1000000 + Real.log ((11 : ℝ) / 2) *
        ∫ t : ℝ, t ∂M.mu)
      (by linarith) (by linarith)
    unfold p0PositiveEnergyValue
    linarith
  have hl2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  simp only [P0.ell] at hprofile
  norm_num at hl2
  linarith [I.qLog_lower]

theorem p0PositiveEnergyProfileActual_smoothing
    (q : ℕ) (hq : InRange (q : ℤ)) (h3 : 3 ≤ q) :
    P0PaperAnalyticEstimate
      (p0PositiveEnergyProfileActual (positiveBaseParameter q)) (q : ℤ)
      (family (q : ℤ) hq) := by
  exact P0SmoothingRoute.smoothing_of_inputs q hq h3
    (fun m hm h4 => P0SmoothingRoute.signed_coefficient_envelope_of_leaves q
      (by omega) (by rcases hq with ⟨_, hhi⟩; omega) m hm h4)
    (fun m hm h4 => P0SmoothingRoute.tail_bound_of_leaves q m hm (by omega) h4)
    (fun m hm h4 => P0SmoothingRoute.cutoff_bound_of_leaves q
      (by omega) (by rcases hq with ⟨_, hhi⟩; omega) m hm h4)
    (fun alpha m hm => P0SmoothingRoute.exponent_budget_of_leaves alpha m hm)

/-- Interpolation step: B2 chord lower bound + monotonicity in the rate. -/
theorem P0PositiveEnergyProfile.chord_estimate (P : P0PositiveEnergyProfile)
    (q : ℕ) (hq : InRange (q : ℤ)) (h3 : 3 ≤ q) :
    P0PaperAnalyticEstimate (p0PositiveChord q) (q : ℤ) (family (q : ℤ) hq) := by
  have h11 : q ≤ 11 := by
    rcases hq with ⟨_, hhi⟩
    omega
  exact (P.smoothing q hq h3).mono
    (positiveBaseEndpointChord P.concave P.endpoint_two P.endpoint_eleven
      (by omega) h11)

/-- Generic positive-base endpoint certificate. This is
`q11EndpointCertificate_of_inputs` (Q11EndpointCertificate.lean:9-85) with
`11` replaced by `q`, the integerizer rate made a parameter, and the
paper constants `cLog = 50`, `cLinear = 58`, `cConst = 301`
(`10 m log m + 40 log m ≤ 50 m log m` for `m ≥ 1`). -/
theorem positiveEndpointCertificate {q : ℤ} (hq : InRange q) {alpha rate : ℝ}
    (hA : P0PaperAnalyticEstimate alpha q (family q hq))
    (hI : P0IntegerizerBoundAt (family q hq) rate)
    (hRate : rate < alpha)
    (hN : P0NonvanishingStatement (family q hq)) :
    Nonempty (EndpointCertificate (li2InvValue q)) := by
  obtain ⟨D, hDpos, hdeg, hpoly, hrate⟩ := hI
  obtain ⟨M, p, hMpos, hM4, hp, hp10, hNv⟩ := hN
  have hpone : 1 < p := hp.one_lt
  have hidx_pos : ∀ k : ℕ, 0 < M * p ^ (k + 1) := by
    intro k
    positivity
  have hidx4 : ∀ k : ℕ, 4 ∣ M * p ^ (k + 1) := by
    intro k
    exact dvd_mul_of_dvd_left hM4 _
  have hidx8 : ∀ k : ℕ, 8 ≤ M * p ^ (k + 1) := by
    intro k
    have hMge : 4 ≤ M := by omega
    have hpge : 11 ≤ p := by omega
    have hpow1 : 1 ≤ p ^ k := Nat.one_le_pow _ _ (by omega)
    have hpow_ge : p ≤ p ^ (k + 1) := by
      calc
        p = p * 1 := by simp
        _ ≤ p * p ^ k := Nat.mul_le_mul_left p hpow1
        _ = p ^ (k + 1) := by
          rw [pow_succ]
          exact Nat.mul_comm _ _
    have hsmall : 8 ≤ 4 * p := by omega
    have hprod : 4 * p ≤ M * p ^ (k + 1) :=
      Nat.mul_le_mul hMge hpow_ge
    exact le_trans hsmall hprod
  have hmono : StrictMono (fun k : ℕ => M * p ^ (k + 1)) := by
    intro i j hij
    have hpow : p ^ (i + 1) < p ^ (j + 1) := by
      apply Nat.pow_lt_pow_right hpone
      omega
    exact (Nat.mul_lt_mul_left hMpos).2 hpow
  have hrate' : ∀ ε : ℝ, 0 < ε → ∃ k₀, ∀ k, k₀ ≤ k →
      Real.log (D (M * p ^ (k + 1)) : ℝ) /
          ((M * p ^ (k + 1) : ℕ) : ℝ) ^ 2 ≤ rate + ε := by
    intro ε hε
    obtain ⟨K, hK⟩ := hrate ε hε
    refine ⟨K, fun k hk => ?_⟩
    have hkpow : k + 1 ≤ p ^ (k + 1) := (Nat.lt_pow_self hpone).le
    have hM1 : 1 ≤ M := by omega
    have hprod : p ^ (k + 1) ≤ M * p ^ (k + 1) := by
      simpa using Nat.mul_le_mul_right (p ^ (k + 1)) hM1
    have hidx : K ≤ M * p ^ (k + 1) := by omega
    exact hK (M * p ^ (k + 1)) hidx (hidx_pos k) (hidx4 k)
  have hnonzero : ∀ r : ℚ, ∃ k₀, ∀ k, k₀ ≤ k →
      ((family q hq).G (M * p ^ (k + 1))).eval (r : ℝ) ≠ 0 := by
    intro r
    obtain ⟨K, hK⟩ := hNv r
    exact ⟨K, fun k hk => hK (k + 1) (by omega)⟩
  refine ⟨{
    index := fun k => M * p ^ (k + 1)
    G := (family q hq).G
    D := D
    alpha := alpha
    tau := rate
    cLog := 50
    cLinear := 58
    cConst := 301
    index_strictMono := hmono
    index_multiple_four := hidx4
    index_ge_eight := hidx8
    alpha_gt_tau := hRate
    degree_bound := fun k => hdeg _ (hidx_pos k) (hidx4 k)
    integerizer_pos := fun k => hDpos _ (hidx_pos k) (hidx4 k)
    integerizer_poly := fun k => hpoly _ (hidx_pos k) (hidx4 k)
    analytic_bound := fun k => by
      refine (hA _ (hidx8 k) (hidx4 k)).trans (Real.exp_le_exp.mpr ?_)
      have hx1 : (1 : ℝ) ≤ ((M * p ^ (k + 1) : ℕ) : ℝ) := by
        exact_mod_cast (show 1 ≤ M * p ^ (k + 1) by have := hidx8 k; omega)
      have hlog := Real.log_nonneg hx1
      nlinarith [mul_nonneg (sub_nonneg.mpr hx1) hlog]   -- verified side condition
    integerizer_rate := hrate'
    nonzero_at_rationals := hnonzero }⟩

/-- General-base Frobenius tower (merged consumer `p0FrobeniusTower_nonvanishing`,
P0/Nonvanishing.lean:270). -/
theorem p0Nonvanishing_of_tower {F : P0Family}
    (h : ∃ M p : ℕ, Nonempty (P0FrobeniusTowerCertificate F M p)) :
    P0NonvanishingStatement F := by
  obtain ⟨M, p, ⟨c⟩⟩ := h
  exact p0FrobeniusTower_nonvanishing c

/-- Positive range 2..11: n = 2 from the frozen 1/2 theorem, 3..11 from the
profile (interpolation), per-q integerizer, per-q rate margin, per-q tower. -/
theorem p0_positive_range_of_producers
    (P : P0PositiveEnergyProfile)
    (rate : ℕ → ℝ)
    (hI : ∀ (q : ℕ) (hq : InRange (q : ℤ)), 3 ≤ q →
      P0IntegerizerBoundAt (family (q : ℤ) hq) (rate q))
    (hMargin : ∀ q : ℕ, 3 ≤ q → q ≤ 11 → rate q < p0PositiveChord q)
    (hN : ∀ (q : ℕ) (hq : InRange (q : ℤ)), 3 ≤ q →
      P0NonvanishingStatement (family (q : ℤ) hq)) :
    ∀ n : ℤ, (2 : ℤ) ≤ n → n ≤ 11 → n ≠ 0 → Irrational (li2InvValue n) := by
  intro n hlo hhi _
  by_cases h2 : n = 2
  · subst h2
    exact li2_half_irrational_unconditional          -- kernel-checked endpoint theorem
  · obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : (0 : ℤ) ≤ n)
    have h3 : 3 ≤ q := by omega
    have h11 : q ≤ 11 := by omega
    have hq : InRange (q : ℤ) := by
      unfold InRange
      omega
    obtain ⟨c⟩ := positiveEndpointCertificate hq (P.chord_estimate q hq h3)
      (hI q hq h3) (hMargin q h3 h11) (hN q hq h3)
    exact l1_endpoint_criterion _ c

/-! ## B.2 Signed V range, -7 ≤ n ≤ -2 -/

/-- The literal V determinant `G_m(T; -q)` of v13 v-arithmetic.tex:24-32,
indexed by `m = 4n` (`Li2Lean.V.vPolynomial n a` is `G_{4n}`). -/
def vFamilyG (q : ℕ) (m : ℕ) : Polynomial ℝ :=
  (Li2Lean.V.vPolynomial (m / 4) (-(q : ℤ))).map (algebraMap ℚ ℝ)

/-- Replacement for the false `TopDownB3SmoothingPrebound` (Sk:129-143):
the certificate is for the ACTUAL `g = log|G_m(Li2(-1/q); -q)|`, with
`q, m, alpha, sigma` pinned. The B3 certificate alone, with `alpha` free, is
vacuous (take `alpha` very negative); pinning `alpha` to the table value and
pairing it with the integerizer margin is what gives content. -/
def B3PreboundActual (q : ℕ) (alphaQ sigmaQ : ℝ) : Prop :=
  ∀ m : ℕ, 64 ≤ m → 4 ∣ m →
    (vFamilyG q m).eval (li2InvValue (-(q : ℤ))) ≠ 0 →
    ∃ c : B3.AllMSmoothingCertificate
        (Real.log |(vFamilyG q m).eval (li2InvValue (-(q : ℤ)))|),
      c.q = q ∧ c.m = m ∧ alphaQ ≤ c.alpha ∧ c.sigma ≤ sigmaQ

/-- v13 `eq:v-allm-bound` from the merged `B3.all_m_log_bound_of_certificate`. -/
theorem vAnalytic_of_b3Prebound {q : ℕ} {alphaQ sigmaQ : ℝ}
    (h : B3PreboundActual q alphaQ sigmaQ) :
    ∀ m : ℕ, 64 ≤ m → 4 ∣ m →
      |(vFamilyG q m).eval (li2InvValue (-(q : ℤ)))| ≤
        Real.exp (-alphaQ * (m : ℝ) ^ 2 +
          (10 + 3 * sigmaQ) * (m : ℝ) * Real.log (m : ℝ)) := by
  intro m hm h4
  apply abs_le_exp_of_log_abs_le
  intro hx
  obtain ⟨c, _, hcm, hca, hcs⟩ := h m hm h4 hx
  have hb := B3.all_m_log_bound_of_certificate c
  rw [hcm] at hb
  have hmR : (64 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hlog : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg (by linarith)
  have hmlog : 0 ≤ (m : ℝ) * Real.log (m : ℝ) :=
    mul_nonneg (by positivity) hlog
  have halpha : -c.alpha * (m : ℝ) ^ 2 ≤ -alphaQ * (m : ℝ) ^ 2 := by
    have hsq : 0 ≤ (m : ℝ) ^ 2 := sq_nonneg _
    nlinarith
  have hcoeff : 10 + 3 * c.sigma ≤ 10 + 3 * sigmaQ := by nlinarith
  have hsigma := mul_le_mul_of_nonneg_right hcoeff hmlog
  nlinarith [hb, halpha, hsigma]

/-- All fixed-base signed-V inputs, on the literal V family. -/
structure SignedVEndpointInputs (q : ℕ) where
  alpha : ℝ
  tau : ℝ
  C : ℝ
  analytic : ∀ m : ℕ, 64 ≤ m → 4 ∣ m →
    |(vFamilyG q m).eval (li2InvValue (-(q : ℤ)))| ≤
      Real.exp (-alpha * (m : ℝ) ^ 2 + C * (m : ℝ) * Real.log (m : ℝ))
  D : ℕ → ℚ
  degree : ∀ m, 0 < m → 4 ∣ m → (vFamilyG q m).natDegree ≤ m
  integerizer_pos : ∀ m, 0 < m → 4 ∣ m → 0 < D m
  integerizer_poly : ∀ m, 0 < m → 4 ∣ m → ∃ P : Polynomial ℤ,
    P.map (Int.castRingHom ℝ) = Polynomial.C (D m : ℝ) * vFamilyG q m
  integerizer_rate : ∀ ε : ℝ, 0 < ε → ∃ M, ∀ m, M ≤ m → 0 < m → 4 ∣ m →
    Real.log (D m : ℝ) / (m : ℝ) ^ 2 ≤ tau + ε
  rate_margin : tau < alpha
  towerM : ℕ
  towerP : ℕ
  towerM_pos : 0 < towerM
  towerM_four : 4 ∣ towerM
  towerP_prime : Nat.Prime towerP
  nonvanishing : ∀ r : ℚ, ∃ k₀, ∀ k, k₀ ≤ k →
    (vFamilyG q (towerM * towerP ^ k)).eval (r : ℝ) ≠ 0

/-- Constructor from the split producers (B3 prebound, integerizer, seed
prime, Frobenius transport). Paper tower: `M = 4`, `p_r ∈ {11,11,23,11,17,17}`. -/
def SignedVEndpointInputs.ofParts {q : ℕ} {alphaQ sigmaQ tauQ : ℝ}
    (hPre : B3PreboundActual q alphaQ sigmaQ)
    (D : ℕ → ℚ)
    (hdeg : ∀ m, 0 < m → 4 ∣ m → (vFamilyG q m).natDegree ≤ m)
    (hpos : ∀ m, 0 < m → 4 ∣ m → 0 < D m)
    (hpoly : ∀ m, 0 < m → 4 ∣ m → ∃ P : Polynomial ℤ,
      P.map (Int.castRingHom ℝ) = Polynomial.C (D m : ℝ) * vFamilyG q m)
    (hrate : ∀ ε : ℝ, 0 < ε → ∃ M, ∀ m, M ≤ m → 0 < m → 4 ∣ m →
      Real.log (D m : ℝ) / (m : ℝ) ^ 2 ≤ tauQ + ε)
    (hmargin : tauQ < alphaQ)
    (p : ℕ) (hp : Nat.Prime p)
    (hNv : ∀ r : ℚ, ∃ k₀, ∀ k, k₀ ≤ k →
      (vFamilyG q (4 * p ^ k)).eval (r : ℝ) ≠ 0) :
    SignedVEndpointInputs q where
  alpha := alphaQ
  tau := tauQ
  C := 10 + 3 * sigmaQ
  analytic := vAnalytic_of_b3Prebound hPre
  D := D
  degree := hdeg
  integerizer_pos := hpos
  integerizer_poly := hpoly
  integerizer_rate := hrate
  rate_margin := hmargin
  towerM := 4
  towerP := p
  towerM_pos := by norm_num
  towerM_four := dvd_refl 4
  towerP_prime := hp
  nonvanishing := hNv

/-- Endpoint certificate for `li2InvValue (-q)` along `index k = M p^(k+6)`
(the shift makes every index ≥ 64). -/
theorem signedVEndpointCertificate {q : ℕ} (I : SignedVEndpointInputs q) :
    Nonempty (EndpointCertificate (li2InvValue (-(q : ℤ)))) := by
  have hp := I.towerP_prime
  have hpone : 1 < I.towerP := hp.one_lt
  have hM4 : 4 ≤ I.towerM := Nat.le_of_dvd I.towerM_pos I.towerM_four
  have hpow64 : ∀ k : ℕ, 64 ≤ I.towerP ^ (k + 6) := by
    intro k
    calc (64 : ℕ) = 2 ^ 6 := by norm_num
      _ ≤ I.towerP ^ 6 := Nat.pow_le_pow_left hp.two_le 6
      _ ≤ I.towerP ^ (k + 6) := Nat.pow_le_pow_right hp.pos (by omega)
  have hprodge : ∀ k : ℕ, I.towerP ^ (k + 6) ≤ I.towerM * I.towerP ^ (k + 6) := by
    intro k
    simpa using Nat.mul_le_mul_right (I.towerP ^ (k + 6)) (show 1 ≤ I.towerM by omega)
  have hidx64 : ∀ k, 64 ≤ I.towerM * I.towerP ^ (k + 6) := by
    intro k
    have := hpow64 k
    have := hprodge k
    omega
  have hidx_pos : ∀ k, 0 < I.towerM * I.towerP ^ (k + 6) := by
    intro k
    have := hidx64 k
    omega
  have hidx4 : ∀ k, 4 ∣ I.towerM * I.towerP ^ (k + 6) := fun k =>
    dvd_mul_of_dvd_left I.towerM_four _
  have hidx8 : ∀ k, 8 ≤ I.towerM * I.towerP ^ (k + 6) := by
    intro k
    have := hidx64 k
    omega
  have hmono : StrictMono (fun k : ℕ => I.towerM * I.towerP ^ (k + 6)) := by
    intro i j hij
    have hpow : I.towerP ^ (i + 6) < I.towerP ^ (j + 6) :=
      Nat.pow_lt_pow_right hpone (by omega)
    exact (Nat.mul_lt_mul_left I.towerM_pos).2 hpow
  have hrate' : ∀ ε : ℝ, 0 < ε → ∃ k₀, ∀ k, k₀ ≤ k →
      Real.log (I.D (I.towerM * I.towerP ^ (k + 6)) : ℝ) /
          ((I.towerM * I.towerP ^ (k + 6) : ℕ) : ℝ) ^ 2 ≤ I.tau + ε := by
    intro ε hε
    obtain ⟨K, hK⟩ := I.integerizer_rate ε hε
    refine ⟨K, fun k hk => ?_⟩
    have hkpow : k + 6 < I.towerP ^ (k + 6) := Nat.lt_pow_self hpone
    have := hprodge k
    exact hK _ (by omega) (hidx_pos k) (hidx4 k)
  have hnonzero : ∀ r : ℚ, ∃ k₀, ∀ k, k₀ ≤ k →
      (vFamilyG q (I.towerM * I.towerP ^ (k + 6))).eval (r : ℝ) ≠ 0 := by
    intro r
    obtain ⟨K, hK⟩ := I.nonvanishing r
    exact ⟨K, fun k hk => hK (k + 6) (by omega)⟩
  refine ⟨{
    index := fun k => I.towerM * I.towerP ^ (k + 6)
    G := vFamilyG q
    D := I.D
    alpha := I.alpha
    tau := I.tau
    cLog := I.C
    cLinear := 0
    cConst := 0
    index_strictMono := hmono
    index_multiple_four := hidx4
    index_ge_eight := hidx8
    alpha_gt_tau := I.rate_margin
    degree_bound := fun k => I.degree _ (hidx_pos k) (hidx4 k)
    integerizer_pos := fun k => I.integerizer_pos _ (hidx_pos k) (hidx4 k)
    integerizer_poly := fun k => I.integerizer_poly _ (hidx_pos k) (hidx4 k)
    analytic_bound := fun k => by
      refine (I.analytic _ (hidx64 k) (hidx4 k)).trans (le_of_eq ?_)
      congr 1
      ring
    integerizer_rate := hrate'
    nonzero_at_rationals := hnonzero }⟩

theorem signed_v_range_of_producers
    (hV : ∀ q : ℕ, 2 ≤ q → q ≤ 7 → SignedVEndpointInputs q) :
    ∀ n : ℤ, (-7 : ℤ) ≤ n → n ≤ -2 → n ≠ 0 → Irrational (li2InvValue n) := by
  intro n hlo hhi _
  obtain ⟨q, hq⟩ := Int.eq_ofNat_of_zero_le (by omega : (0 : ℤ) ≤ -n)
  have hn : n = -(q : ℤ) := by omega
  subst hn
  obtain ⟨c⟩ := signedVEndpointCertificate (hV q (by omega) (by omega))
  exact l1_endpoint_criterion _ c

/-! ## B.3 Hermite--Padé tails, n ≥ 12 and n ≤ -8 -/

open Li2Lean.B4 Li2Lean.B4.Residues

/-- `b_n = binom(2n+1, n)`, hp-tail.tex:55. -/
def hpB (n : ℕ) : ℕ := Nat.choose (2 * n + 1) n

/-- The ACTUAL integer form of hp-tail.tex `eq:hp-integer-form`:
`L_n(a) = a^N (d_N²/b_n²) (W_n(1/a) + V_n(1/a) Li2(1/a))`, `N = 2n+1`.
Unlike `TopDownHPIntegerizedAffineForm` (Sk:388), it is pinned to the
construction, so decay and no-adjacent-zero are meaningful statements. -/
def hpIntegerFormL (a : ℤ) (n : ℕ) : ℝ :=
  (a : ℝ) ^ (2 * n + 1) *
    ((hpIntegerizationScale (hpDenominator (2 * n + 1)) (hpB n) : ℚ) : ℝ) *
    (((Polynomial.eval ((a : ℚ)⁻¹) (hpWpoly n) : ℚ) : ℝ) +
      ((Polynomial.eval ((a : ℚ)⁻¹) (hpVpoly n) : ℚ) : ℝ) * li2InvValue a)

def HPIntegralForm (a : ℤ) : Prop :=
  ∃ X Y : ℕ → ℤ, ∀ n, hpIntegerFormL a n = (X n : ℝ) + (Y n : ℝ) * li2InvValue a

def HPDecay (a : ℤ) : Prop :=
  Tendsto (hpIntegerFormL a) atTop (𝓝 0)

def HPNoAdjacentZero (a : ℤ) : Prop :=
  ∀ n, ¬ (hpIntegerFormL a n = 0 ∧ hpIntegerFormL a (n + 1) = 0)

/-- Fixed-base limit glue (replaces Sk:477-482 for the actual form). -/
theorem hp_tail_irrational {a : ℤ} (hI : HPIntegralForm a) (hD : HPDecay a)
    (hZ : HPNoAdjacentZero a) : Irrational (li2InvValue a) := by
  obtain ⟨X, Y, hform⟩ := hI
  exact B4.irrational_of_integer_affine_forms_tendsto_zero X Y
    (hpIntegerFormL a) hform hD hZ

/-! ## B.4 The producer interface and the final assembly -/

/-- Named producers only. No field is `Irrational _`, an `EndpointCertificate`
for an unrestricted polynomial family, a generic affine-form record, or an
`Li2Bridges` field. Each field is stated on the literal construction. -/
structure AllNProducers where
  -- positive P0, q = 3..11 (q = 2 is the frozen 1/2 theorem)
  p0Profile : P0PositiveEnergyProfile
  p0Rate : ℕ → ℝ
  p0Integerizer : ∀ (q : ℕ) (hq : InRange (q : ℤ)), 3 ≤ q →
    P0IntegerizerBoundAt (family (q : ℤ) hq) (p0Rate q)
  p0RateMargin : ∀ q : ℕ, 3 ≤ q → q ≤ 11 → p0Rate q < p0PositiveChord q
  p0Tower : ∀ (q : ℕ) (hq : InRange (q : ℤ)), 3 ≤ q →
    ∃ M p : ℕ, Nonempty (P0FrobeniusTowerCertificate (family (q : ℤ) hq) M p)
  -- signed V, q = 2..7
  vInputs : ∀ q : ℕ, 2 ≤ q → q ≤ 7 → SignedVEndpointInputs q
  -- Hermite--Padé tails
  hpIntegral : ∀ a : ℤ, ((12 : ℤ) ≤ a ∨ a ≤ -8) → HPIntegralForm a
  hpDecayPos : ∀ a : ℤ, (12 : ℤ) ≤ a → HPDecay a
  hpDecayNeg : ∀ a : ℤ, a ≤ (-8 : ℤ) → HPDecay a
  hpNoAdj : ∀ a : ℤ, ((12 : ℤ) ≤ a ∨ a ≤ -8) → HPNoAdjacentZero a

/-- FINAL ASSEMBLY (replaces Sk:516-534 and is sorry-free). -/
theorem li2_inv_irrational_of_producers (P : AllNProducers) :
    li2InvIrrationalStatement := by
  unfold li2InvIrrationalStatement
  intro n hn
  rcases li2InvRangeSplit n hn with h | h | h | h | h | h
  · subst h
    exact li2_inv_irrational_one
  · subst h
    exact li2_inv_irrational_neg_one
  · exact p0_positive_range_of_producers P.p0Profile P.p0Rate P.p0Integerizer
      P.p0RateMargin (fun q hq h3 => p0Nonvanishing_of_tower (P.p0Tower q hq h3))
      n h.1 h.2 hn
  · exact signed_v_range_of_producers P.vInputs n h.1 h.2 hn
  · exact hp_tail_irrational (P.hpIntegral n (Or.inl h)) (P.hpDecayPos n h)
      (P.hpNoAdj n (Or.inl h))
  · exact hp_tail_irrational (P.hpIntegral n (Or.inr h)) (P.hpDecayNeg n h)
      (P.hpNoAdj n (Or.inr h))

/-- Exactly the Challenge/Solution signature, from the producers. -/
theorem li2_inv_irrational_of_producers' (P : AllNProducers) (n : ℤ) (hn : n ≠ 0) :
    Irrational (∑' k : ℕ, ((n : ℝ)⁻¹) ^ (k + 1) / ((k : ℝ) + 1) ^ 2) :=
  li2_inv_irrational_of_producers P n hn

end

end Li2Lean.AllNAssembly
