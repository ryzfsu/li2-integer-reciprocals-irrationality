/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang

The compiled degree-50 S6-dq certificate used by all six reference leaves.

S6-dq: the degree-50 moment expansion of the cross interaction
`D_q(μx, μv) = ∬ log|q + u v| dμx(u) dμv(v)` with an explicit remainder,

  D_q = dSeriesValue q D + ρ,   0 ≤ ρ ≤ m₅₁(μx) m₅₁(μv) / (51 q^51) ≤ Mx Mv / (51 q^51),

which places `ρ` inside `DEncBridge.tailInterval q D`.

Route (no infinite series and no Fubini over a series is needed):
* pointwise Leibniz remainder for `log (1 + s)`, `s ≥ 0`, even degree `n`:
  `0 ≤ log (1 + s) - P_n(s) ≤ s^(n+1)/(n+1)` (monotonicity from derivatives);
* on the a.e. support `[0,1]²` write
  `log (q + u v) = log q + Σ_{i<50} c_i u^(i+1) v^(i+1) + R(u v / q)`;
* integrate term by term (`integral_prod_mul`), moments by summation by parts
  (`v13ChainCells_diff_sum`), remainder by `integral_mono_ae`.

Deviation from v13 (recorded): v13 `certificate-algorithm.tex:117-121` uses degree 420
and the geometric tail `2 Mx Mv / (421 q^421)`.  The Lean evaluator `dEnc` uses degree
50 and tail `|Mx Mv| / (51 q^51)` without the factor 2; this file proves that tail via
the alternating (Leibniz) remainder of an even-degree truncation, which has sign `+`.

Implementation notes for the elaborated Mathlib steps are marked `-- note:`.
-/

import Mathlib
import Li2Lean.B3.DEdBridge
import Li2Lean.B3.V13RowFacts
import Li2Lean.B3.ReferencePackageGeneric
import Li2Lean.B3.V13ChainLogEndpoint
import Li2Lean.B3.F3Ball

namespace Li2Lean

noncomputable section

namespace B3

namespace DqSeries

open MeasureTheory Set Filter
open scoped ENNReal
open V
open V.EnergyCertI
open V.EnergyCertI.IK

/-! ## 1. Pointwise Leibniz remainder for `log (1 + s)` -/

/-- `P_n(s) = Σ_{i<n} (-1)^i s^(i+1) / (i+1)`. -/
def logPartial (n : ℕ) (s : ℝ) : ℝ :=
  ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * s ^ (i + 1) / ((i : ℝ) + 1)

/-- `R_n(s) = log (1 + s) - P_n(s)`. -/
def logRem (n : ℕ) (s : ℝ) : ℝ := Real.log (1 + s) - logPartial n s

theorem logPartial_zero_arg (n : ℕ) : logPartial n 0 = 0 := by
  simp [logPartial]

theorem logRem_zero_arg (n : ℕ) : logRem n 0 = 0 := by
  simp [logRem, logPartial_zero_arg]

theorem hasDerivAt_logPartial (n : ℕ) (s : ℝ) :
    HasDerivAt (logPartial n) (∑ i ∈ Finset.range n, (-s) ^ i) s := by
  have h : ∀ i ∈ Finset.range n,
      HasDerivAt (fun x : ℝ => (-1 : ℝ) ^ i * x ^ (i + 1) / ((i : ℝ) + 1))
        ((-s) ^ i) s := by
    intro i _
    have h1 := ((hasDerivAt_pow (i + 1) s).const_mul ((-1 : ℝ) ^ i)).div_const
      ((i : ℝ) + 1)
    convert h1 using 1
    -- note: goal `(-s)^i = (-1)^i * (↑(i+1) * s^(i+1-1)) / (↑i+1)`
    have hi : ((i : ℝ) + 1) ≠ 0 := by positivity
    rw [neg_pow, Nat.add_sub_cancel]
    push_cast
    first
      | (field_simp; ring)
      | field_simp
  have hs := HasDerivAt.sum h  -- note: `HasDerivAt.sum` / `HasDerivAt.fun_sum`
  convert hs using 1 <;> ext x <;> simp [logPartial]

/-- Geometric identity behind the remainder derivative. -/
theorem inv_sub_geom (n : ℕ) {s : ℝ} (hs : 1 + s ≠ 0) :
    1 / (1 + s) - ∑ i ∈ Finset.range n, (-s) ^ i = (-s) ^ n / (1 + s) := by
  have hg := geom_sum_mul (-s) n  -- (Σ (-s)^i) * (-s - 1) = (-s)^n - 1
  have h2 : (∑ i ∈ Finset.range n, (-s) ^ i) * (1 + s) = 1 - (-s) ^ n := by
    have : (∑ i ∈ Finset.range n, (-s) ^ i) * (1 + s) =
        -((∑ i ∈ Finset.range n, (-s) ^ i) * (-s - 1)) := by ring
    rw [this, hg]; ring
  rw [eq_div_iff hs, sub_mul, one_div_mul_cancel hs, h2]
  ring

theorem hasDerivAt_logRem (n : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    HasDerivAt (logRem n) ((-s) ^ n / (1 + s)) s := by
  have hpos : 0 < 1 + s := by linarith
  have hlog : HasDerivAt (fun x : ℝ => Real.log (1 + x)) (1 / (1 + s)) s := by
    have h := ((hasDerivAt_id' s).const_add (1 : ℝ)).log (ne_of_gt hpos)
    -- note: `HasDerivAt.log` yields derivative `1 / (1 + s)`
    simpa using h
  have h := hlog.sub (hasDerivAt_logPartial n s)
  rw [inv_sub_geom n (ne_of_gt hpos)] at h
  exact h

/-- Monotonicity helper: nonnegative derivative on `[0, ∞)` gives `f 0 ≤ f s`. -/
theorem le_of_hasDerivAt_nonneg {f f' : ℝ → ℝ}
    (hf : ∀ x, 0 ≤ x → HasDerivAt f (f' x) x) (hf' : ∀ x, 0 ≤ x → 0 ≤ f' x)
    {s : ℝ} (hs : 0 ≤ s) : f 0 ≤ f s := by
  have hmono : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · intro x hx
      exact (hf x hx).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      exact (hf x (le_of_lt hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      rw [(hf x (le_of_lt hx)).deriv]
      exact hf' x (le_of_lt hx)
  exact hmono (show (0 : ℝ) ∈ Set.Ici 0 from Set.mem_Ici.mpr le_rfl)
    (Set.mem_Ici.mpr hs) hs

/-- Leibniz remainder for an even truncation degree. -/
theorem logRem_bounds {n : ℕ} (hn : Even n) {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ logRem n s ∧ logRem n s ≤ s ^ (n + 1) / ((n : ℝ) + 1) := by
  have hderiv : ∀ x, 0 ≤ x → HasDerivAt (logRem n) (x ^ n / (1 + x)) x := by
    intro x hx
    simpa [hn.neg_pow] using hasDerivAt_logRem n hx
  constructor
  · have h : logRem n 0 ≤ logRem n s :=
      le_of_hasDerivAt_nonneg (f := logRem n) (f' := fun x => x ^ n / (1 + x))
        hderiv (fun x hx => div_nonneg (pow_nonneg hx n) (by linarith)) hs
    rw [logRem_zero_arg] at h
    exact h
  · -- g x = x^(n+1)/(n+1) - R_n(x) has derivative x^n - x^n/(1+x) ≥ 0
    have hg : ∀ x, 0 ≤ x → HasDerivAt
        (fun y => y ^ (n + 1) / ((n : ℝ) + 1) - logRem n y)
        (x ^ n - x ^ n / (1 + x)) x := by
      intro x hx
      have hp := (hasDerivAt_pow (n + 1) x).div_const ((n : ℝ) + 1)
      have hp' : HasDerivAt (fun y : ℝ => y ^ (n + 1) / ((n : ℝ) + 1)) (x ^ n) x := by
        convert hp using 1
        have : ((n : ℝ) + 1) ≠ 0 := by positivity
        rw [Nat.add_sub_cancel]; push_cast
        first
          | (field_simp; ring)
          | field_simp
      exact hp'.sub (hderiv x hx)
    have hg' : ∀ x : ℝ, 0 ≤ x → 0 ≤ x ^ n - x ^ n / (1 + x) := by
      intro x hx
      have hxn : 0 ≤ x ^ n := pow_nonneg hx n
      have h1 : x ^ n / (1 + x) ≤ x ^ n :=
        div_le_self hxn (by linarith)
      linarith
    have h : (0 : ℝ) ^ (n + 1) / ((n : ℝ) + 1) - logRem n 0 ≤
        s ^ (n + 1) / ((n : ℝ) + 1) - logRem n s :=
      le_of_hasDerivAt_nonneg hg hg' hs
    have h0 : (0 : ℝ) ^ (n + 1) = 0 := by simp
    rw [h0, zero_div, logRem_zero_arg, sub_zero] at h
    linarith

theorem even_fifty : Even (50 : ℕ) := ⟨25, rfl⟩

/-! ## 2. The evaluator coefficients and the finite list sum -/

/-- The coefficient of the `i`-th dq term, exactly as in `DEncBridge.dSeriesValue`. -/
def dqCoeff (q i : ℕ) : ℝ :=
  IK.val ((if i % 2 = 0 then 1 else -1), (i + 1) * q ^ (i + 1))

theorem dqCoeff_eq (q i : ℕ) :
    dqCoeff q i = (-1 : ℝ) ^ i / (((i : ℝ) + 1) * (q : ℝ) ^ (i + 1)) := by
  unfold dqCoeff IK.val
  have hnum : (((if i % 2 = 0 then (1 : ℤ) else -1 : ℤ)) : ℝ) = (-1 : ℝ) ^ i := by
    rcases Nat.even_or_odd i with h | h
    · rw [if_pos (Nat.even_iff.mp h), h.neg_one_pow]; simp
    · have h1 : i % 2 ≠ 0 := by rw [Nat.odd_iff.mp h]; decide
      rw [if_neg h1, h.neg_one_pow]; simp
  -- note: the first component is elaborated as `ℤ`; `simp only` may be needed first
  rw [hnum]
  push_cast
  ring

theorem logPartial_fifty_eq (q : ℕ) (hq : 0 < (q : ℝ)) (u v : ℝ) :
    logPartial 50 (u * v / q) =
      ∑ i ∈ Finset.range 50, dqCoeff q i * (u ^ (i + 1) * v ^ (i + 1)) := by
  unfold logPartial
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [dqCoeff_eq]
  have hq0 : (q : ℝ) ≠ 0 := ne_of_gt hq
  have hi : ((i : ℝ) + 1) ≠ 0 := by positivity
  rw [div_pow, mul_pow]
  first
    | (field_simp; ring)
    | field_simp

theorem list_range_map_sum (f : ℕ → ℝ) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
      simp

/-! ## 3. Moments of a decoded chain measure -/

theorem val_qpow_of_nonneg {a : QF} (ha : 0 ≤ a.1) (n : ℕ) :
    IK.val (qpow a n) = IK.val a ^ n := by
  have hnot : ¬ (a.1 < 0 ∧ n % 2 = 1) := fun h => absurd h.1 (not_lt.mpr ha)
  unfold IK.val qpow
  rw [if_neg hnot, div_pow]
  -- note: cast normal form of `((Int.ofNat (a.1.natAbs ^ n) : ℤ) : ℝ)`
  simp only [Int.ofNat_eq_coe, Int.cast_natCast, Nat.cast_pow]
  rw [Int.natAbs_of_nonneg ha, Int.cast_pow]

theorem momentValue_eq (rows : List CP) (k : ℕ) (he : ∀ p ∈ rows, 0 ≤ p.e.1) :
    DEncBridge.momentValue rows k =
      -(rows.map fun p => IK.val p.J * (IK.val p.e ^ (k + 1) / ((k : ℝ) + 1))).sum := by
  induction rows with
  | nil => simp [DEncBridge.momentValue]
  | cons p ps ih =>
      have hp : 0 ≤ p.e.1 := he p (by simp)
      have hps : ∀ r ∈ ps, 0 ≤ r.e.1 := fun r hr => he r (by simp [hr])
      have ih' := ih hps
      unfold DEncBridge.momentValue at ih' ⊢
      simp only [List.map_cons, List.sum_cons]
      rw [ih']
      have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
      rw [val_qmul, val_qneg, val_qmul, val_qpow_of_nonneg hp]
      have h1 : IK.val ((1 : ℤ), k + 1) = 1 / ((k : ℝ) + 1) := by
        simp [IK.val]  -- note: cast of `k + 1 : ℕ`
      rw [h1]
      ring

theorem integral_pow_v13ChainMeasure (cells : List V13ChainCell) (k : ℕ)
    (hb : ∀ c ∈ cells, c.left ≤ c.right) (hd : ∀ c ∈ cells, 0 ≤ c.density) :
    (∫ u : ℝ, u ^ k ∂v13ChainMeasure cells) =
      (cells.map fun c => c.density *
        (c.right ^ (k + 1) / ((k : ℝ) + 1) - c.left ^ (k + 1) / ((k : ℝ) + 1))).sum := by
  induction cells with
  | nil => simp [v13ChainMeasure]
  | cons c cs ih =>
      have hc : c ∈ c :: cs := by simp
      have hbR : ∀ d ∈ cs, d.left ≤ d.right := fun d hd' => hb d (by simp [hd'])
      have hdR : ∀ d ∈ cs, 0 ≤ d.density := fun d hd' => hd d (by simp [hd'])
      have hcell : Integrable (fun u : ℝ => u ^ k) (volume.restrict (Ioc c.left c.right)) :=
        ((continuous_pow k).continuousOn.integrableOn_compact isCompact_Icc).mono_set
          Ioc_subset_Icc_self
      have hcell' : Integrable (fun u : ℝ => u ^ k)
          (ENNReal.ofReal c.density • volume.restrict (Ioc c.left c.right)) :=
        hcell.smul_measure ENNReal.ofReal_ne_top
      have htail : Integrable (fun u : ℝ => u ^ k) (v13ChainMeasure cs) :=
        integrable_v13ChainMeasure_of_continuousOn_cells cs _
          (fun _ _ => (continuous_pow k).continuousOn)
      have hsplit : v13ChainMeasure (c :: cs) =
          ENNReal.ofReal c.density • volume.restrict (Ioc c.left c.right) +
            v13ChainMeasure cs := by
        simp [v13ChainMeasure]
      rw [hsplit, integral_add_measure hcell' htail, integral_smul_measure,
        ENNReal.toReal_ofReal (hd c hc), smul_eq_mul]
      have hseg : (∫ u in Ioc c.left c.right, u ^ k) =
          (c.right ^ (k + 1) - c.left ^ (k + 1)) / ((k : ℝ) + 1) := by
        rw [← intervalIntegral.integral_of_le (hb c hc), integral_pow]
      rw [hseg, ih hbR hdR]
      simp only [List.map_cons, List.sum_cons]
      ring

/-- `∫ u^k dμ = momentValue rows k` for a decoded chain (summation by parts, `ΣJ = 0`). -/
theorem integral_pow_decoded (rows : List CP) (k : ℕ)
    (hb : ∀ c ∈ v13ChainCells rows, c.left ≤ c.right)
    (hd : ∀ c ∈ v13ChainCells rows, 0 ≤ c.density)
    (hsum : (rows.map fun p => IK.val p.J).sum = 0)
    (he : ∀ p ∈ rows, 0 ≤ p.e.1) :
    (∫ u : ℝ, u ^ k ∂v13ChainMeasure (v13ChainCells rows)) =
      DEncBridge.momentValue rows k := by
  rw [integral_pow_v13ChainMeasure _ k hb hd, momentValue_eq rows k he]
  have h := v13ChainCells_diff_sum (fun t : ℝ => t ^ (k + 1) / ((k : ℝ) + 1)) rows hsum
  -- note: `h` has exactly the left-hand list (density * (f right - f left))
  simpa using h

theorem integrable_pow_chain (cells : List V13ChainCell) (k : ℕ) :
    Integrable (fun u : ℝ => u ^ k) (v13ChainMeasure cells) :=
  integrable_v13ChainMeasure_of_continuousOn_cells cells _
    (fun _ _ => (continuous_pow k).continuousOn)

/-! ## 4. The tail interval -/

theorem den_pos_of_val_ne_zero {a : QF} (h : IK.val a ≠ 0) : 0 < a.2 := by
  apply Nat.pos_of_ne_zero
  intro h0
  apply h
  simp [IK.val, h0]

theorem tail_mem {q : ℕ} {D : IData} (hq : 0 < q) (hden : 0 < (qmul D.mx D.mv).2)
    {rho : ℝ} (h0 : 0 ≤ rho)
    (h1 : rho ≤ |IK.val (qmul D.mx D.mv)| / (51 * (q : ℝ) ^ 51)) :
    IV.mem (DEncBridge.tailInterval q D) rho := by
  have hd : 0 < DEncBridge.tailDen q D :=
    Nat.mul_pos (Nat.mul_pos (by norm_num) (pow_pos hq 51)) hden
  have hS : (0 : ℝ) < (S : ℝ) := by norm_num [S]
  have hdR : (0 : ℝ) < (DEncBridge.tailDen q D : ℝ) := by exact_mod_cast hd
  have hval : ((DEncBridge.tailNumerator D : ℕ) : ℝ) / (DEncBridge.tailDen q D : ℝ) =
      |IK.val (qmul D.mx D.mv)| / (51 * (q : ℝ) ^ 51) := by
    have hden' : (0 : ℝ) < ((qmul D.mx D.mv).2 : ℝ) := by exact_mod_cast hden
    simp only [DEncBridge.tailNumerator, DEncBridge.tailDen, IK.val]
    rw [natAbs_cast, abs_div, abs_of_pos hden']
    push_cast
    field_simp
  have hnn : (0 : ℝ) ≤ ((DEncBridge.tailNumerator D : ℕ) : ℝ) := by positivity
  unfold IV.mem DEncBridge.tailInterval
  constructor
  · have hfl := fl_le_div (-(Int.ofNat (DEncBridge.tailNumerator D) * Int.ofNat S)) hd
    have hneg : ((-(Int.ofNat (DEncBridge.tailNumerator D) * Int.ofNat S) : ℤ) : ℝ) /
        (DEncBridge.tailDen q D : ℝ) ≤ 0 := by
      have hnum : ((-(Int.ofNat (DEncBridge.tailNumerator D) * Int.ofNat S) : ℤ) : ℝ) ≤ 0 := by
        push_cast  -- note: `Int.ofNat n` casts to `(n : ℝ)`
        exact neg_nonpos.mpr (mul_nonneg hnn hS.le)
      exact div_nonpos_of_nonpos_of_nonneg hnum hdR.le
    have : ((fl (-(Int.ofNat (DEncBridge.tailNumerator D) * Int.ofNat S))
        (DEncBridge.tailDen q D) : ℤ) : ℝ) / (S : ℝ) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (le_trans hfl hneg) hS.le
    linarith
  · have hcl := div_le_cl (Int.ofNat (DEncBridge.tailNumerator D) * Int.ofNat S) hd
    rw [le_div_iff₀ hS]
    calc rho * (S : ℝ)
        ≤ (((DEncBridge.tailNumerator D : ℕ) : ℝ) / (DEncBridge.tailDen q D : ℝ)) * S := by
          rw [hval]; exact mul_le_mul_of_nonneg_right h1 hS.le
      _ = ((Int.ofNat (DEncBridge.tailNumerator D) * Int.ofNat S : ℤ) : ℝ) /
            (DEncBridge.tailDen q D : ℝ) := by
          field_simp [hdR.ne']
          norm_cast
      _ ≤ _ := hcl

/-! ## 5. The kernel on the support box -/

/-- Polynomial part of the kernel on `ℝ × ℝ`. -/
def dqPoly (q : ℕ) (z : ℝ × ℝ) : ℝ :=
  ∑ i ∈ Finset.range 50, dqCoeff q i * (z.1 ^ (i + 1) * z.2 ^ (i + 1))

/-- Remainder part of the kernel on `ℝ × ℝ`. -/
def dqRem (q : ℕ) (z : ℝ × ℝ) : ℝ := logRem 50 (z.1 * z.2 / q)

/-- Majorant of the remainder. -/
def dqMaj (q : ℕ) (z : ℝ × ℝ) : ℝ := (1 / (51 * (q : ℝ) ^ 51)) * (z.1 ^ 51 * z.2 ^ 51)

theorem kernel_decomp {q : ℕ} (hq : 0 < (q : ℝ)) {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    V.vCrossKernel q (u : ℂ) (v : ℂ) = Real.log q + dqPoly q (u, v) + dqRem q (u, v) := by
  have hpos : 0 < (q : ℝ) + u * v := by positivity
  have hker : V.vCrossKernel q (u : ℂ) (v : ℂ) = Real.log ((q : ℝ) + u * v) := by
    unfold V.vCrossKernel
    have hcast : ((q : ℂ) + (u : ℂ) * (v : ℂ)) = (((q : ℝ) + u * v : ℝ) : ℂ) := by
      push_cast; ring
    rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
  have hq0 : (q : ℝ) ≠ 0 := ne_of_gt hq
  have h1 : (0 : ℝ) < 1 + u * v / q := by positivity
  have hsplit : (q : ℝ) + u * v = (q : ℝ) * (1 + u * v / q) := by
    rw [mul_add, mul_one, mul_div_cancel₀ (u * v) hq0]  -- note: `mul_div_cancel₀` form
  rw [hker, hsplit, Real.log_mul hq0 (ne_of_gt h1)]
  unfold dqRem dqPoly logRem
  dsimp only  -- reduce `(u, v).1`, `(u, v).2`
  rw [logPartial_fifty_eq q hq u v]
  ring

theorem dqRem_bounds {q : ℕ} (hq : 0 < (q : ℝ)) {z : ℝ × ℝ} (h1 : 0 ≤ z.1) (h2 : 0 ≤ z.2) :
    0 ≤ dqRem q z ∧ dqRem q z ≤ dqMaj q z := by
  have hs : 0 ≤ z.1 * z.2 / q := by positivity
  obtain ⟨hlo, hhi⟩ := logRem_bounds even_fifty hs
  refine ⟨hlo, ?_⟩
  unfold dqRem dqMaj
  have hq0 : (q : ℝ) ≠ 0 := ne_of_gt hq
  have : (z.1 * z.2 / q) ^ (50 + 1) / (((50 : ℕ) : ℝ) + 1) =
      (1 / (51 * (q : ℝ) ^ 51)) * (z.1 ^ 51 * z.2 ^ 51) := by
    rw [div_pow, mul_pow]; push_cast
    first
      | (field_simp; ring)
      | field_simp
  exact le_of_le_of_eq hhi this

theorem measurable_dqRem (q : ℕ) : Measurable (dqRem q) := by
  unfold dqRem logRem logPartial
  -- note: `measurability` / `fun_prop` should close this (log is measurable)
  measurability

/-! ## 6. Main theorem -/

/-- S6-dq for an arbitrary decoded source.  The conclusion is literally the body of
`V13DqSeries Dr N` in `H6CertPerQ.lean`. -/
theorem v13_dq_series_core {q : ℕ} {hq : SignedVBaseRange q} (Dr : V13DecodedRows q)
    (hDr : V13FieldRowFacts Dr) (hrows : V13DecodedRowBounds q Dr)
    (N : V13MeasureNormalization hq (v13RefRaw Dr))
    (hmx : IK.val Dr.data.mx = 1) (hmv : IK.val Dr.data.mv = 5 / 4) :
    ∃ rho : ℝ, IV.mem (DEncBridge.tailInterval q Dr.data) rho ∧
      V.vCrossInteraction q (v13RefMeasure Dr N).μx (v13RefMeasure Dr N).μv =
        DEncBridge.dSeriesValue q Dr.data + rho := by
  -- basic constants
  have hq2 : 2 ≤ q := hq.1
  have hqN : 0 < q := by omega
  have hqR : (0 : ℝ) < q := by exact_mod_cast hqN
  -- the two real chain measures
  set μ := v13ChainMeasure (v13ChainCells Dr.data.xp) with hμdef
  set ν := v13ChainMeasure (v13ChainCells Dr.data.vp) with hνdef
  haveI : IsFiniteMeasure μ := v13ChainMeasure_isFinite _
  haveI : IsFiniteMeasure ν := v13ChainMeasure_isFinite _
  -- row facts
  have hxb : ∀ c ∈ v13ChainCells Dr.data.xp, 0 ≤ c.left ∧ c.left ≤ c.right :=
    fun c hc => ⟨(hDr.x_cells c hc).1, (hDr.x_cells c hc).2.1⟩
  have hvb : ∀ c ∈ v13ChainCells Dr.data.vp, 0 ≤ c.left ∧ c.left ≤ c.right :=
    fun c hc => ⟨(hDr.v_cells c hc).1, (hDr.v_cells c hc).2.1⟩
  have hxd : ∀ c ∈ v13ChainCells Dr.data.xp, 0 ≤ c.density :=
    fun c hc => (hDr.x_cells c hc).2.2
  have hvd : ∀ c ∈ v13ChainCells Dr.data.vp, 0 ≤ c.density :=
    fun c hc => (hDr.v_cells c hc).2.2
  have hxr : ∀ c ∈ v13ChainCells Dr.data.xp, c.right ≤ 1 :=
    fun c hc => (hrows.x_full c hc).2
  have hvr : ∀ c ∈ v13ChainCells Dr.data.vp, c.right ≤ 1 :=
    fun c hc => (hrows.v_full c hc).2
  have hxe : ∀ p ∈ Dr.data.xp, 0 ≤ p.e.1 := fun p hp => (hDr.x_rows p hp).1
  have hve : ∀ p ∈ Dr.data.vp, 0 ≤ p.e.1 := fun p hp => (hDr.v_rows p hp).1
  -- moments
  have hmomx : ∀ k, (∫ u : ℝ, u ^ k ∂μ) = DEncBridge.momentValue Dr.data.xp k :=
    fun k => integral_pow_decoded Dr.data.xp k (fun c hc => (hxb c hc).2) hxd hDr.x_jump hxe
  have hmomv : ∀ k, (∫ u : ℝ, u ^ k ∂ν) = DEncBridge.momentValue Dr.data.vp k :=
    fun k => integral_pow_decoded Dr.data.vp k (fun c hc => (hvb c hc).2) hvd hDr.v_jump hve
  -- masses of the real measures (from the normalization witness)
  have hμ1 : μ Set.univ = 1 := by
    have h := N.mass_x
    change Measure.map Complex.ofReal μ Set.univ = 1 at h  -- note: defeq unfolding
    rwa [Measure.map_apply Complex.measurable_ofReal MeasurableSet.univ,
      Set.preimage_univ] at h
  have hν54 : ν Set.univ = 5 / 4 := by
    have h := N.mass_v
    change Measure.map Complex.ofReal ν Set.univ = 5 / 4 at h
    rwa [Measure.map_apply Complex.measurable_ofReal MeasurableSet.univ,
      Set.preimage_univ] at h
  have hμr : μ.real Set.univ = 1 := by
    simp [measureReal_def, hμ1]  -- note: `measureReal_def`
  have hνr : ν.real Set.univ = 5 / 4 := by
    rw [measureReal_def, hν54]
    -- note: `ENNReal.toReal (5/4) = 5/4`
    norm_num [ENNReal.toReal_div]
  have hprodr : (μ.prod ν).real Set.univ = 5 / 4 := by
    rw [measureReal_def, ← Set.univ_prod_univ, Measure.prod_prod, hμ1, hν54, one_mul]
    norm_num [ENNReal.toReal_div]  -- note: same `toReal (5/4)` step as `hνr`
  -- transfer the complex product integral to `ℝ × ℝ`
  have hEmb : MeasurableEmbedding (Prod.map Complex.ofReal Complex.ofReal : ℝ × ℝ → ℂ × ℂ) :=
    (Complex.isometry_ofReal.isClosedEmbedding.prodMap
      Complex.isometry_ofReal.isClosedEmbedding).measurableEmbedding
    -- note: alternatively `MeasurableEmbedding.prodMap hE hE` with
    -- `hE := Complex.isometry_ofReal.isClosedEmbedding.measurableEmbedding`
  have hD : V.vCrossInteraction q (v13RefMeasure Dr N).μx (v13RefMeasure Dr N).μv =
      ∫ z : ℝ × ℝ, V.vCrossKernel q (z.1 : ℂ) (z.2 : ℂ) ∂(μ.prod ν) := by
    change (∫ p : ℂ × ℂ, V.vCrossKernel q p.1 p.2
        ∂((Measure.map Complex.ofReal μ).prod (Measure.map Complex.ofReal ν))) = _
    -- note: `Measure.map_prod_map` argument order / SigmaFinite instances
    rw [Measure.map_prod_map μ ν Complex.measurable_ofReal Complex.measurable_ofReal,
      hEmb.integral_map]
    rfl
  -- a.e. support box
  have hx_ae : ∀ᵐ u ∂μ, 0 ≤ u ∧ u ≤ 1 :=
    (ae_nonneg_v13ChainMeasure _ hxb).and (ae_le_of_right_le_v13ChainMeasure _ hxr)
  have hv_ae : ∀ᵐ v ∂ν, 0 ≤ v ∧ v ≤ 1 :=
    (ae_nonneg_v13ChainMeasure _ hvb).and (ae_le_of_right_le_v13ChainMeasure _ hvr)
  have hae : ∀ᵐ z ∂(μ.prod ν), (0 ≤ z.1 ∧ z.1 ≤ 1) ∧ (0 ≤ z.2 ∧ z.2 ≤ 1) :=
    -- note: `Measure.quasiMeasurePreserving_fst/snd` and `QuasiMeasurePreserving.ae`
    ((Measure.quasiMeasurePreserving_fst).ae hx_ae).and
      ((Measure.quasiMeasurePreserving_snd).ae hv_ae)
  -- integrability of the three pieces
  have hIpoly : Integrable (dqPoly q) (μ.prod ν) := by
    unfold dqPoly
    refine integrable_finset_sum (Finset.range 50) (fun i _ => ?_)
    exact ((integrable_pow_chain _ (i + 1)).mul_prod
      (integrable_pow_chain _ (i + 1))).const_mul (dqCoeff q i)
    -- note: `Integrable.prod_mul` name/argument form
  have hImaj : Integrable (dqMaj q) (μ.prod ν) := by
    unfold dqMaj
    exact ((integrable_pow_chain _ 51).mul_prod (integrable_pow_chain _ 51)).const_mul _
  have hIrem : Integrable (dqRem q) (μ.prod ν) := by
    refine hImaj.mono' (measurable_dqRem q).aestronglyMeasurable ?_
    filter_upwards [hae] with z hz
    obtain ⟨hlo, hhi⟩ := dqRem_bounds hqR hz.1.1 hz.2.1
    rw [Real.norm_eq_abs, abs_of_nonneg hlo]
    exact hhi
  -- the remainder and its bracket
  set rho := ∫ z : ℝ × ℝ, dqRem q z ∂(μ.prod ν) with hrho
  have hrho0 : 0 ≤ rho := by
    apply integral_nonneg_of_ae
    filter_upwards [hae] with z hz
    exact (dqRem_bounds hqR hz.1.1 hz.2.1).1
  have hmaj_int : (∫ z : ℝ × ℝ, dqMaj q z ∂(μ.prod ν)) =
      (1 / (51 * (q : ℝ) ^ 51)) * ((∫ u : ℝ, u ^ 51 ∂μ) * (∫ v : ℝ, v ^ 51 ∂ν)) := by
    unfold dqMaj
    rw [integral_const_mul, integral_prod_mul (fun u : ℝ => u ^ 51) (fun v : ℝ => v ^ 51)]
    -- note: `integral_prod_mul` explicit-argument form
  have hm51x0 : 0 ≤ ∫ u : ℝ, u ^ 51 ∂μ :=
    integral_nonneg_of_ae (hx_ae.mono fun u hu => pow_nonneg hu.1 _)
  have hm51v0 : 0 ≤ ∫ v : ℝ, v ^ 51 ∂ν :=
    integral_nonneg_of_ae (hv_ae.mono fun v hv => pow_nonneg hv.1 _)
  have hm51x1 : (∫ u : ℝ, u ^ 51 ∂μ) ≤ 1 := by
    have h := integral_mono_ae (integrable_pow_chain _ 51) (integrable_const (1 : ℝ))
      (hx_ae.mono fun u hu => pow_le_one₀ hu.1 hu.2)
    -- note: `integral_const` returns `μ.real univ • 1`
    rw [integral_const, smul_eq_mul, hμr, mul_one] at h
    exact h
  have hm51v1 : (∫ v : ℝ, v ^ 51 ∂ν) ≤ 5 / 4 := by
    have h := integral_mono_ae (integrable_pow_chain _ 51) (integrable_const (1 : ℝ))
      (hv_ae.mono fun v hv => pow_le_one₀ hv.1 hv.2)
    rw [integral_const, smul_eq_mul, hνr, mul_one] at h
    exact h
  have hrho1 : rho ≤ (5 / 4 : ℝ) / (51 * (q : ℝ) ^ 51) := by
    have h := integral_mono_ae hIrem hImaj
      (hae.mono fun z hz => (dqRem_bounds hqR hz.1.1 hz.2.1).2)
    rw [hmaj_int] at h
    have hprod : (∫ u : ℝ, u ^ 51 ∂μ) * (∫ v : ℝ, v ^ 51 ∂ν) ≤ 1 * (5 / 4) :=
      mul_le_mul hm51x1 hm51v1 hm51v0 zero_le_one
    have hc : 0 ≤ 1 / (51 * (q : ℝ) ^ 51) := by positivity
    calc rho ≤ _ := h
      _ ≤ (1 / (51 * (q : ℝ) ^ 51)) * (1 * (5 / 4)) := mul_le_mul_of_nonneg_left hprod hc
      _ = (5 / 4 : ℝ) / (51 * (q : ℝ) ^ 51) := by ring
  -- tail membership
  have hmxden : 0 < Dr.data.mx.2 := den_pos_of_val_ne_zero (by rw [hmx]; norm_num)
  have hmvden : 0 < Dr.data.mv.2 := den_pos_of_val_ne_zero (by rw [hmv]; norm_num)
  have hmass : |IK.val (qmul Dr.data.mx Dr.data.mv)| = 5 / 4 := by
    rw [val_qmul, hmx, hmv]; norm_num
  refine ⟨rho, tail_mem hqN (Nat.mul_pos hmxden hmvden) hrho0 (by rw [hmass]; exact hrho1), ?_⟩
  -- the identity
  rw [hD]
  have hcongr : (∫ z : ℝ × ℝ, V.vCrossKernel q (z.1 : ℂ) (z.2 : ℂ) ∂(μ.prod ν)) =
      ∫ z : ℝ × ℝ, (Real.log q + dqPoly q z) + dqRem q z ∂(μ.prod ν) := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with z hz
    exact kernel_decomp hqR hz.1.1 hz.2.1
  have hpoly_int : (∫ z : ℝ × ℝ, dqPoly q z ∂(μ.prod ν)) =
      ∑ i ∈ Finset.range 50, dqCoeff q i *
        (DEncBridge.momentValue Dr.data.xp (i + 1) *
          DEncBridge.momentValue Dr.data.vp (i + 1)) := by
    unfold dqPoly
    rw [integral_finset_sum (Finset.range 50) (fun i _ =>
      ((integrable_pow_chain _ (i + 1)).mul_prod
        (integrable_pow_chain _ (i + 1))).const_mul (dqCoeff q i))]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [integral_const_mul,
      integral_prod_mul (fun u : ℝ => u ^ (i + 1)) (fun v : ℝ => v ^ (i + 1)),
      hmomx, hmomv]
  have hsplit1 : (∫ z : ℝ × ℝ, (Real.log q + dqPoly q z) + dqRem q z ∂(μ.prod ν)) =
      (∫ z : ℝ × ℝ, Real.log q + dqPoly q z ∂(μ.prod ν)) +
        ∫ z : ℝ × ℝ, dqRem q z ∂(μ.prod ν) :=
    integral_add ((integrable_const (Real.log q)).add hIpoly) hIrem
  have hsplit2 : (∫ z : ℝ × ℝ, Real.log q + dqPoly q z ∂(μ.prod ν)) =
      (∫ _z : ℝ × ℝ, Real.log q ∂(μ.prod ν)) + ∫ z : ℝ × ℝ, dqPoly q z ∂(μ.prod ν) :=
    integral_add (integrable_const (Real.log q)) hIpoly
  rw [hcongr, hsplit1, hsplit2, integral_const, hprodr, smul_eq_mul, hpoly_int]
  try rw [← hrho]  -- make the remainder atom literally `rho` for the final `ring`
  unfold DEncBridge.dSeriesValue
  rw [val_qmul, hmx, hmv, list_range_map_sum]
  have hq1 : IK.val (Int.ofNat q, 1) = (q : ℝ) := by simp [IK.val]
  rw [hq1]
  -- the summands of `dSeriesValue` are `dqCoeff q i * (m_x * m_v)` by definition
  simp only [dqCoeff]
  ring

end DqSeries

/-! ## 7. Hook for `H6CertPerQ.lean`

Replace the `OPEN (S6-dq)` comment after `def V13DqSeries` by:

theorem v13_dq_series {q : ℕ} {hq : SignedVBaseRange q} (Dr : V13DecodedRows q)
    (hDr : V13FieldRowFacts Dr) (hrows : V13DecodedRowBounds q Dr)
    (N : V13MeasureNormalization hq (v13RefRaw Dr))
    (hmx : IK.val Dr.data.mx = 1) (hmv : IK.val Dr.data.mv = 5 / 4) :
    V13DqSeries Dr N :=
  DqSeries.v13_dq_series_core Dr hDr hrows N hmx hmv

(`V13DqSeries` is a `def` whose body is the conclusion of `v13_dq_series_core`; if
`exact` does not unfold it, use `by unfold V13DqSeries; exact ...`.)

Per-q inputs: `hDr` (finite row facts, already `decide`d per q in Part C/D),
`hrows` (`V13DecodedRowBounds`, already a field of `V13NumericCertificates`),
`hmx`, `hmv` (one `norm_num [IK.val, qXD, mkIData, sumU]` / `decide` each; the check
script confirms `val mx = 1`, `val mv = 5/4` exactly for q = 2..7).  No further
q-specific numerics: the tail bound is uniform in q.
-/

end B3

end

end Li2Lean
