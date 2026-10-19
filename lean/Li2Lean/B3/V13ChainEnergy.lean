/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B3.V13ReferenceMeasure
import Li2Lean.B3.V13ReferenceEnergyTerm
import Li2Lean.Kit.LogRectangle

/-!
The logarithmic self-energy of the finite chain measure used by v13 rows.

The row convention includes a closing jump.  The density construction itself
uses only the jumps before the final endpoint, so a row-level identity must
state charge neutrality explicitly.
-/

namespace Li2Lean

noncomputable section

namespace B3

open MeasureTheory Set
open V.EnergyCertI
open V.EnergyCertI.IK

/-! ## Closed jumps

`IData.jumpsI` appends the terminal negative prefix.  The small real-valued
mirror below makes its neutrality explicit before the measure layer is used.
-/

def realJumps (prev : ℝ) : List ℝ → List ℝ
  | [] => [-prev]
  | h :: hs => (h - prev) :: realJumps h hs

lemma realJumps_sum (prev : ℝ) (hs : List ℝ) :
    (realJumps prev hs).sum = -prev := by
  induction hs generalizing prev with
  | nil => simp [realJumps]
  | cons h hs ih =>
      simp only [realJumps, List.sum_cons]
      rw [ih h]
      ring

lemma realJumps_sum_zero (hs : List ℝ) :
    (realJumps 0 hs).sum = 0 := by
  simpa using realJumps_sum 0 hs

lemma val_jumpsI {prev : QF} (hs : List QF) (hp : 0 < prev.2)
    (hhs : ∀ a ∈ hs, 0 < a.2) :
    (jumpsI prev hs).map val = realJumps (val prev) (hs.map val) := by
  induction hs generalizing prev with
  | nil => simp [jumpsI, realJumps, val_qneg]
  | cons h hs ih =>
      have hh : 0 < h.2 := hhs h (by simp)
      have htail : ∀ a ∈ hs, 0 < a.2 := by
        intro a ha
        exact hhs a (by simp [ha])
      simp only [jumpsI, List.map_cons, realJumps]
      rw [val_qsub hh hp]
      simp only [ih hh htail]

theorem val_jumpsI_sum {prev : QF} (hs : List QF) (hp : 0 < prev.2)
    (hhs : ∀ a ∈ hs, 0 < a.2) :
    ((jumpsI prev hs).map val).sum = -val prev := by
  rw [val_jumpsI hs hp hhs]
  exact realJumps_sum _ _

theorem val_jumpsI_zero_sum (hs : List QF) (hhs : ∀ a ∈ hs, 0 < a.2) :
    ((jumpsI (0, 1) hs).map val).sum = 0 := by
  have h := val_jumpsI_sum (prev := (0, 1)) hs (by norm_num) hhs
  norm_num [val] at h ⊢
  exact h

def endpointJump (n : ℕ) (h : ℕ → ℝ) (k : ℕ) : ℝ :=
  (if k < n then h k else 0) - (if k = 0 then 0 else h (k - 1))

lemma endpointJump_eq_of_lt {n k : ℕ} (h : ℕ → ℝ) (hk : k < n) :
    endpointJump n h k = endpointJump (n + 1) h k := by
  simp [endpointJump, hk, Nat.lt_succ_of_lt hk]

lemma endpointJump_succ_last (n : ℕ) (h : ℕ → ℝ) :
    endpointJump (n + 1) h n = endpointJump n h n + h n := by
  by_cases hn : n = 0
  · subst n
    simp [endpointJump]
  · simp [endpointJump, hn]
    ring

lemma endpointJump_succ_end (n : ℕ) (h : ℕ → ℝ) :
    endpointJump (n + 1) h (n + 1) = -h n := by
  simp [endpointJump]

theorem sum_prefix_sbp (n : ℕ) (h f : ℕ → ℝ) :
    (∑ i ∈ Finset.range n, h i * (f (i + 1) - f i)) =
      -(∑ k ∈ Finset.range (n + 1), endpointJump n h k * f k) := by
  induction n with
  | zero => simp [endpointJump]
  | succ n ih =>
      have hsum :
          (∑ k ∈ Finset.range n, endpointJump (n + 1) h k * f k) =
            ∑ k ∈ Finset.range n, endpointJump n h k * f k := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [endpointJump_eq_of_lt h (Finset.mem_range.mp hk)]
      calc
        (∑ i ∈ Finset.range (n + 1), h i * (f (i + 1) - f i)) =
            (∑ i ∈ Finset.range n, h i * (f (i + 1) - f i)) +
              h n * (f (n + 1) - f n) := by
          rw [Finset.sum_range_succ]
        _ = -(∑ k ∈ Finset.range (n + 1), endpointJump n h k * f k) +
              h n * (f (n + 1) - f n) := by rw [ih]
        _ = -(∑ k ∈ Finset.range n, endpointJump n h k * f k +
              endpointJump n h n * f n + h n * f n - h n * f (n + 1)) := by
          rw [Finset.sum_range_succ]
          ring
        _ = -(∑ k ∈ Finset.range (n + 2), endpointJump (n + 1) h k * f k) := by
          rw [Finset.sum_range_succ, Finset.sum_range_succ]
          rw [hsum, endpointJump_succ_last, endpointJump_succ_end]
          ring

/-- Sum the first `k` jumps.  The density on cell `k` is the sum of jumps
through that cell, so its discrete boundary is the original jump sequence. -/
def prefixJumpSum (j : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range k, j i

lemma prefixJumpSum_succ (j : ℕ → ℝ) (k : ℕ) :
    prefixJumpSum j (k + 1) = prefixJumpSum j k + j k := by
  simp [prefixJumpSum, Finset.sum_range_succ]

theorem endpointJump_prefix_interior {n k : ℕ} (j : ℕ → ℝ) (hk : k < n) :
    endpointJump n (fun i => prefixJumpSum j (i + 1)) k = j k := by
  by_cases hk0 : k = 0
  · subst k
    simp [endpointJump, prefixJumpSum, hk]
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
    have hsum := prefixJumpSum_succ j k
    simp [endpointJump, hk, hk0, Nat.sub_add_cancel hkpos]
    rw [hsum]
    ring

theorem endpointJump_prefix_last {n : ℕ} (j : ℕ → ℝ)
    (hclosed : prefixJumpSum j (n + 1) = 0) :
    endpointJump n (fun i => prefixJumpSum j (i + 1)) n = j n := by
  by_cases hn : n = 0
  · subst n
    have hj : j 0 = 0 := by simpa [prefixJumpSum] using hclosed
    simp [endpointJump, hj]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hsum := prefixJumpSum_succ j n
    rw [hclosed] at hsum
    have hlast :
        endpointJump n (fun i => prefixJumpSum j (i + 1)) n =
          -prefixJumpSum j n := by
      simp [endpointJump, hn, Nat.sub_add_cancel hnpos]
    rw [hlast]
    linarith

theorem endpointJump_prefix_eq {n : ℕ} (j : ℕ → ℝ)
    (hclosed : prefixJumpSum j (n + 1) = 0) {k : ℕ} (hk : k ≤ n) :
    endpointJump n (fun i => prefixJumpSum j (i + 1)) k = j k := by
  rcases lt_or_eq_of_le hk with hlt | rfl
  · exact endpointJump_prefix_interior j hlt
  · exact endpointJump_prefix_last j hclosed

theorem double_prefix_sbp (n : ℕ) (h : ℕ → ℝ) (F : ℕ → ℕ → ℝ) :
    (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
      h i * h j * (F (i + 1) j - F i j - F (i + 1) (j + 1) + F i (j + 1))) =
      -(∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (n + 1),
        endpointJump n h k * endpointJump n h l * F k l) := by
  have hinner (i : ℕ) :
      (∑ j ∈ Finset.range n, h j *
        (F (i + 1) j - F i j - F (i + 1) (j + 1) + F i (j + 1))) =
        ∑ l ∈ Finset.range (n + 1), endpointJump n h l *
          (F (i + 1) l - F i l) := by
    let f : ℕ → ℝ := fun j => F (i + 1) j - F i j
    calc
      (∑ j ∈ Finset.range n, h j *
          (F (i + 1) j - F i j - F (i + 1) (j + 1) + F i (j + 1))) =
          -(∑ j ∈ Finset.range n, h j * (f (j + 1) - f j)) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        dsimp [f]
        ring
      _ = ∑ l ∈ Finset.range (n + 1), endpointJump n h l * f l := by
        rw [sum_prefix_sbp]
        ring
      _ = _ := by
        apply Finset.sum_congr rfl
        intro l hl
        rfl
  calc
    (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
        h i * h j *
          (F (i + 1) j - F i j - F (i + 1) (j + 1) + F i (j + 1))) =
        ∑ i ∈ Finset.range n, h i *
          (∑ l ∈ Finset.range (n + 1), endpointJump n h l *
            (F (i + 1) l - F i l)) := by
      apply Finset.sum_congr rfl
      intro i hi
      calc
        (∑ j ∈ Finset.range n, h i * h j *
            (F (i + 1) j - F i j - F (i + 1) (j + 1) + F i (j + 1))) =
            ∑ j ∈ Finset.range n, h i * (h j *
              (F (i + 1) j - F i j - F (i + 1) (j + 1) + F i (j + 1))) := by
                apply Finset.sum_congr rfl
                intro j hj
                ring
        _ = h i * (∑ j ∈ Finset.range n, h j *
              (F (i + 1) j - F i j - F (i + 1) (j + 1) + F i (j + 1))) := by
                rw [Finset.mul_sum]
        _ = h i * (∑ l ∈ Finset.range (n + 1), endpointJump n h l *
              (F (i + 1) l - F i l)) := by rw [hinner]
    _ = ∑ l ∈ Finset.range (n + 1), endpointJump n h l *
          (∑ i ∈ Finset.range n, h i * (F (i + 1) l - F i l)) := by
      calc
        (∑ i ∈ Finset.range n, h i *
            (∑ l ∈ Finset.range (n + 1), endpointJump n h l *
              (F (i + 1) l - F i l))) =
            ∑ i ∈ Finset.range n, ∑ l ∈ Finset.range (n + 1),
              endpointJump n h l * (h i * (F (i + 1) l - F i l)) := by
                apply Finset.sum_congr rfl
                intro i hi
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro l hl
                ring
        _ = ∑ l ∈ Finset.range (n + 1), ∑ i ∈ Finset.range n,
              endpointJump n h l * (h i * (F (i + 1) l - F i l)) := by
                rw [Finset.sum_comm]
        _ = ∑ l ∈ Finset.range (n + 1), endpointJump n h l *
              (∑ i ∈ Finset.range n, h i * (F (i + 1) l - F i l)) := by
                apply Finset.sum_congr rfl
                intro l hl
                rw [Finset.mul_sum]
    _ = -(∑ l ∈ Finset.range (n + 1), endpointJump n h l *
          (∑ k ∈ Finset.range (n + 1), endpointJump n h k * F k l)) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro l hl
      have hsbp : (∑ i ∈ Finset.range n, h i * (F (i + 1) l - F i l)) =
          -(∑ k ∈ Finset.range (n + 1), endpointJump n h k * F k l) :=
        sum_prefix_sbp n h (fun i => F i l)
      rw [hsbp]
      ring
    _ = -(∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (n + 1),
          endpointJump n h k * endpointJump n h l * F k l) := by
      congr 1
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l hl
      ring

theorem vEnergyG_eq_secondPrimitive (s : ℝ) :
    vEnergyG s = LogSegment.secondPrimitive s := by
  by_cases hs : s = 0
  · simp [vEnergyG, LogSegment.secondPrimitive, hs]
  · simp [vEnergyG, LogSegment.secondPrimitive, hs]
    ring

theorem restrict_Ioc_eq_Ico_local (a b : ℝ) :
    volume.restrict (Ioc a b) = volume.restrict (Ico a b) := by
  exact (Measure.restrict_congr_set Ioc_ae_eq_Icc).trans
    (Measure.restrict_congr_set Ico_ae_eq_Icc).symm

theorem integral_log_abs_sub_Ioc_rectangle_eq_vEnergyG
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    (∫ p : ℝ × ℝ, Real.log |p.1 - p.2|
      ∂((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc c d)))) =
      vEnergyG (b - c) - vEnergyG (a - c) -
        vEnergyG (b - d) + vEnergyG (a - d) := by
  rw [restrict_Ioc_eq_Ico_local, restrict_Ioc_eq_Ico_local,
    LogSegment.integral_log_abs_sub_rectangle hab hcd]
  simp only [vEnergyG_eq_secondPrimitive]

/-- The logarithmic interaction of two actual constant-density chain cells
is the density product times the exact endpoint formula. -/
theorem v13ChainCellPairInteraction
    (a b : V13ChainCell) (ha : a.left ≤ a.right)
    (hb : b.left ≤ b.right) (hda : 0 ≤ a.density)
    (hdb : 0 ≤ b.density) :
    (∫ p : ℝ × ℝ, Real.log |p.1 - p.2|
      ∂((ENNReal.ofReal a.density • volume.restrict (Ioc a.left a.right)).prod
        (ENNReal.ofReal b.density • volume.restrict (Ioc b.left b.right)))) =
      a.density * b.density *
        (vEnergyG (a.right - b.left) - vEnergyG (a.left - b.left) -
          vEnergyG (a.right - b.right) + vEnergyG (a.left - b.right)) := by
  let μa := volume.restrict (Ioc a.left a.right)
  let μb := volume.restrict (Ioc b.left b.right)
  let ca := ENNReal.ofReal a.density
  let cb := ENNReal.ofReal b.density
  have hprod : (ca • μa).prod (cb • μb) = (ca * cb) • (μa.prod μb) := by
    rw [Measure.prod_smul_left, Measure.prod_smul_right]
    simp [smul_smul]
  have hint : Integrable (fun p : ℝ × ℝ => Real.log |p.1 - p.2|)
      (μa.prod μb) := by
    change Integrable (fun p : ℝ × ℝ => Real.log |p.1 - p.2|)
      ((volume.restrict (Ioc a.left a.right)).prod
        (volume.restrict (Ioc b.left b.right)))
    rw [restrict_Ioc_eq_Ico_local, restrict_Ioc_eq_Ico_local]
    exact LogSegment.integrable_log_abs_sub_rectangle hb
  have hcoef : (ca * cb).toReal = a.density * b.density := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hda,
      ENNReal.toReal_ofReal hdb]
  rw [show (ENNReal.ofReal a.density • volume.restrict (Ioc a.left a.right)).prod
      (ENNReal.ofReal b.density • volume.restrict (Ioc b.left b.right)) =
        (ca * cb) • (μa.prod μb) by exact hprod]
  rw [integral_smul_measure, hcoef, smul_eq_mul]
  rw [integral_log_abs_sub_Ioc_rectangle_eq_vEnergyG ha hb]

/-- The piecewise-constant density obtained by prefixing a neutral list of
jumps has the exact finite logarithmic interaction of those jumps.  The
left side is the sum of cell-pair rectangle energies; the right side is the
closed jump-pair evaluator used by `vEnergySelfRow`. -/
theorem prefixDensity_rectangleEnergy_eq_closedJumpEnergy
    (n : ℕ) (x jumps : ℕ → ℝ)
    (hclosed : prefixJumpSum jumps (n + 1) = 0) :
    (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
      prefixJumpSum jumps (i + 1) * prefixJumpSum jumps (j + 1) *
        (vEnergyG (x (i + 1) - x j) - vEnergyG (x i - x j) -
          vEnergyG (x (i + 1) - x (j + 1)) +
            vEnergyG (x i - x (j + 1)))) =
      -(∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (n + 1),
        jumps k * jumps l * vEnergyG (x k - x l)) := by
  have hsbp := double_prefix_sbp n
    (fun i => prefixJumpSum jumps (i + 1))
    (fun k l => vEnergyG (x k - x l))
  have hjump (k : ℕ) (hk : k ∈ Finset.range (n + 1)) :
      endpointJump n (fun i => prefixJumpSum jumps (i + 1)) k = jumps k := by
    apply endpointJump_prefix_eq jumps hclosed
    exact Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  calc
    _ = -(∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (n + 1),
        endpointJump n (fun i => prefixJumpSum jumps (i + 1)) k *
          endpointJump n (fun i => prefixJumpSum jumps (i + 1)) l *
            vEnergyG (x k - x l)) := hsbp
    _ = -(∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (n + 1),
        jumps k * jumps l * vEnergyG (x k - x l)) := by
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro l hl
      rw [hjump k hk, hjump l hl]

/-! A concrete finite-chain specialization.  The hypotheses are exactly the
endpoint ordering, nonnegative density, and closing-jump conditions needed by
the measure construction; no evaluator term or certificate bound is hidden in
this interface. -/

def v13PrefixChainCell (x jumps : ℕ → ℝ) (i : ℕ) : V13ChainCell :=
  { left := x i
    right := x (i + 1)
    density := prefixJumpSum jumps (i + 1) }

def v13PrefixChainCellMeasure (x jumps : ℕ → ℝ) (i : ℕ) : Measure ℝ :=
  ENNReal.ofReal (v13PrefixChainCell x jumps i).density •
    volume.restrict (Ioc (v13PrefixChainCell x jumps i).left
      (v13PrefixChainCell x jumps i).right)

def v13PrefixPairIntegral (x jumps : ℕ → ℝ) (i j : ℕ) : ℝ :=
  ∫ p : ℝ × ℝ, Real.log |p.1 - p.2| ∂
    ((v13PrefixChainCellMeasure x jumps i).prod
      (v13PrefixChainCellMeasure x jumps j))

theorem v13PrefixChain_pairIntegral_eq_closedJumpEnergy
    (n : ℕ) (x jumps : ℕ → ℝ)
    (hclosed : prefixJumpSum jumps (n + 1) = 0)
    (hordered : ∀ i < n, x i ≤ x (i + 1))
    (hdensity : ∀ i < n, 0 ≤ prefixJumpSum jumps (i + 1)) :
    (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
      v13PrefixPairIntegral x jumps i j) =
      -(∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (n + 1),
        jumps k * jumps l * vEnergyG (x k - x l)) := by
  calc
    _ = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
        prefixJumpSum jumps (i + 1) * prefixJumpSum jumps (j + 1) *
          (vEnergyG (x (i + 1) - x j) - vEnergyG (x i - x j) -
            vEnergyG (x (i + 1) - x (j + 1)) +
              vEnergyG (x i - x (j + 1))) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      have hp := v13ChainCellPairInteraction
        (v13PrefixChainCell x jumps i) (v13PrefixChainCell x jumps j)
        (hordered i (Finset.mem_range.mp hi))
        (hordered j (Finset.mem_range.mp hj))
        (hdensity i (Finset.mem_range.mp hi))
        (hdensity j (Finset.mem_range.mp hj))
      simpa [v13PrefixPairIntegral, v13PrefixChainCellMeasure,
        v13PrefixChainCell] using hp
    _ = _ := prefixDensity_rectangleEnergy_eq_closedJumpEnergy n x jumps hclosed

theorem v13ChainMeasure_eq_list_sum (cells : List V13ChainCell) :
    v13ChainMeasure cells =
      (cells.map fun c => ENNReal.ofReal c.density •
        (volume.restrict (Ioc c.left c.right))).sum := by
  induction cells with
  | nil => simp [v13ChainMeasure]
  | cons c cs ih =>
      change ENNReal.ofReal c.density • volume.restrict (Ioc c.left c.right) +
        v13ChainMeasure cs = _
      rw [ih]
      rfl

theorem restrict_Ioc_eq_Ico (a b : ℝ) :
    volume.restrict (Ioc a b) = volume.restrict (Ico a b) := by
  exact (Measure.restrict_congr_set Ioc_ae_eq_Icc).trans
    (Measure.restrict_congr_set Ico_ae_eq_Icc).symm

theorem integrable_log_abs_sub_Ioc_rectangle {a b c d : ℝ} (_hab : a ≤ b)
    (hcd : c ≤ d) :
    Integrable (fun p : ℝ × ℝ => Real.log |p.1 - p.2|)
      ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc c d))) := by
  rw [restrict_Ioc_eq_Ico, restrict_Ioc_eq_Ico]
  exact LogSegment.integrable_log_abs_sub_rectangle hcd

theorem integral_log_abs_sub_Ioc_rectangle {a b c d : ℝ} (hab : a ≤ b)
    (hcd : c ≤ d) :
    (∫ p : ℝ × ℝ, Real.log |p.1 - p.2|
      ∂((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc c d)))) =
      LogSegment.secondPrimitive (b - c) - LogSegment.secondPrimitive (a - c) -
        LogSegment.secondPrimitive (b - d) + LogSegment.secondPrimitive (a - d) := by
  rw [restrict_Ioc_eq_Ico, restrict_Ioc_eq_Ico]
  exact LogSegment.integral_log_abs_sub_rectangle hab hcd

/-- The logarithmic potential on a reflected interval, with the endpoint
orientation retained explicitly. -/
theorem integrable_log_sub_Ioc (δ a b : ℝ) (hab : a ≤ b) :
    Integrable (fun t : ℝ => Real.log (δ - t)) (volume.restrict (Ioc a b)) := by
  rw [restrict_Ioc_eq_Ico]
  apply (intervalIntegrable_iff_integrableOn_Ico_of_le hab).mp
  have hi : IntervalIntegrable (fun t : ℝ => Real.log (δ - t)) volume a b := by
    have h :=
      (intervalIntegral.intervalIntegrable_log' (a := δ - a) (b := δ - b)).comp_sub_left δ
    convert h using 1 <;> ring
  exact hi

theorem integral_log_sub_Ioc (δ a b : ℝ) (hab : a ≤ b) :
    (∫ t : ℝ, Real.log (δ - t) ∂(volume.restrict (Ioc a b))) =
      LogSegment.primitive (δ - a) - LogSegment.primitive (δ - b) := by
  rw [restrict_Ioc_eq_Ico, MeasureTheory.integral_Ico_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hab]
  calc
    (∫ t in a..b, Real.log (δ - t)) =
        ∫ x in -b..-a, Real.log (δ + x) := by
      simpa only [sub_eq_add_neg] using
        (intervalIntegral.integral_comp_neg
          (fun x : ℝ => Real.log (δ + x)) (a := a) (b := b))
    _ = LogSegment.primitive (δ - a) - LogSegment.primitive (δ - b) := by
      simpa [sub_eq_add_neg] using LogSegment.integral_log_add δ (-b) (-a)

noncomputable def v13ChainFirstPotentialNeg (δ : ℝ) : List CP → ℝ
  | [] => 0
  | p :: _ => -LogSegment.primitive (δ - IK.val p.e)

theorem integrable_v13Chain_log_sub_aux (h δ : ℝ) (rows : List CP) :
    Integrable (fun t : ℝ => Real.log (δ - t))
      (v13ChainMeasure (v13ChainCellsAux h rows)) := by
  induction rows generalizing h with
  | nil => simp [v13ChainCellsAux, v13ChainMeasure]
  | cons p rows ih =>
    cases rows with
    | nil => simp [v13ChainCellsAux, v13ChainMeasure]
    | cons q rest =>
      change Integrable _
        ((ENNReal.ofReal (h + IK.val p.J) • volume.restrict
          (Ioc (IK.val p.e) (IK.val q.e))) +
          v13ChainMeasure (v13ChainCellsAux (h + IK.val p.J) (q :: rest)))
      apply (integrable_add_measure).mpr
      constructor
      · have hbase : Integrable (fun t : ℝ => Real.log (δ - t))
            (volume.restrict (Ioc (IK.val p.e) (IK.val q.e))) := by
          by_cases hpq : IK.val p.e ≤ IK.val q.e
          · exact integrable_log_sub_Ioc δ _ _ hpq
          · have hempty : Ioc (IK.val p.e) (IK.val q.e) = ∅ := by
              have hqp : IK.val q.e < IK.val p.e := lt_of_not_ge hpq
              ext t
              simp only [Set.mem_Ioc, Set.mem_empty_iff_false]
              constructor
              · rintro ⟨hpt, htq⟩
                exact (not_lt_of_ge (le_of_lt hpt))
                  (lt_of_le_of_lt htq hqp)
              · intro hfalse
                exact hfalse.elim
            simp [hempty]
        exact hbase.smul_measure ENNReal.ofReal_ne_top
      · exact ih (h + IK.val p.J)

theorem integral_v13Chain_log_sub_aux (h δ : ℝ) (rows : List CP)
    (hclosed : (rows.map fun p => IK.val p.J).sum = -h)
    (hordered : rows.Pairwise (fun p q => IK.val p.e ≤ IK.val q.e))
    (hnonneg : ∀ c ∈ v13ChainCellsAux h rows, 0 ≤ c.density) :
    (∫ t : ℝ, Real.log (δ - t) ∂v13ChainMeasure (v13ChainCellsAux h rows)) =
      -h * v13ChainFirstPotentialNeg δ rows -
        (rows.map fun p => IK.val p.J *
          (-LogSegment.primitive (δ - IK.val p.e))).sum := by
  induction rows generalizing h with
  | nil => simp [v13ChainCellsAux, v13ChainMeasure, v13ChainFirstPotentialNeg]
  | cons p rows ih =>
      cases rows with
      | nil =>
          simp [v13ChainCellsAux, v13ChainMeasure, v13ChainFirstPotentialNeg] at hclosed ⊢
          rw [hclosed]
          ring
      | cons q rest =>
          simp only [List.pairwise_cons] at hordered
          rcases hordered with ⟨hfirst, htailOrdered⟩
          have hpq : IK.val p.e ≤ IK.val q.e := hfirst q (by simp)
          have htailOrdered' : List.Pairwise
              (fun p q => IK.val p.e ≤ IK.val q.e) (q :: rest) := by
            simpa only [List.pairwise_cons] using htailOrdered
          have hcell : 0 ≤ h + IK.val p.J := by
            exact hnonneg
              { left := IK.val p.e, right := IK.val q.e,
                density := h + IK.val p.J }
              (by
                simp only [v13ChainCellsAux, List.mem_cons]
                exact Or.inl trivial)
          have hnonnegTail :
              ∀ c ∈ v13ChainCellsAux (h + IK.val p.J) (q :: rest),
                0 ≤ c.density := by
            intro c hc
            apply hnonneg c
            simp only [v13ChainCellsAux, List.mem_cons]
            exact Or.inr hc
          have hclosedTail :
              ((q :: rest).map fun r => IK.val r.J).sum = -(h + IK.val p.J) := by
            have hx : IK.val p.J +
                ((q :: rest).map fun r => IK.val r.J).sum = -h := by
              simpa only [List.map_cons, List.sum_cons] using hclosed
            linarith
          have hprefix := ih (h + IK.val p.J) hclosedTail htailOrdered'
            hnonnegTail
          have hfirstInt :
              (∫ t : ℝ, Real.log (δ - t) ∂
                (ENNReal.ofReal (h + IK.val p.J) •
                  volume.restrict (Ioc (IK.val p.e) (IK.val q.e)))) =
                (h + IK.val p.J) *
                  (LogSegment.primitive (δ - IK.val p.e) -
                    LogSegment.primitive (δ - IK.val q.e)) := by
            rw [integral_smul_measure,
              ENNReal.toReal_ofReal hcell, smul_eq_mul,
              integral_log_sub_Ioc δ _ _ hpq]
          have hdecomp :
              v13ChainMeasure (v13ChainCellsAux h (p :: q :: rest)) =
                (ENNReal.ofReal (h + IK.val p.J) •
                  volume.restrict (Ioc (IK.val p.e) (IK.val q.e))) +
                  v13ChainMeasure (v13ChainCellsAux (h + IK.val p.J) (q :: rest)) := by
            rfl
          rw [hdecomp, integral_add_measure
            (by
              exact (integrable_log_sub_Ioc δ _ _ hpq).smul_measure
                ENNReal.ofReal_ne_top)
            (integrable_v13Chain_log_sub_aux (h + IK.val p.J) δ (q :: rest))]
          rw [hfirstInt, hprefix]
          simp only [List.map_cons, List.sum_cons, v13ChainFirstPotentialNeg]
          ring

lemma list_sum_mul_neg_primitive (δ : ℝ) (rows : List CP) :
    (rows.map fun p => IK.val p.J *
      (-LogSegment.primitive (δ - IK.val p.e))).sum =
    -(rows.map fun p => IK.val p.J *
      LogSegment.primitive (δ - IK.val p.e)).sum := by
  induction rows with
  | nil => simp
  | cons p rows ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [mul_neg, ih]
      ring

theorem integral_v13Chain_log_sub (δ : ℝ) (rows : List CP)
    (hclosed : (rows.map fun p => IK.val p.J).sum = 0)
    (hordered : rows.Pairwise (fun p q => IK.val p.e ≤ IK.val q.e))
    (hnonneg : ∀ c ∈ v13ChainCells rows, 0 ≤ c.density) :
    (∫ t : ℝ, Real.log (δ - t) ∂v13ChainMeasure (v13ChainCells rows)) =
      (rows.map fun p => IK.val p.J *
        LogSegment.primitive (δ - IK.val p.e)).sum := by
  have h := integral_v13Chain_log_sub_aux (0 : ℝ) δ rows
    (by simpa using hclosed) hordered
    (by simpa [v13ChainCells] using hnonneg)
  simp only [v13ChainCells] at h ⊢
  rw [h, list_sum_mul_neg_primitive]
  ring

theorem integrable_log_add_Ioc (δ a b : ℝ) (hab : a ≤ b) :
    Integrable (fun t : ℝ => Real.log (t + δ)) (volume.restrict (Ioc a b)) := by
  rw [restrict_Ioc_eq_Ico]
  apply (intervalIntegrable_iff_integrableOn_Ico_of_le hab).mp
  have hi : IntervalIntegrable (fun t : ℝ => Real.log (t + δ)) volume a b := by
    have h := (intervalIntegral.intervalIntegrable_log' (a := δ + a)
      (b := δ + b)).comp_add_left δ
    simpa [add_comm] using h
  exact hi

theorem integral_log_add_Ioc (δ a b : ℝ) (hab : a ≤ b) :
    (∫ t : ℝ, Real.log (t + δ) ∂(volume.restrict (Ioc a b))) =
      LogSegment.primitive (δ + b) - LogSegment.primitive (δ + a) := by
  rw [restrict_Ioc_eq_Ico, MeasureTheory.integral_Ico_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hab]
  simpa [add_comm] using LogSegment.integral_log_add δ a b

noncomputable def v13ChainFirstPotential (δ : ℝ) : List CP → ℝ
  | [] => 0
  | p :: _ => LogSegment.primitive (δ + IK.val p.e)

theorem integrable_v13Chain_log_add_aux (h δ : ℝ) (rows : List CP) :
    Integrable (fun t : ℝ => Real.log (t + δ))
      (v13ChainMeasure (v13ChainCellsAux h rows)) := by
  induction rows generalizing h with
  | nil => simp [v13ChainCellsAux, v13ChainMeasure]
  | cons p rows ih =>
    cases rows with
    | nil => simp [v13ChainCellsAux, v13ChainMeasure]
    | cons q rest =>
      change Integrable _
        ((ENNReal.ofReal (h + IK.val p.J) • volume.restrict
          (Ioc (IK.val p.e) (IK.val q.e))) +
          v13ChainMeasure (v13ChainCellsAux (h + IK.val p.J) (q :: rest)))
      apply (integrable_add_measure).mpr
      constructor
      · have hbase : Integrable (fun t : ℝ => Real.log (t + δ))
            (volume.restrict (Ioc (IK.val p.e) (IK.val q.e))) := by
          by_cases hpq : IK.val p.e ≤ IK.val q.e
          · exact integrable_log_add_Ioc δ _ _ hpq
          · have hempty : Ioc (IK.val p.e) (IK.val q.e) = ∅ := by
              have hqp : IK.val q.e < IK.val p.e := lt_of_not_ge hpq
              ext t
              simp only [Set.mem_Ioc, Set.mem_empty_iff_false]
              constructor
              · rintro ⟨hpt, htq⟩
                exact (not_lt_of_ge (le_of_lt hpt))
                  (lt_of_le_of_lt htq hqp)
              · intro hfalse
                exact hfalse.elim
            simp [hempty]
        exact hbase.smul_measure ENNReal.ofReal_ne_top
      · exact ih (h + IK.val p.J)

theorem integral_v13Chain_log_add_aux (h δ : ℝ) (rows : List CP)
    (hclosed : (rows.map fun p => IK.val p.J).sum = -h)
    (hordered : rows.Pairwise (fun p q => IK.val p.e ≤ IK.val q.e))
    (hnonneg : ∀ c ∈ v13ChainCellsAux h rows, 0 ≤ c.density) :
    (∫ t : ℝ, Real.log (t + δ) ∂v13ChainMeasure (v13ChainCellsAux h rows)) =
      -h * v13ChainFirstPotential δ rows -
        (rows.map fun p => IK.val p.J *
          LogSegment.primitive (δ + IK.val p.e)).sum := by
  induction rows generalizing h with
  | nil => simp [v13ChainCellsAux, v13ChainMeasure, v13ChainFirstPotential]
  | cons p rows ih =>
      cases rows with
      | nil =>
          simp [v13ChainCellsAux, v13ChainMeasure, v13ChainFirstPotential] at hclosed ⊢
          rw [hclosed]
          ring
      | cons q rest =>
          simp only [List.pairwise_cons] at hordered
          rcases hordered with ⟨hfirst, htailOrdered⟩
          have hpq : IK.val p.e ≤ IK.val q.e := hfirst q (by simp)
          have htailOrdered' : List.Pairwise
              (fun p q => IK.val p.e ≤ IK.val q.e) (q :: rest) := by
            simpa only [List.pairwise_cons] using htailOrdered
          have hcell : 0 ≤ h + IK.val p.J := by
            exact hnonneg
              { left := IK.val p.e, right := IK.val q.e,
                density := h + IK.val p.J }
              (by
                simp only [v13ChainCellsAux, List.mem_cons]
                exact Or.inl trivial)
          have hnonnegTail :
              ∀ c ∈ v13ChainCellsAux (h + IK.val p.J) (q :: rest),
                0 ≤ c.density := by
            intro c hc
            apply hnonneg c
            simp only [v13ChainCellsAux, List.mem_cons]
            exact Or.inr hc
          have hclosedTail :
              ((q :: rest).map fun r => IK.val r.J).sum = -(h + IK.val p.J) := by
            have hx : IK.val p.J +
                ((q :: rest).map fun r => IK.val r.J).sum = -h := by
              simpa only [List.map_cons, List.sum_cons] using hclosed
            linarith
          have hprefix := ih (h + IK.val p.J) hclosedTail htailOrdered'
            hnonnegTail
          have hfirstInt :
              (∫ t : ℝ, Real.log (t + δ) ∂
                (ENNReal.ofReal (h + IK.val p.J) •
                  volume.restrict (Ioc (IK.val p.e) (IK.val q.e)))) =
                (h + IK.val p.J) *
                  (LogSegment.primitive (δ + IK.val q.e) -
                    LogSegment.primitive (δ + IK.val p.e)) := by
            rw [integral_smul_measure,
              ENNReal.toReal_ofReal hcell, smul_eq_mul,
              integral_log_add_Ioc δ _ _ hpq]
          have hdecomp :
              v13ChainMeasure (v13ChainCellsAux h (p :: q :: rest)) =
                (ENNReal.ofReal (h + IK.val p.J) •
                  volume.restrict (Ioc (IK.val p.e) (IK.val q.e))) +
                  v13ChainMeasure (v13ChainCellsAux (h + IK.val p.J) (q :: rest)) := by
            rfl
          rw [hdecomp, integral_add_measure
            (by
              exact (integrable_log_add_Ioc δ _ _ hpq).smul_measure
                ENNReal.ofReal_ne_top)
            (integrable_v13Chain_log_add_aux (h + IK.val p.J) δ (q :: rest))]
          rw [hfirstInt, hprefix]
          simp only [List.map_cons, List.sum_cons, v13ChainFirstPotential]
          ring

theorem integral_v13Chain_log_add (δ : ℝ) (rows : List CP)
    (hclosed : (rows.map fun p => IK.val p.J).sum = 0)
    (hordered : rows.Pairwise (fun p q => IK.val p.e ≤ IK.val q.e))
    (hnonneg : ∀ c ∈ v13ChainCells rows, 0 ≤ c.density) :
    (∫ t : ℝ, Real.log (t + δ) ∂v13ChainMeasure (v13ChainCells rows)) =
      -(rows.map fun p => IK.val p.J *
        LogSegment.primitive (δ + IK.val p.e)).sum := by
  have h := integral_v13Chain_log_add_aux (0 : ℝ) δ rows
    (by simpa using hclosed) hordered
    (by simpa [v13ChainCells] using hnonneg)
  simpa [v13ChainCells] using h

end B3

end

end Li2Lean
