/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.Q11ContourRows
import Li2Lean.P0.CA.Contour.Checker
import Li2Lean.P0.CA.Receipt.Checks
import Li2Lean.Agents.F_L8.Types
import Li2Lean.P0.Q11CA.Contour.Q11ContourEvalAndBound

/-!
# H7-contour (Part 2): Reflected Group Checker, Conjugation Symmetry, and `Q11GammaContourCertificate` Constructor

This module completes the analytical and reflected-checker pipeline for the
`q = 11` ellipse contour floor `∀ z ∈ Gamma, ratioToReal etaFloor ≤ q11Weta z`:

1. **Even / conjugation symmetry on the full turn**:
   Proves `q11WformClosed (-θ) = q11WformClosed θ`,
   `q11Weta (gammaPoint (2 * Real.pi - θ)) = q11Weta (gammaPoint θ)`, and
   `q11Weta (gammaPoint (2 * Real.pi * (1 - u))) = q11Weta (gammaPoint (2 * Real.pi * u))`.
2. **Reflected cell and group checker (`q11CheckCellFrom`, `q11CheckGrpFrom`, `q11CheckGrp`, `q11AllGrp`)**:
   Adapts `Li2Lean.P0.CA.Contour.Checker` to `q11Wform` using the Taylor bound
   `q11_taylor_lower` (`|q11W2| ≤ 2200`, quadratic coefficient `1100`) and
   interval evaluators `q11WIFrom` / `q11DIFrom` / `q11WDIFrom` from
   `Q11ContourEvalAndBound.lean`.
   Also provides `q11BTabOk` so data shards can share a single pre-evaluated
   48-entry rational interval table `bTab : List QI` for `q11BR`.
3. **Full-turn certificate constructor (`q11GammaContourCertificate_of_groupsFrom`, `q11GammaContourCertificate_of_groups`)**:
   Duplicates any verified upper-half cell chain `groups : List Grp` covering
   `[0, 1]` (angles `θ = π v ∈ [0, π]`) into upper-half and reflected lower-half
   `Q11GammaRow`s covering `u ∈ [0, 1]` (angles `2π u ∈ [0, 2π]`), and constructs
   `Q11GammaContourCertificate` (`Li2Lean/P0/Q11ContourRows.lean:132`).
-/

open MeasureTheory Set
open scoped BigOperators

namespace Li2Lean.P0.Q11Data

noncomputable section

open Li2Lean.F_L8
open Li2Lean.P0.CA.Contour
open Li2Lean.P0.CA.Contour.QI
open Li2Lean.P0.CA.Receipt

/-! ## 1. Evenness and Full-Turn Reflection Symmetry of `q11Weta` on `Gamma` -/

theorem Gr_neg_right (s Y : ℝ) : Gr s (-Y) = Gr s Y := by
  unfold Gr
  rw [neg_sq, div_neg, Real.arctan_neg, mul_neg, neg_mul, neg_neg]

theorem q11SegForm_neg_right (X Y : ℝ) :
    q11SegForm X (-Y) = q11SegForm X Y := by
  unfold q11SegForm
  congr 1
  funext κ
  exact Gr_neg_right (X + κ) Y

theorem ellX_neg (θ : ℝ) : ellX (-θ) = ellX θ := by
  unfold ellX
  rw [Real.cos_neg]

theorem ellY_neg (θ : ℝ) : ellY (-θ) = -ellY θ := by
  unfold ellY
  rw [Real.sin_neg, mul_neg]

theorem q11ContourPotentialFourier_neg (θ : ℝ) :
    q11ContourPotentialFourier (-θ) = q11ContourPotentialFourier θ := by
  rw [q11Fourier_eq, q11Fourier_eq]
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  rw [mul_neg, Real.cos_neg]

theorem q11WformClosed_neg (θ : ℝ) :
    q11WformClosed (-θ) = q11WformClosed θ := by
  unfold q11WformClosed
  rw [ellX_neg, ellY_neg, q11SegForm_neg_right, q11ContourPotentialFourier_neg]

theorem q11Wform_neg (θ : ℝ) : q11Wform (-θ) = q11Wform θ := by
  rw [q11Wform_eq_closed, q11Wform_eq_closed, q11WformClosed_neg]

theorem gammaPoint_two_pi_sub (θ : ℝ) :
    gammaPoint (2 * Real.pi - θ) = gammaPoint (-θ) := by
  have h : 2 * Real.pi - θ = -θ + ((1 : ℤ) : ℝ) * (2 * Real.pi) := by
    push_cast
    ring
  unfold gammaPoint
  rw [h, Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]

theorem q11Weta_gammaPoint_two_pi_sub (θ : ℝ) :
    q11Weta (gammaPoint (2 * Real.pi - θ)) = q11Weta (gammaPoint θ) := by
  rw [gammaPoint_two_pi_sub]
  exact q11Wform_neg θ

theorem q11Weta_gammaPoint_symm (u : ℝ) :
    q11Weta (gammaPoint (2 * Real.pi * (1 - u))) =
      q11Weta (gammaPoint (2 * Real.pi * u)) := by
  rw [show 2 * Real.pi * (1 - u) = 2 * Real.pi - 2 * Real.pi * u by ring]
  exact q11Weta_gammaPoint_two_pi_sub (2 * Real.pi * u)

theorem q11Weta_gammaPoint_two_mul (u : ℝ) :
    q11Weta (gammaPoint (2 * Real.pi * u)) = q11Wform (Real.pi * (2 * u)) := by
  unfold q11Wform
  rw [show 2 * Real.pi * u = Real.pi * (2 * u) by ring]

/-! ## 2. Parametric and Default Reflected Interval Evaluators -/

def q11WIFrom (b : ℕ → QI) (c s : ℚ) : QI :=
  q11WIcore (ellXq c) (q11PEdges (ellXq c) (ellYq s)) (q11FEdges (ellXq c) (ellYq s))
    (edge (ellXq c) (ellYq s)) (edge (ellXq c - 2) (ellYq s)) (q11FstateFrom b c s 48)

def q11DIFrom (b : ℕ → QI) (c s : ℚ) : QI :=
  q11DIcore (-(12783 / 10000) * s) (229 / 200 * c) (q11PEdges (ellXq c) (ellYq s))
    (q11FEdges (ellXq c) (ellYq s)) (edge (ellXq c) (ellYq s)) (edge (ellXq c - 2) (ellYq s))
    (q11FstateFrom b c s 48)

def q11WDIFrom (b : ℕ → QI) (c s : ℚ) : QI × QI :=
  let X := ellXq c
  let Y := ellYq s
  let pe := q11PEdges X Y
  let fe := q11FEdges X Y
  let e0 := edge X Y
  let e2 := edge (X - 2) Y
  let F := q11FstateFrom b c s 48
  (q11WIcore X pe fe e0 e2 F, q11DIcore (-(12783 / 10000) * s) (229 / 200 * c) pe fe e0 e2 F)

theorem q11WDIFrom_eq (b : ℕ → QI) (c s : ℚ) :
    q11WDIFrom b c s = (q11WIFrom b c s, q11DIFrom b c s) := rfl

theorem q11WIFrom_mem {b : ℕ → QI} (hb : ∀ k < 48, (b k).mem (q11BR k))
    {θ : ℝ} {c s : ℚ} (hc : Real.cos θ = c) (hs : Real.sin θ = s) :
    (q11WIFrom b c s).mem (q11Wform θ) := by
  rw [q11Wform_eq_closed]
  unfold q11WformClosed q11SegForm
  rw [q11Fourier_eq, ellX_eq hc, ellY_eq hs]
  obtain ⟨-, -, -, -, hv, -⟩ := q11FstateFrom_spec hb hc hs 48 le_rfl
  unfold q11WIFrom q11WIcore
  set X := ellXq c
  set Y := ellYq s
  apply Li2Lean.P0.CA.Contour.QI.mem_sub
  · apply q11SegCombI_mem
    · intro j hj; exact (q11PEdge_ok X Y hj).1
    · intro j hj; exact (q11FEdge_ok X Y hj).1
    · simpa using (edge_ok X Y).1
    · have h := (edge_ok (X - 2) Y).1
      rwa [show (((X - 2 : ℚ)) : ℝ) = (X : ℝ) + -2 by push_cast; ring] at h
    · exact mem_smul X L11_mem
    · have := mem_add (mem_pt (1 / 2)) (mem_smul (1 / 2) L2_mem)
      refine mem_of_eq this ?_
      rw [show Real.log (1 / 2) = -Real.log 2 by rw [one_div, Real.log_inv]]
      push_cast; ring
  · have := mem_smul 2 (mem_sub q11MLC_mem hv)
    refine mem_of_eq this ?_
    push_cast; ring

theorem q11DIFrom_mem {b : ℕ → QI} (hb : ∀ k < 48, (b k).mem (q11BR k))
    {θ : ℝ} {c s : ℚ} (hθ : θ ∈ Set.Ioo 0 Real.pi)
    (hc : Real.cos θ = c) (hs : Real.sin θ = s) :
    (q11DIFrom b c s).mem (q11W1 θ) := by
  rw [q11W1_eq_closed (sin_ne_zero_of_mem hθ)]
  obtain ⟨-, -, -, -, -, hd⟩ := q11FstateFrom_spec hb hc hs 48 le_rfl
  unfold q11W1Closed q11DIFrom q11DIcore
  rw [ellX_eq hc, ellY_eq hs]
  have hX1 : ellX1 θ = ((-(12783 / 10000) * s : ℚ) : ℝ) := by simp [ellX1, hs]
  have hY1 : ellY1 θ = ((229 / 200 * c : ℚ) : ℝ) := by simp [ellY1, hc]
  rw [hX1, hY1]
  set X := ellXq c
  set Y := ellYq s
  have hds : ∀ (e : EV) (u : ℝ), e.ok u Y →
      (add (smul (-(12783 / 10000) * s) e.l) (smul (229 / 200 * c) e.a)).mem
        (dGr u Y ((-(12783 / 10000) * s : ℚ) : ℝ) ((229 / 200 * c : ℚ) : ℝ)) := by
    intro e u he
    have := mem_add (mem_smul (-(12783 / 10000) * s) he.2.1) (mem_smul (229 / 200 * c) he.2.2)
    refine mem_of_eq this ?_
    unfold dGr; ring
  apply Li2Lean.P0.CA.Contour.QI.mem_sub
  · apply q11SegCombI_mem
    · intro j hj; exact hds _ _ (q11PEdge_ok X Y hj)
    · intro j hj; exact hds _ _ (q11FEdge_ok X Y hj)
    · have := hds _ _ (edge_ok X Y); simpa using this
    · exact hds _ _ (by
        have h := edge_ok (X - 2) Y
        rwa [show (((X - 2 : ℚ)) : ℝ) = (X : ℝ) + -2 by push_cast; ring] at h)
    · exact mem_smul _ L11_mem
    · exact mem_pt 0 |> fun h => by simpa using h
  · have := mem_smul 2 hd
    refine mem_of_eq this ?_
    unfold q11F1; push_cast; ring

/-- Boolean validator for a pre-evaluated 48-entry Fourier coefficient table `bTab`. -/
def q11BTabSubCheck (bTab : List QI) : ℕ → Bool
  | 0 => true
  | n + 1 =>
      let b := bTab.getD n (pt 0)
      let bc := q11BComp n
      decide (b.lo ≤ bc.lo ∧ bc.hi ≤ b.hi) && q11BTabSubCheck bTab n

def q11BTabOk (bTab : List QI) : Bool :=
  q11BTabSubCheck bTab 48

theorem q11BTabSubCheck_sound {bTab : List QI} :
    ∀ {n : ℕ}, n ≤ 48 → q11BTabSubCheck bTab n = true →
      ∀ k < n, (bTab.getD k (pt 0)).mem (q11BR k)
  | 0, _, _, k, hk => by omega
  | n + 1, hn, h, k, hk => by
      simp only [q11BTabSubCheck, Bool.and_eq_true, decide_eq_true_eq] at h
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | rfl
      · exact q11BTabSubCheck_sound (by omega) h.2 k hlt
      · have hbc := q11BComp_mem (by omega : k < 48)
        have hlo : ((bTab.getD k (pt 0)).lo : ℝ) ≤ (q11BComp k).lo := by exact_mod_cast h.1.1
        have hhi : ((q11BComp k).hi : ℝ) ≤ (bTab.getD k (pt 0)).hi := by exact_mod_cast h.1.2
        exact ⟨hlo.trans hbc.1, hbc.2.trans hhi⟩

theorem q11BTabOk_sound {bTab : List QI} (h : q11BTabOk bTab = true) :
    ∀ k < 48, (bTab.getD k (pt 0)).mem (q11BR k) :=
  q11BTabSubCheck_sound le_rfl h

/-! ## 3. Reflected Cell and Group Checker for `q = 11` -/

def q11CheckCellFrom (b : ℕ → QI) (W D T : QI) (c : Cell) : Bool :=
  decide (0 ≤ c.lo ∧ c.lo ≤ c.hi ∧ c.hi ≤ 1 ∧ c.lower ≤ cellLower W D T c) &&
    (if c.lo = 0 then decide (c.lower ≤ (q11WIFrom b 1 0).lo) else true) &&
    (if c.hi = 1 then decide (c.lower ≤ (q11WIFrom b (-1) 0).lo) else true)

def q11AllCellsFrom (b : ℕ → QI) (W D T : QI) : List Cell → Bool
  | [] => true
  | c :: cs => q11CheckCellFrom b W D T c && q11AllCellsFrom b W D T cs

def q11GrpCheckAtFrom (b : ℕ → QI) (g : Grp) (wd : QI × QI) (T : QI) : Bool :=
  q11AllCellsFrom b wd.1 wd.2 T g.cells

def q11CheckGrpFrom (b : ℕ → QI) (g : Grp) : Bool :=
  decide (0 < g.t) &&
    q11GrpCheckAtFrom b g
      (q11WDIFrom b (ContourKit.weierstrassCos g.t) (ContourKit.weierstrassSin g.t))
      (smul 2 (atanI g.t))

def q11AllGrpFrom (b : ℕ → QI) : List Grp → Bool
  | [] => true
  | g :: gs => q11CheckGrpFrom b g && q11AllGrpFrom b gs

def q11CheckCell (W D T : QI) (c : Cell) : Bool :=
  q11CheckCellFrom q11BComp W D T c

def q11AllCells (W D T : QI) (cs : List Cell) : Bool :=
  q11AllCellsFrom q11BComp W D T cs

def q11GrpCheckAt (g : Grp) (wd : QI × QI) (T : QI) : Bool :=
  q11GrpCheckAtFrom q11BComp g wd T

def q11CheckGrp (g : Grp) : Bool :=
  q11CheckGrpFrom q11BComp g

def q11AllGrp (gs : List Grp) : Bool :=
  q11AllGrpFrom q11BComp gs

theorem q11AllGrpFrom_append (b : ℕ → QI) (xs ys : List Grp) :
    q11AllGrpFrom b (xs ++ ys) = (q11AllGrpFrom b xs && q11AllGrpFrom b ys) := by
  induction xs with
  | nil => simp [q11AllGrpFrom]
  | cons g gs ih => simp [q11AllGrpFrom, ih, Bool.and_assoc]

theorem q11AllGrp_append (xs ys : List Grp) :
    q11AllGrp (xs ++ ys) = (q11AllGrp xs && q11AllGrp ys) :=
  q11AllGrpFrom_append q11BComp xs ys

theorem q11CheckCellFrom_bounds {b : ℕ → QI} {W D T : QI} {c : Cell}
    (h : q11CheckCellFrom b W D T c = true) :
    0 ≤ c.lo ∧ c.lo ≤ c.hi ∧ c.hi ≤ 1 := by
  simp only [q11CheckCellFrom, Bool.and_eq_true] at h
  obtain ⟨h0lo, hlohi, hhi1, _⟩ := of_decide_eq_true h.1.1
  exact ⟨h0lo, hlohi, hhi1⟩

theorem q11CheckCellFrom_sound {b : ℕ → QI} (hb : ∀ k < 48, (b k).mem (q11BR k))
    {W D T : QI} {θ0 : ℝ} (hθ0 : θ0 ∈ Set.Ioo 0 Real.pi)
    (hW : W.mem (q11Wform θ0)) (hD : D.mem (q11W1 θ0)) (hT : T.mem θ0)
    {c : Cell} (h : q11CheckCellFrom b W D T c = true) {u : ℝ}
    (hlo : (c.lo : ℝ) ≤ u) (hhi : u ≤ (c.hi : ℝ)) :
    (c.lower : ℝ) ≤ q11Wform (Real.pi * u) := by
  simp only [q11CheckCellFrom, Bool.and_eq_true] at h
  obtain ⟨⟨hmain, hend0⟩, hend1⟩ := h
  obtain ⟨h0lo, hlohi, hhi1, hlow⟩ := of_decide_eq_true hmain
  have h0loR : (0 : ℝ) ≤ c.lo := by exact_mod_cast h0lo
  have hhi1R : (c.hi : ℝ) ≤ 1 := by exact_mod_cast hhi1
  rcases eq_or_lt_of_le (le_trans h0loR hlo) with hu0 | hu0
  · have hlo0 : c.lo = 0 := by
      have : (c.lo : ℝ) = 0 := le_antisymm (hu0 ▸ hlo) h0loR
      exact_mod_cast this
    rw [if_pos hlo0] at hend0
    have hb0 : (c.lower : ℝ) ≤ ((q11WIFrom b 1 0).lo : ℝ) := by
      exact_mod_cast of_decide_eq_true hend0
    have hm := q11WIFrom_mem hb (θ := 0) (c := 1) (s := 0) (by simp) (by simp)
    rw [← hu0, mul_zero]
    exact hb0.trans hm.1
  rcases eq_or_lt_of_le (le_trans hhi hhi1R) with hu1 | hu1
  · have hhi1' : c.hi = 1 := by
      have : (c.hi : ℝ) = 1 := le_antisymm hhi1R (hu1 ▸ hhi)
      exact_mod_cast this
    rw [if_pos hhi1'] at hend1
    have hb1 : (c.lower : ℝ) ≤ ((q11WIFrom b (-1) 0).lo : ℝ) := by
      exact_mod_cast of_decide_eq_true hend1
    have hm := q11WIFrom_mem hb (θ := Real.pi) (c := -1) (s := 0) (by simp) (by simp)
    rw [hu1, mul_one]
    exact hb1.trans hm.1
  set θ := Real.pi * u
  have hθ : θ ∈ Set.Ioo 0 Real.pi := ⟨mul_pos Real.pi_pos hu0, by
    have := mul_lt_mul_of_pos_left hu1 Real.pi_pos; simpa using this⟩
  have hTay := q11_taylor_lower hθ hθ0
  have hpi := PI_mem
  have hd : (QI.mk (PI.lo * c.lo - T.hi) (PI.hi * c.hi - T.lo)).mem (θ - θ0) := by
    constructor
    · push_cast
      have : (PI.lo : ℝ) * c.lo ≤ Real.pi * u :=
        mul_le_mul hpi.1 hlo h0loR Real.pi_pos.le
      linarith [hT.2]
    · push_cast
      have h0u : (0 : ℝ) ≤ u := le_of_lt hu0
      have : Real.pi * u ≤ (PI.hi : ℝ) * c.hi :=
        mul_le_mul hpi.2 hhi h0u (le_trans Real.pi_pos.le hpi.2)
      linarith [hT.1]
  have hprod := mem_mul hD hd
  have hsq := sq_le_max_of_mem hd.1 hd.2
  have hlowR : (c.lower : ℝ) ≤ (cellLower W D T c : ℝ) := by exact_mod_cast hlow
  unfold cellLower at hlowR
  push_cast at hlowR hsq
  nlinarith [hW.1, hprod.1, hTay, hsq]

theorem q11AllCellsFrom_mem {b : ℕ → QI} {W D T : QI} {cs : List Cell}
    (h : q11AllCellsFrom b W D T cs = true) {c : Cell} (hc : c ∈ cs) :
    q11CheckCellFrom b W D T c = true := by
  induction cs with
  | nil => simp at hc
  | cons a cs ih =>
      simp only [q11AllCellsFrom, Bool.and_eq_true] at h
      rcases List.mem_cons.mp hc with rfl | hc
      · exact h.1
      · exact ih h.2 hc

theorem q11CheckGrpFrom_bounds {b : ℕ → QI} {g : Grp}
    (h : q11CheckGrpFrom b g = true) {c : Cell} (hc : c ∈ g.cells) :
    0 ≤ c.lo ∧ c.lo ≤ c.hi ∧ c.hi ≤ 1 := by
  simp only [q11CheckGrpFrom, Bool.and_eq_true] at h
  exact q11CheckCellFrom_bounds (q11AllCellsFrom_mem h.2 hc)

theorem q11CheckGrpFrom_sound {b : ℕ → QI} (hb : ∀ k < 48, (b k).mem (q11BR k))
    {g : Grp} (h : q11CheckGrpFrom b g = true) {c : Cell} (hc : c ∈ g.cells)
    {u : ℝ} (hlo : (c.lo : ℝ) ≤ u) (hhi : u ≤ (c.hi : ℝ)) :
    (c.lower : ℝ) ≤ q11Wform (Real.pi * u) := by
  simp only [q11CheckGrpFrom, Bool.and_eq_true] at h
  obtain ⟨ht, hcells⟩ := h
  have htR : (0 : ℝ) < g.t := by exact_mod_cast of_decide_eq_true ht
  set θ0 := 2 * Real.arctan (g.t : ℝ)
  have hθ0 : θ0 ∈ Set.Ioo 0 Real.pi := by
    have a1 : 0 < Real.arctan (g.t : ℝ) := by
      have := Real.arctan_strictMono htR; simpa using this
    have a2 := Real.arctan_lt_pi_div_two (g.t : ℝ)
    constructor <;> linarith
  have hc0 : Real.cos θ0 = (ContourKit.weierstrassCos g.t : ℝ) :=
    ContourKit.cos_two_arctan_rat _
  have hs0 : Real.sin θ0 = (ContourKit.weierstrassSin g.t : ℝ) :=
    ContourKit.sin_two_arctan_rat _
  have hT : (smul 2 (atanI g.t)).mem θ0 := by
    have := mem_smul 2 (atanI_mem g.t); simpa [θ0] using this
  unfold q11GrpCheckAtFrom at hcells
  rw [q11WDIFrom_eq] at hcells
  exact q11CheckCellFrom_sound hb hθ0
    (q11WIFrom_mem hb hc0 hs0) (q11DIFrom_mem hb hθ0 hc0 hs0) hT
    (q11AllCellsFrom_mem hcells hc) hlo hhi

theorem q11AllGrpFrom_mem {b : ℕ → QI} {gs : List Grp}
    (h : q11AllGrpFrom b gs = true) {g : Grp} (hg : g ∈ gs) :
    q11CheckGrpFrom b g = true := by
  induction gs with
  | nil => simp at hg
  | cons a gs ih =>
      simp only [q11AllGrpFrom, Bool.and_eq_true] at h
      rcases List.mem_cons.mp hg with rfl | hg
      · exact h.1
      · exact ih h.2 hg

theorem q11CheckGrp_sound {g : Grp} (h : q11CheckGrp g = true) {c : Cell} (hc : c ∈ g.cells)
    {u : ℝ} (hlo : (c.lo : ℝ) ≤ u) (hhi : u ≤ (c.hi : ℝ)) :
    (c.lower : ℝ) ≤ q11Wform (Real.pi * u) :=
  q11CheckGrpFrom_sound (fun k hk => q11BComp_mem hk) h hc hlo hhi

theorem q11AllGrp_mem {gs : List Grp} (h : q11AllGrp gs = true) {g : Grp} (hg : g ∈ gs) :
    q11CheckGrp g = true :=
  q11AllGrpFrom_mem h hg

/-! ## 4. Full-Turn `Q11GammaRow` Lift and `Q11GammaContourCertificate` Constructor -/

def toUpperGammaRow (c : Cell) : Q11GammaRow :=
  { lo := c.lo / 2
    hi := c.hi / 2
    lower := etaFloor }

def toLowerGammaRow (c : Cell) : Q11GammaRow :=
  { lo := 1 - c.hi / 2
    hi := 1 - c.lo / 2
    lower := etaFloor }

def q11FullGammaRows (groups : List Grp) : List Q11GammaRow :=
  let cells := groups.flatMap Grp.cells
  cells.map toUpperGammaRow ++ cells.map toLowerGammaRow

theorem ratioToReal_etaFloor : ratioToReal etaFloor = -(3359 / 500 : ℝ) := by
  norm_num [ratioToReal, etaFloor]

private theorem etaFloor_le_etaFloor_bool : ratioLeBool etaFloor etaFloor = true := by
  decide

private theorem etaFloor_den_pos_bool : decide (0 < etaFloor.den) = true := by
  decide

theorem q11GammaRowCheck_toUpperGammaRow {c : Cell}
    (h : 0 ≤ c.lo ∧ c.lo ≤ c.hi ∧ c.hi ≤ 1) :
    q11GammaRowCheck (toUpperGammaRow c) = true := by
  unfold q11GammaRowCheck toUpperGammaRow
  simp only [Bool.and_eq_true, etaFloor_le_etaFloor_bool, etaFloor_den_pos_bool, and_true,
    decide_eq_true_eq]
  exact ⟨by linarith [h.1], by linarith [h.2.1], by linarith [h.2.2]⟩

theorem q11GammaRowCheck_toLowerGammaRow {c : Cell}
    (h : 0 ≤ c.lo ∧ c.lo ≤ c.hi ∧ c.hi ≤ 1) :
    q11GammaRowCheck (toLowerGammaRow c) = true := by
  unfold q11GammaRowCheck toLowerGammaRow
  simp only [Bool.and_eq_true, etaFloor_le_etaFloor_bool, etaFloor_den_pos_bool, and_true,
    decide_eq_true_eq]
  exact ⟨by linarith [h.2.2], by linarith [h.2.1], by linarith [h.1]⟩

theorem q11GammaRowsCheck_of_all {rs : List Q11GammaRow}
    (h : ∀ r ∈ rs, q11GammaRowCheck r = true) :
    q11GammaRowsCheck rs = true := by
  induction rs with
  | nil => rfl
  | cons a rs ih =>
      simp only [q11GammaRowsCheck, Bool.and_eq_true]
      exact ⟨h a (by simp), ih (fun r hr => h r (by simp [hr]))⟩

theorem q11FullGammaRows_numeric {b : ℕ → QI} {groups : List Grp}
    (hall : q11AllGrpFrom b groups = true) :
    q11GammaRowsCheck (q11FullGammaRows groups) = true := by
  apply q11GammaRowsCheck_of_all
  intro r hr
  simp only [q11FullGammaRows, List.mem_append, List.mem_map] at hr
  rcases hr with ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩
  · obtain ⟨g, hg, hcg⟩ := List.mem_flatMap.mp hc
    exact q11GammaRowCheck_toUpperGammaRow
      (q11CheckGrpFrom_bounds (q11AllGrpFrom_mem hall hg) hcg)
  · obtain ⟨g, hg, hcg⟩ := List.mem_flatMap.mp hc
    exact q11GammaRowCheck_toLowerGammaRow
      (q11CheckGrpFrom_bounds (q11AllGrpFrom_mem hall hg) hcg)

theorem q11FullGammaRows_cover {groups : List Grp}
    (hchain : Li2Lean.P0.CA.Receipt.chainCheck
      ((groups.flatMap Grp.cells).map Cell.cell) 0 1 = true) :
    ∀ u : ℝ, 0 ≤ u → u ≤ 1 →
      ∃ r ∈ q11FullGammaRows groups, (r.lo : ℝ) ≤ u ∧ u ≤ (r.hi : ℝ) := by
  have hexact : ExactChain ((groups.flatMap Grp.cells).map Cell.cell) 0 1 :=
    Li2Lean.P0.CA.Receipt.chainCheck_sound hchain
  intro u hu0 hu1
  rcases le_total u (1 / 2 : ℝ) with hu_half | hu_half
  · have hv0 : ((0 : ℚ) : ℝ) ≤ 2 * u := by push_cast; linarith
    have hv1 : 2 * u ≤ ((1 : ℚ) : ℝ) := by push_cast; linarith
    obtain ⟨rc, hrc, _, hlo, hhi⟩ := exactChain_covers hexact (2 * u) hv0 hv1
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hrc
    refine ⟨toUpperGammaRow c, ?_, ?_, ?_⟩
    · simp only [q11FullGammaRows, List.mem_append, List.mem_map]
      exact Or.inl ⟨c, hc, rfl⟩
    · simp only [toUpperGammaRow, Cell.cell] at hlo ⊢
      push_cast
      linarith
    · simp only [toUpperGammaRow, Cell.cell] at hhi ⊢
      push_cast
      linarith
  · have hv0 : ((0 : ℚ) : ℝ) ≤ 2 * (1 - u) := by push_cast; linarith
    have hv1 : 2 * (1 - u) ≤ ((1 : ℚ) : ℝ) := by push_cast; linarith
    obtain ⟨rc, hrc, _, hlo, hhi⟩ := exactChain_covers hexact (2 * (1 - u)) hv0 hv1
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hrc
    refine ⟨toLowerGammaRow c, ?_, ?_, ?_⟩
    · simp only [q11FullGammaRows, List.mem_append, List.mem_map]
      exact Or.inr ⟨c, hc, rfl⟩
    · simp only [toLowerGammaRow, Cell.cell] at hhi ⊢
      push_cast
      linarith
    · simp only [toLowerGammaRow, Cell.cell] at hlo ⊢
      push_cast
      linarith

theorem q11FullGammaRows_row_lower {b : ℕ → QI}
    (hb : ∀ k < 48, (b k).mem (q11BR k))
    {groups : List Grp}
    (hall : q11AllGrpFrom b groups = true)
    (hfloor : Li2Lean.P0.CA.Receipt.floorCheck (-(3359 / 500 : ℚ))
      ((groups.flatMap Grp.cells).map Cell.cell) = true) :
    ∀ r ∈ q11FullGammaRows groups, ∀ u : ℝ,
      (r.lo : ℝ) ≤ u → u ≤ (r.hi : ℝ) →
        ratioToReal r.lower ≤ q11Weta (gammaPoint (2 * Real.pi * u)) := by
  intro r hr u hlo hhi
  simp only [q11FullGammaRows, List.mem_append, List.mem_map] at hr
  rcases hr with ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩
  · obtain ⟨g, hg, hcg⟩ := List.mem_flatMap.mp hc
    have hflQ : -(3359 / 500 : ℚ) ≤ c.lower := by
      have hmem : c.cell ∈ (groups.flatMap Grp.cells).map Cell.cell :=
        List.mem_map.mpr ⟨c, hc, rfl⟩
      exact Li2Lean.P0.CA.Receipt.floorCheck_sound hfloor c.cell hmem
    have hflR : ratioToReal (toUpperGammaRow c).lower ≤ (c.lower : ℝ) := by
      simp only [toUpperGammaRow, ratioToReal_etaFloor]
      have hcast : ((-(3359 / 500 : ℚ) : ℚ) : ℝ) = -(3359 / 500 : ℝ) := by
        norm_num
      rw [← hcast]
      exact Rat.cast_le.mpr hflQ
    have hvlo : (c.lo : ℝ) ≤ 2 * u := by
      simp only [toUpperGammaRow] at hlo
      push_cast at hlo
      linarith
    have hvhi : 2 * u ≤ (c.hi : ℝ) := by
      simp only [toUpperGammaRow] at hhi
      push_cast at hhi
      linarith
    have hval := q11CheckGrpFrom_sound hb (q11AllGrpFrom_mem hall hg) hcg hvlo hvhi
    rw [q11Weta_gammaPoint_two_mul]
    exact hflR.trans hval
  · obtain ⟨g, hg, hcg⟩ := List.mem_flatMap.mp hc
    have hflQ : -(3359 / 500 : ℚ) ≤ c.lower := by
      have hmem : c.cell ∈ (groups.flatMap Grp.cells).map Cell.cell :=
        List.mem_map.mpr ⟨c, hc, rfl⟩
      exact Li2Lean.P0.CA.Receipt.floorCheck_sound hfloor c.cell hmem
    have hflR : ratioToReal (toLowerGammaRow c).lower ≤ (c.lower : ℝ) := by
      simp only [toLowerGammaRow, ratioToReal_etaFloor]
      have hcast : ((-(3359 / 500 : ℚ) : ℚ) : ℝ) = -(3359 / 500 : ℝ) := by
        norm_num
      rw [← hcast]
      exact Rat.cast_le.mpr hflQ
    have hvlo : (c.lo : ℝ) ≤ 2 * (1 - u) := by
      simp only [toLowerGammaRow] at hhi
      push_cast at hhi
      linarith
    have hvhi : 2 * (1 - u) ≤ (c.hi : ℝ) := by
      simp only [toLowerGammaRow] at hlo
      push_cast at hlo
      linarith
    have hval := q11CheckGrpFrom_sound hb (q11AllGrpFrom_mem hall hg) hcg hvlo hvhi
    rw [← q11Weta_gammaPoint_symm u, q11Weta_gammaPoint_two_mul (1 - u)]
    exact hflR.trans hval

/-- Construct `Q11GammaContourCertificate` from any verified upper-half group list
    parameterized by a validated Fourier coefficient enclosure `b`. -/
def q11GammaContourCertificate_of_groupsFrom
    {b : ℕ → QI} (hb : ∀ k < 48, (b k).mem (q11BR k))
    (groups : List Grp)
    (hall : q11AllGrpFrom b groups = true)
    (hfloor : Li2Lean.P0.CA.Receipt.floorCheck (-(3359 / 500 : ℚ))
      ((groups.flatMap Grp.cells).map Cell.cell) = true)
    (hchain : Li2Lean.P0.CA.Receipt.chainCheck
      ((groups.flatMap Grp.cells).map Cell.cell) 0 1 = true) :
    Q11GammaContourCertificate where
  rows := q11FullGammaRows groups
  numeric := q11FullGammaRows_numeric hall
  cover := q11FullGammaRows_cover hchain
  row_lower := q11FullGammaRows_row_lower hb hall hfloor

/-- Construct `Q11GammaContourCertificate` from any verified upper-half group list
    using the default `q11BComp` enclosure. -/
def q11GammaContourCertificate_of_groups
    (groups : List Grp)
    (hall : q11AllGrp groups = true)
    (hfloor : Li2Lean.P0.CA.Receipt.floorCheck (-(3359 / 500 : ℚ))
      ((groups.flatMap Grp.cells).map Cell.cell) = true)
    (hchain : Li2Lean.P0.CA.Receipt.chainCheck
      ((groups.flatMap Grp.cells).map Cell.cell) 0 1 = true) :
    Q11GammaContourCertificate :=
  q11GammaContourCertificate_of_groupsFrom (fun k hk => q11BComp_mem hk)
    groups hall hfloor hchain

/-- Direct contour floor theorem on `Gamma` from a verified upper-half group list
    and a validated `bTab : List QI`. -/
theorem q11GammaContourFloor_of_bTab_and_groups
    {bTab : List QI} (hbTab : q11BTabOk bTab = true)
    {groups : List Grp}
    (hall : q11AllGrpFrom (fun k => bTab.getD k (pt 0)) groups = true)
    (hfloor : Li2Lean.P0.CA.Receipt.floorCheck (-(3359 / 500 : ℚ))
      ((groups.flatMap Grp.cells).map Cell.cell) = true)
    (hchain : Li2Lean.P0.CA.Receipt.chainCheck
      ((groups.flatMap Grp.cells).map Cell.cell) 0 1 = true) :
    ∀ z ∈ Gamma, ratioToReal etaFloor ≤ q11Weta z :=
  q11GammaContourFloor_of_certificate
    (q11GammaContourCertificate_of_groupsFrom (q11BTabOk_sound hbTab)
      groups hall hfloor hchain)

/-- Direct contour floor theorem on `Gamma` from a verified upper-half group list. -/
theorem q11GammaContourFloor_of_groups
    {groups : List Grp}
    (hall : q11AllGrp groups = true)
    (hfloor : Li2Lean.P0.CA.Receipt.floorCheck (-(3359 / 500 : ℚ))
      ((groups.flatMap Grp.cells).map Cell.cell) = true)
    (hchain : Li2Lean.P0.CA.Receipt.chainCheck
      ((groups.flatMap Grp.cells).map Cell.cell) 0 1 = true) :
    ∀ z ∈ Gamma, ratioToReal etaFloor ≤ q11Weta z :=
  q11GammaContourFloor_of_certificate
    (q11GammaContourCertificate_of_groups groups hall hfloor hchain)

end

end Li2Lean.P0.Q11Data
