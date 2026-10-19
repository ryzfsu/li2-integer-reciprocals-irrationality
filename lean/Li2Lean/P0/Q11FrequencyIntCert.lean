/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.CA.Receipt.Checks
import Li2Lean.P0.CA.Frequency.FixTerms

/-!
# Integer-arithmetic certificates for `Q11Frequency*`

To prevent the external `nanoda` kernel from unfolding `instDecidableEqRat`
(`Eq.ndrec` over `ℚ`) or normalizing large rational sums/products via `Nat.gcd`
inside `decide +kernel`, this module provides pure `ℤ`/`ℕ` numerator/denominator
evaluators and Boolean checkers together with generic soundness theorems proved
once by induction and algebra.
-/

namespace Li2Lean.P0.Q11Data

open Li2Lean.F_L8
open Li2Lean.P0.CA.Receipt
open Li2Lean.P0.CA.Frequency

/-! ## 1. Unnormalized `(num, den) : ℤ × ℕ` arithmetic -/

/-- Rational value of an unnormalized `(num, den)` pair. -/
def valZ (p : ℤ × ℕ) : ℚ := (p.1 : ℚ) / (p.2 : ℚ)

/-- Extract the canonical `(num, den)` pair of a rational `q : ℚ`. -/
def ratPairOfRat (q : ℚ) : ℤ × ℕ := (q.num, q.den)

theorem ratPairOfRat_den_pos (q : ℚ) : 0 < (ratPairOfRat q).2 := q.den_pos

theorem valZ_ratPairOfRat (q : ℚ) : valZ (ratPairOfRat q) = q :=
  Rat.num_div_den q

/-- Scale `(n, d)` to a target denominator grid `G` whenever `d ∣ G` (`G % d = 0`),
using pure integer multiplication and division with no `gcd`. -/
def scalePairTo (G : ℕ) (p : ℤ × ℕ) : ℤ × ℕ :=
  if p.2 ≠ 0 ∧ G ≠ 0 ∧ G % p.2 = 0 then
    (p.1 * ((G / p.2 : ℕ) : ℤ), G)
  else
    p

theorem scalePairTo_den_pos (G : ℕ) {p : ℤ × ℕ} (hp : 0 < p.2) :
    0 < (scalePairTo G p).2 := by
  unfold scalePairTo
  split_ifs with h
  · exact Nat.pos_of_ne_zero h.2.1
  · exact hp

theorem valZ_scalePairTo (G : ℕ) (p : ℤ × ℕ) :
    valZ (scalePairTo G p) = valZ p := by
  unfold scalePairTo valZ
  split_ifs with h
  · rcases h with ⟨hp0, hG0, hmod⟩
    dsimp
    have hdvd : p.2 ∣ G := Nat.dvd_of_mod_eq_zero hmod
    have hm : p.2 * (G / p.2) = G := Nat.mul_div_cancel' hdvd
    have hmQ : (p.2 : ℚ) * ((G / p.2 : ℕ) : ℚ) = (G : ℚ) := by
      exact_mod_cast hm
    have hpQ : (p.2 : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp0
    have hGQ : (G : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hG0
    rw [div_eq_div_iff hGQ hpQ]
    push_cast
    calc
      (p.1 : ℚ) * ((G / p.2 : ℕ) : ℚ) * (p.2 : ℚ) =
          (p.1 : ℚ) * ((p.2 : ℚ) * ((G / p.2 : ℕ) : ℚ)) := by ring
      _ = (p.1 : ℚ) * (G : ℚ) := by rw [hmQ]
  · rfl

/-- Unnormalized addition of `(num, den)` pairs, preserving a shared denominator
when `p.2 = q.2` so fixed-grid sums never grow denominators or call `gcd`. -/
def pairAddZ (p q : ℤ × ℕ) : ℤ × ℕ :=
  if p.2 = q.2 then (p.1 + q.1, p.2)
  else (p.1 * (q.2 : ℤ) + q.1 * (p.2 : ℤ), p.2 * q.2)

theorem pairAddZ_den_pos {p q : ℤ × ℕ} (hp : 0 < p.2) (hq : 0 < q.2) :
    0 < (pairAddZ p q).2 := by
  unfold pairAddZ
  split_ifs
  · exact hp
  · exact Nat.mul_pos hp hq

theorem valZ_pairAddZ {p q : ℤ × ℕ} (hp : 0 < p.2) (hq : 0 < q.2) :
    valZ (pairAddZ p q) = valZ p + valZ q := by
  have hp' : (p.2 : ℚ) ≠ 0 := by exact_mod_cast hp.ne'
  have hq' : (q.2 : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  unfold pairAddZ valZ
  split_ifs with heq
  · dsimp
    rw [heq]
    push_cast
    ring
  · dsimp
    push_cast
    rw [div_add_div _ _ hp' hq']
    ring

def pairNegZ (p : ℤ × ℕ) : ℤ × ℕ := (-p.1, p.2)

theorem pairNegZ_den_pos {p : ℤ × ℕ} (hp : 0 < p.2) :
    0 < (pairNegZ p).2 := hp

theorem valZ_pairNegZ (p : ℤ × ℕ) :
    valZ (pairNegZ p) = -valZ p := by
  unfold valZ pairNegZ
  push_cast
  ring

def pairSubZ (p q : ℤ × ℕ) : ℤ × ℕ := pairAddZ p (pairNegZ q)

theorem pairSubZ_den_pos {p q : ℤ × ℕ} (hp : 0 < p.2) (hq : 0 < q.2) :
    0 < (pairSubZ p q).2 :=
  pairAddZ_den_pos hp hq

theorem valZ_pairSubZ {p q : ℤ × ℕ} (hp : 0 < p.2) (hq : 0 < q.2) :
    valZ (pairSubZ p q) = valZ p - valZ q := by
  unfold pairSubZ
  rw [valZ_pairAddZ (p := p) (q := pairNegZ q) hp (pairNegZ_den_pos hq), valZ_pairNegZ]
  ring

def pairMulZ (p q : ℤ × ℕ) : ℤ × ℕ := (p.1 * q.1, p.2 * q.2)

theorem pairMulZ_den_pos {p q : ℤ × ℕ} (hp : 0 < p.2) (hq : 0 < q.2) :
    0 < (pairMulZ p q).2 :=
  Nat.mul_pos hp hq

theorem valZ_pairMulZ (p q : ℤ × ℕ) :
    valZ (pairMulZ p q) = valZ p * valZ q := by
  unfold valZ pairMulZ
  push_cast
  exact mul_div_mul_comm _ _ _ _

def pairMaxZeroZ (p : ℤ × ℕ) : ℤ × ℕ := (max p.1 0, p.2)

theorem pairMaxZeroZ_den_pos {p : ℤ × ℕ} (hp : 0 < p.2) :
    0 < (pairMaxZeroZ p).2 := hp

theorem valZ_pairMaxZeroZ (p : ℤ × ℕ) :
    valZ (pairMaxZeroZ p) = max (valZ p) 0 := by
  unfold valZ pairMaxZeroZ
  dsimp
  have hd : (0 : ℚ) ≤ (p.2 : ℚ) := Nat.cast_nonneg p.2
  rcases le_total p.1 0 with hle | hge
  · have hleQ : (p.1 : ℚ) ≤ 0 := by exact_mod_cast hle
    have hdiv : (p.1 : ℚ) / (p.2 : ℚ) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hleQ hd
    rw [max_eq_right hle, max_eq_right hdiv]
    simp
  · have hgeQ : (0 : ℚ) ≤ (p.1 : ℚ) := by exact_mod_cast hge
    have hdiv : (0 : ℚ) ≤ (p.1 : ℚ) / (p.2 : ℚ) := div_nonneg hgeQ hd
    rw [max_eq_left hge, max_eq_left hdiv]

/-! ## 2. Pure `ℤ`/`ℕ` Boolean equality and order certificates -/

/-- Compare two rationals by Boolean equality of numerators and denominators
(avoiding `instDecidableEqRat` / `Eq.ndrec` in kernel proofs). -/
def qEqZ (a b : ℚ) : Bool :=
  (a.num == b.num) && (a.den == b.den)

theorem qEqZ_sound {a b : ℚ} (h : qEqZ a b = true) : a = b := by
  unfold qEqZ at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact Rat.ext h.1 h.2

/-- Compare two unnormalized `(num, den)` pairs by cross-multiplication in `ℤ`. -/
def pairLeZ (p q : ℤ × ℕ) : Bool :=
  decide (p.1 * (q.2 : ℤ) ≤ q.1 * (p.2 : ℤ))

theorem pairLeZ_sound {p q : ℤ × ℕ} (hp : 0 < p.2) (hq : 0 < q.2)
    (h : pairLeZ p q = true) :
    valZ p ≤ valZ q := by
  unfold pairLeZ valZ at *
  simp only [decide_eq_true_eq] at h
  have hpQ : (0 : ℚ) < (p.2 : ℚ) := by exact_mod_cast hp
  have hqQ : (0 : ℚ) < (q.2 : ℚ) := by exact_mod_cast hq
  rw [div_le_div_iff₀ hpQ hqQ]
  exact_mod_cast h

/-- Compare two rationals `a ≤ b` by cross-multiplication in `ℤ`. -/
def qLeZ (a b : ℚ) : Bool :=
  pairLeZ (ratPairOfRat a) (ratPairOfRat b)

theorem qLeZ_sound {a b : ℚ} (h : qLeZ a b = true) : a ≤ b := by
  unfold qLeZ at h
  rw [← valZ_ratPairOfRat a, ← valZ_ratPairOfRat b]
  exact pairLeZ_sound (ratPairOfRat_den_pos a) (ratPairOfRat_den_pos b) h

/-- Certify `q = (n : ℚ) / (d : ℚ)` by integer cross-multiplication `q.num * d == n * q.den`. -/
def ratIntDenCheck (q : ℚ) (n : ℤ) (d : ℕ) : Bool :=
  decide (0 < d) && (q.num * (d : ℤ) == n * (q.den : ℤ))

theorem rat_eq_of_ratIntDenCheck {q : ℚ} {n : ℤ} {d : ℕ}
    (h : ratIntDenCheck q n d = true) :
    q = (n : ℚ) / (d : ℚ) := by
  unfold ratIntDenCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  rcases h with ⟨hd, heq⟩
  rw [← Rat.num_div_den q]
  have hqQ : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_pos.ne'
  have hdQ : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [div_eq_div_iff hqQ hdQ]
  exact_mod_cast heq

/-- Integer-arithmetic exact-chain checker (avoids `instDecidableEqRat` and
`instDecidableLERat`). -/
def chainCheckZ : List ReceiptCell → ℚ → ℚ → Bool
  | [], _, _ => false
  | [c], left, right =>
      qEqZ c.lo left && qEqZ c.hi right && qLeZ c.lo c.hi
  | c :: d :: rest, left, right =>
      qEqZ c.lo left && qEqZ c.hi d.lo && qLeZ c.lo c.hi &&
        chainCheckZ (d :: rest) d.lo right

theorem chainCheck_eq_true_of_chainCheckZ :
    ∀ {cells : List ReceiptCell} {left right : ℚ},
      chainCheckZ cells left right = true → chainCheck cells left right = true
  | [], _, _, h => by simp [chainCheckZ] at h
  | [c], left, right, h => by
      simp only [chainCheckZ, Bool.and_eq_true] at h
      simp only [chainCheck, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨qEqZ_sound h.1.1, qEqZ_sound h.1.2⟩, qLeZ_sound h.2⟩
  | c :: d :: rest, left, right, h => by
      simp only [chainCheckZ, Bool.and_eq_true] at h
      simp only [chainCheck, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨⟨qEqZ_sound h.1.1.1, qEqZ_sound h.1.1.2⟩, qLeZ_sound h.1.2⟩,
        chainCheck_eq_true_of_chainCheckZ h.2⟩

/-- Elementwise integer cross-multiplication identity for `TermI.toQ t = p`. -/
def termIToQCheck (t : TermI) (p : ℚ × ℚ) : Bool :=
  ratIntDenCheck p.1 t.1 t.2.1 && ratIntDenCheck p.2 t.2.2.1 t.2.2.2

theorem termIToQCheck_sound {t : TermI} {p : ℚ × ℚ}
    (h : termIToQCheck t p = true) : TermI.toQ t = p := by
  unfold termIToQCheck at h
  simp only [Bool.and_eq_true] at h
  unfold TermI.toQ
  exact Prod.ext (rat_eq_of_ratIntDenCheck h.1).symm (rat_eq_of_ratIntDenCheck h.2).symm

/-- Elementwise list checker for `ts.map TermI.toQ = ps`. -/
def termIListToQCheck : List TermI → List (ℚ × ℚ) → Bool
  | [], [] => true
  | t :: ts, p :: ps => termIToQCheck t p && termIListToQCheck ts ps
  | _, _ => false

theorem termIListToQCheck_sound :
    ∀ {ts : List TermI} {ps : List (ℚ × ℚ)},
      termIListToQCheck ts ps = true → ts.map TermI.toQ = ps
  | [], [], _ => rfl
  | t :: ts, p :: ps, h => by
      simp only [termIListToQCheck, Bool.and_eq_true] at h
      simp only [List.map_cons, termIToQCheck_sound h.1,
        termIListToQCheck_sound h.2]
  | [], _ :: _, h => by simp [termIListToQCheck] at h
  | _ :: _, [], h => by simp [termIListToQCheck] at h

/-! ## 3. Integer-arithmetic `penaltyMassZ` and `penaltyMassZCheck` -/

def widthGrid : ℕ := 40960
def floorGrid : ℕ := 10000000000
def massGrid : ℕ := 409600000000000

theorem massGrid_pos : 0 < massGrid := by decide

def cellWidthZ (c : ReceiptCell) : ℤ × ℕ :=
  pairSubZ (scalePairTo widthGrid (ratPairOfRat c.hi))
           (scalePairTo widthGrid (ratPairOfRat c.lo))

theorem cellWidthZ_den_pos (c : ReceiptCell) :
    0 < (cellWidthZ c).2 := by
  unfold cellWidthZ
  exact pairSubZ_den_pos
    (scalePairTo_den_pos widthGrid (ratPairOfRat_den_pos c.hi))
    (scalePairTo_den_pos widthGrid (ratPairOfRat_den_pos c.lo))

theorem valZ_cellWidthZ (c : ReceiptCell) :
    valZ (cellWidthZ c) = c.hi - c.lo := by
  unfold cellWidthZ
  rw [valZ_pairSubZ
        (scalePairTo_den_pos widthGrid (ratPairOfRat_den_pos c.hi))
        (scalePairTo_den_pos widthGrid (ratPairOfRat_den_pos c.lo))]
  simp only [valZ_scalePairTo, valZ_ratPairOfRat]

def cellDiffZ (h a : ℚ) (c : ReceiptCell) : ℤ × ℕ :=
  pairSubZ (scalePairTo floorGrid (ratPairOfRat h))
           (pairSubZ (scalePairTo floorGrid (ratPairOfRat c.lower))
                     (scalePairTo floorGrid (ratPairOfRat a)))

theorem cellDiffZ_den_pos (h a : ℚ) (c : ReceiptCell) :
    0 < (cellDiffZ h a c).2 := by
  unfold cellDiffZ
  exact pairSubZ_den_pos
    (scalePairTo_den_pos floorGrid (ratPairOfRat_den_pos h))
    (pairSubZ_den_pos
      (scalePairTo_den_pos floorGrid (ratPairOfRat_den_pos c.lower))
      (scalePairTo_den_pos floorGrid (ratPairOfRat_den_pos a)))

theorem valZ_cellDiffZ (h a : ℚ) (c : ReceiptCell) :
    valZ (cellDiffZ h a c) = h - (c.lower - a) := by
  unfold cellDiffZ
  rw [valZ_pairSubZ
        (scalePairTo_den_pos floorGrid (ratPairOfRat_den_pos h))
        (pairSubZ_den_pos
          (scalePairTo_den_pos floorGrid (ratPairOfRat_den_pos c.lower))
          (scalePairTo_den_pos floorGrid (ratPairOfRat_den_pos a))),
      valZ_pairSubZ
        (scalePairTo_den_pos floorGrid (ratPairOfRat_den_pos c.lower))
        (scalePairTo_den_pos floorGrid (ratPairOfRat_den_pos a))]
  simp only [valZ_scalePairTo, valZ_ratPairOfRat]

/-- Unnormalized `(num, den)` cell penalty computed by integer arithmetic only. -/
def cellPenaltyZ (h a : ℚ) (c : ReceiptCell) : ℤ × ℕ :=
  pairMulZ (cellWidthZ c) (pairMaxZeroZ (cellDiffZ h a c))

theorem cellPenaltyZ_den_pos (h a : ℚ) (c : ReceiptCell) :
    0 < (cellPenaltyZ h a c).2 := by
  unfold cellPenaltyZ
  exact pairMulZ_den_pos (cellWidthZ_den_pos c)
    (pairMaxZeroZ_den_pos (cellDiffZ_den_pos h a c))

theorem valZ_cellPenaltyZ (h a : ℚ) (c : ReceiptCell) :
    valZ (cellPenaltyZ h a c) = (c.hi - c.lo) * max (h - (c.lower - a)) 0 := by
  unfold cellPenaltyZ
  rw [valZ_pairMulZ, valZ_cellWidthZ, valZ_pairMaxZeroZ, valZ_cellDiffZ]

/-- Unnormalized `(num, den)` penalty mass over a list of receipt cells,
computed by integer arithmetic only with no `gcd` normalization. -/
def penaltyMassZ (h a : ℚ) : List ReceiptCell → ℤ × ℕ
  | [] => (0, massGrid)
  | c :: rest => pairAddZ (cellPenaltyZ h a c) (penaltyMassZ h a rest)

theorem penaltyMassZ_den_pos (h a : ℚ) :
    ∀ (cells : List ReceiptCell), 0 < (penaltyMassZ h a cells).2
  | [] => massGrid_pos
  | c :: rest => pairAddZ_den_pos (cellPenaltyZ_den_pos h a c) (penaltyMassZ_den_pos h a rest)

theorem valZ_penaltyMassZ (h a : ℚ) :
    ∀ (cells : List ReceiptCell), valZ (penaltyMassZ h a cells) = penaltyMass h a cells
  | [] => by simp [penaltyMassZ, penaltyMass, valZ]
  | c :: rest => by
      simp only [penaltyMassZ, penaltyMass]
      rw [valZ_pairAddZ (cellPenaltyZ_den_pos h a c) (penaltyMassZ_den_pos h a rest),
          valZ_cellPenaltyZ, valZ_penaltyMassZ h a rest]

theorem penaltyMassZ_sound (h a : ℚ) (cells : List ReceiptCell) :
    ((penaltyMassZ h a cells).1 : ℚ) / ((penaltyMassZ h a cells).2 : ℚ) =
      penaltyMass h a cells :=
  valZ_penaltyMassZ h a cells

/-- Pure `ℤ`/`ℕ` Boolean certificate for `penaltyMass h a cells = (N : ℚ) / (D : ℚ)`. -/
def penaltyMassZCheck (h a : ℚ) (cells : List ReceiptCell) (N : ℤ) (D : ℕ) : Bool :=
  let p := penaltyMassZ h a cells
  decide (0 < D) && (p.1 * (D : ℤ) == N * (p.2 : ℤ))

theorem penaltyMass_eq_of_penaltyMassZCheck {h a : ℚ} {cells : List ReceiptCell}
    {N : ℤ} {D : ℕ} (hc : penaltyMassZCheck h a cells N D = true) :
    penaltyMass h a cells = (N : ℚ) / (D : ℚ) := by
  simp only [penaltyMassZCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
  rcases hc with ⟨hD, heq⟩
  rw [← penaltyMassZ_sound h a cells]
  have hp2 : ((penaltyMassZ h a cells).2 : ℚ) ≠ 0 := by
    exact_mod_cast (penaltyMassZ_den_pos h a cells).ne'
  have hDQ : (D : ℚ) ≠ 0 := by
    exact_mod_cast hD.ne'
  rw [div_eq_div_iff hp2 hDQ]
  exact_mod_cast heq

theorem penaltyMass_eq_zero_of_penaltyMassZCheck {h a : ℚ} {cells : List ReceiptCell}
    (hc : penaltyMassZCheck h a cells 0 1 = true) :
    penaltyMass h a cells = 0 := by
  have h0 := penaltyMass_eq_of_penaltyMassZCheck hc
  simpa using h0

end Li2Lean.P0.Q11Data
