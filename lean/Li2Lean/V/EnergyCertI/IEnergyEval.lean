/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.V.EnergyCertI.IData

/-!
# v2 energy evaluator (integer kit, energy mode `ntl = 7`, `nta = 4`)

Generated certificate data; compiled in the release.  Same closed
forms as v1 `EnergyEval.lean` (summation by parts; `G`, `A`, reflected point
`r²c/|c|²`, Poisson×Poisson `log|r² - c̄c'| - log r`, `D_q` moment series to
degree 50 with tail `|Mx Mv|/(51 q^51)`); only the arithmetic changed.
-/

namespace Li2Lean.V.EnergyCertI

open IK

structure Mode where
  ntl : Nat
  nta : Nat

def fieldMode : Mode := ⟨3, 2⟩
def energyMode : Mode := ⟨7, 4⟩

def R : QF := (3, 5)
def R2 : QF := (9, 25)

/-- `s log|s| - s`. -/
def hsI (md : Mode) (s : QF) : IV :=
  if s.1 = 0 then zero else add (smulQ s (logQ md.ntl (qabs s))) (ofQ (qneg s))

/-- `s/2 log(s²+Y²) - s + Y atan(s/Y)`; `hs s` for `Y = 0`. -/
def aI (md : Mode) (s Y : QF) : IV :=
  if Y.1 = 0 then hsI md s else
    add (add (smulQ (qhalf s) (logQ md.ntl (qadd (qsq s) (qsq Y)))) (ofQ (qneg s)))
      (smulQ Y (atanQ md.nta (qdiv s Y)))

/-- `s²/2 log|s| - 3s²/4`. -/
def gI (md : Mode) (s : QF) : IV :=
  if s.1 = 0 then zero else
    add (smulQ (qhalf (qsq s)) (logQ md.ntl (qabs s))) (ofQ (qneg (qmul (3, 4) (qsq s))))

def selfRow (md : Mode) (pts : List CP) (k : Nat) : IV :=
  match pts.drop k with
  | [] => zero
  | p :: rest => sumI (rest.map fun l => smulQ (qmul (-2, 1) (qmul p.J l.J)) (gI md (qsub l.e p.e)))

def crossRow (md : Mode) (pts1 pts2 : List CP) (k : Nat) : IV :=
  match pts1.drop k with
  | [] => zero
  | p :: _ => sumI (pts2.map fun l => smulQ (qneg (qmul p.J l.J)) (gI md (qsub p.e l.e)))

def phiOut (md : Mode) (c : PR) (u : QF) : IV := aI md (qsub u c.cx) c.cy

def phiIn (md : Mode) (c : PR) (u : QF) (lr : IV) : IV :=
  if c.cx.1 = 0 ∧ c.cy.1 = 0 then smulQ u lr else
    add (smulQ u (sub (smulQ (1, 2) (logQ md.ntl (qadd (qsq c.cx) (qsq c.cy)))) lr))
      (aI md (qsub u (qdiv (qmul R2 c.cx) (qadd (qsq c.cx) (qsq c.cy))))
        (qdiv (qmul R2 c.cy) (qadd (qsq c.cx) (qsq c.cy))))

def phiV (md : Mode) (c : PR) (u : QF) (lr : IV) : IV :=
  if qle R u then phiOut md c u else
    add (sub (phiIn md c u lr) (phiIn md c R lr)) (phiOut md c R)

def intPoiRow (md : Mode) (zp vp : List CP) (c : PR) (lr : IV) : IV :=
  smulQ (qneg (qmul (Int.ofNat c.mult, 1) c.w))
    (add (smulInt 2 (sumI (zp.map fun p => smulQ p.J (phiOut md c p.e))))
      (sumI (vp.map fun p => smulQ p.J (phiV md c p.e lr))))

def modsq (ci cj : PR) : QF :=
  qadd (qsq (qsub R2 (qadd (qmul ci.cx cj.cx) (qmul ci.cy cj.cy))))
    (qsq (qsub (qmul ci.cx cj.cy) (qmul ci.cy cj.cx)))

def ppTerm (md : Mode) (ci cj : PR) (lr : IV) : IV :=
  sub (smulQ (1, 2) (logQ md.ntl (modsq ci cj))) lr

def ppRow (md : Mode) (full : List PR) (i : Nat) (lr : IV) : IV :=
  match full.drop i with
  | [] => zero
  | ci :: rest =>
      sumI (smulQ (qmul ci.w ci.w) (ppTerm md ci ci lr) ::
        rest.map fun cj => smulQ (qmul (2, 1) (qmul ci.w cj.w)) (ppTerm md ci cj lr))

/-- `m_k = -1/(k+1) Σ_l J_l e_l^(k+1)`, every term rounded outward. -/
def momentI (pts : List CP) (k : Nat) : IV :=
  sumI (pts.map fun p => ofQ (qmul (qneg (qmul p.J (qpow p.e (k + 1)))) (1, k + 1)))

/-- `D_q = Mx Mv log q + Σ_{k=1}^{50} (-1)^(k+1)/(k q^k) m_k(x) m_k(v) ± |Mx Mv|/(51 q^51)`. -/
def dEnc (md : Mode) (q : Nat) (D : IData) : IV :=
  add (add (smulQ (qmul D.mx D.mv) (logQ md.ntl (Int.ofNat q, 1)))
      (sumI ((List.range 50).map fun i =>
        smulQ ((if i % 2 = 0 then 1 else -1), (i + 1) * q ^ (i + 1))
          (mulI (momentI D.xp (i + 1)) (momentI D.vp (i + 1))))))
    (fl (-(Int.ofNat (qmul D.mx D.mv).1.natAbs * Int.ofNat S)) (51 * q ^ 51 * (qmul D.mx D.mv).2),
     cl (Int.ofNat (qmul D.mx D.mv).1.natAbs * Int.ofNat S) (51 * q ^ 51 * (qmul D.mx D.mv).2))

inductive EKind where
  | selfX | selfV | selfZ | crossVZ | intPoi | pp | dq
  deriving DecidableEq, Repr

/-- The contribution of one shard to `signedVQuadratic` (sign included). -/
def energyShard (D : IData) (q : Nat) (lr : IV) : EKind → Nat → Nat → IV
  | .selfX, i0, i1 => sumI ((List.range' i0 (i1 - i0)).map (selfRow energyMode D.xp))
  | .selfV, i0, i1 => sumI ((List.range' i0 (i1 - i0)).map (selfRow energyMode D.vp))
  | .selfZ, i0, i1 => sumI ((List.range' i0 (i1 - i0)).map (selfRow energyMode D.zp))
  | .crossVZ, i0, i1 => sumI ((List.range' i0 (i1 - i0)).map (crossRow energyMode D.vp D.zp))
  | .intPoi, i0, i1 =>
      sumI (((D.pre.drop i0).take (i1 - i0)).map fun c => intPoiRow energyMode D.zp D.vp c lr)
  | .pp, i0, i1 => sumI ((List.range' i0 (i1 - i0)).map fun i => ppRow energyMode D.full i lr)
  | .dq, _, _ => neg (dEnc energyMode q D)

/-- Shard Verified: the claimed lower bound (an `Int` at scale `2^-64`) is `≤` the enclosure's `lo`. -/
def energyShardOK (D : IData) (q : Nat) (lr : IV) (k : EKind) (i0 i1 : Nat) (claim : Int) : Bool :=
  decide (claim ≤ (energyShard D q lr k i0 i1).1)

def kindCount (D : IData) : EKind → Nat
  | .selfX => D.xp.length
  | .selfV => D.vp.length
  | .selfZ => D.zp.length
  | .crossVZ => D.vp.length
  | .intPoi => D.pre.length
  | .pp => D.full.length
  | .dq => 1

def rangesOf (k : EKind) (plan : List (EKind × Nat × Nat × Int)) : List (Nat × Nat) :=
  (plan.filter fun e => decide (e.1 = k)).map fun e => (e.2.1, e.2.2.1)

def tilesFrom : Nat → Nat → List (Nat × Nat) → Bool
  | cur, n, [] => cur == n
  | cur, n, (a, b) :: rest => (a == cur) && Nat.blt a b && tilesFrom b n rest

def energyPlanTiles (D : IData) (plan : List (EKind × Nat × Nat × Int)) : Bool :=
  [EKind.selfX, .selfV, .selfZ, .crossVZ, .intPoi, .pp, .dq].all fun k =>
    tilesFrom 0 (kindCount D k) (rangesOf k plan)

/-- `Σ claims / 2^64 > Qlow`. -/
def claimsGt (plan : List (EKind × Nat × Nat × Int)) (qlow : QF) : Bool :=
  qlt qlow ((plan.map fun e => e.2.2.2).foldl (· + ·) 0, S)

/-! Obligation E-d (v2): for every kind/range, `IV.mem (energyShard D q lr k i0 i1)` of the
real partial sum of `signedVQuadratic`, given `IV.mem lr (Real.log (3/5))`; it follows
term by term from K-1..K-9 exactly as v1 E-d followed from the P0 `mem_*` lemmas. -/

end Li2Lean.V.EnergyCertI
