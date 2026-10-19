/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.V.EnergyCertI.IEnergyEval

/-!
# v2 directed field bounds on cells (integer kit, field mode `ntl = 3`, `nta = 2`)

Generated certificate data; compiled in the release.  The cell
bounds are exactly the v1 bounds of `FieldEval.lean` (obligations F-a .. F-g:
max trick + closed form for chains, `D_v(t)` increasing, `log` monotone,
Poisson Taylor on real cells, arc monotonicity / arc Taylor in the rational
parametrisation, endpoint disks `eq:v-endpoint`); only the arithmetic changed.
One change of form: `hs((t1-t0)/2)` is computed once per cell (`ubarI`)
instead of once per chain point (same value, same enclosure).
-/

namespace Li2Lean.V.EnergyCertI

open IK

def FAIL : IV := (18446744073709551616000, 18446744073709551616000)

/-- Antiderivative in `u` of `log max(|t0-u|, |t1-u|)`; `H = hs((t1-t0)/2)`. -/
def psiI (md : Mode) (t0 t1 u : QF) (H : IV) : IV :=
  if qle u (qhalf (qadd t0 t1)) then neg (hsI md (qsub t1 u))
  else sub (hsI md (qsub u t0)) (smulInt 2 H)

def ubarI (md : Mode) (pts : List CP) (t0 t1 : QF) : IV :=
  neg (sumI (pts.map fun p => smulQ p.J (psiI md t0 t1 p.e (hsI md (qhalf (qsub t1 t0))))))

def lamI (md : Mode) (q : Nat) (t0 u : QF) : IV :=
  smulQ (qdiv (qadd (Int.ofNat q, 1) (qmul t0 u)) t0)
    (sub (logQ md.ntl (qadd (Int.ofNat q, 1) (qmul t0 u))) (ofQ (1, 1)))

def dlowI (md : Mode) (q : Nat) (pts : List CP) (t0 : QF) : IV :=
  neg (sumI (pts.map fun p => smulQ p.J (lamI md q t0 p.e)))

def clampQ (t0 t1 x : QF) : QF := if qlt x t0 then t0 else if qlt t1 x then t1 else x

def giQ (c : PR) (t : QF) : QF := qadd (qsq (qsub R2 (qmul c.cx t))) (qsq (qmul c.cy t))

def poiRealI (md : Mode) (c : PR) (t0 t1 : QF) (lr : IV) : IV :=
  let m := qhalf (qadd t0 t1)
  let hw := qhalf (qsub t1 t0)
  let wgt := qmul (Int.ofNat c.mult, 1) c.w
  if qle R t0 || qle t1 (qneg R) then
    let gm := qadd (qsq (qsub m c.cx)) (qsq c.cy)
    let gmin := qadd (qsq (qsub c.cx (clampQ t0 t1 c.cx))) (qsq c.cy)
    smulQ wgt (add (smulQ (1, 2) (logQ md.ntl gm))
      (ofQ (qadd (qmul (qabs (qdiv (qsub m c.cx) gm)) hw) (qdiv (qsq hw) (qmul (2, 1) gmin)))))
  else if qle (qneg R) t0 && qle t1 R then
    if c.cx.1 = 0 ∧ c.cy.1 = 0 then smulQ wgt lr else
      let cc := qadd (qsq c.cx) (qsq c.cy)
      let der := qdiv (qadd (qmul (qmul (-2, 1) c.cx) (qsub R2 (qmul c.cx m)))
          (qmul (qmul (2, 1) (qsq c.cy)) m)) (qmul (2, 1) (giQ c m))
      smulQ wgt (add (sub (smulQ (1, 2) (logQ md.ntl (giQ c m))) lr)
        (ofQ (qadd (qmul (qabs der) hw)
          (qdiv (qmul cc (qsq hw)) (qmul (2, 1) (giQ c (clampQ t0 t1 (qdiv (qmul R2 c.cx) cc))))))))
  else FAIL

def poiRealSum (md : Mode) (pre : List PR) (t0 t1 : QF) (lr : IV) : IV :=
  sumI (pre.map fun c => poiRealI md c t0 t1 lr)

def fxUB (md : Mode) (D : IData) (q : Nat) (t0 t1 : QF) : IV :=
  add (add (smulInt 2 (ubarI md D.xp t0 t1)) (neg (dlowI md q D.vp t0)))
    (smulQ (3, 4) (logQ md.ntl t1))

def fvUB (md : Mode) (D : IData) (q : Nat) (t0 t1 : QF) (lr : IV) : IV :=
  add (add (add (add (smulInt 2 (ubarI md D.vp t0 t1)) (ubarI md D.zp t0 t1))
    (poiRealSum md D.pre t0 t1 lr)) (neg (dlowI md q D.xp t0))) (smulQ (1, 4) (logQ md.ntl t1))

def fzNegUB (md : Mode) (D : IData) (t0 t1 : QF) (lr : IV) : IV :=
  add (add (smulInt 2 (add (ubarI md D.zp t0 t1) (poiRealSum md D.pre t0 t1 lr)))
    (ubarI md D.vp t0 t1)) (smulQ (-5, 4) (logQ md.ntl (qneg t1)))

def fzPosUB (md : Mode) (D : IData) (t0 t1 : QF) (lr : IV) : IV :=
  add (add (smulInt 2 (add (ubarI md D.zp t0 t1) (poiRealSum md D.pre t0 t1 lr)))
    (ubarI md D.vp t0 t1)) (smulQ (-5, 4) (logQ md.ntl t0))

/-- Rational point of the upper arc: quarter 1 `θ = 2 atan s`, quarter 2 `θ = π - 2 atan s`. -/
def wX (quarter : Nat) (s : QF) : QF :=
  if quarter = 1 then qdiv (qmul R (qsub (1, 1) (qsq s))) (qadd (1, 1) (qsq s))
  else qneg (qdiv (qmul R (qsub (1, 1) (qsq s))) (qadd (1, 1) (qsq s)))

def wY (s : QF) : QF := qdiv (qmul R (qmul (2, 1) s)) (qadd (1, 1) (qsq s))

def uChainAt (md : Mode) (pts : List CP) (X Y : QF) : IV :=
  neg (sumI (pts.map fun p => smulQ p.J (aI md (qsub p.e X) Y)))

def poiArc (md : Mode) (c : PR) (Xm Ym Th : QF) : IV :=
  let Dm := qadd (qsq (qsub Xm c.cx)) (qsq (qsub Ym c.cy))
  let Sv := qsub (qmul Ym c.cx) (qmul Xm c.cy)
  let rcU := qhalf (qadd R2 (qadd (qsq c.cx) (qsq c.cy)))
  let Dlo := qsub (qsub Dm (qmul (qmul (2, 1) (qabs Sv)) Th)) (qmul rcU (qsq Th))
  if qle Dlo (0, 1) then FAIL else
    smulQ c.w (add (smulQ (1, 2) (logQ md.ntl Dm))
      (ofQ (qadd (qmul (qdiv (qabs Sv) Dm) Th) (qdiv (qmul (3, 1) (qmul rcU (qsq Th))) (qmul (2, 1) Dlo)))))

def fzArcUB (md : Mode) (D : IData) (quarter : Nat) (s0 s1 : QF) (lr : IV) : IV :=
  let sm := qhalf (qadd s0 s1)
  let Th := qdiv (qsub s1 s0) (qadd (1, 1) (qsq s0))
  let sa := if quarter = 1 then s0 else s1
  let sb := if quarter = 1 then s1 else s0
  add (add (smulInt 2 (add (uChainAt md D.zp (wX quarter sa) (wY sa))
      (sumI (D.full.map fun c => poiArc md c (wX quarter sm) (wY sm) Th))))
    (uChainAt md D.vp (wX quarter sb) (wY sb))) (neg (smulQ (5, 4) lr))

inductive FPiece where
  | x | vlo | vhi | zneg | zpos | arc1 | arc2
  deriving DecidableEq, Repr

def fieldUB (D : IData) (q : Nat) (lr : IV) : FPiece → QF → QF → IV
  | .x, a, b => fxUB fieldMode D q a b
  | .vlo, a, b => fvUB fieldMode D q a b lr
  | .vhi, a, b => fvUB fieldMode D q a b lr
  | .zneg, a, b => fzNegUB fieldMode D a b lr
  | .zpos, a, b => fzPosUB fieldMode D a b lr
  | .arc1, a, b => fzArcUB fieldMode D 1 a b lr
  | .arc2, a, b => fzArcUB fieldMode D 2 a b lr

/-- Consecutive breakpoints `[b_i, b_{i+1}]`: nonempty and directed upper bound `< K`
(structural on the list; the recursive call is on the tail `tl`). -/
def cellsOK (ub : QF → QF → IV) (K : QF) : List QF → Bool
  | [] => true
  | a :: tl =>
      match tl with
      | [] => true
      | b :: _ => qlt a b && hiLt (ub a b) K && cellsOK ub K tl

def headQ (l : List QF) : QF := l.headD (0, 1)
def lastQ (l : List QF) : QF := l.getLastD (0, 1)
def qeq (a b : QF) : Bool := qle a b && qle b a

/-- Blocks chain into one cover of `[lo, hi]`. -/
def chainOK (lo hi : QF) : List (List QF) → Bool
  | [] => false
  | s :: tl =>
      qeq (headQ s) lo &&
        match tl with
        | [] => qeq (lastQ s) hi
        | _ :: _ => chainOK (lastQ s) hi tl

/-! Endpoint disks (`eq:v-endpoint`, `δ = 1/250`) -/

def DELTA : QF := (1, 250)

def jPos (md : Mode) (pts : List CP) : IV :=
  neg (sumI (pts.map fun p => smulQ p.J (hsI md (qadd p.e DELTA))))

def jNeg (md : Mode) (pts : List CP) : IV :=
  sumI (pts.map fun p => smulQ p.J (hsI md (qadd (qneg p.e) DELTA)))

def exUB (md : Mode) (D : IData) (q : Nat) : IV :=
  add (add (smulInt 2 (jPos md D.xp)) (smulQ (-5, 4) (logQ md.ntl (qsub (Int.ofNat q, 1) DELTA))))
    (smulQ (3, 4) (logQ md.ntl DELTA))

def evUB (md : Mode) (D : IData) (q : Nat) : IV :=
  add (add (add (smulInt 2 (jPos md D.vp))
      (add (jNeg md D.zp) (smulQ D.pm (logQ md.ntl (qadd R DELTA)))))
    (neg (logQ md.ntl (qsub (Int.ofNat q, 1) DELTA)))) (smulQ (1, 4) (logQ md.ntl DELTA))

end Li2Lean.V.EnergyCertI
