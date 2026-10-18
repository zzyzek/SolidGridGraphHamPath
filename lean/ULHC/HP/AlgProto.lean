/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.Algorithm

/-!
# Prototype: the ULHC search restricted away from the endpoints (no proofs)

For testing only. From a path-factor `G` (degree 1 at `s`, `t`), repeat: flip a Type III cell
with no endpoint as a corner; else apply the first strip of a minimum chain in the link graph
restricted to strips with no endpoint as a corner of any cell; else, with two components, flip
any Type III cell. `runR` returns `0` (one component reached), `1` (stuck) or `2` (fuel out).
-/

namespace ULHC

namespace HP

open Finset

def cornerB (z c : Pt) : Bool :=
  c == z || (c.1 + 1, c.2) == z || (c.1, c.2 + 1) == z || (c.1 + 1, c.2 + 1) == z

def avoidB (s t : Pt) (σ : StripSpec) : Bool :=
  (List.range σ.n).all fun j => !cornerB s (cellJ σ.c σ.s j) && !cornerB t (cellJ σ.c σ.s j)

def candNR (V : Finset Pt) (G : Finset Edge) (s t : Pt) : Finset Node :=
  (candN V G).filter fun x => avoidB s t x.σ

-- Targets: odd strips, and (as a first strip) even strips of `G` that lower the count.
--
def gtgtR (V : Finset Pt) (G : Finset Edge) (x : Node) : Bool :=
  x.σ.n % 2 == 1 || (x.pos == 1 && decide (cncomp V (applyS G x.σ) < cncomp V G))

-- The merging even strips of `G` avoiding the endpoints, computed once per round.
--
def mergeSet (V : Finset Pt) (G : Finset Edge) (s t : Pt) : Finset StripSpec :=
  (allStrips V G).filter fun σ =>
    σ.n % 2 = 0 ∧ avoidB s t σ = true ∧ cncomp V (applyS G σ) < cncomp V G

def gtgtM (M : Finset StripSpec) (x : Node) : Bool :=
  x.σ.n % 2 == 1 || (x.pos == 1 && decide (x.σ ∈ M))

def findPathR (V : Finset Pt) (G : Finset Edge) (s t : Pt) :
    Option (StripSpec × List StripSpec) :=
  let M := mergeSet V G s t
  (MP.minPath (candNR V G s t) (gsrc V G) gmid (gtgtM M) (gedge V G) gw).bind decode

def findT3R (V : Finset Pt) (G : Finset Edge) (s t : Pt) : Option (Pt × Side) :=
  ((cellList V).flatMap fun d => sidesL.map fun tf => (d, tf)).find? fun p =>
    !cornerB s p.1 && !cornerB t p.1 && t3B V G p.1 p.2

def stepR (V : Finset Pt) (G : Finset Edge) (s t : Pt) : Option (Finset Edge) :=
  match findT3R V G s t with
  | some (d, _) => some (flip G d)
  | none =>
    match findPathR V G s t with
    | some (a, _) => some (applyS G a)
    | none =>
      if cncomp V G == 2 then
        match findT3 V G with
        | some (d, _) => some (flip G d)
        | none => none
      else none

def runR (V : Finset Pt) (s t : Pt) : ℕ → Finset Edge → ℕ
  | 0, G => if cncomp V G == 1 then 0 else 2
  | k + 1, G =>
    if cncomp V G == 1 then 0
    else match stepR V G s t with
      | some G' => runR V s t k G'
      | none => 1

end HP

end ULHC

namespace ULHC

namespace HP

-- `runR` that also returns the last factor and the number of rounds.
--
def runRS (V : Finset Pt) (s t : Pt) : ℕ → ℕ → Finset Edge → ℕ × ℕ × Finset Edge
  | 0, r, G => (if cncomp V G == 1 then 0 else 2, r, G)
  | k + 1, r, G =>
    if cncomp V G == 1 then (0, r, G)
    else match stepR V G s t with
      | some G' => runRS V s t k (r + 1) G'
      | none => (1, r, G)

end HP

end ULHC

namespace ULHC

namespace HP

def isTailB (mid tgt : Node → Bool) (edge : Node → Node → Bool) : Node → List Node → Bool
  | x, [] => tgt x
  | x, y :: L => mid x && edge x y && isTailB mid tgt edge y L

def isPathB (src mid tgt : Node → Bool) (edge : Node → Node → Bool) : List Node → Bool
  | [] => false
  | x :: L => src x && isTailB mid tgt edge x L

-- The round with the `round_ca` check: after applying the first strip `a` of the minimum
-- chain `a :: L` (with `L ≠ []`), is `L` a chain of the new factor (restricted, positions from
-- 1), and is the next minimum weight below the current one?
--
def restOK (V : Finset Pt) (G : Finset Edge) (s t : Pt) (a : StripSpec) (L : List StripSpec) :
    Bool :=
  let G' := applyS G a
  (L.all fun σ => avoidB s t σ) &&
    isPathB (gsrc V G') gmid (gtgtR V G') (gedge V G') (posList 1 L)

def wtL (a : StripSpec) (L : List StripSpec) : ℕ := a.n + (L.map StripSpec.n).sum

-- Counts: (outcome, rounds with a chain of ≥ 2 strips, of these with the rest valid,
-- rounds where the next minimum weight is not below the current).
--
def runRC (V : Finset Pt) (s t : Pt) : ℕ → ℕ × ℕ × ℕ → Option ℕ → Finset Edge → ℕ × ℕ × ℕ × ℕ
  | 0, (r, v, w), _, G => (if cncomp V G == 1 then 0 else 2, r, v, w)
  | k + 1, (r, v, w), prev, G =>
    if cncomp V G == 1 then (0, r, v, w)
    else match findT3R V G s t with
      | some (d, _) => runRC V s t k (r, v, w) none (flip G d)
      | none =>
        match findPathR V G s t with
        | some (a, L) =>
          let cur := wtL a L
          let w' := match prev with
            | some p => if cur < p then w else w + 1
            | none => w
          let nxt := if L = [] then none else some cur
          if L = [] then runRC V s t k (r, v, w') nxt (applyS G a)
          else runRC V s t k (r + 1, v + (if restOK V G s t a L then 1 else 0), w') nxt (applyS G a)
        | none =>
          if cncomp V G == 2 then
            match findT3 V G with
            | some (d, _) => runRC V s t k (r, v, w) none (flip G d)
            | none => (1, r, v, w)
          else (1, r, v, w)

end HP

end ULHC
