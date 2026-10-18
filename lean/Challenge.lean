/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import Mathlib

@[expose] public section

/-!
# Challenge: Hamiltonian `s`–`t` paths in solid grid graphs

The statement `SolidGridHam.HP.decideHamPath_correct` at the end of this file says that the
algorithm `decideHamPath` returns `true` on a solid grid graph `V` and distinct points `s, t ∈ V`
exactly when `V` has a Hamiltonian path from `s` to `t`.

The problem. A point is a pair of integers (`Pt`). `V` is a finite set of points, and its grid
graph has an edge between every two points of `V` at distance `1` (`Edge`, `IsEdge`). `deg F p`
counts the edges of `F` at `p`. `IsFactor V d F` says that `F` is a set of edges of `V` with
degree `d p` at every `p ∈ V`, and `dST s t` is `1` at `s` and `t` and `2` elsewhere. `ncomp V F`
is the number of connected components of `(V, F)`. An edge set with degrees `dST s t` and one
component is exactly a Hamiltonian `s`–`t` path. `Solid V` says that every point outside `V`
reaches the region left of `V` by king moves through points outside `V`, that is, `V` has no
holes.

The algorithm. Everything else is the algorithm `decideHamPath` and its subroutines. It is
computable. Its loops are bounded by explicit fuel (`|V| + 2` rounds of the phase loop, `2|V| + 1`
class values per vortex, walks of fixed depth). A step bound `5 220 000 (|V| + 3)⁶` for cost
functions that mirror the algorithm is proved in the library (`decideHamPath_main`), but it is
not part of this statement.

The definitions are copied verbatim from the library module `SolidGridHam.Algorithm`.
-/

/-! ### From `Basic.Grid` -/

namespace SolidGridHam

/-- A lattice point. -/
abbrev Pt := ℤ × ℤ

/-- The direction of an edge: horizontal (`h`) or vertical (`v`). -/
inductive Dir
  | h
  | v
  deriving DecidableEq, Repr

/-- A unit edge of the lattice, from `p` one step right (`d = h`) or up (`d = v`). -/
structure Edge where
  d : Dir
  p : Pt
  deriving DecidableEq, Repr

namespace Edge

/-- The far endpoint of the edge. -/
def q (e : Edge) : Pt :=
  match e.d with
  | .h => (e.p.1 + 1, e.p.2)
  | .v => (e.p.1, e.p.2 + 1)

/-- The cell on the low side (below an `h` edge, left of a `v` edge). -/
def lo (e : Edge) : Pt :=
  match e.d with
  | .h => (e.p.1, e.p.2 - 1)
  | .v => (e.p.1 - 1, e.p.2)

/-- The cell on the high side (above an `h` edge, right of a `v` edge). -/
def hi (e : Edge) : Pt := e.p

end Edge

/-- The bottom side of the cell with lower-left corner `c`. -/
def bot (c : Pt) : Edge := ⟨.h, c⟩

/-- The top side of the cell `c`. -/
def top (c : Pt) : Edge := ⟨.h, (c.1, c.2 + 1)⟩

/-- The left side of the cell `c`. -/
def lft (c : Pt) : Edge := ⟨.v, c⟩

/-- The right side of the cell `c`. -/
def rgt (c : Pt) : Edge := ⟨.v, (c.1 + 1, c.2)⟩

/-- Edges leaving `p` to the right, left, up and down. -/
def eR (p : Pt) : Edge := ⟨.h, p⟩

/-- The edge leaving `p` to the left. -/
def eL (p : Pt) : Edge := ⟨.h, (p.1 - 1, p.2)⟩

/-- The edge leaving `p` upward. -/
def eU (p : Pt) : Edge := ⟨.v, p⟩

/-- The edge leaving `p` downward. -/
def eD (p : Pt) : Edge := ⟨.v, (p.1, p.2 - 1)⟩

/-- Indicator of membership, as a natural number. -/
def ind (F : Finset Edge) (e : Edge) : ℕ := if e ∈ F then 1 else 0

/-- Degree of `p` in the edge set `F`. -/
def deg (F : Finset Edge) (p : Pt) : ℕ :=
  ind F (eR p) + ind F (eL p) + ind F (eU p) + ind F (eD p)

/-- An edge of the grid graph on vertex set `V` (node-induced). -/
def IsEdge (V : Finset Pt) (e : Edge) : Prop := e.p ∈ V ∧ e.q ∈ V

/-- `IsEdge` is decidable. -/
instance (V : Finset Pt) (e : Edge) : Decidable (IsEdge V e) := by
  unfold IsEdge; infer_instance

/-- A cell of the grid graph: all four corners are vertices. -/
def IsCell (V : Finset Pt) (c : Pt) : Prop :=
  c ∈ V ∧ (c.1 + 1, c.2) ∈ V ∧ (c.1, c.2 + 1) ∈ V ∧ (c.1 + 1, c.2 + 1) ∈ V

/-- `IsCell` is decidable. -/
instance (V : Finset Pt) (c : Pt) : Decidable (IsCell V c) := by
  unfold IsCell; infer_instance

/-- A factor of the grid graph on `V` with degree function `d`: a set of grid edges in which every vertex `p` has degree `d p`. 2-factors have `d ≡ 2`; path-factors have `d = 1` at the two ends and `2` elsewhere. -/
def IsFactor (V : Finset Pt) (d : Pt → ℕ) (F : Finset Edge) : Prop :=
  (∀ e ∈ F, IsEdge V e) ∧ ∀ p ∈ V, deg F p = d p

/-- The degrees of a Hamiltonian `s`–`t` path: `1` at `s` and `t`, `2` everywhere else. -/
def dST (s t : Pt) (z : Pt) : ℕ := if z = s ∨ z = t then 1 else 2

/-- King-move adjacency between two lattice points that are both outside `V`. -/
def MissAdj (V : Finset Pt) (a b : Pt) : Prop :=
  a ∉ V ∧ b ∉ V ∧ |a.1 - b.1| ≤ 1 ∧ |a.2 - b.2| ≤ 1

/-- `V` is solid (no holes): every lattice point outside `V` is joined, by king moves through points outside `V`, to a point strictly left of all of `V`. A bounded face of area > 1 would contain a missing lattice point that cannot escape this way, and conversely. -/
def Solid (V : Finset Pt) : Prop :=
  ∀ a, a ∉ V → ∃ b, Relation.ReflTransGen (MissAdj V) a b ∧ ∀ p ∈ V, b.1 < p.1

/-! ### From `Basic.Arcs` -/

/-- Cell colour: true for odd `x + y`. -/
def par (c : Pt) : Bool := decide ((c.1 + c.2) % 2 = 1)

/-- `e ∈ E1(F)`. -/
def inE1 (F : Finset Edge) (e : Edge) : Bool :=
  match e.d with
  | .h => decide (e ∈ F)
  | .v => !decide (e ∈ F)

/-- The arc across `e` points from its low cell to its high cell. -/
def up (F : Finset Edge) (e : Edge) : Bool := (par e.lo == inE1 F e)

/-- A side of a cell: bottom, top, left or right. -/
inductive Side
  | b
  | t
  | l
  | r
  deriving DecidableEq, Repr

/-- The edge on side `s` of the cell `c`. -/
def sideEdge (c : Pt) : Side → Edge
  | .b => bot c
  | .t => top c
  | .l => lft c
  | .r => rgt c

/-- The neighbouring cell across a side. -/
def nb (c : Pt) : Side → Pt
  | .b => (c.1, c.2 - 1)
  | .t => (c.1, c.2 + 1)
  | .l => (c.1 - 1, c.2)
  | .r => (c.1 + 1, c.2)

/-- The opposite side. -/
def Side.opp : Side → Side
  | .b => .t
  | .t => .b
  | .l => .r
  | .r => .l

/-- The arc across side `s` of `c` points out of `c`. -/
def outArc (F : Finset Edge) (c : Pt) (s : Side) : Bool :=
  match s with
  | .b => !up F (bot c)
  | .t => up F (top c)
  | .l => !up F (lft c)
  | .r => up F (rgt c)

/-- An alternating cell: two opposite sides in `F`, the other two not. -/
def Alt (F : Finset Edge) (c : Pt) : Prop :=
  (bot c ∈ F ∧ top c ∈ F ∧ lft c ∉ F ∧ rgt c ∉ F) ∨
  (bot c ∉ F ∧ top c ∉ F ∧ lft c ∈ F ∧ rgt c ∈ F)

/-- `Alt` is decidable. -/
instance (F : Finset Edge) (c : Pt) : Decidable (Alt F c) := by
  unfold Alt; infer_instance

end SolidGridHam

/-! ### From `Basic.D` -/

namespace SolidGridHam
open Finset

/-- The four sides of cell `c`, and the edge set obtained by flipping them. -/
def cellE (c : Pt) : Finset Edge := {bot c, top c, lft c, rgt c}

/-- Flip the cell `c`: toggle its four sides in `F`. -/
def flip (F : Finset Edge) (c : Pt) : Finset Edge := symmDiff F (cellE c)

end SolidGridHam

/-! ### From `Basic.Conn` -/

namespace SolidGridHam

/-- `a` and `b` are the two endpoints of an edge of `F`. -/
def Adj (F : Finset Edge) (a b : Pt) : Prop :=
  ∃ e ∈ F, (e.p = a ∧ e.q = b) ∨ (e.p = b ∧ e.q = a)

/-- Connected by a path of edges of `F` (reflexive-transitive closure of `Adj F`). -/
def Conn (F : Finset Edge) : Pt → Pt → Prop := Relation.ReflTransGen (Adj F)

end SolidGridHam

/-! ### From `Basic.Graph` -/

namespace SolidGridHam
open Finset Classical

/-- The points of `V` connected to `x` by edges of `F`. -/
noncomputable def cls (V : Finset Pt) (F : Finset Edge) (x : Pt) : Finset Pt := V.filter (Conn F x)

/-- The number of connected components of the graph `(V, F)`. -/
noncomputable def ncomp (V : Finset Pt) (F : Finset Edge) : ℕ := (V.image (cls V F)).card

/-- The other end of `e` from `y`. -/
def other (e : Edge) (y : Pt) : Pt := if e.p = y then e.q else e.p

end SolidGridHam

/-! ### From `Cycle.Strip` -/

namespace SolidGridHam
open Finset

/-- The side of `c` facing direction `s`. -/
def front (c : Pt) (s : Side) : Edge := sideEdge c s

/-- The side of `c` facing away from direction `s`. -/
def back (c : Pt) (s : Side) : Edge := sideEdge c s.opp

/-- The first lateral side of `c` for direction `s` (left for up and down, bottom for left and right). -/
def lat1 (c : Pt) : Side → Edge
  | .t => lft c
  | .b => lft c
  | .r => bot c
  | .l => bot c

/-- The first corner of `c` on its back side for direction `s`. -/
def back1 (c : Pt) : Side → Pt
  | .t => (c.1, c.2)
  | .b => (c.1, c.2 + 1)
  | .r => (c.1, c.2)
  | .l => (c.1 + 1, c.2)

/-- The second corner of `c` on its back side for direction `s`. -/
def back2 (c : Pt) : Side → Pt
  | .t => (c.1 + 1, c.2)
  | .b => (c.1 + 1, c.2 + 1)
  | .r => (c.1, c.2 + 1)
  | .l => (c.1 + 1, c.2 + 1)

/-- The first corner of `c` on its front side for direction `s`. -/
def front1 (c : Pt) : Side → Pt
  | .t => (c.1, c.2 + 1)
  | .b => (c.1, c.2)
  | .r => (c.1 + 1, c.2)
  | .l => (c.1, c.2)

/-- The second corner of `c` on its front side for direction `s`. -/
def front2 (c : Pt) : Side → Pt
  | .t => (c.1 + 1, c.2 + 1)
  | .b => (c.1 + 1, c.2)
  | .r => (c.1 + 1, c.2 + 1)
  | .l => (c.1, c.2 + 1)

/-- The `j`-th cell of the strip. -/
def cellJ (c : Pt) (s : Side) (j : ℕ) : Pt :=
  match s with
  | .t => (c.1, c.2 + j)
  | .b => (c.1, c.2 - j)
  | .r => (c.1 + j, c.2)
  | .l => (c.1 - j, c.2)

end SolidGridHam

/-! ### From `Cycle.StripCount` -/

namespace SolidGridHam
open Finset Classical

/-- Flip the first `n` cells of the strip from `c` in direction `s`. -/
def flipCol (F : Finset Edge) (c : Pt) (s : Side) : ℕ → Finset Edge
  | 0 => F
  | n + 1 => flipCol (flip F (cellJ c s n)) c s n

end SolidGridHam

/-! ### From `Cycle.TwoFactor` -/

namespace SolidGridHam
open Finset

namespace TF

/-- The four edges at a point, as a list (searched in this order). -/
def inc4 (z : Pt) : List Edge := [eR z, eL z, eU z, eD z]

end TF

/-! ### From `Cycle.Comp` -/

/-- The points one step from `u` along `F`. -/
def fnbr (F : Finset Edge) (u : Pt) : Finset Pt :=
  (((TF.inc4 u).filter (fun e => decide (e ∈ F))).map (fun e => other e u)).toFinset

/-- Points reachable from `x` in at most `k` steps. -/
def creach (F : Finset Edge) (x : Pt) : ℕ → Finset Pt
  | 0 => {x}
  | k + 1 =>
    let C := creach F x k
    C ∪ C.biUnion (fnbr F)

/-- The component of `x` in `(V, F)`, computed by `|V|` rounds of reachability. -/
def ccls (V : Finset Pt) (F : Finset Edge) (x : Pt) : Finset Pt := creach F x V.card

/-- The number of components of `(V, F)`, computed (a computable `ncomp`). -/
def cncomp (V : Finset Pt) (F : Finset Edge) : ℕ := (V.image (ccls V F)).card

/-! ### From `Cycle.Enum` -/

section
variable {V : Finset Pt} {F G : Finset Edge}

/-- Connectivity, via the computed class. -/
def connB (V : Finset Pt) (F : Finset Edge) (x y : Pt) : Bool := decide (y ∈ ccls V F x)

end

/-! ### From `Cycle.Algorithm` -/

/-- The cells of `V`, listed (lexicographic order on points). -/
def cellList (V : Finset Pt) : List Pt :=
  (((V.filter (IsCell V)).map toLex.toEmbedding).sort (· ≤ ·)).map ofLex

/-- The four sides, in search order. -/
def sidesL : List Side := [.b, .t, .l, .r]

/-! ### From `Path.FindFactor` -/

namespace DF
variable {d : Pt → ℕ}

/-- Black points have an even coordinate sum. -/
def Black (z : Pt) : Prop := (z.1 + z.2) % 2 = 0

/-- `Black` is decidable. -/
instance (z : Pt) : Decidable (Black z) := by unfold Black; infer_instance

/-- The four edges at a point, as a list (searched in this order). -/
def inc4 (z : Pt) : List Edge := [eR z, eL z, eU z, eD z]

/-- A forward alternating step from `u` along `e`: a grid edge, not in `F` when `u` is black, in `F` when `u` is white. -/
def Fwd (V : Finset Pt) (F : Finset Edge) (u : Pt) (e : Edge) : Prop :=
  IsEdge V e ∧ (Black u → e ∉ F) ∧ (¬ Black u → e ∈ F)

/-- `Fwd` is decidable. -/
instance (V : Finset Pt) (F : Finset Edge) (u : Pt) (e : Edge) : Decidable (Fwd V F u e) := by
  unfold Fwd; infer_instance

/-- The points one forward step from `u`. -/
def nbr (V : Finset Pt) (F : Finset Edge) (u : Pt) : Finset Pt :=
  (((inc4 u).filter (fun e => decide (Fwd V F u e))).map (fun e => other e u)).toFinset

/-- The alternating layers: layer `k` holds the points reachable in at most `k` steps from a deficient black point. -/
def layer (V : Finset Pt) (d : Pt → ℕ) (F : Finset Edge) : ℕ → Finset Pt
  | 0 => V.filter (fun z => Black z ∧ deg F z < d z)
  | k + 1 =>
    let L := layer V d F k
    L ∪ L.biUnion (nbr V F)

/-- A backward step from `v` along `e` into `L`: the reverse of a forward step from `other e v ∈ L`. -/
def Bwd (V : Finset Pt) (F : Finset Edge) (L : Finset Pt) (v : Pt) (e : Edge) : Prop :=
  IsEdge V e ∧ other e v ∈ L ∧ (Black v → e ∈ F) ∧ (¬ Black v → e ∉ F)

/-- `Bwd` is decidable. -/
instance (V : Finset Pt) (F : Finset Edge) (L : Finset Pt) (v : Pt) (e : Edge) :
    Decidable (Bwd V F L v e) := by
  unfold Bwd; infer_instance

/-- The first backward step from `v` into `L`, if any. -/
def pred (V : Finset Pt) (F : Finset Edge) (L : Finset Pt) (v : Pt) : Option Edge :=
  (inc4 v).find? (fun e => decide (Bwd V F L v e))

/-- The same layers computed bottom up, each from the previous one only once: `layerAcc V d F k = [layer k, layer (k-1), ..., layer 0]` (`layerAcc_eq`). -/
def layerAcc (V : Finset Pt) (d : Pt → ℕ) (F : Finset Edge) : ℕ → List (Finset Pt)
  | 0 => [V.filter (fun z => Black z ∧ deg F z < d z)]
  | k + 1 =>
    match layerAcc V d F k with
    | [] => []
    | L :: Ls => (L ∪ L.biUnion (nbr V F)) :: L :: Ls

/-- Walk back from `v` down the layers `Ls` (top first), flipping the crossed edges of `F`. `F0` is the edge set the layers were built from. One list entry is consumed per step. -/
def walk (V : Finset Pt) (F0 : Finset Edge) :
    List (Finset Pt) → Pt → Finset Edge → Finset Edge
  | [], _, F => F
  | L :: Ls, v, F =>
    if v ∈ L then walk V F0 Ls v F
    else
      match pred V F0 L v with
      | none => F
      | some e => walk V F0 Ls (other e v) (if Black v then F.erase e else insert e F)

/-- A computable choice of an element of a finite set of points (the lexicographic least). -/
def pick (S : Finset Pt) : Option Pt :=
  match (S.image toLex).min with
  | ⊤ => none
  | (x : Lex (ℤ × ℤ)) => some (ofLex x)

/-- One augmentation: `none` when no deficient white point is reachable. -/
def augStep (V : Finset Pt) (d : Pt → ℕ) (F : Finset Edge) : Option (Finset Edge) :=
  match layerAcc V d F V.card with
  | [] => none
  | L :: Ls =>
    match pick (L.filter (fun w => ¬ Black w ∧ deg F w < d w)) with
    | none => none
    | some w => some (walk V F Ls w F)

/-- Augment at most `n` times. -/
def augLoop (V : Finset Pt) (d : Pt → ℕ) : ℕ → Finset Edge → Finset Edge
  | 0, F => F
  | n + 1, F =>
    match augStep V d F with
    | none => F
    | some F' => augLoop V d n F'

end DF

end SolidGridHam

namespace SolidGridHam
open Finset
open DF

/-- **A verified d-factor algorithm** (degree caps at most 2): augment from the empty set, then check. -/
def findFactor (V : Finset Pt) (d : Pt → ℕ) : Option (Finset Edge) :=
  let F := augLoop V d (V.card + 1) ∅
  if ∀ z ∈ V, deg F z = d z then some F else none

end SolidGridHam

/-! ### From `Path.StuckL4` -/

namespace SolidGridHam

namespace HP
open Finset Classical

/-- **Opposed phantoms.** The out-vertices `a`, `b` differ by 2 along an axis (and by at most 2 along the other), and their phantoms `ma`, `mb` point away from each other along that axis. -/
def Opp (a ma b mb : Pt) : Prop :=
  (b.1 - a.1 = 2 ∧ |b.2 - a.2| ≤ 2 ∧ ma = (a.1 - 1, a.2) ∧ mb = (b.1 + 1, b.2)) ∨
  (b.1 - a.1 = -2 ∧ |b.2 - a.2| ≤ 2 ∧ ma = (a.1 + 1, a.2) ∧ mb = (b.1 - 1, b.2)) ∨
  (b.2 - a.2 = 2 ∧ |b.1 - a.1| ≤ 2 ∧ ma = (a.1, a.2 - 1) ∧ mb = (b.1, b.2 + 1)) ∨
  (b.2 - a.2 = -2 ∧ |b.1 - a.1| ≤ 2 ∧ ma = (a.1, a.2 + 1) ∧ mb = (b.1, b.2 - 1))

/-! ### From `Path.Bridges` -/

/-- A bridge: the strip of `r` cells from cell `q` in direction `a` (a row flipped by the phase). -/
structure Bridge where
  q : Pt
  a : Side
  r : ℕ

namespace Bridge

/-- The `j`-th cell of the bridge. -/
def cell (b : Bridge) (j : ℕ) : Pt := cellJ b.q b.a j

/-- The last cell of the bridge. -/
def E (b : Bridge) : Pt := b.cell (b.r - 1)

end Bridge

/-! ### From `Path.SAlg` -/

section
variable {V W : Finset Pt} {H : Finset Edge}

/-- Some corner of `c` is not connected to its lower-left corner in `(W, H)`. -/
def cutB (W : Finset Pt) (H : Finset Edge) (c : Pt) : Bool :=
  !(connB W H c (c.1 + 1, c.2) && connB W H c (c.1 + 1, c.2 + 1) && connB W H c (c.1, c.2 + 1))

/-- `c` is one of the last two cells of some bridge. -/
def pairSqB (BS : List Bridge) (c : Pt) : Bool :=
  BS.any fun b => decide (c = b.cell (b.r - 2)) || decide (c = b.E)

/-- How a run from a critical square ends: it turns after `r` squares (a row), or meets a non-cell or a cut square at index `k` (stuck). -/
inductive RunEnd
  | row (r : ℕ)
  | stuck (k : ℕ)
  deriving DecidableEq

end

/-! ### From `Path.SPhaseAlg` -/

/-- How a phase ends: stuck, a merging cell, an odd or twisted row, or out of fuel. -/
inductive POut
  | stuck
  | merge (c : Pt)
  | odd (b : Bridge)
  | twist (b : Bridge)
  | fuel

/-- Flipping the last cell of `b` disconnects its back corner from its front corner. -/
def flipSplits (W : Finset Pt) (H : Finset Edge) (b : Bridge) : Bool :=
  !connB W (flip H b.E) (back1 b.E b.a) (front1 b.E b.a)

/-! ### From `Path.Undo` -/

section
variable {V W : Finset Pt} {d : Pt → ℕ} {H : Finset Edge}

/-- A join: flip `n` cells of the strip from `c` in direction `a`. -/
structure Join where
  c : Pt
  a : Side
  n : ℕ

/-- Apply a join to `G`. -/
def Join.apply (G : Finset Edge) (o : Join) : Finset Edge := flipCol G o.c o.a o.n

end

/-! ### From `Path.UndoCount` -/

/-- Apply a list of joins in order. -/
def applyAll (G : Finset Edge) : List Join → Finset Edge
  | [] => G
  | o :: os => applyAll (o.apply G) os

/-! ### From `Path.Node` -/

/-- The back and front corners of the first cell of `b`. -/
def rowStartPair (b : Bridge) : Pt × Pt := (back1 b.q b.a, front1 b.q b.a)

/-! ### From `Path.Reduce` -/

/-- The frame of an alternating cell in which its back and front are dark. -/
def altFrame (G : Finset Edge) (X : Pt) : Side := if bot X ∈ G then .t else .r

/-! ### From `Path.Compat0` -/

/-- The join that flips all cells of `b` but the last. -/
def lowJ (b : Bridge) : Join := ⟨b.q, b.a, b.r - 1⟩

/-- The join that flips the last cell of `b`. -/
def undoJ (b : Bridge) : Join := ⟨b.E, b.a, 1⟩

/-! ### From `Path.S4TheoremR` -/

/-- The start pair of a merging cell (the pair `reduceOut` uses). -/
def mergePair (H : Finset Edge) (X : Pt) : Pt × Pt := (back1 X (altFrame H X), front1 X (altFrame H X))

/-! ### From `Path.ConnSet` -/

/-- The components of `(W, H)` met along a list of points, skipping points already covered. -/
def compsAux (W : Finset Pt) (H : Finset Edge) : List Pt → Finset Pt → List (Finset Pt)
  | [], _ => []
  | x :: xs, cov =>
    if x ∈ cov then compsAux W H xs cov
    else ccls W H x :: compsAux W H xs (cov ∪ ccls W H x)

/-- The points of `W` in lexicographic order. -/
def ptList (W : Finset Pt) : List Pt := ((W.map toLex.toEmbedding).sort (· ≤ ·)).map ofLex

/-- The components of `(W, H)`. -/
def comps (W : Finset Pt) (H : Finset Edge) : List (Finset Pt) := compsAux W H (ptList W) ∅

/-- The pairs of points in one component of `(W, H)`. -/
def connectedPairs (W : Finset Pt) (H : Finset Edge) : Finset (Pt × Pt) :=
  (comps W H).toFinset.biUnion fun C => C ×ˢ C

/-- `x` and `y` are connected, read from the table `S` of connected pairs. -/
def isConnected (S : Finset (Pt × Pt)) (x y : Pt) : Bool := decide ((x, y) ∈ S)

/-! ### From `Path.PhaseS` -/

/-- Some corner of `c` is not connected to its lower-left corner (by the table `S`). -/
def isCutCell (S : Finset (Pt × Pt)) (c : Pt) : Bool :=
  !(isConnected S c (c.1 + 1, c.2) && isConnected S c (c.1 + 1, c.2 + 1) && isConnected S c (c.1, c.2 + 1))

/-- The first alternating cut cell that is not one of the last two cells of a bridge. -/
def findMergingCell (V : Finset Pt) (S : Finset (Pt × Pt)) (H : Finset Edge) (BS : List Bridge) :
    Option Pt :=
  (cellList V).find? fun c => decide (Alt H c) && isCutCell S c && !pairSqB BS c

/-- Cell `q` is critical in direction `a`: its back corners and its front corners are connected pairs, back and front are not connected, the back side is in `H` and the front side is not. -/
def isCritical (S : Finset (Pt × Pt)) (H : Finset Edge) (q : Pt) (a : Side) : Bool :=
  isConnected S (back1 q a) (back2 q a) && isConnected S (front1 q a) (front2 q a) &&
    !isConnected S (back1 q a) (front1 q a) && decide (back q a ∈ H) && decide (front q a ∉ H)

/-- Scan the strip from `q` in direction `a` until the arc orientation changes (a row) or a non-cell or cut cell is met (stuck). -/
def scanRowAux (V : Finset Pt) (S : Finset (Pt × Pt)) (H : Finset Edge) (q : Pt) (a : Side)
    (o : Bool) : ℕ → ℕ → Option RunEnd
  | 0, _ => none
  | fuel + 1, j =>
    if outArc H (cellJ q a (j - 1)) a ≠ o then some (.row j)
    else if ¬ IsCell V (cellJ q a j) ∨ isCutCell S (cellJ q a j) = true then some (.stuck j)
    else scanRowAux V S H q a o fuel (j + 1)

/-- Scan the run from the critical cell `q` in direction `a`. -/
def scanRow (V : Finset Pt) (S : Finset (Pt × Pt)) (H : Finset Edge) (q : Pt) (a : Side) :
    Option RunEnd :=
  scanRowAux V S H q a (outArc H q a) (V.card + 1) 1

/-- The squares of the bridges, as one set. -/
def bridgeSquares (BS : List Bridge) : Finset Pt :=
  (BS.flatMap fun b => (List.range b.r).map b.cell).toFinset

/-- The bridge starting at a critical cell outside the bridge cells `B`, if its run ends in a row. -/
def rowOf (V : Finset Pt) (S : Finset (Pt × Pt)) (H : Finset Edge) (B : Finset Pt)
    (x : Pt × Side) : Option Bridge :=
  if isCritical S H x.1 x.2 && !decide (x.1 ∈ B) then
    match scanRow V S H x.1 x.2 with
    | some (.row r) => some ⟨x.1, x.2, r⟩
    | _ => none
  else none

/-- The first bridge from a critical cell, over all cells and directions. -/
def findRow (V : Finset Pt) (S : Finset (Pt × Pt)) (H : Finset Edge) (BS : List Bridge) :
    Option Bridge :=
  let B := bridgeSquares BS
  ((cellList V).flatMap fun q => sidesL.map fun a => (q, a)).findSome? (rowOf V S H B)

/-- The phase: repeatedly flip rows until a merging cell, an odd or twisted row, a stuck run, or the fuel runs out. -/
def runPhase (V W : Finset Pt) : ℕ → Finset Edge → List Bridge → Finset Edge × List Bridge × POut
  | 0, H, BS => (H, BS, .fuel)
  | n + 1, H, BS =>
    let S := connectedPairs W H
    match findMergingCell V S H BS with
    | some c => (H, BS, .merge c)
    | none =>
      match findRow V S H BS with
      | none => (H, BS, .stuck)
      | some b =>
        if b.r % 2 = 1 then (H, BS, .odd b)
        else if flipSplits W H b then runPhase V W n (flip H b.E) (b :: BS)
        else (H, BS, .twist b)

/-! ### From `Path.SheffBoundary` -/

/-- The four lattice neighbours of `t` with the edges to them. -/
def nbrsL (t : Pt) : List (Pt × Edge) :=
  [((t.1 + 1, t.2), eR t), ((t.1 - 1, t.2), eL t), ((t.1, t.2 + 1), eU t), ((t.1, t.2 - 1), eD t)]

/-! ### From `Path.ReduceS` -/

/-- The connected-pair tables after undoing the last cell of each bridge in turn. -/
def bridgeStatesConn (W : Finset Pt) : Finset Edge → List Bridge → List (Finset (Pt × Pt))
  | _, [] => []
  | H, b :: BS => connectedPairs W (flip H b.E) :: bridgeStatesConn W (flip H b.E) BS

/-- For each bridge, whether the tracked pair is connected in its table, and the pair tracked next. -/
def undoPlanSteps : List (Finset (Pt × Pt)) → List Bridge → Pt × Pt → List (Bool × (Pt × Pt))
  | S :: Ss, b :: BS, uv =>
    if isConnected S uv.1 uv.2 then (true, uv) :: undoPlanSteps Ss BS (rowStartPair b)
    else (false, uv) :: undoPlanSteps Ss BS uv
  | _, _, _ => []

/-- The joins that undo the bridges, `lowJ` or `undoJ` per bridge as `undoPlanSteps` decides. -/
def undoPlan (Ss : List (Finset (Pt × Pt))) (BS : List Bridge) (uv : Pt × Pt) : List Join :=
  List.zipWith (fun b e => if e.1 then lowJ b else undoJ b) BS (undoPlanSteps Ss BS uv)

/-- An alternating cut cell, not among the last two cells of a bridge, compatible with the undo plan. -/
def isGoodMergingCell (W : Finset Pt) (H : Finset Edge) (BS : List Bridge) (Ss : List (Finset (Pt × Pt)))
    (X : Pt) : Bool :=
  decide (Alt H X) && cutB W H X && !pairSqB BS X &&
    (let P := undoPlanSteps Ss BS (mergePair H X)
     (List.finRange BS.length).all fun i =>
      (P.getD i (false, mergePair H X)).1 || decide (X ≠ nb (BS.get i).E (BS.get i).a))

/-- Reduce the number of components using the phase outcome: flip the merging cell or the odd row, then undo the bridges. -/
def reducePieces (V W : Finset Pt) (H : Finset Edge) (BS : List Bridge) : POut → Finset Edge
  | .merge c =>
    let Ss := bridgeStatesConn W H BS
    let X := ((cellList V).find? (isGoodMergingCell W H BS Ss)).getD c
    applyAll (flipCol H X (altFrame H X) 1) (undoPlan Ss BS (mergePair H X))
  | .odd b => applyAll (flipCol H b.q b.a b.r) (undoPlan (bridgeStatesConn W H BS) BS (rowStartPair b))
  | .twist b => applyAll (flipCol H b.q b.a b.r) (undoPlan (bridgeStatesConn W H BS) BS (rowStartPair b))
  | _ => H

/-- Repeat phase and reduction on `V` with phantoms `p, q` until one component (true) or stuck (false). -/
def twoPhantomLoop (V : Finset Pt) (p q : Pt) : ℕ → Finset Edge → Bool
  | 0, G => cncomp (insert q (insert p V)) G == 1
  | n + 1, G =>
    if cncomp (insert q (insert p V)) G == 1 then true
    else
      match runPhase V (insert q (insert p V)) ((insert q (insert p V)).card + 1) G [] with
      | (_, _, .stuck) => false
      | (_, _, .fuel) => false
      | (H, BS, out) => twoPhantomLoop V p q n (reducePieces V (insert q (insert p V)) H BS out)

/-! ### From `Path.LoopF` -/

/-- Find a factor with degrees `dST s t`, add the phantom edges `e0, e1`, and run `twoPhantomLoop`. -/
def twoPhantomTest (V : Finset Pt) (s t p q : Pt) (e0 e1 : Edge) : Bool :=
  match findFactor V (dST s t) with
  | none => false
  | some R => twoPhantomLoop V p q (V.card + 2) (insert e1 (insert e0 R))

/-! ### From `Path.TwoPhWalk` -/

/-- `Far`, decided (king distance at least 2). -/
def isFar (t s : Pt) : Bool :=
  decide (t = s) || !(decide (|t.1 - s.1| ≤ 1) && decide (|t.2 - s.2| ≤ 1))

/-- `Opp` is decidable. -/
instance (a ma b mb : Pt) : Decidable (Opp a ma b mb) := by unfold Opp; infer_instance

/-- Opposed phantoms, decided. -/
def phantomsOpposed (a ma b mb : Pt) : Bool := decide (Opp a ma b mb)

/-- A usable phantom for `t`: a missing lattice neighbour, not `s`'s phantom `q`, not opposed. -/
def isUsablePhantom (V : Finset Pt) (s q t : Pt) (x : Pt × Edge) : Bool :=
  decide (x.1 ∉ V) && decide (x.1 ≠ q) && !phantomsOpposed t x.1 s q

/-- **The walk.** `s` keeps its phantom `q` (edge `e1`); `t` moves until it is Far from `s` and has a usable phantom. -/
def boundaryEndpointsWalk (s q : Pt) (e1 : Edge) : ℕ → Finset Pt → Pt → Bool
  | 0, _, _ => false
  | n + 1, V, t =>
    if V.card ≤ 2 then (nbrsL t).any (fun x => decide (x.1 = s))
    else
      match (nbrsL t).find? (isUsablePhantom V s q t) with
      | some x =>
        if isFar t s then twoPhantomTest V s t x.1 q x.2 e1
        else (nbrsL t).any (fun x => decide (x.1 ∈ V) && decide (x.1 ≠ s) &&
          boundaryEndpointsWalk s q e1 n (V.erase t) x.1)
      | none => (nbrsL t).any (fun x => decide (x.1 ∈ V) && decide (x.1 ≠ s) &&
          boundaryEndpointsWalk s q e1 n (V.erase t) x.1)

/-- **Two boundary endpoints.** If `s` has a missing neighbour, walk with it as `s`'s phantom; otherwise delete `s` once first. -/
def boundaryEndpoints (V : Finset Pt) (s t : Pt) : Bool :=
  if V.card ≤ 2 then (nbrsL t).any (fun x => decide (x.1 = s))
  else
    match (nbrsL s).find? (fun x => decide (x.1 ∉ V)) with
    | some x => boundaryEndpointsWalk s x.1 x.2 12 V t
    | none => (nbrsL s).any (fun x => decide (x.1 ∈ V) && decide (x.1 ≠ t) &&
        boundaryEndpointsWalk x.1 s x.2 12 (V.erase s) t)

end HP

/-! ### From `Path.HoleAdm` -/

namespace HP
open Finset

/-- The height step across `e`: `+1` if the arc points up, `-1` otherwise. -/
def sv (F : Finset Edge) (e : Edge) : ℤ := if up F e then 1 else -1

/-! ### From `Path.HoleRelax` -/

/-- The least `x` coordinate of `V`. -/
def bx0 (V : Finset Pt) : ℤ := if h : V.Nonempty then V.inf' h Prod.fst else 0

/-- The greatest `x` coordinate of `V`. -/
def bx1 (V : Finset Pt) : ℤ := if h : V.Nonempty then V.sup' h Prod.fst else 0

/-- The least `y` coordinate of `V`. -/
def by0 (V : Finset Pt) : ℤ := if h : V.Nonempty then V.inf' h Prod.snd else 0

/-- The greatest `y` coordinate of `V`. -/
def by1 (V : Finset Pt) : ℤ := if h : V.Nonempty then V.sup' h Prod.snd else 0

/-- The width bound on hole values. -/
def boxWidth (V : Finset Pt) : ℤ := bx1 V - bx0 V

/-- The cells strictly inside the box: `bx0 ≤ x < bx1`, `by0 ≤ y < by1`. -/
def boxSquares (V : Finset Pt) : List Pt :=
  (List.range (bx1 V - bx0 V).toNat).flatMap fun (i : ℕ) =>
    (List.range (by1 V - by0 V).toNat).map fun (j : ℕ) => ((bx0 V + (i : ℤ), by0 V + (j : ℤ)) : Pt)

/-- The allowed jumps across `e`, as an interval. -/
def ivl (V : Finset Pt) (F : Finset Edge) (e : Edge) : ℤ × ℤ :=
  if IsEdge V e then (min 0 (sv F e), max 0 (sv F e)) else (0, 0)

/-- The largest lower bound the four sides of `s` force on `f s`. -/
def lowerBound (V : Finset Pt) (F : Finset Edge) (f : Pt → ℤ) (s : Pt) : ℤ :=
  max (max (f (bot s).lo + (ivl V F (bot s)).1) (f (lft s).lo + (ivl V F (lft s)).1))
    (max (f (top s).hi - (ivl V F (top s)).2) (f (rgt s).hi - (ivl V F (rgt s)).2))

/-- The potential `f` does not jump across `e`, or jumps by the height step of a grid edge. -/
def sideOK (V : Finset Pt) (F : Finset Edge) (f : Pt → ℤ) (e : Edge) : Bool :=
  decide (f e.hi - f e.lo = 0 ∨ (IsEdge V e ∧ f e.hi - f e.lo = sv F e))

/-- The four sides of cell `s`. -/
def sides (s : Pt) : List Edge := [bot s, lft s, top s, rgt s]

/-- `f` is admissible: every side of every box cell is `sideOK`, and `f` takes the prescribed values `hs` at the cells `as`. -/
def isAdmissible (V : Finset Pt) (F : Finset Edge) (as : List Pt) (hs : List ℤ) (f : Pt → ℤ) :
    Bool :=
  (boxSquares V).all (fun s => (sides s).all (sideOK V F f)) && (as.zip hs).all (fun ah => f ah.1 == ah.2)

/-- The grid edges across which `f` jumps. -/
def jumpEdges (V : Finset Pt) (f : Pt → ℤ) : Finset Edge :=
  (((boxSquares V).flatMap sides).filter (fun e => decide (IsEdge V e ∧ f e.hi ≠ f e.lo))).toFinset

/-- The number of relaxation rounds: one more than the number of box cells. -/
def kFuel (V : Finset Pt) : ℕ := (boxSquares V).length + 1

/-- The width of the box, in cells. -/
def kWn (V : Finset Pt) : ℕ := (bx1 V - bx0 V).toNat

/-- The height of the box, in cells. -/
def kHn (V : Finset Pt) : ℕ := (by1 V - by0 V).toNat

/-- The cell `c` lies in the box of `V`. -/
def inBox (V : Finset Pt) (c : Pt) : Prop := bx0 V ≤ c.1 ∧ c.1 < bx1 V ∧ by0 V ≤ c.2 ∧ c.2 < by1 V

/-- `inBox` is decidable. -/
instance (V : Finset Pt) (c : Pt) : Decidable (inBox V c) := by unfold inBox; infer_instance

/-- The array index of a box cell (column-major). -/
def idx (V : Finset Pt) (c : Pt) : ℕ := (c.1 - bx0 V).toNat * kHn V + (c.2 - by0 V).toNat

/-- The box cell at array index `k`. -/
def cellOf (V : Finset Pt) (k : ℕ) : Pt := (bx0 V + ((k / kHn V : ℕ) : ℤ), by0 V + ((k % kHn V : ℕ) : ℤ))

/-- Read a potential stored as an array (`0` outside the box). -/
def toFA (V : Finset Pt) (A : Array ℤ) (c : Pt) : ℤ := if inBox V c then A.getD (idx V c) 0 else 0

/-- One Bellman–Ford round: raise every cell to the lower bound its sides force. -/
def roundA (V : Finset Pt) (F : Finset Edge) (A : Array ℤ) : Array ℤ :=
  Array.ofFn (n := kWn V * kHn V) fun k =>
    max (toFA V A (cellOf V k)) (lowerBound V F (toFA V A) (cellOf V k))

/-- Run up to `n` relaxation rounds, stopping early at a fixed point. -/
def relaxA (V : Finset Pt) (F : Finset Edge) : ℕ → Array ℤ → Array ℤ
  | 0, A => A
  | n + 1, A =>
    let A' := roundA V F A
    if (boxSquares V).all (fun c => toFA V A' c == toFA V A c) then A else relaxA V F n A'

/-- The initial potential: the prescribed value `hs` at the cells `as`, minus the box width elsewhere. -/
def kInitA (V : Finset Pt) (as : List Pt) (hs : List ℤ) : Array ℤ :=
  Array.ofFn (n := kWn V * kHn V) fun k => ((as.zip hs).lookup (cellOf V k)).getD (- boxWidth V)

/-- The least potential above the initial one that the relaxation reaches. -/
def classPotential (V : Finset Pt) (F : Finset Edge) (as : List Pt) (hs : List ℤ) : Pt → ℤ :=
  toFA V (relaxA V F (kFuel V) (kInitA V as hs))

/-! ### From `Path.HoleTry` -/

/-- The factor of the flip class with values `hs` at the cells `as`, if the class is nonempty: `F ⊕ jumpEdges φ` for the class potential `φ`. -/
def classSearch (V : Finset Pt) (F : Finset Edge) (as : List Pt) (hs : List ℤ) :
    Option (Finset Edge) :=
  let f := classPotential V F as hs
  if isAdmissible V F as hs f then some (symmDiff F (jumpEdges V f)) else none

/-- The one-hole try: the least admissible potential with value `h` at `t`. -/
def classSearchOne (V : Finset Pt) (F : Finset Edge) (t : Pt) (h : ℤ) : Option (Finset Edge) :=
  classSearch V F [t] [h]

/-- The candidate classes `-|V|, …, |V|`. -/
def classRange (V : Finset Pt) : List ℤ :=
  (List.range (2 * V.card + 1)).map fun (i : ℕ) => (i : ℤ) - V.card

end HP

/-! ### From `Path.HoleOne` -/

namespace HP
open Finset Classical

/-- The box of a set connected by a Hamiltonian path is narrow (`narrow_of_ncomp`). -/
def isNarrow (U : Finset Pt) : Bool :=
  decide (bx1 U - bx0 U < U.card) && decide (by1 U - by0 U < U.card)

/-! ### From `Path.HoleWalk` -/

/-- `fin U s q e1` decides the problem on `U` from `s` to `w` when `w` and `s` are far apart. -/
def holeCaseWalk (fin : Finset Pt → Pt → Pt → Edge → Bool) (w pw : Pt) :
    ℕ → Finset Pt → Pt → Pt → Edge → Bool
  | 0, _, _, _, _ => false
  | n + 1, U, s, q, e1 =>
    if U.card ≤ 2 then (nbrsL w).any (fun x => decide (x.1 = s))
    else if isFar w s && !phantomsOpposed w pw s q then fin U s q e1
    else (nbrsL s).any (fun x => decide (x.1 ∈ U) && decide (x.1 ≠ w) &&
      holeCaseWalk fin w pw n (U.erase s) x.1 s x.2)

/-- Delete `t` (branch over `w`), delete `s` (branch over its successor), then walk. -/
def holeCase (fin : Pt → Edge → Finset Pt → Pt → Pt → Edge → Bool) (V : Finset Pt) (s t : Pt) :
    Bool :=
  if V.card ≤ 2 then (nbrsL t).any (fun x => decide (x.1 = s))
  else (nbrsL t).any fun y => decide (y.1 ∈ V) && decide (y.1 ≠ s) &&
    if (V.erase t).card ≤ 2 then (nbrsL y.1).any (fun x => decide (x.1 = s))
    else (nbrsL s).any fun x => decide (x.1 ∈ V.erase t) && decide (x.1 ≠ y.1) &&
      holeCaseWalk (fin y.1 y.2) y.1 t 10 ((V.erase t).erase s) x.1 s x.2

/-- Per class (`classRange`) the factor `classSearchOne` returns, then the two-phantom loop. -/
def oneHoleFinalTest (U : Finset Pt) (s w t q : Pt) (e0 e1 : Edge) : Bool :=
  isNarrow U &&
    match findFactor U (dST s w) with
    | none => false
    | some R => (classRange U).any fun h =>
        match classSearchOne U (insert e1 (insert e0 R)) t h with
        | some G => twoPhantomLoop U t q (U.card + 2) G
        | none => false

/-- The case where `t` is inner and `s` is not. -/
def oneHoleCase (V : Finset Pt) (s t : Pt) : Bool :=
  holeCase (fun w e0 U s' q e1 => oneHoleFinalTest U s' w t q e0 e1) V s t

/-! ### From `Path.HoleTwoV` -/

/-- The final test when both endpoints are inner: on a narrow box, find a factor, then for every pair of class values at the vortices `t` and `r`, search that class and run `twoPhantomLoop`. -/
def twoHoleFinalTest (U : Finset Pt) (s w t r q : Pt) (e0 e1 : Edge) : Bool :=
  isNarrow U &&
    match findFactor U (dST s w) with
    | none => false
    | some R => (classRange U).any fun h1 => (classRange U).any fun h2 =>
        match classSearch U (insert e1 (insert e0 R)) [t, r] [h1, h2] with
        | some G => twoPhantomLoop U t q (U.card + 2) G
        | none => false

/-- The case where both endpoints are inner. -/
def twoHoleCase (V : Finset Pt) (s t : Pt) : Bool :=
  holeCase (fun w e0 U s' q e1 => twoHoleFinalTest U s' w t s q e0 e1) V s t

/-! ### From `Path.HPFinal` -/

/-- `Inner`, decided. -/
def isInner (V : Finset Pt) (p : Pt) : Bool :=
  decide (IsCell V (p.1 - 1, p.2 - 1)) && decide (IsCell V (p.1, p.2 - 1)) &&
    decide (IsCell V (p.1 - 1, p.2)) && decide (IsCell V p)

/-- **The algorithm.** Decide whether the solid grid graph `V` has a Hamiltonian path from `s` to `t`, by cases on which endpoints are inner (all eight king neighbours in `V`). -/
def decideHamPath (V : Finset Pt) (s t : Pt) : Bool :=
  if isInner V s then (if isInner V t then twoHoleCase V s t else oneHoleCase V t s)
  else if isInner V t then oneHoleCase V s t else boundaryEndpoints V s t

end HP

end SolidGridHam

namespace SolidGridHam

namespace HP

/-- **The statement.** For a solid grid graph `V` and distinct points `s, t ∈ V`, the algorithm
`decideHamPath` returns `true` exactly when `V` has a Hamiltonian path from `s` to `t`: an edge
set of the grid graph on `V` with degree `1` at `s` and `t`, degree `2` everywhere else, and one
connected component. -/
theorem decideHamPath_correct {V : Finset Pt} {s t : Pt}
    (hs : Solid V) (hst : s ≠ t) (hsV : s ∈ V) (htV : t ∈ V) :
    decideHamPath V s t = true ↔ ∃ H, IsFactor V (dST s t) H ∧ ncomp V H = 1 := by
  sorry

end HP

end SolidGridHam
