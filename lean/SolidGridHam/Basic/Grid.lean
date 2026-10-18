/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import Mathlib

/-!
# Grid graphs: points, edges, cells, degrees

Lattice points are `ℤ × ℤ`. An edge is named by its lower-left end: `⟨.h, p⟩` joins `p`
and `p + (1,0)`, `⟨.v, p⟩` joins `p` and `p + (0,1)`. A cell is named by its lower-left
corner.

The two cells beside an edge are its *low* cell (below an `h` edge, left of a `v` edge)
and its *high* cell (above / right). Crossing an edge from low to high is the positive
direction used by potentials (`Potential.lean`).
-/

namespace SolidGridHam

abbrev Pt := ℤ × ℤ

inductive Dir
  | h
  | v
  deriving DecidableEq, Repr

structure Edge where
  d : Dir
  p : Pt
  deriving DecidableEq, Repr

namespace Edge

-- The far endpoint of the edge.
--
def q (e : Edge) : Pt :=
  match e.d with
  | .h => (e.p.1 + 1, e.p.2)
  | .v => (e.p.1, e.p.2 + 1)

-- The cell on the low side (below an `h` edge, left of a `v` edge).
--
def lo (e : Edge) : Pt :=
  match e.d with
  | .h => (e.p.1, e.p.2 - 1)
  | .v => (e.p.1 - 1, e.p.2)

-- The cell on the high side (above an `h` edge, right of a `v` edge).
--
def hi (e : Edge) : Pt := e.p

end Edge

/-! ## The four edges of a cell -/

def bot (c : Pt) : Edge := ⟨.h, c⟩
def top (c : Pt) : Edge := ⟨.h, (c.1, c.2 + 1)⟩
def lft (c : Pt) : Edge := ⟨.v, c⟩
def rgt (c : Pt) : Edge := ⟨.v, (c.1 + 1, c.2)⟩

/-! ## The four edges at a point -/

-- Edges leaving `p` to the right, left, up and down.
--
def eR (p : Pt) : Edge := ⟨.h, p⟩
def eL (p : Pt) : Edge := ⟨.h, (p.1 - 1, p.2)⟩
def eU (p : Pt) : Edge := ⟨.v, p⟩
def eD (p : Pt) : Edge := ⟨.v, (p.1, p.2 - 1)⟩

-- Indicator of membership, as a natural number.
--
def ind (F : Finset Edge) (e : Edge) : ℕ := if e ∈ F then 1 else 0

-- Degree of `p` in the edge set `F`.
--
def deg (F : Finset Edge) (p : Pt) : ℕ :=
  ind F (eR p) + ind F (eL p) + ind F (eU p) + ind F (eD p)

/-! ## Grid graphs and factors -/

-- An edge of the grid graph on vertex set `V` (node-induced).
--
def IsEdge (V : Finset Pt) (e : Edge) : Prop := e.p ∈ V ∧ e.q ∈ V

instance (V : Finset Pt) (e : Edge) : Decidable (IsEdge V e) := by
  unfold IsEdge; infer_instance

-- A cell of the grid graph: all four corners are vertices.
--
def IsCell (V : Finset Pt) (c : Pt) : Prop :=
  c ∈ V ∧ (c.1 + 1, c.2) ∈ V ∧ (c.1, c.2 + 1) ∈ V ∧ (c.1 + 1, c.2 + 1) ∈ V

instance (V : Finset Pt) (c : Pt) : Decidable (IsCell V c) := by
  unfold IsCell; infer_instance

-- A factor of the grid graph on `V` with degree function `d`: a set of grid edges in
-- which every vertex `p` has degree `d p`. 2-factors have `d ≡ 2`; path-factors have
-- `d = 1` at the two ends and `2` elsewhere.
--
def IsFactor (V : Finset Pt) (d : Pt → ℕ) (F : Finset Edge) : Prop :=
  (∀ e ∈ F, IsEdge V e) ∧ ∀ p ∈ V, deg F p = d p

-- The degrees of a Hamiltonian `s`–`t` path: `1` at `s` and `t`, `2` everywhere else.
--
def dST (s t : Pt) (z : Pt) : ℕ := if z = s ∨ z = t then 1 else 2

def Is2Factor (V : Finset Pt) (F : Finset Edge) : Prop := IsFactor V (fun _ => 2) F

/-! ## Solid grid graphs -/

-- King-move adjacency between two lattice points that are both outside `V`.
--
def MissAdj (V : Finset Pt) (a b : Pt) : Prop :=
  a ∉ V ∧ b ∉ V ∧ |a.1 - b.1| ≤ 1 ∧ |a.2 - b.2| ≤ 1

-- `V` is solid (no holes): every lattice point outside `V` is joined, by king moves
-- through points outside `V`, to a point strictly left of all of `V`.
-- A bounded face of area > 1 would contain a missing lattice point that cannot escape
-- this way, and conversely.
--
def Solid (V : Finset Pt) : Prop :=
  ∀ a, a ∉ V → ∃ b, Relation.ReflTransGen (MissAdj V) a b ∧ ∀ p ∈ V, b.1 < p.1

/-! ## Basic lemmas -/

@[simp] lemma Edge.hi_mk (d : Dir) (p : Pt) : (Edge.mk d p).hi = p := rfl
@[simp] lemma Edge.lo_h (p : Pt) : (Edge.mk .h p).lo = (p.1, p.2 - 1) := rfl
@[simp] lemma Edge.lo_v (p : Pt) : (Edge.mk .v p).lo = (p.1 - 1, p.2) := rfl
@[simp] lemma Edge.q_h (p : Pt) : (Edge.mk .h p).q = (p.1 + 1, p.2) := rfl
@[simp] lemma Edge.q_v (p : Pt) : (Edge.mk .v p).q = (p.1, p.2 + 1) := rfl

lemma ind_le_one (F : Finset Edge) (e : Edge) : ind F e ≤ 1 := by
  unfold ind; split <;> omega

end SolidGridHam
