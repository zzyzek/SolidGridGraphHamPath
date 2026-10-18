/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import Mathlib
public import SolidGridHam.Algorithm

@[expose] public section

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

namespace Edge

end Edge

/-! ## The four edges of a cell -/

/-! ## The four edges at a point -/

/-! ## Grid graphs and factors -/

def Is2Factor (V : Finset Pt) (F : Finset Edge) : Prop := IsFactor V (fun _ => 2) F

/-! ## Solid grid graphs -/

/-! ## Basic lemmas -/

@[simp] lemma Edge.hi_mk (d : Dir) (p : Pt) : (Edge.mk d p).hi = p := rfl
@[simp] lemma Edge.lo_h (p : Pt) : (Edge.mk .h p).lo = (p.1, p.2 - 1) := rfl
@[simp] lemma Edge.lo_v (p : Pt) : (Edge.mk .v p).lo = (p.1 - 1, p.2) := rfl
@[simp] lemma Edge.q_h (p : Pt) : (Edge.mk .h p).q = (p.1 + 1, p.2) := rfl
@[simp] lemma Edge.q_v (p : Pt) : (Edge.mk .v p).q = (p.1, p.2 + 1) := rfl

lemma ind_le_one (F : Finset Edge) (e : Edge) : ind F e ≤ 1 := by
  unfold ind; split <;> omega

end SolidGridHam
