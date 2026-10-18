/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import SolidGridHam.Basic.Potential

/-!
# Dependency arcs (thesis §4.1–4.2, paper Definition 3)

Every edge `e` of the grid is crossed by one dependency arc, between its low and high
cells. Following the paper, split edges into
`E1(F) = {horizontal edges in F} ∪ {vertical edges not in F}` and `E2(F)` (the rest), and
colour cells by the parity of `x + y`. The arc across `e` leaves the cell of colour `k`
exactly when `e ∈ E_k`. We take colour 1 = odd cells. (The other choice reverses every
arc; nothing below depends on it.)

No consistency argument (thesis Lemmas 4.1, 4.2) is needed: on `ℤ²` this is an explicit
formula.
-/

namespace SolidGridHam

-- Cell colour: true for odd `x + y`.
--
def par (c : Pt) : Bool := decide ((c.1 + c.2) % 2 = 1)

-- `e ∈ E1(F)`.
--
def inE1 (F : Finset Edge) (e : Edge) : Bool :=
  match e.d with
  | .h => decide (e ∈ F)
  | .v => !decide (e ∈ F)

-- The arc across `e` points from its low cell to its high cell.
--
def up (F : Finset Edge) (e : Edge) : Bool := (par e.lo == inE1 F e)

/-! ## Parity bookkeeping -/

lemma par_sub_fst (c : Pt) : par (c.1 - 1, c.2) = !par c := by
  unfold par; by_cases h : (c.1 + c.2) % 2 = 1 <;> simp [h] <;> omega

lemma par_sub_snd (c : Pt) : par (c.1, c.2 - 1) = !par c := by
  unfold par; by_cases h : (c.1 + c.2) % 2 = 1 <;> simp [h] <;> omega

lemma par_add_fst (c : Pt) : par (c.1 + 1, c.2) = !par c := by
  unfold par; by_cases h : (c.1 + c.2) % 2 = 1 <;> simp [h] <;> omega

lemma par_add_snd (c : Pt) : par (c.1, c.2 + 1) = !par c := by
  unfold par; by_cases h : (c.1 + c.2) % 2 = 1 <;> simp [h] <;> omega

lemma par_sub_sub (c : Pt) : par (c.1 - 1, c.2 - 1) = par c := by
  unfold par; by_cases h : (c.1 + c.2) % 2 = 1 <;> simp [h] <;> omega

/-! ## Arcs at a cell

The four sides of a cell, and whether the arc across a side points out of the cell.
-/

inductive Side
  | b
  | t
  | l
  | r
  deriving DecidableEq, Repr

def sideEdge (c : Pt) : Side → Edge
  | .b => bot c
  | .t => top c
  | .l => lft c
  | .r => rgt c

-- The neighbouring cell across a side.
--
def nb (c : Pt) : Side → Pt
  | .b => (c.1, c.2 - 1)
  | .t => (c.1, c.2 + 1)
  | .l => (c.1 - 1, c.2)
  | .r => (c.1 + 1, c.2)

-- The opposite side.
--
def Side.opp : Side → Side
  | .b => .t
  | .t => .b
  | .l => .r
  | .r => .l

def Side.horiz : Side → Bool
  | .b => true
  | .t => true
  | .l => false
  | .r => false

-- The arc across side `s` of `c` points out of `c`.
--
def outArc (F : Finset Edge) (c : Pt) (s : Side) : Bool :=
  match s with
  | .b => !up F (bot c)
  | .t => up F (top c)
  | .l => !up F (lft c)
  | .r => up F (rgt c)

-- Closed form: on horizontal sides the arc points out iff `par c` agrees with membership
-- in `F`; on vertical sides iff they disagree.
--
lemma outArc_eq (F : Finset Edge) (c : Pt) (s : Side) :
    outArc F c s =
      if s.horiz then (par c == decide (sideEdge c s ∈ F))
      else !(par c == decide (sideEdge c s ∈ F)) := by
  obtain ⟨x, y⟩ := c
  cases s
  · have := par_sub_snd (x, y)
    simp only at this
    simp only [outArc, up, inE1, Side.horiz, sideEdge, bot, Edge.lo, this, ite_true]
    cases par (x, y) <;> by_cases hm : (⟨.h, (x, y)⟩ : Edge) ∈ F <;> simp [hm]
  · simp only [outArc, up, inE1, Side.horiz, sideEdge, top, Edge.lo, add_sub_cancel_right,
      ite_true]
    rfl
  · have := par_sub_fst (x, y)
    simp only at this
    simp only [outArc, up, inE1, Side.horiz, sideEdge, lft, Edge.lo, this, ite_false,
      Bool.false_eq_true]
    cases par (x, y) <;> by_cases hm : (⟨.v, (x, y)⟩ : Edge) ∈ F <;> simp [hm]
  · simp only [outArc, up, inE1, Side.horiz, sideEdge, rgt, Edge.lo, add_sub_cancel_right,
      ite_false, Bool.false_eq_true]
    cases par (x, y) <;> by_cases hm : (⟨.v, (x + 1, y)⟩ : Edge) ∈ F <;> simp [hm]

/-! ## Cell configurations -/

-- Membership pattern of the four sides (bottom, top, left, right).
--
def darkB (F : Finset Edge) (c : Pt) : Bool := decide (bot c ∈ F)
def darkT (F : Finset Edge) (c : Pt) : Bool := decide (top c ∈ F)
def darkL (F : Finset Edge) (c : Pt) : Bool := decide (lft c ∈ F)
def darkR (F : Finset Edge) (c : Pt) : Bool := decide (rgt c ∈ F)

-- An alternating cell: two opposite sides in `F`, the other two not.
--
def Alt (F : Finset Edge) (c : Pt) : Prop :=
  (bot c ∈ F ∧ top c ∈ F ∧ lft c ∉ F ∧ rgt c ∉ F) ∨
  (bot c ∉ F ∧ top c ∉ F ∧ lft c ∈ F ∧ rgt c ∈ F)

instance (F : Finset Edge) (c : Pt) : Decidable (Alt F c) := by
  unfold Alt; infer_instance

-- All four arcs point out of `c` (a source) / into `c` (a sink).
--
def Source (F : Finset Edge) (c : Pt) : Prop := ∀ s, outArc F c s = true
def Sink (F : Finset Edge) (c : Pt) : Prop := ∀ s, outArc F c s = false

-- Thesis §4.1: a cell is alternating iff its four arcs agree.
--
lemma alt_iff_uniform (F : Finset Edge) (c : Pt) :
    Alt F c ↔ Source F c ∨ Sink F c := by
  have hs : ∀ s, outArc F c s = _ := outArc_eq F c
  unfold Alt Source Sink
  have e : ∀ P : Side → Bool, (∀ s, P s = true) ↔
      (P .b = true ∧ P .t = true ∧ P .l = true ∧ P .r = true) := by
    intro P; constructor
    · intro h; exact ⟨h _, h _, h _, h _⟩
    · rintro ⟨h1, h2, h3, h4⟩ s; cases s <;> assumption
  have e' : ∀ P : Side → Bool, (∀ s, P s = false) ↔
      (P .b = false ∧ P .t = false ∧ P .l = false ∧ P .r = false) := by
    intro P; constructor
    · intro h; exact ⟨h _, h _, h _, h _⟩
    · rintro ⟨h1, h2, h3, h4⟩ s; cases s <;> assumption
  rw [e, e']
  simp only [hs, Side.horiz, sideEdge, ite_true, ite_false, Bool.false_eq_true]
  cases par c <;>
    by_cases hb : bot c ∈ F <;> by_cases ht : top c ∈ F <;>
    by_cases hl : lft c ∈ F <;> by_cases hr : rgt c ∈ F <;> simp [hb, ht, hl, hr]

end SolidGridHam
