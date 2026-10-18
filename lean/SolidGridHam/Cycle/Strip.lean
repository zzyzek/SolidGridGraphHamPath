/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import SolidGridHam.Cycle.Iso

/-!
# Strips: geometry in each direction

A strip runs from a cell `c` in direction `s` (the side it leaves through). For each cell,
relative to `s`:
* `front` is side `s`, `back` is the opposite side, `lat1`, `lat2` are the other two;
* `back1`, `back2`, `front1`, `front2` are the corners, with `lat1 = back1–front1`,
  `lat2 = back2–front2`;
* `outer1`, `outer2` are the edges at `front1`, `front2` pointing away from the strip.

The next cell's back side is this cell's front side.
-/

namespace SolidGridHam

open Finset

def front (c : Pt) (s : Side) : Edge := sideEdge c s
def back (c : Pt) (s : Side) : Edge := sideEdge c s.opp

def lat1 (c : Pt) : Side → Edge
  | .t => lft c
  | .b => lft c
  | .r => bot c
  | .l => bot c

def lat2 (c : Pt) : Side → Edge
  | .t => rgt c
  | .b => rgt c
  | .r => top c
  | .l => top c

def back1 (c : Pt) : Side → Pt
  | .t => (c.1, c.2)
  | .b => (c.1, c.2 + 1)
  | .r => (c.1, c.2)
  | .l => (c.1 + 1, c.2)

def back2 (c : Pt) : Side → Pt
  | .t => (c.1 + 1, c.2)
  | .b => (c.1 + 1, c.2 + 1)
  | .r => (c.1, c.2 + 1)
  | .l => (c.1 + 1, c.2 + 1)

def front1 (c : Pt) : Side → Pt
  | .t => (c.1, c.2 + 1)
  | .b => (c.1, c.2)
  | .r => (c.1 + 1, c.2)
  | .l => (c.1, c.2)

def front2 (c : Pt) : Side → Pt
  | .t => (c.1 + 1, c.2 + 1)
  | .b => (c.1 + 1, c.2)
  | .r => (c.1 + 1, c.2 + 1)
  | .l => (c.1, c.2 + 1)

def outer1 (c : Pt) : Side → Edge
  | .t => ⟨.h, (c.1 - 1, c.2 + 1)⟩
  | .b => ⟨.h, (c.1 - 1, c.2)⟩
  | .r => ⟨.v, (c.1 + 1, c.2 - 1)⟩
  | .l => ⟨.v, (c.1, c.2 - 1)⟩

def outer2 (c : Pt) : Side → Edge
  | .t => ⟨.h, (c.1 + 1, c.2 + 1)⟩
  | .b => ⟨.h, (c.1 + 1, c.2)⟩
  | .r => ⟨.v, (c.1 + 1, c.2 + 1)⟩
  | .l => ⟨.v, (c.1, c.2 + 1)⟩

-- The `j`-th cell of the strip.
--
def cellJ (c : Pt) (s : Side) (j : ℕ) : Pt :=
  match s with
  | .t => (c.1, c.2 + j)
  | .b => (c.1, c.2 - j)
  | .r => (c.1 + j, c.2)
  | .l => (c.1 - j, c.2)

/-! ## Basic facts -/

section geo

variable (c : Pt) (s : Side)

lemma nb_cellJ (j : ℕ) : nb (cellJ c s j) s = cellJ c s (j + 1) := by
  obtain ⟨x, y⟩ := c
  cases s <;> simp [nb, cellJ] <;> ring

lemma cellJ_zero : cellJ c s 0 = c := by
  obtain ⟨x, y⟩ := c; cases s <;> simp [cellJ]

lemma back_nb : back (nb c s) s = front c s := by
  obtain ⟨x, y⟩ := c
  cases s <;> simp [back, front, nb, sideEdge, Side.opp, bot, top, lft, rgt]

lemma back1_nb : back1 (nb c s) s = front1 c s := by
  obtain ⟨x, y⟩ := c; cases s <;> simp [back1, front1, nb]

lemma back2_nb : back2 (nb c s) s = front2 c s := by
  obtain ⟨x, y⟩ := c; cases s <;> simp [back2, front2, nb]

lemma ends_lat1 : Ends (lat1 c s) (back1 c s) (front1 c s) := by
  obtain ⟨x, y⟩ := c
  cases s <;> simp [Ends, lat1, back1, front1, lft, bot, Edge.q]

lemma ends_lat2 : Ends (lat2 c s) (back2 c s) (front2 c s) := by
  obtain ⟨x, y⟩ := c
  cases s <;> simp [Ends, lat2, back2, front2, rgt, top, Edge.q]

lemma ends_back : Ends (back c s) (back1 c s) (back2 c s) := by
  obtain ⟨x, y⟩ := c
  cases s <;> simp [Ends, back, back1, back2, sideEdge, Side.opp, bot, top, lft, rgt, Edge.q]

lemma ends_front : Ends (front c s) (front1 c s) (front2 c s) := by
  obtain ⟨x, y⟩ := c
  cases s <;> simp [Ends, front, front1, front2, sideEdge, bot, top, lft, rgt, Edge.q]

-- The degree at `front1` is read off its four edges.
--
lemma deg_front1 (F : Finset Edge) :
    deg F (front1 c s) =
      ind F (lat1 c s) + ind F (front c s) + ind F (lat1 (nb c s) s) + ind F (outer1 c s) := by
  obtain ⟨x, y⟩ := c
  cases s <;> simp only [deg, front1, lat1, front, outer1, nb, sideEdge, eR, eL, eU, eD,
    lft, rgt, bot, top] <;> (try simp only [add_sub_cancel_right]) <;> omega

lemma deg_front2 (F : Finset Edge) :
    deg F (front2 c s) =
      ind F (lat2 c s) + ind F (front c s) + ind F (lat2 (nb c s) s) + ind F (outer2 c s) := by
  obtain ⟨x, y⟩ := c
  cases s <;> simp only [deg, front2, lat2, front, outer2, nb, sideEdge, eR, eL, eU, eD,
    lft, rgt, bot, top] <;> (try simp only [add_sub_cancel_right]) <;> omega

end geo

/-! ## The planar lemma for each strip direction

For the end cell of an even strip, the dark sides are `lat1` and `lat2`. Splitting needs:
no `G` joins `front1–back2` and `front2–back1` while separating `back1` from `front1`,
when `lat1` and `back` are absent from `G`.
-/

-- Given `u ~ w`, separating `v` from `u` is the same as separating it from `w`.
--
lemma not_conn_swap {G : Finset Edge} {u v w : Pt} (huw : Conn G u w) (h : ¬ Conn G v u) :
    ¬ Conn G v w := fun h' => h (h'.trans huw.symm)

lemma planar_t (G : Finset Edge) (c : Pt) (h1 : lat1 c .t ∉ G) (h2 : back c .t ∉ G)
    (h3 : Conn G (front1 c .t) (back2 c .t)) (h4 : Conn G (front2 c .t) (back1 c .t))
    (h5 : ¬ Conn G (back1 c .t) (front1 c .t)) : False := by
  obtain ⟨x, y⟩ := c
  simp only [lat1, back, sideEdge, Side.opp, front1, back1, back2, front2] at *
  exact planar_cell G x y h2 h1 h3.symm h4 (not_conn_swap h3 h5)

lemma planar_r (G : Finset Edge) (c : Pt) (h1 : lat1 c .r ∉ G) (h2 : back c .r ∉ G)
    (h3 : Conn G (front1 c .r) (back2 c .r)) (h4 : Conn G (front2 c .r) (back1 c .r))
    (h5 : ¬ Conn G (back1 c .r) (front1 c .r)) : False := by
  obtain ⟨x, y⟩ := c
  simp only [lat1, back, sideEdge, Side.opp, front1, back1, back2, front2] at *
  exact planar_cell G x y h1 h2 h3 h4 h5

lemma planar_b (G : Finset Edge) (c : Pt) (h1 : lat1 c .b ∉ G) (h2 : back c .b ∉ G)
    (h3 : Conn G (front1 c .b) (back2 c .b)) (h4 : Conn G (front2 c .b) (back1 c .b))
    (h5 : ¬ Conn G (back1 c .b) (front1 c .b)) : False := by
  obtain ⟨x, y⟩ := c
  simp only [lat1, back, sideEdge, Side.opp, front1, back1, back2, front2] at *
  set I := reflectIso
  set G' := G.image I.g
  have m : ∀ e, I.g e ∈ G' ↔ e ∈ G := fun e => I.mem_image_iff
  have cn : ∀ u v, Conn G' (I.f u) (I.f v) ↔ Conn G u v := fun u v => I.conn_iff
  have fP : ∀ p : Pt, I.f p = (p.1, -p.2) := fun _ => rfl
  apply planar_cell G' x (-y - 1)
  · have : bot (x, -y - 1) = I.g (top (x, y)) := by
      simp [bot, top, I, reflectIso, rE, rP]; ring
    rw [this, m]; exact h2
  · have : lft (x, -y - 1) = I.g (lft (x, y)) := by
      simp [lft, I, reflectIso, rE]
    rw [this, m]; exact h1
  · have e1 : ((x + 1, -y - 1) : Pt) = I.f (x + 1, y + 1) := by rw [fP]; simp; ring
    have e2 : ((x, -y - 1 + 1) : Pt) = I.f (x, y) := by rw [fP]; simp
    rw [e1, e2, cn]; exact h3.symm
  · have e1 : ((x + 1, -y - 1 + 1) : Pt) = I.f (x + 1, y) := by rw [fP]; simp
    have e2 : ((x, -y - 1) : Pt) = I.f (x, y + 1) := by rw [fP]; simp; ring
    rw [e1, e2, cn]; exact h4
  · have e1 : ((x, -y - 1) : Pt) = I.f (x, y + 1) := by rw [fP]; simp; ring
    have e2 : ((x + 1, -y - 1) : Pt) = I.f (x + 1, y + 1) := by rw [fP]; simp; ring
    rw [e1, e2, cn]
    intro h'; exact h5 (h'.trans h3.symm)

lemma planar_l (G : Finset Edge) (c : Pt) (h1 : lat1 c .l ∉ G) (h2 : back c .l ∉ G)
    (h3 : Conn G (front1 c .l) (back2 c .l)) (h4 : Conn G (front2 c .l) (back1 c .l))
    (h5 : ¬ Conn G (back1 c .l) (front1 c .l)) : False := by
  obtain ⟨x, y⟩ := c
  simp only [lat1, back, sideEdge, Side.opp, front1, back1, back2, front2] at *
  set I := transposeIso
  set G' := G.image I.g
  have m : ∀ e, I.g e ∈ G' ↔ e ∈ G := fun e => I.mem_image_iff
  have cn : ∀ u v, Conn G' (I.f u) (I.f v) ↔ Conn G u v := fun u v => I.conn_iff
  have fP : ∀ p : Pt, I.f p = (p.2, p.1) := fun _ => rfl
  apply planar_b G' (y, x)
  · have : lat1 (y, x) .b = I.g (bot (x, y)) := by simp [lat1, lft, bot, I, transposeIso, tE, tP]
    rw [this, m]; exact h1
  · have : back (y, x) .b = I.g (rgt (x, y)) := by
      simp [back, sideEdge, Side.opp, top, rgt, I, transposeIso, tE, tP]
    rw [this, m]; exact h2
  · simp only [front1, back2]
    rw [show ((y, x) : Pt) = I.f (x, y) from rfl, show ((y + 1, x + 1) : Pt) = I.f (x + 1, y + 1)
      from rfl, cn]; exact h3
  · simp only [front2, back1]
    rw [show ((y + 1, x) : Pt) = I.f (x, y + 1) from rfl, show ((y, x + 1) : Pt) = I.f (x + 1, y)
      from rfl, cn]; exact h4
  · simp only [back1, front1]
    rw [show ((y, x + 1) : Pt) = I.f (x + 1, y) from rfl, show ((y, x) : Pt) = I.f (x, y)
      from rfl, cn]; exact h5

lemma planar_lat (G : Finset Edge) (c : Pt) (s : Side) (h1 : lat1 c s ∉ G) (h2 : back c s ∉ G)
    (h3 : Conn G (front1 c s) (back2 c s)) (h4 : Conn G (front2 c s) (back1 c s))
    (h5 : ¬ Conn G (back1 c s) (front1 c s)) : False := by
  cases s
  · exact planar_b G c h1 h2 h3 h4 h5
  · exact planar_t G c h1 h2 h3 h4 h5
  · exact planar_l G c h1 h2 h3 h4 h5
  · exact planar_r G c h1 h2 h3 h4 h5

end SolidGridHam
