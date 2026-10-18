/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.Chain

/-!
# Lemma 5.7: after an even strip, a Type III cell (if any) lies on the created chain

Notation: strip of length `k + 2` from `c` in direction `s`, end cell `u = c_(k+1)`,
`F' = flipCol F c s (k + 2)`. The created chain is the chain of `u` in `F'`.
-/

namespace ULHC

open Finset Classical

/-! ## Geometry around a strip -/

section geo3

variable (c : Pt) (s : Side)

-- The two cells sharing a side of `c` are `c` and its neighbour across that side.
--
lemma cell_of_side {d : Pt} {tf : Side} (h : sideEdge c tf ∈ cellE d) : d = c ∨ d = nb c tf := by
  rw [mem_cellE_iff] at h
  obtain ⟨x, y⟩ := c
  cases tf <;> rcases h with h | h <;>
    simp only [sideEdge, bot, top, lft, rgt, Edge.hi_mk, Edge.lo_h, Edge.lo_v] at h <;>
    subst h <;> simp [nb]

lemma lat1_side_nb : lat1 c s = sideEdge (nb c (latA s)) (latA s).opp := by
  obtain ⟨x, y⟩ := c; cases s <;> simp [lat1, latA, sideEdge, nb, Side.opp, bot, top, lft, rgt]

lemma lat2_side_nb : lat2 c s = sideEdge (nb c (latB s)) (latB s).opp := by
  obtain ⟨x, y⟩ := c; cases s <;> simp [lat2, latB, sideEdge, nb, Side.opp, bot, top, lft, rgt]

lemma outer1_side_nb : outer1 c s = sideEdge (nb c (latA s)) s := by
  obtain ⟨x, y⟩ := c; cases s <;> simp [outer1, latA, sideEdge, nb, bot, top, lft, rgt]

lemma outer2_side_nb : outer2 c s = sideEdge (nb c (latB s)) s := by
  obtain ⟨x, y⟩ := c; cases s <;> simp [outer2, latB, sideEdge, nb, bot, top, lft, rgt]

-- The lateral neighbour of the next cell has this cell's outer edge as its back side.
--
lemma outer1_side_nb_next : outer1 c s = sideEdge (nb (nb c s) (latA s)) s.opp := by
  obtain ⟨x, y⟩ := c; cases s <;> simp [outer1, latA, sideEdge, nb, Side.opp, bot, top, lft, rgt]
   

lemma outer2_side_nb_next : outer2 c s = sideEdge (nb (nb c s) (latB s)) s.opp := by
  obtain ⟨x, y⟩ := c; cases s <;> simp [outer2, latB, sideEdge, nb, Side.opp, bot, top, lft, rgt]
   

lemma outer1_not_mem (j m : ℕ) : outer1 (cellJ c s j) s ∉ cellE (cellJ c s m) := by
  obtain ⟨x, y⟩ := c
  cases s <;> simp [cellE, outer1, cellJ, bot, top, lft, rgt]

lemma outer2_not_mem (j m : ℕ) : outer2 (cellJ c s j) s ∉ cellE (cellJ c s m) := by
  obtain ⟨x, y⟩ := c
  cases s <;> simp [cellE, outer2, cellJ, bot, top, lft, rgt]

lemma lat1_beyond_not_mem (n m : ℕ) (hm : m < n) :
    lat1 (cellJ c s n) s ∉ cellE (cellJ c s m) := lat1_not_mem c s (by omega)

-- The cell `g` beside `c` across `lat1 c s`, seen in the frame of direction `s`.
--
lemma side_back2 : back2 (nb c (latA s)) s = back1 c s := by
  obtain ⟨x, y⟩ := c; cases s <;> simp [back1, back2, latA, nb]

lemma side_front2 : front2 (nb c (latA s)) s = front1 c s := by
  obtain ⟨x, y⟩ := c; cases s <;> simp [front1, front2, latA, nb]

lemma latB_eq_opp (tf : Side) : latB tf = (latA tf).opp := by cases tf <;> rfl

lemma side_lat2 : lat2 (nb c (latA s)) s = lat1 c s := by
  rw [lat2_eq, latB_eq_opp, lat1_side_nb]

lemma side_front : front (nb c (latA s)) s = outer1 c s := by
  rw [outer1_side_nb]; rfl

lemma side_back_next : back (nb (nb c s) (latA s)) s = outer1 c s := by
  rw [outer1_side_nb_next]; rfl

lemma back2_not_side_corner :
    back2 c s ∉ ({back1 (nb c (latA s)) s, back2 (nb c (latA s)) s, front1 (nb c (latA s)) s,
      front2 (nb c (latA s)) s} : Finset Pt) := by
  obtain ⟨x, y⟩ := c
  cases s <;> simp [back1, back2, front1, front2, latA, nb] <;> omega

lemma side_lat1_not_mem (j m : ℕ) : lat1 (nb (cellJ c s j) (latA s)) s ∉ cellE (cellJ c s m) := by
  obtain ⟨x, y⟩ := c
  cases s <;> simp [cellE, lat1, latA, nb, cellJ, bot, top, lft, rgt] <;> omega

end geo3

lemma Ends.inV {V : Finset Pt} {e : Edge} {a b : Pt} (h : Ends e a b) (hV : e.p ∈ V ∧ e.q ∈ V) :
    a ∈ V ∧ b ∈ V := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [← h1, ← h2] <;> tauto

lemma Ends.isEdge {V : Finset Pt} {e : Edge} {a b : Pt} (h : Ends e a b) (ha : a ∈ V)
    (hb : b ∈ V) : IsEdge V e := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> unfold IsEdge <;> rw [h1, h2] <;> tauto

lemma cut_ends {P : Finset Pt} {e : Edge} {a b : Pt} (h : Ends e a b) :
    Cut P e ↔ (a ∈ P ↔ b ∉ P) := by
  unfold Cut
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> (rw [h1, h2]; try tauto)

/-! ## Not alternating implies not Type III -/

lemma alt_of_pattern {F : Finset Edge} {d : Pt} {tf : Side} (h1 : back d tf ∈ F) (h2 : front d tf ∈ F)
    (h3 : lat1 d tf ∉ F) (h4 : lat2 d tf ∉ F) : Alt F d := by
  unfold Alt
  cases tf <;> simp only [back, front, lat1, lat2, sideEdge, Side.opp] at h1 h2 h3 h4 <;> tauto

lemma notTypeIII_of_not_alt {V : Finset Pt} {F : Finset Edge} {d : Pt} (h : ¬ Alt F d) :
    NotTypeIII V F d := fun _ h1 h2 h3 h4 => absurd (alt_of_pattern h1 h2 h3 h4) h

lemma notTypeIII_of_corners {V : Finset Pt} {F : Finset Edge} {d : Pt}
    (h : Conn F d (d.1 + 1, d.2) ∧ Conn F d (d.1, d.2 + 1) ∧ Conn F d (d.1 + 1, d.2 + 1)) :
    NotTypeIII V F d := by
  intro tf _ _ _ _
  obtain ⟨x, y⟩ := d
  obtain ⟨h1, h2, h3⟩ := h
  cases tf <;> simp only [back1, front1] at * <;>
    first
    | exact h2 | exact h1 | exact h2.symm.trans h3 | exact h1.symm.trans h3
    | exact h2.symm.trans h1 | exact h1.symm.trans h2 | exact h2.symm | exact h1.symm

/-! ## The strip after flipping -/

section after

variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hk : k % 2 = 0) (hpat : StripPat F c s (k + 2))
include hk hpat

omit hk hpat in
lemma mem_after (e : Edge) :
    e ∈ flipCol F c s (k + 2) ↔ (e ∈ F ↔ nOn c s (k + 2) e % 2 = 0) := mem_flipCol F c s _ e

lemma lat1_after {j : ℕ} (hj : j ≤ k + 1) :
    lat1 (cellJ c s j) s ∈ flipCol F c s (k + 2) ↔ j % 2 = 0 := by
  rw [mem_after, nOn_lat1 c s (by omega), (hpat.2.1 j (by omega)).1]; omega

lemma lat2_after {j : ℕ} (hj : j ≤ k + 1) :
    lat2 (cellJ c s j) s ∈ flipCol F c s (k + 2) ↔ j % 2 = 0 := by
  rw [mem_after, nOn_lat2 c s (by omega), (hpat.2.1 j (by omega)).2]; omega

lemma front_after {j : ℕ} (hj : j ≤ k) :
    front (cellJ c s j) s ∈ flipCol F c s (k + 2) ↔ j % 2 = 1 := by
  rw [mem_after, nOn_front_mid c s (by omega), hpat.2.2 j (by omega)]
  have : j + 1 < k + 2 := by omega
  simp [this]

lemma front_end_after : front (cellJ c s (k + 1)) s ∈ flipCol F c s (k + 2) := by
  rw [mem_after, nOn_front_last c s (k + 1), hpat.2.2 (k + 1) (by omega)]
  simp; omega

lemma back_after : back c s ∉ flipCol F c s (k + 2) := by
  rw [mem_after, nOn_back c s (by omega)]; simp [hpat.1]

lemma back_after_j {j : ℕ} (hj : 1 ≤ j) (hj' : j ≤ k + 1) :
    back (cellJ c s j) s ∈ flipCol F c s (k + 2) ↔ j % 2 = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  rw [back_cellJ_succ, front_after hk hpat (by omega)]; omega

-- Every strip cell except the first is not alternating after the flip.
--
lemma not_alt_after {j : ℕ} (hj : 1 ≤ j) (hj' : j ≤ k + 1) :
    ¬ Alt (flipCol F c s (k + 2)) (cellJ c s j) := by
  intro ha
  have hl1 := lat1_after hk hpat (j := j) (by omega)
  have hb := back_after_j hk hpat hj hj'
  have hf : front (cellJ c s j) s ∈ flipCol F c s (k + 2) ↔ j % 2 = 1 := by
    rcases (show j ≤ k ∨ j = k + 1 by omega) with h | rfl
    · exact front_after hk hpat h
    · constructor
      · intro _; omega
      · intro _; exact front_end_after hk hpat
  rw [lat1_eq] at hl1
  simp only [back, front] at hb hf
  unfold Alt at ha
  generalize hd : cellJ c s j = d at *
  obtain ⟨x, y⟩ := d
  cases s <;> simp only [latA, sideEdge, Side.opp] at hl1 hb hf <;>
    rcases Nat.mod_two_eq_zero_or_one j with h | h <;> simp_all

end after

/-! ## Corners of a cell, in frame form -/

-- All four corners connected, stated from the lower-left corner.
--
def AllConn (F : Finset Edge) (d : Pt) : Prop :=
  Conn F d (d.1 + 1, d.2) ∧ Conn F d (d.1, d.2 + 1) ∧ Conn F d (d.1 + 1, d.2 + 1)

lemma allConn_of_frame {F : Finset Edge} {d : Pt} (tf : Side)
    (h1 : Conn F (back1 d tf) (back2 d tf)) (h2 : Conn F (back1 d tf) (front1 d tf))
    (h3 : Conn F (back1 d tf) (front2 d tf)) : AllConn F d := by
  obtain ⟨x, y⟩ := d
  unfold AllConn
  cases tf <;> simp only [back1, back2, front1, front2] at h1 h2 h3 ⊢ <;>
    refine ⟨?_, ?_, ?_⟩ <;>
    first
    | exact h1 | exact h2 | exact h3 | exact h1.symm | exact h2.symm | exact h3.symm
    | exact h2.symm.trans h1 | exact h2.symm.trans h3

lemma frame_of_allConn {F : Finset Edge} {d : Pt} (h : AllConn F d) (tf : Side) :
    Conn F (back1 d tf) (back2 d tf) ∧ Conn F (back1 d tf) (front1 d tf) ∧
      Conn F (back1 d tf) (front2 d tf) := by
  obtain ⟨x, y⟩ := d
  obtain ⟨h1, h2, h3⟩ := h
  cases tf <;> simp only [back1, back2, front1, front2] <;>
    refine ⟨?_, ?_, ?_⟩ <;>
    first
    | exact h1 | exact h2 | exact h3 | exact h1.symm | exact h2.symm | exact h3.symm
    | exact h2.symm.trans h1 | exact h2.symm.trans h3 | exact h1.symm.trans h2
    | exact h1.symm.trans h3

lemma notTypeIII_of_allConn {V : Finset Pt} {F : Finset Edge} {d : Pt} (h : AllConn F d) :
    NotTypeIII V F d := fun tf _ _ _ _ => (frame_of_allConn h tf).2.1

lemma alt_adj {F : Finset Edge} {d : Pt} (ha : Alt F d) (tf : Side) :
    (sideEdge d tf ∈ F ↔ sideEdge d (latA tf) ∉ F) ∧ (sideEdge d tf ∈ F ↔ sideEdge d (latB tf) ∉ F) := by
  unfold Alt at ha
  cases tf <;> simp only [sideEdge, latA, latB] <;> tauto

/-! ## A cell all of whose sides are dark is a class of its own -/

lemma corner_step {F : Finset Edge} {K : Finset Pt} {x : Pt} {e1 e2 : Edge} {a1 b1 a2 b2 : Pt}
    (h1 : Ends e1 a1 b1) (h2 : Ends e2 a2 b2) (he1 : e1 ∈ F) (he2 : e2 ∈ F) (hne : e1 ≠ e2)
    (hd : deg F x = 2) (i1 : x = a1 ∨ x = b1) (i2 : x = a2 ∨ x = b2)
    (k1 : a1 ∈ K ∧ b1 ∈ K) (k2 : a2 ∈ K ∧ b2 ∈ K) : ∀ y, Adj F x y → y ∈ K := by
  intro y hxy
  obtain ⟨f, hf, hfe⟩ := hxy
  have hfx : f.p = x ∨ f.q = x := by
    rcases hfe with ⟨q, _⟩ | ⟨_, q⟩
    · exact Or.inl q
    · exact Or.inr q
  have hfy : f.p = y ∨ f.q = y := by
    rcases hfe with ⟨_, q⟩ | ⟨q, _⟩
    · exact Or.inr q
    · exact Or.inl q
  rcases inc_of_deg_two hd he1 ((h1.inc_iff x).2 i1) he2 ((h2.inc_iff x).2 i2) hne hf hfx with
    rfl | rfl
  · rcases (h1.inc_iff y).1 hfy with rfl | rfl
    · exact k1.1
    · exact k1.2
  · rcases (h2.inc_iff y).1 hfy with rfl | rfl
    · exact k2.1
    · exact k2.2

lemma four_sides_class {V : Finset Pt} {F : Finset Edge} (hF : Deg2 V F) {g : Pt} (hg : IsCell V g)
    (tf : Side) (h1 : back g tf ∈ F) (h2 : front g tf ∈ F) (h3 : lat1 g tf ∈ F) (h4 : lat2 g tf ∈ F)
    {z : Pt} (hz : Conn F (back1 g tf) z) :
    z ∈ ({back1 g tf, back2 g tf, front1 g tf, front2 g tf} : Finset Pt) := by
  set K : Finset Pt := {back1 g tf, back2 g tf, front1 g tf, front2 g tf}
  obtain ⟨vb1, vb2, vf1, vf2⟩ := isCell_corners hg tf
  have eb := ends_back g tf; have ef := ends_front g tf
  have el1 := ends_lat1 g tf; have el2 := ends_lat2 g tf
  have mb1 : back1 g tf ∈ K := by simp [K]
  have mb2 : back2 g tf ∈ K := by simp [K]
  have mf1 : front1 g tf ∈ K := by simp [K]
  have mf2 : front2 g tf ∈ K := by simp [K]
  -- distinct sides
  have nq : ∀ (p q : Pt → Side → Pt), (∀ t', p g t' ≠ q g t') → p g tf ≠ q g tf := fun _ _ h => h tf
  have d1 : front1 g tf ≠ back1 g tf := by obtain ⟨x, y⟩ := g; cases tf <;> simp [back1, front1]
  have d2 : front1 g tf ≠ back2 g tf := by obtain ⟨x, y⟩ := g; cases tf <;> simp [back2, front1]
  have d3 : front2 g tf ≠ back1 g tf := by obtain ⟨x, y⟩ := g; cases tf <;> simp [back1, front2]
  have d4 : front2 g tf ≠ back2 g tf := by obtain ⟨x, y⟩ := g; cases tf <;> simp [back2, front2]
  have bf : back g tf ≠ lat1 g tf := eb.ne_of el1 d1 d2
  have bl2 : back g tf ≠ lat2 g tf := eb.ne_of el2 d3 d4
  have fl1 : front g tf ≠ lat1 g tf := ef.ne_of el1.swap d1.symm d3.symm
  have fl2 : front g tf ≠ lat2 g tf := ef.ne_of el2.swap d2.symm d4.symm
  have hK : Closed F K := by
    intro x hx y hxy
    simp only [K, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact corner_step eb el1 h1 h3 bf (hF.2 _ vb1) (Or.inl rfl) (Or.inl rfl) ⟨mb1, mb2⟩
        ⟨mb1, mf1⟩ y hxy
    · exact corner_step eb el2 h1 h4 bl2 (hF.2 _ vb2) (Or.inr rfl) (Or.inl rfl) ⟨mb1, mb2⟩
        ⟨mb2, mf2⟩ y hxy
    · exact corner_step ef el1 h2 h3 fl1 (hF.2 _ vf1) (Or.inl rfl) (Or.inr rfl) ⟨mf1, mf2⟩
        ⟨mb1, mf1⟩ y hxy
    · exact corner_step ef el2 h2 h4 fl2 (hF.2 _ vf2) (Or.inr rfl) (Or.inr rfl) ⟨mf1, mf2⟩
        ⟨mb2, mf2⟩ y hxy
  exact closed_conn hK mb1 hz

/-! ## Lemma 5.7 -/

section l57

variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hF : Deg2 V F) (hT : NoTypeIII V F) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat F c s (k + 2))
  (hsep : ¬ Conn F (back1 c s) (front1 c s))

include hT hk hcell hpat in
lemma end_same : Conn F (back1 (cellJ c s (k + 1)) s) (back2 (cellJ c s (k + 1)) s) := by
  have hu := hcell (k + 1) le_rfl
  obtain ⟨_, hl, hf⟩ := hpat
  have l1 := (hl (k + 1) (by omega)).1.2 (by omega)
  have l2 := (hl (k + 1) (by omega)).2.2 (by omega)
  have fF : front (cellJ c s (k + 1)) s ∉ F := by
    intro h; have := (hf (k + 1) (by omega)).1 h; omega
  have bF : back (cellJ c s (k + 1)) s ∉ F := by
    rw [back_cellJ_succ]; intro h; have := (hf k (by omega)).1 h; omega
  -- `u` is alternating with its lateral sides dark: rotate to the frame where they are
  -- back and front.
  have ha : Alt F (cellJ c s (k + 1)) := by
    rw [lat1_eq] at l1; rw [lat2_eq] at l2
    simp only [back, front] at fF bF
    generalize cellJ c s (k + 1) = r at *
    obtain ⟨x, y⟩ := r
    cases s <;> simp only [latA, latB, sideEdge, Side.opp] at l1 l2 fF bF <;> unfold Alt <;> tauto
  exact (frame_of_allConn (alt_corners_conn hT hu ha) s).1

include hF hT hk hcell hpat hsep in
-- The first cell is not Type III after the flip: all its corners are joined.
--
lemma start_notTypeIII : NotTypeIII V (flipCol F c s (k + 2)) c := by
  obtain ⟨F1, hF1, _, _, _, _, hodd⟩ :=
    strip_even_rel k hk F hF hcell hpat hsep (end_same hT hk hcell hpat)
  have hl1 := (lat1_after hk hpat (j := 0) (by omega)).2 rfl
  have hl2 := (lat2_after hk hpat (j := 0) (by omega)).2 rfl
  rw [cellJ_zero] at hl1 hl2
  have c1 : Conn (flipCol F c s (k + 2)) (back1 c s) (front1 c s) := (ends_lat1 c s).conn hl1
  have c2 : Conn (flipCol F c s (k + 2)) (back2 c s) (front2 c s) := (ends_lat2 c s).conn hl2
  have hbF1 : back c s ∈ F1 := by
    rw [hF1, mem_flip_iff]
    have := back_not_mem c s (m := k + 1) (by omega)
    have := hpat.1
    tauto
  have c3 : Conn F1 (back1 c s) (back2 c s) := (ends_back c s).conn hbF1
  have c3' : Conn (flipCol F c s (k + 2)) (back1 c s) (back2 c s) :=
    (hodd _ _ (not_mid_start c s k).1 (not_mid_back2 c s k)).2 (Or.inl c3)
  exact notTypeIII_of_allConn (allConn_of_frame s c3' c1 (c3'.trans c2))

include hF hk hcell hpat in
-- A lateral neighbour of an even strip cell is not alternating after the flip.
--
lemma lateral_even_not_alt {j : ℕ} (hj : j ≤ k) (hje : j % 2 = 0) :
    ¬ Alt (flipCol F c s (k + 2)) (nb (cellJ c s j) (latA s)) ∧
      ¬ Alt (flipCol F c s (k + 2)) (nb (cellJ c s j) (latB s)) := by
  have hcj := hcell j (by omega)
  obtain ⟨_, _, f1V, f2V⟩ := isCell_corners hcj s
  have d1 := deg_front1 (cellJ c s j) s F
  have d2 := deg_front2 (cellJ c s j) s F
  rw [hF.2 _ f1V] at d1
  rw [hF.2 _ f2V] at d2
  rw [nb_cellJ] at d1 d2
  have l1 : lat1 (cellJ c s j) s ∉ F := fun h => by
    have := (hpat.2.1 j (by omega)).1.1 h; omega
  have l2 : lat2 (cellJ c s j) s ∉ F := fun h => by
    have := (hpat.2.1 j (by omega)).2.1 h; omega
  have fr : front (cellJ c s j) s ∉ F := fun h => by
    have := (hpat.2.2 j (by omega)).1 h
    have q : j + 1 < k + 2 := by omega
    simp only [q, iff_true] at this; omega
  have n1 : lat1 (cellJ c s (j + 1)) s ∈ F := (hpat.2.1 (j + 1) (by omega)).1.2 (by omega)
  have n2 : lat2 (cellJ c s (j + 1)) s ∈ F := (hpat.2.1 (j + 1) (by omega)).2.2 (by omega)
  have i0 : ∀ e, e ∉ F → ind F e = 0 := fun e h => by simp [ind, h]
  have i1 : ∀ e, e ∈ F → ind F e = 1 := fun e h => by simp [ind, h]
  rw [i0 _ l1, i0 _ fr, i1 _ n1] at d1
  rw [i0 _ l2, i0 _ fr, i1 _ n2] at d2
  have o1 : outer1 (cellJ c s j) s ∈ F := by
    by_contra h; rw [i0 _ h] at d1; omega
  have o2 : outer2 (cellJ c s j) s ∈ F := by
    by_contra h; rw [i0 _ h] at d2; omega
  -- After the flip: the lateral side is dark and the outer edge is unchanged.
  have o1' : outer1 (cellJ c s j) s ∈ flipCol F c s (k + 2) := by
    rw [mem_after, nOn_zero c s (fun m _ => outer1_not_mem c s j m)]; simp [o1]
  have o2' : outer2 (cellJ c s j) s ∈ flipCol F c s (k + 2) := by
    rw [mem_after, nOn_zero c s (fun m _ => outer2_not_mem c s j m)]; simp [o2]
  have l1' := (lat1_after hk hpat (j := j) (by omega)).2 hje
  have l2' := (lat2_after hk hpat (j := j) (by omega)).2 hje
  constructor
  · intro ha
    have := (alt_adj ha s).2
    rw [latB_eq_opp, ← lat1_side_nb, ← outer1_side_nb] at this
    exact (this.1 o1') l1'
  · intro ha
    have := (alt_adj ha s).1
    have e : latA s = (latB s).opp := by cases s <;> rfl
    rw [e, ← lat2_side_nb, ← outer2_side_nb] at this
    exact (this.1 o2') l2'

include hk hpat in
-- With both front corners of the end cell continuing forward, the cell beyond the end is
-- not alternating after the flip.
--
lemma beyond_not_alt (h1 : lat1 (cellJ c s (k + 2)) s ∈ F) :
    ¬ Alt (flipCol F c s (k + 2)) (cellJ c s (k + 2)) := by
  intro ha
  have hb : back (cellJ c s (k + 2)) s ∈ flipCol F c s (k + 2) := by
    rw [back_cellJ_succ]; exact front_end_after hk hpat
  have hl : lat1 (cellJ c s (k + 2)) s ∈ flipCol F c s (k + 2) := by
    rw [mem_after, nOn_zero c s (fun m hm => lat1_not_mem c s (by omega))]; simp [h1]
  have := (alt_adj ha s.opp).1
  rw [latA_opp, ← lat1_eq] at this
  exact (this.1 hb) hl

include hk hpat in
-- Edges that the flip turns dark: even lateral sides, and the end cell's front side.
--
lemma darkened {e : Edge} (h1 : e ∈ flipCol F c s (k + 2)) (h2 : e ∉ F) :
    (∃ j ≤ k, j % 2 = 0 ∧ (e = lat1 (cellJ c s j) s ∨ e = lat2 (cellJ c s j) s)) ∨
      e = front (cellJ c s (k + 1)) s := by
  rw [mem_after] at h1
  have hodd : nOn c s (k + 2) e % 2 = 1 := by
    by_contra h; exact h2 (h1.2 (by omega))
  have hne : nOn c s (k + 2) e ≠ 0 := by omega
  unfold nOn at hne
  obtain ⟨m, hm⟩ := Finset.card_ne_zero.1 hne
  simp only [Finset.mem_filter, Finset.mem_range] at hm
  obtain ⟨hmk, hme⟩ := hm
  rw [cellE_frame _ s] at hme
  simp only [Finset.mem_insert, Finset.mem_singleton] at hme
  rcases hme with h | h | h | h
  · -- a back side
    exfalso
    rcases m with _ | m
    · rw [cellJ_zero] at h; rw [h] at h2; exact h2 hpat.1
    · rw [back_cellJ_succ] at h
      rw [h, nOn_front_mid c s (by omega)] at hodd; omega
  · rcases (show m ≤ k ∨ m = k + 1 by omega) with hm' | rfl
    · exfalso; rw [h, nOn_front_mid c s (by omega)] at hodd; omega
    · exact Or.inr h
  · left
    refine ⟨m, ?_, ?_, Or.inl h⟩
    · by_contra hm'
      have : m = k + 1 := by omega
      subst this
      exact h2 (h ▸ (hpat.2.1 (k + 1) (by omega)).1.2 (by omega))
    · by_contra hm'
      exact h2 (h ▸ (hpat.2.1 m hmk).1.2 (by omega))
  · left
    refine ⟨m, ?_, ?_, Or.inr h⟩
    · by_contra hm'
      have : m = k + 1 := by omega
      subst this
      exact h2 (h ▸ (hpat.2.1 (k + 1) (by omega)).2.2 (by omega))
    · by_contra hm'
      exact h2 (h ▸ (hpat.2.1 m hmk).2.2 (by omega))

include hF hT hk hcell hpat hsep in
-- A cell with an edge that the flip turned dark is not Type III (case γ: both front corners
-- of the end cell continue forward).
--
lemma darkened_cell_notTypeIII (hγ : lat1 (cellJ c s (k + 2)) s ∈ F) {d : Pt} {e : Edge}
    (he1 : e ∈ flipCol F c s (k + 2)) (he2 : e ∉ F) (hed : e ∈ cellE d) :
    NotTypeIII V (flipCol F c s (k + 2)) d := by
  rcases darkened hk hpat he1 he2 with ⟨j, hj, hje, h | h⟩ | h
  · rw [h, lat1_eq] at hed
    rcases cell_of_side _ hed with rfl | rfl
    · rcases j with _ | j
      · rw [cellJ_zero]; exact start_notTypeIII hF hT hk hcell hpat hsep
      · exact notTypeIII_of_not_alt (not_alt_after hk hpat (by omega) (by omega))
    · exact notTypeIII_of_not_alt (lateral_even_not_alt hF hk hcell hpat hj hje).1
  · rw [h, lat2_eq] at hed
    rcases cell_of_side _ hed with rfl | rfl
    · rcases j with _ | j
      · rw [cellJ_zero]; exact start_notTypeIII hF hT hk hcell hpat hsep
      · exact notTypeIII_of_not_alt (not_alt_after hk hpat (by omega) (by omega))
    · exact notTypeIII_of_not_alt (lateral_even_not_alt hF hk hcell hpat hj hje).2
  · rw [h] at hed
    simp only [front] at hed
    rcases cell_of_side _ hed with rfl | rfl
    · exact notTypeIII_of_not_alt (not_alt_after hk hpat (by omega) le_rfl)
    · rw [nb_cellJ]; exact notTypeIII_of_not_alt (beyond_not_alt hk hpat hγ)

include hF hk hcell hpat in
-- A middle corner of the odd part is not an end of a dark side of a Type III cell.
--
lemma mid_not_end (_hγ : lat1 (cellJ c s (k + 2)) s ∈ F) {d : Pt} {e : Edge} {z : Pt}
    (hz : IsMid c s k z) (he : e ∈ flipCol F c s (k + 2)) (hez : e.p = z ∨ e.q = z)
    (hed : e ∈ cellE d) : NotTypeIII V (flipCol F c s (k + 2)) d := by
  obtain ⟨j, hjo, hjk, hzj⟩ := hz
  have hF' : Deg2 V (flipCol F c s (k + 2)) := deg2_flipCol _ F hF hpat (fun j hj => hcell j (by omega))
  have hfr : front (cellJ c s j) s ∈ flipCol F c s (k + 2) := (front_after hk hpat (by omega)).2 hjo
  have nmid : ∀ m, 1 ≤ m → m ≤ k + 1 → NotTypeIII V (flipCol F c s (k + 2)) (cellJ c s m) :=
    fun m h1 h2 => notTypeIII_of_not_alt (not_alt_after hk hpat h1 h2)
  have hfrc : ∀ d', front (cellJ c s j) s ∈ cellE d' →
      NotTypeIII V (flipCol F c s (k + 2)) d' := by
    intro d' h
    simp only [front] at h
    rcases cell_of_side _ h with rfl | rfl
    · exact nmid j (by omega) (by omega)
    · rw [nb_cellJ]; exact nmid (j + 1) (by omega) (by omega)
  rcases hzj with rfl | rfl
  · -- `z = front1 c_j`: its two edges after the flip are `front c_j` and `lat1 c_(j+1)`.
    have hl : lat1 (cellJ c s (j + 1)) s ∈ flipCol F c s (k + 2) :=
      (lat1_after hk hpat (by omega)).2 (by omega)
    have zV : front1 (cellJ c s j) s ∈ V := (isCell_corners (hcell j (by omega)) s).2.2.1
    have e1 : (front (cellJ c s j) s).p = front1 (cellJ c s j) s ∨
        (front (cellJ c s j) s).q = front1 (cellJ c s j) s :=
      ((ends_front _ s).inc_iff _).2 (Or.inl rfl)
    have e2 : (lat1 (cellJ c s (j + 1)) s).p = front1 (cellJ c s j) s ∨
        (lat1 (cellJ c s (j + 1)) s).q = front1 (cellJ c s j) s := by
      have := ends_lat1 (cellJ c s (j + 1)) s
      rw [back1_cellJ_succ] at this
      exact (this.inc_iff _).2 (Or.inl rfl)
    have hne : front (cellJ c s j) s ≠ lat1 (cellJ c s (j + 1)) s := by
      intro h
      have := front_mem_self c s j
      exact absurd (h ▸ this) (lat1_not_mem c s (j := j + 1) (m := j) (by omega))
    rcases inc_of_deg_two (hF'.2 _ zV) hfr e1 hl e2 hne he hez with rfl | rfl
    · exact hfrc d hed
    · rw [lat1_eq] at hed
      rcases cell_of_side _ hed with rfl | rfl
      · exact nmid (j + 1) (by omega) (by omega)
      · exact notTypeIII_of_not_alt
          (lateral_even_not_alt hF hk hcell hpat (j := j + 1) (by omega) (by omega)).1
  · have hl : lat2 (cellJ c s (j + 1)) s ∈ flipCol F c s (k + 2) :=
      (lat2_after hk hpat (by omega)).2 (by omega)
    have zV : front2 (cellJ c s j) s ∈ V := (isCell_corners (hcell j (by omega)) s).2.2.2
    have e1 : (front (cellJ c s j) s).p = front2 (cellJ c s j) s ∨
        (front (cellJ c s j) s).q = front2 (cellJ c s j) s :=
      ((ends_front _ s).inc_iff _).2 (Or.inr rfl)
    have e2 : (lat2 (cellJ c s (j + 1)) s).p = front2 (cellJ c s j) s ∨
        (lat2 (cellJ c s (j + 1)) s).q = front2 (cellJ c s j) s := by
      have := ends_lat2 (cellJ c s (j + 1)) s
      have hb : back2 (cellJ c s (j + 1)) s = front2 (cellJ c s j) s := by
        rw [← nb_cellJ, back2_nb]
      rw [hb] at this
      exact (this.inc_iff _).2 (Or.inl rfl)
    have hne : front (cellJ c s j) s ≠ lat2 (cellJ c s (j + 1)) s := by
      intro h
      have := front_mem_self c s j
      exact absurd (h ▸ this) (lat2_not_mem c s (j := j + 1) (m := j) (by omega))
    rcases inc_of_deg_two (hF'.2 _ zV) hfr e1 hl e2 hne he hez with rfl | rfl
    · exact hfrc d hed
    · rw [lat2_eq] at hed
      rcases cell_of_side _ hed with rfl | rfl
      · exact nmid (j + 1) (by omega) (by omega)
      · exact notTypeIII_of_not_alt
          (lateral_even_not_alt hF hk hcell hpat (j := j + 1) (by omega) (by omega)).2

include hF hT hk hcell hpat hsep in
-- **Classes of a Type III cell (case γ).** Its dark sides lie in the classes of the end
-- cell's back and front corners.
--
theorem typeIII_classes (hγ : lat1 (cellJ c s (k + 2)) s ∈ F) {d : Pt} (hd : IsCell V d)
    {tf : Side} (hb : back d tf ∈ flipCol F c s (k + 2)) (hf : front d tf ∈ flipCol F c s (k + 2))
    (hl1 : lat1 d tf ∉ flipCol F c s (k + 2)) (hl2 : lat2 d tf ∉ flipCol F c s (k + 2))
    (hn : ¬ Conn (flipCol F c s (k + 2)) (back1 d tf) (front1 d tf)) :
    (Conn (flipCol F c s (k + 2)) (back1 d tf) (back1 (cellJ c s (k + 1)) s) ∧
        Conn (flipCol F c s (k + 2)) (front1 d tf) (front1 (cellJ c s (k + 1)) s)) ∨
      (Conn (flipCol F c s (k + 2)) (back1 d tf) (front1 (cellJ c s (k + 1)) s) ∧
        Conn (flipCol F c s (k + 2)) (front1 d tf) (back1 (cellJ c s (k + 1)) s)) := by
  set F' := flipCol F c s (k + 2)
  have hT' : ¬ NotTypeIII V F' d := fun h => hn (h tf hb hf hl1 hl2)
  have hbd : back d tf ∈ cellE d := by rw [cellE_frame d tf]; simp
  have hfd : front d tf ∈ cellE d := by rw [cellE_frame d tf]; simp
  -- The two dark sides were dark before the flip.
  have hbF : back d tf ∈ F := by
    by_contra h; exact hT' (darkened_cell_notTypeIII hF hT hk hcell hpat hsep hγ hb h hbd)
  have hfF : front d tf ∈ F := by
    by_contra h; exact hT' (darkened_cell_notTypeIII hF hT hk hcell hpat hsep hγ hf h hfd)
  -- Their ends were joined before the flip.
  have hxy : Conn F (back1 d tf) (front1 d tf) := by
    by_cases h1 : lat1 d tf ∈ F
    · exact (ends_lat1 d tf).conn h1
    by_cases h2 : lat2 d tf ∈ F
    · exact (((ends_back d tf).conn hbF).trans ((ends_lat2 d tf).conn h2)).trans
        ((ends_front d tf).conn hfF).symm
    · exact hT d hd tf hbF hfF h1 h2
  -- The ends are not middle corners.
  have nx : ¬ IsMid c s k (back1 d tf) := fun hz =>
    hT' (mid_not_end hF hk hcell hpat hγ hz hb (((ends_back d tf).inc_iff _).2 (Or.inl rfl))
      hbd)
  have ny : ¬ IsMid c s k (front1 d tf) := fun hz =>
    hT' (mid_not_end hF hk hcell hpat hγ hz hf (((ends_front d tf).inc_iff _).2 (Or.inl rfl))
      hfd)
  -- Transfer through the split and the odd part.
  obtain ⟨F1, _, _, _, hrel, hfine, hodd⟩ :=
    strip_even_rel k hk F hF hcell hpat hsep (end_same hT hk hcell hpat)
  obtain ⟨na, nb'⟩ := end_not_mid c s k
  have up : ∀ x y, ¬ IsMid c s k x → ¬ IsMid c s k y → Conn F1 x y → Conn F' x y :=
    fun x y hx hy h => (hodd x y hx hy).2 (Or.inl h)
  have h1 : ¬ Conn F1 (back1 d tf) (front1 d tf) := fun h => hn (up _ _ nx ny h)
  rcases (hfine _ _).1 hxy with h | ⟨h2, h3⟩ | ⟨h2, h3⟩
  · exact absurd h h1
  · exact Or.inl ⟨up _ _ nx na h2, (up _ _ nb' ny h3).symm⟩
  · exact Or.inr ⟨up _ _ nx nb' h2, (up _ _ na ny h3).symm⟩

include hF hT hk hcell hpat hsep in
-- The end cell's `lat1` side is an inter side of the flipped factor, on the end cell's chain.
--
lemma end_inter :
    Inter V (flipCol F c s (k + 2)) (lat1 (cellJ c s (k + 1)) s) ∧
      lat1 (cellJ c s (k + 1)) s ∈
        EB V (flipCol F c s (k + 2)) (cellJ c s (k + 1)) := by
  have hcu := hcell (k + 1) le_rfl
  obtain ⟨b1, _, f1, _⟩ := isCell_corners hcu s
  have hsplit := even_end_border k hk F hF hcell hpat hsep (end_same hT hk hcell hpat)
  have hE : IsEdge V (lat1 (cellJ c s (k + 1)) s) := (ends_lat1 _ s).isEdge b1 f1
  have hI : Inter V (flipCol F c s (k + 2)) (lat1 (cellJ c s (k + 1)) s) := by
    refine ⟨hE, fun h => ?_, fun h => hsplit (((ends_lat1 _ s).conn_iff _).1 h)⟩
    have := (lat1_after hk hpat (j := k + 1) le_rfl).1 h; omega
  refine ⟨hI, ?_⟩
  simp only [EB, Finset.mem_filter]
  refine ⟨mem_GE.2 hE, hI, cellJ c s (k + 1), ?_, by rw [cellE_frame _ s]; simp⟩
  simp only [chainCells, Finset.mem_filter]
  exact ⟨mem_cells.2 hcu, Relation.ReflTransGen.refl⟩

include hF hT hk hcell hpat hsep in
-- **Case α:** the end cell's `front1` corner turns sideways. Then the cell `g` beside the end
-- cell (across `lat1`) is Type III after the flip and lies on the end cell's chain.
--
theorem alpha_typeIII (hα : lat1 (cellJ c s (k + 2)) s ∉ F) :
    nb (cellJ c s (k + 1)) (latA s) ∈ chainCells V (flipCol F c s (k + 2)) (cellJ c s (k + 1)) ∧
      ¬ NotTypeIII V (flipCol F c s (k + 2)) (nb (cellJ c s (k + 1)) (latA s)) := by
  have hcu := hcell (k + 1) le_rfl
  have hck := hcell k (by omega)
  obtain ⟨_, _, f1V, _⟩ := isCell_corners hcu s
  obtain ⟨_, _, k1V, _⟩ := isCell_corners hck s
  have i0 : ∀ e, e ∉ F → ind F e = 0 := fun e h => by simp [ind, h]
  have i1 : ∀ e, e ∈ F → ind F e = 1 := fun e h => by simp [ind, h]
  have uL1 : lat1 (cellJ c s (k + 1)) s ∈ F := (hpat.2.1 (k + 1) (by omega)).1.2 (by omega)
  have uF : front (cellJ c s (k + 1)) s ∉ F := fun h => by
    have := (hpat.2.2 (k + 1) (by omega)).1 h; omega
  have kL1 : lat1 (cellJ c s k) s ∉ F := fun h => by
    have := (hpat.2.1 k (by omega)).1.1 h; omega
  have kF : front (cellJ c s k) s ∉ F := fun h => by
    have := ((hpat.2.2 k (by omega)).1 h).2 (by omega); omega
  -- The outer edges at both lateral corners of `g` are dark (degree count).
  have d1 := deg_front1 (cellJ c s (k + 1)) s F
  rw [hF.2 _ f1V, nb_cellJ, i1 _ uL1, i0 _ uF, i0 _ hα] at d1
  have o1 : outer1 (cellJ c s (k + 1)) s ∈ F := by
    by_contra h; rw [i0 _ h] at d1; omega
  have d0 := deg_front1 (cellJ c s k) s F
  rw [hF.2 _ k1V, nb_cellJ, i0 _ kL1, i0 _ kF, i1 _ uL1] at d0
  have o0 : outer1 (cellJ c s k) s ∈ F := by
    by_contra h; rw [i0 _ h] at d0; omega
  -- The sides and corners of `g`.
  have gF : front (nb (cellJ c s (k + 1)) (latA s)) s = outer1 (cellJ c s (k + 1)) s :=
    side_front _ s
  have gB : back (nb (cellJ c s (k + 1)) (latA s)) s = outer1 (cellJ c s k) s := by
    rw [← nb_cellJ]; exact side_back_next _ s
  have gL2 := side_lat2 (cellJ c s (k + 1)) s
  have gb2 := side_back2 (cellJ c s (k + 1)) s
  have gf2 := side_front2 (cellJ c s (k + 1)) s
  have eB := ends_back (nb (cellJ c s (k + 1)) (latA s)) s
  have eF := ends_front (nb (cellJ c s (k + 1)) (latA s)) s
  have vB := eB.inV (hF.1 _ (gB ▸ o0))
  have vF := eF.inV (hF.1 _ (gF ▸ o1))
  have hg : IsCell V (nb (cellJ c s (k + 1)) (latA s)) :=
    isCell_of_corners _ s vB.1 vB.2 vF.1 vF.2
  -- Its outer side is light: otherwise `g` is a 4-cycle of `F` holding `back2` of the end cell.
  have oF : lat1 (nb (cellJ c s (k + 1)) (latA s)) s ∉ F := by
    intro h
    have hz : Conn F (back1 (nb (cellJ c s (k + 1)) (latA s)) s) (back2 (cellJ c s (k + 1)) s) := by
      refine (eB.conn (gB ▸ o0)).trans ?_
      rw [gb2]; exact end_same hT hk hcell hpat
    exact back2_not_side_corner _ s
      (four_sides_class hF hg s (gB ▸ o0) (gF ▸ o1) h (gL2 ▸ uL1) hz)
  -- After the flip.
  have oF' : lat1 (nb (cellJ c s (k + 1)) (latA s)) s ∉ flipCol F c s (k + 2) := by
    rw [mem_after, nOn_zero c s (fun m _ => side_lat1_not_mem c s (k + 1) m)]; simp [oF]
  have l2F' : lat2 (nb (cellJ c s (k + 1)) (latA s)) s ∉ flipCol F c s (k + 2) := by
    rw [gL2]; intro h; have := (lat1_after hk hpat (j := k + 1) le_rfl).1 h; omega
  have bF' : back (nb (cellJ c s (k + 1)) (latA s)) s ∈ flipCol F c s (k + 2) := by
    rw [gB, mem_after, nOn_zero c s (fun m _ => outer1_not_mem c s k m)]; simp [o0]
  have fF' : front (nb (cellJ c s (k + 1)) (latA s)) s ∈ flipCol F c s (k + 2) := by
    rw [gF, mem_after, nOn_zero c s (fun m _ => outer1_not_mem c s (k + 1) m)]; simp [o1]
  have hsplit := even_end_border k hk F hF hcell hpat hsep (end_same hT hk hcell hpat)
  refine ⟨?_, fun h => hsplit ?_⟩
  · obtain ⟨hI, _⟩ := end_inter hF hT hk hcell hpat hsep
    simp only [chainCells, Finset.mem_filter]
    refine ⟨mem_cells.2 hg, Relation.ReflTransGen.single
      ⟨hcu, hg, _, hI, by rw [cellE_frame _ s]; simp, ?_⟩⟩
    rw [lat1_side_nb]; exact side_mem_cellE _ _
  · have h1 := h s bF' fF' oF' l2F'
    have hb := eB.conn bF'
    have hf := eF.conn fF'
    rw [gb2] at hb
    rw [gf2] at hf
    exact (hb.symm.trans h1).trans hf

include hF hT hk hcell hpat hsep in
-- **Lemma 5.7.** If the factor after an even strip flip has a Type III cell, then the chain
-- of the end cell has one.
--
theorem lemma57 (hs : Solid V) (x0 : Pt) (hconn : ∀ z ∈ V, Conn (GE V) x0 z) {d : Pt}
    (hd : IsCell V d) (hd3 : ¬ NotTypeIII V (flipCol F c s (k + 2)) d) :
    ∃ d' ∈ chainCells V (flipCol F c s (k + 2)) (cellJ c s (k + 1)),
      ¬ NotTypeIII V (flipCol F c s (k + 2)) d' := by
  by_cases hγ : lat1 (cellJ c s (k + 2)) s ∈ F
  · by_contra hno
    have hC : ∀ d' ∈ chainCells V (flipCol F c s (k + 2)) (cellJ c s (k + 1)),
        NotTypeIII V (flipCol F c s (k + 2)) d' :=
      fun d' hd' => by_contra fun h => hno ⟨d', hd', h⟩
    have hF' : Deg2 V (flipCol F c s (k + 2)) :=
      deg2_flipCol _ F hF hpat (fun j hj => hcell j (by omega))
    obtain ⟨P, hB, hcut⟩ := chain_border_l hs hF' x0 hconn _ hC
    simp only [NotTypeIII, not_forall] at hd3
    obtain ⟨tf, hb, hf, hl1, hl2, hn⟩ := hd3
    obtain ⟨hI, hEB⟩ := end_inter hF hT hk hcell hpat hsep
    have hu := (hcut _ hI.1).2 hEB
    rw [cut_ends (ends_lat1 _ s)] at hu
    obtain ⟨b1, _, f1, _⟩ := isCell_corners hd tf
    have hE : IsEdge V (lat1 d tf) := (ends_lat1 d tf).isEdge b1 f1
    have hdc : Cut P (lat1 d tf) := by
      rw [cut_ends (ends_lat1 d tf)]
      rcases typeIII_classes hF hT hk hcell hpat hsep hγ hd hb hf hl1 hl2 hn with
        ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [hB.same_side h1, hB.same_side h2]; exact hu
      · rw [hB.same_side h1, hB.same_side h2]; tauto
    have hon := on_chain_of_side hd (by rw [cellE_frame d tf]; simp) ((hcut _ hE).1 hdc)
    exact hn (hC d hon tf hb hf hl1 hl2)
  · obtain ⟨hmem, h3⟩ := alpha_typeIII hF hT hk hcell hpat hsep hγ
    exact ⟨_, hmem, h3⟩

end l57

end ULHC
