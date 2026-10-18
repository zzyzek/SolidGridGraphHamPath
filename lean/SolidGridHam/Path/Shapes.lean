/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import SolidGridHam.Path.Agree

/-!
# Cut-square shapes: Sheffield's Lemma 1

A square is a **cut square** of `F` when its corners do not all lie on one piece, and a **merging
square** when it is also alternating (flipping it joins the two pieces of its dark sides).

**Lemma 1** (Sheffield, §4.3): if a cut square and its four neighbours are not merging squares,
and its corners have degree 2, then it is **critical** (two corners from each piece, the
same-piece pairs adjacent, exactly one of the two same-piece sides dark) or a **corner** square
(one corner alone, the two sides at the opposite corner dark).

The proof only uses degree 2 at the square's own corners. At a notch endpoint, viewed on
`W = insert p V`, every corner has degree 2 (`t` through its edge to `p`), so Lemma 1 holds with
the squares of `W`; the squares at `p` are the only ones the algorithm never flips.
-/

namespace SolidGridHam

namespace HP

open Finset Classical

section shapes

variable {F : Finset Edge}

-- Not all four corners on one piece.
--
def CutSq (F : Finset Edge) (c : Pt) : Prop :=
  ¬ (Conn F c (c.1 + 1, c.2) ∧ Conn F c (c.1 + 1, c.2 + 1) ∧ Conn F c (c.1, c.2 + 1))

-- The square across side `s` of `c` is a merging square (seen from `c`'s frame `s`: its back
-- corners are `c`'s front corners).
--
def MergeAcross (F : Finset Edge) (c : Pt) (s : Side) : Prop :=
  Alt F (nb c s) ∧ ¬ Conn F (front1 c s) (front2 c s)

-- Critical in frame `s`: back pair and front pair, each on one piece, the two pieces different,
-- exactly one of the back and front sides dark.
--
def CriticalIn (F : Finset Edge) (c : Pt) (s : Side) : Prop :=
  Conn F (back1 c s) (back2 c s) ∧ Conn F (front1 c s) (front2 c s) ∧
    ¬ Conn F (back1 c s) (front1 c s) ∧ Xor (back c s ∈ F) (front c s ∈ F)

-- Corner in frame `s`: `front1` alone and the sides at `back2` (back, lat2) dark, or `front2`
-- alone and the sides at `back1` (back, lat1) dark.
--
def CornerIn (F : Finset Edge) (c : Pt) (s : Side) : Prop :=
  (¬ Conn F (front1 c s) (back1 c s) ∧ ¬ Conn F (front1 c s) (front2 c s) ∧
    Conn F (back1 c s) (back2 c s) ∧ Conn F (back2 c s) (front2 c s) ∧
    back c s ∈ F ∧ lat2 c s ∈ F) ∨
  (¬ Conn F (front2 c s) (back2 c s) ∧ ¬ Conn F (front2 c s) (front1 c s) ∧
    Conn F (back1 c s) (back2 c s) ∧ Conn F (back1 c s) (front1 c s) ∧
    back c s ∈ F ∧ lat1 c s ∈ F)

-- **The square across the front.** Dark lateral sides beyond the front, a light front, and front
-- corners on different pieces make the square across the front a merging square.
--
lemma merge_across (c : Pt) (s : Side) (h1 : lat1 (nb c s) s ∈ F) (h2 : lat2 (nb c s) s ∈ F)
    (hf : front c s ∉ F) (hn : ¬ Conn F (front1 c s) (front2 c s)) : MergeAcross F c s := by
  refine ⟨alt_of_lats h1 h2 (by rw [back_nb]; exact hf) ?_, hn⟩
  intro hff
  have e1 := ends_lat1 (nb c s) s
  have e2 := ends_lat2 (nb c s) s
  rw [back1_nb] at e1; rw [back2_nb] at e2
  have k1 := e1.conn h1
  have k2 := e2.conn h2
  have k3 := (ends_front (nb c s) s).conn hff
  exact hn (k1.trans (k3.trans k2.symm))

-- A front corner of degree 2 whose two sides on `c` are light continues beyond the front.
--
lemma cutoff_front1 (c : Pt) (s : Side) (hd : deg F (front1 c s) = 2) (h1 : lat1 c s ∉ F)
    (h2 : front c s ∉ F) : lat1 (nb c s) s ∈ F := by
  have := deg_front1 c s F
  rw [hd, ind_of_not_mem h1, ind_of_not_mem h2] at this
  by_contra h; rw [ind_of_not_mem h] at this
  have : ind F (outer1 c s) ≤ 1 := by unfold ind; split_ifs <;> omega
  omega

lemma cutoff_front2 (c : Pt) (s : Side) (hd : deg F (front2 c s) = 2) (h1 : lat2 c s ∉ F)
    (h2 : front c s ∉ F) : lat2 (nb c s) s ∈ F := by
  have := deg_front2 c s F
  rw [hd, ind_of_not_mem h1, ind_of_not_mem h2] at this
  by_contra h; rw [ind_of_not_mem h] at this
  have : ind F (outer2 c s) ≤ 1 := by unfold ind; split_ifs <;> omega
  omega

-- Both front corners cut off, on different pieces: a merging square across the front.
--
lemma merge_of_cutoff (c : Pt) (s : Side) (hd1 : deg F (front1 c s) = 2)
    (hd2 : deg F (front2 c s) = 2) (hl1 : lat1 c s ∉ F) (hl2 : lat2 c s ∉ F)
    (hf : front c s ∉ F) (hn : ¬ Conn F (front1 c s) (front2 c s)) : MergeAcross F c s :=
  merge_across c s (cutoff_front1 c s hd1 hl1 hf) (cutoff_front2 c s hd2 hl2 hf) hf hn

-- Sides between different pieces are light.
--
lemma not_mem_of_not_conn {e : Edge} {u v : Pt} (h : Ends e u v) (hn : ¬ Conn F u v) : e ∉ F :=
  fun he => hn (h.conn he)

end shapes

/-! ## Lemma 1 in coordinates

Corners `a = (x,y)`, `b = (x+1,y)`, `C = (x+1,y+1)`, `d = (x,y+1)`; sides `bot = a–b`,
`rgt = b–C`, `top = d–C`, `lft = a–d`. -/

section lemma1

variable {F : Finset Edge}

lemma ends_bot (x y : ℤ) : Ends (bot (x, y)) (x, y) (x + 1, y) := by simp [Ends, bot, Edge.q]
lemma ends_top (x y : ℤ) : Ends (top (x, y)) (x, y + 1) (x + 1, y + 1) := by simp [Ends, top, Edge.q]
lemma ends_lft (x y : ℤ) : Ends (lft (x, y)) (x, y) (x, y + 1) := by simp [Ends, lft, Edge.q]
lemma ends_rgt (x y : ℤ) : Ends (rgt (x, y)) (x + 1, y) (x + 1, y + 1) := by simp [Ends, rgt, Edge.q]

-- The four "both front corners cut off" contradictions, one per side.
--
lemma merge_top {x y : ℤ} (hd : deg F (x, y + 1) = 2) (hC : deg F (x + 1, y + 1) = 2)
    (hl : lft (x, y) ∉ F) (hr : rgt (x, y) ∉ F) (ht : top (x, y) ∉ F)
    (hn : ¬ Conn F (x, y + 1) (x + 1, y + 1)) : MergeAcross F (x, y) .t :=
  merge_of_cutoff (x, y) .t hd hC hl hr ht hn

lemma merge_bot {x y : ℤ} (ha : deg F (x, y) = 2) (hb : deg F (x + 1, y) = 2)
    (hl : lft (x, y) ∉ F) (hr : rgt (x, y) ∉ F) (hbt : bot (x, y) ∉ F)
    (hn : ¬ Conn F (x, y) (x + 1, y)) : MergeAcross F (x, y) .b :=
  merge_of_cutoff (x, y) .b ha hb hl hr hbt hn

lemma merge_rgt {x y : ℤ} (hb : deg F (x + 1, y) = 2) (hC : deg F (x + 1, y + 1) = 2)
    (hbt : bot (x, y) ∉ F) (ht : top (x, y) ∉ F) (hr : rgt (x, y) ∉ F)
    (hn : ¬ Conn F (x + 1, y) (x + 1, y + 1)) : MergeAcross F (x, y) .r :=
  merge_of_cutoff (x, y) .r hb hC hbt ht hr hn

lemma merge_lft {x y : ℤ} (ha : deg F (x, y) = 2) (hd : deg F (x, y + 1) = 2)
    (hbt : bot (x, y) ∉ F) (ht : top (x, y) ∉ F) (hl : lft (x, y) ∉ F)
    (hn : ¬ Conn F (x, y) (x, y + 1)) : MergeAcross F (x, y) .l :=
  merge_of_cutoff (x, y) .l ha hd hbt ht hl hn

-- **Sheffield's Lemma 1.** A cut square with degree-2 corners, not itself alternating and with no
-- merging square across any side, is critical or a corner square.
--
theorem lemma1 {x y : ℤ} (ha : deg F (x, y) = 2) (hb : deg F (x + 1, y) = 2)
    (hC : deg F (x + 1, y + 1) = 2) (hd : deg F (x, y + 1) = 2) (hcut : CutSq F (x, y))
    (hnc : ¬ Alt F (x, y)) (hno : ∀ s, ¬ MergeAcross F (x, y) s) :
    ∃ s, CriticalIn F (x, y) s ∨ CornerIn F (x, y) s := by
  set a : Pt := (x, y); set b : Pt := (x + 1, y)
  set C : Pt := (x + 1, y + 1); set d : Pt := (x, y + 1)
  have Eb := ends_bot x y; have Et := ends_top x y; have El := ends_lft x y; have Er := ends_rgt x y
  unfold CutSq at hcut
  have alt_of : bot a ∈ F → top a ∈ F → lft a ∉ F → rgt a ∉ F → False := fun h1 h2 h3 h4 =>
    hnc (Or.inl ⟨h1, h2, h3, h4⟩)
  have alt_of' : lft a ∈ F → rgt a ∈ F → bot a ∉ F → top a ∉ F → False := fun h1 h2 h3 h4 =>
    hnc (Or.inr ⟨h3, h4, h1, h2⟩)
  by_cases Pab : Conn F a b <;> by_cases Pbc : Conn F b C <;> by_cases Pcd : Conn F C d <;>
    by_cases Pda : Conn F d a
  -- all four, or three (the fourth follows): one piece
  · exact absurd ⟨Pab, Pab.trans Pbc, Pda.symm⟩ hcut
  · exact absurd ⟨Pab, Pab.trans Pbc, (Pab.trans Pbc).trans Pcd⟩ hcut
  · exact absurd ⟨Pab, Pab.trans Pbc, Pda.symm⟩ hcut
  -- Pab, Pbc only: d alone (corner)
  · have hl := not_mem_of_not_conn El (fun h => Pda h.symm)
    have ht := not_mem_of_not_conn Et (fun h => Pcd h.symm)
    refine ⟨.t, Or.inr (Or.inl ⟨fun h => Pda h, fun h => Pcd h.symm, Pab, Pbc, ?_, ?_⟩)⟩
    · by_contra hbt
      exact hno .l (merge_lft ha hd hbt ht hl (fun h => Pda h.symm))
    · by_contra hr
      exact hno .t (merge_top hd hC hl hr ht (fun h => Pcd h.symm))
  · exact absurd ⟨Pab, Pda.symm.trans (Pcd.symm), Pda.symm⟩ hcut
  -- Pab, Pcd only: critical in frame t
  · have hl := not_mem_of_not_conn El (fun h => Pda h.symm)
    have hr := not_mem_of_not_conn Er Pbc
    refine ⟨.t, Or.inl ⟨Pab, Pcd.symm, fun h => Pda h.symm, ?_⟩⟩
    show Xor (bot a ∈ F) (top a ∈ F)
    by_cases h1 : bot a ∈ F <;> by_cases h2 : top a ∈ F
    · exact absurd (alt_of h1 h2 hl hr) id
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h2, h1⟩
    · exact absurd (merge_lft ha hd h1 h2 hl (fun h => Pda h.symm)) (hno .l)
  -- Pab, Pda only: C alone (corner, front2 in frame t)
  · have hr := not_mem_of_not_conn Er Pbc
    have ht := not_mem_of_not_conn Et (fun h => Pcd h.symm)
    refine ⟨.t, Or.inr (Or.inr ⟨fun h => Pbc h.symm, fun h => Pcd h, Pab, Pda.symm, ?_, ?_⟩)⟩
    · by_contra hbt
      exact hno .r (merge_rgt hb hC hbt ht hr Pbc)
    · by_contra hl
      exact hno .t (merge_top hd hC hl hr ht (fun h => Pcd h.symm))
  -- Pab only: C and d isolated
  · have hl := not_mem_of_not_conn El (fun h => Pda h.symm)
    have hr := not_mem_of_not_conn Er Pbc
    have ht := not_mem_of_not_conn Et (fun h => Pcd h.symm)
    exact absurd (merge_top hd hC hl hr ht (fun h => Pcd h.symm)) (hno .t)
  · exact absurd ⟨Pda.symm.trans (Pcd.symm.trans Pbc.symm), Pda.symm.trans Pcd.symm, Pda.symm⟩ hcut
  -- Pbc, Pcd only: a alone (corner, front1 in frame b)
  · have hl := not_mem_of_not_conn El (fun h => Pda h.symm)
    have hbt := not_mem_of_not_conn Eb Pab
    refine ⟨.b, Or.inr (Or.inl ⟨fun h => Pda h.symm, Pab, Pcd.symm, Pbc.symm, ?_, ?_⟩)⟩
    · by_contra ht
      exact hno .l (merge_lft ha hd hbt ht hl (fun h => Pda h.symm))
    · by_contra hr
      exact hno .b (merge_bot ha hb hl hr hbt Pab)
  -- Pbc, Pda only: critical in frame r
  · have hbt := not_mem_of_not_conn Eb Pab
    have ht := not_mem_of_not_conn Et (fun h => Pcd h.symm)
    refine ⟨.r, Or.inl ⟨Pda.symm, Pbc, Pab, ?_⟩⟩
    show Xor (lft a ∈ F) (rgt a ∈ F)
    by_cases h1 : lft a ∈ F <;> by_cases h2 : rgt a ∈ F
    · exact absurd (alt_of' h1 h2 hbt ht) id
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h2, h1⟩
    · exact absurd (merge_top hd hC h1 h2 ht (fun h => Pcd h.symm)) (hno .t)
  -- Pbc only: a and d isolated
  · have hbt := not_mem_of_not_conn Eb Pab
    have ht := not_mem_of_not_conn Et (fun h => Pcd h.symm)
    have hl := not_mem_of_not_conn El (fun h => Pda h.symm)
    exact absurd (merge_lft ha hd hbt ht hl (fun h => Pda h.symm)) (hno .l)
  -- Pcd, Pda only: b alone (corner, front1 in frame r)
  · have hbt := not_mem_of_not_conn Eb Pab
    have hr := not_mem_of_not_conn Er Pbc
    refine ⟨.r, Or.inr (Or.inl ⟨fun h => Pab h.symm, Pbc, Pda.symm, Pcd.symm, ?_, ?_⟩)⟩
    · by_contra hl
      exact hno .b (merge_bot ha hb hl hr hbt Pab)
    · by_contra ht
      exact hno .r (merge_rgt hb hC hbt ht hr Pbc)
  -- Pcd only: a and b isolated
  · have hbt := not_mem_of_not_conn Eb Pab
    have hr := not_mem_of_not_conn Er Pbc
    have hl := not_mem_of_not_conn El (fun h => Pda h.symm)
    exact absurd (merge_bot ha hb hl hr hbt Pab) (hno .b)
  -- Pda only: b and C isolated
  · have hbt := not_mem_of_not_conn Eb Pab
    have hr := not_mem_of_not_conn Er Pbc
    have ht := not_mem_of_not_conn Et (fun h => Pcd h.symm)
    exact absurd (merge_rgt hb hC hbt ht hr Pbc) (hno .r)
  -- none: C and d isolated
  · have hl := not_mem_of_not_conn El (fun h => Pda h.symm)
    have hr := not_mem_of_not_conn Er Pbc
    have ht := not_mem_of_not_conn Et (fun h => Pcd h.symm)
    exact absurd (merge_top hd hC hl hr ht (fun h => Pcd h.symm)) (hno .t)

end lemma1

end HP

end SolidGridHam
