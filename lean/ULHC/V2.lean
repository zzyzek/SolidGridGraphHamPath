/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.TheoremA

/-!
# Toward V2: what an even strip does to the classes

Flipping an even strip of length `k + 2` = flipping its end cell `u` (a split of one class
into the class of `back1 u` and the class of `front1 u`), then the odd strip before it (pair
flips keep connections, and the first cell merges two classes).

**Lemma 5.6:** afterwards `back1 u` and `front1 u` are in different classes, so `u` is a
border cell.
-/

namespace ULHC

open Finset Classical

lemma front_corner_ne (c : Pt) (s : Side) {i j : ℕ} (h : i ≠ j) :
    front1 (cellJ c s i) s ≠ front1 (cellJ c s j) s ∧ front1 (cellJ c s i) s ≠ front2 (cellJ c s j) s ∧
      front2 (cellJ c s i) s ≠ front1 (cellJ c s j) s ∧ front2 (cellJ c s i) s ≠ front2 (cellJ c s j) s := by
  obtain ⟨x, y⟩ := c
  cases s <;> simp [front1, front2, cellJ] <;> omega

lemma back1_cellJ_succ (c : Pt) (s : Side) (j : ℕ) :
    back1 (cellJ c s (j + 1)) s = front1 (cellJ c s j) s := by
  rw [← nb_cellJ, back1_nb]

-- The end cell's corners are not middles of the odd strip before it.
--
lemma end_not_mid (c : Pt) (s : Side) (k : ℕ) :
    ¬ IsMid c s k (back1 (cellJ c s (k + 1)) s) ∧ ¬ IsMid c s k (front1 (cellJ c s (k + 1)) s) := by
  rw [back1_cellJ_succ]
  constructor
  · rintro ⟨j, _, hj, h | h⟩
    · exact (front_corner_ne c s (i := k) (j := j) (by omega)).1 h
    · exact (front_corner_ne c s (i := k) (j := j) (by omega)).2.1 h
  · rintro ⟨j, _, hj, h | h⟩
    · exact (front_corner_ne c s (i := k + 1) (j := j) (by omega)).1 h
    · exact (front_corner_ne c s (i := k + 1) (j := j) (by omega)).2.1 h

lemma not_mid_back2 (c : Pt) (s : Side) (k : ℕ) : ¬ IsMid c s k (back2 c s) := by
  rintro ⟨j, hj, _, h | h⟩ <;> obtain ⟨x, y⟩ := c <;> cases s <;>
    simp [back2, front1, front2, cellJ] at h <;> omega

lemma not_mid_start (c : Pt) (s : Side) (k : ℕ) :
    ¬ IsMid c s k (back1 c s) ∧ ¬ IsMid c s k (front1 c s) := by
  constructor
  · rintro ⟨j, hj, _, h | h⟩
    · exact (corner_ne c s (m := j) (by omega)).1 h
    · exact (corner_ne c s (m := j) (by omega)).2.1 h
  · rintro ⟨j, hj, _, h | h⟩
    · exact (corner_ne c s (m := j) (by omega)).2.2.1 h
    · exact (corner_ne c s (m := j) (by omega)).2.2.2 h

section even

variable {V : Finset Pt} {c : Pt} {s : Side}

-- **Even strip, with connections.** `F1` is the factor after the end cell's split.
--
theorem strip_even_rel (k : ℕ) (hk : k % 2 = 0) (F : Finset Edge) (hF : Deg2 V F)
    (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat F c s (k + 2))
    (hsep : ¬ Conn F (back1 c s) (front1 c s))
    (hsame : Conn F (back1 (cellJ c s (k + 1)) s) (back2 (cellJ c s (k + 1)) s)) :
    ∃ F1 : Finset Edge, F1 = flip F (cellJ c s (k + 1)) ∧
      flipCol F c s (k + 2) = flipCol F1 c s (k + 1) ∧
      ¬ Conn F1 (back1 (cellJ c s (k + 1)) s) (front1 (cellJ c s (k + 1)) s) ∧
      (∀ x y, Conn F1 x y → Conn F x y) ∧
      (∀ x y, Conn F x y ↔ Conn F1 x y ∨
        (Conn F1 x (back1 (cellJ c s (k + 1)) s) ∧ Conn F1 (front1 (cellJ c s (k + 1)) s) y) ∨
        (Conn F1 x (front1 (cellJ c s (k + 1)) s) ∧ Conn F1 (back1 (cellJ c s (k + 1)) s) y)) ∧
      ∀ x y, ¬ IsMid c s k x → ¬ IsMid c s k y →
        (Conn (flipCol F c s (k + 2)) x y ↔ Conn F1 x y ∨
          (Conn F1 x (back1 c s) ∧ Conn F1 (front1 c s) y) ∨
          (Conn F1 x (front1 c s) ∧ Conn F1 (back1 c s) y)) := by
  set u := cellJ c s (k + 1)
  obtain ⟨hb, hl, hf⟩ := hpat
  have uL1 : lat1 u s ∈ F := (hl (k + 1) (by omega)).1.2 (by omega)
  have uL2 : lat2 u s ∈ F := (hl (k + 1) (by omega)).2.2 (by omega)
  have uB : back u s ∉ F := by
    rw [back_cellJ_succ]; intro h; have := (hf k (by omega)).1 h; omega
  have uF : front u s ∉ F := by
    intro h; have := (hf (k + 1) (by omega)).1 h; omega
  have hcu : IsCell V u := hcell (k + 1) le_rfl
  obtain ⟨ub1, ub2, uf1, uf2⟩ := isCell_corners hcu s
  have hE := mkLat_cellE u s
  have hflip := (mkLat u s).flip_eq hE uL1 uL2 uB uF
  obtain ⟨hcount, hrel, hfine⟩ := (mkLat u s).split hF.1 ub1 uf1 ub2 uf2 uL1 uL2 uB
    (fun z hz => by rcases hz with hz | hz
                    · exact hF.class ub1 hz
                    · exact hF.class ub2 hz) hsame hF.le_two
    (fun G h1 h2 h3 h4 h5 => planar_lat G u s h1 h2 h3 h4 h5)
  set F1 := (mkLat u s).res F
  have hF' : Deg2 V F1 := by
    rw [← hflip]; exact hF.flip (mkLat u s) hcu hE uL1 uL2 uB uF
  have hpat' : StripPat F1 c s (k + 1) := by
    rw [← hflip]; exact pat_flip_last hk ⟨hb, hl, hf⟩
  have hsep' : ¬ Conn F1 (back1 c s) (front1 c s) := fun h => hsep (hrel _ _ h)
  have hab : ¬ Conn F1 (back1 u s) (front1 u s) := by
    intro h
    have : ncomp V F1 = ncomp V F := by
      apply ncomp_congr
      intro x _ y _
      rw [hfine x y]
      constructor
      · exact fun h' => Or.inl h'
      · rintro (h' | ⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact h'
        · exact (h1.trans h).trans h2
        · exact (h1.trans h.symm).trans h2
    omega
  refine ⟨F1, hflip.symm, by rw [flipCol_succ, hflip], hab, hrel, hfine, ?_⟩
  intro x y hx hy
  rw [flipCol_succ, hflip]
  exact (strip_odd k hk F1 hF' (fun j hj => hcell j (by omega)) hpat' hsep').2 x y hx hy

-- **Lemma 5.6.** After flipping an even strip, the end cell's `back1` and `front1` are in
-- different classes.
--
theorem even_end_border (k : ℕ) (hk : k % 2 = 0) (F : Finset Edge) (hF : Deg2 V F)
    (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat F c s (k + 2))
    (hsep : ¬ Conn F (back1 c s) (front1 c s))
    (hsame : Conn F (back1 (cellJ c s (k + 1)) s) (back2 (cellJ c s (k + 1)) s)) :
    ¬ Conn (flipCol F c s (k + 2)) (back1 (cellJ c s (k + 1)) s) (front1 (cellJ c s (k + 1)) s) := by
  obtain ⟨F1, _, _, hab, hrel, _, hodd⟩ := strip_even_rel k hk F hF hcell hpat hsep hsame
  obtain ⟨na, nb⟩ := end_not_mid c s k
  rw [hodd _ _ na nb]
  -- `back1 u ~ front1 u` in `F` (the end cell's dark lateral side).
  have huF : Conn F (back1 (cellJ c s (k + 1)) s) (front1 (cellJ c s (k + 1)) s) := by
    obtain ⟨_, hl, _⟩ := hpat
    exact (ends_lat1 _ s).conn ((hl (k + 1) (by omega)).1.2 (by omega))
  rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
  · exact hab h
  · exact hsep ((hrel _ _ h1).symm.trans (huF.trans (hrel _ _ h2).symm))
  · exact hsep ((hrel _ _ h2).trans (huF.symm.trans (hrel _ _ h1)))

end even

end ULHC
