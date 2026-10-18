/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.HP.TouchLoc
import ULHC.NearChain

/-!
# Touch lemmas at a phantom start (s–t path extension)

A strip `a = (c, s, ·)` *starts on the endpoint's edge* when its back corner `back1 c` is the
endpoint t and the missing neighbour p of t lies beside it, across `latA`. Then the cell beside `c`
on that side has p as a corner and is no cell, and the forcing lemmas that ULHC applies there
(`back_outer_light`, `back_down`) no longer hold: `t` has no edge going back, so
`lat1 (nb c s.opp) s ∉ F`.

These lemmas give the phantom versions of the touch lemmas that used those facts. They use only
that every cell of the touching strip is a cell of `V`, so a strip cannot pass through a square
with p as a corner.
-/

namespace ULHC

namespace HP

open Finset Classical

-- **`touch_behind` at a phantom start.** Behind the start cell `c`, the side under `t` is light
-- and the other is dark. Then no strip of `V` passes through the cell behind `c`: along the axis
-- its two lateral sides would differ, across toward `latA` its back would be dark and its sides
-- light, and across toward `latB` the previous cell is the square beside it with p as a corner.
--
theorem touch_behind_phantom {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side}
    {z : Pt} {tf : Side} {m i0 i : ℕ} (hz : SigFrom F z tf m i0) (hi0 : i0 ≤ i) (hi : i < m)
    (hq : cellJ z tf i = nb c s.opp) (hback : back c s ∈ F)
    (hn1 : lat1 (nb c s.opp) s ∉ F) (d2 : lat2 (nb c s.opp) s ∈ F)
    (hzc : ∀ j < m, IsCell V (cellJ z tf j))
    (hw : ¬ IsCell V (nb (nb c s.opp) (latA s))) : False := by
  have df : front (nb c s.opp) s ∈ F := by rw [front_nb_opp]; exact hback
  obtain ⟨g1, g2, gb, _⟩ := hz i hi0 hi
  rw [hq] at g1 g2 gb
  rcases side_cases s tf with rfl | rfl | rfl | rfl
  · exact hn1 (g1.2 (g2.1 d2))
  · obtain ⟨f1, f2, _, _⟩ := frame_opp (nb c s.opp) s
    rw [f1] at g1; rw [f2] at g2
    exact hn1 (g1.2 (g2.1 d2))
  · obtain ⟨_, fb, fl⟩ := frame_latA (nb c s.opp) s
    rw [fb] at gb
    have he := gb.1 d2
    rcases fl with ⟨_, h'⟩ | ⟨h', _⟩
    · rw [h'] at g2; have := g2.1 df; omega
    · rw [h'] at g1; have := g1.1 df; omega
  · obtain ⟨_, fb, _⟩ := frame_latB (nb c s.opp) s
    rw [fb] at gb
    have hodd : i % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one i with h0 | h0
      · exact absurd (gb.2 h0) hn1
      · exact h0
    have hp := cell_prev_L (z := z) (tf := latB s) (i := i) (by omega)
    have e : (latB s).opp = latA s := by rw [latB_eq_opp, opp_opp]
    rw [hq, e] at hp
    exact hw (hp ▸ hzc (i - 1) (by omega))

-- **`touch_behind` when the forcing behind `c` fails because the outer edge at `back1 c` is dark**
-- (the configuration with the endpoint at `front1 c` and p beside it, where the cell beside `c`
-- may be phantom Type III). Then the side of the cell behind `c` under `back1 c` is light, and no
-- strip passes through that cell: as above along the axis and toward `latA`, and toward `latB`
-- the previous cell has the dark outer edge as a lateral side at an even index.
--
theorem touch_behind_outer {F : Finset Edge} {c : Pt} {s : Side}
    {z : Pt} {tf : Side} {m i0 i : ℕ} (hz : SigFrom F z tf m i0) (hi0 : i0 ≤ i) (hi : i < m)
    (hq : cellJ z tf i = nb c s.opp) (hback : back c s ∈ F)
    (hn1 : lat1 (nb c s.opp) s ∉ F) (d2 : lat2 (nb c s.opp) s ∈ F)
    (hbL : back (nb c (latA s)) s ∈ F) (hprev : i % 2 = 1 → i0 < i) : False := by
  have df : front (nb c s.opp) s ∈ F := by rw [front_nb_opp]; exact hback
  obtain ⟨g1, g2, gb, _⟩ := hz i hi0 hi
  rw [hq] at g1 g2 gb
  rcases side_cases s tf with rfl | rfl | rfl | rfl
  · exact hn1 (g1.2 (g2.1 d2))
  · obtain ⟨f1, f2, _, _⟩ := frame_opp (nb c s.opp) s
    rw [f1] at g1; rw [f2] at g2
    exact hn1 (g1.2 (g2.1 d2))
  · obtain ⟨_, fb, fl⟩ := frame_latA (nb c s.opp) s
    rw [fb] at gb
    have he := gb.1 d2
    rcases fl with ⟨_, h'⟩ | ⟨h', _⟩
    · rw [h'] at g2; have := g2.1 df; omega
    · rw [h'] at g1; have := g1.1 df; omega
  · obtain ⟨_, fb, _⟩ := frame_latB (nb c s.opp) s
    rw [fb] at gb
    have hodd : i % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one i with h0 | h0
      · exact absurd (gb.2 h0) hn1
      · exact h0
    have hlt := hprev hodd
    have hp := cell_prev_L (z := z) (tf := latB s) (i := i) (by omega)
    have e : (latB s).opp = latA s := by rw [latB_eq_opp, opp_opp]
    rw [hq, e] at hp
    obtain ⟨p1, p2, _, _⟩ := hz (i - 1) (by omega) (by omega)
    rw [hp] at p1 p2
    have hfw : front (nb (nb c s.opp) (latA s)) s ∈ F := by
      have hc : nb (nb c s.opp) (latA s) = nb (nb c (latA s)) s.opp := by
        obtain ⟨x, y⟩ := c
        cases s <;> simp only [nb, Side.opp, latA]
      rw [hc, front_nb_opp]; exact hbL
    obtain ⟨_, _, fl⟩ := frame_latB (nb (nb c s.opp) (latA s)) s
    rcases fl with ⟨_, h'⟩ | ⟨h', _⟩
    · rw [h'] at p2; have := p2.1 hfw; omega
    · rw [h'] at p1; have := p1.1 hfw; omega

section sides

variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hDc : ∀ j ≤ k + 1, ∀ z, IsCorner z (cellJ c s j) → deg F z = 2)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat F c s (k + 2))

include hDc hpat in
-- **Side facts from the second cell on.** Beside the body (across `lat1`), from `j = 1` on, the
-- facts of `side1_facts_L` need no hypothesis on the cell beside `c`: only the first cell uses the
-- forcing there. So at a phantom start they hold for every `j ≥ 1`.
--
lemma side1_facts_succ {j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ k) :
    (lat2 (nb (cellJ c s j) (latA s)) s ∈ F ↔ j % 2 = 1) ∧
      (back (nb (cellJ c s j) (latA s)) s ∈ F ↔ j % 2 = 1) ∧
      (front (nb (cellJ c s j) (latA s)) s ∈ F ↔ j % 2 = 0) := by
  refine ⟨by rw [side_lat2]; exact (strip_sig hpat (show j < k + 2 by omega)).1, ?_, ?_⟩
  · obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    rw [← nb_cellJ, side_back_next, outer1_body_L hDc hpat (by omega)]; omega
  · rw [side_front]; exact outer1_body_L hDc hpat hj

include hDc hpat in
lemma side2_facts_succ {j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ k) :
    (lat1 (nb (cellJ c s j) (latB s)) s ∈ F ↔ j % 2 = 1) ∧
      (back (nb (cellJ c s j) (latB s)) s ∈ F ↔ j % 2 = 1) ∧
      (front (nb (cellJ c s j) (latB s)) s ∈ F ↔ j % 2 = 0) := by
  refine ⟨by rw [side2_lat1]; exact (strip_sig hpat (show j < k + 2 by omega)).2.1, ?_, ?_⟩
  · obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    rw [← nb_cellJ, show back (nb (nb (cellJ c s j) s) (latB s)) s = outer2 (cellJ c s j) s by
      rw [outer2_side_nb_next]; rfl, outer2_body_L hDc hpat (by omega)]; omega
  · rw [side2_front]; exact outer2_body_L hDc hpat hj

end sides

-- **`touch_side1` from the side facts alone.** A strip through the cell `L` beside the body
-- (across `lat1`) at `c_j` runs against `s` with the parity of `j` and continues, given only the
-- three side facts at `L`.
--
theorem touch_side1_of_facts {F : Finset Edge} {c : Pt} {s : Side} {j : ℕ}
    {z : Pt} {tf : Side} {m i0 i : ℕ} (hz : SigFrom F z tf m i0) (hi0 : i0 ≤ i) (hi : i < m)
    (fn : lat2 (nb (cellJ c s j) (latA s)) s ∈ F ↔ j % 2 = 1)
    (fb : back (nb (cellJ c s j) (latA s)) s ∈ F ↔ j % 2 = 1)
    (ff : front (nb (cellJ c s j) (latA s)) s ∈ F ↔ j % 2 = 0)
    (hq : cellJ z tf i = nb (cellJ c s j) (latA s)) :
    tf = s.opp ∧ i % 2 = j % 2 ∧ i + 1 < m := by
  obtain ⟨g1, g2, gb, gf⟩ := hz i hi0 hi
  rw [hq] at g1 g2 gb gf
  set L := nb (cellJ c s j) (latA s)
  rcases side_cases s tf with h | h | h | h <;> rw [h] at g1 g2 gb gf
  · exfalso
    have hp := par_of_iff_L (g2.symm.trans fn)
    rcases Nat.mod_two_eq_zero_or_one i with h0 | h0
    · have := fb.1 (gb.2 h0); omega
    · have : back L s ∈ F := fb.2 (by omega)
      have := gb.1 this; omega
  · obtain ⟨_, f2, fbk, ff'⟩ := frame_opp L s
    rw [f2] at g2; rw [ff'] at gf
    have hp := par_of_iff_L (g2.symm.trans fn)
    exact ⟨h, hp, cont_of gf (fb.trans (by omega))⟩
  · exfalso
    have := perp_bf g1 g2 (frame_latA L s).2.2
    rw [fb, ff] at this; omega
  · exfalso
    have := perp_bf g1 g2 (frame_latB L s).2.2
    rw [fb, ff] at this; omega

theorem touch_side2_of_facts {F : Finset Edge} {c : Pt} {s : Side} {j : ℕ}
    {z : Pt} {tf : Side} {m i0 i : ℕ} (hz : SigFrom F z tf m i0) (hi0 : i0 ≤ i) (hi : i < m)
    (fn : lat1 (nb (cellJ c s j) (latB s)) s ∈ F ↔ j % 2 = 1)
    (fb : back (nb (cellJ c s j) (latB s)) s ∈ F ↔ j % 2 = 1)
    (ff : front (nb (cellJ c s j) (latB s)) s ∈ F ↔ j % 2 = 0)
    (hq : cellJ z tf i = nb (cellJ c s j) (latB s)) :
    tf = s.opp ∧ i % 2 = j % 2 ∧ i + 1 < m := by
  obtain ⟨g1, g2, gb, gf⟩ := hz i hi0 hi
  rw [hq] at g1 g2 gb gf
  set L := nb (cellJ c s j) (latB s)
  rcases side_cases s tf with h | h | h | h <;> rw [h] at g1 g2 gb gf
  · exfalso
    have hp := par_of_iff_L (g1.symm.trans fn)
    rcases Nat.mod_two_eq_zero_or_one i with h0 | h0
    · have := fb.1 (gb.2 h0); omega
    · have : back L s ∈ F := fb.2 (by omega)
      have := gb.1 this; omega
  · obtain ⟨f1, _, fbk, ff'⟩ := frame_opp L s
    rw [f1] at g1; rw [ff'] at gf
    have hp := par_of_iff_L (g1.symm.trans fn)
    exact ⟨h, hp, cont_of gf (fb.trans (by omega))⟩
  · exfalso
    have := perp_bf g1 g2 (frame_latA L s).2.2
    rw [fb, ff] at this; omega
  · exfalso
    have := perp_bf g1 g2 (frame_latB L s).2.2
    rw [fb, ff] at this; omega

-- **`touch_side1` when the square beside the start is no cell** (configurations A and B: it has
-- the missing point p as a corner). A strip of `V` cannot use that square, and beside the later
-- cells the side facts hold without any hypothesis on it. This replaces `touch_side1_L`, which
-- needs the square beside the start to be a cell that is not Type III.
--
theorem touch_side1_noncell {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
    (hDc : ∀ j ≤ k + 1, ∀ z, IsCorner z (cellJ c s j) → deg F z = 2)
    (_hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat F c s (k + 2))
    (hL0 : ¬ IsCell V (nb c (latA s)))
    {z : Pt} {tf : Side} {m i0 i : ℕ} (hz : SigFrom F z tf m i0) (hi0 : i0 ≤ i) (hi : i < m)
    (hzc : ∀ j < m, IsCell V (cellJ z tf j))
    {j : ℕ} (hj : j ≤ k) (hq : cellJ z tf i = nb (cellJ c s j) (latA s)) :
    tf = s.opp ∧ i % 2 = j % 2 ∧ i + 1 < m := by
  rcases Nat.eq_zero_or_pos j with rfl | hj1
  · rw [cellJ_zero] at hq
    exact absurd (hq ▸ hzc i hi) hL0
  · obtain ⟨fn, fb, ff⟩ := side1_facts_succ hDc hpat hj1 hj
    exact touch_side1_of_facts hz hi0 hi fn fb ff hq

theorem touch_side2_noncell {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
    (hDc : ∀ j ≤ k + 1, ∀ z, IsCorner z (cellJ c s j) → deg F z = 2)
    (_hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat F c s (k + 2))
    (hL0 : ¬ IsCell V (nb c (latB s)))
    {z : Pt} {tf : Side} {m i0 i : ℕ} (hz : SigFrom F z tf m i0) (hi0 : i0 ≤ i) (hi : i < m)
    (hzc : ∀ j < m, IsCell V (cellJ z tf j))
    {j : ℕ} (hj : j ≤ k) (hq : cellJ z tf i = nb (cellJ c s j) (latB s)) :
    tf = s.opp ∧ i % 2 = j % 2 ∧ i + 1 < m := by
  rcases Nat.eq_zero_or_pos j with rfl | hj1
  · rw [cellJ_zero] at hq
    exact absurd (hq ▸ hzc i hi) hL0
  · obtain ⟨fn, fb, ff⟩ := side2_facts_succ hDc hpat hj1 hj
    exact touch_side2_of_facts hz hi0 hi fn fb ff hq

-- **No strip of `V` runs beside the body on the phantom side.** When the square beside the start
-- is no cell, a strip through a cell beside the body (across `lat1`) runs against `s`, cell by
-- cell, toward that square, which it cannot enter (ULHC's `side_chain1` ends there).
--
theorem side_chain1_noncell {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
    (hDc : ∀ j ≤ k + 1, ∀ z, IsCorner z (cellJ c s j) → deg F z = 2)
    (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat F c s (k + 2))
    (hL0 : ¬ IsCell V (nb c (latA s)))
    {z : Pt} {tf : Side} {m i0 : ℕ} (hz : SigFrom F z tf m i0)
    (hzc : ∀ j < m, IsCell V (cellJ z tf j)) :
    ∀ j i, j ≤ k → i0 ≤ i → i < m → cellJ z tf i = nb (cellJ c s j) (latA s) → False := by
  intro j
  induction j with
  | zero =>
    intro i _ _ hi hq
    rw [cellJ_zero] at hq
    exact hL0 (hq ▸ hzc i hi)
  | succ j ih =>
    intro i hj h0 hi hq
    obtain ⟨ht, _, hi1⟩ := touch_side1_noncell hDc hcell hpat hL0 hz h0 hi hzc hj hq
    exact ih (i + 1) (by omega) (by omega) hi1 (by rw [← nb_cellJ, hq, ht, side1_down])

theorem side_chain2_noncell {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
    (hDc : ∀ j ≤ k + 1, ∀ z, IsCorner z (cellJ c s j) → deg F z = 2)
    (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat F c s (k + 2))
    (hL0 : ¬ IsCell V (nb c (latB s)))
    {z : Pt} {tf : Side} {m i0 : ℕ} (hz : SigFrom F z tf m i0)
    (hzc : ∀ j < m, IsCell V (cellJ z tf j)) :
    ∀ j i, j ≤ k → i0 ≤ i → i < m → cellJ z tf i = nb (cellJ c s j) (latB s) → False := by
  intro j
  induction j with
  | zero =>
    intro i _ _ hi hq
    rw [cellJ_zero] at hq
    exact hL0 (hq ▸ hzc i hi)
  | succ j ih =>
    intro i hj h0 hi hq
    obtain ⟨ht, _, hi1⟩ := touch_side2_noncell hDc hcell hpat hL0 hz h0 hi hzc hj hq
    exact ih (i + 1) (by omega) (by omega) hi1 (by rw [← nb_cellJ, hq, ht, side2_down])

-- **`side_chain2` from the side facts alone** (as ULHC's `side_chain2`, with the facts at every
-- cell beside the body given instead of derived).
--
theorem side_chain2_of_facts {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
    (hfacts : ∀ j ≤ k, (lat1 (nb (cellJ c s j) (latB s)) s ∈ F ↔ j % 2 = 1) ∧
      (back (nb (cellJ c s j) (latB s)) s ∈ F ↔ j % 2 = 1) ∧
      (front (nb (cellJ c s j) (latB s)) s ∈ F ↔ j % 2 = 0))
    {z : Pt} {tf : Side} {m i0 : ℕ} (hz : SigFrom F z tf m i0) :
    ∀ j i, j ≤ k → i0 ≤ i → i < m → cellJ z tf i = nb (cellJ c s j) (latB s) →
      tf = s.opp ∧ ∃ ie, i ≤ ie ∧ ie < m ∧ ie % 2 = 0 ∧ cellJ z tf ie = nb c (latB s) := by
  intro j
  induction j with
  | zero =>
    intro i hj h0 hi hq
    obtain ⟨fn, fb, ff⟩ := hfacts 0 hj
    obtain ⟨ht, hp, _⟩ := touch_side2_of_facts hz h0 hi fn fb ff hq
    exact ⟨ht, i, le_rfl, hi, by omega, by rw [hq, cellJ_zero]⟩
  | succ j ih =>
    intro i hj h0 hi hq
    obtain ⟨fn, fb, ff⟩ := hfacts (j + 1) hj
    obtain ⟨ht, _, hi1⟩ := touch_side2_of_facts hz h0 hi fn fb ff hq
    obtain ⟨ht', ie, h1, h2⟩ := ih (i + 1) (by omega) (by omega) hi1 (by
      rw [← nb_cellJ, hq, ht, side2_down])
    exact ⟨ht', ie, by omega, h2⟩

-- **`touch_behind_phantom` across `latB`** (mirror): the side of the cell behind `c` under
-- `back2 c` is light, the other dark, and the square behind the cell beside `c` across `latB`
-- is no cell.
--
theorem touch_behind_phantomB {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side}
    {z : Pt} {tf : Side} {m i0 i : ℕ} (hz : SigFrom F z tf m i0) (hi0 : i0 ≤ i) (hi : i < m)
    (hq : cellJ z tf i = nb c s.opp) (hback : back c s ∈ F)
    (hn2 : lat2 (nb c s.opp) s ∉ F) (d1 : lat1 (nb c s.opp) s ∈ F)
    (hzc : ∀ j < m, IsCell V (cellJ z tf j))
    (hw : ¬ IsCell V (nb (nb c s.opp) (latB s))) : False := by
  have df : front (nb c s.opp) s ∈ F := by rw [front_nb_opp]; exact hback
  obtain ⟨g1, g2, gb, _⟩ := hz i hi0 hi
  rw [hq] at g1 g2 gb
  rcases side_cases s tf with rfl | rfl | rfl | rfl
  · exact hn2 (g2.2 (g1.1 d1))
  · obtain ⟨f1, f2, _, _⟩ := frame_opp (nb c s.opp) s
    rw [f1] at g1; rw [f2] at g2
    exact hn2 (g2.2 (g1.1 d1))
  · obtain ⟨_, fb, _⟩ := frame_latA (nb c s.opp) s
    rw [fb] at gb
    have hodd : i % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one i with h0 | h0
      · exact absurd (gb.2 h0) hn2
      · exact h0
    have hp := cell_prev_L (z := z) (tf := latA s) (i := i) (by omega)
    have e : (latA s).opp = latB s := by rw [latB_eq_opp]
    rw [hq, e] at hp
    exact hw (hp ▸ hzc (i - 1) (by omega))
  · obtain ⟨_, fb, fl⟩ := frame_latB (nb c s.opp) s
    rw [fb] at gb
    have he := gb.1 d1
    rcases fl with ⟨_, h'⟩ | ⟨h', _⟩
    · rw [h'] at g2; have := g2.1 df; omega
    · rw [h'] at g1; have := g1.1 df; omega

-- **`touch_behind_outer` across `latB`** (mirror).
--
theorem touch_behind_outerB {F : Finset Edge} {c : Pt} {s : Side}
    {z : Pt} {tf : Side} {m i0 i : ℕ} (hz : SigFrom F z tf m i0) (hi0 : i0 ≤ i) (hi : i < m)
    (hq : cellJ z tf i = nb c s.opp) (hback : back c s ∈ F)
    (hn2 : lat2 (nb c s.opp) s ∉ F) (d1 : lat1 (nb c s.opp) s ∈ F)
    (hbR : back (nb c (latB s)) s ∈ F) (hprev : i % 2 = 1 → i0 < i) : False := by
  have df : front (nb c s.opp) s ∈ F := by rw [front_nb_opp]; exact hback
  obtain ⟨g1, g2, gb, _⟩ := hz i hi0 hi
  rw [hq] at g1 g2 gb
  rcases side_cases s tf with rfl | rfl | rfl | rfl
  · exact hn2 (g2.2 (g1.1 d1))
  · obtain ⟨f1, f2, _, _⟩ := frame_opp (nb c s.opp) s
    rw [f1] at g1; rw [f2] at g2
    exact hn2 (g2.2 (g1.1 d1))
  · obtain ⟨_, fb, _⟩ := frame_latA (nb c s.opp) s
    rw [fb] at gb
    have hodd : i % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one i with h0 | h0
      · exact absurd (gb.2 h0) hn2
      · exact h0
    have hlt := hprev hodd
    have hp := cell_prev_L (z := z) (tf := latA s) (i := i) (by omega)
    have e : (latA s).opp = latB s := by rw [latB_eq_opp]
    rw [hq, e] at hp
    obtain ⟨p1, p2, _, _⟩ := hz (i - 1) (by omega) (by omega)
    rw [hp] at p1 p2
    have hfw : front (nb (nb c s.opp) (latB s)) s ∈ F := by
      have hc : nb (nb c s.opp) (latB s) = nb (nb c (latB s)) s.opp := by
        obtain ⟨x, y⟩ := c
        cases s <;> simp only [nb, Side.opp, latB]
      rw [hc, front_nb_opp]; exact hbR
    obtain ⟨_, _, fl⟩ := frame_latA (nb (nb c s.opp) (latB s)) s
    rcases fl with ⟨_, h'⟩ | ⟨h', _⟩
    · rw [h'] at p2; have := p2.1 hfw; omega
    · rw [h'] at p1; have := p1.1 hfw; omega
  · obtain ⟨_, fb, fl⟩ := frame_latB (nb c s.opp) s
    rw [fb] at gb
    have he := gb.1 d1
    rcases fl with ⟨_, h'⟩ | ⟨h', _⟩
    · rw [h'] at g2; have := g2.1 df; omega
    · rw [h'] at g1; have := g1.1 df; omega

-- **`side_chain1` from the side facts alone** (mirror of `side_chain2_of_facts`).
--
theorem side_chain1_of_facts {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
    (hfacts : ∀ j ≤ k, (lat2 (nb (cellJ c s j) (latA s)) s ∈ F ↔ j % 2 = 1) ∧
      (back (nb (cellJ c s j) (latA s)) s ∈ F ↔ j % 2 = 1) ∧
      (front (nb (cellJ c s j) (latA s)) s ∈ F ↔ j % 2 = 0))
    {z : Pt} {tf : Side} {m i0 : ℕ} (hz : SigFrom F z tf m i0) :
    ∀ j i, j ≤ k → i0 ≤ i → i < m → cellJ z tf i = nb (cellJ c s j) (latA s) →
      tf = s.opp ∧ ∃ ie, i ≤ ie ∧ ie < m ∧ ie % 2 = 0 ∧ cellJ z tf ie = nb c (latA s) := by
  intro j
  induction j with
  | zero =>
    intro i hj h0 hi hq
    obtain ⟨fn, fb, ff⟩ := hfacts 0 hj
    obtain ⟨ht, hp, _⟩ := touch_side1_of_facts hz h0 hi fn fb ff hq
    exact ⟨ht, i, le_rfl, hi, by omega, by rw [hq, cellJ_zero]⟩
  | succ j ih =>
    intro i hj h0 hi hq
    obtain ⟨fn, fb, ff⟩ := hfacts (j + 1) hj
    obtain ⟨ht, _, hi1⟩ := touch_side1_of_facts hz h0 hi fn fb ff hq
    obtain ⟨ht', ie, h1, h2⟩ := ih (i + 1) (by omega) (by omega) hi1 (by
      rw [← nb_cellJ, hq, ht, side1_down])
    exact ⟨ht', ie, by omega, h2⟩

end HP

end ULHC
