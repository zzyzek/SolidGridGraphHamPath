/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.Near

/-!
# Strip cells touching a proper strip

A cell of a strip `z` (direction `t`) is read in the frame of the strip `a` (direction `s`):
`t` is `s`, `s.opp`, `latA s` or `latB s`, and the frame lemmas translate sides. The strip
signature (`strip_sig`) says: the lateral sides agree, and the back side is dark exactly when
the lateral sides are light. Against the sides of the cells around `a` that are known (the
pattern of `a`, the forced outer sides, `back_down`), this pins down how `z` can pass.

* `touch_behind`: through the cell behind `c_0`, `z` runs in direction `s` into `c_0`.
* `touch_body`: through a cell `c_j` before the end cell, `z` runs in direction `s` with the
  same index parity, into `c_{j+1}`.
* `touch_end`: through the end cell, `z` ends there.
-/

namespace ULHC

open Finset

section frames

variable (d : Pt) (s : Side)

lemma frame_opp : lat1 d s.opp = lat1 d s ∧ lat2 d s.opp = lat2 d s ∧
    back d s.opp = front d s ∧ front d s.opp = back d s := by
  refine ⟨by rw [lat1_eq, lat1_eq, latA_opp], by rw [lat2_eq, lat2_eq, latB_opp], ?_, rfl⟩
  show sideEdge d s.opp.opp = sideEdge d s
  rw [opp_opp]

lemma frame_latA : front d (latA s) = lat1 d s ∧ back d (latA s) = lat2 d s ∧
    ((lat1 d (latA s) = back d s ∧ lat2 d (latA s) = front d s) ∨
      (lat1 d (latA s) = front d s ∧ lat2 d (latA s) = back d s)) := by
  refine ⟨(lat1_eq d s).symm, ?_, ?_⟩
  · show sideEdge d (latA s).opp = lat2 d s
    rw [lat2_eq, latB_eq_opp]
  · cases s <;> simp [lat1, lat2, back, front, latA, sideEdge, Side.opp]

lemma frame_latB : front d (latB s) = lat2 d s ∧ back d (latB s) = lat1 d s ∧
    ((lat1 d (latB s) = back d s ∧ lat2 d (latB s) = front d s) ∨
      (lat1 d (latB s) = front d s ∧ lat2 d (latB s) = back d s)) := by
  refine ⟨(lat2_eq d s).symm, ?_, ?_⟩
  · show sideEdge d (latB s).opp = lat1 d s
    rw [lat1_eq, latB_eq_opp, opp_opp]
  · cases s <;> simp [lat1, lat2, back, front, latB, sideEdge, Side.opp]

end frames

-- The signature of the `i`-th cell of a strip.
--
lemma strip_sig {F : Finset Edge} {z : Pt} {tf : Side} {m i : ℕ} (hp : StripPat F z tf m)
    (hi : i < m) :
    (lat1 (cellJ z tf i) tf ∈ F ↔ i % 2 = 1) ∧ (lat2 (cellJ z tf i) tf ∈ F ↔ i % 2 = 1) ∧
      (back (cellJ z tf i) tf ∈ F ↔ i % 2 = 0) ∧
      (front (cellJ z tf i) tf ∈ F ↔ (i % 2 = 1 ↔ i + 1 < m)) := by
  obtain ⟨hb, hl, hf⟩ := hp
  refine ⟨(hl i hi).1, (hl i hi).2, ?_, hf i hi⟩
  rcases i with _ | j
  · rw [cellJ_zero]; simp [hb]
  · rw [back_cellJ_succ, hf j (by omega)]; omega

-- The strip signature from index `i0` on (a chain strip's pattern holds in `F` from index 1).
--
def SigFrom (F : Finset Edge) (z : Pt) (tf : Side) (m i0 : ℕ) : Prop :=
  ∀ i, i0 ≤ i → i < m →
    (lat1 (cellJ z tf i) tf ∈ F ↔ i % 2 = 1) ∧ (lat2 (cellJ z tf i) tf ∈ F ↔ i % 2 = 1) ∧
      (back (cellJ z tf i) tf ∈ F ↔ i % 2 = 0) ∧
      (front (cellJ z tf i) tf ∈ F ↔ (i % 2 = 1 ↔ i + 1 < m))

lemma sig_of_pat {F : Finset Edge} {z : Pt} {tf : Side} {m : ℕ} (hp : StripPat F z tf m) :
    SigFrom F z tf m 0 := fun _ _ hi => strip_sig hp hi

lemma front_nb_opp (c : Pt) (s : Side) : front (nb c s.opp) s = back c s := by
  have := back_nb (nb c s.opp) s
  rw [show nb (nb c s.opp) s = c by
    have h := nb_nb_opp c s.opp; rwa [opp_opp] at h] at this
  exact this.symm


lemma perp_bf {F : Finset Edge} {d : Pt} {s tf : Side} {P : Prop} (g1 : lat1 d tf ∈ F ↔ P)
    (g2 : lat2 d tf ∈ F ↔ P)
    (fl : (lat1 d tf = back d s ∧ lat2 d tf = front d s) ∨ (lat1 d tf = front d s ∧ lat2 d tf = back d s)) :
    back d s ∈ F ↔ front d s ∈ F := by
  rcases fl with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1] at g1; rw [h2] at g2; exact g1.trans g2.symm
  · rw [h1] at g1; rw [h2] at g2; exact g2.trans g1.symm

lemma cont_of {P : Prop} {i m : ℕ} (gf : P ↔ (i % 2 = 1 ↔ i + 1 < m)) (h : P ↔ i % 2 = 1) :
    i + 1 < m := by
  have e2 := gf.symm.trans h
  by_contra hm
  rcases Nat.mod_two_eq_zero_or_one i with h0 | h0
  · exact absurd (e2.1 ⟨fun h' => by omega, fun h' => absurd h' hm⟩) (by omega)
  · exact hm ((e2.2 h0).1 h0)

section touch

variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hF : Deg2 V F) (hT : NoTypeIII V F) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat F c s (k + 2))
  (hsep : ¬ Conn F (back1 c s) (front1 c s))
  {z : Pt} {tf : Side} {m i i0 : ℕ} (hz : SigFrom F z tf m i0) (hi0 : i0 ≤ i) (hi : i < m)

lemma par_of_iff {a b : ℕ} (h : a % 2 = 1 ↔ b % 2 = 1) : a % 2 = b % 2 := by
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
    rcases Nat.mod_two_eq_zero_or_one b with hb | hb <;> simp_all

include hF hT hk hcell hpat hsep hz hi0 hi in
-- Through the cell behind `c_0`, a strip runs in direction `s`, at an odd index, into `c_0`.
--
theorem touch_behind (hq : cellJ z tf i = nb c s.opp) : tf = s ∧ i % 2 = 1 ∧ i + 1 < m := by
  have hc0 : IsCell V c := by have := hcell 0 (by omega); rwa [cellJ_zero] at this
  have h2 : 2 ≤ k + 2 := by omega
  have d1 := back_down hF hT hpat h2 hc0 hsep
  have d2 := back_down2 hF hT hpat h2 hc0 hsep
  have df : front (nb c s.opp) s ∈ F := by rw [front_nb_opp]; exact hpat.1
  obtain ⟨g1, g2, gb, gf⟩ := hz i hi0 hi
  rw [hq] at g1 g2 gb gf
  rcases side_cases s tf with h | h | h | h <;> rw [h] at g1 g2 gb gf
  · have hodd := g1.1 d1
    exact ⟨h, hodd, (gf.1 df).1 hodd⟩
  · obtain ⟨f1, _, fb, _⟩ := frame_opp (nb c s.opp) s
    rw [f1] at g1; rw [fb] at gb
    have := g1.1 d1; have := gb.1 df; omega
  · obtain ⟨_, fb, fl⟩ := frame_latA (nb c s.opp) s
    rw [fb] at gb
    have he := gb.1 d2
    rcases fl with ⟨_, h'⟩ | ⟨h', _⟩
    · rw [h'] at g2; have := g2.1 df; omega
    · rw [h'] at g1; have := g1.1 df; omega
  · obtain ⟨_, fb, fl⟩ := frame_latB (nb c s.opp) s
    rw [fb] at gb
    have he := gb.1 d1
    rcases fl with ⟨_, h'⟩ | ⟨h', _⟩
    · rw [h'] at g2; have := g2.1 df; omega
    · rw [h'] at g1; have := g1.1 df; omega

include hpat hz hi0 hi in
-- Through a cell `c_j` before the end cell, a strip runs in direction `s`, with the parity of
-- `j`, and continues.
--
theorem touch_body {j : ℕ} (hj : j ≤ k) (hq : cellJ z tf i = cellJ c s j) :
    tf = s ∧ i % 2 = j % 2 ∧ i + 1 < m := by
  obtain ⟨g1, g2, gb, gf⟩ := hz i hi0 hi
  obtain ⟨a1, a2, ab, af⟩ := strip_sig hpat (show j < k + 2 by omega)
  rw [hq] at g1 g2 gb gf
  -- In `a`'s frame the front of `c_j` is dark iff `j` is odd.
  --
  have af' : front (cellJ c s j) s ∈ F ↔ j % 2 = 1 := by rw [af]; omega
  rcases side_cases s tf with h | h | h | h <;> rw [h] at g1 g2 gb gf
  · have hp := par_of_iff (g1.symm.trans a1)
    refine ⟨h, hp, ?_⟩
    have e2 := gf.symm.trans af'
    by_contra hm
    rcases Nat.mod_two_eq_zero_or_one i with h0 | h0
    · exact absurd (e2.1 ⟨fun h' => by omega, fun h' => absurd h' hm⟩) (by omega)
    · exact hm (((e2.2 (by omega)).1) h0)
  · obtain ⟨f1, _, fb, _⟩ := frame_opp (cellJ c s j) s
    rw [f1] at g1; rw [fb] at gb
    have hp := par_of_iff (g1.symm.trans a1)
    have := gb.symm.trans af'
    exfalso
    rcases Nat.mod_two_eq_zero_or_one i with h0 | h0
    · have := this.1 h0; omega
    · have : ¬ (j % 2 = 1) := fun h' => by have := this.2 h'; omega
      omega
  · obtain ⟨_, _, fl⟩ := frame_latA (cellJ c s j) s
    exfalso
    have hbf : (back (cellJ c s j) s ∈ F ↔ front (cellJ c s j) s ∈ F) := by
      rcases fl with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1] at g1; rw [h2] at g2; exact g1.trans g2.symm
      · rw [h1] at g1; rw [h2] at g2; exact g2.trans g1.symm
    rw [ab, af'] at hbf; omega
  · obtain ⟨_, _, fl⟩ := frame_latB (cellJ c s j) s
    exfalso
    have hbf : (back (cellJ c s j) s ∈ F ↔ front (cellJ c s j) s ∈ F) := by
      rcases fl with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1] at g1; rw [h2] at g2; exact g1.trans g2.symm
      · rw [h1] at g1; rw [h2] at g2; exact g2.trans g1.symm
    rw [ab, af'] at hbf; omega

include hF hpat hcell in
-- The forced outer sides beside the body: `outer1 c_j` is dark iff `j` is even.
--
lemma outer1_body {j : ℕ} (hj : j ≤ k) : outer1 (cellJ c s j) s ∈ F ↔ j % 2 = 0 := by
  obtain ⟨a1, _, _, af⟩ := strip_sig hpat (show j < k + 2 by omega)
  obtain ⟨b1, _, _, _⟩ := strip_sig hpat (show j + 1 < k + 2 by omega)
  have hd := hF.2 _ (corners4 (hcell j (by omega)) s).2.2.1
  rw [deg_front1, nb_cellJ] at hd
  have af' : front (cellJ c s j) s ∈ F ↔ j % 2 = 1 := by rw [af]; omega
  by_cases h : j % 2 = 1
  · rw [ind_of_mem (a1.2 h), ind_of_mem (af'.2 h),
      ind_of_not_mem (fun h' => by have := b1.1 h'; omega)] at hd
    constructor
    · intro ho; rw [ind_of_mem ho] at hd; omega
    · intro h'; omega
  · rw [ind_of_not_mem (fun h' => h (a1.1 h')), ind_of_not_mem (fun h' => h (af'.1 h')),
      ind_of_mem (b1.2 (by omega))] at hd
    constructor
    · intro _; omega
    · intro _; by_contra ho; rw [ind_of_not_mem ho] at hd; omega

include hF hpat hcell in
lemma outer2_body {j : ℕ} (hj : j ≤ k) : outer2 (cellJ c s j) s ∈ F ↔ j % 2 = 0 := by
  obtain ⟨_, a2, _, af⟩ := strip_sig hpat (show j < k + 2 by omega)
  obtain ⟨_, b2, _, _⟩ := strip_sig hpat (show j + 1 < k + 2 by omega)
  have hd := hF.2 _ (corners4 (hcell j (by omega)) s).2.2.2
  rw [deg_front2, nb_cellJ] at hd
  have af' : front (cellJ c s j) s ∈ F ↔ j % 2 = 1 := by rw [af]; omega
  by_cases h : j % 2 = 1
  · rw [ind_of_mem (a2.2 h), ind_of_mem (af'.2 h),
      ind_of_not_mem (fun h' => by have := b2.1 h'; omega)] at hd
    constructor
    · intro ho; rw [ind_of_mem ho] at hd; omega
    · intro h'; omega
  · rw [ind_of_not_mem (fun h' => h (a2.1 h')), ind_of_not_mem (fun h' => h (af'.1 h')),
      ind_of_mem (b2.2 (by omega))] at hd
    constructor
    · intro _; omega
    · intro _; by_contra ho; rw [ind_of_not_mem ho] at hd; omega

include hF hT hk hcell hpat in
-- The cell beside the end cell, with dark back and front sides, has a light far side:
-- otherwise its four dark sides close a class that would have to contain `back2 e`.
--
lemma end_side_far1 (hb : outer1 (cellJ c s k) s ∈ F) (hf : outer1 (cellJ c s (k + 1)) s ∈ F) :
    lat1 (nb (cellJ c s (k + 1)) (latA s)) s ∉ F := by
  intro hl
  set u := cellJ c s (k + 1)
  set L := nb u (latA s)
  have hbL : back L s ∈ F := by
    rw [show back L s = outer1 (cellJ c s k) s by rw [← side_back_next, nb_cellJ]]; exact hb
  have hfL : front L s ∈ F := by rw [side_front]; exact hf
  have hnL : lat2 L s ∈ F := by
    rw [side_lat2]; exact (strip_sig hpat (show k + 1 < k + 2 by omega)).1.2 (by omega)
  have hV1 := (side_back_ends u s).inV (hF.1 _ hbL)
  have hV2 := (side_front_ends u s).inV (hF.1 _ hf)
  have hcL : IsCell V L := by
    refine isCell_of_corners L s hV1.1 ?_ hV2.1 ?_
    · rw [side_back2]; exact hV1.2
    · rw [side_front2]; exact hV2.2
  have hz : Conn F (back1 L s) (back2 u s) :=
    ((side_back_ends u s).conn hbL).trans (end_same hT hk hcell hpat)
  exact back2_not_side_corner u s (four_sides_class hF hcL s hbL hfL hl hnL hz)

lemma back1_not_side2_corner (c : Pt) (s : Side) :
    back1 c s ∉ ({back1 (nb c (latB s)) s, back2 (nb c (latB s)) s, front1 (nb c (latB s)) s,
      front2 (nb c (latB s)) s} : Finset Pt) := by
  obtain ⟨x, y⟩ := c
  cases s <;> simp [back1, back2, front1, front2, latB, nb] <;> omega

include hF hT hk hcell hpat in
lemma end_side_far2 (hb : outer2 (cellJ c s k) s ∈ F) (hf : outer2 (cellJ c s (k + 1)) s ∈ F) :
    lat2 (nb (cellJ c s (k + 1)) (latB s)) s ∉ F := by
  intro hl
  set u := cellJ c s (k + 1)
  set L := nb u (latB s)
  have hbL : back L s ∈ F := by
    rw [show back L s = outer2 (cellJ c s k) s by rw [outer2_side_nb_next, nb_cellJ]; rfl]
    exact hb
  have hfL : front L s ∈ F := by rw [side2_front]; exact hf
  have hnL : lat1 L s ∈ F := by
    rw [side2_lat1]; exact (strip_sig hpat (show k + 1 < k + 2 by omega)).2.1.2 (by omega)
  have hV1 := (side2_back_ends u s).inV (hF.1 _ hbL)
  have hV2 := (side2_front_ends u s).inV (hF.1 _ hf)
  have hcL : IsCell V L := by
    refine isCell_of_corners L s ?_ hV1.2 ?_ hV2.2
    · rw [side2_back1]; exact hV1.1
    · rw [side2_front1]; exact hV2.1
  have hz : Conn F (back1 L s) (back1 u s) := by
    rw [side2_back1]; exact (end_same hT hk hcell hpat).symm
  exact back1_not_side2_corner u s (four_sides_class hF hcL s hbL hfL hnL hl hz)

include hk hpat hz hi0 hi in
-- Through the end cell, a strip ends there: along or against `s` at an odd index, or across
-- at an even index.
--
theorem touch_end (hq : cellJ z tf i = cellJ c s (k + 1)) :
    i + 1 = m ∧ (((tf = s ∨ tf = s.opp) ∧ i % 2 = 1) ∨ ((tf = latA s ∨ tf = latB s) ∧ i % 2 = 0)) := by
  obtain ⟨g1, g2, gb, gf⟩ := hz i hi0 hi
  obtain ⟨a1, a2, ab, af⟩ := strip_sig hpat (show k + 1 < k + 2 by omega)
  rw [hq] at g1 g2 gb gf
  have l1 := a1.2 (by omega)
  have l2 := a2.2 (by omega)
  have hb' : back (cellJ c s (k + 1)) s ∉ F := fun h => by have := ab.1 h; omega
  have hf' : front (cellJ c s (k + 1)) s ∉ F := fun h => by have := (af.1 h).1 (by omega); omega
  rcases side_cases s tf with h | h | h | h <;> rw [h] at g1 g2 gb gf
  · have ho := g1.1 l1
    refine ⟨?_, Or.inl ⟨Or.inl h, ho⟩⟩
    by_contra hm
    exact hf' (gf.2 ⟨fun _ => by omega, fun _ => ho⟩)
  · obtain ⟨f1, _, _, ff⟩ := frame_opp (cellJ c s (k + 1)) s
    rw [f1] at g1; rw [ff] at gf
    have ho := g1.1 l1
    refine ⟨?_, Or.inl ⟨Or.inr h, ho⟩⟩
    by_contra hm
    exact hb' (gf.2 ⟨fun _ => by omega, fun _ => ho⟩)
  · obtain ⟨ff, _, fl⟩ := frame_latA (cellJ c s (k + 1)) s
    rw [ff] at gf
    have he : i % 2 = 0 := by
      rcases fl with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1] at g1
      · have := mt g1.2 hb'; omega
      · have := mt g1.2 hf'; omega
    refine ⟨?_, Or.inr ⟨Or.inl h, he⟩⟩
    have := (gf.1 l1); by_contra hm
    have := this.2 (by omega); omega
  · obtain ⟨ff, _, fl⟩ := frame_latB (cellJ c s (k + 1)) s
    rw [ff] at gf
    have he : i % 2 = 0 := by
      rcases fl with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1] at g1
      · have := mt g1.2 hb'; omega
      · have := mt g1.2 hf'; omega
    refine ⟨?_, Or.inr ⟨Or.inr h, he⟩⟩
    have := (gf.1 l2); by_contra hm
    have := this.2 (by omega); omega

lemma cell_prev {z : Pt} {tf : Side} {i : ℕ} (hi : 1 ≤ i) :
    cellJ z tf (i - 1) = nb (cellJ z tf i) tf.opp := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  rw [show j + 1 - 1 = j by omega, ← nb_cellJ, nb_nb_opp]

include hF hk hpat hcell hz hi0 hi in
-- Through the cell beyond the end cell: a strip against `s` ends there (odd index) or goes on
-- into the end cell (even index), or a strip across `s` starts there.
--
theorem touch_beyond (hpvs : tf = s → 1 ≤ i → i0 ≤ i - 1) (hpv2 : 2 ≤ i → i0 ≤ i - 1) (hq : cellJ z tf i = nb (cellJ c s (k + 1)) s) :
    (tf = s.opp ∧ i % 2 = 1 ∧ i + 1 = m) ∨ (tf = s.opp ∧ i % 2 = 0 ∧ i + 1 < m) ∨
      ((tf = latA s ∨ tf = latB s) ∧ i = 0) := by
  set e := cellJ c s (k + 1)
  obtain ⟨a1, a2, ab, af⟩ := strip_sig hpat (show k + 1 < k + 2 by omega)
  have l1 : lat1 e s ∈ F := a1.2 (by omega)
  have l2 : lat2 e s ∈ F := a2.2 (by omega)
  have hfe : front e s ∉ F := fun h => by have := (af.1 h).1 (by omega); omega
  have hbu : back (nb e s) s ∉ F := by rw [back_nb]; exact hfe
  obtain ⟨g1, g2, gb, gf⟩ := hz i hi0 hi
  rw [hq] at g1 g2 gb gf
  rcases side_cases s tf with h | h | h | h <;> rw [h] at g1 g2 gb gf
  · exfalso
    have ho : i % 2 = 1 := by have := mt gb.2 hbu; omega
    have hp := cell_prev (z := z) (tf := tf) (i := i) (by omega)
    rw [hq, h, nb_nb_opp] at hp
    obtain ⟨p1, _, _, _⟩ := hz (i - 1) (hpvs h (by omega)) (show i - 1 < m by omega)
    rw [h] at p1; rw [hp] at p1
    have := p1.1 l1; omega
  · obtain ⟨_, _, _, ff⟩ := frame_opp (nb e s) s
    rw [ff] at gf
    rcases Nat.mod_two_eq_zero_or_one i with h0 | h0
    · refine Or.inr (Or.inl ⟨h, h0, ?_⟩)
      by_contra hm; exact hbu (gf.2 ⟨fun h' => by omega, fun h' => absurd h' hm⟩)
    · refine Or.inl ⟨h, h0, ?_⟩
      by_contra hm; exact hbu (gf.2 ⟨fun _ => by omega, fun _ => h0⟩)
  · obtain ⟨_, fb, fl⟩ := frame_latA (nb e s) s
    rw [fb] at gb
    have he : i % 2 = 0 := by
      rcases fl with ⟨h1, _⟩ | ⟨_, h2⟩
      · rw [h1] at g1; have := mt g1.2 hbu; omega
      · rw [h2] at g2; have := mt g2.2 hbu; omega
    refine Or.inr (Or.inr ⟨Or.inl h, ?_⟩)
    by_contra h0
    exfalso
    have hl2u := gb.2 he
    have hp := cell_prev (z := z) (tf := tf) (i := i) (by omega)
    rw [hq, h, ← latB_eq_opp] at hp
    obtain ⟨p1, p2, _, _⟩ := hz (i - 1) (hpv2 (by omega)) (show i - 1 < m by omega)
    rw [h] at p1 p2; rw [hp] at p1 p2
    have hbP : back (nb (nb e s) (latB s)) s ∈ F := by
      obtain ⟨_, _, fl'⟩ := frame_latA (nb (nb e s) (latB s)) s
      rcases fl' with ⟨h1, _⟩ | ⟨_, h2⟩
      · rw [← h1]; exact p1.2 (by omega)
      · rw [← h2]; exact p2.2 (by omega)
    have ho : outer2 e s ∈ F := by rw [outer2_side_nb_next]; exact hbP
    have hd := hF.2 _ (corners4 (hcell (k + 1) le_rfl) s).2.2.2
    rw [deg_front2, ind_of_mem l2, ind_of_not_mem hfe, ind_of_mem hl2u, ind_of_mem ho] at hd
    omega
  · obtain ⟨_, fb, fl⟩ := frame_latB (nb e s) s
    rw [fb] at gb
    have he : i % 2 = 0 := by
      rcases fl with ⟨h1, _⟩ | ⟨_, h2⟩
      · rw [h1] at g1; have := mt g1.2 hbu; omega
      · rw [h2] at g2; have := mt g2.2 hbu; omega
    refine Or.inr (Or.inr ⟨Or.inr h, ?_⟩)
    by_contra h0
    exfalso
    have hl1u := gb.2 he
    have hp := cell_prev (z := z) (tf := tf) (i := i) (by omega)
    have hBA : (latB s).opp = latA s := by rw [latB_eq_opp, opp_opp]
    rw [hq, h, hBA] at hp
    obtain ⟨p1, p2, _, _⟩ := hz (i - 1) (hpv2 (by omega)) (show i - 1 < m by omega)
    rw [h] at p1 p2; rw [hp] at p1 p2
    have hbP : back (nb (nb e s) (latA s)) s ∈ F := by
      obtain ⟨_, _, fl'⟩ := frame_latB (nb (nb e s) (latA s)) s
      rcases fl' with ⟨h1, _⟩ | ⟨_, h2⟩
      · rw [← h1]; exact p1.2 (by omega)
      · rw [← h2]; exact p2.2 (by omega)
    have ho : outer1 e s ∈ F := by rw [outer1_side_nb_next]; exact hbP
    have hd := hF.2 _ (corners4 (hcell (k + 1) le_rfl) s).2.2.1
    rw [deg_front1, ind_of_mem l1, ind_of_not_mem hfe, ind_of_mem hl1u, ind_of_mem ho] at hd
    omega

include hF hT hk hcell hpat hsep in
-- The sides of the cell beside `c_j` (across `lat1`), for `j` before the end cell.
--
lemma side1_facts {j : ℕ} (hj : j ≤ k) :
    (lat2 (nb (cellJ c s j) (latA s)) s ∈ F ↔ j % 2 = 1) ∧
      (back (nb (cellJ c s j) (latA s)) s ∈ F ↔ j % 2 = 1) ∧
      (front (nb (cellJ c s j) (latA s)) s ∈ F ↔ j % 2 = 0) := by
  refine ⟨by rw [side_lat2]; exact (strip_sig hpat (show j < k + 2 by omega)).1, ?_, ?_⟩
  · rcases j with _ | j
    · rw [cellJ_zero]
      have hc0 : IsCell V c := by have := hcell 0 (by omega); rwa [cellJ_zero] at this
      simp only [Nat.zero_mod, zero_ne_one, iff_false]
      exact back_outer_light hF hT hpat (by omega) hc0 hsep
    · rw [← nb_cellJ, side_back_next, outer1_body hF hcell hpat (by omega)]; omega
  · rw [side_front]; exact outer1_body hF hcell hpat hj

include hF hT hk hcell hpat hsep in
lemma side2_facts {j : ℕ} (hj : j ≤ k) :
    (lat1 (nb (cellJ c s j) (latB s)) s ∈ F ↔ j % 2 = 1) ∧
      (back (nb (cellJ c s j) (latB s)) s ∈ F ↔ j % 2 = 1) ∧
      (front (nb (cellJ c s j) (latB s)) s ∈ F ↔ j % 2 = 0) := by
  refine ⟨by rw [side2_lat1]; exact (strip_sig hpat (show j < k + 2 by omega)).2.1, ?_, ?_⟩
  · rcases j with _ | j
    · rw [cellJ_zero]
      have hc0 : IsCell V c := by have := hcell 0 (by omega); rwa [cellJ_zero] at this
      simp only [Nat.zero_mod, zero_ne_one, iff_false]
      exact back_outer2_light hF hT hpat (by omega) hc0 hsep
    · rw [← nb_cellJ, show back (nb (nb (cellJ c s j) s) (latB s)) s = outer2 (cellJ c s j) s by
        rw [outer2_side_nb_next]; rfl, outer2_body hF hcell hpat (by omega)]; omega
  · rw [side2_front]; exact outer2_body hF hcell hpat hj

include hF hT hk hcell hpat hsep hz hi0 hi in
-- Beside the body (across `lat1`), a strip runs against `s`, with the parity of `j`, and
-- continues.
--
theorem touch_side1 {j : ℕ} (hj : j ≤ k) (hq : cellJ z tf i = nb (cellJ c s j) (latA s)) :
    tf = s.opp ∧ i % 2 = j % 2 ∧ i + 1 < m := by
  obtain ⟨fn, fb, ff⟩ := side1_facts hF hT hk hcell hpat hsep hj
  obtain ⟨g1, g2, gb, gf⟩ := hz i hi0 hi
  rw [hq] at g1 g2 gb gf
  set L := nb (cellJ c s j) (latA s)
  rcases side_cases s tf with h | h | h | h <;> rw [h] at g1 g2 gb gf
  · exfalso
    have hp := par_of_iff (g2.symm.trans fn)
    rcases Nat.mod_two_eq_zero_or_one i with h0 | h0
    · have := fb.1 (gb.2 h0); omega
    · have : back L s ∈ F := fb.2 (by omega)
      have := gb.1 this; omega
  · obtain ⟨_, f2, fbk, ff'⟩ := frame_opp L s
    rw [f2] at g2; rw [ff'] at gf
    have hp := par_of_iff (g2.symm.trans fn)
    exact ⟨h, hp, cont_of gf (fb.trans (by omega))⟩
  · exfalso
    have := perp_bf g1 g2 (frame_latA L s).2.2
    rw [fb, ff] at this; omega
  · exfalso
    have := perp_bf g1 g2 (frame_latB L s).2.2
    rw [fb, ff] at this; omega

include hF hT hk hcell hpat hsep hz hi0 hi in
theorem touch_side2 {j : ℕ} (hj : j ≤ k) (hq : cellJ z tf i = nb (cellJ c s j) (latB s)) :
    tf = s.opp ∧ i % 2 = j % 2 ∧ i + 1 < m := by
  obtain ⟨fn, fb, ff⟩ := side2_facts hF hT hk hcell hpat hsep hj
  obtain ⟨g1, g2, gb, gf⟩ := hz i hi0 hi
  rw [hq] at g1 g2 gb gf
  set L := nb (cellJ c s j) (latB s)
  rcases side_cases s tf with h | h | h | h <;> rw [h] at g1 g2 gb gf
  · exfalso
    have hp := par_of_iff (g1.symm.trans fn)
    rcases Nat.mod_two_eq_zero_or_one i with h0 | h0
    · have := fb.1 (gb.2 h0); omega
    · have : back L s ∈ F := fb.2 (by omega)
      have := gb.1 this; omega
  · obtain ⟨f1, _, fbk, ff'⟩ := frame_opp L s
    rw [f1] at g1; rw [ff'] at gf
    have hp := par_of_iff (g1.symm.trans fn)
    exact ⟨h, hp, cont_of gf (fb.trans (by omega))⟩
  · exfalso
    have := perp_bf g1 g2 (frame_latA L s).2.2
    rw [fb, ff] at this; omega
  · exfalso
    have := perp_bf g1 g2 (frame_latB L s).2.2
    rw [fb, ff] at this; omega

include hF hk hcell hpat hz hi0 hi in
-- Beside the end cell (across `lat1`): a strip runs against `s` and continues, or it crosses
-- into the end cell with dark outer sides and a light far side (then `beside_end1` applies).
--
theorem touch_side1_end (hq : cellJ z tf i = nb (cellJ c s (k + 1)) (latA s)) :
    (tf = s.opp ∧ i % 2 = 1 ∧ i + 1 < m) ∨
      (tf = latB s ∧ outer1 (cellJ c s (k + 1)) s ∈ F ∧
        lat1 (nb (cellJ c s (k + 1)) (latA s)) s ∉ F) := by
  set L := nb (cellJ c s (k + 1)) (latA s)
  have fn : lat2 L s ∈ F := by
    rw [side_lat2]; exact (strip_sig hpat (show k + 1 < k + 2 by omega)).1.2 (by omega)
  have fb : back L s ∈ F := by
    rw [show back L s = outer1 (cellJ c s k) s by rw [← side_back_next, nb_cellJ]]
    exact (outer1_body hF hcell hpat le_rfl).2 hk
  obtain ⟨g1, g2, gb, gf⟩ := hz i hi0 hi
  rw [hq] at g1 g2 gb gf
  rcases side_cases s tf with h | h | h | h <;> rw [h] at g1 g2 gb gf
  · exfalso; have := g2.1 fn; have := gb.1 fb; omega
  · obtain ⟨_, f2, _, ff'⟩ := frame_opp L s
    rw [f2] at g2; rw [ff'] at gf
    have ho := g2.1 fn
    exact Or.inl ⟨h, ho, cont_of gf ⟨fun _ => ho, fun _ => fb⟩⟩
  · exfalso
    obtain ⟨_, fbk, fl⟩ := frame_latA L s
    rw [fbk] at gb
    have he := gb.1 fn
    rcases fl with ⟨h1, _⟩ | ⟨_, h2⟩
    · rw [h1] at g1; have := g1.1 fb; omega
    · rw [h2] at g2; have := g2.1 fb; omega
  · obtain ⟨_, fbk, fl⟩ := frame_latB L s
    rw [fbk] at gb
    have ho : i % 2 = 1 := by
      rcases fl with ⟨h1, _⟩ | ⟨_, h2⟩
      · rw [h1] at g1; exact g1.1 fb
      · rw [h2] at g2; exact g2.1 fb
    refine Or.inr ⟨h, ?_, fun h' => by have := gb.1 h'; omega⟩
    rw [← side_front]
    rcases fl with ⟨_, h2⟩ | ⟨h1, _⟩
    · rw [h2] at g2; exact g2.2 ho
    · rw [h1] at g1; exact g1.2 ho

include hF hk hcell hpat hz hi0 hi in
theorem touch_side2_end (hq : cellJ z tf i = nb (cellJ c s (k + 1)) (latB s)) :
    (tf = s.opp ∧ i % 2 = 1 ∧ i + 1 < m) ∨
      (tf = latA s ∧ outer2 (cellJ c s (k + 1)) s ∈ F ∧
        lat2 (nb (cellJ c s (k + 1)) (latB s)) s ∉ F) := by
  set L := nb (cellJ c s (k + 1)) (latB s)
  have fn : lat1 L s ∈ F := by
    rw [side2_lat1]; exact (strip_sig hpat (show k + 1 < k + 2 by omega)).2.1.2 (by omega)
  have fb : back L s ∈ F := by
    rw [show back L s = outer2 (cellJ c s k) s by rw [outer2_side_nb_next, nb_cellJ]; rfl]
    exact (outer2_body hF hcell hpat le_rfl).2 hk
  obtain ⟨g1, g2, gb, gf⟩ := hz i hi0 hi
  rw [hq] at g1 g2 gb gf
  rcases side_cases s tf with h | h | h | h <;> rw [h] at g1 g2 gb gf
  · exfalso; have := g1.1 fn; have := gb.1 fb; omega
  · obtain ⟨f1, _, _, ff'⟩ := frame_opp L s
    rw [f1] at g1; rw [ff'] at gf
    have ho := g1.1 fn
    exact Or.inl ⟨h, ho, cont_of gf ⟨fun _ => ho, fun _ => fb⟩⟩
  · obtain ⟨_, fbk, fl⟩ := frame_latA L s
    rw [fbk] at gb
    have ho : i % 2 = 1 := by
      rcases fl with ⟨h1, _⟩ | ⟨_, h2⟩
      · rw [h1] at g1; exact g1.1 fb
      · rw [h2] at g2; exact g2.1 fb
    refine Or.inr ⟨h, ?_, fun h' => by have := gb.1 h'; omega⟩
    rw [← side2_front]
    rcases fl with ⟨_, h2⟩ | ⟨h1, _⟩
    · rw [h2] at g2; exact g2.2 ho
    · rw [h1] at g1; exact g1.2 ho
  · exfalso
    obtain ⟨_, fbk, fl⟩ := frame_latB L s
    rw [fbk] at gb
    have he := gb.1 fn
    rcases fl with ⟨h1, _⟩ | ⟨_, h2⟩
    · rw [h1] at g1; have := g1.1 fb; omega
    · rw [h2] at g2; have := g2.1 fb; omega

end touch

end ULHC
