/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import SolidGridHam.Cycle.NearChain

@[expose] public section

/-!
# Touch analysis for strips that keep off the previous end cell

`NoChain b c`: no cell of `c` shares a side with `b`'s end cell, so `c`'s pattern holds in `G`
itself. The touch classification here (`touch_outcome`, `touch_outcomeW`) and the shortcut
`link_a` are used by the near lemma for chain links anywhere (`NearCA.lean`).

* `link_a`: a strip of `G` that does not touch `a`, whose start is split by `a`'s end cell, is a
  link from `a`. All shortcuts of the near lemma end in this.
-/

namespace SolidGridHam

open Finset

def NoChain (b c : StripSpec) : Prop :=
  ∀ j < c.n, ∀ x ∈ cellE (cellJ c.c c.s j), x ∉ cellE (endCell b)

lemma pat_flip_off {F : Finset Edge} {u : Pt} {w : StripSpec} (h1 : 1 ≤ w.n)
    (hoff : ∀ j < w.n, ∀ x ∈ cellE (cellJ w.c w.s j), x ∉ cellE u) :
    StripPat (flip F u) w.c w.s w.n ↔ StripPat F w.c w.s w.n := by
  obtain ⟨n, hn⟩ : ∃ n, w.n = n + 1 := ⟨w.n - 1, by omega⟩
  rw [hn] at hoff ⊢
  exact stripPat_congr (fun j hj e he => mem_flip_off (hoff j hj e he))

-- Dark edges of a strip at its start corners.
--
lemma start_corner_edges {F : Finset Edge} {w : StripSpec} (hp : StripPat F w.c w.s w.n)
    (h1 : 1 ≤ w.n) :
    (back w.c w.s ∈ F ∧ ((back w.c w.s).p = back1 w.c w.s ∨ (back w.c w.s).q = back1 w.c w.s) ∧
      back w.c w.s ∈ cellE (cellJ w.c w.s 0)) ∧
    ∃ j < w.n, ∃ x ∈ F, (x.p = front1 w.c w.s ∨ x.q = front1 w.c w.s) ∧
      x ∈ cellE (cellJ w.c w.s j) := by
  refine ⟨⟨hp.1, (ends_back w.c w.s).inc_iff _ |>.2 (Or.inl rfl), by
    rw [cellJ_zero, cellE_frame w.c w.s]; simp⟩, ?_⟩
  by_cases hn : w.n = 1
  · refine ⟨0, by omega, front w.c w.s, ?_, (ends_front w.c w.s).inc_iff _ |>.2 (Or.inl rfl), ?_⟩
    · have := hp.2.2 0 (by omega); rw [cellJ_zero] at this; rw [this]; omega
    · rw [cellJ_zero, cellE_frame w.c w.s]; simp
  · refine ⟨1, by omega, lat1 (cellJ w.c w.s 1) w.s, (hp.2.1 1 (by omega)).1.2 rfl, ?_, ?_⟩
    · have he := ends_lat1 (cellJ w.c w.s 1) w.s
      rw [← nb_cellJ, cellJ_zero, back1_nb] at he
      rw [← nb_cellJ, cellJ_zero]
      exact he.inc_iff _ |>.2 (Or.inl rfl)
    · rw [cellE_frame _ w.s]; simp

section linka

variable {V : Finset Pt} {G : Finset Edge} {a : StripSpec}
  (hG : Deg2 V G) (ha : ValidStrip V G a) (hae : a.n % 2 = 0) (ha2 : 2 ≤ a.n)
include hG ha hae ha2

-- A strip of `G` not touching `a`, whose start `a`'s end cell splits, is a link from `a`.
--
theorem link_a {w : StripSpec} (hw1 : 1 ≤ w.n) (hpw : StripPat G w.c w.s w.n)
    (hcw : ∀ j < w.n, IsCell V (cellJ w.c w.s j)) (hnt : ¬ Touches a w)
    (hcg : Conn G (back1 w.c w.s) (front1 w.c w.s))
    (hcu : ¬ Conn (flip G (endCell a)) (back1 w.c w.s) (front1 w.c w.s)) : CR2 V G a w := by
  obtain ⟨k, hk⟩ : ∃ k, a.n = k + 2 := ⟨a.n - 2, by omega⟩
  obtain ⟨_, hpa, hca, _⟩ := ha
  rw [hk] at hpa hca
  have hcell : ∀ j ≤ k + 1, IsCell V (cellJ a.c a.s j) := fun j hj => hca j (by omega)
  have hoff : ∀ j < w.n, ∀ i < a.n, ∀ x ∈ cellE (cellJ w.c w.s j), x ∉ cellE (cellJ a.c a.s i) :=
    fun j hj i hi x hx hx' => hnt ⟨j, hj, i, hi, x, hx, hx'⟩
  have hend : endCell a = cellJ a.c a.s (a.n - 1) := rfl
  have hmid : ∀ p, (∃ j < w.n, ∃ x ∈ G, (x.p = p ∨ x.q = p) ∧ x ∈ cellE (cellJ w.c w.s j)) →
      ¬ IsMid a.c a.s (a.n - 2) p := by
    rintro p ⟨j, hj, x, hx, hxp, hxw⟩ hm
    rw [hk, show k + 2 - 2 = k by omega] at hm
    obtain ⟨i, hi, hxi⟩ := mid_touch hG hpa hcell hm hx hxp
    exact hoff j hj i (by omega) x hxw hxi
  obtain ⟨⟨hb, hbp, hb0⟩, hfr⟩ := start_corner_edges hpw hw1
  refine ⟨ha2, hae, hw1, (pat_flip_off hw1 (fun j hj x hx => by
      rw [hend]; exact hoff j hj _ (by omega) x hx)).2 hpw, hcw,
    fun j hj i hi x hx => hoff j hj i (by omega) x hx, ?_, ?_,
    hmid _ ⟨0, by omega, _, hb, hbp, hb0⟩, hmid _ hfr, hcg, hcu⟩
  · intro j hj heq
    have := side_mem_self (cellJ w.c w.s j) .b
    exact hoff j hj (a.n - 1) (by omega) _ this (by rw [← hend, ← heq]; exact this)
  · intro _ x hx
    rw [hend]; exact hoff _ (by omega) _ (by omega) x hx

end linka

lemma cellJ_down (c : Pt) (s : Side) (j : ℕ) : nb (cellJ c s (j + 1)) s.opp = cellJ c s j := by
  rw [← nb_cellJ, nb_nb_opp]

lemma behind_up (c : Pt) (s : Side) : nb (nb c s.opp) s = c := by
  have h := nb_nb_opp c s.opp; rwa [opp_opp] at h

-- An alternating cell, read in any frame: opposite sides agree, and back and lateral sides
-- differ.
--
lemma alt_frame {F : Finset Edge} {w : Pt} {tw : Side} (s : Side)
    (l1 : lat1 w tw ∈ F) (l2 : lat2 w tw ∈ F) (bw : back w tw ∉ F) (fw : front w tw ∉ F) :
    (back w s ∈ F ↔ front w s ∈ F) ∧ (lat1 w s ∈ F ↔ lat2 w s ∈ F) ∧
      (back w s ∈ F ↔ lat1 w s ∉ F) := by
  rcases side_cases s tw with h | h | h | h <;> subst h
  · tauto
  · obtain ⟨f1, f2, fb, ff⟩ := frame_opp w s
    rw [f1] at l1; rw [f2] at l2; rw [fb] at bw; rw [ff] at fw
    tauto
  · obtain ⟨ff, fb, fl⟩ := frame_latA w s
    rw [ff] at fw; rw [fb] at bw
    rcases fl with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1] at l1 <;> rw [h2] at l2 <;> tauto
  · obtain ⟨ff, fb, fl⟩ := frame_latB w s
    rw [ff] at fw; rw [fb] at bw
    rcases fl with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1] at l1 <;> rw [h2] at l2 <;> tauto

-- The two corners of a cell's `lat1` side, for a frame across `s`, are the two corners of its
-- back or of its front side in the frame `s`.
--
lemma perp_pair (d : Pt) {s tf : Side} (ht : tf = latA s ∨ tf = latB s) :
    (back1 d tf = back1 d s ∧ front1 d tf = back2 d s) ∨
      (back1 d tf = back2 d s ∧ front1 d tf = back1 d s) ∨
      (back1 d tf = front1 d s ∧ front1 d tf = front2 d s) ∨
      (back1 d tf = front2 d s ∧ front1 d tf = front1 d s) := by
  obtain ⟨x, y⟩ := d
  rcases ht with rfl | rfl <;> cases s <;> simp [back1, front1, back2, front2, latA, latB]

-- Turning a split pair on a cell's front side into one on its back side, through its dark
-- lateral sides.
--
lemma front_to_back {A : Finset Edge} {d : Pt} {s : Side} (h1 : lat1 d s ∈ A) (h2 : lat2 d s ∈ A)
    (hn : ¬ Conn A (front1 d s) (front2 d s)) : ¬ Conn A (back1 d s) (back2 d s) := fun h =>
  hn ((((ends_lat1 d s).conn h1).symm.trans h).trans ((ends_lat2 d s).conn h2))

-- From a split `lat1` pair across `s` to a split back pair, for a cell whose `s`-lateral
-- sides are dark.
--
lemma cross_to_back {A : Finset Edge} {d : Pt} {s tf : Side} (ht : tf = latA s ∨ tf = latB s)
    (h1 : lat1 d s ∈ A) (h2 : lat2 d s ∈ A) (hn : ¬ Conn A (back1 d tf) (front1 d tf)) :
    ¬ Conn A (back1 d s) (back2 d s) := by
  rcases perp_pair d ht with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2] at hn
  · exact hn
  · exact fun h => hn h.symm
  · exact front_to_back h1 h2 hn
  · exact front_to_back h1 h2 (fun h => hn h.symm)

lemma ends_unique {e : Edge} {u v u' v' : Pt} (h : Ends e u v) (h' : Ends e u' v') :
    (u = u' ∧ v = v') ∨ (u = v' ∧ v = u') := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases h' with ⟨h3, h4⟩ | ⟨h3, h4⟩
  · exact Or.inl ⟨h1.symm.trans h3, h2.symm.trans h4⟩
  · exact Or.inr ⟨h1.symm.trans h3, h2.symm.trans h4⟩
  · exact Or.inr ⟨h2.symm.trans h4, h1.symm.trans h3⟩
  · exact Or.inl ⟨h2.symm.trans h4, h1.symm.trans h3⟩

lemma conn_lat1_opp {A : Finset Edge} {d : Pt} {s : Side}
    (h : ¬ Conn A (back1 d s) (front1 d s)) : ¬ Conn A (back1 d s.opp) (front1 d s.opp) := by
  have e1 := ends_lat1 d s.opp
  rw [(frame_opp d s).1] at e1
  rcases ends_unique (ends_lat1 d s) e1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [← h1, ← h2]; exact h
  · rw [← h1, ← h2]; exact fun h' => h h'.symm

lemma two_at {A : Finset Edge} {p : Pt} {g1 g2 x : Edge} (hdeg : deg A p = 2) (h1 : g1 ∈ A)
    (h2 : g2 ∈ A) (i1 : g1.p = p ∨ g1.q = p) (i2 : g2.p = p ∨ g2.q = p) (n12 : g1 ≠ g2)
    (hx : x ∈ A) (ix : x.p = p ∨ x.q = p) : x = g1 ∨ x = g2 := by
  by_contra h
  push Not at h
  have := three_le_deg h1 h2 hx i1 i2 ix n12 (Ne.symm h.1) (Ne.symm h.2)
  omega

lemma latA_ne_opp (s : Side) : latA s ≠ s.opp := by cases s <;> simp [latA, Side.opp]
lemma latB_ne_opp (s : Side) : latB s ≠ s.opp := by cases s <;> simp [latB, Side.opp]
lemma latA_opp_eq (s : Side) : (latA s).opp = latB s := by rw [latB_eq_opp]
lemma latB_opp_eq (s : Side) : (latB s).opp = latA s := by rw [latB_eq_opp, opp_opp]

lemma back1_ne_front1_nb (d : Pt) (s : Side) : back1 d s ≠ front1 (nb d s) s := by
  obtain ⟨x, y⟩ := d; cases s <;> simp [back1, front1, nb] <;> omega

lemma back2_ne_front2_nb (d : Pt) (s : Side) : back2 d s ≠ front2 (nb d s) s := by
  obtain ⟨x, y⟩ := d; cases s <;> simp [back2, front2, nb] <;> omega

lemma wt_cons (τ w : StripSpec) (L : List StripSpec) : wt τ (w :: L) = τ.n + wt w L := by
  simp [wt]

section classifyW

variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hs : Solid V) (x0 : Pt) (hconn : ∀ z ∈ V, Conn (GE V) x0 z)
  (hF : Deg2 V F) (hT : NoTypeIII V F) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat F c s (k + 2))
  (hsep : ¬ Conn F (back1 c s) (front1 c s)) (hT' : NoTypeIII V (flipCol F c s (k + 2)))
  {z : Pt} {tf : Side} {m i0 : ℕ} (hzw : SigFrom F z tf m i0)
include hs x0 hconn hF hT hk hcell hpat hsep hT' hzw

-- `touch_outcome` for a pattern holding from index `i0`, reporting indices from the touching
-- one on.
--
omit hs x0 hconn in
theorem touch_outcomeW {i j : ℕ} (hi0 : i0 ≤ i) (hi : i < m) (hj : j < k + 2) {x : Edge}
    (hx1 : x ∈ cellE (cellJ z tf i)) (hx2 : x ∈ cellE (cellJ c s j)) :
    (∃ i', i ≤ i' ∧ i' < m ∧ cellJ z tf i' = cellJ c s (k + 1)) ∨
      (∃ i', i ≤ i' ∧ i' < m ∧ cellJ z tf i' = nb (cellJ c s (k + 1)) s) ∨
      (tf = s.opp ∧ ∃ ie, i ≤ ie ∧ ie < m ∧ ie % 2 = 0 ∧
        (cellJ z tf ie = nb c (latA s) ∨ cellJ z tf ie = nb c (latB s))) := by
  have re : ∀ i' j', i ≤ i' → i' < m → j' ≤ k + 1 → cellJ z tf i' = cellJ c s j' →
      ∃ i'', i ≤ i'' ∧ i'' < m ∧ cellJ z tf i'' = cellJ c s (k + 1) := fun i' j' hii hi' hj' hq => by
    obtain ⟨i'', h0, h1, h2⟩ := reach_end hk hpat hzw (k + 1 - j') i' j' (by omega) (by omega) hi' hq
    exact ⟨i'', by omega, h1, h2⟩
  rcases touch_cases s hx1 hx2 with hq | hq | hq | hq | hq
  · exact Or.inl (re i j le_rfl hi (by omega) hq)
  · by_cases hjk : j ≤ k
    · exact Or.inl (re i (j + 1) le_rfl hi (by omega) (by rw [hq, nb_cellJ]))
    · exact Or.inr (Or.inl ⟨i, le_rfl, hi, by rw [hq, show j = k + 1 by omega]⟩)
  · rcases j with _ | j
    · rw [cellJ_zero] at hq
      obtain ⟨ht, _, hi1⟩ := touch_behind hF hT hk hcell hpat hsep hzw hi0 hi hq
      refine Or.inl (re (i + 1) 0 (by omega) hi1 (by omega) ?_)
      rw [← nb_cellJ, hq, ht, behind_up, cellJ_zero]
    · exact Or.inl (re i j le_rfl hi (by omega) (by rw [hq, cellJ_down]))
  · by_cases hjk : j ≤ k
    · obtain ⟨ht, ie, hle, h1, h2, h3⟩ := side_chain1 hF hT hk hcell hpat hsep hzw j i hjk hi0 hi hq
      exact Or.inr (Or.inr ⟨ht, ie, hle, h1, h2, Or.inl h3⟩)
    · obtain rfl : j = k + 1 := by omega
      rcases touch_side1_end hF hk hcell hpat hzw hi0 hi hq with ⟨ht, _, hi1⟩ | ⟨_, hf, hl⟩
      · obtain ⟨ht', ie, hle, h1, h2, h3⟩ := side_chain1 hF hT hk hcell hpat hsep hzw k (i + 1) le_rfl (by omega)
          hi1 (by rw [← nb_cellJ, hq, ht, side1_down])
        exact Or.inr (Or.inr ⟨ht', ie, by omega, h1, h2, Or.inl h3⟩)
      · exact absurd hT' (beside_end1 hF hT hk hcell hpat hsep
          ((outer1_body hF hcell hpat le_rfl).2 hk) hf hl)
  · by_cases hjk : j ≤ k
    · obtain ⟨ht, ie, hle, h1, h2, h3⟩ := side_chain2 hF hT hk hcell hpat hsep hzw j i hjk hi0 hi hq
      exact Or.inr (Or.inr ⟨ht, ie, hle, h1, h2, Or.inr h3⟩)
    · obtain rfl : j = k + 1 := by omega
      rcases touch_side2_end hF hk hcell hpat hzw hi0 hi hq with ⟨ht, _, hi1⟩ | ⟨_, hf, hl⟩
      · obtain ⟨ht', ie, hle, h1, h2, h3⟩ := side_chain2 hF hT hk hcell hpat hsep hzw k (i + 1) le_rfl (by omega)
          hi1 (by rw [← nb_cellJ, hq, ht, side2_down])
        exact Or.inr (Or.inr ⟨ht', ie, by omega, h1, h2, Or.inr h3⟩)
      · exact absurd hT' (beside_end2 hF hT hk hcell hpat hsep
          ((outer2_body hF hcell hpat le_rfl).2 hk) hf hl)

end classifyW

section classify

variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hs : Solid V) (x0 : Pt) (hconn : ∀ z ∈ V, Conn (GE V) x0 z)
  (hF : Deg2 V F) (hT : NoTypeIII V F) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat F c s (k + 2))
  (hsep : ¬ Conn F (back1 c s) (front1 c s)) (hT' : NoTypeIII V (flipCol F c s (k + 2)))
  {z : Pt} {tf : Side} {m : ℕ} (hz : StripPat F z tf m)
include hs x0 hconn hF hT hk hcell hpat hsep hT' hz

-- A strip touching `a` reaches the end cell, or the cell beyond it, or runs against `s`
-- to a cell beside `c_0`, which it meets at an even index.
omit hs hconn in
--
omit x0 in
theorem touch_outcome {i j : ℕ} (hi : i < m) (hj : j < k + 2) {x : Edge}
    (hx1 : x ∈ cellE (cellJ z tf i)) (hx2 : x ∈ cellE (cellJ c s j)) :
    (∃ i' < m, cellJ z tf i' = cellJ c s (k + 1)) ∨
      (∃ i' < m, cellJ z tf i' = nb (cellJ c s (k + 1)) s) ∨
      (tf = s.opp ∧ ∃ i0 < m, i0 % 2 = 0 ∧
        (cellJ z tf i0 = nb c (latA s) ∨ cellJ z tf i0 = nb c (latB s))) := by
  have re : ∀ i' j', i' < m → j' ≤ k + 1 → cellJ z tf i' = cellJ c s j' →
      ∃ i'' < m, cellJ z tf i'' = cellJ c s (k + 1) := fun i' j' hi' hj' hq => by
    obtain ⟨i'', -, h1, h2⟩ := reach_end hk hpat (sig_of_pat hz) (k + 1 - j') i' j' (by omega) (Nat.zero_le _) hi' hq
    exact ⟨i'', h1, h2⟩
  rcases touch_cases s hx1 hx2 with hq | hq | hq | hq | hq
  · exact Or.inl (re i j hi (by omega) hq)
  · by_cases hjk : j ≤ k
    · exact Or.inl (re i (j + 1) hi (by omega) (by rw [hq, nb_cellJ]))
    · exact Or.inr (Or.inl ⟨i, hi, by rw [hq, show j = k + 1 by omega]⟩)
  · rcases j with _ | j
    · rw [cellJ_zero] at hq
      obtain ⟨ht, _, hi1⟩ := touch_behind hF hT hk hcell hpat hsep (sig_of_pat hz) (Nat.zero_le _) hi hq
      refine Or.inl (re (i + 1) 0 hi1 (by omega) ?_)
      rw [← nb_cellJ, hq, ht, behind_up, cellJ_zero]
    · exact Or.inl (re i j hi (by omega) (by rw [hq, cellJ_down]))
  · by_cases hjk : j ≤ k
    · obtain ⟨ht, i0, -, h1, h2, h3⟩ := side_chain1 hF hT hk hcell hpat hsep (sig_of_pat hz) j i hjk (Nat.zero_le _) hi hq
      exact Or.inr (Or.inr ⟨ht, i0, h1, h2, Or.inl h3⟩)
    · obtain rfl : j = k + 1 := by omega
      rcases touch_side1_end hF hk hcell hpat (sig_of_pat hz) (Nat.zero_le _) hi hq with ⟨ht, _, hi1⟩ | ⟨_, hf, hl⟩
      · obtain ⟨ht', i0, -, h1, h2, h3⟩ := side_chain1 hF hT hk hcell hpat hsep (sig_of_pat hz) k (i + 1) le_rfl (Nat.zero_le _)
          hi1 (by rw [← nb_cellJ, hq, ht, side1_down])
        exact Or.inr (Or.inr ⟨ht', i0, h1, h2, Or.inl h3⟩)
      · exact absurd hT' (beside_end1 hF hT hk hcell hpat hsep
          ((outer1_body hF hcell hpat le_rfl).2 hk) hf hl)
  · by_cases hjk : j ≤ k
    · obtain ⟨ht, i0, -, h1, h2, h3⟩ := side_chain2 hF hT hk hcell hpat hsep (sig_of_pat hz) j i hjk (Nat.zero_le _) hi hq
      exact Or.inr (Or.inr ⟨ht, i0, h1, h2, Or.inr h3⟩)
    · obtain rfl : j = k + 1 := by omega
      rcases touch_side2_end hF hk hcell hpat (sig_of_pat hz) (Nat.zero_le _) hi hq with ⟨ht, _, hi1⟩ | ⟨_, hf, hl⟩
      · obtain ⟨ht', i0, -, h1, h2, h3⟩ := side_chain2 hF hT hk hcell hpat hsep (sig_of_pat hz) k (i + 1) le_rfl (Nat.zero_le _)
          hi1 (by rw [← nb_cellJ, hq, ht, side2_down])
        exact Or.inr (Or.inr ⟨ht', i0, h1, h2, Or.inr h3⟩)
      · exact absurd hT' (beside_end2 hF hT hk hcell hpat hsep
          ((outer2_body hF hcell hpat le_rfl).2 hk) hf hl)

-- Cells of `a` before the end cell are not alternating.
--
omit hs x0 hconn hF hT hcell hsep hT' hz in
lemma body_not_alt {j : ℕ} (hj : j ≤ k) {tw : Side} (l1 : lat1 (cellJ c s j) tw ∈ F)
    (l2 : lat2 (cellJ c s j) tw ∈ F) (bw : back (cellJ c s j) tw ∉ F)
    (fw : front (cellJ c s j) tw ∉ F) : False := by
  obtain ⟨_, _, ab, af⟩ := strip_sig hpat (show j < k + 2 by omega)
  have := (alt_frame s l1 l2 bw fw).1
  rw [ab, af] at this; omega

omit hs hconn hT' hz in
-- The only alternating cells sharing a side with `a` are the end cell and the cell beyond.
omit x0 in
--
theorem alt_touch {w : Pt} {tw : Side} (l1 : lat1 w tw ∈ F) (l2 : lat2 w tw ∈ F)
    (bw : back w tw ∉ F) (fw : front w tw ∉ F) {j : ℕ} (hj : j < k + 2) {x : Edge}
    (hx1 : x ∈ cellE w) (hx2 : x ∈ cellE (cellJ c s j)) :
    w = cellJ c s (k + 1) ∨ w = nb (cellJ c s (k + 1)) s := by
  have af := alt_frame s l1 l2 bw fw
  have body : ∀ j' ≤ k + 1, w = cellJ c s j' → w = cellJ c s (k + 1) := by
    intro j' hj' hw
    by_cases h : j' = k + 1
    · rw [hw, h]
    · rw [hw] at l1 l2 bw fw
      exact (body_not_alt hk hpat (by omega) l1 l2 bw fw).elim
  rcases touch_cases s hx1 hx2 with hq | hq | hq | hq | hq
  · exact Or.inl (body j (by omega) hq)
  · by_cases hjk : j ≤ k
    · exact Or.inl (body (j + 1) (by omega) (by rw [hq, nb_cellJ]))
    · exact Or.inr (by rw [hq, show j = k + 1 by omega])
  · rcases j with _ | j
    · exfalso
      rw [cellJ_zero] at hq
      have hc0 : IsCell V c := by have := hcell 0 (by omega); rwa [cellJ_zero] at this
      have d1 := back_down hF hT hpat (by omega) hc0 hsep
      have df : front (nb c s.opp) s ∈ F := by rw [front_nb_opp]; exact hpat.1
      rw [← hq] at d1 df
      have := af.2.2; have := af.1; tauto
    · exact Or.inl (body j (by omega) (by rw [hq, cellJ_down]))
  · exfalso
    by_cases hjk : j ≤ k
    · obtain ⟨_, fb, ff⟩ := side1_facts hF hT hk hcell hpat hsep hjk
      rw [← hq] at fb ff
      have := af.1; rw [fb, ff] at this; omega
    · obtain rfl : j = k + 1 := by omega
      have fn : lat2 w s ∈ F := by
        rw [hq, side_lat2]; exact (strip_sig hpat (show k + 1 < k + 2 by omega)).1.2 (by omega)
      have fb : back w s ∈ F := by
        rw [hq, show back (nb (cellJ c s (k + 1)) (latA s)) s = outer1 (cellJ c s k) s by
          rw [← side_back_next, nb_cellJ]]
        exact (outer1_body hF hcell hpat le_rfl).2 hk
      have := af.2.1; have := af.2.2; tauto
  · exfalso
    by_cases hjk : j ≤ k
    · obtain ⟨_, fb, ff⟩ := side2_facts hF hT hk hcell hpat hsep hjk
      rw [← hq] at fb ff
      have := af.1; rw [fb, ff] at this; omega
    · obtain rfl : j = k + 1 := by omega
      have fn : lat1 w s ∈ F := by
        rw [hq, side2_lat1]; exact (strip_sig hpat (show k + 1 < k + 2 by omega)).2.1.2 (by omega)
      have fb : back w s ∈ F := by
        rw [hq, show back (nb (cellJ c s (k + 1)) (latB s)) s = outer2 (cellJ c s k) s by
          rw [outer2_side_nb_next, nb_cellJ]; rfl]
        exact (outer2_body hF hcell hpat le_rfl).2 hk
      have := af.2.1; have := af.2.2; tauto

omit hs hconn in
-- A strip starting across `s` at the cell beyond the end cell, of length at least 2, forces
omit x0 in
-- a dark outer edge at the end cell's front, hence a Type III cell after `a`.
--
theorem beyond_cross (ht : tf = latA s ∨ tf = latB s) (hq : z = nb (cellJ c s (k + 1)) s)
    (hm : 2 ≤ m) : False := by
  set e := cellJ c s (k + 1)
  obtain ⟨_, _, gb, gf⟩ := strip_sig hz (show 0 < m by omega)
  rw [cellJ_zero, hq] at gb gf
  have hfz : front (nb e s) tf ∉ F := fun h => by have := (gf.1 h).2 (by omega); omega
  obtain ⟨a1, a2, _, af⟩ := strip_sig hpat (show k + 1 < k + 2 by omega)
  have l1 : lat1 e s ∈ F := a1.2 (by omega)
  have l2 : lat2 e s ∈ F := a2.2 (by omega)
  have hfe : front e s ∉ F := fun h => by have := (af.1 h).1 (by omega); omega
  have he := hcell (k + 1) le_rfl
  rcases ht with rfl | rfl
  · rw [(frame_latA (nb e s) s).1] at hfz
    have hd := hF.2 _ (corners4 he s).2.2.1
    rw [deg_front1, ind_of_mem l1, ind_of_not_mem hfe, ind_of_not_mem hfz] at hd
    have ho : outer1 e s ∈ F := by by_contra ho; rw [ind_of_not_mem ho] at hd; omega
    have hb := (outer1_body hF hcell hpat le_rfl).2 hk
    exact beside_end1 hF hT hk hcell hpat hsep hb ho
      (end_side_far1 hF hT hk hcell hpat hb ho) hT'
  · rw [(frame_latB (nb e s) s).1] at hfz
    have hd := hF.2 _ (corners4 he s).2.2.2
    rw [deg_front2, ind_of_mem l2, ind_of_not_mem hfe, ind_of_not_mem hfz] at hd
    have ho : outer2 e s ∈ F := by by_contra ho; rw [ind_of_not_mem ho] at hd; omega
    have hb := (outer2_body hF hcell hpat le_rfl).2 hk
    exact beside_end2 hF hT hk hcell hpat hsep hb ho
      (end_side_far2 hF hT hk hcell hpat hb ho) hT'

omit hs hconn hz in
-- An alternating cell `w` other than the end cell and the cell beyond cannot split the end
-- cell's lateral sides (`split_end_t3`).
--
omit x0 in
theorem split_core {w : Pt} {tw : Side} (hw : IsCell V w) (l1 : lat1 w tw ∈ F)
    (l2 : lat2 w tw ∈ F) (bw : back w tw ∉ F) (fw : front w tw ∉ F)
    (hwe : w ≠ cellJ c s (k + 1)) (hwu : w ≠ nb (cellJ c s (k + 1)) s)
    (hsplit : ¬ Conn (flip F w) (back1 (cellJ c s (k + 1)) s) (back2 (cellJ c s (k + 1)) s)) :
    False := by
  have hdisj : ∀ j < k + 2, ∀ x ∈ cellE w, x ∉ cellE (cellJ c s j) := by
    intro j hj x hx1 hx2
    rcases alt_touch hF hT hk hcell hpat hsep l1 l2 bw fw hj hx1 hx2 with h | h
    · exact hwe h
    · exact hwu h
  have hmid : ∀ y, y = lat1 w tw ∨ y = lat2 w tw → y ∈ cellE w := by
    intro y hy; rw [cellE_frame w tw]; rcases hy with rfl | rfl <;> simp
  have hm1 : ¬ IsMid c s k (back1 w tw) := fun hm => by
    obtain ⟨j, hj, hx⟩ := mid_touch hF hpat hcell hm l1 ((ends_lat1 w tw).inc_iff _ |>.2 (Or.inl rfl))
    exact hdisj j hj _ (hmid _ (Or.inl rfl)) hx
  have hm2 : ¬ IsMid c s k (back2 w tw) := fun hm => by
    obtain ⟨j, hj, hx⟩ := mid_touch hF hpat hcell hm l2 ((ends_lat2 w tw).inc_iff _ |>.2 (Or.inl rfl))
    exact hdisj j hj _ (hmid _ (Or.inr rfl)) hx
  exact split_end_t3 hF hT hk hcell hpat hsep hw l1 l2 bw fw hdisj hm1 hm2 hsplit hT'

end classify

end SolidGridHam
