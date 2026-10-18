/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import SolidGridHam.Cycle.Near

@[expose] public section

/-!
# Two stacked alternating cells

Let `e` and `u = nb e s` be alternating cells stacked in direction `s`, both with dark
lateral sides, so that their common side `front e s = back u s` is light. Flipping `e` or
flipping `u` gives the same connections between points other than the two middle corners
`m1 = front1 e s = back1 u s` and `m2 = front2 e s = back2 u s`.

* `series_reduce`: a series reduction. If the only edges of `A` at `m1`, `m2` form a path
  `x – m1 – m2 – y`, and `K` is `A` with that path replaced by one edge `x – y`, then `A`
  and `K` give the same connections between points other than `m1`, `m2`.
* `stacked_split`: both flips reduce to the same edge set `K`.
-/

namespace SolidGridHam

open Finset

/-! ## Series reduction -/

-- Three distinct edges at `z` give degree at least three.
--
lemma three_le_deg {A : Finset Edge} {z : Pt} {g1 g2 g3 : Edge}
    (h1 : g1 ∈ A) (h2 : g2 ∈ A) (h3 : g3 ∈ A)
    (i1 : g1.p = z ∨ g1.q = z) (i2 : g2.p = z ∨ g2.q = z) (i3 : g3.p = z ∨ g3.q = z)
    (n12 : g1 ≠ g2) (n13 : g1 ≠ g3) (n23 : g2 ≠ g3) : 3 ≤ deg A z := by
  have e1 := deg_erase h1 z
  rw [ite_eq_left i1] at e1
  have h2' : g2 ∈ A.erase g1 := Finset.mem_erase.2 ⟨n12.symm, h2⟩
  have e2 := deg_erase h2' z
  rw [ite_eq_left i2] at e2
  have h3' : g3 ∈ (A.erase g1).erase g2 :=
    Finset.mem_erase.2 ⟨n23.symm, Finset.mem_erase.2 ⟨n13.symm, h3⟩⟩
  have := one_le_deg h3' i3
  omega

-- The two ends of an adjacency along an edge are the two ends of the edge.
--
lemma Ends.adj_cases {g : Edge} {s tf u v : Pt} (h : Ends g s tf)
    (huv : (g.p = u ∧ g.q = v) ∨ (g.p = v ∧ g.q = u)) :
    (u = s ∧ v = tf) ∨ (u = tf ∧ v = s) := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases huv with ⟨h3, h4⟩ | ⟨h3, h4⟩
  · exact Or.inl ⟨h3.symm.trans h1, h4.symm.trans h2⟩
  · exact Or.inr ⟨h4.symm.trans h2, h3.symm.trans h1⟩
  · exact Or.inr ⟨h3.symm.trans h1, h4.symm.trans h2⟩
  · exact Or.inl ⟨h4.symm.trans h2, h3.symm.trans h1⟩

-- Two edges sharing the end `m` and differing at the other end are different.
--
lemma Ends.ne_at {g g' : Edge} {x m m' : Pt} (h : Ends g x m) (h' : Ends g' m m')
    (hx : x ≠ m') : g ≠ g' := by
  intro heq
  subst heq
  rcases (h'.inc_iff x).1 ((h.inc_iff x).2 (Or.inl rfl)) with h1 | h1
  · exact h.ne h1
  · exact hx h1

-- **Series reduction.** The edges of `A` at `m1`, `m2` are exactly the path
-- `x – m1 – m2 – y` (edges `a`, `b`, `c`; degree at most two forces this). `K` agrees with
-- `A` away from `m1`, `m2` and has the edge `d = x – y` in place of the path. Then `A` and
-- `K` join the same pairs of points other than `m1`, `m2`.
--
theorem series_reduce {A K : Finset Edge} {m1 m2 x y : Pt} {a b c d : Edge}
    (ha : Ends a x m1) (hb : Ends b m1 m2) (hc : Ends c m2 y) (hd : Ends d x y)
    (aA : a ∈ A) (bA : b ∈ A) (cA : c ∈ A) (dK : d ∈ K)
    (hxm2 : x ≠ m2) (hym1 : y ≠ m1)
    (hdeg1 : deg A m1 ≤ 2) (hdeg2 : deg A m2 ≤ 2)
    (hoff : ∀ g ∈ A, ¬ (g.p = m1 ∨ g.q = m1) → ¬ (g.p = m2 ∨ g.q = m2) → g ∈ K)
    (hK : ∀ g ∈ K, g ∈ A ∨ g = d)
    {p q : Pt} (hp1 : p ≠ m1) (hp2 : p ≠ m2) (hq1 : q ≠ m1) (hq2 : q ≠ m2) :
    Conn A p q ↔ Conn K p q := by
  -- The only edges of `A` at `m1` are `a`, `b`, and at `m2` are `b`, `c`.
  --
  have nab : a ≠ b := ha.ne_at hb hxm2
  have nbc : b ≠ c := fun h => (hc.swap.ne_at hb.swap hym1) h.symm
  have ia1 : a.p = m1 ∨ a.q = m1 := (ha.inc_iff m1).2 (Or.inr rfl)
  have ib1 : b.p = m1 ∨ b.q = m1 := (hb.inc_iff m1).2 (Or.inl rfl)
  have ib2 : b.p = m2 ∨ b.q = m2 := (hb.inc_iff m2).2 (Or.inr rfl)
  have ic2 : c.p = m2 ∨ c.q = m2 := (hc.inc_iff m2).2 (Or.inl rfl)
  have hinc : ∀ g ∈ A, ((g.p = m1 ∨ g.q = m1) ∨ (g.p = m2 ∨ g.q = m2)) →
      g = a ∨ g = b ∨ g = c := by
    intro g hg hi
    by_contra hn
    simp only [not_or] at hn
    obtain ⟨na, nb', nc⟩ := hn
    rcases hi with hi | hi
    · have := three_le_deg aA bA hg ia1 ib1 hi nab (Ne.symm na) (Ne.symm nb')
      omega
    · have := three_le_deg bA cA hg ib2 ic2 hi nbc (Ne.symm nb') (Ne.symm nc)
      omega
  constructor
  · -- Collapse `m1`, `m2` onto `x`.
    --
    intro h
    let φ : Pt → Pt := fun z => if z = m1 ∨ z = m2 then x else z
    have φx : φ x = x := by simp only [φ]; split_ifs <;> rfl
    have φ1 : φ m1 = x := by simp [φ]
    have φ2 : φ m2 = x := by simp [φ]
    have φy : φ y = y := by
      simp only [φ]; rw [ite_eq_right (not_or.2 ⟨hym1, hc.ne.symm⟩)]
    have φz : ∀ z, z ≠ m1 → z ≠ m2 → φ z = z := fun z h1 h2 => by
      simp only [φ]; rw [ite_eq_right (not_or.2 ⟨h1, h2⟩)]
    have step : ∀ u v, Adj A u v → Conn K (φ u) (φ v) := by
      intro u v huv
      obtain ⟨g, hg, huv⟩ := huv
      -- An edge of the path, with ends `s`, `t` already joined after collapsing.
      --
      have via : ∀ {s tf : Pt}, Ends g s tf → Conn K (φ s) (φ tf) → Conn K (φ u) (φ v) := by
        intro s tf hst hc'
        rcases hst.adj_cases huv with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h1, h2]; exact hc'
        · rw [h1, h2]; exact hc'.symm
      by_cases hi : (g.p = m1 ∨ g.q = m1) ∨ (g.p = m2 ∨ g.q = m2)
      · rcases hinc g hg hi with rfl | rfl | rfl
        · apply via ha; rw [φx, φ1]; exact Conn.refl _ _
        · apply via hb; rw [φ1, φ2]; exact Conn.refl _ _
        · apply via hc; rw [φ2, φy]; exact hd.conn dK
      · simp only [not_or] at hi
        obtain ⟨⟨n1, n2⟩, n3, n4⟩ := hi
        have hgK := hoff g hg (by rw [not_or]; exact ⟨n1, n2⟩) (by rw [not_or]; exact ⟨n3, n4⟩)
        have hu : u ≠ m1 ∧ u ≠ m2 := by
          rcases huv with ⟨h1, _⟩ | ⟨_, h2⟩
          · rw [← h1]; exact ⟨n1, n3⟩
          · rw [← h2]; exact ⟨n2, n4⟩
        have hv : v ≠ m1 ∧ v ≠ m2 := by
          rcases huv with ⟨_, h2⟩ | ⟨h1, _⟩
          · rw [← h2]; exact ⟨n2, n4⟩
          · rw [← h1]; exact ⟨n1, n3⟩
        rw [φz u hu.1 hu.2, φz v hv.1 hv.2]
        exact Conn.of_adj ⟨g, hgK, huv⟩
    have := conn_map φ step h
    rwa [φz p hp1 hp2, φz q hq1 hq2] at this
  · -- Each edge of `K` is an edge of `A`, or `d`, whose ends are joined along the path.
    --
    intro h
    have hxy : Conn A x y := ((ha.conn aA).trans (hb.conn bA)).trans (hc.conn cA)
    refine conn_map (fun z => z) (fun u v huv => ?_) h
    obtain ⟨g, hg, huv⟩ := huv
    rcases hK g hg with hgA | rfl
    · exact Conn.of_adj ⟨g, hgA, huv⟩
    · rcases hd.adj_cases huv with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]; exact hxy
      · rw [h1, h2]; exact hxy.symm

/-! ## Geometry of two stacked cells -/

section geo

variable (c : Pt) (s : Side)

lemma mem_cellE_frame (g : Edge) :
    g ∈ cellE c ↔ g = back c s ∨ g = front c s ∨ g = lat1 c s ∨ g = lat2 c s := by
  rw [cellE_frame c s]; simp only [Finset.mem_insert, Finset.mem_singleton]

lemma stk_lat1_up : lat1 (nb c s) s ∉ cellE c := by
  obtain ⟨x, y⟩ := c
  cases s <;> simp only [cellE, lat1, nb, bot, top, lft, rgt, Finset.mem_insert,
    Finset.mem_singleton, Edge.mk.injEq, Prod.mk.injEq, reduceCtorEq, true_and, and_true,
    false_and, or_false, false_or] <;> omega

lemma stk_lat2_up : lat2 (nb c s) s ∉ cellE c := by
  obtain ⟨x, y⟩ := c
  cases s <;> simp only [cellE, lat2, nb, bot, top, lft, rgt, Finset.mem_insert,
    Finset.mem_singleton, Edge.mk.injEq, Prod.mk.injEq, reduceCtorEq, true_and, and_true,
    false_and, or_false, false_or] <;> omega

lemma stk_front_up : front (nb c s) s ∉ cellE c := by
  obtain ⟨x, y⟩ := c
  cases s <;> simp only [cellE, front, sideEdge, nb, bot, top, lft, rgt, Finset.mem_insert,
    Finset.mem_singleton, Edge.mk.injEq, Prod.mk.injEq, reduceCtorEq, true_and, and_true,
    false_and, or_false, false_or] <;> omega

lemma stk_lat1_dn : lat1 c s ∉ cellE (nb c s) := by
  obtain ⟨x, y⟩ := c
  cases s <;> simp only [cellE, lat1, nb, bot, top, lft, rgt, Finset.mem_insert,
    Finset.mem_singleton, Edge.mk.injEq, Prod.mk.injEq, reduceCtorEq, true_and, and_true,
    false_and, or_false, false_or] <;> omega

lemma stk_lat2_dn : lat2 c s ∉ cellE (nb c s) := by
  obtain ⟨x, y⟩ := c
  cases s <;> simp only [cellE, lat2, nb, bot, top, lft, rgt, Finset.mem_insert,
    Finset.mem_singleton, Edge.mk.injEq, Prod.mk.injEq, reduceCtorEq, true_and, and_true,
    false_and, or_false, false_or] <;> omega

lemma stk_back_dn : back c s ∉ cellE (nb c s) := by
  obtain ⟨x, y⟩ := c
  cases s <;> simp only [cellE, back, sideEdge, Side.opp, nb, bot, top, lft, rgt,
    Finset.mem_insert, Finset.mem_singleton, Edge.mk.injEq, Prod.mk.injEq,
    reduceCtorEq, true_and, and_true, false_and, or_false, false_or] <;> omega

lemma stk_front_mem : front c s ∈ cellE (nb c s) := by
  rw [mem_cellE_frame (nb c s) s _, back_nb]; exact Or.inl rfl

lemma stk_f1_f2 : front1 (nb c s) s ≠ front2 c s := by
  obtain ⟨x, y⟩ := c
  cases s <;> simp only [front1, front2, nb, ne_eq, Prod.mk.injEq] <;> omega

lemma stk_f2_f1 : front2 (nb c s) s ≠ front1 c s := by
  obtain ⟨x, y⟩ := c
  cases s <;> simp only [front1, front2, nb, ne_eq, Prod.mk.injEq] <;> omega

lemma stk_b1_f2 : back1 c s ≠ front2 c s := by
  obtain ⟨x, y⟩ := c
  cases s <;> simp only [back1, front2, ne_eq, Prod.mk.injEq] <;> omega

lemma stk_b2_f1 : back2 c s ≠ front1 c s := by
  obtain ⟨x, y⟩ := c
  cases s <;> simp only [back2, front1, ne_eq, Prod.mk.injEq] <;> omega

end geo

/-! ## Stacked cells -/

-- Two stacked alternating cells with dark laterals and a light common side: flipping either
-- gives the same connections away from the two middle corners.
--
theorem stacked_split {V : Finset Pt} {F : Finset Edge} (hF : Deg2 V F) {e : Pt} {s : Side}
    (he : IsCell V e) (hu : IsCell V (nb e s))
    (el1 : lat1 e s ∈ F) (el2 : lat2 e s ∈ F) (eb : back e s ∉ F) (ef : front e s ∉ F)
    (ul1 : lat1 (nb e s) s ∈ F) (ul2 : lat2 (nb e s) s ∈ F) (uf : front (nb e s) s ∉ F)
    {p q : Pt} (hp1 : p ≠ front1 e s) (hp2 : p ≠ front2 e s)
    (hq1 : q ≠ front1 e s) (hq2 : q ≠ front2 e s) :
    Conn (flip F e) p q ↔ Conn (flip F (nb e s)) p q := by
  set u := nb e s with hu_def
  set m1 := front1 e s
  set m2 := front2 e s
  have hb1 : back1 u s = m1 := back1_nb e s
  have hb2 : back2 u s = m2 := back2_nb e s
  have hbk : back u s = front e s := back_nb e s
  have ub : back u s ∉ F := by rw [hbk]; exact ef
  obtain ⟨_, _, vm1, vm2⟩ := isCell_corners he s
  have hFe : Deg2 V (flip F e) := hF.flip (mkLat e s) he (mkLat_cellE e s) el1 el2 eb ef
  have hFu : Deg2 V (flip F u) := hF.flip (mkLat u s) hu (mkLat_cellE u s) ul1 ul2 ub uf
  -- The common reduced edge set.
  --
  set K : Finset Edge :=
    (F \ {lat1 e s, lat2 e s, lat1 u s, lat2 u s}) ∪ {back e s, front u s} with hK_def
  have memK : ∀ g, g ∈ K ↔
      (g ∈ F ∧ ¬ (g = lat1 e s ∨ g = lat2 e s ∨ g = lat1 u s ∨ g = lat2 u s)) ∨
        (g = back e s ∨ g = front u s) := by
    intro g
    simp only [K, Finset.mem_union, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
  -- Ends of the edges involved.
  --
  have eL1u : Ends (lat1 u s) m1 (front1 u s) := by
    have := ends_lat1 u s; rwa [hb1] at this
  have eL2u : Ends (lat2 u s) m2 (front2 u s) := by
    have := ends_lat2 u s; rwa [hb2] at this
  have eFe : Ends (front e s) m1 m2 := ends_front e s
  have eFu : Ends (front u s) (front1 u s) (front2 u s) := ends_front u s
  have eL1e : Ends (lat1 e s) (back1 e s) m1 := ends_lat1 e s
  have eL2e : Ends (lat2 e s) (back2 e s) m2 := ends_lat2 e s
  have eBe : Ends (back e s) (back1 e s) (back2 e s) := ends_back e s
  have i1 : ∀ {g : Edge} {x y : Pt}, Ends g x y → (g.p = x ∨ g.q = x) :=
    fun h => (h.inc_iff _).2 (Or.inl rfl)
  have i2 : ∀ {g : Edge} {x y : Pt}, Ends g x y → (g.p = y ∨ g.q = y) :=
    fun h => (h.inc_iff _).2 (Or.inr rfl)
  have ceE := mem_cellE_frame e s
  have ceU := mem_cellE_frame u s
  have l1e_e : lat1 e s ∈ cellE e := (ceE _).2 (Or.inr (Or.inr (Or.inl rfl)))
  have l2e_e : lat2 e s ∈ cellE e := (ceE _).2 (Or.inr (Or.inr (Or.inr rfl)))
  have l1u_u : lat1 u s ∈ cellE u := (ceU _).2 (Or.inr (Or.inr (Or.inl rfl)))
  have l2u_u : lat2 u s ∈ cellE u := (ceU _).2 (Or.inr (Or.inr (Or.inr rfl)))
  have fe_e : front e s ∈ cellE e := (ceE _).2 (Or.inr (Or.inl rfl))
  have be_e : back e s ∈ cellE e := (ceE _).2 (Or.inl rfl)
  have fu_u : front u s ∈ cellE u := (ceU _).2 (Or.inr (Or.inl rfl))
  have fe_u : front e s ∈ cellE u := stk_front_mem e s
  -- Reduce `flip F e` to `K`: the path `front1 u – m1 – m2 – front2 u`, shortcut `front u`.
  --
  have redE : Conn (flip F e) p q ↔ Conn K p q := by
    refine series_reduce eL1u.swap eFe eL2u eFu ?_ ?_ ?_ ?_ (stk_f1_f2 e s) (stk_f2_f1 e s)
      (hFe.le_two _) (hFe.le_two _) ?_ ?_ hp1 hp2 hq1 hq2
    · exact mem_flip_iff.2 ⟨fun _ => stk_lat1_up e s, fun _ => ul1⟩
    · exact mem_flip_iff.2 ⟨fun h => absurd h ef, fun h => absurd fe_e h⟩
    · exact mem_flip_iff.2 ⟨fun _ => stk_lat2_up e s, fun _ => ul2⟩
    · exact (memK _).2 (Or.inr (Or.inr rfl))
    · intro g hg n1 n2
      rw [mem_flip_iff] at hg
      by_cases hgF : g ∈ F
      · have hgc := hg.1 hgF
        refine (memK g).2 (Or.inl ⟨hgF, ?_⟩)
        rintro (rfl | rfl | rfl | rfl)
        · exact hgc l1e_e
        · exact hgc l2e_e
        · exact n1 (i1 eL1u)
        · exact n2 (i1 eL2u)
      · have hgc : g ∈ cellE e := by by_contra h; exact hgF (hg.2 h)
        rcases (ceE _).1 hgc with rfl | rfl | rfl | rfl
        · exact (memK _).2 (Or.inr (Or.inl rfl))
        · exact absurd (i1 eFe) n1
        · exact absurd el1 hgF
        · exact absurd el2 hgF
    · intro g hg
      rcases (memK g).1 hg with ⟨hgF, hn⟩ | rfl | rfl
      · left
        refine mem_flip_iff.2 ⟨fun _ hgc => ?_, fun _ => hgF⟩
        rcases (ceE _).1 hgc with rfl | rfl | rfl | rfl
        · exact eb hgF
        · exact ef hgF
        · exact hn (Or.inl rfl)
        · exact hn (Or.inr (Or.inl rfl))
      · left
        exact mem_flip_iff.2 ⟨fun h => absurd h eb, fun h => absurd be_e h⟩
      · right; rfl
  -- Reduce `flip F u` to `K`: the path `back1 e – m1 – m2 – back2 e`, shortcut `back e`.
  --
  have redU : Conn (flip F u) p q ↔ Conn K p q := by
    refine series_reduce eL1e eFe eL2e.swap eBe ?_ ?_ ?_ ?_ (stk_b1_f2 e s) (stk_b2_f1 e s)
      (hFu.le_two _) (hFu.le_two _) ?_ ?_ hp1 hp2 hq1 hq2
    · exact mem_flip_iff.2 ⟨fun _ => stk_lat1_dn e s, fun _ => el1⟩
    · exact mem_flip_iff.2 ⟨fun h => absurd h ef, fun h => absurd fe_u h⟩
    · exact mem_flip_iff.2 ⟨fun _ => stk_lat2_dn e s, fun _ => el2⟩
    · exact (memK _).2 (Or.inr (Or.inl rfl))
    · intro g hg n1 n2
      rw [mem_flip_iff] at hg
      by_cases hgF : g ∈ F
      · have hgc := hg.1 hgF
        refine (memK g).2 (Or.inl ⟨hgF, ?_⟩)
        rintro (rfl | rfl | rfl | rfl)
        · exact n1 (i2 eL1e)
        · exact n2 (i2 eL2e)
        · exact hgc l1u_u
        · exact hgc l2u_u
      · have hgc : g ∈ cellE u := by by_contra h; exact hgF (hg.2 h)
        rcases (ceU _).1 hgc with rfl | rfl | rfl | rfl
        · rw [hbk] at n1; exact absurd (i1 eFe) n1
        · exact (memK _).2 (Or.inr (Or.inr rfl))
        · exact absurd ul1 hgF
        · exact absurd ul2 hgF
    · intro g hg
      rcases (memK g).1 hg with ⟨hgF, hn⟩ | rfl | rfl
      · left
        refine mem_flip_iff.2 ⟨fun _ hgc => ?_, fun _ => hgF⟩
        rcases (ceU _).1 hgc with rfl | rfl | rfl | rfl
        · exact ub hgF
        · exact uf hgF
        · exact hn (Or.inr (Or.inr (Or.inl rfl)))
        · exact hn (Or.inr (Or.inr (Or.inr rfl)))
      · right; rfl
      · left
        exact mem_flip_iff.2 ⟨fun h => absurd h uf, fun h => absurd fu_u h⟩
  rw [redE, redU]

end SolidGridHam
