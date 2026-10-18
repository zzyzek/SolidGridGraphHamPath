/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.HP.WalkT
import ULHC.HP.TheoremAPF

/-!
# A start for the walk that avoids a Type III cell at `t` (notes P23)

The walk starts at a cell `v` across a cut edge `e` of `H` (cut by `t`'s class of `F`) and needs
a dark side of `v` next to `e`. If there is none, degree 2 at `v`'s corners forces the cell `r`
across `e` to have both sides perpendicular to `e` in `F`; then `r` is Type III, so (all other
Type III cells being gone) it has `t` as a corner, and its side through `t` is `t`'s edge, which
ends at an end `b1` of `e`. A second cut edge `e' ≠ e` exists (handshake: `s` and `t` both lie
in `t`'s class). If `e'` were bad too, uniqueness of `t`'s edge gives the same `b1`, and `b1`
would have three edges of `H`: `e`, `e'` and `t`'s edge.
-/

namespace ULHC

open Finset Classical

namespace HP

lemma notTypeIII_of_not_cell {V : Finset Pt} {F : Finset Edge} (hIn : Inside V F) {c : Pt}
    (hc : ¬ IsCell V c) : NotTypeIII V F c := by
  intro s hb hf _ _
  exfalso; apply hc
  have h1 := hIn _ hb
  have h2 := hIn _ hf
  have eb : Ends (back c s) (back1 c s) (back2 c s) := ends_back c s
  have ef : Ends (front c s) (front1 c s) (front2 c s) := ends_front c s
  have k1 : back1 c s ∈ V ∧ back2 c s ∈ V := by
    rcases eb with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> rw [a1, a2] at h1 <;> tauto
  have k2 : front1 c s ∈ V ∧ front2 c s ∈ V := by
    rcases ef with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> rw [a1, a2] at h2 <;> tauto
  exact isCell_of_corners c s k1.1 k1.2 k2.1 k2.2

-- No dark side next to side `s` of a degree-2 cell forces both sides of the next cell
-- perpendicular to `s`.
--
lemma lats_of_no_dark {F : Finset Edge} {w : Pt} (hw2 : Deg2Cell F w) (s : Side)
    (hfr : sideEdge w s ∉ F) (hn : ¬ (sideEdge w (latA s) ∈ F ∨ sideEdge w (latB s) ∈ F)) :
    lat1 (nb w s) s ∈ F ∧ lat2 (nb w s) s ∈ F := by
  push Not at hn
  obtain ⟨n1, n2⟩ := hn
  rw [← lat1_eq] at n1
  rw [← lat2_eq] at n2
  have hfr' : front w s ∉ F := hfr
  have d1 := deg_front1 w s F
  have d2 := deg_front2 w s F
  rw [deg2_front1 hw2 s] at d1
  rw [deg2_front2 hw2 s] at d2
  have i1 : ind F (lat1 w s) = 0 := by simp [ind, n1]
  have i2 : ind F (lat2 w s) = 0 := by simp [ind, n2]
  have i3 : ind F (front w s) = 0 := by simp [ind, hfr']
  have mem1 : ∀ e, ind F e = 1 → e ∈ F := by
    intro e h; unfold ind at h; split_ifs at h with h'; exact h'
  rw [i1, i3] at d1
  rw [i2, i3] at d2
  refine ⟨?_, ?_⟩
  · have := ind_le_one F (lat1 (nb w s) s)
    have := ind_le_one F (outer1 w s)
    exact mem1 _ (by omega)
  · have := ind_le_one F (lat2 (nb w s) s)
    have := ind_le_one F (outer2 w s)
    exact mem1 _ (by omega)

lemma corner_cases_side {t r : Pt} (h : IsCorner t r) (s : Side) :
    t = back1 r s ∨ t = back2 r s ∨ t = front1 r s ∨ t = front2 r s := by
  obtain ⟨x, y⟩ := r
  unfold IsCorner at h
  dsimp only at h
  cases s <;> simp only [back1, back2, front1, front2] <;> tauto

-- F and H use the same edges at `t` when `D` vanishes on `t`'s cells.
--
lemma agree_at {V : Finset Pt} {d : Pt → ℕ} {F H : Finset Edge} (hF : IsFactor V d F)
    (hH : IsFactor V d H) {t : Pt} (hz : ∀ w, IsCorner t w → D F H w = 0) {g : Edge}
    (hg : g.p = t ∨ g.q = t) : g ∈ F ↔ g ∈ H := by
  have hj := D_jump hF hH g
  have hc : IsCorner t g.hi ∧ IsCorner t g.lo := by
    obtain ⟨dd, ⟨p1, p2⟩⟩ := g
    obtain ⟨x, y⟩ := t
    cases dd <;> rcases hg with h | h <;>
      simp only [Edge.q, Edge.hi, Edge.lo, IsCorner, Prod.mk.injEq] at h ⊢ <;> omega
  rw [hz _ hc.1, hz _ hc.2] at hj
  unfold wD wb at hj
  by_cases a : g ∈ F <;> by_cases b : g ∈ H <;> simp [a, b] at hj ⊢ <;> split_ifs at hj <;> omega

lemma three_le_deg {H : Finset Edge} {b : Pt} {e1 e2 e3 : Edge} (h1 : e1 ∈ H) (h2 : e2 ∈ H)
    (h3 : e3 ∈ H) (i1 : e1.p = b ∨ e1.q = b) (i2 : e2.p = b ∨ e2.q = b)
    (i3 : e3.p = b ∨ e3.q = b) (n12 : e1 ≠ e2) (n13 : e1 ≠ e3) (n23 : e2 ≠ e3) :
    3 ≤ deg H b := by
  have a := deg_erase h1 b
  have h2' : e2 ∈ H.erase e1 := Finset.mem_erase.2 ⟨n12.symm, h2⟩
  have b' := deg_erase h2' b
  have h3' : e3 ∈ (H.erase e1).erase e2 :=
    Finset.mem_erase.2 ⟨n23.symm, Finset.mem_erase.2 ⟨n13.symm, h3⟩⟩
  have c := deg_erase h3' b
  simp only [i1, ite_true] at a
  simp only [i2, ite_true] at b'
  simp only [i3, ite_true] at c
  omega

-- A sum of `if x = a then 1 else 2` over a set containing `a` is odd.
--
lemma odd_sum {K : Finset Pt} {a : Pt} (ha : a ∈ K) :
    ¬ Even (∑ x ∈ K, (if x = a then 1 else 2)) := by
  rw [← Finset.add_sum_erase _ _ ha]
  have : ∑ x ∈ K.erase a, (if x = a then 1 else 2) = ∑ x ∈ K.erase a, 2 :=
    Finset.sum_congr rfl (fun x hx => by simp [Finset.ne_of_mem_erase hx])
  rw [this, Finset.sum_const, smul_eq_mul]
  simp only [ite_true]
  rintro ⟨k, hk⟩
  omega

-- `s` lies in `t`'s class of a path-factor.
--
lemma conn_t_s {V : Finset Pt} {d : Pt → ℕ} {F : Finset Edge} (hF : IsFactor V d F) {s t : Pt}
    (hd : ∀ z, z ≠ s → z ≠ t → d z = 2) (hdt : d t = 1) (htV : t ∈ V) : Conn F t s := by
  by_contra hn
  have hK := handshake (closed_cls (Inside.of_factor hF) t)
  have hsum : ∑ x ∈ cls V F t, deg F x = ∑ x ∈ cls V F t, (if x = t then 1 else 2) := by
    apply Finset.sum_congr rfl; intro x hx
    have hxV : x ∈ V := (Finset.mem_filter.1 hx).1
    rw [hF.2 x hxV]
    by_cases hxt : x = t
    · subst hxt; simp [hdt]
    · have hxs : x ≠ s := by rintro rfl; exact hn (Finset.mem_filter.1 hx).2
      simp [hxt, hd x hxs hxt]
  rw [hsum] at hK
  exact odd_sum (mem_cls_self htV) hK

-- A second cut edge of `H`, when `e` joins `b1` (in `P`, joined to `t` without `e`) to `b2`.
--
lemma second_cut {V : Finset Pt} {d : Pt → ℕ} {H : Finset Edge} (hH : IsFactor V d H)
    {s t : Pt} (hd : ∀ z, z ≠ s → z ≠ t → d z = 2) {P : Finset Pt} {e : Edge} (he : e ∈ H)
    {b1 b2 : Pt} (hend : Ends e b1 b2) (hb1 : b1 ∈ P) (hb2 : b2 ∉ P) (hb2V : b2 ∈ V)
    (hdb2 : d b2 = 2) (hsP : s ∈ P) (htb : Conn (H.erase e) t b1) :
    ∃ e' ∈ H, e' ≠ e ∧ Cut P e' := by
  by_cases hc : Conn (H.erase e) b1 b2
  · obtain ⟨e', he', hcut⟩ := exists_cut_edge hc hb1 hb2
    exact ⟨e', (Finset.mem_erase.1 he').2, (Finset.mem_erase.1 he').1, hcut⟩
  · have hIn : Inside V (H.erase e) := (Inside.of_factor hH).mono (Finset.erase_subset _ _)
    have hs2 : Conn (H.erase e) b2 s := by
      by_contra hn
      have hK := handshake (closed_cls hIn b2)
      have hsum : ∑ x ∈ cls V (H.erase e) b2, deg (H.erase e) x =
          ∑ x ∈ cls V (H.erase e) b2, (if x = b2 then 1 else 2) := by
        apply Finset.sum_congr rfl; intro x hx
        have hxV : x ∈ V := (Finset.mem_filter.1 hx).1
        have hbx : Conn (H.erase e) b2 x := (Finset.mem_filter.1 hx).2
        have hx1 : x ≠ b1 := by rintro rfl; exact hc hbx.symm
        have hxt : x ≠ t := by rintro rfl; exact hc (hbx.trans htb).symm
        have hxs : x ≠ s := by rintro rfl; exact hn hbx
        have := hend.deg_erase he x
        rw [hH.2 x hxV] at this
        by_cases hx2 : x = b2
        · subst hx2; simp only [or_true, ite_true] at this; rw [hdb2] at this; simp; omega
        · simp only [hx1, hx2, or_self, ite_false, add_zero] at this
          rw [this, hd x hxs hxt]; simp [hx2]
      rw [hsum] at hK
      exact odd_sum (mem_cls_self hb2V) hK
    obtain ⟨e', he', hcut⟩ := exists_cut_edge hs2.symm hsP hb2
    exact ⟨e', (Finset.mem_erase.1 he').2, (Finset.mem_erase.1 he').1, hcut⟩

-- **The shape of a bad start.** With no dark side of `v` next to the cut side `s0`, the cell
-- across is Type III, so it has `t` as a corner, and `t`'s edge ends at an end of that side.
--
lemma bad_shape {V : Finset Pt} {F : Finset Edge} (hIn : Inside V F) {s t : Pt}
    (hsfree : ∀ w, IsCorner s w → ¬ IsCell V w)
    (hfar : ∀ c, IsCell V c → ¬ IsCorner s c → ¬ IsCorner t c → NotTypeIII V F c)
    (hdt : deg F t = 1) {P : Finset Pt} (hB : Border V F P)
    {v : Pt} (hv : IsCell V v) (hv2 : Deg2Cell F v) (s0 : Side) (hcut : Cut P (sideEdge v s0))
    (hn : ¬ (sideEdge v (latA s0) ∈ F ∨ sideEdge v (latB s0) ∈ F)) :
    ∃ g ∈ F, ∃ b, Ends g t b ∧ (b = front1 v s0 ∨ b = front2 v s0) := by
  have hT : ¬ NotTypeIII V F (nb v s0) := fun h => hn (cut_has_dark_lat_r hIn hB hv hv2 s0 h hcut)
  have hrc : IsCell V (nb v s0) := by
    by_contra h; exact hT (notTypeIII_of_not_cell hIn h)
  have htr : IsCorner t (nb v s0) := by
    by_contra h1
    by_cases h2 : IsCorner s (nb v s0)
    · exact hsfree _ h2 hrc
    · exact hT (hfar _ hrc h2 h1)
  have hfr : sideEdge v s0 ∉ F := fun h => hB.not_cut h hcut
  obtain ⟨l1, l2⟩ := lats_of_no_dark hv2 s0 hfr hn
  have dt1 : t ≠ front1 v s0 := by
    intro h; have := deg2_front1 hv2 s0; rw [← h] at this; omega
  have dt2 : t ≠ front2 v s0 := by
    intro h; have := deg2_front2 hv2 s0; rw [← h] at this; omega
  rcases corner_cases_side htr s0 with h | h | h | h
  · rw [back1_nb] at h; exact absurd h dt1
  · rw [back2_nb] at h; exact absurd h dt2
  · refine ⟨lat1 (nb v s0) s0, l1, front1 v s0, ?_, Or.inl rfl⟩
    have e1 : Ends (lat1 (nb v s0) s0) (back1 (nb v s0) s0) (front1 (nb v s0) s0) :=
      ends_lat1 _ _
    rw [← h, back1_nb] at e1; exact e1.swap
  · refine ⟨lat2 (nb v s0) s0, l2, front2 v s0, ?_, Or.inr rfl⟩
    have e1 : Ends (lat2 (nb v s0) s0) (back2 (nb v s0) s0) (front2 (nb v s0) s0) :=
      ends_lat2 _ _
    rw [← h, back2_nb] at e1; exact e1.swap

-- The walk's start at a cut edge of `H`: orientation from the sign of `D` at the arc's tail.
--
lemma key_of_edge {V : Finset Pt} {d : Pt → ℕ} {F H : Finset Edge} (hF : IsFactor V d F)
    (hH : IsFactor V d H) {P : Finset Pt} (hB : Border V F P) {e : Edge} (heH : e ∈ H)
    (hcut : Cut P e) :
    ∃ o v s0, sideEdge v s0 = e ∧ outArc F v s0 = !o ∧
      (if o then D F H v = D F H (nb v s0) + 2 else D F H v = D F H (nb v s0) - 2) ∧
      Good o (D F H v) := by
  have heF : e ∉ F := fun h => hB.not_cut h hcut
  obtain ⟨sh, sl, h1, h2', h3, h4, h5, h6⟩ := edge_cells F e
  have hjump := D_jump hF hH e
  have hw : wD F H e = if up F e then 2 else -2 := by
    unfold wD wb; simp [heF, heH]
  rw [hw] at hjump
  obtain ⟨a, b, sa, sb, ha1, ha2, ha3, hb1, hb2, hb3, hD⟩ :
      ∃ a b sa sb, sideEdge a sa = e ∧ nb a sa = b ∧ outArc F a sa = true ∧
        sideEdge b sb = e ∧ nb b sb = a ∧ outArc F b sb = false ∧
        D F H b = D F H a + 2 := by
    cases hu : up F e
    · refine ⟨e.hi, e.lo, sh, sl, h1, h2', by rw [h3, hu]; rfl, h4, h5, by rw [h6, hu], ?_⟩
      rw [hu] at hjump; simp at hjump; omega
    · refine ⟨e.lo, e.hi, sl, sh, h4, h5, by rw [h6, hu], h1, h2', by rw [h3, hu]; rfl, ?_⟩
      rw [hu] at hjump; simp at hjump; omega
  by_cases hpos : 0 ≤ D F H a
  · refine ⟨true, b, sb, hb1, by rw [hb3]; rfl, ?_, ?_⟩
    · simp only [ite_true]; rw [hb2]; exact hD
    · unfold Good; simp; omega
  · obtain ⟨m, hm⟩ := D_even F H a
    refine ⟨false, a, sa, ha1, by rw [ha3]; rfl, ?_, ?_⟩
    · simp only [Bool.false_eq_true, ite_false]; rw [ha2]; omega
    · unfold Good; simp; omega

-- **A good start.** With `D = 0` on the endpoints' cells, no cell at `s`, and no Type III cell
-- away from the endpoints, some cut edge of `H` (cut by `t`'s class) gives a start with a dark
-- side next to the entry side.
--
theorem good_start {V : Finset Pt} {d : Pt → ℕ} {F H : Finset Edge} (hs : Solid V)
    (hF : IsFactor V d F) (hH : IsFactor V d H) (hHam : ncomp V H = 1) {s t : Pt}
    (hd : ∀ z, z ≠ s → z ≠ t → d z = 2) (hdt : d t = 1) (htV : t ∈ V)
    (hsfree : ∀ w, IsCorner s w → ¬ IsCell V w)
    (hfar : ∀ c, IsCell V c → ¬ IsCorner s c → ¬ IsCorner t c → NotTypeIII V F c)
    (hz : ∀ w, IsCorner s w ∨ IsCorner t w → D F H w = 0) (h2 : 2 ≤ ncomp V F) :
    ∃ o v s0, Cut (cls V F t) (sideEdge v s0) ∧ outArc F v s0 = !o ∧
      (if o then D F H v = D F H (nb v s0) + 2 else D F H v = D F H (nb v s0) - 2) ∧
      Good o (D F H v) ∧ (sideEdge v (latA s0) ∈ F ∨ sideEdge v (latB s0) ∈ F) := by
  set P := cls V F t with hP
  have hIn := Inside.of_factor hF
  have hB : Border V F P := ⟨Finset.filter_subset _ _, fun u hu w hw => closed_cls hIn t u hu w hw⟩
  have hdegt : deg F t = 1 := by rw [hF.2 t htV, hdt]
  have hloc := deg2Cell_of_zero hF hH (SolidFor.of_solid hF hH hs) hd hz
  have memP : ∀ z, z ∈ V → Conn F t z → z ∈ P := fun z hz hc =>
    Finset.mem_filter.2 ⟨hz, hc⟩
  -- A point outside `t`'s class.
  --
  obtain ⟨y, hyV, hyP⟩ : ∃ y ∈ V, y ∉ P := by
    obtain ⟨x, hx, y, hy, hxy⟩ := exists_not_conn h2
    by_cases htx : Conn F t x
    · refine ⟨y, hy, fun h => hxy (htx.symm.trans (Finset.mem_filter.1 h).2)⟩
    · exact ⟨x, hx, fun h => htx (Finset.mem_filter.1 h).2⟩
  have hsP : s ∈ P := by
    have hc := conn_t_s hF hd hdt htV
    have hsV : s ∈ V := conn_mem hIn htV hc
    exact memP s hsV hc
  -- For a bad start, the end `b1` of `t`'s edge on the cut side.
  --
  have bad : ∀ e ∈ H, Cut P e → ∀ o v s0, sideEdge v s0 = e → Good o (D F H v) →
      ¬ (sideEdge v (latA s0) ∈ F ∨ sideEdge v (latB s0) ∈ F) →
      ∃ g ∈ F, ∃ b1 b2, Ends g t b1 ∧ Ends e b1 b2 ∧ b1 ∈ V ∧ b2 ∈ V ∧ d b1 = 2 ∧ d b2 = 2 := by
    intro e _ hcut o v s0 hve hg hn
    have hv := Good.isCell_f (SolidFor.of_solid hF hH hs) hg
    have hv2 := hloc o v hg
    obtain ⟨g, hgF, b, hgb, hb⟩ :=
      bad_shape hIn hsfree hfar hdegt hB hv hv2 s0 (by rw [hve]; exact hcut) hn
    have ef : Ends (front v s0) (front1 v s0) (front2 v s0) := ends_front v s0
    have hfe : front v s0 = e := hve
    rw [hfe] at ef
    obtain ⟨c1, c2, c3, c4⟩ := isCell_corners hv s0
    have d1 : d (front1 v s0) = 2 := by rw [← hF.2 _ c3]; exact deg2_front1 hv2 s0
    have d2 : d (front2 v s0) = 2 := by rw [← hF.2 _ c4]; exact deg2_front2 hv2 s0
    rcases hb with rfl | rfl
    · exact ⟨g, hgF, _, _, hgb, ef, c3, c4, d1, d2⟩
    · exact ⟨g, hgF, _, _, hgb, ef.swap, c4, c3, d2, d1⟩
  obtain ⟨e, heH, hcut⟩ := exists_cut_edge (conn_of_ncomp_one hHam htV hyV)
    (mem_cls_self htV) hyP
  obtain ⟨o, v, s0, hve, hin, hj, hg⟩ := key_of_edge hF hH hB heH hcut
  by_cases hL : sideEdge v (latA s0) ∈ F ∨ sideEdge v (latB s0) ∈ F
  · exact ⟨o, v, s0, by rw [hve]; exact hcut, hin, hj, hg, hL⟩
  obtain ⟨g, hgF, b1, b2, hgb, heb, hb1V, hb2V, hdb1, hdb2⟩ :=
    bad e heH hcut o v s0 hve hg hL
  have heF : e ∉ F := fun h => hB.not_cut h hcut
  have hgH : g ∈ H := (agree_at hF hH (fun w hw => hz w (Or.inr hw))
    ((hgb.inc_iff t).2 (Or.inl rfl))).1 hgF
  have hge : g ≠ e := fun h => heF (h ▸ hgF)
  have hb1P : b1 ∈ P := memP b1 hb1V (hgb.conn hgF)
  have hb2P : b2 ∉ P := by
    intro h2P
    unfold Cut at hcut
    rcases heb with ⟨q1, q2⟩ | ⟨q1, q2⟩ <;> rw [q1, q2] at hcut <;> tauto
  have htb : Conn (H.erase e) t b1 :=
    hgb.conn (Finset.mem_erase.2 ⟨hge, hgH⟩)
  obtain ⟨e', he'H, hne, hcut'⟩ :=
    second_cut hH hd heH heb hb1P hb2P hb2V hdb2 hsP htb
  obtain ⟨o', v', s0', hve', hin', hj', hg'⟩ := key_of_edge hF hH hB he'H hcut'
  by_cases hL' : sideEdge v' (latA s0') ∈ F ∨ sideEdge v' (latB s0') ∈ F
  · exact ⟨o', v', s0', by rw [hve']; exact hcut', hin', hj', hg', hL'⟩
  exfalso
  obtain ⟨g', hg'F, b1', b2', hgb', heb', hb1'V, _, hdb1', _⟩ :=
    bad e' he'H hcut' o' v' s0' hve' hg' hL'
  have hgg : g' = g := inc_unique hdegt hgF ((hgb.inc_iff t).2 (Or.inl rfl)) hg'F
    ((hgb'.inc_iff t).2 (Or.inl rfl))
  rw [hgg] at hgb'
  have hb1t : b1' ≠ t := by intro h; rw [h, hdt] at hdb1'; omega
  have hbb : b1' = b1 := by
    rcases (hgb.inc_iff b1').1 ((hgb'.inc_iff b1').2 (Or.inr rfl)) with h | h
    · exact absurd h hb1t
    · exact h
  rw [hbb] at heb'
  have heF' : e' ∉ F := fun h => hB.not_cut h hcut'
  have h3 := three_le_deg heH he'H hgH ((heb.inc_iff b1).2 (Or.inl rfl))
    ((heb'.inc_iff b1).2 (Or.inl rfl)) ((hgb.inc_iff b1).2 (Or.inr rfl)) hne.symm
    (fun h => heF (h ▸ hgF)) (fun h => heF' (h ▸ hgF))
  rw [hH.2 b1 hb1V, hdb1] at h3
  omega

end HP

end ULHC
