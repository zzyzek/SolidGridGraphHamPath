/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.HP.StartEdge

/-!
# The walk's start with both endpoints in the grid (notes P24)

Without the tail at `s`, a bad start can come from either endpoint: the cell across the cut
edge is Type III with `s` or `t` as a corner, and that endpoint's edge ends on the cut edge.
Two bad edges at the same endpoint are equal (their common end would have three edges of `H`),
so there are at most two, `e1` and `e2`, one per endpoint. If every cut edge of `t`'s class `P`
and of the class `P'` of the far end of `e1` is bad, then no edge of `H` leaves `P ∪ P'`, so `F`
has exactly two components, and flipping the Type III cell joins them into a Hamiltonian path.
-/

namespace ULHC

open Finset Classical

namespace HP

lemma bad_shape2 {V : Finset Pt} {F : Finset Edge} (hIn : Inside V F) {s t : Pt}
    (hfar : ∀ c, IsCell V c → ¬ IsCorner s c → ¬ IsCorner t c → NotTypeIII V F c)
    (hds1 : deg F s = 1) (hdt1 : deg F t = 1) {P : Finset Pt} (hB : Border V F P)
    {v : Pt} (hv : IsCell V v) (hv2 : Deg2Cell F v) (s0 : Side) (hcut : Cut P (sideEdge v s0))
    (hn : ¬ (sideEdge v (latA s0) ∈ F ∨ sideEdge v (latB s0) ∈ F)) :
    IsCell V (nb v s0) ∧ ¬ NotTypeIII V F (nb v s0) ∧
      ∃ z, (z = s ∨ z = t) ∧ ∃ g ∈ F, ∃ b, Ends g z b ∧ (b = front1 v s0 ∨ b = front2 v s0) := by
  have hT : ¬ NotTypeIII V F (nb v s0) := fun h => hn (cut_has_dark_lat_r hIn hB hv hv2 s0 h hcut)
  have hrc : IsCell V (nb v s0) := by
    by_contra h; exact hT (notTypeIII_of_not_cell hIn h)
  obtain ⟨z, hz, hzr⟩ : ∃ z, (z = s ∨ z = t) ∧ IsCorner z (nb v s0) := by
    by_contra h
    push Not at h
    exact hT (hfar _ hrc (h s (Or.inl rfl)) (h t (Or.inr rfl)))
  have hdz : deg F z = 1 := by rcases hz with rfl | rfl <;> assumption
  have hfr : sideEdge v s0 ∉ F := fun h => hB.not_cut h hcut
  obtain ⟨l1, l2⟩ := lats_of_no_dark hv2 s0 hfr hn
  have dt1 : z ≠ front1 v s0 := by
    intro h; have := deg2_front1 hv2 s0; rw [← h] at this; omega
  have dt2 : z ≠ front2 v s0 := by
    intro h; have := deg2_front2 hv2 s0; rw [← h] at this; omega
  refine ⟨hrc, hT, z, hz, ?_⟩
  rcases corner_cases_side hzr s0 with h | h | h | h
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

-- Two bad edges at the same endpoint are equal.
--
lemma bad_same {V : Finset Pt} {d : Pt → ℕ} {F H : Finset Edge} (hH : IsFactor V d H)
    {z : Pt} (hdz : d z = 1) (hzF : deg F z = 1)
    (hag : ∀ g, (g.p = z ∨ g.q = z) → (g ∈ F ↔ g ∈ H))
    {e e' g g' : Edge} {b1 b2 b1' b2' : Pt} (he : e ∈ H) (he' : e' ∈ H) (heF : e ∉ F)
    (heF' : e' ∉ F) (hgF : g ∈ F) (hg'F : g' ∈ F) (hgb : Ends g z b1) (hgb' : Ends g' z b1')
    (heb : Ends e b1 b2) (heb' : Ends e' b1' b2') (hb1V : b1 ∈ V) (hdb1 : d b1 = 2)
    (hdb1' : d b1' = 2) : e = e' := by
  by_contra hne
  have hgH : g ∈ H := (hag g ((hgb.inc_iff z).2 (Or.inl rfl))).1 hgF
  have hgg : g' = g := inc_unique hzF hgF ((hgb.inc_iff z).2 (Or.inl rfl)) hg'F
    ((hgb'.inc_iff z).2 (Or.inl rfl))
  rw [hgg] at hgb'
  have hb1z : b1' ≠ z := by intro h; rw [h, hdz] at hdb1'; omega
  have hbb : b1' = b1 := by
    rcases (hgb.inc_iff b1').1 ((hgb'.inc_iff b1').2 (Or.inr rfl)) with h | h
    · exact absurd h hb1z
    · exact h
  rw [hbb] at heb'
  have h3 := three_le_deg he he' hgH ((heb.inc_iff b1).2 (Or.inl rfl))
    ((heb'.inc_iff b1).2 (Or.inl rfl)) ((hgb.inc_iff b1).2 (Or.inr rfl)) hne
    (fun h => heF (h ▸ hgF)) (fun h => heF' (h ▸ hgF))
  rw [hH.2 b1 hb1V, hdb1] at h3
  omega

-- If erasing `e` separates its ends, the far end's piece holds an endpoint (handshake).
--
lemma split_or_conn {V : Finset Pt} {d : Pt → ℕ} {H : Finset Edge} (hH : IsFactor V d H)
    {s t : Pt} (hd : ∀ z, z ≠ s → z ≠ t → d z = 2) {e : Edge} (he : e ∈ H)
    {b1 b2 : Pt} (hend : Ends e b1 b2) (hb2V : b2 ∈ V) (hdb2 : d b2 = 2)
    (hnc : ¬ Conn (H.erase e) b1 b2) : Conn (H.erase e) b2 s ∨ Conn (H.erase e) b2 t := by
  by_contra hn
  push Not at hn
  have hIn : Inside V (H.erase e) := (Inside.of_factor hH).mono (Finset.erase_subset _ _)
  have hK := handshake (closed_cls hIn b2)
  have hsum : ∑ x ∈ cls V (H.erase e) b2, deg (H.erase e) x =
      ∑ x ∈ cls V (H.erase e) b2, (if x = b2 then 1 else 2) := by
    apply Finset.sum_congr rfl; intro x hx
    have hxV : x ∈ V := (Finset.mem_filter.1 hx).1
    have hbx : Conn (H.erase e) b2 x := (Finset.mem_filter.1 hx).2
    have hx1 : x ≠ b1 := by rintro rfl; exact hnc hbx.symm
    have hxs : x ≠ s := by rintro rfl; exact hn.1 hbx
    have hxt : x ≠ t := by rintro rfl; exact hn.2 hbx
    have := hend.deg_erase he x
    rw [hH.2 x hxV] at this
    by_cases hx2 : x = b2
    · subst hx2; simp only [or_true, ite_true] at this; rw [hdb2] at this; simp; omega
    · simp only [hx1, hx2, or_self, ite_false, add_zero] at this
      rw [this, hd x hxs hxt]; simp [hx2]
  rw [hsum] at hK
  exact odd_sum (mem_cls_self hb2V) hK

lemma ncomp_le_two {V : Finset Pt} {F : Finset Edge} {a b : Pt}
    (h : ∀ z ∈ V, z ∈ cls V F a ∨ z ∈ cls V F b) : ncomp V F ≤ 2 := by
  unfold ncomp
  have hsub : V.image (cls V F) ⊆ {cls V F a, cls V F b} := by
    intro K hK
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hK
    rcases h z hz with h1 | h1
    · have := (Finset.mem_filter.1 h1).2
      simp [cls_eq_of_conn this.symm]
    · have := (Finset.mem_filter.1 h1).2
      simp [cls_eq_of_conn this.symm]
  exact (Finset.card_le_card hsub).trans (Finset.card_le_two)

lemma pick_of_two {z z1 z2 s t : Pt} (hz : z = s ∨ z = t) (h1 : z1 = s ∨ z1 = t)
    (h2 : z2 = s ∨ z2 = t) (h12 : z1 ≠ z2) : z = z1 ∨ z = z2 := by
  rcases hz with rfl | rfl <;> rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;> simp_all

lemma cut_union {P P' : Finset Pt} {g : Edge} (h : Cut (P ∪ P') g) : Cut P g ∨ Cut P' g := by
  unfold Cut at *
  simp only [Finset.mem_union] at h
  by_cases a : g.p ∈ P <;> by_cases b : g.q ∈ P <;> by_cases a' : g.p ∈ P' <;>
    by_cases b' : g.q ∈ P' <;> simp only [a, b, a', b', or_true, or_false,
      not_true, not_false_iff, iff_true, iff_false] at h ⊢

-- **A good start, or two components and a Type III cell.**
--
theorem good_start2 {V : Finset Pt} {d : Pt → ℕ} {F H : Finset Edge} (hs : SolidFor V F H)
    (hF : IsFactor V d F) (hH : IsFactor V d H) (hHam : ncomp V H = 1) {s t : Pt}
    (hd : ∀ z, z ≠ s → z ≠ t → d z = 2) (hds : d s = 1) (hdt : d t = 1)
    (hsV : s ∈ V) (htV : t ∈ V)
    (hfar : ∀ c, IsCell V c → ¬ IsCorner s c → ¬ IsCorner t c → NotTypeIII V F c)
    (hz : ∀ w, IsCorner s w ∨ IsCorner t w → D F H w = 0) (h2 : 2 ≤ ncomp V F) :
    (∃ P, Border V F P ∧ ∃ o v s0, Cut P (sideEdge v s0) ∧ outArc F v s0 = !o ∧
      (if o then D F H v = D F H (nb v s0) + 2 else D F H v = D F H (nb v s0) - 2) ∧
      Good o (D F H v) ∧ (sideEdge v (latA s0) ∈ F ∨ sideEdge v (latB s0) ∈ F)) ∨
    (ncomp V F = 2 ∧ ∃ c, IsCell V c ∧ ¬ NotTypeIII V F c) := by
  by_cases hL : ∃ P, Border V F P ∧ ∃ o v s0, Cut P (sideEdge v s0) ∧ outArc F v s0 = !o ∧
      (if o then D F H v = D F H (nb v s0) + 2 else D F H v = D F H (nb v s0) - 2) ∧
      Good o (D F H v) ∧ (sideEdge v (latA s0) ∈ F ∨ sideEdge v (latB s0) ∈ F)
  · exact Or.inl hL
  right
  have hIn := Inside.of_factor hF
  have hloc := deg2Cell_of_zero hF hH hs hd hz
  have hds1 : deg F s = 1 := by rw [hF.2 s hsV, hds]
  have hdt1 : deg F t = 1 := by rw [hF.2 t htV, hdt]
  -- Every cut edge of a union of classes is a bad start.
  --
  have bad : ∀ P, Border V F P → ∀ e ∈ H, Cut P e →
      ∃ c, IsCell V c ∧ ¬ NotTypeIII V F c ∧ ∃ z, (z = s ∨ z = t) ∧ ∃ g ∈ F, ∃ b1 b2,
        Ends g z b1 ∧ Ends e b1 b2 ∧ b1 ∈ V ∧ b2 ∈ V ∧ d b1 = 2 ∧ d b2 = 2 := by
    intro P hB e heH hcut
    obtain ⟨o, v, s0, hve, hin, hj, hg⟩ := key_of_edge hF hH hB heH hcut
    have hn : ¬ (sideEdge v (latA s0) ∈ F ∨ sideEdge v (latB s0) ∈ F) := fun hd' =>
      hL ⟨P, hB, o, v, s0, by rw [hve]; exact hcut, hin, hj, hg, hd'⟩
    have hv := Good.isCell_f hs hg
    have hv2 := hloc o v hg
    obtain ⟨hrc, hT, z, hzst, g, hgF, b, hgb, hb⟩ :=
      bad_shape2 hIn hfar hds1 hdt1 hB hv hv2 s0 (by rw [hve]; exact hcut) hn
    have ef : Ends (front v s0) (front1 v s0) (front2 v s0) := ends_front v s0
    have hfe : front v s0 = e := hve
    rw [hfe] at ef
    obtain ⟨_, _, c3, c4⟩ := isCell_corners hv s0
    have d1 : d (front1 v s0) = 2 := by rw [← hF.2 _ c3]; exact deg2_front1 hv2 s0
    have d2 : d (front2 v s0) = 2 := by rw [← hF.2 _ c4]; exact deg2_front2 hv2 s0
    refine ⟨_, hrc, hT, z, hzst, g, hgF, ?_⟩
    rcases hb with rfl | rfl
    · exact ⟨_, _, hgb, ef, c3, c4, d1, d2⟩
    · exact ⟨_, _, hgb, ef.swap, c4, c3, d2, d1⟩
  have hag : ∀ z, (z = s ∨ z = t) → ∀ g : Edge, (g.p = z ∨ g.q = z) → (g ∈ F ↔ g ∈ H) := by
    rintro z (rfl | rfl) g hg
    · exact agree_at hF hH (fun w hw => hz w (Or.inl hw)) hg
    · exact agree_at hF hH (fun w hw => hz w (Or.inr hw)) hg
  -- Two bad edges at the same endpoint are equal.
  --
  have uniq : ∀ z, (z = s ∨ z = t) → ∀ e e' g g' b1 b2 b1' b2', e ∈ H → e' ∈ H → e ∉ F →
      e' ∉ F → g ∈ F → g' ∈ F → Ends g z b1 → Ends g' z b1' → Ends e b1 b2 →
      Ends e' b1' b2' → b1 ∈ V → d b1 = 2 → d b1' = 2 → e = e' := by
    intro z hzst e e' g g' b1 b2 b1' b2' he he' heF heF' hgF hg'F hgb hgb' heb heb' hb1V hdb1 hdb1'
    have hdz : d z = 1 := by rcases hzst with rfl | rfl <;> assumption
    have hzF : deg F z = 1 := by rcases hzst with rfl | rfl <;> assumption
    exact bad_same hH hdz hzF (hag z hzst) he he' heF heF' hgF hg'F hgb hgb' heb heb' hb1V hdb1 hdb1'
  set P := cls V F t with hPdef
  have hB : Border V F P := ⟨Finset.filter_subset _ _, fun u hu w hw => closed_cls hIn t u hu w hw⟩
  have memP : ∀ z, z ∈ V → Conn F t z → z ∈ P := fun z hz hc => Finset.mem_filter.2 ⟨hz, hc⟩
  have htP : t ∈ P := mem_cls_self htV
  have hsP : s ∈ P := memP s hsV (conn_t_s hF hd hdt htV)
  have hzP : ∀ z, (z = s ∨ z = t) → z ∈ P := by rintro z (rfl | rfl) <;> assumption
  obtain ⟨y, hyV, hyP⟩ : ∃ y ∈ V, y ∉ P := by
    obtain ⟨x, hx, y, hy, hxy⟩ := exists_not_conn h2
    by_cases htx : Conn F t x
    · exact ⟨y, hy, fun h => hxy (htx.symm.trans (Finset.mem_filter.1 h).2)⟩
    · exact ⟨x, hx, fun h => htx (Finset.mem_filter.1 h).2⟩
  obtain ⟨e1, he1H, hcut1⟩ := exists_cut_edge (conn_of_ncomp_one hHam htV hyV) htP hyP
  obtain ⟨c1, hc1, hT1, z1, hz1, g1, hg1F, b1, b2, hg1b, he1b, hb1V, hb2V, hdb1, hdb2⟩ :=
    bad P hB e1 he1H hcut1
  have he1F : e1 ∉ F := fun h => hB.not_cut h hcut1
  have hb1P : b1 ∈ P := by
    have := hzP z1 hz1
    exact memP b1 hb1V ((Finset.mem_filter.1 this).2.trans (hg1b.conn hg1F))
  have hb2P : b2 ∉ P := by
    intro h; unfold Cut at hcut1
    rcases he1b with ⟨q1, q2⟩ | ⟨q1, q2⟩ <;> rw [q1, q2] at hcut1 <;> tauto
  -- A second cut edge of any set holding exactly one end of `e1`, and `s`, `t` with `b1`.
  --
  have other : ∀ Q : Finset Pt, (b2 ∈ Q ↔ b1 ∉ Q) → (s ∈ Q ↔ b1 ∈ Q) → (t ∈ Q ↔ b1 ∈ Q) →
      ∃ e' ∈ H, e' ≠ e1 ∧ Cut Q e' := by
    intro Q q2 qs qt
    have fin : ∀ x y, Conn (H.erase e1) x y → x ∈ Q → y ∉ Q → ∃ e' ∈ H, e' ≠ e1 ∧ Cut Q e' := by
      intro x y hc hx hy
      obtain ⟨e', he', hcut⟩ := exists_cut_edge hc hx hy
      exact ⟨e', (Finset.mem_erase.1 he').2, (Finset.mem_erase.1 he').1, hcut⟩
    by_cases hc : Conn (H.erase e1) b1 b2
    · by_cases h1 : b1 ∈ Q
      · exact fin _ _ hc h1 (fun h => (q2.1 h) h1)
      · exact fin _ _ hc.symm (q2.2 h1) h1
    · rcases split_or_conn hH hd he1H he1b hb2V hdb2 hc with hcz | hcz
      · by_cases h1 : b1 ∈ Q
        · exact fin _ _ hcz.symm (qs.2 h1) (fun h => (q2.1 h) h1)
        · exact fin _ _ hcz (q2.2 h1) (fun h => h1 (qs.1 h))
      · by_cases h1 : b1 ∈ Q
        · exact fin _ _ hcz.symm (qt.2 h1) (fun h => (q2.1 h) h1)
        · exact fin _ _ hcz (q2.2 h1) (fun h => h1 (qt.1 h))
  obtain ⟨e2, he2H, hne21, hcut2⟩ := other P ⟨fun h => absurd h hb2P, fun h => absurd hb1P h⟩
    ⟨fun _ => hb1P, fun _ => hsP⟩ ⟨fun _ => hb1P, fun _ => htP⟩
  obtain ⟨_, _, _, z2, hz2, g2, hg2F, b1', b2', hg2b, he2b, hb1'V, _, hdb1', _⟩ :=
    bad P hB e2 he2H hcut2
  have he2F : e2 ∉ F := fun h => hB.not_cut h hcut2
  have hz12 : z1 ≠ z2 := by
    intro h; rw [← h] at hg2b
    exact hne21 (uniq z1 hz1 _ _ _ _ _ _ _ _ he2H he1H he2F he1F hg2F hg1F hg2b hg1b he2b he1b
      hb1'V hdb1' hdb1)
  -- Every cut edge of a union of classes is `e1` or `e2`.
  --
  have allcut : ∀ Q, Border V F Q → ∀ g ∈ H, Cut Q g → g = e1 ∨ g = e2 := by
    intro Q hQ g hgH hcut
    obtain ⟨_, _, _, z, hz, g', hg'F, a1, a2, hg'b, hgb, ha1V, _, hda1, _⟩ := bad Q hQ g hgH hcut
    have hgF : g ∉ F := fun h => hQ.not_cut h hcut
    have hzz : z = z1 ∨ z = z2 := pick_of_two hz hz1 hz2 hz12
    rcases hzz with rfl | rfl
    · exact Or.inl (uniq z hz _ _ _ _ _ _ _ _ hgH he1H hgF he1F hg'F hg1F hg'b hg1b hgb he1b ha1V
        hda1 hdb1)
    · exact Or.inr (uniq z hz _ _ _ _ _ _ _ _ hgH he2H hgF he2F hg'F hg2F hg'b hg2b hgb he2b ha1V
        hda1 hdb1')
  set P' := cls V F b2 with hP'def
  have hB' : Border V F P' := ⟨Finset.filter_subset _ _, fun u hu w hw => closed_cls hIn b2 u hu w hw⟩
  have disj : ∀ x, x ∈ P → x ∉ P' := by
    intro x hx hx'
    exact hb2P (memP b2 hb2V ((Finset.mem_filter.1 hx).2.trans (Finset.mem_filter.1 hx').2.symm))
  have hb2P' : b2 ∈ P' := mem_cls_self hb2V
  obtain ⟨e', he'H, hne', hcut'⟩ := other P' ⟨fun _ => disj b1 hb1P, fun _ => hb2P'⟩
    ⟨fun h => absurd h (disj s hsP), fun h => absurd h (disj b1 hb1P)⟩
    ⟨fun h => absurd h (disj t htP), fun h => absurd h (disj b1 hb1P)⟩
  have he'2 : e' = e2 := (allcut P' hB' e' he'H hcut').resolve_left hne'
  rw [he'2] at hcut'
  have hb1'P : b1' ∈ P := by
    have := hzP z2 hz2
    exact memP b1' hb1'V ((Finset.mem_filter.1 this).2.trans (hg2b.conn hg2F))
  have hb2'P' : b2' ∈ P' := by
    have h1 := disj b1' hb1'P
    unfold Cut at hcut'
    rcases he2b with ⟨q1, q2⟩ | ⟨q1, q2⟩ <;> rw [q1, q2] at hcut' <;> tauto
  -- No edge of `H` leaves `P ∪ P'`.
  --
  have ends_in : ∀ g, (g = e1 ∨ g = e2) → g.p ∈ P ∪ P' ∧ g.q ∈ P ∪ P' := by
    rintro g (rfl | rfl)
    · rcases he1b with ⟨q1, q2⟩ | ⟨q1, q2⟩ <;> rw [q1, q2] <;> simp [hb1P, hb2P']
    · rcases he2b with ⟨q1, q2⟩ | ⟨q1, q2⟩ <;> rw [q1, q2] <;> simp [hb1'P, hb2'P']
  have cover : ∀ z ∈ V, z ∈ cls V F t ∨ z ∈ cls V F b2 := by
    intro z hzV
    by_contra hn
    push Not at hn
    have hzQ : z ∉ P ∪ P' := by simp only [Finset.mem_union, not_or]; exact hn
    obtain ⟨g, hgH, hcutQ⟩ := exists_cut_edge (conn_of_ncomp_one hHam htV hzV)
      (Finset.mem_union_left _ htP) hzQ
    have hcP : Cut P g ∨ Cut P' g := cut_union hcutQ
    have hg12 : g = e1 ∨ g = e2 := by
      rcases hcP with h | h
      · exact allcut P hB g hgH h
      · exact allcut P' hB' g hgH h
    obtain ⟨k1, k2⟩ := ends_in g hg12
    exact (hcutQ.1 k1) k2
  exact ⟨le_antisymm (ncomp_le_two cover) h2, c1, hc1, hT1⟩

end HP

end ULHC
