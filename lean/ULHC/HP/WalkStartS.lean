/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.HP.TheoremAT2

/-!
# The walk's start, with the endpoint recorded

`good_start2`'s Type III case comes from two bad cut edges of `H` at different endpoints
(`hz12`). Each bad edge comes with a Type III square having its endpoint as a corner
(`bad_shape2`). So in that case some Type III square has `s` as a corner. When `s` is a corner of
no square, the case is impossible and the walk always starts (`lemmaB_t2s`).
-/

namespace ULHC

open Finset Classical

namespace HP

lemma bad_shape2s {V : Finset Pt} {F : Finset Edge} (hIn : Inside V F) {s t : Pt}
    (hfar : ∀ c, IsCell V c → ¬ IsCorner s c → ¬ IsCorner t c → NotTypeIII V F c)
    (hds1 : deg F s = 1) (hdt1 : deg F t = 1) {P : Finset Pt} (hB : Border V F P)
    {v : Pt} (hv : IsCell V v) (hv2 : Deg2Cell F v) (s0 : Side) (hcut : Cut P (sideEdge v s0))
    (hn : ¬ (sideEdge v (latA s0) ∈ F ∨ sideEdge v (latB s0) ∈ F)) :
    IsCell V (nb v s0) ∧ ¬ NotTypeIII V F (nb v s0) ∧
      ∃ z, (z = s ∨ z = t) ∧ IsCorner z (nb v s0) ∧
        ∃ g ∈ F, ∃ b, Ends g z b ∧ (b = front1 v s0 ∨ b = front2 v s0) := by
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
  refine ⟨hrc, hT, z, hz, hzr, ?_⟩
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


theorem good_start2s {V : Finset Pt} {d : Pt → ℕ} {F H : Finset Edge} (hs : SolidFor V F H)
    (hF : IsFactor V d F) (hH : IsFactor V d H) (hHam : ncomp V H = 1) {s t : Pt}
    (hd : ∀ z, z ≠ s → z ≠ t → d z = 2) (hds : d s = 1) (hdt : d t = 1)
    (hsV : s ∈ V) (htV : t ∈ V)
    (hfar : ∀ c, IsCell V c → ¬ IsCorner s c → ¬ IsCorner t c → NotTypeIII V F c)
    (hz : ∀ w, IsCorner s w ∨ IsCorner t w → D F H w = 0) (h2 : 2 ≤ ncomp V F) :
    (∃ P, Border V F P ∧ ∃ o v s0, Cut P (sideEdge v s0) ∧ outArc F v s0 = !o ∧
      (if o then D F H v = D F H (nb v s0) + 2 else D F H v = D F H (nb v s0) - 2) ∧
      Good o (D F H v) ∧ (sideEdge v (latA s0) ∈ F ∨ sideEdge v (latB s0) ∈ F)) ∨
    (∃ c, IsCell V c ∧ ¬ NotTypeIII V F c ∧ IsCorner s c) := by
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
      ∃ c, IsCell V c ∧ ¬ NotTypeIII V F c ∧ ∃ z, (z = s ∨ z = t) ∧ IsCorner z c ∧ ∃ g ∈ F, ∃ b1 b2,
        Ends g z b1 ∧ Ends e b1 b2 ∧ b1 ∈ V ∧ b2 ∈ V ∧ d b1 = 2 ∧ d b2 = 2 := by
    intro P hB e heH hcut
    obtain ⟨o, v, s0, hve, hin, hj, hg⟩ := key_of_edge hF hH hB heH hcut
    have hn : ¬ (sideEdge v (latA s0) ∈ F ∨ sideEdge v (latB s0) ∈ F) := fun hd' =>
      hL ⟨P, hB, o, v, s0, by rw [hve]; exact hcut, hin, hj, hg, hd'⟩
    have hv := Good.isCell_f hs hg
    have hv2 := hloc o v hg
    obtain ⟨hrc, hT, z, hzst, hzc, g, hgF, b, hgb, hb⟩ :=
      bad_shape2s hIn hfar hds1 hdt1 hB hv hv2 s0 (by rw [hve]; exact hcut) hn
    have ef : Ends (front v s0) (front1 v s0) (front2 v s0) := ends_front v s0
    have hfe : front v s0 = e := hve
    rw [hfe] at ef
    obtain ⟨_, _, c3, c4⟩ := isCell_corners hv s0
    have d1 : d (front1 v s0) = 2 := by rw [← hF.2 _ c3]; exact deg2_front1 hv2 s0
    have d2 : d (front2 v s0) = 2 := by rw [← hF.2 _ c4]; exact deg2_front2 hv2 s0
    refine ⟨_, hrc, hT, z, hzst, hzc, g, hgF, ?_⟩
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
  obtain ⟨c1, hc1, hT1, z1, hz1, hzc1, g1, hg1F, b1, b2, hg1b, he1b, hb1V, hb2V, hdb1, hdb2⟩ :=
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
  obtain ⟨c2, hc2, hT2, z2, hz2, hzc2, g2, hg2F, b1', b2', hg2b, he2b, hb1'V, _, hdb1', _⟩ :=
    bad P hB e2 he2H hcut2
  have he2F : e2 ∉ F := fun h => hB.not_cut h hcut2
  have hz12 : z1 ≠ z2 := by
    intro h; rw [← h] at hg2b
    exact hne21 (uniq z1 hz1 _ _ _ _ _ _ _ _ he2H he1H he2F he1F hg2F hg1F hg2b hg1b he2b he1b
      hb1'V hdb1' hdb1)
  -- The two bad edges sit at different endpoints, so one of the two Type III squares has `s` as a
  -- corner.
  --
  rcases hz1 with rfl | rfl
  · exact ⟨c1, hc1, hT1, hzc1⟩
  · rcases hz2 with rfl | rfl
    · exact ⟨c2, hc2, hT2, hzc2⟩
    · exact absurd rfl hz12

theorem endpoint_criterion_t2s {V : Finset Pt} {d : Pt → ℕ} {F H : Finset Edge} (hs : SolidFor V F H)
    (hF : IsFactor V d F) (hH : IsFactor V d H) (hHam : ncomp V H = 1) {s t : Pt}
    (hd : ∀ z, z ≠ s → z ≠ t → d z = 2)
    (hz : ∀ w, IsCorner s w ∨ IsCorner t w → D F H w = 0)
    (hds : d s = 1) (hdt : d t = 1) (hsV : s ∈ V) (htV : t ∈ V)
    (hfar : ∀ c, IsCell V c → ¬ IsCorner s c → ¬ IsCorner t c → NotTypeIII V F c)
    (h2 : 2 ≤ ncomp V F) :
    (∃ σ : StripSpec, ValidStrip V F σ ∧ 2 ≤ σ.n ∧ mu V (applyS F σ) H + 2 * σ.n = mu V F H ∧
      (∀ j < σ.n, ¬ IsCorner s (cellJ σ.c σ.s j) ∧ ¬ IsCorner t (cellJ σ.c σ.s j)) ∧
      ∃ o, ParOK σ.c σ.s o ∧ ∀ j < σ.n, Good o (D F H (cellJ σ.c σ.s j))) ∨
    (∃ c, IsCell V c ∧ ¬ NotTypeIII V F c ∧ IsCorner s c) := by
  have hloc := deg2Cell_of_zero hF hH hs hd hz
  rcases good_start2s hs hF hH hHam hd hds hdt hsV htV hfar hz h2 with
    ⟨P, hB, o, v, s0, hc0, hi0, hj0, hg0, hL0⟩ | hr
  swap
  · exact Or.inr hr
  left
  have hTg : ∀ c, Good o (D F H c) → NotTypeIII V F c := by
    intro c hg
    have h0 := good_ne_zero hg
    exact hfar c (Good.isCell_f hs hg) (fun h => h0 (hz _ (Or.inl h)))
      (fun h => h0 (hz _ (Or.inr h)))
  obtain ⟨w, _, hgw, hst⟩ := phase1_t hF hH hs hB o hTg (hloc o) v s0 hc0 hi0 hj0 hg0 hL0
  obtain ⟨s', n, hn, hpat, hcell, hgood, hp, hsep⟩ := phase2_loc hF hH hs hB (hloc o) hgw hst
  refine ⟨⟨w, s', n⟩, ⟨show 1 ≤ n by omega, hpat, hcell, hsep⟩, hn,
    strip_mu hp n hpat hcell hgood, fun j hj => ?_, o, hp, hgood⟩
  have h0 := good_ne_zero (hgood j hj)
  exact ⟨fun h => h0 (hz _ (Or.inl h)), fun h => h0 (hz _ (Or.inr h))⟩

theorem lemmaB_t2s {V : Finset Pt} {d : Pt → ℕ} {F H : Finset Edge} (hs : SolidFor V F H)
    (hF : IsFactor V d F) (hH : IsFactor V d H) (hHam : ncomp V H = 1) {s t : Pt}
    (hd : ∀ z, z ≠ s → z ≠ t → d z = 2) (hds : d s = 1) (hsV : s ∈ V)
    (hz : ∀ w, IsCorner s w ∨ IsCorner t w → D F H w = 0)
    (hdt : d t = 1) (htV : t ∈ V)
    (hfar : ∀ c, IsCell V c → ¬ IsCorner s c → ¬ IsCorner t c → NotTypeIII V F c)
    (h2 : 2 ≤ ncomp V F) :
    (∃ σ : StripSpec, ValidStrip V F σ ∧ 2 ≤ σ.n ∧ mu V (applyS F σ) H + 2 * σ.n = mu V F H ∧
      (∀ j < σ.n, ¬ IsCorner s (cellJ σ.c σ.s j) ∧ ¬ IsCorner t (cellJ σ.c σ.s j)) ∧
      ncomp V (applyS F σ) ≤ ncomp V F ∧ ncomp V F ≤ ncomp V (applyS F σ) + 1 ∧
      (σ.n % 2 = 1 → ncomp V (applyS F σ) + 1 = ncomp V F) ∧
      ∃ o, ParOK σ.c σ.s o ∧ ∀ j < σ.n, Good o (D F H (cellJ σ.c σ.s j))) ∨
    (∃ c, IsCell V c ∧ ¬ NotTypeIII V F c ∧ IsCorner s c) := by
  rcases endpoint_criterion_t2s hs hF hH hHam hd hz hds hdt hsV htV hfar h2 with
    ⟨σ, hv, hn, hmu, hcor, o, hpo, hgo⟩ | hr
  swap
  · exact Or.inr hr
  left
  have hD : Deg2Off V F s t :=
    ⟨InsideST.of_inside (Inside.of_factor hF), fun z hz hzs hzt => by rw [hF.2 z hz]; exact hd z hzs hzt⟩
  have hdsF : deg F s = 1 := by rw [hF.2 s hsV]; exact hds
  have hst := conn_st hD hsV hdsF
  suffices hcnt : ncomp V (applyS F σ) ≤ ncomp V F ∧ ncomp V F ≤ ncomp V (applyS F σ) + 1 ∧
      (σ.n % 2 = 1 → ncomp V (applyS F σ) + 1 = ncomp V F) from
    ⟨σ, hv, hn, hmu, hcor, hcnt.1, hcnt.2.1, hcnt.2.2, o, hpo, hgo⟩
  obtain ⟨_, hpat, hcell, hsep⟩ := hv
  unfold applyS
  rcases Nat.mod_two_eq_zero_or_one σ.n with hev | hodd
  · obtain ⟨k, hk⟩ : ∃ k, σ.n = k + 2 := ⟨σ.n - 2, by omega⟩
    have hk2 : k % 2 = 0 := by omega
    rw [hk] at hpat hcell hcor ⊢
    have hsame : Conn F (back1 (cellJ σ.c σ.s (k + 1)) σ.s) (back2 (cellJ σ.c σ.s (k + 1)) σ.s) := by
      have hce := hcell (k + 1) (by omega)
      obtain ⟨_, hl, hf⟩ := hpat
      have ha : Alt F (cellJ σ.c σ.s (k + 1)) := by
        have l1 := (hl (k + 1) (by omega)).1.2 (by omega)
        have l2 := (hl (k + 1) (by omega)).2.2 (by omega)
        have fF : front (cellJ σ.c σ.s (k + 1)) σ.s ∉ F := by
          intro h; have := (hf (k + 1) (by omega)).1 h; omega
        have bF : back (cellJ σ.c σ.s (k + 1)) σ.s ∉ F := by
          rw [back_cellJ_succ]; intro h; have := (hf k (by omega)).1 h; omega
        rw [lat1_eq] at l1
        rw [lat2_eq] at l2
        simp only [back, front] at fF bF
        generalize cellJ σ.c σ.s (k + 1) = r at *
        obtain ⟨x, y⟩ := r
        cases hs' : σ.s <;> rw [hs'] at l1 l2 fF bF <;>
          simp only [latA, latB, sideEdge, Side.opp] at l1 l2 fF bF <;> unfold Alt <;> tauto
      obtain ⟨k1, k2, k3⟩ := alt_corners_conn' (hfar _ hce (hcor (k + 1) (by omega)).1
        (hcor (k + 1) (by omega)).2) ha
      generalize cellJ σ.c σ.s (k + 1) = r at *
      obtain ⟨x, y⟩ := r
      cases σ.s <;> simp only [back1, back2] at * <;>
        first
        | exact k1
        | exact k2.symm.trans k3
        | exact k1.symm.trans k3
        | exact k2
    obtain ⟨b1, b2⟩ := strip_even_count_pf k hk2 F hD hsV hdsF (fun j hj => hcell j (by omega))
      (fun j hj => hcor j (by omega)) hpat hsep hsame
    exact ⟨b1, b2, fun h => by omega⟩
  · obtain ⟨k, hk⟩ : ∃ k, σ.n = k + 1 := ⟨σ.n - 1, by omega⟩
    have hk2 : k % 2 = 0 := by omega
    rw [hk] at hpat hcell hcor ⊢
    have := strip_odd_count_pf k hk2 F hD hst (fun j hj => hcell j (by omega))
      (fun j hj => hcor j (by omega)) hpat hsep
    exact ⟨by omega, by omega, fun _ => this⟩


end HP

end ULHC
