/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.Reroute

/-!
# The boundary created by one even strip, seen from `F`

Let `a` be a proper even strip of a factor `F` with no Type III cell, ending at `u`, and
suppose `F' = F ⊕ a` has no Type III cell either. The end cell splits its cycle into the
classes `A ∋ back1 u` and `B ∋ front1 u`.

**`created_iff`.** For a side `e` away from the strip, the following are equivalent:
* (static) some even set of sides that are light in `F` or lateral sides of `u` contains `e`,
  avoiding the start cell and meeting `u` only at its lateral sides; and no even set of
  sides light in `F` avoiding the start cell and `u` contains `e`;
* (dynamic) `e` joins `A` and `B` in `F'`.
-/

namespace ULHC

open Finset Classical

lemma allConn_side {F : Finset Edge} {d : Pt} (h : AllConn F d) (tf : Side) :
    Conn F (sideEdge d tf).p (sideEdge d tf).q := by
  obtain ⟨x, y⟩ := d
  obtain ⟨h1, h2, h3⟩ := h
  cases tf <;> simp only [sideEdge, bot, top, lft, rgt, Edge.q]
  · exact h1
  · exact h2.symm.trans h3
  · exact h2
  · exact h1.symm.trans h3

-- An even set of light sides never contains a side whose ends are joined.
--
lemma even_light_inter {V : Finset Pt} {F : Finset Edge} (hs : Solid V) (hFV : Inside V F)
    (x0 : Pt) (hconn : ∀ z ∈ V, Conn (GE V) x0 z) {B : Finset Edge}
    (heven : ∀ c, IsCell V c → sidesIn B c % 2 = 0) (hl : ∀ f ∈ B, f ∉ F) {e : Edge}
    (hE : IsEdge V e) (he : e ∈ B) : ¬ Conn F e.p e.q :=
  (inter_iff_even hs hFV x0 hconn hE).2 ⟨B, heven, hl, he⟩

-- The cut of a vertex set closed along `F`, as an even set of light sides.
--
lemma cut_even_light {V : Finset Pt} {F : Finset Edge} (S : Finset Pt)
    (hS : ∀ x y, Conn F x y → (x ∈ S ↔ y ∈ S)) :
    let B := (GE V).filter (Cut S)
    (∀ c, IsCell V c → sidesIn B c % 2 = 0) ∧ (∀ f ∈ B, f ∉ F) ∧
      ∀ f, f ∈ B ↔ IsEdge V f ∧ Cut S f := by
  intro B
  refine ⟨cut_sides_even S B (fun f => by simp [B, Finset.mem_filter, mem_GE]), ?_, ?_⟩
  · intro f hf hfF
    simp only [B, Finset.mem_filter] at hf
    have := hS _ _ (Conn.of_edge hfF)
    unfold Cut at hf
    tauto
  · intro f; simp [B, Finset.mem_filter, mem_GE]

section created

variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hs : Solid V) (x0 : Pt) (hconn : ∀ z ∈ V, Conn (GE V) x0 z)
  (hF : Deg2 V F) (hT : NoTypeIII V F) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat F c s (k + 2))
  (hsep : ¬ Conn F (back1 c s) (front1 c s)) (hT' : NoTypeIII V (flipCol F c s (k + 2)))
include hs x0 hconn hF hT hk hcell hpat hsep hT'

-- In `F'` the start cell has all four corners in one class.
--
omit hs x0 hconn hF hT in
lemma start_allConn : AllConn (flipCol F c s (k + 2)) c := by
  have l1 := (lat1_after hk hpat (j := 0) (by omega)).2 rfl
  have l2 := (lat2_after hk hpat (j := 0) (by omega)).2 rfl
  have fr : front c s ∉ flipCol F c s (k + 2) := by
    have := (front_after hk hpat (j := 0) (by omega)); rw [cellJ_zero] at this
    intro h; have := this.1 h; omega
  have bk := back_after hk hpat
  rw [cellJ_zero] at l1 l2
  have hc : IsCell V c := by have := hcell 0 (by omega); rwa [cellJ_zero] at this
  have ha : Alt (flipCol F c s (k + 2)) c := by
    rw [lat1_eq] at l1; rw [lat2_eq] at l2
    simp only [back, front] at fr bk
    obtain ⟨x, y⟩ := c
    cases s <;> simp only [latA, latB, sideEdge, Side.opp] at l1 l2 fr bk <;> unfold Alt <;> tauto
  unfold AllConn
  exact alt_corners_conn' (V := V) (hT' c hc) ha

-- In `F'` the end cell's back corners are joined, and so are its front corners.
--
omit hs x0 hconn hT' in
lemma end_corners :
    Conn (flipCol F c s (k + 2)) (back1 (cellJ c s (k + 1)) s) (back2 (cellJ c s (k + 1)) s) ∧
      Conn (flipCol F c s (k + 2)) (front1 (cellJ c s (k + 1)) s)
        (front2 (cellJ c s (k + 1)) s) ∧
      ¬ Conn (flipCol F c s (k + 2)) (back1 (cellJ c s (k + 1)) s)
        (front1 (cellJ c s (k + 1)) s) := by
  have hsame := end_same hT hk hcell hpat
  refine ⟨?_, (ends_front _ s).conn (front_end_after hk hpat),
    even_end_border k hk F hF hcell hpat hsep hsame⟩
  obtain ⟨F1, hF1, _, _, _, _, hodd⟩ := strip_even_rel k hk F hF hcell hpat hsep hsame
  -- `back u` is in `F1` (the end cell's own flip), and the back corners are not middles.
  have hb : back (cellJ c s (k + 1)) s ∈ F1 := by
    rw [hF1, mem_flip_iff]
    have uB : back (cellJ c s (k + 1)) s ∉ F := by
      rw [back_cellJ_succ]; intro h; have := (hpat.2.2 k (by omega)).1 h; omega
    have : back (cellJ c s (k + 1)) s ∈ cellE (cellJ c s (k + 1)) := by
      rw [cellE_frame _ s]; simp
    tauto
  have n1 := (end_not_mid c s k).1
  have n2 : ¬ IsMid c s k (back2 (cellJ c s (k + 1)) s) := by
    rw [← nb_cellJ, back2_nb]
    rintro ⟨j, _, hj, h | h⟩
    · exact (front_corner_ne c s (i := k) (j := j) (by omega)).2.2.1 h
    · exact (front_corner_ne c s (i := k) (j := j) (by omega)).2.2.2 h
  exact (hodd _ _ n1 n2).2 (Or.inl ((ends_back _ s).conn hb))

-- **The created boundary, seen from `F`.**
--
theorem created_iff {e : Edge} (hE : IsEdge V e) (hfar : ∀ j, e ∉ Tsw c s j) :
    ((∃ B : Finset Edge, (∀ x, IsCell V x → sidesIn B x % 2 = 0) ∧
        (∀ f ∈ B, f ∉ F ∨ f = lat1 (cellJ c s (k + 1)) s ∨ f = lat2 (cellJ c s (k + 1)) s) ∧
        (∀ f ∈ B, f ∉ cellE c) ∧
        (∀ f ∈ B, f ∈ cellE (cellJ c s (k + 1)) →
          f = lat1 (cellJ c s (k + 1)) s ∨ f = lat2 (cellJ c s (k + 1)) s) ∧ e ∈ B) ∧
      ¬ (∃ B : Finset Edge, (∀ x, IsCell V x → sidesIn B x % 2 = 0) ∧ (∀ f ∈ B, f ∉ F) ∧
        (∀ f ∈ B, f ∉ cellE c) ∧ (∀ f ∈ B, f ∉ cellE (cellJ c s (k + 1))) ∧ e ∈ B)) ↔
    (Conn (flipCol F c s (k + 2)) e.p (back1 (cellJ c s (k + 1)) s) ∧
        Conn (flipCol F c s (k + 2)) e.q (front1 (cellJ c s (k + 1)) s)) ∨
      (Conn (flipCol F c s (k + 2)) e.p (front1 (cellJ c s (k + 1)) s) ∧
        Conn (flipCol F c s (k + 2)) e.q (back1 (cellJ c s (k + 1)) s)) := by
  set u := cellJ c s (k + 1)
  set F' := flipCol F c s (k + 2)
  have hF' : Deg2 V F' := deg2_flipCol _ F hF hpat (fun j hj => hcell j (by omega))
  have hFV' := hF'.1
  obtain ⟨cb, cf, cn⟩ := end_corners hF hT hk hcell hpat hsep
  have hstart := start_allConn hk hcell hpat hsep hT'
  have hc : IsCell V c := by have := hcell 0 (by omega); rwa [cellJ_zero] at this
  have hu : IsCell V u := hcell (k + 1) le_rfl
  have fuF : front u s ∈ F' := front_end_after hk hpat
  -- Even light sets of `F'` avoid the start cell and the end cell's back and front.
  have EL : ∀ B : Finset Edge, (∀ x, IsCell V x → sidesIn B x % 2 = 0) → (∀ f ∈ B, f ∉ F') →
      (∀ f ∈ B, f ∉ cellE c) ∧ back u s ∉ B ∧ front u s ∉ B := by
    intro B hev hl
    refine ⟨fun f hf hfc => ?_, fun hb => ?_, fun hf => hl _ hf fuF⟩
    · rw [cellE_frame c s] at hfc
      have : ∃ tf, f = sideEdge c tf := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hfc
        rcases hfc with rfl | rfl | rfl | rfl
        · exact ⟨s.opp, rfl⟩
        · exact ⟨s, rfl⟩
        · exact ⟨latA s, lat1_eq c s⟩
        · exact ⟨latB s, lat2_eq c s⟩
      obtain ⟨tf, rfl⟩ := this
      exact even_light_inter hs hFV' x0 hconn hev hl (isEdge_side hc tf) hf (allConn_side hstart tf)
    · have hE' : IsEdge V (back u s) := isEdge_side hu s.opp
      exact even_light_inter hs hFV' x0 hconn hev hl hE' hb (((ends_back u s).conn_iff F').2 cb)
  have memU : ∀ f, f ∈ cellE u ↔ f = back u s ∨ f = front u s ∨ f = lat1 u s ∨ f = lat2 u s := by
    intro f; rw [cellE_frame u s]; simp
  constructor
  · rintro ⟨⟨B1, ev1, l1, c1, u1, e1⟩, hno⟩
    obtain ⟨B', ev', l', _, ag'⟩ :=
      reroute_fwd_rung hF hk hcell hpat ev1 l1 c1 u1
    have eB' : e ∈ B' := (ag' e hfar).2 e1
    have hne : ¬ Conn F' e.p e.q := even_light_inter hs hFV' x0 hconn ev' l' hE eB'
    by_contra hsepAB
    -- A vertex set closed along `F'` with `e` cut and `u`'s lateral sides not cut.
    obtain ⟨S, hS, hpS, hqS, hb1, hl1, hl2⟩ : ∃ S : Finset Pt,
        (∀ x y, Conn F' x y → (x ∈ S ↔ y ∈ S)) ∧ e.p ∈ S ∧ e.q ∉ S ∧
        (back1 u s ∈ S ↔ front1 u s ∈ S) ∧ True ∧ True := by
      by_cases hp : Conn F' e.p (back1 u s) ∨ Conn F' e.p (front1 u s)
      · refine ⟨V.filter (fun z => Conn F' (back1 u s) z ∨ Conn F' (front1 u s) z),
          fun x y hxy => ?_, ?_, ?_, ?_, trivial, trivial⟩
        · simp only [Finset.mem_filter]
          constructor
          · rintro ⟨hx, h | h⟩
            · exact ⟨conn_mem hFV' hx hxy, Or.inl (h.trans hxy)⟩
            · exact ⟨conn_mem hFV' hx hxy, Or.inr (h.trans hxy)⟩
          · rintro ⟨hy, h | h⟩
            · exact ⟨conn_mem hFV' hy hxy.symm, Or.inl (h.trans hxy.symm)⟩
            · exact ⟨conn_mem hFV' hy hxy.symm, Or.inr (h.trans hxy.symm)⟩
        · simp only [Finset.mem_filter]
          rcases hp with h | h
          · exact ⟨hE.1, Or.inl h.symm⟩
          · exact ⟨hE.1, Or.inr h.symm⟩
        · simp only [Finset.mem_filter, not_and, not_or]
          intro _
          constructor
          · intro h
            rcases hp with hp | hp
            · exact hne (hp.trans h)
            · exact hsepAB (Or.inr ⟨hp, h.symm⟩)
          · intro h
            rcases hp with hp | hp
            · exact hsepAB (Or.inl ⟨hp, h.symm⟩)
            · exact hne (hp.trans h)
        · simp only [Finset.mem_filter]
          obtain ⟨b1V, _, f1V, _⟩ := isCell_corners hu s
          exact ⟨fun _ => ⟨f1V, Or.inr (Conn.refl _ _)⟩, fun _ => ⟨b1V, Or.inl (Conn.refl _ _)⟩⟩
      · push Not at hp
        refine ⟨V.filter (fun z => Conn F' e.p z), fun x y hxy => ?_, ?_, ?_, ?_, trivial, trivial⟩
        · simp only [Finset.mem_filter]
          exact ⟨fun ⟨hx, h⟩ => ⟨conn_mem hFV' hx hxy, h.trans hxy⟩,
            fun ⟨hy, h⟩ => ⟨conn_mem hFV' hy hxy.symm, h.trans hxy.symm⟩⟩
        · simp only [Finset.mem_filter]; exact ⟨hE.1, Conn.refl _ _⟩
        · simp only [Finset.mem_filter, not_and]; exact fun _ => hne
        · simp only [Finset.mem_filter]
          exact ⟨fun h => absurd h.2 hp.1, fun h => absurd h.2 hp.2⟩
    obtain ⟨ev2, l2, m2⟩ := cut_even_light (V := V) S hS
    set B2 := (GE V).filter (Cut S)
    have hcut : ∀ {f : Edge} {a b : Pt}, Ends f a b → (f ∈ B2 ↔ IsEdge V f ∧ (a ∈ S ↔ b ∉ S)) :=
      fun hf => by rw [m2, cut_ends hf]
    have eB2 : e ∈ B2 := (m2 e).2 ⟨hE, by unfold Cut; tauto⟩
    obtain ⟨ELc, ELb, ELf⟩ := EL B2 ev2 l2
    have nl1 : lat1 u s ∉ B2 := by
      rw [hcut (ends_lat1 u s)]; tauto
    have nl2 : lat2 u s ∉ B2 := by
      rw [hcut (ends_lat2 u s)]
      have q1 := hS _ _ cb
      have q2 := hS _ _ cf
      tauto
    have avoidU : ∀ f ∈ B2, f ∉ cellE u := by
      intro f hf hfu
      rcases (memU f).1 hfu with rfl | rfl | rfl | rfl
      · exact ELb hf
      · exact ELf hf
      · exact nl1 hf
      · exact nl2 hf
    obtain ⟨B3, ev3, l3, cu3, ag3⟩ := reroute_back hF hk hcell hpat ev2 l2 ELc avoidU
    exact hno ⟨B3, ev3, l3, fun f hf => (cu3 f hf).1, fun f hf => (cu3 f hf).2,
      (ag3 e hfar).2 eB2⟩
  · intro hAB
    constructor
    · -- the cut of `A`
      set S := V.filter (fun z => Conn F' (back1 u s) z)
      have hS : ∀ x y, Conn F' x y → (x ∈ S ↔ y ∈ S) := by
        intro x y hxy
        simp only [S, Finset.mem_filter]
        exact ⟨fun ⟨hx, h⟩ => ⟨conn_mem hFV' hx hxy, h.trans hxy⟩,
          fun ⟨hy, h⟩ => ⟨conn_mem hFV' hy hxy.symm, h.trans hxy.symm⟩⟩
      obtain ⟨ev2, l2, m2⟩ := cut_even_light (V := V) S hS
      set B2 := (GE V).filter (Cut S)
      have eB2 : e ∈ B2 := by
        rw [m2]
        refine ⟨hE, ?_⟩
        unfold Cut
        simp only [S, Finset.mem_filter]
        rcases hAB with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · constructor
          · intro _ ⟨_, h⟩; exact cn (h.trans h2)
          · intro _; exact ⟨hE.1, h1.symm⟩
        · constructor
          · intro ⟨_, h⟩; exact absurd (h.trans h1) cn
          · intro h; exact absurd ⟨hE.2, h2.symm⟩ h
      obtain ⟨ELc, ELb, ELf⟩ := EL B2 ev2 l2
      have hu2 : ∀ f ∈ B2, f ∈ cellE u → f = lat1 u s ∨ f = lat2 u s := by
        intro f hf hfu
        rcases (memU f).1 hfu with rfl | rfl | h | h
        · exact absurd hf ELb
        · exact absurd hf ELf
        · exact Or.inl h
        · exact Or.inr h
      obtain ⟨B3, ev3, l3, cu3, ag3⟩ := reroute_back_rung hF hk hcell hpat ev2 l2 ELc hu2
      exact ⟨B3, ev3, l3, fun f hf => (cu3 f hf).1, fun f hf => (cu3 f hf).2, (ag3 e hfar).2 eB2⟩
    · rintro ⟨B, ev, l, cB, uB, eB⟩
      obtain ⟨B', ev', l', cu', ag'⟩ := reroute_fwd hF hk hcell hpat ev l cB uB
      obtain ⟨P, hBP, hcutP⟩ := separation B' hs ev' hFV' l' x0 hconn
      have heP := (hcutP e hE).2 ((ag' e hfar).2 eB)
      have hl1E : IsEdge V (lat1 u s) := by
        rw [lat1_eq]; exact isEdge_side hu _
      have : lat1 u s ∈ B' := by
        apply (hcutP _ hl1E).1
        rw [cut_ends (ends_lat1 u s)]
        unfold Cut at heP
        rcases hAB with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [← hBP.same_side h1, ← hBP.same_side h2]; exact heP
        · rw [← hBP.same_side h1, ← hBP.same_side h2]; tauto
      exact (cu' _ this).2 (by rw [cellE_frame u s]; simp)

end created

end ULHC
