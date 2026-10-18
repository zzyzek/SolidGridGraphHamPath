/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import SolidGridHam.Path.Prelim.StripEvenPF
import SolidGridHam.Cycle.V2
import SolidGridHam.Cycle.Cr2

/-!
# Connection relations of flips and strips, for path-factors

ULHC's `ACell.merge` / `ACell.split` derive their connection relations together with the
component counts, assuming degree 2 on the whole class (every component a cycle). The
relations themselves need no degree hypothesis:

* `conn_jump`: if every edge of `X` either joins two points already joined in `F`, or "jumps"
  between the classes of `p` and `q`, then a connection in `X` is one in `F`, possibly with a
  single jump. Two jumps cancel.
* `split_rel_pf`: flipping a cell whose dark sides are in one class: a connection in `F` is one
  after the flip, possibly through one jump between `a` and `b`.
* `merge_rel_pf`: flipping a cell whose dark sides are in two classes, at least one a cycle: the
  two classes join and nothing else changes.

These replace the cycle-only parts of `ACell.merge` / `ACell.split` (audit of 2026-10-12);
the counts are `merge_count` and `flip_same_count` (StripCountPF, StripEvenPF).
-/

namespace SolidGridHam

open Finset Classical

namespace HP

-- `u`, `v` are joined in `F`, or `u` is joined to one of `p`, `q` and `v` to the other.
--
def JumpRel (F : Finset Edge) (p q u v : Pt) : Prop :=
  Conn F u v ∨ (Conn F u p ∧ Conn F v q) ∨ (Conn F u q ∧ Conn F v p)

lemma JumpRel.symm {F : Finset Edge} {p q u v : Pt} (h : JumpRel F p q u v) :
    JumpRel F p q v u := by
  rcases h with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl h.symm
  · exact Or.inr (Or.inr ⟨h2, h1⟩)
  · exact Or.inr (Or.inl ⟨h2, h1⟩)

-- **One jump suffices.** Every edge of `X` is a `JumpRel` pair of `F`; then a connection in
-- `X` is one in `F` with at most one jump between the classes of `p` and `q`.
--
theorem conn_jump {X F : Finset Edge} {p q : Pt}
    (hX : ∀ f ∈ X, JumpRel F p q f.p f.q) {x y : Pt} (h : Conn X x y) :
    Conn F x y ∨ (Conn F x p ∧ Conn F q y) ∨ (Conn F x q ∧ Conn F p y) := by
  induction h with
  | refl => exact Or.inl (Conn.refl _ _)
  | tail _ hyz ih =>
    rename_i y z _
    obtain ⟨f, hf, hfe⟩ := hyz
    have J : JumpRel F p q y z := by
      rcases hfe with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have := hX f hf; rw [h1, h2] at this; exact this
      · have := hX f hf; rw [h1, h2] at this; exact this.symm
    rcases J with hj | ⟨hyp, hzq⟩ | ⟨hyq, hzp⟩
    · rcases ih with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl (h.trans hj)
      · exact Or.inr (Or.inl ⟨h1, h2.trans hj⟩)
      · exact Or.inr (Or.inr ⟨h1, h2.trans hj⟩)
    · rcases ih with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inr (Or.inl ⟨h.trans hyp, hzq.symm⟩)
      · exact Or.inl ((h1.trans (h2.trans hyp).symm).trans hzq.symm)
      · exact Or.inl (h1.trans hzq.symm)
    · rcases ih with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inr (Or.inr ⟨h.trans hyq, hzp.symm⟩)
      · exact Or.inl (h1.trans hzp.symm)
      · exact Or.inl ((h1.trans (h2.trans hyq).symm).trans hzp.symm)

-- A point joined to one end of an `Ends` edge, in either orientation of the edge.
--
lemma jump_of_ends {F : Finset Edge} {e : Edge} {u v p q : Pt} (h : Ends e u v)
    (hp : Conn F u p) (hq : Conn F v q) : JumpRel F p q e.p e.q := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
  · exact Or.inr (Or.inl ⟨hp, hq⟩)
  · exact Or.inr (Or.inr ⟨hq, hp⟩)

lemma mem_res_cases {C : ACell} {F : Finset Edge} {f : Edge} (hf : f ∈ C.res F) :
    f = C.l2 ∨ f = C.l1 ∨ (f ∈ F ∧ f ≠ C.e1 ∧ f ≠ C.e2) := by
  unfold ACell.res at hf
  rcases Finset.mem_insert.1 hf with rfl | hf
  · exact Or.inl rfl
  rcases Finset.mem_insert.1 hf with rfl | hf
  · exact Or.inr (Or.inl rfl)
  obtain ⟨h2, hf⟩ := Finset.mem_erase.1 hf
  obtain ⟨h1, hf⟩ := Finset.mem_erase.1 hf
  exact Or.inr (Or.inr ⟨hf, h1, h2⟩)

lemma l1_mem_res (C : ACell) (F : Finset Edge) : C.l1 ∈ C.res F := by
  unfold ACell.res; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)

lemma l2_mem_res (C : ACell) (F : Finset Edge) : C.l2 ∈ C.res F := by
  unfold ACell.res; exact Finset.mem_insert_self _ _

lemma mem_res_of {C : ACell} {F : Finset Edge} {f : Edge} (hf : f ∈ F) (h1 : f ≠ C.e1)
    (h2 : f ≠ C.e2) : f ∈ C.res F := by
  unfold ACell.res
  exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
    (Finset.mem_erase.2 ⟨h2, Finset.mem_erase.2 ⟨h1, hf⟩⟩))

section rel

variable {F : Finset Edge} (C : ACell) (he1 : C.e1 ∈ F) (he2 : C.e2 ∈ F)
include he1 he2

-- **Split relation, any factor.** Flipping a cell whose dark sides are in one class: a
-- connection of `F` is one after the flip, possibly through one jump between `a` and `b`;
-- and the flip joins nothing new.
--
theorem split_rel_pf (hsame : Conn F C.a C.d) (x y : Pt) :
    Conn F x y ↔ Conn (C.res F) x y ∨ (Conn (C.res F) x C.a ∧ Conn (C.res F) C.b y) ∨
      (Conn (C.res F) x C.b ∧ Conn (C.res F) C.a y) := by
  constructor
  · intro h
    apply conn_jump _ h
    intro f hf
    by_cases f1 : f = C.e1
    · subst f1; exact jump_of_ends C.h1 (Conn.refl _ _) (Conn.refl _ _)
    by_cases f2 : f = C.e2
    · subst f2
      exact jump_of_ends C.h2 (C.h3.conn (l1_mem_res C F)).symm (C.h4.conn (l2_mem_res C F)).symm
    · exact Or.inl (Conn.of_edge (mem_res_of hf f1 f2))
  · have sub := flip_same_conn C he1 he2 hsame
    have hab : Conn F C.a C.b := C.h1.conn he1
    rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact sub _ _ h
    · exact ((sub _ _ h1).trans hab).trans (sub _ _ h2)
    · exact ((sub _ _ h1).trans hab.symm).trans (sub _ _ h2)

-- **Merge relation, given the two re-joinings.** If after the flip `a`, `b` are joined and `d`,
-- `k` are joined, the flip joins the classes of `a` and `d` and changes nothing else.
--
theorem merge_rel_of (hab : Conn (C.res F) C.a C.b) (hdk : Conn (C.res F) C.d C.k) (x y : Pt) :
    Conn (C.res F) x y ↔
      Conn F x y ∨ (Conn F x C.a ∧ Conn F C.d y) ∨ (Conn F x C.d ∧ Conn F C.a y) := by
  have hFab : Conn F C.a C.b := C.h1.conn he1
  have hFdk : Conn F C.d C.k := C.h2.conn he2
  have lift : ∀ u v, Conn F u v → Conn (C.res F) u v := by
    intro u v h
    induction h with
    | refl => exact Conn.refl _ _
    | tail _ hyz ih =>
      obtain ⟨f, hf, hfe⟩ := hyz
      by_cases f1 : f = C.e1
      · subst f1; exact ih.trans (conn_of_ends C.h1 hab hfe)
      by_cases f2 : f = C.e2
      · subst f2; exact ih.trans (conn_of_ends C.h2 hdk hfe)
      · exact ih.trans (Conn.of_adj ⟨f, mem_res_of hf f1 f2, hfe⟩)
  have had : Conn (C.res F) C.a C.d := C.h3.conn (l1_mem_res C F)
  constructor
  · intro h
    apply conn_jump _ h
    intro f hf
    rcases mem_res_cases hf with rfl | rfl | ⟨hf, _, _⟩
    · exact jump_of_ends C.h4 hFab.symm hFdk.symm
    · exact jump_of_ends C.h3 (Conn.refl _ _) (Conn.refl _ _)
    · exact Or.inl (Conn.of_edge hf)
  · rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact lift _ _ h
    · exact ((lift _ _ h1).trans had).trans (lift _ _ h2)
    · exact ((lift _ _ h1).trans had.symm).trans (lift _ _ h2)

-- **Merge relation, cycle on the `d` side.**
--
theorem merge_rel_d {V : Finset Pt} (hV : Inside V F)
    (hdeg : ∀ z, Conn F C.d z → deg F z = 2) (hn : ¬ Conn F C.a C.d) (x y : Pt) :
    Conn (C.res F) x y ↔
      Conn F x y ∨ (Conn F x C.a ∧ Conn F C.d y) ∨ (Conn F x C.d ∧ Conn F C.a y) := by
  set G1 := F.erase C.e1 with hG1
  have hG1F : G1 ⊆ F := Finset.erase_subset _ _
  have he2' : C.e2 ∈ G1 := Finset.mem_erase.2 ⟨C.e2_ne_e1, he2⟩
  have hFab : Conn F C.a C.b := C.h1.conn he1
  have hdk0 : Conn (G1.erase C.e2) C.d C.k := by
    apply C.h2.erase_conn (hV.mono hG1F) he2'
    intro z _ hz
    have hzF : Conn F C.d z := hz.mono hG1F
    have hza : ¬ (z = C.a ∨ z = C.b) := by
      rintro (rfl | rfl)
      · exact hn hzF.symm
      · exact hn (hFab.trans hzF.symm)
    have := C.h1.deg_erase he1 z
    rw [ite_eq_right hza, add_zero, ← hG1] at this
    rw [this, hdeg z hzF]; exact even_two
  have sub : G1.erase C.e2 ⊆ C.res F := by
    intro f hf; unfold ACell.res
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hf)
  have hdk : Conn (C.res F) C.d C.k := hdk0.mono sub
  have had : Conn (C.res F) C.a C.d := C.h3.conn (l1_mem_res C F)
  have hbk : Conn (C.res F) C.b C.k := C.h4.conn (l2_mem_res C F)
  exact merge_rel_of C he1 he2 ((had.trans hdk).trans hbk.symm) hdk x y

end rel

-- **Merge relation for path-factors**: one of the two classes is a cycle.
--
theorem merge_rel_pf {V : Finset Pt} {F : Finset Edge} (C : ACell) (hV : Inside V F)
    (he1 : C.e1 ∈ F) (he2 : C.e2 ∈ F)
    (hcyc : (∀ z, Conn F C.d z → deg F z = 2) ∨ (∀ z, Conn F C.a z → deg F z = 2))
    (hn : ¬ Conn F C.a C.d) (x y : Pt) :
    Conn (C.res F) x y ↔
      Conn F x y ∨ (Conn F x C.a ∧ Conn F C.d y) ∨ (Conn F x C.d ∧ Conn F C.a y) := by
  rcases hcyc with h | h
  · exact merge_rel_d C he1 he2 hV h hn x y
  · have := merge_rel_d C.swap he2 he1 hV h (fun h' => hn h'.symm) x y
    rw [C.swap_res] at this
    rw [this]
    show Conn F x y ∨ (Conn F x C.d ∧ Conn F C.a y) ∨ (Conn F x C.a ∧ Conn F C.d y) ↔ _
    tauto

section odd

variable {V : Finset Pt} {c : Pt} {s : Side} {s0 t0 : Pt}

-- **Odd strip for path-factors, with connections** (ULHC `strip_odd` for path-factors): no cell
-- has `s0` or `t0` as a corner; the count drops by one and the classes of `back1 c`,
-- `front1 c` join.
--
theorem strip_odd_pf : ∀ k : ℕ, k % 2 = 0 → ∀ F : Finset Edge, Deg2Off V F s0 t0 →
    Conn F s0 t0 → (∀ j ≤ k, IsCell V (cellJ c s j)) →
    (∀ j ≤ k, ¬ IsCorner s0 (cellJ c s j) ∧ ¬ IsCorner t0 (cellJ c s j)) →
    StripPat F c s (k + 1) → ¬ Conn F (back1 c s) (front1 c s) →
    ncomp V (flipCol F c s (k + 1)) + 1 = ncomp V F ∧
      ∀ x y, ¬ IsMid c s k x → ¬ IsMid c s k y →
        (Conn (flipCol F c s (k + 1)) x y ↔ Conn F x y ∨
          (Conn F x (back1 c s) ∧ Conn F (front1 c s) y) ∨
          (Conn F x (front1 c s) ∧ Conn F (back1 c s) y)) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro hk F hF hst hcell hcor hpat hsep
  rcases (show k = 0 ∨ 2 ≤ k by omega) with rfl | hk2
  · rw [flipCol_succ]
    simp only [flipCol]
    rw [cellJ_zero]
    have hc : IsCell V c := by have := hcell 0 le_rfl; rwa [cellJ_zero] at this
    obtain ⟨hb, hl, hf⟩ := hpat
    have l1 := (hl 0 (by omega)).1
    have l2 := (hl 0 (by omega)).2
    have f0 := hf 0 (by omega)
    rw [cellJ_zero] at l1 l2 f0
    simp at l1 l2 f0
    rw [(mkBF c s).flip_eq (mkBF_cellE c s) hb f0 l1 l2]
    obtain ⟨cb1, cb2, cf1, cf2⟩ := isCell_corners hc s
    have hcyc : (∀ z, Conn F (mkBF c s).d z → deg F z = 2) ∨
        (∀ z, Conn F (mkBF c s).a z → deg F z = 2) := by
      by_cases hd : Conn F (front1 c s) s0
      · right
        exact class_deg2 hF hst cb1 (fun h => hsep (h.trans hd.symm))
      · left
        exact class_deg2 hF hst cf1 hd
    exact ⟨merge_count (mkBF c s) hF.1 cb1 cb2 cf1 cf2 hb f0 hcyc hsep,
      fun x y _ _ => merge_rel_pf (mkBF c s) hF.1 hb f0 hcyc hsep x y⟩
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
    have hm : m % 2 = 0 := by omega
    rw [show m + 2 + 1 = m + 3 from rfl, flipCol_succ, flipCol_succ]
    set u := cellJ c s (m + 1)
    have hnb : nb u s = cellJ c s (m + 2) := nb_cellJ c s (m + 1)
    obtain ⟨hb, hl, hf⟩ := hpat
    have uL1 : lat1 u s ∈ F := (hl (m + 1) (by omega)).1.2 (by omega)
    have uL2 : lat2 u s ∈ F := (hl (m + 1) (by omega)).2.2 (by omega)
    have uF : front u s ∈ F := (hf (m + 1) (by omega)).2 (by omega)
    have uB : back u s ∉ F := by
      rw [back_cellJ_succ]
      intro h; have := (hf m (by omega)).1 h; omega
    have wL1 : lat1 (nb u s) s ∉ F := by
      rw [hnb]; intro h; have := (hl (m + 2) (by omega)).1.1 h; omega
    have wL2 : lat2 (nb u s) s ∉ F := by
      rw [hnb]; intro h; have := (hl (m + 2) (by omega)).2.1 h; omega
    have wF : front (nb u s) s ∈ F := by
      rw [hnb]; exact (hf (m + 2) (by omega)).2 (by omega)
    have hdouble : flip (flip F (cellJ c s (m + 2))) (cellJ c s (m + 1)) = (mkPair u s).res F := by
      rw [← hnb]; exact pair_flip_eq u s uL1 uL2 wF uB wL1 wL2
    have hcu : IsCell V u := hcell (m + 1) (by omega)
    have hcw : IsCell V (nb u s) := by rw [hnb]; exact hcell (m + 2) (by omega)
    obtain ⟨ub1, ub2, uf1, uf2⟩ := isCell_corners hcu s
    obtain ⟨_, _, wf1, wf2⟩ := isCell_corners hcw s
    obtain ⟨cu1, cu2⟩ := hcor (m + 1) (by omega)
    have nf1s : front1 u s ≠ s0 := fun h => cu1 (h ▸ isCorner_front1 u s)
    have nf1t : front1 u s ≠ t0 := fun h => cu2 (h ▸ isCorner_front1 u s)
    have nf2s : front2 u s ≠ s0 := fun h => cu1 (h ▸ isCorner_front2 u s)
    have nf2t : front2 u s ≠ t0 := fun h => cu2 (h ▸ isCorner_front2 u s)
    obtain ⟨hcount, hrel⟩ := (mkPair u s).flip ub2 uf1 uf2 wf1 uL1 uL2 uF wF
      (hF.2 _ uf1 nf1s nf1t) (hF.2 _ uf2 nf2s nf2t)
    rw [hdouble]
    have hF2' : Deg2Off V ((mkPair u s).res F) s0 t0 := by
      rw [← hdouble]
      have hw : cellJ c s (m + 2) = nb u s := hnb.symm
      have d1 : Deg2Off V (flip F (cellJ c s (m + 2))) s0 t0 := by
        rw [hw]
        exact hF.flip (mkBF (nb u s) s) hcw (mkBF_cellE _ s)
          (by show back (nb u s) s ∈ F; rw [back_nb]; exact uF) wF wL1 wL2
      have m1 : lat1 u s ∈ flip F (cellJ c s (m + 2)) := by
        rw [mem_flip_iff]; have := lat1_not_mem c s (j := m + 1) (m := m + 2) (by omega); tauto
      have m2 : lat2 u s ∈ flip F (cellJ c s (m + 2)) := by
        rw [mem_flip_iff]; have := lat2_not_mem c s (j := m + 1) (m := m + 2) (by omega); tauto
      have m3 : back u s ∉ flip F (cellJ c s (m + 2)) := by
        rw [mem_flip_iff, back_cellJ_succ]
        have := front_not_mem c s (j := m) (m := m + 2) (by omega) (by omega)
        rw [back_cellJ_succ] at uB; tauto
      have m4 : front u s ∉ flip F (cellJ c s (m + 2)) := by
        rw [mem_flip_iff]; have := front_mem_next c s (m + 1); tauto
      exact d1.flip (mkLat u s) hcu (mkLat_cellE u s) m1 m2 m3 m4
    have hpat2 : StripPat ((mkPair u s).res F) c s (m + 1) := by
      rw [← hdouble]; exact pat_flip_pair hm ⟨hb, hl, hf⟩
    have hsep2 : ¬ Conn ((mkPair u s).res F) (back1 c s) (front1 c s) := by
      obtain ⟨n1, n2, n3, n4⟩ := corner_ne c s (m := m + 1) (by omega)
      rw [hrel _ _ n1 n2 n3 n4]; exact hsep
    have hst2 : Conn ((mkPair u s).res F) s0 t0 := by
      rw [hrel _ _ nf1s.symm nf2s.symm nf1t.symm nf2t.symm]; exact hst
    obtain ⟨ihc, ihr⟩ := ih m (by omega) hm _ hF2' hst2 (fun j hj => hcell j (by omega))
      (fun j hj => hcor j (by omega)) hpat2 hsep2
    refine ⟨by omega, fun x y hx hy => ?_⟩
    have nm : ∀ z, ¬ IsMid c s (m + 2) z → z ≠ front1 u s ∧ z ≠ front2 u s := by
      intro z hz
      exact ⟨fun h => hz ⟨m + 1, by omega, by omega, Or.inl h⟩,
        fun h => hz ⟨m + 1, by omega, by omega, Or.inr h⟩⟩
    have sub : ∀ z, ¬ IsMid c s (m + 2) z → ¬ IsMid c s m z := by
      intro z hz ⟨j, h1, h2, h3⟩; exact hz ⟨j, h1, by omega, h3⟩
    obtain ⟨n1, n2, n3, n4⟩ := corner_ne c s (m := m + 1) (by omega)
    obtain ⟨x1, x2⟩ := nm x hx
    obtain ⟨y1, y2⟩ := nm y hy
    rw [ihr x y (sub x hx) (sub y hy), hrel _ _ x1 x2 y1 y2, hrel _ _ x1 x2 n1 n2,
      hrel _ _ n3 n4 y1 y2, hrel _ _ x1 x2 n3 n4, hrel _ _ n1 n2 y1 y2]

end odd

section even

variable {V : Finset Pt} {c : Pt} {s : Side} {s0 t0 : Pt}

-- **Even strip for path-factors, with connections** (ULHC `strip_even_rel`). `F1` is `F` with
-- the end cell `u` flipped. Unlike ULHC, `u` need not separate its corners (it may twist the
-- path); it does when its flip raises the count, which a count-neutral strip forces.
--
theorem strip_even_rel_pf (k : ℕ) (hk : k % 2 = 0) (F : Finset Edge) (hF : Deg2Off V F s0 t0)
    (hs0 : s0 ∈ V) (hds : deg F s0 = 1)
    (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j))
    (hcor : ∀ j ≤ k + 1, ¬ IsCorner s0 (cellJ c s j) ∧ ¬ IsCorner t0 (cellJ c s j))
    (hpat : StripPat F c s (k + 2)) (hsep : ¬ Conn F (back1 c s) (front1 c s))
    (hsame : Conn F (back1 (cellJ c s (k + 1)) s) (back2 (cellJ c s (k + 1)) s)) :
    ∃ F1 : Finset Edge, F1 = flip F (cellJ c s (k + 1)) ∧
      flipCol F c s (k + 2) = flipCol F1 c s (k + 1) ∧
      (∀ x y, Conn F1 x y → Conn F x y) ∧
      (∀ x y, Conn F x y ↔ Conn F1 x y ∨
        (Conn F1 x (back1 (cellJ c s (k + 1)) s) ∧ Conn F1 (front1 (cellJ c s (k + 1)) s) y) ∨
        (Conn F1 x (front1 (cellJ c s (k + 1)) s) ∧ Conn F1 (back1 (cellJ c s (k + 1)) s) y)) ∧
      (∀ x y, ¬ IsMid c s k x → ¬ IsMid c s k y →
        (Conn (flipCol F c s (k + 2)) x y ↔ Conn F1 x y ∨
          (Conn F1 x (back1 c s) ∧ Conn F1 (front1 c s) y) ∨
          (Conn F1 x (front1 c s) ∧ Conn F1 (back1 c s) y))) ∧
      ncomp V (flipCol F c s (k + 2)) + 1 = ncomp V F1 ∧
      (ncomp V F1 = ncomp V F + 1 →
        ¬ Conn F1 (back1 (cellJ c s (k + 1)) s) (front1 (cellJ c s (k + 1)) s)) := by
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
  have hflip : flip F u = (mkLat u s).res F := (mkLat u s).flip_eq hE uL1 uL2 uB uF
  have hconn := flip_same_conn (mkLat u s) uL1 uL2 hsame
  have hrel := split_rel_pf (mkLat u s) uL1 uL2 hsame
  have hF' : Deg2Off V ((mkLat u s).res F) s0 t0 := by
    rw [← hflip]; exact hF.flip (mkLat u s) hcu hE uL1 uL2 uB uF
  have hds' : deg ((mkLat u s).res F) s0 = 1 := by
    rw [(mkLat u s).deg_res uL1 uL2 uB uF]; exact hds
  have hst' := conn_st hF' hs0 hds'
  have hpat' : StripPat ((mkLat u s).res F) c s (k + 1) := by
    rw [← hflip]; exact pat_flip_last hk ⟨hb, hl, hf⟩
  have hsep' : ¬ Conn ((mkLat u s).res F) (back1 c s) (front1 c s) :=
    fun h => hsep (hconn _ _ h)
  obtain ⟨hcnt, hodd⟩ := strip_odd_pf k hk _ hF' hst' (fun j hj => hcell j (by omega))
    (fun j hj => hcor j (by omega)) hpat' hsep'
  have hcol : flipCol F c s (k + 2) = flipCol ((mkLat u s).res F) c s (k + 1) := by
    rw [flipCol_succ, hflip]
  refine ⟨(mkLat u s).res F, hflip.symm, hcol, hconn, hrel, ?_, ?_, ?_⟩
  · intro x y hx hy; rw [hcol]; exact hodd x y hx hy
  · rw [hcol]; exact hcnt
  · intro hup hj
    have same : ∀ x ∈ V, ∀ y ∈ V, Conn F x y ↔ Conn ((mkLat u s).res F) x y := by
      intro x _ y _
      rw [hrel x y]
      constructor
      · rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact h
        · exact (h1.trans hj).trans h2
        · exact (h1.trans hj.symm).trans h2
      · exact fun h => Or.inl h
    have := ncomp_congr same
    omega

-- **A count-neutral even strip splits at its end cell**: flipping `u` alone raises the count.
--
theorem neutral_end_splits (k : ℕ) (hk : k % 2 = 0) (F : Finset Edge) (hF : Deg2Off V F s0 t0)
    (hs0 : s0 ∈ V) (hds : deg F s0 = 1)
    (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j))
    (hcor : ∀ j ≤ k + 1, ¬ IsCorner s0 (cellJ c s j) ∧ ¬ IsCorner t0 (cellJ c s j))
    (hpat : StripPat F c s (k + 2)) (hsep : ¬ Conn F (back1 c s) (front1 c s))
    (hsame : Conn F (back1 (cellJ c s (k + 1)) s) (back2 (cellJ c s (k + 1)) s))
    (hneut : ncomp V (flipCol F c s (k + 2)) = ncomp V F) :
    ¬ Conn (flip F (cellJ c s (k + 1))) (back1 (cellJ c s (k + 1)) s)
      (front1 (cellJ c s (k + 1)) s) := by
  obtain ⟨F1, rfl, _, _, _, _, hcnt, hab⟩ :=
    strip_even_rel_pf k hk F hF hs0 hds hcell hcor hpat hsep hsame
  exact hab (by omega)

-- **Lemma 5.6 for path-factors**, for a count-neutral strip: afterwards the end cell's
-- `back1` and `front1` are in different classes.
--
theorem even_end_border_pf (k : ℕ) (hk : k % 2 = 0) (F : Finset Edge) (hF : Deg2Off V F s0 t0)
    (hs0 : s0 ∈ V) (hds : deg F s0 = 1)
    (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j))
    (hcor : ∀ j ≤ k + 1, ¬ IsCorner s0 (cellJ c s j) ∧ ¬ IsCorner t0 (cellJ c s j))
    (hpat : StripPat F c s (k + 2)) (hsep : ¬ Conn F (back1 c s) (front1 c s))
    (hsame : Conn F (back1 (cellJ c s (k + 1)) s) (back2 (cellJ c s (k + 1)) s))
    (hneut : ncomp V (flipCol F c s (k + 2)) = ncomp V F) :
    ¬ Conn (flipCol F c s (k + 2)) (back1 (cellJ c s (k + 1)) s) (front1 (cellJ c s (k + 1)) s) := by
  obtain ⟨F1, rfl, _, hrel, _, hodd, hcnt, hab0⟩ :=
    strip_even_rel_pf k hk F hF hs0 hds hcell hcor hpat hsep hsame
  have hab := hab0 (by omega)
  obtain ⟨na, nb⟩ := end_not_mid c s k
  rw [hodd _ _ na nb]
  have huF : Conn F (back1 (cellJ c s (k + 1)) s) (front1 (cellJ c s (k + 1)) s) := by
    obtain ⟨_, hl, _⟩ := hpat
    exact (ends_lat1 _ s).conn ((hl (k + 1) (by omega)).1.2 (by omega))
  rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
  · exact hab h
  · exact hsep ((hrel _ _ h1).symm.trans (huF.trans (hrel _ _ h2).symm))
  · exact hsep ((hrel _ _ h2).trans (huF.symm.trans (hrel _ _ h1)))

end even

section symm

variable {V : Finset Pt} {G : Finset Edge} {s0 t0 : Pt}

-- Flipping an alternating cell (frame `tf`) of a path-factor: down by one when its lateral
-- sides are in different classes; up by 0 or 1 when in one class.
--
lemma lat_count (hG : Deg2Off V G s0 t0) (hst : Conn G s0 t0) {v : Pt} {tf : Side}
    (hv : IsCell V v) (lv1 : lat1 v tf ∈ G) (lv2 : lat2 v tf ∈ G) (bv : back v tf ∉ G)
    (fv : front v tf ∉ G) :
    (Conn G (back1 v tf) (back2 v tf) →
      ncomp V G ≤ ncomp V (flip G v) ∧ ncomp V (flip G v) ≤ ncomp V G + 1) ∧
    (¬ Conn G (back1 v tf) (back2 v tf) → ncomp V (flip G v) + 1 = ncomp V G) := by
  have hE := mkLat_cellE v tf
  rw [(mkLat v tf).flip_eq hE lv1 lv2 bv fv]
  obtain ⟨vb1, vb2, vf1, vf2⟩ := isCell_corners hv tf
  refine ⟨fun h => flip_same_count (mkLat v tf) vb1 vf1 vb2 vf2 lv1 lv2 h, fun h => ?_⟩
  have hcyc : (∀ z, Conn G (mkLat v tf).d z → deg G z = 2) ∨
      (∀ z, Conn G (mkLat v tf).a z → deg G z = 2) := by
    by_cases hd : Conn G (back2 v tf) s0
    · right; exact class_deg2 hG hst vb1 (fun h' => h (h'.trans hd.symm))
    · left; exact class_deg2 hG hst vb2 hd
  exact merge_count (mkLat v tf) hG.1 vb1 vf1 vb2 vf2 lv1 lv2 hcyc h

-- **`split_symm` for path-factors**, when both cells split (neither twists): `u` separates
-- `v`'s back corners iff `v` separates `u`'s.
--
theorem split_symm_pf (hG : Deg2Off V G s0 t0) (hs0 : s0 ∈ V) (hds : deg G s0 = 1)
    {u v : Pt} {s tf : Side} (hu : IsCell V u) (hv : IsCell V v)
    (lu1 : lat1 u s ∈ G) (lu2 : lat2 u s ∈ G) (bu : back u s ∉ G) (fu : front u s ∉ G)
    (lv1 : lat1 v tf ∈ G) (lv2 : lat2 v tf ∈ G) (bv : back v tf ∉ G) (fv : front v tf ∉ G)
    (hdisj : ∀ e, e ∈ cellE u → e ∉ cellE v)
    (hspu : ncomp V (flip G u) = ncomp V G + 1) (hspv : ncomp V (flip G v) = ncomp V G + 1) :
    Conn (flip G u) (back1 v tf) (back2 v tf) ↔ Conn (flip G v) (back1 u s) (back2 u s) := by
  have hdisj' : ∀ e, e ∈ cellE v → e ∉ cellE u := fun e h1 h2 => hdisj e h2 h1
  have mv : ∀ e, e ∈ cellE v → (e ∈ flip G u ↔ e ∈ G) := fun e he => mem_flip_off (hdisj' e he)
  have mu : ∀ e, e ∈ cellE u → (e ∈ flip G v ↔ e ∈ G) := fun e he => mem_flip_off (hdisj e he)
  have sv : ∀ e, e = lat1 v tf ∨ e = lat2 v tf ∨ e = back v tf ∨ e = front v tf → e ∈ cellE v := by
    intro e he; rw [cellE_frame v tf]; rcases he with rfl | rfl | rfl | rfl <;> simp
  have su : ∀ e, e = lat1 u s ∨ e = lat2 u s ∨ e = back u s ∨ e = front u s → e ∈ cellE u := by
    intro e he; rw [cellE_frame u s]; rcases he with rfl | rfl | rfl | rfl <;> simp
  have hGu : Deg2Off V (flip G u) s0 t0 := by
    rw [(mkLat u s).flip_eq (mkLat_cellE u s) lu1 lu2 bu fu]
    rw [← (mkLat u s).flip_eq (mkLat_cellE u s) lu1 lu2 bu fu]
    exact hG.flip (mkLat u s) hu (mkLat_cellE u s) lu1 lu2 bu fu
  have hGv : Deg2Off V (flip G v) s0 t0 :=
    hG.flip (mkLat v tf) hv (mkLat_cellE v tf) lv1 lv2 bv fv
  have dsu : deg (flip G u) s0 = 1 := by
    rw [(mkLat u s).flip_eq (mkLat_cellE u s) lu1 lu2 bu fu, (mkLat u s).deg_res lu1 lu2 bu fu]
    exact hds
  have dsv : deg (flip G v) s0 = 1 := by
    rw [(mkLat v tf).flip_eq (mkLat_cellE v tf) lv1 lv2 bv fv, (mkLat v tf).deg_res lv1 lv2 bv fv]
    exact hds
  have stu := conn_st hGu hs0 dsu
  have stv := conn_st hGv hs0 dsv
  have A := lat_count hGu stu hv ((mv _ (sv _ (Or.inl rfl))).2 lv1)
    ((mv _ (sv _ (Or.inr (Or.inl rfl)))).2 lv2)
    (fun h => bv ((mv _ (sv _ (Or.inr (Or.inr (Or.inl rfl))))).1 h))
    (fun h => fv ((mv _ (sv _ (Or.inr (Or.inr (Or.inr rfl))))).1 h))
  have B := lat_count hGv stv hu ((mu _ (su _ (Or.inl rfl))).2 lu1)
    ((mu _ (su _ (Or.inr (Or.inl rfl)))).2 lu2)
    (fun h => bu ((mu _ (su _ (Or.inr (Or.inr (Or.inl rfl))))).1 h))
    (fun h => fu ((mu _ (su _ (Or.inr (Or.inr (Or.inr rfl))))).1 h))
  rw [flip_flip_comm] at A
  constructor
  · intro h
    by_contra h'
    have := A.1 h; have := B.2 h'; omega
  · intro h
    by_contra h'
    have := A.2 h'; have := B.1 h; omega

end symm

end HP

end SolidGridHam
