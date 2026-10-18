/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import SolidGridHam.Path.Prelim.Endpoint

@[expose] public section

/-!
# Strip counts for path-factors (notes: Lemma B, part 3)

`ACell.merge` assumes both components met by the flipped cell are cycles. For a path-factor
one of them may be the s–t path. `merge_count` needs only one of them to be a cycle: delete
the cycle's edge (no change), add `l1` (merge), then delete `e1` and add `l2`, which either
both change nothing or raise and lower the count by one.

`strip_odd_count_pf`: an odd strip of a path-factor whose cells have neither `s` nor `t` as a
corner lowers the component count by one.
-/

namespace SolidGridHam

open Finset Classical

namespace HP

lemma inside_mono_right {V W : Finset Pt} {F : Finset Edge} (h : Inside V F) (hVW : V ⊆ W) :
    Inside W F := fun e he => ⟨hVW (h e he).1, hVW (h e he).2⟩

lemma isCell_mono {V W : Finset Pt} {c : Pt} (h : IsCell V c) (hVW : V ⊆ W) : IsCell W c :=
  ⟨hVW h.1, hVW h.2.1, hVW h.2.2.1, hVW h.2.2.2⟩

lemma sub_insST (V : Finset Pt) (s t : Pt) : V ⊆ insert s (insert t V) :=
  fun _ hz => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hz)

-- Edges inside `V`, except that an endpoint may lie outside `V` (a phantom endpoint, joined to
-- `V` by its edge). For endpoints in `V` this is `Inside V F`.
--
def InsideST (V : Finset Pt) (F : Finset Edge) (s t : Pt) : Prop :=
  Inside (insert s (insert t V)) F

lemma InsideST.of_inside {V : Finset Pt} {F : Finset Edge} {s t : Pt} (h : Inside V F) :
    InsideST V F s t :=
  inside_mono_right h (sub_insST V s t)

lemma InsideST.inside {V : Finset Pt} {F : Finset Edge} {s t : Pt} (h : InsideST V F s t)
    (hs : s ∈ V) (ht : t ∈ V) : Inside V F := by
  unfold InsideST at h; rwa [Finset.insert_eq_of_mem ht, Finset.insert_eq_of_mem hs] at h

lemma InsideST.flip {V : Finset Pt} {F : Finset Edge} {s t : Pt} (h : InsideST V F s t) {c : Pt}
    (hc : IsCell V c) : InsideST V (SolidGridHam.flip F c) s t :=
  inside_flip h (isCell_mono hc (sub_insST V s t))

lemma InsideST.conn_mem {V : Finset Pt} {F : Finset Edge} {s t : Pt} (h : InsideST V F s t)
    {a z : Pt} (ha : a ∈ V) (hc : Conn F a z) (hzs : z ≠ s) (hzt : z ≠ t) : z ∈ V := by
  have := SolidGridHam.conn_mem (V := insert s (insert t V)) h (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ha)) hc
  rcases Finset.mem_insert.1 this with h1 | h1
  · exact absurd h1 hzs
  rcases Finset.mem_insert.1 h1 with h2 | h2
  · exact absurd h2 hzt
  · exact h2

-- A point of `V ∪ {s, t}` is in `V` when `s ∈ V` and it is not a phantom `t`.
--
lemma memW {V : Finset Pt} {s t z : Pt} (hz : z ∈ insert s (insert t V)) (hs : s ∈ V)
    (ht : z = t → t ∈ V) : z ∈ V := by
  rcases Finset.mem_insert.1 hz with h | h
  · exact h ▸ hs
  rcases Finset.mem_insert.1 h with h' | h'
  · exact h' ▸ ht h'
  · exact h'

-- Inside `V` (up to phantom endpoints), and degree 2 at every point of `V` other than `s`, `t`.
--
def Deg2Off (V : Finset Pt) (F : Finset Edge) (s t : Pt) : Prop :=
  InsideST V F s t ∧ ∀ z ∈ V, z ≠ s → z ≠ t → deg F z = 2

lemma Deg2Off.flip {V : Finset Pt} {F : Finset Edge} {s t : Pt} (h : Deg2Off V F s t)
    (C : ACell) {c : Pt} (hc : IsCell V c) (hE : cellE c = {C.e1, C.e2, C.l1, C.l2})
    (h1 : C.e1 ∈ F) (h2 : C.e2 ∈ F) (h3 : C.l1 ∉ F) (h4 : C.l2 ∉ F) :
    Deg2Off V (SolidGridHam.flip F c) s t := by
  refine ⟨h.1.flip hc, fun z hz hs ht => ?_⟩
  rw [C.flip_eq hE h1 h2 h3 h4, C.deg_res h1 h2 h3 h4]
  exact h.2 z hz hs ht

-- The cell with its two dark sides exchanged.
--
def _root_.SolidGridHam.ACell.swap (C : ACell) : ACell where
  a := C.d
  b := C.k
  d := C.a
  k := C.b
  e1 := C.e2
  e2 := C.e1
  l1 := C.l1
  l2 := C.l2
  h1 := C.h2
  h2 := C.h1
  h3 := C.h3.swap
  h4 := C.h4.swap
  ad := C.ad.symm
  ak := C.bd.symm
  bd := C.ak.symm
  bk := C.bk.symm

lemma _root_.SolidGridHam.ACell.swap_res (C : ACell) (F : Finset Edge) : C.swap.res F = C.res F := by
  unfold ACell.res ACell.swap
  simp only
  rw [Finset.erase_right_comm]

section merge

variable {V W : Finset Pt} {F : Finset Edge} (C : ACell)
  (hV : Inside W F) (hVa : C.a ∈ V) (hVb : C.b ∈ V) (hVd : C.d ∈ V) (hVk : C.k ∈ V)
  (he1 : C.e1 ∈ F) (he2 : C.e2 ∈ F)

include hV hVa hVb hVd hVk he1 he2 in
-- **Merge, cycle on the `d` side.**
--
theorem merge_count_d (hdeg : ∀ z, Conn F C.d z → deg F z = 2) (hn : ¬ Conn F C.a C.d) :
    ncomp V (C.res F) + 1 = ncomp V F := by
  set G1 := F.erase C.e1 with hG1
  have hG1F : G1 ⊆ F := Finset.erase_subset _ _
  have he2' : C.e2 ∈ G1 := Finset.mem_erase.2 ⟨C.e2_ne_e1, he2⟩
  have hFab : Conn F C.a C.b := C.h1.conn he1
  have hdk : Conn (G1.erase C.e2) C.d C.k := by
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
  set G := G1.erase C.e2 with hG
  have hGF : G ⊆ F := (Finset.erase_subset _ _).trans hG1F
  have e2 : ncomp V G = ncomp V G1 := by
    conv_rhs => rw [← Finset.insert_erase he2']
    apply ncomp_congr; intro u _ v _; exact (C.h2.insert_conn hdk u v).symm
  have em : ncomp V (insert C.l1 G) + 1 = ncomp V G :=
    C.h3.merge hVa hVd (fun h => hn (h.mono hGF))
  have hres : C.res F = insert C.l2 (insert C.l1 G) := rfl
  by_cases hab : Conn G1 C.a C.b
  · -- `a`, `b` stay joined: the original count.
    have e1 : ncomp V G1 = ncomp V F := by
      conv_rhs => rw [← Finset.insert_erase he1]
      apply ncomp_congr; intro u _ v _; exact (C.h1.insert_conn hab u v).symm
    have habG : Conn G C.a C.b := by
      have : Conn (insert C.e2 G) C.a C.b := by rw [Finset.insert_erase he2']; exact hab
      rcases conn_insert.1 this with h | ⟨h1, _⟩ | ⟨h1, _⟩
      · exact h
      · have : Conn F C.a C.d ∨ Conn F C.a C.k := by
          rcases C.h2 with ⟨q1, _⟩ | ⟨q1, _⟩ <;> rw [q1] at h1
          · exact Or.inl (h1.mono hGF)
          · exact Or.inr (h1.mono hGF)
        rcases this with h | h
        · exact absurd h hn
        · exact absurd (h.trans (C.h2.conn he2).symm) hn
      · have : Conn F C.a C.d ∨ Conn F C.a C.k := by
          rcases C.h2 with ⟨_, q2⟩ | ⟨_, q2⟩ <;> rw [q2] at h1
          · exact Or.inr (h1.mono hGF)
          · exact Or.inl (h1.mono hGF)
        rcases this with h | h
        · exact absurd h hn
        · exact absurd (h.trans (C.h2.conn he2).symm) hn
    have hbk : Conn (insert C.l1 G) C.b C.k := by
      have s : G ⊆ insert C.l1 G := Finset.subset_insert _ _
      have hl' : Conn (insert C.l1 G) C.a C.d := C.h3.conn (Finset.mem_insert_self _ _)
      exact ((habG.mono s).symm.trans hl').trans (hdk.mono s)
    have er : ncomp V (C.res F) = ncomp V (insert C.l1 G) := by
      rw [hres]; apply ncomp_congr; intro u _ v _; exact C.h4.insert_conn hbk u v
    omega
  · -- `a`, `b` split when `e1` goes: up one, then `l2` joins them again.
    have e1 : ncomp V F + 1 = ncomp V G1 := by
      have := C.h1.merge hVa hVb hab
      rwa [Finset.insert_erase he1] at this
    have hnbk : ¬ Conn (insert C.l1 G) C.b C.k := by
      rw [C.h3.conn_insert_iff]
      have hFdk : Conn F C.d C.k := C.h2.conn he2
      rintro (h | ⟨h, _⟩ | ⟨h, _⟩)
      · exact hn (hFab.trans ((h.mono hGF).trans hFdk.symm))
      · exact hab ((h.mono (Finset.erase_subset _ _)).symm)
      · exact hn (hFab.trans (h.mono hGF))
    have er : ncomp V (C.res F) + 1 = ncomp V (insert C.l1 G) := by
      rw [hres]
      exact C.h4.merge hVb hVk hnbk
    omega

end merge

-- **Merge** when at least one of the two components is a cycle.
--
theorem merge_count {V W : Finset Pt} {F : Finset Edge} (C : ACell) (hV : Inside W F)
    (hVa : C.a ∈ V) (hVb : C.b ∈ V) (hVd : C.d ∈ V) (hVk : C.k ∈ V)
    (he1 : C.e1 ∈ F) (he2 : C.e2 ∈ F)
    (hcyc : (∀ z, Conn F C.d z → deg F z = 2) ∨ (∀ z, Conn F C.a z → deg F z = 2))
    (hn : ¬ Conn F C.a C.d) : ncomp V (C.res F) + 1 = ncomp V F := by
  rcases hcyc with h | h
  · exact merge_count_d C hV hVa hVb hVd hVk he1 he2 h hn
  · rw [← C.swap_res]
    exact merge_count_d C.swap hV hVd hVk hVa hVb he2 he1 h (fun h' => hn h'.symm)

lemma isCorner_front1 (c : Pt) (s : Side) : IsCorner (front1 c s) c := by
  obtain ⟨x, y⟩ := c; cases s <;> simp [IsCorner, front1]

lemma isCorner_front2 (c : Pt) (s : Side) : IsCorner (front2 c s) c := by
  obtain ⟨x, y⟩ := c; cases s <;> simp [IsCorner, front2]

lemma isCorner_back1 (c : Pt) (s : Side) : IsCorner (back1 c s) c := by
  obtain ⟨x, y⟩ := c; cases s <;> simp [IsCorner, back1]

lemma isCorner_back2 (c : Pt) (s : Side) : IsCorner (back2 c s) c := by
  obtain ⟨x, y⟩ := c; cases s <;> simp [IsCorner, back2]

-- In a path-factor (`s`, `t` joined), a class missing `s` consists of degree-2 points.
--
lemma class_deg2 {V : Finset Pt} {F : Finset Edge} {s t : Pt} (h : Deg2Off V F s t)
    (hst : Conn F s t) {a : Pt} (ha : a ∈ V) (hn : ¬ Conn F a s) :
    ∀ z, Conn F a z → deg F z = 2 := by
  intro z hz
  have hzs : z ≠ s := by rintro rfl; exact hn hz
  have hzt : z ≠ t := by rintro rfl; exact hn (hz.trans hst.symm)
  exact h.2 z (h.1.conn_mem ha hz hzs hzt) hzs hzt

section count

variable {V : Finset Pt} {c : Pt} {s : Side} {s0 t0 : Pt}

-- **Odd strip for path-factors**: if no cell of the strip has `s0` or `t0` as a corner, the
-- count drops by one.
--
theorem strip_odd_count_pf : ∀ k : ℕ, k % 2 = 0 → ∀ F : Finset Edge, Deg2Off V F s0 t0 →
    Conn F s0 t0 → (∀ j ≤ k, IsCell V (cellJ c s j)) →
    (∀ j ≤ k, ¬ IsCorner s0 (cellJ c s j) ∧ ¬ IsCorner t0 (cellJ c s j)) →
    StripPat F c s (k + 1) → ¬ Conn F (back1 c s) (front1 c s) →
    ncomp V (flipCol F c s (k + 1)) + 1 = ncomp V F := by
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
    exact merge_count (mkBF c s) hF.1 cb1 cb2 cf1 cf2 hb f0 hcyc hsep
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
    have ihc := ih m (by omega) hm _ hF2' hst2 (fun j hj => hcell j (by omega))
      (fun j hj => hcor j (by omega)) hpat2 hsep2
    omega

end count

end HP

end SolidGridHam
