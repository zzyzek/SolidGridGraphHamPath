/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import SolidGridHam.Cycle.Flip

@[expose] public section

/-!
# Merge and split, stated for abstract corners

The proofs in `Flip.lean` use only: which of four named edges are in `F`, their ends, the
degrees, and (for the split) one planar fact. Here they are restated over abstract
corners `a b d k` and edges `e1 = a–b`, `e2 = d–k` (dark), `l1 = a–d`, `l2 = b–k` (light),
so that one proof serves every orientation of a cell. The planar fact enters as a
hypothesis and is discharged per orientation.
-/

namespace SolidGridHam

open Finset Classical

-- `e` joins `u` and `v`, in either order.
--
def Ends (e : Edge) (u v : Pt) : Prop := (e.p = u ∧ e.q = v) ∨ (e.p = v ∧ e.q = u)

section ends

variable {e : Edge} {u v : Pt}

lemma Ends.inc_iff (h : Ends e u v) (z : Pt) : (e.p = z ∨ e.q = z) ↔ (z = u ∨ z = v) := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> constructor <;> rintro (h | h) <;>
    simp_all

lemma Ends.conn_iff (h : Ends e u v) (F : Finset Edge) : Conn F e.p e.q ↔ Conn F u v := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
  exact ⟨Conn.symm, Conn.symm⟩

lemma Ends.conn {F : Finset Edge} (h : Ends e u v) (he : e ∈ F) : Conn F u v :=
  (h.conn_iff F).1 (Conn.of_edge he)

lemma Ends.ne (h : Ends e u v) : u ≠ v := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [← h1, ← h2]; exact Edge.p_ne_q e
  · rw [← h1, ← h2]; exact (Edge.p_ne_q e).symm

lemma Ends.insert_conn {F : Finset Edge} (h : Ends e u v) (hc : Conn F u v) (x y : Pt) :
    Conn (insert e F) x y ↔ Conn F x y :=
  conn_insert_of_conn ((h.conn_iff F).2 hc) x y

lemma Ends.conn_insert_iff {F : Finset Edge} (h : Ends e u v) (x y : Pt) :
    Conn (insert e F) x y ↔
      Conn F x y ∨ (Conn F x u ∧ Conn F v y) ∨ (Conn F x v ∧ Conn F u y) := by
  rw [conn_insert]
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
  tauto

lemma Ends.merge {V : Finset Pt} {F : Finset Edge} (h : Ends e u v) (hu : u ∈ V) (hv : v ∈ V)
    (hn : ¬ Conn F u v) : ncomp V (insert e F) + 1 = ncomp V F := by
  apply ncomp_insert_merge
  · rcases h with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1] <;> assumption
  · rcases h with ⟨_, h2⟩ | ⟨_, h2⟩ <;> rw [h2] <;> assumption
  · rwa [h.conn_iff]

lemma Ends.deg_erase {F : Finset Edge} (h : Ends e u v) (he : e ∈ F) (z : Pt) :
    deg (F.erase e) z + (if z = u ∨ z = v then 1 else 0) = deg F z := by
  have := SolidGridHam.deg_erase he z
  by_cases hz : z = u ∨ z = v
  · rw [ite_eq_left ((h.inc_iff z).2 hz)] at this; rw [ite_eq_left hz]; exact this
  · rw [ite_eq_right (fun h' => hz ((h.inc_iff z).1 h'))] at this; rw [ite_eq_right hz]; exact this

lemma Ends.erase_conn {V : Finset Pt} {F : Finset Edge} (hV : Inside V F) (h : Ends e u v)
    (he : e ∈ F) (heven : ∀ z ∈ V, Conn F u z → Even (deg F z)) : Conn (F.erase e) u v := by
  have huv : Conn F u v := h.conn he
  have := conn_erase_of_even hV he (by
    intro z hz hc
    apply heven z hz
    rcases h with ⟨h1, _⟩ | ⟨h1, _⟩
    · rwa [h1] at hc
    · rw [h1] at hc; exact huv.trans hc)
  exact (h.conn_iff _).1 this

end ends

/-! ## An abstract cell -/

structure ACell where
  a : Pt
  b : Pt
  d : Pt
  k : Pt
  e1 : Edge
  e2 : Edge
  l1 : Edge
  l2 : Edge
  h1 : Ends e1 a b
  h2 : Ends e2 d k
  h3 : Ends l1 a d
  h4 : Ends l2 b k
  ad : a ≠ d
  ak : a ≠ k
  bd : b ≠ d
  bk : b ≠ k

-- The edge set after flipping: drop the dark pair, add the light pair.
--
def ACell.res (C : ACell) (F : Finset Edge) : Finset Edge :=
  insert C.l2 (insert C.l1 ((F.erase C.e1).erase C.e2))

namespace ACell

variable (C : ACell)

lemma ab : C.a ≠ C.b := C.h1.ne
lemma dk : C.d ≠ C.k := C.h2.ne

lemma e2_ne_e1 : C.e2 ≠ C.e1 := by
  intro h
  have h2 := C.h2; rw [h] at h2
  have := (C.h1.inc_iff C.d).1 ((h2.inc_iff C.d).2 (Or.inl rfl))
  rcases this with h | h
  · exact C.ad h.symm
  · exact C.bd h.symm

end ACell

section abstract

variable {V : Finset Pt} {F : Finset Edge} (C : ACell)
  (hV : Inside V F) (hVa : C.a ∈ V) (hVb : C.b ∈ V) (hVd : C.d ∈ V) (hVk : C.k ∈ V)
  (he1 : C.e1 ∈ F) (he2 : C.e2 ∈ F) (hl1 : C.l1 ∉ F) (hl2 : C.l2 ∉ F)
  (hdeg2 : ∀ z, (Conn F C.a z ∨ Conn F C.d z) → deg F z = 2)
include hV hVa hVb hVd hVk he1 he2 hl1 hl2 hdeg2

-- **Merge** (abstract).
--
omit hVb hVk hl1 hl2 in
theorem ACell.merge (hn : ¬ Conn F C.a C.d) :
    ncomp V (C.res F) + 1 = ncomp V F ∧
      ∀ x y, Conn (C.res F) x y ↔
        Conn F x y ∨ (Conn F x C.a ∧ Conn F C.d y) ∨ (Conn F x C.d ∧ Conn F C.a y) := by
  set G1 := F.erase C.e1 with hG1
  have hG1F : G1 ⊆ F := Finset.erase_subset _ _
  have hab : Conn G1 C.a C.b :=
    C.h1.erase_conn hV he1 (fun z _ hz => by rw [hdeg2 z (Or.inl hz)]; exact even_two)
  have e1 : ncomp V G1 = ncomp V F := by
    conv_rhs => rw [← Finset.insert_erase he1]
    apply ncomp_congr; intro u _ v _; exact (C.h1.insert_conn hab u v).symm
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
    rw [this, hdeg2 z (Or.inr hzF)]; exact even_two
  set G := G1.erase C.e2 with hG
  have hGF : G ⊆ F := (Finset.erase_subset _ _).trans hG1F
  have e2 : ncomp V G = ncomp V G1 := by
    conv_rhs => rw [← Finset.insert_erase he2']
    apply ncomp_congr; intro u _ v _; exact (C.h2.insert_conn hdk u v).symm
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
  have em : ncomp V (insert C.l1 G) + 1 = ncomp V G :=
    C.h3.merge hVa hVd (fun h => hn (h.mono hGF))
  have hbk : Conn (insert C.l1 G) C.b C.k := by
    have s : G ⊆ insert C.l1 G := Finset.subset_insert _ _
    have hl' : Conn (insert C.l1 G) C.a C.d := C.h3.conn (Finset.mem_insert_self _ _)
    exact ((habG.mono s).symm.trans hl').trans (hdk.mono s)
  have er : ncomp V (C.res F) = ncomp V (insert C.l1 G) := by
    unfold ACell.res
    apply ncomp_congr; intro u _ v _; exact C.h4.insert_conn hbk u v
  refine ⟨by rw [er]; omega, fun x y => ?_⟩
  -- Connections: `G` has the same connections as `F`; then `l1` joins `a` and `d`.
  have cG1 : ∀ u v, Conn G1 u v ↔ Conn F u v := by
    intro u v
    have := C.h1.insert_conn hab u v
    rw [Finset.insert_erase he1] at this; exact this.symm
  have cG : ∀ u v, Conn G u v ↔ Conn G1 u v := by
    intro u v
    have := C.h2.insert_conn hdk u v
    rw [Finset.insert_erase he2'] at this
    exact this.symm
  have cGF : ∀ u v, Conn G u v ↔ Conn F u v := fun u v => (cG u v).trans (cG1 u v)
  unfold ACell.res
  rw [C.h4.insert_conn hbk, C.h3.conn_insert_iff, cGF, cGF, cGF, cGF, cGF]

-- **Split** (abstract). The planar fact is a hypothesis.
--
omit hl2 in
theorem ACell.split (hy : Conn F C.a C.d) (hle : ∀ z, deg F z ≤ 2)
    (hplanar : ∀ G : Finset Edge, C.e1 ∉ G → C.l1 ∉ G → Conn G C.b C.d → Conn G C.k C.a →
      ¬ Conn G C.a C.b → False) :
    ncomp V (C.res F) = ncomp V F + 1 ∧ (∀ u v, Conn (C.res F) u v → Conn F u v) ∧
      ∀ u v, Conn F u v ↔ Conn (C.res F) u v ∨ (Conn (C.res F) u C.a ∧ Conn (C.res F) C.b v) ∨
        (Conn (C.res F) u C.b ∧ Conn (C.res F) C.a v) := by
  set G1 := F.erase C.e1 with hG1
  have hG1F : G1 ⊆ F := Finset.erase_subset _ _
  have hab : Conn G1 C.a C.b :=
    C.h1.erase_conn hV he1 (fun z _ hz => by rw [hdeg2 z (Or.inl hz)]; exact even_two)
  have e1 : ncomp V G1 = ncomp V F := by
    conv_rhs => rw [← Finset.insert_erase he1]
    apply ncomp_congr; intro u _ v _; exact (C.h1.insert_conn hab u v).symm
  have he2' : C.e2 ∈ G1 := Finset.mem_erase.2 ⟨C.e2_ne_e1, he2⟩
  set G := G1.erase C.e2 with hG
  have hGF : G ⊆ F := (Finset.erase_subset _ _).trans hG1F
  have hVG : Inside V G := hV.mono hGF
  have he1G : C.e1 ∉ G := fun h => by simp [G, G1] at h
  have hl1G : C.l1 ∉ G := fun h => hl1 (hGF h)
  set S : Finset Pt := {C.a, C.b, C.d, C.k} with hS
  have hFab : Conn F C.a C.b := C.h1.conn he1
  have degG : ∀ z, Conn F C.a z → deg G z = if z ∈ S then 1 else 2 := by
    intro z hz
    have hz2 := hdeg2 z (Or.inl hz)
    have f1 := C.h1.deg_erase he1 z
    have f2 := C.h2.deg_erase he2' z
    rw [← hG1] at f1
    rw [← hG] at f2
    simp only [S, Finset.mem_insert, Finset.mem_singleton]
    by_cases za : z = C.a
    · subst za
      rw [ite_eq_left (Or.inl rfl)] at f1
      rw [ite_eq_right (by rintro (h | h); exact C.ad h; exact C.ak h)] at f2
      rw [ite_eq_left (Or.inl rfl)]; omega
    by_cases zb : z = C.b
    · subst zb
      rw [ite_eq_left (Or.inr rfl)] at f1
      rw [ite_eq_right (by rintro (h | h); exact C.bd h; exact C.bk h)] at f2
      rw [ite_eq_left (Or.inr (Or.inl rfl))]; omega
    rw [ite_eq_right (by rintro (h | h); exact za h; exact zb h)] at f1
    by_cases zd : z = C.d
    · subst zd
      rw [ite_eq_left (Or.inl rfl)] at f2
      rw [ite_eq_left (Or.inr (Or.inr (Or.inl rfl)))]; omega
    by_cases zk : z = C.k
    · subst zk
      rw [ite_eq_left (Or.inr rfl)] at f2
      rw [ite_eq_left (Or.inr (Or.inr (Or.inr rfl)))]; omega
    rw [ite_eq_right (by rintro (h | h); exact zd h; exact zk h)] at f2
    rw [ite_eq_right (by rintro (h | h | h | h) <;> contradiction)]; omega
  have hleG : ∀ z, deg G z ≤ 2 := by
    intro z
    have f1 := C.h1.deg_erase he1 z
    have f2 := C.h2.deg_erase he2' z
    rw [← hG1] at f1
    rw [← hG] at f2
    have := hle z
    omega
  have mem_cls : ∀ u w, w ∈ cls V G u ↔ w ∈ V ∧ Conn G u w := by
    intro u w; simp [cls]
  have cnt : ∀ K : Finset Pt, ((K ∩ S).card : ℕ) =
      (if C.a ∈ K then 1 else 0) + (if C.b ∈ K then 1 else 0) + (if C.d ∈ K then 1 else 0) +
        (if C.k ∈ K then 1 else 0) := by
    intro K
    rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.card_filter]
    rw [hS, Finset.sum_insert (by simp [C.ab, C.ad, C.ak]),
      Finset.sum_insert (by simp [C.bd, C.bk]),
      Finset.sum_insert (by simp [C.dk]), Finset.sum_singleton]
    ring
  have par : ∀ u, Conn F C.a u → Even ((cls V G u ∩ S).card) := by
    intro u hu
    apply class_parity hVG u S
    intro z hz
    rw [mem_cls] at hz
    exact degG z (hu.trans (hz.2.mono hGF))
  have leaf : ∀ u, Conn F C.a u → (cls V G u ∩ S).card ≤ 2 := by
    intro u hu
    have hl2 := leaves_le_two (V := V) _ G rfl hVG hleG u
    refine le_trans (Finset.card_le_card ?_) hl2
    intro z hz
    rw [Finset.mem_inter, mem_cls] at hz
    rw [Finset.mem_filter]
    refine ⟨hz.1.1, hz.1.2, ?_⟩
    rw [degG z (hu.trans (hz.1.2.mono hGF)), ite_eq_left hz.2]
  have aK : C.a ∈ cls V G C.a := mem_cls_self hVa
  have bK : C.b ∈ cls V G C.b := mem_cls_self hVb
  have pa := par C.a (Conn.refl _ _)
  have la := leaf C.a (Conn.refl _ _)
  have pb := par C.b hFab
  rw [cnt] at pa la pb
  rw [ite_eq_left aK] at pa la
  rw [ite_eq_left bK] at pb
  by_cases hbA : C.b ∈ cls V G C.a
  · exfalso
    rw [ite_eq_left hbA] at la pa
    have hdA : C.d ∉ cls V G C.a := by intro h; rw [ite_eq_left h] at la; split_ifs at la <;> omega
    have hkA : C.k ∉ cls V G C.a := by intro h; rw [ite_eq_left h] at la; split_ifs at la; omega
    have hcl : Closed F (cls V G C.a) := by
      intro u hu w huw
      obtain ⟨f, hf, hfw⟩ := huw
      have hw : Ends f u w := by
        rcases hfw with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨h1, h2⟩
        · exact Or.inr ⟨h1, h2⟩
      by_cases hfb : f = C.e1
      · subst hfb
        have hw' := (C.h1.inc_iff w).1 ((hw.inc_iff w).2 (Or.inr rfl))
        rcases hw' with rfl | rfl
        · exact aK
        · exact hbA
      by_cases hft : f = C.e2
      · subst hft
        have hu' := (C.h2.inc_iff u).1 ((hw.inc_iff u).2 (Or.inl rfl))
        rcases hu' with rfl | rfl
        · exact absurd hu hdA
        · exact absurd hu hkA
      · exact closed_cls hVG C.a u hu w
          ⟨f, Finset.mem_erase.2 ⟨hft, Finset.mem_erase.2 ⟨hfb, hf⟩⟩, hfw⟩
    exact hdA (closed_conn hcl aK hy)
  rw [ite_eq_right hbA] at la pa
  have hAB : ∀ w, w ∈ cls V G C.a → w ∉ cls V G C.b := by
    intro w hwa hwb
    apply hbA
    rw [mem_cls] at hwa hwb ⊢
    exact ⟨hVb, hwa.2.trans hwb.2.symm⟩
  have haB : C.a ∉ cls V G C.b := fun h => hAB C.a aK h
  rw [ite_eq_right haB] at pb
  by_cases hkA : C.k ∈ cls V G C.a
  · exfalso
    have hkB : C.k ∉ cls V G C.b := hAB C.k hkA
    rw [ite_eq_right hkB] at pb
    have hdB : C.d ∈ cls V G C.b := by
      by_contra h; rw [ite_eq_right h] at pb; simp at pb
    apply hplanar G he1G hl1G
    · exact ((mem_cls _ _).1 hdB).2
    · exact ((mem_cls _ _).1 hkA).2.symm
    · intro h; exact hbA ((mem_cls _ _).2 ⟨hVb, h⟩)
  · rw [ite_eq_right hkA] at la pa
    have hdA : C.d ∈ cls V G C.a := by
      by_contra h; rw [ite_eq_right h] at pa; simp at pa
    have hdB : C.d ∉ cls V G C.b := hAB C.d hdA
    rw [ite_eq_right hdB] at pb
    have hkB : C.k ∈ cls V G C.b := by
      by_contra h; rw [ite_eq_right h] at pb; simp at pb
    have hGad : Conn G C.a C.d := ((mem_cls _ _).1 hdA).2
    have hGbk : Conn G C.b C.k := ((mem_cls _ _).1 hkB).2
    have hGdk : ¬ Conn G C.d C.k := by
      intro h; exact hkA ((mem_cls _ _).2 ⟨hVk, hGad.trans h⟩)
    have em : ncomp V G1 + 1 = ncomp V G := by
      have := C.h2.merge (V := V) (F := G) hVd hVk hGdk
      rw [Finset.insert_erase he2'] at this
      exact this
    have s1 : G ⊆ insert C.l1 G := Finset.subset_insert _ _
    have cl : ∀ u v, Conn (insert C.l1 G) u v ↔ Conn G u v := C.h3.insert_conn hGad
    have cr : ∀ u v, Conn (C.res F) u v ↔ Conn (insert C.l1 G) u v :=
      C.h4.insert_conn (hGbk.mono s1)
    have el : ncomp V (insert C.l1 G) = ncomp V G := by
      apply ncomp_congr; intro u _ v _; exact cl u v
    have er : ncomp V (C.res F) = ncomp V (insert C.l1 G) := by
      apply ncomp_congr; intro u _ v _; exact cr u v
    have cRG : ∀ u v, Conn (C.res F) u v ↔ Conn G u v := fun u v => (cr u v).trans (cl u v)
    refine ⟨by rw [er, el]; omega, fun u v h => ((cRG u v).1 h).mono hGF, fun u v => ?_⟩
    -- `F` has the connections of `G1 = G + e2`, with `e2 = d–k`, `a ~ d`, `b ~ k` in `G`.
    have cG1 : ∀ u v, Conn G1 u v ↔ Conn F u v := by
      intro u v
      have := C.h1.insert_conn hab u v
      rw [Finset.insert_erase he1] at this; exact this.symm
    rw [← cG1, ← Finset.insert_erase he2', C.h2.conn_insert_iff, cRG, cRG, cRG, cRG, cRG]
    constructor
    · rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨h1.trans hGad.symm, hGbk.trans h2⟩)
      · exact Or.inr (Or.inr ⟨h1.trans hGbk.symm, hGad.trans h2⟩)
    · rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨h1.trans hGad, hGbk.symm.trans h2⟩)
      · exact Or.inr (Or.inr ⟨h1.trans hGbk, hGad.symm.trans h2⟩)

end abstract

-- Two edges differ when an end of one is not an end of the other.
--
lemma Ends.swap {e : Edge} {u v : Pt} (h : Ends e u v) : Ends e v u := by
  rcases h with h | h
  · exact Or.inr h
  · exact Or.inl h

lemma Ends.ne_of {e e' : Edge} {u v u' v' : Pt} (h : Ends e u v) (h' : Ends e' u' v')
    (h1 : v' ≠ u) (h2 : v' ≠ v) : e ≠ e' := by
  intro heq
  subst heq
  rcases (h.inc_iff v').1 ((h'.inc_iff v').2 (Or.inr rfl)) with h | h
  · exact h1 h
  · exact h2 h

/-! ## Degree 2: the incident edges are exactly two -/

lemma inc_of_deg_two {F : Finset Edge} {z : Pt} (hd : deg F z = 2) {e e' f : Edge}
    (he : e ∈ F) (hz : e.p = z ∨ e.q = z) (he' : e' ∈ F) (hz' : e'.p = z ∨ e'.q = z)
    (hne : e ≠ e') (hf : f ∈ F) (hzf : f.p = z ∨ f.q = z) : f = e ∨ f = e' := by
  by_contra h
  push Not at h
  have h1 := SolidGridHam.deg_erase he z
  rw [ite_eq_left hz] at h1
  have he'' : e' ∈ F.erase e := Finset.mem_erase.2 ⟨hne.symm, he'⟩
  have h2 := SolidGridHam.deg_erase he'' z
  rw [ite_eq_left hz'] at h2
  have hf' : f ∈ (F.erase e).erase e' :=
    Finset.mem_erase.2 ⟨h.2, Finset.mem_erase.2 ⟨h.1, hf⟩⟩
  have h3 := one_le_deg hf' hzf
  omega

/-! ## Flipping a U-shaped cell and the alternating cell beside it (thesis Lemma 5.3) -/

-- Six corners: `a b` (far side of the U), `m1 m2` (the shared side), `t1 t2` (far side of
-- the alternating cell). Before: `a–m1`, `b–m2`, `m1–m2`, `t1–t2` dark, `a–b`, `m1–t1`,
-- `m2–t2` light. After: the six outer edges swap.
--
structure APair where
  a : Pt
  b : Pt
  m1 : Pt
  m2 : Pt
  t1 : Pt
  t2 : Pt
  eab : Edge
  eam : Edge
  ebm : Edge
  em : Edge
  et : Edge
  emt1 : Edge
  emt2 : Edge
  hab : Ends eab a b
  ham : Ends eam a m1
  hbm : Ends ebm b m2
  hm : Ends em m1 m2
  ht : Ends et t1 t2
  hmt1 : Ends emt1 m1 t1
  hmt2 : Ends emt2 m2 t2
  -- `m1`, `m2` differ from the other four corners.
  m1a : m1 ≠ a
  m1b : m1 ≠ b
  m1t1 : m1 ≠ t1
  m1t2 : m1 ≠ t2
  m2a : m2 ≠ a
  m2b : m2 ≠ b
  m2t1 : m2 ≠ t1
  m2t2 : m2 ≠ t2

def APair.res (P : APair) (F : Finset Edge) : Finset Edge :=
  (insert P.emt2 (insert P.emt1
    (((insert P.eab F).erase P.eam).erase P.ebm))).erase P.et

section pair

variable {V : Finset Pt} {F : Finset Edge} (P : APair)
  (hV : Inside V F) (hVa : P.a ∈ V) (hVb : P.b ∈ V) (hVm1 : P.m1 ∈ V) (hVm2 : P.m2 ∈ V)
  (hVt1 : P.t1 ∈ V) (hVt2 : P.t2 ∈ V)
  (heam : P.eam ∈ F) (hebm : P.ebm ∈ F) (hem : P.em ∈ F) (het : P.et ∈ F)
  (hd1 : deg F P.m1 = 2) (hd2 : deg F P.m2 = 2)
include hV hVa hVb hVm1 hVm2 hVt1 hVt2 heam hebm hem het hd1 hd2

omit hV hVa hVt2 in
theorem APair.flip :
    ncomp V (P.res F) = ncomp V F ∧
      ∀ x y, x ≠ P.m1 → x ≠ P.m2 → y ≠ P.m1 → y ≠ P.m2 →
        (Conn (P.res F) x y ↔ Conn F x y) := by
  -- Edges at `m1` and `m2` in `F`.
  have neq1 : P.eam ≠ P.em := P.ham.ne_of P.hm P.m2a (fun h => P.hm.ne h.symm)
  have neq2 : P.ebm ≠ P.em := (P.hm.ne_of P.hbm.swap P.m1b.symm P.m2b.symm).symm
  have at1 : ∀ f ∈ F, (f.p = P.m1 ∨ f.q = P.m1) → f = P.eam ∨ f = P.em := fun f hf hz =>
    inc_of_deg_two hd1 heam ((P.ham.inc_iff _).2 (Or.inr rfl)) hem
      ((P.hm.inc_iff _).2 (Or.inl rfl)) neq1 hf hz
  have at2 : ∀ f ∈ F, (f.p = P.m2 ∨ f.q = P.m2) → f = P.ebm ∨ f = P.em := fun f hf hz =>
    inc_of_deg_two hd2 hebm ((P.hbm.inc_iff _).2 (Or.inr rfl)) hem
      ((P.hm.inc_iff _).2 (Or.inr rfl)) neq2 hf hz
  -- Step 1: insert `a–b` (already joined through `m1`, `m2`).
  have cab : Conn F P.a P.b :=
    ((P.ham.conn heam).trans (P.hm.conn hem)).trans (P.hbm.conn hebm).symm
  set F1 := insert P.eab F with hF1
  have c1 : ∀ x y, Conn F1 x y ↔ Conn F x y := P.hab.insert_conn cab
  -- Step 2: erase `a–m1` (still joined through `b`, `m2`).
  have hamF1 : P.eam ∈ F1 := Finset.mem_insert_of_mem heam
  set F2 := F1.erase P.eam with hF2
  have eab_ne : P.eab ≠ P.eam := (P.hab.ne_of P.ham P.m1a P.m1b)
  have cam2 : Conn F2 P.a P.m1 := by
    have s1 : Conn F2 P.a P.b := P.hab.conn (Finset.mem_erase.2 ⟨eab_ne, Finset.mem_insert_self _ _⟩)
    have s2 : Conn F2 P.b P.m2 := P.hbm.conn (Finset.mem_erase.2
      ⟨(P.ham.ne_of P.hbm P.m2a (fun h => P.hm.ne h.symm)).symm, Finset.mem_insert_of_mem hebm⟩)
    have s3 : Conn F2 P.m2 P.m1 :=
      (P.hm.conn (Finset.mem_erase.2 ⟨neq1.symm, Finset.mem_insert_of_mem hem⟩)).symm
    exact (s1.trans s2).trans s3
  have c2 : ∀ x y, Conn F2 x y ↔ Conn F1 x y := by
    intro x y
    have := P.ham.insert_conn cam2 x y
    rw [Finset.insert_erase hamF1] at this
    exact this.symm
  -- Step 3: erase `b–m2`; now `{m1, m2}` is a class of its own.
  have hebmF2 : P.ebm ∈ F2 := Finset.mem_erase.2
    ⟨(P.ham.ne_of P.hbm P.m2a (fun h => P.hm.ne h.symm)).symm, Finset.mem_insert_of_mem hebm⟩
  set F3 := F2.erase P.ebm with hF3
  have F3sub : ∀ f ∈ F3, f ∈ F ∧ f ≠ P.eam ∧ f ≠ P.ebm ∨ f = P.eab := by
    intro f hf
    simp only [F3, F2, F1, Finset.mem_erase, Finset.mem_insert] at hf
    obtain ⟨h1, h2, h3 | h3⟩ := hf
    · exact Or.inr h3
    · exact Or.inl ⟨h3, h2, h1⟩
  set K : Finset Pt := {P.m1, P.m2} with hK
  have eab_m1 : ¬ (P.eab.p = P.m1 ∨ P.eab.q = P.m1) := fun h => by
    rcases (P.hab.inc_iff _).1 h with h | h
    · exact P.m1a h
    · exact P.m1b h
  have eab_m2 : ¬ (P.eab.p = P.m2 ∨ P.eab.q = P.m2) := fun h => by
    rcases (P.hab.inc_iff _).1 h with h | h
    · exact P.m2a h
    · exact P.m2b h
  have closedK : Closed F3 K := by
    intro u hu w huw
    obtain ⟨f, hf, hfw⟩ := huw
    have hfu : f.p = u ∨ f.q = u := by
      rcases hfw with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact Or.inl h1
      · exact Or.inr h2
    have hfw' : f.p = w ∨ f.q = w := by
      rcases hfw with ⟨_, h2⟩ | ⟨h1, _⟩
      · exact Or.inr h2
      · exact Or.inl h1
    have hfm : f = P.em := by
      simp only [K, Finset.mem_insert, Finset.mem_singleton] at hu
      rcases F3sub f hf with ⟨hfF, hne1, hne2⟩ | rfl
      · rcases hu with rfl | rfl
        · rcases at1 f hfF hfu with h | h
          · exact absurd h hne1
          · exact h
        · rcases at2 f hfF hfu with h | h
          · exact absurd h hne2
          · exact h
      · rcases hu with rfl | rfl
        · exact absurd hfu eab_m1
        · exact absurd hfu eab_m2
    subst hfm
    rcases (P.hm.inc_iff w).1 hfw' with rfl | rfl <;> simp [K]
  have m1K : P.m1 ∈ K := by simp [K]
  have m2K : P.m2 ∈ K := by simp [K]
  have notK : ∀ z, z ∉ K → ∀ w ∈ K, ¬ Conn F3 w z := fun z hz w hw h =>
    hz (closed_conn closedK hw h)
  have bK : P.b ∉ K := by simp [K, P.m1b.symm, P.m2b.symm]
  have t1K : P.t1 ∉ K := by simp [K, P.m1t1.symm, P.m2t1.symm]
  have e3 : ncomp V F2 + 1 = ncomp V F3 := by
    have := P.hbm.merge (V := V) (F := F3) hVb hVm2 (fun h => notK _ bK _ m2K h.symm)
    rwa [Finset.insert_erase hebmF2] at this
  have c3 : ∀ x y, x ∉ K → y ∉ K → (Conn F2 x y ↔ Conn F3 x y) := by
    intro x y hx hy
    rw [← Finset.insert_erase hebmF2, conn_insert]
    constructor
    · rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact h
      · exfalso
        rcases P.hbm with ⟨q1, q2⟩ | ⟨q1, q2⟩
        · rw [q2] at h2; exact notK _ hy _ m2K h2
        · rw [q1] at h1; exact notK _ hx _ m2K h1.symm
      · exfalso
        rcases P.hbm with ⟨q1, q2⟩ | ⟨q1, q2⟩
        · rw [q2] at h1; exact notK _ hx _ m2K h1.symm
        · rw [q1] at h2; exact notK _ hy _ m2K h2
    · exact fun h => Or.inl h
  -- Step 4: insert `m1–t1` (merges `{m1, m2}` into `t1`'s class).
  set F4 := insert P.emt1 F3 with hF4
  have e4 : ncomp V F4 + 1 = ncomp V F3 :=
    P.hmt1.merge hVm1 hVt1 (fun h => notK _ t1K _ m1K h)
  have c4 : ∀ x y, x ∉ K → y ∉ K → (Conn F4 x y ↔ Conn F3 x y) := by
    intro x y hx hy
    rw [conn_insert]
    constructor
    · rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact h
      · exfalso
        rcases P.hmt1 with ⟨q1, q2⟩ | ⟨q1, q2⟩
        · rw [q1] at h1; exact notK _ hx _ m1K h1.symm
        · rw [q2] at h2; exact notK _ hy _ m1K h2
      · exfalso
        rcases P.hmt1 with ⟨q1, q2⟩ | ⟨q1, q2⟩
        · rw [q1] at h2; exact notK _ hy _ m1K h2
        · rw [q2] at h1; exact notK _ hx _ m1K h1.symm
    · exact fun h => Or.inl h
  -- Membership facts in `F3`.
  have emF3 : P.em ∈ F3 := by
    simp only [F3, F2, F1, Finset.mem_erase, Finset.mem_insert]
    exact ⟨neq2.symm, neq1.symm, Or.inr hem⟩
  have et_ne_am : P.et ≠ P.eam := P.ht.ne_of P.ham P.m1t1 P.m1t2
  have et_ne_bm : P.et ≠ P.ebm := P.ht.ne_of P.hbm P.m2t1 P.m2t2
  have etF3 : P.et ∈ F3 := by
    simp only [F3, F2, F1, Finset.mem_erase, Finset.mem_insert]
    exact ⟨et_ne_bm, et_ne_am, Or.inr het⟩
  -- Step 5: insert `m2–t2` (inside a class).
  have s34 : F3 ⊆ F4 := Finset.subset_insert _ _
  have c45 : Conn F4 P.m2 P.t2 :=
    (((P.hm.conn (s34 emF3)).symm.trans (P.hmt1.conn (Finset.mem_insert_self _ _))).trans
      (P.ht.conn (s34 etF3)))
  set F5 := insert P.emt2 F4 with hF5
  have c5 : ∀ x y, Conn F5 x y ↔ Conn F4 x y := P.hmt2.insert_conn c45
  -- Step 6: erase `t1–t2` (still joined through `m1`, `m2`).
  have etF5 : P.et ∈ F5 := Finset.mem_insert_of_mem (s34 etF3)
  set F6 := F5.erase P.et with hF6
  have c56 : Conn F6 P.t1 P.t2 := by
    have a1 : P.emt1 ∈ F6 := Finset.mem_erase.2
      ⟨(P.ht.ne_of P.hmt1.swap P.m1t1 P.m1t2).symm,
        Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)⟩
    have a2 : P.em ∈ F6 := Finset.mem_erase.2
      ⟨(P.ht.ne_of P.hm P.m2t1 P.m2t2).symm, Finset.mem_insert_of_mem (s34 emF3)⟩
    have a3 : P.emt2 ∈ F6 := Finset.mem_erase.2
      ⟨(P.ht.ne_of P.hmt2.swap P.m2t1 P.m2t2).symm, Finset.mem_insert_self _ _⟩
    exact ((P.hmt1.conn a1).symm.trans (P.hm.conn a2)).trans (P.hmt2.conn a3)
  have c6 : ∀ x y, Conn F6 x y ↔ Conn F5 x y := by
    intro x y
    have := P.ht.insert_conn c56 x y
    rw [Finset.insert_erase etF5] at this
    exact this.symm
  have hres : P.res F = F6 := rfl
  -- Assemble.
  have n1 : ncomp V F1 = ncomp V F := ncomp_congr (fun u _ v _ => c1 u v)
  have n2 : ncomp V F2 = ncomp V F1 := ncomp_congr (fun u _ v _ => c2 u v)
  have n5 : ncomp V F5 = ncomp V F4 := ncomp_congr (fun u _ v _ => c5 u v)
  have n6 : ncomp V F6 = ncomp V F5 := ncomp_congr (fun u _ v _ => c6 u v)
  refine ⟨by rw [hres]; omega, ?_⟩
  intro x y hx1 hx2 hy1 hy2
  have hx : x ∉ K := by simp [K, hx1, hx2]
  have hy : y ∉ K := by simp [K, hy1, hy2]
  rw [hres, c6, c5, c4 x y hx hy, ← c3 x y hx hy, c2, c1]

end pair

end SolidGridHam
