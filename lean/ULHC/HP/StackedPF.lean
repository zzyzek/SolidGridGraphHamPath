/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.Stacked
import ULHC.HP.ChainTg
import ULHC.HP.TouchLoc

/-!
# Twists as connections, and stacked cells (for rule Tg)

* `ncomp_lt_of_refine`: a refinement of the classes that separates two joined points has more
  classes.
* `twists_iff_conn`: an alternating cell with its lateral sides in one class twists (count
  unchanged by its flip) exactly when its lateral corners stay joined after the flip.
* `stacked_split_le`: ULHC's `stacked_split` with degree at most 2 only.
* `stacked_twist`: of two stacked alternating cells, one twists iff the other does (case G1 of the
  Tg port: no twist ending at the cell beyond a neutral strip's end cell).
-/

namespace ULHC

namespace HP

open Finset Classical

-- **Strict refinement raises the count.**
--
theorem ncomp_lt_of_refine {V : Finset Pt} {F F' : Finset Edge}
    (href : ∀ x ∈ V, ∀ y ∈ V, Conn F' x y → Conn F x y) {a b : Pt} (ha : a ∈ V) (hb : b ∈ V)
    (hab : Conn F a b) (hn : ¬ Conn F' a b) : ncomp V F < ncomp V F' := by
  unfold ncomp
  set A := V.image (cls V F')
  set f : Finset Pt → Finset Pt := fun S => if h : S.Nonempty then cls V F h.choose else ∅
  have hfx : ∀ x ∈ V, f (cls V F' x) = cls V F x := by
    intro x hx
    have hne : (cls V F' x).Nonempty := ⟨x, mem_cls_self hx⟩
    simp only [f, dite_eq_left hne]
    have hc := hne.choose_spec
    simp only [cls, Finset.mem_filter] at hc
    exact (cls_eq_of_conn (href x hx _ hc.1 hc.2)).symm
  have hB : V.image (cls V F) = A.image f := by
    ext S
    simp only [A, Finset.mem_image]
    constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨cls V F' x, ⟨x, hx, rfl⟩, hfx x hx⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩; exact ⟨x, hx, (hfx x hx).symm⟩
  rw [hB]
  have hnot : ¬ Set.InjOn f A := by
    intro hinj
    have hma : cls V F' a ∈ A := Finset.mem_image.2 ⟨a, ha, rfl⟩
    have hmb : cls V F' b ∈ A := Finset.mem_image.2 ⟨b, hb, rfl⟩
    have heq := hinj hma hmb (by rw [hfx a ha, hfx b hb]; exact cls_eq_of_conn hab)
    have : b ∈ cls V F' a := by rw [heq]; exact mem_cls_self hb
    simp only [cls, Finset.mem_filter] at this
    exact hn this.2
  have hle := Finset.card_image_le (s := A) (f := f)
  have hne : (A.image f).card ≠ A.card := fun h => hnot (Finset.card_image_iff.1 h)
  omega

-- **A twist is a flip that keeps the lateral corners joined.**
--
theorem twists_iff_conn {V : Finset Pt} {F : Finset Edge} {u : Pt} {s : Side} (hu : IsCell V u)
    (l1 : lat1 u s ∈ F) (l2 : lat2 u s ∈ F) (bu : back u s ∉ F) (fu : front u s ∉ F)
    (hsame : Conn F (back1 u s) (back2 u s)) :
    ncomp V (flip F u) = ncomp V F ↔ Conn (flip F u) (back1 u s) (front1 u s) := by
  have hE := mkLat_cellE u s
  rw [(mkLat u s).flip_eq hE l1 l2 bu fu]
  have hconn := flip_same_conn (mkLat u s) l1 l2 hsame
  have hrel := split_rel_pf (mkLat u s) l1 l2 hsame
  obtain ⟨ub1, ub2, uf1, uf2⟩ := isCell_corners hu s
  constructor
  · intro heq
    by_contra hn
    have hlt := ncomp_lt_of_refine (V := V) (fun x _ y _ h => hconn x y h) ub1 uf1
      ((ends_lat1 u s).conn l1) hn
    omega
  · intro hj
    apply (ncomp_congr fun x _ y _ => ?_).symm
    rw [hrel x y]
    constructor
    · rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact h
      · exact (h1.trans hj).trans h2
      · exact (h1.trans hj.symm).trans h2
    · exact fun h => Or.inl h

-- **`stacked_split` with degree at most 2.**
--
theorem stacked_split_le {V : Finset Pt} {F : Finset Edge} (hle : ∀ z, deg F z ≤ 2) {e : Pt} {s : Side}
    (he : IsCell V e) (_hu : IsCell V (nb e s))
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
  have hleE : ∀ z, deg (flip F e) z ≤ 2 := fun z => by
    rw [(mkLat e s).flip_eq (mkLat_cellE e s) el1 el2 eb ef, (mkLat e s).deg_res el1 el2 eb ef]; exact hle z
  have hleU : ∀ z, deg (flip F u) z ≤ 2 := fun z => by
    rw [(mkLat u s).flip_eq (mkLat_cellE u s) ul1 ul2 ub uf, (mkLat u s).deg_res ul1 ul2 ub uf]; exact hle z
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
      (hleE _) (hleE _) ?_ ?_ hp1 hp2 hq1 hq2
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
      (hleU _) (hleU _) ?_ ?_ hp1 hp2 hq1 hq2
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

-- **Stacked twists.** Two stacked alternating cells with their lateral sides in one class: one
-- twists exactly when the other does. Joining `back1 e` to `front1 e` after flipping `e` is the
-- same as joining it to `front1 u` (along `lat1 u`), and after flipping `u` the corner `m1` is
-- joined to `back1 e` along `lat1 e`, so both reduce to `stacked_split_le` on the outer corners.
--
theorem stacked_twist {V : Finset Pt} {F : Finset Edge} (hle : ∀ z, deg F z ≤ 2) {e : Pt}
    {s : Side} (he : IsCell V e) (hu : IsCell V (nb e s))
    (el1 : lat1 e s ∈ F) (el2 : lat2 e s ∈ F) (eb : back e s ∉ F) (ef : front e s ∉ F)
    (ul1 : lat1 (nb e s) s ∈ F) (ul2 : lat2 (nb e s) s ∈ F) (uf : front (nb e s) s ∉ F)
    (hsame : Conn F (front1 e s) (front2 e s)) :
    ncomp V (flip F e) = ncomp V F ↔ ncomp V (flip F (nb e s)) = ncomp V F := by
  have ub : back (nb e s) s ∉ F := by rw [back_nb]; exact ef
  have hsE : Conn F (back1 e s) (back2 e s) :=
    (((ends_lat1 e s).conn el1).trans hsame).trans ((ends_lat2 e s).conn el2).symm
  have hsU : Conn F (back1 (nb e s) s) (back2 (nb e s) s) := by
    rw [back1_nb, back2_nb]; exact hsame
  rw [twists_iff_conn he el1 el2 eb ef hsE, twists_iff_conn hu ul1 ul2 ub uf hsU, back1_nb]
  have hA : Conn (flip F e) (front1 e s) (front1 (nb e s) s) := by
    have := (ends_lat1 (nb e s) s).conn
      (mem_flip_iff.2 ⟨fun _ => stk_lat1_up e s, fun _ => ul1⟩ : lat1 (nb e s) s ∈ flip F e)
    rwa [back1_nb] at this
  have hB : Conn (flip F (nb e s)) (back1 e s) (front1 e s) :=
    (ends_lat1 e s).conn (mem_flip_iff.2 ⟨fun _ => stk_lat1_dn e s, fun _ => el1⟩)
  have hq1 : front1 (nb e s) s ≠ front1 e s := by
    have := (ends_lat1 (nb e s) s).ne; rw [back1_nb] at this; exact this.symm
  have key := stacked_split_le hle he hu el1 el2 eb ef ul1 ul2 uf
    (ends_lat1 e s).ne (stk_b1_f2 e s) hq1 (stk_f1_f2 e s)
  constructor
  · intro h; exact hB.symm.trans (key.1 (h.trans hA))
  · intro h; exact (key.2 (hB.trans h)).trans hA.symm

-- **Case G1.** If `e` splits, the stacked cell `nb e s` does not twist.
--
theorem stacked_no_twist {V : Finset Pt} {F : Finset Edge} (hle : ∀ z, deg F z ≤ 2) {e : Pt}
    {s : Side} (he : IsCell V e) (hu : IsCell V (nb e s))
    (el1 : lat1 e s ∈ F) (el2 : lat2 e s ∈ F) (eb : back e s ∉ F) (ef : front e s ∉ F)
    (ul1 : lat1 (nb e s) s ∈ F) (ul2 : lat2 (nb e s) s ∈ F) (uf : front (nb e s) s ∉ F)
    (hsame : Conn F (front1 e s) (front2 e s))
    (hsp : ncomp V (flip F e) = ncomp V F + 1) : ¬ TwistsIn V F (nb e s) := by
  rintro ⟨_, h⟩
  have := (stacked_twist hle he hu el1 el2 eb ef ul1 ul2 uf hsame).2 h
  omega

end HP

end ULHC
