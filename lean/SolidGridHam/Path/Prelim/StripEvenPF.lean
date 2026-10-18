/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import SolidGridHam.Path.Prelim.StripCountPF

/-!
# Even strips for path-factors (notes: Lemma B, part 3)

An even strip's last cell is flipped alone first. Its two dark sides lie in one class. For a
cycle this splits the class (`ACell.split`); on the s–t path the flip may instead only
reverse a piece of the path. `flip_same_count`: in every case the count goes up by 0 or 1,
and `flip_same_conn`: the flip never joins two classes. The count is read off single-edge
insertions; the connections among the four corners in `F` minus the two dark sides form one
of finitely many patterns, checked by `decide` (`part4`).

`conn_st`: in a path-factor (degree 1 at `s`, degree 2 at every other point but `t`), `s` and
`t` are joined (handshake per class), so this survives any degree-preserving flip.

`strip_even_count_pf`: an even strip whose cells have neither endpoint as a corner lowers the
count by 0 or 1.
-/

namespace SolidGridHam

open Finset Classical

namespace HP

lemma conn_comm {F : Finset Edge} {x y : Pt} : Conn F x y ↔ Conn F y x :=
  ⟨Conn.symm, Conn.symm⟩

-- Inserting an edge lowers the count by one exactly when its ends were apart.
--
lemma ins_count {V : Finset Pt} {X : Finset Edge} {e : Edge} {u v : Pt} (h : Ends e u v)
    (hu : u ∈ V) (hv : v ∈ V) :
    ncomp V (insert e X) + (if Conn X u v then 0 else 1) = ncomp V X := by
  by_cases hc : Conn X u v
  · simp only [hc, ↓reduceIte, add_zero]; apply ncomp_congr; intro x _ y _; exact h.insert_conn hc x y
  · simp only [hc, ↓reduceIte]; exact h.merge hu hv hc

-- The finite check. `ab … dk` are the connections among the corners `a b d k` in `F` minus
-- the dark sides `a–b`, `d–k` (an equivalence relation: the twelve transitivity conditions);
-- the light sides are `a–d`, `b–k`.
--
theorem part4 : ∀ ab ad ak bd bk dk : Bool,
    (!ab || !bd || ad) = true → (!ab || !ad || bd) = true → (!ad || !bd || ab) = true →
    (!ab || !bk || ak) = true → (!ab || !ak || bk) = true → (!ak || !bk || ab) = true →
    (!ad || !dk || ak) = true → (!ad || !ak || dk) = true → (!ak || !dk || ad) = true →
    (!bd || !dk || bk) = true → (!bd || !bk || dk) = true → (!bk || !dk || bd) = true →
    (ad || ak || bd || bk) = true →
    ((if ad then 0 else 1) + (if (bk || (ab && dk) || (bd && ak)) then 0 else 1) ≤
        (if dk then 0 else 1) + (if (ab || (ad && bk) || (ak && bd)) then 0 else 1) ∧
      (if dk then 0 else 1) + (if (ab || (ad && bk) || (ak && bd)) then 0 else 1) ≤
        (if ad then 0 else 1) + (if (bk || (ab && dk) || (bd && ak)) then 0 else 1) + 1) := by
  decide

lemma tri (F : Finset Edge) (x y z : Pt) :
    (!decide (Conn F x y) || !decide (Conn F y z) || decide (Conn F x z)) = true := by
  by_cases h1 : Conn F x y
  · by_cases h2 : Conn F y z
    · simp [h1.trans h2]
    · simp [h2]
  · simp [h1]

lemma dsymm (F : Finset Edge) (x y : Pt) : decide (Conn F x y) = decide (Conn F y x) := by
  by_cases h : Conn F x y
  · simp [h, h.symm]
  · have h' : ¬ Conn F y x := fun h'' => h h''.symm
    simp [h, h']

-- **Flipping a cell inside one class**: the count goes up by 0 or 1.
--
theorem flip_same_count {V : Finset Pt} {F : Finset Edge} (C : ACell)
    (hVa : C.a ∈ V) (hVb : C.b ∈ V) (hVd : C.d ∈ V) (hVk : C.k ∈ V)
    (he1 : C.e1 ∈ F) (he2 : C.e2 ∈ F) (hsame : Conn F C.a C.d) :
    ncomp V F ≤ ncomp V (C.res F) ∧ ncomp V (C.res F) ≤ ncomp V F + 1 := by
  set G := (F.erase C.e1).erase C.e2 with hG
  have he2' : C.e2 ∈ F.erase C.e1 := Finset.mem_erase.2 ⟨C.e2_ne_e1, he2⟩
  have hX : insert C.e2 G = F.erase C.e1 := Finset.insert_erase he2'
  have hFX : insert C.e1 (insert C.e2 G) = F := by rw [hX, Finset.insert_erase he1]
  have c1 := ins_count (X := G) C.h2 hVd hVk
  have c2 := ins_count (X := insert C.e2 G) C.h1 hVa hVb
  rw [hFX] at c2
  have c3 := ins_count (X := G) C.h3 hVa hVd
  have c4 := ins_count (X := insert C.l1 G) C.h4 hVb hVk
  have hres : C.res F = insert C.l2 (insert C.l1 G) := rfl
  rw [← hres] at c4
  have hB : Conn (insert C.e2 G) C.a C.b ↔
      Conn G C.a C.b ∨ (Conn G C.a C.d ∧ Conn G C.b C.k) ∨ (Conn G C.a C.k ∧ Conn G C.b C.d) := by
    rw [C.h2.conn_insert_iff, conn_comm (x := C.k), conn_comm (x := C.d) (y := C.b)]
  have hQ : Conn (insert C.l1 G) C.b C.k ↔
      Conn G C.b C.k ∨ (Conn G C.a C.b ∧ Conn G C.d C.k) ∨ (Conn G C.b C.d ∧ Conn G C.a C.k) := by
    rw [C.h3.conn_insert_iff, conn_comm (x := C.b) (y := C.a)]
  have hS : Conn G C.a C.d ∨ Conn G C.a C.k ∨ Conn G C.b C.d ∨ Conn G C.b C.k := by
    by_contra hn
    push Not at hn
    obtain ⟨n1, n2, n3, n4⟩ := hn
    have h0 := hsame
    rw [← hFX] at h0
    simp only [C.h1.conn_insert_iff, C.h2.conn_insert_iff] at h0
    have m2 : ¬ Conn G C.k C.a := fun h => n2 h.symm
    have m4 : ¬ Conn G C.k C.b := fun h => n4 h.symm
    have m1 : ¬ Conn G C.d C.a := fun h => n1 h.symm
    have m3 : ¬ Conn G C.d C.b := fun h => n3 h.symm
    tauto
  rw [hB] at c2
  rw [hQ] at c4
  have hp := part4 (decide (Conn G C.a C.b)) (decide (Conn G C.a C.d)) (decide (Conn G C.a C.k))
    (decide (Conn G C.b C.d)) (decide (Conn G C.b C.k)) (decide (Conn G C.d C.k))
    (tri G _ _ _) (by have := tri G C.b C.a C.d; rwa [dsymm G C.b C.a] at this)
    (by have := tri G C.a C.d C.b; rwa [dsymm G C.d C.b] at this)
    (tri G _ _ _) (by have := tri G C.b C.a C.k; rwa [dsymm G C.b C.a] at this)
    (by have := tri G C.a C.k C.b; rwa [dsymm G C.k C.b] at this)
    (tri G _ _ _) (by have := tri G C.d C.a C.k; rwa [dsymm G C.d C.a] at this)
    (by have := tri G C.a C.k C.d; rwa [dsymm G C.k C.d] at this)
    (tri G _ _ _) (by have := tri G C.d C.b C.k; rwa [dsymm G C.d C.b] at this)
    (by have := tri G C.b C.k C.d; rwa [dsymm G C.k C.d] at this)
    (by simp only [Bool.or_eq_true, decide_eq_true_eq]; tauto)
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, or_assoc] at hp
  split_ifs at c1 c2 c3 c4 hp <;> omega

-- An edge whose ends are joined in `F` adds no new connection.
--
lemma conn_of_ends {F : Finset Edge} {e : Edge} {u v x y : Pt} (h : Ends e u v)
    (huv : Conn F u v) (hxy : (e.p = x ∧ e.q = y) ∨ (e.p = y ∧ e.q = x)) : Conn F x y := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hxy with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
    rw [h1] at h3 <;> rw [h2] at h4 <;> subst h3 h4
  · exact huv
  · exact huv.symm
  · exact huv.symm
  · exact huv

-- **Flipping a cell inside one class never joins two classes.**
--
theorem flip_same_conn {F : Finset Edge} (C : ACell) (he1 : C.e1 ∈ F) (he2 : C.e2 ∈ F)
    (hsame : Conn F C.a C.d) : ∀ x y, Conn (C.res F) x y → Conn F x y := by
  have hbk : Conn F C.b C.k :=
    ((C.h1.conn he1).symm.trans hsame).trans (C.h2.conn he2)
  intro x y h
  induction h with
  | refl => exact Conn.refl _ _
  | tail _ hyz ih =>
    obtain ⟨f, hf, hfe⟩ := hyz
    unfold ACell.res at hf
    rcases Finset.mem_insert.1 hf with rfl | hf
    · exact ih.trans (conn_of_ends C.h4 hbk hfe)
    rcases Finset.mem_insert.1 hf with rfl | hf
    · exact ih.trans (conn_of_ends C.h3 hsame hfe)
    · have hfF : f ∈ F := (Finset.mem_erase.1 (Finset.mem_erase.1 hf).2).2
      exact ih.trans (Conn.of_adj ⟨f, hfF, hfe⟩)

-- **`s` and `t` are joined** in a path-factor (handshake per class).
--
lemma conn_st {V : Finset Pt} {F : Finset Edge} {s t : Pt} (h : Deg2Off V F s t) (_hs : s ∈ V)
    (hds : deg F s = 1) : Conn F s t := by
  by_contra hn
  set K := cls (insert s (insert t V)) F s with hK
  have hcl : Closed F K := closed_cls h.1 s
  have he := handshake hcl
  have hsK : s ∈ K := mem_cls_self (Finset.mem_insert_self _ _)
  rw [← Finset.add_sum_erase K _ hsK] at he
  have h2 : ∑ x ∈ K.erase s, deg F x = ∑ _x ∈ K.erase s, 2 := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.mem_erase] at hx
    obtain ⟨hxs, hxK⟩ := hx
    simp only [K, cls, Finset.mem_filter] at hxK
    have hxt : x ≠ t := by rintro rfl; exact hn hxK.2
    have hxV : x ∈ V := by
      rcases Finset.mem_insert.1 hxK.1 with h1 | h1
      · exact absurd h1 hxs
      rcases Finset.mem_insert.1 h1 with h2 | h2
      · exact absurd h2 hxt
      · exact h2
    exact h.2 x hxV hxs hxt
  rw [h2, Finset.sum_const, smul_eq_mul, hds] at he
  obtain ⟨r, hr⟩ := he
  omega

section count

variable {V : Finset Pt} {c : Pt} {s : Side} {s0 t0 : Pt}

-- **Even strip for path-factors**: if no cell of the strip has `s0` or `t0` as a corner and the
-- last cell is not a Type III cell, the count drops by 0 or 1.
--
theorem strip_even_count_pf (k : ℕ) (hk : k % 2 = 0) (F : Finset Edge) (hF : Deg2Off V F s0 t0)
    (hs0 : s0 ∈ V) (hds : deg F s0 = 1)
    (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j))
    (hcor : ∀ j ≤ k + 1, ¬ IsCorner s0 (cellJ c s j) ∧ ¬ IsCorner t0 (cellJ c s j))
    (hpat : StripPat F c s (k + 2)) (hsep : ¬ Conn F (back1 c s) (front1 c s))
    (hsame : Conn F (back1 (cellJ c s (k + 1)) s) (back2 (cellJ c s (k + 1)) s)) :
    ncomp V (flipCol F c s (k + 2)) ≤ ncomp V F ∧
      ncomp V F ≤ ncomp V (flipCol F c s (k + 2)) + 1 := by
  rw [flipCol_succ]
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
  rw [(mkLat u s).flip_eq hE uL1 uL2 uB uF]
  have hb2 := flip_same_count (V := V) (mkLat u s) ub1 uf1 ub2 uf2 uL1 uL2 hsame
  have hconn := flip_same_conn (mkLat u s) uL1 uL2 hsame
  have hF' : Deg2Off V ((mkLat u s).res F) s0 t0 := by
    rw [← (mkLat u s).flip_eq hE uL1 uL2 uB uF]
    exact hF.flip (mkLat u s) hcu hE uL1 uL2 uB uF
  have hds' : deg ((mkLat u s).res F) s0 = 1 := by
    rw [(mkLat u s).deg_res uL1 uL2 uB uF]; exact hds
  have hst' := conn_st hF' hs0 hds'
  have hpat' : StripPat ((mkLat u s).res F) c s (k + 1) := by
    rw [← (mkLat u s).flip_eq hE uL1 uL2 uB uF]; exact pat_flip_last hk ⟨hb, hl, hf⟩
  have hsep' : ¬ Conn ((mkLat u s).res F) (back1 c s) (front1 c s) :=
    fun h => hsep (hconn _ _ h)
  have := strip_odd_count_pf k hk _ hF' hst' (fun j hj => hcell j (by omega))
    (fun j hj => hcor j (by omega)) hpat' hsep'
  omega

end count

end HP

end SolidGridHam
