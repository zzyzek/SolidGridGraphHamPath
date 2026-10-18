/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import SolidGridHam.Basic.Graph

@[expose] public section

/-!
# Flipping one alternating cell: merge or split

Cell `c = (x, y)` with corners `a = (x, y)`, `b = (x+1, y)`, `d = (x, y+1)`, `k = (x+1, y+1)`.
Its bottom (`a–b`) and top (`d–k`) are in `F`, its left (`a–d`) and right (`b–k`) are not.
Assume every vertex in the classes of `a` and `d` has degree 2 (so both dark edges lie on
cycles; for a path-factor this excludes the path), and all degrees are at most 2.

* If `a` and `d` are in different classes, flipping `c` merges them: count − 1.
* If they are in the same class, flipping `c` splits it: count + 1. The planar lemma rules
  out the twisted reconnection.

The other orientation (left and right sides dark) is obtained by symmetry later.
-/

namespace SolidGridHam

open Finset Classical

lemma closed_conn {F : Finset Edge} {K : Finset Pt} (hK : Closed F K) {x y : Pt} (hx : x ∈ K)
    (h : Conn F x y) : y ∈ K := by
  induction h with
  | refl => exact hx
  | tail _ hyz ih => exact hK _ ih _ hyz

-- Parity of the odd-degree vertices in a class, when degrees there are 1 (on `S`) or 2.
--
lemma class_parity {V : Finset Pt} {G : Finset Edge} (hV : Inside V G) (x : Pt) (S : Finset Pt)
    (h : ∀ z ∈ cls V G x, deg G z = if z ∈ S then 1 else 2) :
    Even ((cls V G x ∩ S).card) := by
  have hs := handshake (closed_cls hV x)
  have e1 : ∑ z ∈ cls V G x, deg G z =
      ∑ z ∈ cls V G x, (2 - (if z ∈ S then 1 else 0)) := by
    apply Finset.sum_congr rfl; intro z hz; rw [h z hz]; split_ifs <;> rfl
  have e2 : ∑ z ∈ cls V G x, (2 - (if z ∈ S then 1 else 0)) + (cls V G x ∩ S).card =
      2 * (cls V G x).card := by
    have e3 : (cls V G x ∩ S).card = ∑ z ∈ cls V G x, (if z ∈ S then 1 else 0) := by
      rw [Finset.sum_boole, Nat.cast_id, Finset.filter_mem_eq_inter]
    rw [e3, ← Finset.sum_add_distrib, Finset.card_eq_sum_ones, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro z _; split_ifs <;> rfl
  rw [e1] at hs
  obtain ⟨r, hr⟩ := hs
  refine ⟨(cls V G x).card - r, ?_⟩
  omega

lemma flip_eq {F : Finset Edge} {c : Pt} (hb : bot c ∈ F) (ht : top c ∈ F) (hl : lft c ∉ F)
    (hr : rgt c ∉ F) :
    flip F c = insert (rgt c) (insert (lft c) ((F.erase (bot c)).erase (top c))) := by
  obtain ⟨x, y⟩ := c
  ext e
  simp only [flip, cellE, Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton,
    Finset.mem_erase]
  constructor
  · rintro (⟨he, hn⟩ | ⟨hn, he⟩)
    · push Not at hn; exact Or.inr (Or.inr ⟨hn.2.1, hn.1, he⟩)
    · rcases hn with rfl | rfl | rfl | rfl
      · exact absurd hb he
      · exact absurd ht he
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl rfl
  · rintro (rfl | rfl | ⟨h1, h2, he⟩)
    · exact Or.inr ⟨by simp [rgt, bot, top, lft], hr⟩
    · exact Or.inr ⟨by simp [rgt, bot, top, lft], hl⟩
    · refine Or.inl ⟨he, ?_⟩
      rintro (rfl | rfl | rfl | rfl)
      · exact h2 rfl
      · exact h1 rfl
      · exact hl he
      · exact hr he

section cell

variable {V : Finset Pt} {F : Finset Edge} {x y : ℤ}
  (hV : Inside V F) (hc : IsCell V (x, y))
  (hb : bot (x, y) ∈ F) (ht : top (x, y) ∈ F) (hl : lft (x, y) ∉ F) (hr : rgt (x, y) ∉ F)
  (h2 : ∀ z, (Conn F (x, y) z ∨ Conn F (x, y + 1) z) → deg F z = 2)
include hV hc hb ht hl hr h2

-- Shared first step: remove the bottom edge (not a bridge).
--
omit hc ht hl hr in
lemma flip_step1 :
    Conn (F.erase (bot (x, y))) (x, y) (x + 1, y) ∧
      ncomp V (F.erase (bot (x, y))) = ncomp V F := by
  have hc1 : Conn (F.erase (bot (x, y))) (bot (x, y)).p (bot (x, y)).q := by
    apply conn_erase_of_even hV hb
    intro z _ hz
    rw [h2 z (Or.inl hz)]; exact even_two
  refine ⟨hc1, ?_⟩
  have := Finset.insert_erase hb
  conv_rhs => rw [← this]
  apply ncomp_congr
  intro u _ v _
  exact (conn_insert_of_conn hc1 u v).symm

-- **Merge.**
--
theorem flip_merge (hn : ¬ Conn F (x, y) (x, y + 1)) :
    ncomp V (flip F (x, y)) + 1 = ncomp V F := by
  obtain ⟨hab, e1⟩ := flip_step1 hV hb h2
  set G1 := F.erase (bot (x, y)) with hG1
  have hG1F : G1 ⊆ F := Finset.erase_subset _ _
  have htG1 : top (x, y) ∈ G1 := Finset.mem_erase.2 ⟨by simp [top, bot], ht⟩
  -- Remove the top edge (not a bridge: `d`'s class avoids `a` and `b`).
  have hdk : Conn (G1.erase (top (x, y))) (top (x, y)).p (top (x, y)).q := by
    apply conn_erase_of_even (hV.mono hG1F) htG1
    intro z _ hz
    have hzF : Conn F (x, y + 1) z := hz.mono hG1F
    have hza : ¬ (bot (x, y)).p = z ∧ ¬ (bot (x, y)).q = z := by
      constructor
      · intro h; apply hn; rw [show (bot (x, y)).p = (x, y) from rfl] at h; subst h
        exact hzF.symm
      · intro h; apply hn; rw [show (bot (x, y)).q = (x + 1, y) from rfl] at h; subst h
        exact (Conn.of_edge hb).trans hzF.symm
    have := deg_erase hb z
    rw [ite_eq_right (by tauto), ← hG1, add_zero] at this
    rw [this, h2 z (Or.inr hzF)]; exact even_two
  set G := G1.erase (top (x, y)) with hG
  have hGF : G ⊆ F := (Finset.erase_subset _ _).trans hG1F
  have e2 : ncomp V G = ncomp V G1 := by
    have := Finset.insert_erase htG1
    conv_rhs => rw [← this]
    apply ncomp_congr
    intro u _ v _
    exact (conn_insert_of_conn hdk u v).symm
  -- `a`, `b` stay joined in `G`.
  have habG : Conn G (x, y) (x + 1, y) := by
    have : Conn (insert (top (x, y)) G) (x, y) (x + 1, y) := by
      rw [Finset.insert_erase htG1]; exact hab
    rcases conn_insert.1 this with h | ⟨h1, _⟩ | ⟨h1, _⟩
    · exact h
    · exact absurd (h1.mono hGF) hn
    · exact absurd ((h1.mono hGF).trans (Conn.of_edge ht).symm) hn
  -- Insert the left side (merge) and the right side (inside a class).
  have hlv : (lft (x, y)).p ∈ V ∧ (lft (x, y)).q ∈ V := ⟨hc.1, hc.2.2.1⟩
  have em : ncomp V (insert (lft (x, y)) G) + 1 = ncomp V G :=
    ncomp_insert_merge hlv.1 hlv.2 (fun h => hn (h.mono hGF))
  have hbk : Conn (insert (lft (x, y)) G) (rgt (x, y)).p (rgt (x, y)).q := by
    have s : G ⊆ insert (lft (x, y)) G := Finset.subset_insert _ _
    have hl' : Conn (insert (lft (x, y)) G) (x, y) (x, y + 1) :=
      Conn.of_edge (Finset.mem_insert_self _ _)
    exact ((habG.mono s).symm.trans hl').trans (hdk.mono s)
  have er : ncomp V (insert (rgt (x, y)) (insert (lft (x, y)) G)) =
      ncomp V (insert (lft (x, y)) G) := by
    apply ncomp_congr; intro u _ v _; exact conn_insert_of_conn hbk u v
  rw [flip_eq hb ht hl hr, er]
  omega

-- **Split.**
--
theorem flip_split (hy : Conn F (x, y) (x, y + 1)) (hle : ∀ z, deg F z ≤ 2) :
    ncomp V (flip F (x, y)) = ncomp V F + 1 := by
  obtain ⟨hab, e1⟩ := flip_step1 hV hb h2
  set a : Pt := (x, y) with ha
  set b : Pt := (x + 1, y) with hbb
  set d : Pt := (x, y + 1) with hd
  set k : Pt := (x + 1, y + 1) with hk
  set G1 := F.erase (bot a) with hG1
  have hG1F : G1 ⊆ F := Finset.erase_subset _ _
  have htG1 : top a ∈ G1 := Finset.mem_erase.2 ⟨by simp [top, bot, a], ht⟩
  set G := G1.erase (top a) with hG
  have hGF : G ⊆ F := (Finset.erase_subset _ _).trans hG1F
  have hVG : Inside V G := hV.mono hGF
  have hbG : bot a ∉ G := fun h => by simp [G, G1] at h
  have hlG : lft a ∉ G := fun h => hl (hGF h)
  -- Degrees in `G`.
  set S : Finset Pt := {a, b, d, k} with hS
  have hFab : Conn F a b := Conn.of_edge hb
  have hFdk : Conn F d k := Conn.of_edge ht
  have degG : ∀ z, Conn F a z → deg G z = if z ∈ S then 1 else 2 := by
    intro z hz
    have hz2 := h2 z (Or.inl hz)
    have f1 := deg_erase hb z
    have f2 := deg_erase htG1 z
    rw [← hG1] at f1
    rw [← hG] at f2
    simp only [bot, top, Edge.q, S, Finset.mem_insert, Finset.mem_singleton, a, b, d, k]
      at f1 f2 ⊢
    obtain ⟨z1, z2⟩ := z
    simp only [Prod.mk.injEq] at f1 f2 ⊢
    split_ifs at f1 f2 ⊢ <;> omega
  have hleG : ∀ z, deg G z ≤ 2 := by
    intro z
    have f1 := deg_erase hb z
    have f2 := deg_erase htG1 z
    rw [← hG1] at f1
    rw [← hG] at f2
    have := hle z
    omega
  -- Class bookkeeping.
  have mem_cls : ∀ u w, w ∈ cls V G u ↔ w ∈ V ∧ Conn G u w := by
    intro u w; simp [cls]
  have aV : a ∈ V := hc.1
  have bV : b ∈ V := hc.2.1
  have dV : d ∈ V := hc.2.2.1
  have kV : k ∈ V := hc.2.2.2
  have cnt : ∀ K : Finset Pt, ((K ∩ S).card : ℕ) =
      (if a ∈ K then 1 else 0) + (if b ∈ K then 1 else 0) + (if d ∈ K then 1 else 0) +
        (if k ∈ K then 1 else 0) := by
    intro K
    rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.card_filter]
    rw [hS, Finset.sum_insert (by simp [a, b, d, k]), Finset.sum_insert (by simp [b, d, k]),
      Finset.sum_insert (by simp [d, k]), Finset.sum_singleton]
    ring
  -- Parity and the leaf bound in `a`'s class and `b`'s class.
  have par : ∀ u, Conn F a u → Even ((cls V G u ∩ S).card) := by
    intro u hu
    apply class_parity hVG u S
    intro z hz
    rw [mem_cls] at hz
    exact degG z (hu.trans (hz.2.mono hGF))
  have leaf : ∀ u, Conn F a u → (cls V G u ∩ S).card ≤ 2 := by
    intro u hu
    have hl2 := leaves_le_two (V := V) _ G rfl hVG hleG u
    refine le_trans (Finset.card_le_card ?_) hl2
    intro z hz
    rw [Finset.mem_inter, mem_cls] at hz
    rw [Finset.mem_filter]
    refine ⟨hz.1.1, hz.1.2, ?_⟩
    rw [degG z (hu.trans (hz.1.2.mono hGF)), ite_eq_left hz.2]
  have sym : ∀ u w, w ∈ cls V G u → u ∈ V → u ∈ cls V G w := by
    intro u w hw hu
    rw [mem_cls] at hw ⊢; exact ⟨hu, hw.2.symm⟩
  have aK : a ∈ cls V G a := mem_cls_self aV
  have bK : b ∈ cls V G b := mem_cls_self bV
  have pa := par a (Conn.refl _ _)
  have la := leaf a (Conn.refl _ _)
  have pb := par b hFab
  rw [cnt] at pa la pb
  rw [ite_eq_left aK] at pa la
  rw [ite_eq_left bK] at pb
  by_cases hbA : b ∈ cls V G a
  · -- Then `d`, `k` are outside `a`'s class, so `F` cannot join `a` to `d`.
    exfalso
    rw [ite_eq_left hbA] at la pa
    have hdA : d ∉ cls V G a := by intro h; rw [ite_eq_left h] at la; split_ifs at la <;> omega
    have hkA : k ∉ cls V G a := by intro h; rw [ite_eq_left h] at la; split_ifs at la; omega
    have hcl : Closed F (cls V G a) := by
      intro u hu w huw
      obtain ⟨f, hf, hfw⟩ := huw
      by_cases hfb : f = bot a
      · subst hfb
        rcases hfw with ⟨h1, h2'⟩ | ⟨h1, h2'⟩
        · rw [← h2']; exact hbA
        · rw [← h1]; exact aK
      by_cases hft : f = top a
      · subst hft
        rcases hfw with ⟨h1, _⟩ | ⟨_, h2'⟩
        · rw [← h1] at hu; exact absurd hu hdA
        · rw [← h2'] at hu; exact absurd hu hkA
      · exact closed_cls hVG a u hu w
          ⟨f, Finset.mem_erase.2 ⟨hft, Finset.mem_erase.2 ⟨hfb, hf⟩⟩, hfw⟩
    exact hdA (closed_conn hcl aK hy)
  rw [ite_eq_right hbA] at la pa
  have hAB : ∀ w, w ∈ cls V G a → w ∉ cls V G b := by
    intro w hwa hwb
    apply hbA
    rw [mem_cls] at hwa hwb ⊢
    exact ⟨bV, hwa.2.trans hwb.2.symm⟩
  have haB : a ∉ cls V G b := fun h => hAB a aK h
  rw [ite_eq_right haB] at pb
  by_cases hkA : k ∈ cls V G a
  · -- Twisted pairing: excluded by the planar lemma.
    exfalso
    have hkB : k ∉ cls V G b := hAB k hkA
    rw [ite_eq_right hkB] at pb
    have hdB : d ∈ cls V G b := by
      by_contra h; rw [ite_eq_right h] at pb; simp at pb
    apply planar_cell G x y hbG hlG
    · exact ((mem_cls _ _).1 hdB).2
    · exact ((mem_cls _ _).1 hkA).2.symm
    · intro h; exact hbA ((mem_cls _ _).2 ⟨bV, h⟩)
  · rw [ite_eq_right hkA] at la pa
    have hdA : d ∈ cls V G a := by
      by_contra h; rw [ite_eq_right h] at pa; simp at pa
    have hdB : d ∉ cls V G b := hAB d hdA
    rw [ite_eq_right hdB] at pb
    have hkB : k ∈ cls V G b := by
      by_contra h; rw [ite_eq_right h] at pb; simp at pb
    have hGad : Conn G a d := ((mem_cls _ _).1 hdA).2
    have hGbk : Conn G b k := ((mem_cls _ _).1 hkB).2
    have hGdk : ¬ Conn G d k := by
      intro h; exact hkA ((mem_cls _ _).2 ⟨kV, hGad.trans h⟩)
    -- Count: `G1 = G + top` merges; adding the two sides changes nothing.
    have em : ncomp V G1 + 1 = ncomp V G := by
      have := ncomp_insert_merge (V := V) (F := G) (e := top a) dV kV hGdk
      rw [Finset.insert_erase htG1] at this
      exact this
    have s1 : G ⊆ insert (lft a) G := Finset.subset_insert _ _
    have el : ncomp V (insert (lft a) G) = ncomp V G := by
      apply ncomp_congr; intro u _ v _; exact conn_insert_of_conn hGad u v
    have er : ncomp V (insert (rgt a) (insert (lft a) G)) = ncomp V (insert (lft a) G) := by
      apply ncomp_congr; intro u _ v _; exact conn_insert_of_conn (hGbk.mono s1) u v
    rw [flip_eq hb ht hl hr, er, el]
    omega

end cell

end SolidGridHam
