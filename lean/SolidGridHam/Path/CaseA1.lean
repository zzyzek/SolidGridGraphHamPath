/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import SolidGridHam.Path.Compat3

/-!
# Lemma 4, case A1 (docs/S4_UNDO.md §II.3)

An earlier chain operation (a row at a state no older than bridge `i`'s, whose start pair is a
pending pair from before `i` in the plan) has no square beside `E_i` across `E_i`'s lateral, when
`i` is undone: that square is cut, so it is the row's start, and the start's pair is matched with
`E_i`'s pair, so its node is `i`, which the plan never gives a pending pair of an undone bridge.
-/

namespace SolidGridHam

namespace HP

open Finset Classical

lemma Matched.trans {R : Pt → Pt → Prop} (hR : IsEqv R) {x y u v a b : Pt}
    (h1 : Matched R x y u v) (h2 : Matched R u v a b) : Matched R x y a b := by
  rcases h1 with ⟨p1, p2⟩ | ⟨p1, p2⟩ <;> rcases h2 with ⟨q1, q2⟩ | ⟨q1, q2⟩
  · exact Or.inl ⟨hR.trans p1 q1, hR.trans p2 q2⟩
  · exact Or.inr ⟨hR.trans p1 q1, hR.trans p2 q2⟩
  · exact Or.inr ⟨hR.trans p1 q2, hR.trans p2 q1⟩
  · exact Or.inl ⟨hR.trans p1 q2, hR.trans p2 q1⟩

lemma Matched.of_ends {R : Pt → Pt → Prop} (hR : IsEqv R) {e : Edge} {u v u' v' : Pt}
    (h1 : Ends e u v) (h2 : Ends e u' v') : Matched R u v u' v' := by
  rcases h1 with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> rcases h2 with ⟨b1, b2⟩ | ⟨b1, b2⟩
  · exact Or.inl ⟨by rw [show u = u' from a1.symm.trans b1]; exact hR.refl _,
      by rw [show v = v' from a2.symm.trans b2]; exact hR.refl _⟩
  · exact Or.inr ⟨by rw [show u = v' from a1.symm.trans b1]; exact hR.refl _,
      by rw [show v = u' from a2.symm.trans b2]; exact hR.refl _⟩
  · exact Or.inr ⟨by rw [show u = v' from a2.symm.trans b2]; exact hR.refl _,
      by rw [show v = u' from a1.symm.trans b1]; exact hR.refl _⟩
  · exact Or.inl ⟨by rw [show u = u' from a2.symm.trans b2]; exact hR.refl _,
      by rw [show v = v' from a1.symm.trans b1]; exact hR.refl _⟩

lemma sideEdge_inj {c : Pt} {s1 s2 : Side} (h : sideEdge c s1 = sideEdge c s2) : s1 = s2 := by
  obtain ⟨x, y⟩ := c
  cases s1 <;> cases s2 <;> simp [sideEdge, bot, top, lft, rgt, Prod.ext_iff] at h ⊢

-- A cell's start pair matched with the ends of either lateral, when its back and front pairs are
-- joined.
--
lemma lat_matched {F : Finset Edge} {q : Pt} {a : Side}
    (hb : Conn F (back1 q a) (back2 q a)) (hf : Conn F (front1 q a) (front2 q a)) {e : Edge}
    (he : e = lat1 q a ∨ e = lat2 q a) {u v : Pt} (hu : Ends e u v) :
    Matched (Conn F) (back1 q a) (front1 q a) u v := by
  have hR := isEqv_conn F
  rcases he with rfl | rfl
  · exact Matched.of_ends hR (ends_lat1 (c := q) (s := a)) hu
  · have := Matched.of_ends hR (ends_lat2 (c := q) (s := a)) hu
    exact Matched.trans hR (Or.inl ⟨hb, hf⟩) this

section caseA1

variable {V W : Finset Pt} {d : Pt → ℕ} {t0 u0 : Pt} {H0 : Finset Edge}
  (hVW : V ⊆ W) (hdc : ∀ q, IsCell V q → ∀ z, IsCorner z q → d z = 2)
  (h0 : IsFactor W d H0) (hout0 : ∀ e ∈ H0, (e.p ∉ V → e.q = t0 ∨ e.q = u0) ∧ (e.q ∉ V → e.p = t0 ∨ e.p = u0))
include hVW hdc h0 hout0

-- The state after the newest `m` bridges are removed, its bridges frozen.
--
lemma frozen_at {BS : List Bridge} {H : Finset Edge} (hr : Reach V H0 H BS) {m i : ℕ}
    (hm : m ≤ i) (hi : i < BS.length) :
    Reach V H0 (seqH H0 (BS.drop m)) (BS.drop m) ∧ (BS[i]'hi) ∈ BS.drop m ∧
      RegionOK (seqH H0 (BS.drop m)) (BS[i]'hi) ∧ 2 ≤ (BS[i]'hi).r ∧ (BS[i]'hi).r % 2 = 0 := by
  have hrm : Reach V H0 (seqH H0 (BS.drop m)) (BS.drop m) := by
    have e := List.take_append_drop m BS
    have hr2 : Reach V H0 H (BS.take m ++ BS.drop m) := by rw [e]; exact hr
    exact reach_suffix hr2
  have hmem : (BS[i]'hi) ∈ BS.drop m := by
    rw [List.mem_iff_getElem]
    exact ⟨i - m, by simp; omega, by simp [List.getElem_drop]; congr 1; omega⟩
  have hinv := pinv_reach (t0 := t0) (u0 := u0) hVW hdc h0 hout0 hrm
  obtain ⟨hR, h2, he, _⟩ := hinv.reg _ hmem
  exact ⟨hrm, hmem, hR, h2, he⟩

-- **Case A1.**
--
theorem caseA1 {BS : List Bridge} {H : Finset Edge} (hr : Reach V H0 H BS) {uv : Pt × Pt}
    (hn : ¬ Conn H uv.1 uv.2) {i : ℕ} (hi : i < BS.length) (hlow : lowAt H BS uv i = false)
    {m j' : ℕ} (hm : m ≤ i) (hj' : j' ≤ i) {q : Pt} {a : Side} {n : ℕ}
    (hrow : RowAt V (seqH H0 (BS.drop m)) (BS.drop m) q a n)
    (hpair : pendAt H BS uv j' = (back1 q a, front1 q a)) {nO : ℕ} (hnO : nO ≤ n) {j : ℕ}
    (hj : j < nO) {s' : Side} (hs' : s' = latA (BS[i]'hi).a ∨ s' = latB (BS[i]'hi).a)
    (hX : cellJ q a j = nb (BS[i]'hi).E s')
    (hrole : sideEdge (BS[i]'hi).E s' = lat1 (cellJ q a j) a ∨
      sideEdge (BS[i]'hi).E s' = lat2 (cellJ q a j) a ∨
      (j = 0 ∧ sideEdge (BS[i]'hi).E s' = back q a) ∨
      (j + 1 = nO ∧ sideEdge (BS[i]'hi).E s' = front (cellJ q a j) a)) : False := by
  obtain ⟨_, _, hR, htwo, _⟩ := frozen_at hVW hdc h0 hout0 hr hm hi
  set F := seqH H0 (BS.drop m) with hF
  set b := BS[i]'hi with hb
  obtain ⟨c1, c2⟩ := cutE_both hR htwo
  have bE : back b.E b.a ∈ F := by
    have := hR.frA
    unfold Bridge.E Bridge.cell at *
    rw [show b.r - 1 = b.r - 2 + 1 by omega, back_cellJ_succ]; exact this
  -- The square beside `E` is cut, so it is the start.
  --
  have hcut : CutSq F (cellJ q a j) := by
    rw [hX]
    rcases hs' with h | h <;> rw [h]
    · refine cutSq_of_corners (isCorner_back2 _ b.a) (isCorner_front2 _ b.a) ?_
      rw [sideA_back2, sideA_front2]; exact c1
    · refine cutSq_of_corners (isCorner_back1 _ b.a) (isCorner_front1 _ b.a) ?_
      rw [sideB_back1, sideB_front1]; exact c2
  have hj0 : j = 0 := by
    by_contra hne
    exact hrow.uncut j (by omega) (by omega) hcut
  subst hj0
  rw [cellJ_zero] at hX hrole
  -- `e` is a light lateral of `E`.
  --
  have hlight : sideEdge b.E s' ∉ F := by
    rcases hs' with h | h <;> rw [h]
    · rw [← lat1_eq]; exact hR.latE.1
    · rw [← lat2_eq]; exact hR.latE.2
  have lateral : sideEdge b.E s' = lat1 q a ∨ sideEdge b.E s' = lat2 q a → False := by
    intro hl
    have hR' := isEqv_conn F
    have hmE : Matched (Conn F) (back1 q a) (front1 q a) (back1 b.E b.a) (front1 b.E b.a) := by
      rcases hs' with h | h
      · have he : Ends (sideEdge b.E s') (back1 b.E b.a) (front1 b.E b.a) := by
          rw [h, ← lat1_eq]; exact ends_lat1 _ _
        exact lat_matched hrow.crit.1 hrow.crit.2.1 hl he
      · have he : Ends (sideEdge b.E s') (back2 b.E b.a) (front2 b.E b.a) := by
          rw [h, ← lat2_eq]; exact ends_lat2 _ _
        have m1 := lat_matched hrow.crit.1 hrow.crit.2.1 hl he
        have m2 : Matched (Conn F) (back2 b.E b.a) (front2 b.E b.a) (back1 b.E b.a)
            (front1 b.E b.a) :=
          Or.inl ⟨((ends_back (c := b.E) (s := b.a)).conn bE).symm,
            ((ends_front (c := b.E) (s := b.a)).conn hR.frE).symm⟩
        exact Matched.trans hR' m1 m2
    have hnode := sameNodeI' hVW hdc h0 hout0 hr hi hm hmE
    have hne := (node_pend hVW hdc h0 hout0 hr hn (i - j') j' i rfl hj' hi).1 hlow
    rw [hpair] at hne
    exact hne hnode
  rcases hrole with h | h | ⟨_, h⟩ | ⟨h1, h⟩
  · exact lateral (Or.inl h)
  · exact lateral (Or.inr h)
  · rw [h] at hlight; exact hlight hrow.bk
  · -- a one-square operation: its front faces `E`, and the next row square is `E`
    have e1 : sideEdge q s'.opp = sideEdge q a := by
      rw [hX, sideEdge_nb_opp]; unfold front at h; rw [← hX]; exact h
    have ha := sideEdge_inj e1
    have hnext : cellJ q a 1 = b.E := by
      rw [show (1 : ℕ) = 0 + 1 from rfl, ← nb_cellJ, cellJ_zero, ← ha, hX, nb_nb_opp]
    exact hrow.uncut 1 le_rfl (by have := hrow.two; omega) (hnext ▸ cutSq_E hR)

end caseA1

end HP

end SolidGridHam
