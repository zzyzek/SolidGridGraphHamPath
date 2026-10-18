/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import SolidGridHam.Path.SideAfter

@[expose] public section

/-!
# E1's shape after a move

Three-piece cells after a move: away from the move nothing changes; on the moved column and at
even side squares two pairs of corners are joined; an odd side square `S_k` that touches three
pieces either forces `S_(k+1)` to touch three pieces before the move with its lone corners facing
the cell `S_k` (against E1's shape), or, when `S_(k+1)` is not a cell, has E1's shape itself with `t`
its outer front corner (the edge from that corner to the missing corner leaves `V`, so it is `t`'s).
-/

namespace SolidGridHam

namespace HP

open Finset Classical

section helpers

variable {F : Finset Edge}

-- Every corner joined to `A` or to `B`: at most two pieces.
--
lemma noThree_two {q A B : Pt} (h : ∀ u, IsCorner u q → Conn F u A ∨ Conn F u B) :
    ¬ Three F q := by
  rintro ⟨u, v, w, hu, hv, hw, huv, hvw, huw⟩
  rcases h u hu with a | a <;> rcases h v hv with b | b <;> rcases h w hw with c' | c'
  · exact huv (a.trans b.symm)
  · exact huv (a.trans b.symm)
  · exact huw (a.trans c'.symm)
  · exact hvw (b.trans c'.symm)
  · exact hvw (b.trans c'.symm)
  · exact huw (a.trans c'.symm)
  · exact huv (a.trans b.symm)
  · exact huv (a.trans b.symm)

lemma isCell_of_corners {V : Finset Pt} {q : Pt} {a : Side} (h1 : back1 q a ∈ V)
    (h2 : back2 q a ∈ V) (h3 : front1 q a ∈ V) (h4 : front2 q a ∈ V) : IsCell V q := by
  obtain ⟨x, y⟩ := q
  cases a <;> simp only [back1, back2, front1, front2] at h1 h2 h3 h4 <;>
    exact ⟨by simpa using (by first | exact h1 | exact h2 | exact h3), by
      first | exact h1 | exact h2 | exact h3 | exact h4, by
      first | exact h1 | exact h2 | exact h3 | exact h4, by
      first | exact h1 | exact h2 | exact h3 | exact h4⟩

end helpers

section geo

variable {c : Pt} {s : Side} {n : ℕ}

lemma sideA_front2 (x : Pt) (s : Side) : front2 (nb x (latA s)) s = front1 x s := by
  obtain ⟨a, b⟩ := x; cases s <;> simp [front1, front2, nb, latA]

lemma sideA_back2 (x : Pt) (s : Side) : back2 (nb x (latA s)) s = back1 x s := by
  obtain ⟨a, b⟩ := x; cases s <;> simp [back1, back2, nb, latA]

lemma sideB_front1 (x : Pt) (s : Side) : front1 (nb x (latB s)) s = front2 x s := by
  obtain ⟨a, b⟩ := x; cases s <;> simp [front1, front2, nb, latB]

lemma sideB_back1 (x : Pt) (s : Side) : back1 (nb x (latB s)) s = back2 x s := by
  obtain ⟨a, b⟩ := x; cases s <;> simp [back1, back2, nb, latB]

-- Points off the column are not even-height interior column vertices.
--
lemma notMid_outA (k : ℕ) :
    ¬ IsMid c s n (front1 (nb (cellJ c s k) (latA s)) s) ∧
      ¬ IsMid c s n (back1 (nb (cellJ c s k) (latA s)) s) := by
  constructor <;> rintro ⟨j, _, _, h | h⟩ <;> obtain ⟨x, y⟩ := c <;>
    cases s <;> simp [front1, front2, back1, nb, latA, cellJ] at h <;> omega

lemma notMid_outB (k : ℕ) :
    ¬ IsMid c s n (front2 (nb (cellJ c s k) (latB s)) s) ∧
      ¬ IsMid c s n (back2 (nb (cellJ c s k) (latB s)) s) := by
  constructor <;> rintro ⟨j, _, _, h | h⟩ <;> obtain ⟨x, y⟩ := c <;>
    cases s <;> simp [front1, front2, back2, nb, latB, cellJ] at h <;> omega

lemma notMid_even {m : ℕ} (hm : m % 2 = 0) :
    ¬ IsMid c s n (front1 (cellJ c s m) s) ∧ ¬ IsMid c s n (front2 (cellJ c s m) s) := by
  constructor <;> rintro ⟨j, hj, _, h | h⟩ <;> obtain ⟨x, y⟩ := c <;>
    cases s <;> simp [front1, front2, cellJ] at h <;> omega

lemma back1_col {k : ℕ} (hk : 1 ≤ k) : back1 (cellJ c s k) s = front1 (cellJ c s (k - 1)) s := by
  have := back1_nb (cellJ c s (k - 1)) s; rwa [nb_cellJ, show k - 1 + 1 = k by omega] at this

lemma back2_col {k : ℕ} (hk : 1 ≤ k) : back2 (cellJ c s k) s = front2 (cellJ c s (k - 1)) s := by
  have := back2_nb (cellJ c s (k - 1)) s; rwa [nb_cellJ, show k - 1 + 1 = k by omega] at this

end geo

section e1after

variable {V W : Finset Pt} {d : Pt → ℕ} {H H' : Finset Edge} {FP : List FixedPr} {c : Pt}
  {s : Side} {n : ℕ} {i : FixedPr} {t0 u0 : Pt}

-- Edges leaving `V` are not moved.
--
lemma MoveCtx.out_H1 (M : MoveCtx V W d H H' FP c s n i t0 u0) :
    ∀ e ∈ lowerCol H c s n, (e.p ∉ V → e.q = t0 ∨ e.q = u0) ∧ (e.q ∉ V → e.p = t0 ∨ e.p = u0) := by
  intro e he
  by_cases h : ∃ j, 1 ≤ j ∧ j ≤ n ∧ e ∈ cellE (cellJ c s j)
  · obtain ⟨j, _, h2, he'⟩ := h
    have := isEdge_of_cellE (M.cell j (by omega)) he'
    exact ⟨fun h' => absurd this.1 h', fun h' => absurd this.2 h'⟩
  · push Not at h
    exact M.inv.out e ((mem_lowerCol_off (F := H) (c := c) (s := s) (k := n) h).1 he)

-- **An odd side square (`latA`) touching three pieces after the move has E1's shape.**
--
theorem MoveCtx.oddA_tri (M : MoveCtx V W d H H' FP c s n i t0 u0) {k : ℕ} (h1 : 1 ≤ k)
    (h2 : k ≤ n) (hko : k % 2 = 1) (hf : IsCell V (nb (cellJ c s k) (latA s)))
    (h3 : Three (lowerCol H c s n) (nb (cellJ c s k) (latA s))) :
    TriShape V (lowerCol H c s n) t0 (nb (cellJ c s k) (latA s)) ∨
      TriShape V (lowerCol H c s n) u0 (nb (cellJ c s k) (latA s)) := by
  set Sk := nb (cellJ c s k) (latA s) with hSk
  set Sk1 := nb (cellJ c s (k + 1)) (latA s) with hSk1
  have hnb : nb Sk s = Sk1 := by rw [hSk, hSk1, nb_side_comm, nb_cellJ]
  have hkn : k + 1 ≤ n := by have := M.ev; omega
  -- The back of `S_k` is dark: its back corners are joined.
  --
  have hbk : back Sk s ∈ lowerCol H c s n := by
    have e : back Sk s = outer1 (cellJ c s (k - 1)) s := by
      rw [outer1_side_nb_next, nb_cellJ, show k - 1 + 1 = k by omega]; rfl
    rw [e, M.outer1_H1 (by omega)]; omega
  have eAB := (ends_back Sk s).conn hbk
  -- Three pieces: the front corners are alone.
  --
  have cs : ∀ {u : Pt}, IsCorner u Sk → u = back1 Sk s ∨ u = back2 Sk s ∨ u = front1 Sk s ∨
      u = front2 Sk s := fun hu => corner_cases Sk s hu
  have n12 : ¬ Conn (lowerCol H c s n) (front1 Sk s) (front2 Sk s) := fun h => by
    apply noThree_two (A := back1 Sk s) (B := front1 Sk s) _ h3
    intro u hu; rcases cs hu with rfl | rfl | rfl | rfl
    · exact Or.inl (Conn.refl _ _)
    · exact Or.inl eAB.symm
    · exact Or.inr (Conn.refl _ _)
    · exact Or.inr h.symm
  have n1A : ¬ Conn (lowerCol H c s n) (front1 Sk s) (back1 Sk s) := fun h => by
    apply noThree_two (A := back1 Sk s) (B := front2 Sk s) _ h3
    intro u hu; rcases cs hu with rfl | rfl | rfl | rfl
    · exact Or.inl (Conn.refl _ _)
    · exact Or.inl eAB.symm
    · exact Or.inl h
    · exact Or.inr (Conn.refl _ _)
  have n2B : ¬ Conn (lowerCol H c s n) (front2 Sk s) (back2 Sk s) := fun h => by
    apply noThree_two (A := back1 Sk s) (B := front1 Sk s) _ h3
    intro u hu; rcases cs hu with rfl | rfl | rfl | rfl
    · exact Or.inl (Conn.refl _ _)
    · exact Or.inl eAB.symm
    · exact Or.inr (Conn.refl _ _)
    · exact Or.inl (h.trans eAB.symm)
  by_cases hc1 : IsCell V Sk1
  · -- `S_(k+1)` touched three pieces before the move, its lone corners facing the cell `S_k`.
    exfalso
    have hcol : IsCell V (cellJ c s (k + 1)) := M.cell (k + 1) (by omega)
    have nmA := (notMid_outA (c := c) (s := s) (n := n) k)
    have nmA1 := (notMid_outA (c := c) (s := s) (n := n) (k + 1))
    have nmB : ¬ IsMid c s n (back2 Sk s) := by
      rw [hSk, sideA_back2, back1_col h1]; exact (notMid_even (by omega)).1
    have nmG2 : ¬ IsMid c s n (front2 Sk1 s) := by
      rw [hSk1, sideA_front2]; exact (notMid_even (by omega)).1
    have cc := M.conn
    have eB2 : Conn H (back2 Sk s) (front2 Sk s) := by
      apply (ends_lat2 Sk s).conn
      rw [hSk, side_near]; exact (M.pat.2.1 k (by omega)).1.2 hko
    have eG : Conn H (front1 Sk1 s) (front2 Sk1 s) := by
      apply (ends_front Sk1 s).conn
      rw [hSk1, side_front]; exact (outer1_all M.ev M.two M.pat M.d1 M.d2 M.altB hkn).2 (by omega)
    have eF2G2 : Conn (lowerCol H c s n) (front2 Sk s) (front2 Sk1 s) := by
      have := (ends_lat2 Sk1 s).conn (F := lowerCol H c s n) (by
        rw [hSk1, side_near]; exact (lat1_after M.ev M.two M.pat (by omega) hkn).2 (by omega))
      rw [← hnb, back2_nb, hnb] at this; exact this
    have b1 : back1 Sk1 s = front1 Sk s := by rw [← hnb, back1_nb]
    have b2 : back2 Sk1 s = front2 Sk s := by rw [← hnb, back2_nb]
    have n1B : ¬ Conn H (front1 Sk s) (back2 Sk s) := by
      rw [← cc _ _ nmA.1 nmB]
      intro h; exact n1A (h.trans eAB.symm)
    have nBG2 : ¬ Conn H (back2 Sk s) (front2 Sk1 s) := by
      rw [← cc _ _ nmB nmG2]
      intro h; exact n2B (eF2G2.trans h.symm)
    have n1G2 : ¬ Conn H (front1 Sk s) (front2 Sk1 s) := by
      rw [← cc _ _ nmA.1 nmG2]
      intro h; exact n12 (h.trans eF2G2.symm)
    have three : Three H Sk1 := by
      refine ⟨front1 Sk s, front2 Sk s, front2 Sk1 s, ?_, ?_, isCorner_front2 _ _,
        fun h => n1B (h.trans eB2.symm), fun h => nBG2 (eB2.trans h),  n1G2⟩
      · rw [← b1]; exact isCorner_back1 _ _
      · rw [← b2]; exact isCorner_back2 _ _
    rcases (M.inv.tri Sk1 hc1 three).ex with ⟨_, _, sd', _, hout', hbb', _⟩ | hD
    swap
    · exact hD.1 s eG
    rcases side_cases s sd' with h | h | h | h <;> rw [h] at hbb' hout'
    · rw [b1, b2] at hbb'; exact n1B (hbb'.trans eB2.symm)
    · rw [show nb Sk1 s.opp = Sk by rw [← hnb, nb_nb_opp]] at hout'; exact hout' hf
    · have e1 := (ends_back Sk1 (latA s)).conn_iff H
      rw [show back Sk1 (latA s) = lat2 Sk1 s by
        rw [lat2_eq]; unfold back; rw [latA_opp']] at e1
      rw [← e1, (ends_lat2 Sk1 s).conn_iff, b2] at hbb'
      exact nBG2 (eB2.trans hbb')
    · have e1 := (ends_back Sk1 (latB s)).conn_iff H
      rw [show back Sk1 (latB s) = lat1 Sk1 s by
        rw [lat1_eq]; unfold back; rw [latB_opp']] at e1
      rw [← e1, (ends_lat1 Sk1 s).conn_iff, b1] at hbb'
      exact n1G2 (hbb'.trans eG)
  · -- `S_(k+1)` is not a cell: `S_k` has E1's shape, with `t` its outer front corner.
    suffices hw : front1 Sk s = t0 ∨ front1 Sk s = u0 by
      rcases hw with hw | hw
      · exact Or.inl ⟨s, Or.inl hw.symm, by rwa [hnb], eAB, n12, n1A, n2B⟩
      · exact Or.inr ⟨s, Or.inl hw.symm, by rwa [hnb], eAB, n12, n1A, n2B⟩
    have hcorn := isCell_corners hf s
    have hd : deg (lowerCol H c s n) (front1 Sk s) = 2 := by
      rw [M.factor.2 _ (M.hVW hcorn.2.2.1)]; exact M.hdc _ hf _ (isCorner_front1 _ _)
    rw [deg_front1, hnb] at hd
    have l1 : lat1 Sk s ∉ lowerCol H c s n := fun h => n1A ((ends_lat1 Sk s).conn h).symm
    have fr : front Sk s ∉ lowerCol H c s n := fun h => n12 ((ends_front Sk s).conn h)
    rw [ind_of_not_mem l1, ind_of_not_mem fr] at hd
    have hl : lat1 Sk1 s ∈ lowerCol H c s n := by
      by_contra hh; rw [ind_of_not_mem hh] at hd
      have := ind_le_one (lowerCol H c s n) (outer1 Sk s); omega
    have hG1 : front1 Sk1 s ∉ V := by
      intro hG
      apply hc1
      refine isCell_of_corners (a := s) ?_ ?_ hG ?_
      · rw [← hnb, back1_nb]; exact hcorn.2.2.1
      · rw [← hnb, back2_nb]; exact hcorn.2.2.2
      · rw [hSk1, sideA_front2]
        exact (isCell_corners (M.cell (k + 1) (by omega)) s).2.2.1
    have hout := M.out_H1 (lat1 Sk1 s) hl
    have b1 : back1 Sk1 s = front1 Sk s := by rw [← hnb, back1_nb]
    rcases ends_lat1 Sk1 s with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [b1] at e1
      have := hout.2 (by rw [e2]; exact hG1)
      rw [e1] at this; exact this
    · rw [b1] at e2
      have := hout.1 (by rw [e1]; exact hG1)
      rw [e2] at this; exact this

-- **An odd side square (`latB`) touching three pieces after the move has E1's shape.**
--
theorem MoveCtx.oddB_tri (M : MoveCtx V W d H H' FP c s n i t0 u0) {k : ℕ} (h1 : 1 ≤ k)
    (h2 : k ≤ n) (hko : k % 2 = 1) (hf : IsCell V (nb (cellJ c s k) (latB s)))
    (h3 : Three (lowerCol H c s n) (nb (cellJ c s k) (latB s))) :
    TriShape V (lowerCol H c s n) t0 (nb (cellJ c s k) (latB s)) ∨
      TriShape V (lowerCol H c s n) u0 (nb (cellJ c s k) (latB s)) := by
  set Sk := nb (cellJ c s k) (latB s) with hSk
  set Sk1 := nb (cellJ c s (k + 1)) (latB s) with hSk1
  have hnb : nb Sk s = Sk1 := by rw [hSk, hSk1, nb_sideB_comm, nb_cellJ]
  have hkn : k + 1 ≤ n := by have := M.ev; omega
  -- The back of `S_k` is dark: its back corners are joined.
  --
  have hbk : back Sk s ∈ lowerCol H c s n := by
    have e : back Sk s = outer2 (cellJ c s (k - 1)) s := by
      rw [outer2_side_nb_next, nb_cellJ, show k - 1 + 1 = k by omega]; rfl
    rw [e, M.outer2_H1 (by omega)]; omega
  have eAB := ((ends_back Sk s).conn hbk).symm
  -- Three pieces: the front corners are alone.
  --
  have cs : ∀ {u : Pt}, IsCorner u Sk → u = back2 Sk s ∨ u = back1 Sk s ∨ u = front2 Sk s ∨
      u = front1 Sk s := fun hu => by rcases corner_cases Sk s hu with h | h | h | h <;> tauto
  have n12 : ¬ Conn (lowerCol H c s n) (front2 Sk s) (front1 Sk s) := fun h => by
    apply noThree_two (A := back2 Sk s) (B := front2 Sk s) _ h3
    intro u hu; rcases cs hu with rfl | rfl | rfl | rfl
    · exact Or.inl (Conn.refl _ _)
    · exact Or.inl eAB.symm
    · exact Or.inr (Conn.refl _ _)
    · exact Or.inr h.symm
  have n1A : ¬ Conn (lowerCol H c s n) (front2 Sk s) (back2 Sk s) := fun h => by
    apply noThree_two (A := back2 Sk s) (B := front1 Sk s) _ h3
    intro u hu; rcases cs hu with rfl | rfl | rfl | rfl
    · exact Or.inl (Conn.refl _ _)
    · exact Or.inl eAB.symm
    · exact Or.inl h
    · exact Or.inr (Conn.refl _ _)
  have n2B : ¬ Conn (lowerCol H c s n) (front1 Sk s) (back1 Sk s) := fun h => by
    apply noThree_two (A := back2 Sk s) (B := front2 Sk s) _ h3
    intro u hu; rcases cs hu with rfl | rfl | rfl | rfl
    · exact Or.inl (Conn.refl _ _)
    · exact Or.inl eAB.symm
    · exact Or.inr (Conn.refl _ _)
    · exact Or.inl (h.trans eAB.symm)
  by_cases hc1 : IsCell V Sk1
  · -- `S_(k+1)` touched three pieces before the move, its lone corners facing the cell `S_k`.
    exfalso
    have hcol : IsCell V (cellJ c s (k + 1)) := M.cell (k + 1) (by omega)
    have nmA := (notMid_outB (c := c) (s := s) (n := n) k)
    have nmA1 := (notMid_outB (c := c) (s := s) (n := n) (k + 1))
    have nmB : ¬ IsMid c s n (back1 Sk s) := by
      rw [hSk, sideB_back1, back2_col h1]; exact (notMid_even (by omega)).2
    have nmG2 : ¬ IsMid c s n (front1 Sk1 s) := by
      rw [hSk1, sideB_front1]; exact (notMid_even (by omega)).2
    have cc := M.conn
    have eB2 : Conn H (back1 Sk s) (front1 Sk s) := by
      apply (ends_lat1 Sk s).conn
      rw [hSk, sideB_near]; exact (M.pat.2.1 k (by omega)).2.2 hko
    have eG : Conn H (front2 Sk1 s) (front1 Sk1 s) := by
      apply Conn.symm; apply (ends_front Sk1 s).conn
      rw [hSk1, sideB_front]; exact (outer2_all M.ev M.two M.pat M.d1 M.d2 M.altB hkn).2 (by omega)
    have eF2G2 : Conn (lowerCol H c s n) (front1 Sk s) (front1 Sk1 s) := by
      have := (ends_lat1 Sk1 s).conn (F := lowerCol H c s n) (by
        rw [hSk1, sideB_near]; exact (lat2_after M.ev M.two M.pat (by omega) hkn).2 (by omega))
      rw [← hnb, back1_nb, hnb] at this; exact this
    have b1 : back2 Sk1 s = front2 Sk s := by rw [← hnb, back2_nb]
    have b2 : back1 Sk1 s = front1 Sk s := by rw [← hnb, back1_nb]
    have n1B : ¬ Conn H (front2 Sk s) (back1 Sk s) := by
      rw [← cc _ _ nmA.1 nmB]
      intro h; exact n1A (h.trans eAB.symm)
    have nBG2 : ¬ Conn H (back1 Sk s) (front1 Sk1 s) := by
      rw [← cc _ _ nmB nmG2]
      intro h; exact n2B (eF2G2.trans h.symm)
    have n1G2 : ¬ Conn H (front2 Sk s) (front1 Sk1 s) := by
      rw [← cc _ _ nmA.1 nmG2]
      intro h; exact n12 (h.trans eF2G2.symm)
    have three : Three H Sk1 := by
      refine ⟨front2 Sk s, front1 Sk s, front1 Sk1 s, ?_, ?_, isCorner_front1 _ _,
        fun h => n1B (h.trans eB2.symm), fun h => nBG2 (eB2.trans h),  n1G2⟩
      · rw [← b1]; exact isCorner_back2 _ _
      · rw [← b2]; exact isCorner_back1 _ _
    rcases (M.inv.tri Sk1 hc1 three).ex with ⟨_, _, sd', _, hout', hbb', _⟩ | hD
    swap
    · exact hD.1 s eG.symm
    rcases side_cases s sd' with h | h | h | h <;> rw [h] at hbb' hout'
    · rw [b1, b2] at hbb'; exact n1B (hbb'.symm.trans eB2.symm)
    · rw [show nb Sk1 s.opp = Sk by rw [← hnb, nb_nb_opp]] at hout'; exact hout' hf
    · have e1 := (ends_back Sk1 (latA s)).conn_iff H
      rw [show back Sk1 (latA s) = lat2 Sk1 s by
        rw [lat2_eq]; unfold back; rw [latA_opp']] at e1
      rw [← e1, (ends_lat2 Sk1 s).conn_iff, b1] at hbb'
      exact n1G2 (hbb'.trans eG)
    · have e1 := (ends_back Sk1 (latB s)).conn_iff H
      rw [show back Sk1 (latB s) = lat1 Sk1 s by
        rw [lat1_eq]; unfold back; rw [latB_opp']] at e1
      rw [← e1, (ends_lat1 Sk1 s).conn_iff, b2] at hbb'
      exact nBG2 (eB2.trans hbb')
  · -- `S_(k+1)` is not a cell: `S_k` has E1's shape, with `t` its outer front corner.
    suffices hw : front2 Sk s = t0 ∨ front2 Sk s = u0 by
      rcases hw with hw | hw
      · exact Or.inl ⟨s, Or.inr hw.symm, by rwa [hnb], eAB.symm, fun h => n12 h.symm, n2B, n1A⟩
      · exact Or.inr ⟨s, Or.inr hw.symm, by rwa [hnb], eAB.symm, fun h => n12 h.symm, n2B, n1A⟩
    have hcorn := isCell_corners hf s
    have hd : deg (lowerCol H c s n) (front2 Sk s) = 2 := by
      rw [M.factor.2 _ (M.hVW hcorn.2.2.2)]; exact M.hdc _ hf _ (isCorner_front2 _ _)
    rw [deg_front2, hnb] at hd
    have l1 : lat2 Sk s ∉ lowerCol H c s n := fun h => n1A ((ends_lat2 Sk s).conn h).symm
    have fr : front Sk s ∉ lowerCol H c s n := fun h => n12 ((ends_front Sk s).conn h).symm
    rw [ind_of_not_mem l1, ind_of_not_mem fr] at hd
    have hl : lat2 Sk1 s ∈ lowerCol H c s n := by
      by_contra hh; rw [ind_of_not_mem hh] at hd
      have := ind_le_one (lowerCol H c s n) (outer2 Sk s); omega
    have hG1 : front2 Sk1 s ∉ V := by
      intro hG
      apply hc1
      refine isCell_of_corners (a := s) ?_ ?_ ?_ hG
      · rw [← hnb, back1_nb]; exact hcorn.2.2.1
      · rw [← hnb, back2_nb]; exact hcorn.2.2.2
      · rw [hSk1, sideB_front1]
        exact (isCell_corners (M.cell (k + 1) (by omega)) s).2.2.2
    have hout := M.out_H1 (lat2 Sk1 s) hl
    have b1 : back2 Sk1 s = front2 Sk s := by rw [← hnb, back2_nb]
    rcases ends_lat2 Sk1 s with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [b1] at e1
      have := hout.2 (by rw [e2]; exact hG1)
      rw [e1] at this; exact this
    · rw [b1] at e2
      have := hout.1 (by rw [e1]; exact hG1)
      rw [e2] at this; exact this

-- **E1's shape after a move.**
--
theorem MoveCtx.tri_after (M : MoveCtx V W d H H' FP c s n i t0 u0) :
    ∀ f, IsCell V f → Three (lowerCol H c s n) f → TriOK V (lowerCol H c s n) t0 u0 f := by
  intro f hf h3
  have cc := M.conn
  by_cases hn : NearM c s n f
  · rcases near_cases hn with ⟨k, hk, rfl⟩ | ⟨k, h1, h2, rfl | rfl⟩
    · exfalso
      rcases (show k = 0 ∨ (1 ≤ k ∧ k ≤ n ∧ k % 2 = 1) ∨ (2 ≤ k ∧ k ≤ n ∧ k % 2 = 0) ∨ k = n + 1 by
          omega) with rfl | ⟨k1, k2, ko⟩ | ⟨k1, k2, ke⟩ | rfl
      · -- `c_0`: dark back and front
        rw [cellJ_zero] at h3
        have hb := (ends_back c s).conn (back0_after M.ev M.two M.pat)
        have hfr := (ends_front c s).conn (front0_after M.ev M.two M.pat)
        apply noThree_two (A := back1 c s) (B := front1 c s) _ h3
        intro u hu; rcases corner_cases c s hu with rfl | rfl | rfl | rfl
        · exact Or.inl (Conn.refl _ _)
        · exact Or.inl hb.symm
        · exact Or.inr (Conn.refl _ _)
        · exact Or.inr hfr.symm
      · -- odd `c_k`: dark front; the back corners are joined by the U-turn before the move
        have hfr := (ends_front (cellJ c s k) s).conn
          ((front_inner_after M.ev M.two M.pat k1 (by have := M.ev; omega)).2 ko)
        have hbH : Conn H (back1 (cellJ c s k) s) (back2 (cellJ c s k) s) := by
          have a1 := (ends_lat1 (cellJ c s k) s).conn ((M.pat.2.1 k (by omega)).1.2 ko)
          have a2 := (ends_lat2 (cellJ c s k) s).conn ((M.pat.2.1 k (by omega)).2.2 ko)
          have a3 := (ends_front (cellJ c s k) s).conn
            ((M.pat.2.2 k (by omega)).2 ⟨fun _ => by have := M.ev; omega, fun _ => ko⟩)
          exact a1.trans (a3.trans a2.symm)
        have nm1 : ¬ IsMid c s n (back1 (cellJ c s k) s) := by
          rw [back1_col k1]; exact (notMid_even (by omega)).1
        have nm2 : ¬ IsMid c s n (back2 (cellJ c s k) s) := by
          rw [back2_col k1]; exact (notMid_even (by omega)).2
        have hb := (cc _ _ nm1 nm2).2 hbH
        apply noThree_two (A := back1 (cellJ c s k) s) (B := front1 (cellJ c s k) s) _ h3
        intro u hu; rcases corner_cases (cellJ c s k) s hu with rfl | rfl | rfl | rfl
        · exact Or.inl (Conn.refl _ _)
        · exact Or.inl hb.symm
        · exact Or.inr (Conn.refl _ _)
        · exact Or.inr hfr.symm
      · -- even `c_k`: dark lateral sides
        have l1 := (ends_lat1 (cellJ c s k) s).conn
          ((lat1_after M.ev M.two M.pat (by omega) k2).2 ke)
        have l2 := (ends_lat2 (cellJ c s k) s).conn
          ((lat2_after M.ev M.two M.pat (by omega) k2).2 ke)
        apply noThree_two (A := back1 (cellJ c s k) s) (B := back2 (cellJ c s k) s) _ h3
        intro u hu; rcases corner_cases (cellJ c s k) s hu with rfl | rfl | rfl | rfl
        · exact Or.inl (Conn.refl _ _)
        · exact Or.inr (Conn.refl _ _)
        · exact Or.inl l1.symm
        · exact Or.inr l2.symm
      · -- `B`: dark front; back corners joined by `T`'s dark front before the move
        have hfB : front (cellJ c s (n + 1)) s ∈ lowerCol H c s n := by
          rw [mem_lowerCol_off (fun m _ _ => by rw [front_mem_cellE_iff]; omega)]
          exact (alt_opp_iff M.altB s).2 (by
            show back _ _ ∈ H; rw [back_cellJ_succ]
            exact frontn_mem M.ev M.two M.pat M.d1 M.d2 M.altB)
        have hfr := (ends_front (cellJ c s (n + 1)) s).conn hfB
        have hbH : Conn H (back1 (cellJ c s (n + 1)) s) (back2 (cellJ c s (n + 1)) s) := by
          have := (ends_back (cellJ c s (n + 1)) s).conn (by
            rw [back_cellJ_succ]; exact frontn_mem M.ev M.two M.pat M.d1 M.d2 M.altB)
          exact this
        have nm1 : ¬ IsMid c s n (back1 (cellJ c s (n + 1)) s) := by
          rw [back1_col (by omega), show n + 1 - 1 = n by omega]; exact (notMid_even M.ev).1
        have nm2 : ¬ IsMid c s n (back2 (cellJ c s (n + 1)) s) := by
          rw [back2_col (by omega), show n + 1 - 1 = n by omega]; exact (notMid_even M.ev).2
        have hb := (cc _ _ nm1 nm2).2 hbH
        apply noThree_two (A := back1 (cellJ c s (n + 1)) s) (B := front1 (cellJ c s (n + 1)) s) _ h3
        intro u hu; rcases corner_cases (cellJ c s (n + 1)) s hu with rfl | rfl | rfl | rfl
        · exact Or.inl (Conn.refl _ _)
        · exact Or.inl hb.symm
        · exact Or.inr (Conn.refl _ _)
        · exact Or.inr hfr.symm
    · rcases Nat.mod_two_eq_zero_or_one k with ke | ko
      · exfalso
        have hfr := (ends_front (nb (cellJ c s k) (latA s)) s).conn (by
          rw [side_front]; exact (M.outer1_H1 h2).2 ke)
        have hl := (ends_lat2 (nb (cellJ c s k) (latA s)) s).conn (by
          rw [side_near]; exact (lat1_after M.ev M.two M.pat h1 h2).2 ke)
        apply noThree_two (A := front2 (nb (cellJ c s k) (latA s)) s)
          (B := back1 (nb (cellJ c s k) (latA s)) s) _ h3
        intro u hu; rcases corner_cases (nb (cellJ c s k) (latA s)) s hu with rfl | rfl | rfl | rfl
        · exact Or.inr (Conn.refl _ _)
        · exact Or.inl hl
        · exact Or.inl hfr
        · exact Or.inl (Conn.refl _ _)
      · exact Or.inl (M.oddA_tri h1 h2 ko hf h3)
    · rcases Nat.mod_two_eq_zero_or_one k with ke | ko
      · exfalso
        have hfr := (ends_front (nb (cellJ c s k) (latB s)) s).conn (by
          rw [sideB_front]; exact (M.outer2_H1 h2).2 ke)
        have hl := (ends_lat1 (nb (cellJ c s k) (latB s)) s).conn (by
          rw [sideB_near]; exact (lat2_after M.ev M.two M.pat h1 h2).2 ke)
        apply noThree_two (A := front1 (nb (cellJ c s k) (latB s)) s)
          (B := back2 (nb (cellJ c s k) (latB s)) s) _ h3
        intro u hu; rcases corner_cases (nb (cellJ c s k) (latB s)) s hu with rfl | rfl | rfl | rfl
        · exact Or.inl hl
        · exact Or.inr (Conn.refl _ _)
        · exact Or.inl (Conn.refl _ _)
        · exact Or.inl hfr.symm
      · exact Or.inl (M.oddB_tri h1 h2 ko hf h3)
  · -- away from the move: nothing changes
    have ccf : ∀ {u v : Pt}, IsCorner u f → IsCorner v f →
        (Conn (lowerCol H c s n) u v ↔ Conn H u v) := fun hu hv => conn_corners_after cc hn hu hv
    have h3H : Three H f := by
      obtain ⟨u, v, w, hu, hv, hw, a, b, c'⟩ := h3
      exact ⟨u, v, w, hu, hv, hw, fun h => a ((ccf hu hv).2 h), fun h => b ((ccf hv hw).2 h),
        fun h => c' ((ccf hu hw).2 h)⟩
    rcases (M.inv.tri f hf h3H).ex with ⟨w, hw, sd, ht, hout, hbb, hff, h11, h22⟩ | ⟨hD1, hD2⟩
    swap
    · have k00 : IsCorner (f.1, f.2) f := Or.inl rfl
      have k10 : IsCorner (f.1 + 1, f.2) f := Or.inr (Or.inl rfl)
      have k01 : IsCorner (f.1, f.2 + 1) f := Or.inr (Or.inr (Or.inl rfl))
      have k11 : IsCorner (f.1 + 1, f.2 + 1) f := Or.inr (Or.inr (Or.inr rfl))
      refine Or.inr ⟨fun sd h => hD1 sd ((ccf (isCorner_front1 _ _) (isCorner_front2 _ _)).1 h), ?_⟩
      rcases hD2 with h | h
      · exact Or.inl ((ccf k00 k11).2 h)
      · exact Or.inr ((ccf k10 k01).2 h)
    have X : TriShape V (lowerCol H c s n) w f :=
      ⟨sd, ht, hout, (ccf (isCorner_back1 _ _) (isCorner_back2 _ _)).2 hbb,
        fun h => hff ((ccf (isCorner_front1 _ _) (isCorner_front2 _ _)).1 h),
        fun h => h11 ((ccf (isCorner_front1 _ _) (isCorner_back1 _ _)).1 h),
        fun h => h22 ((ccf (isCorner_front2 _ _) (isCorner_back2 _ _)).1 h)⟩
    rcases hw with rfl | rfl
    · exact Or.inl (Or.inl X)
    · exact Or.inl (Or.inr X)

end e1after

end HP

end SolidGridHam
