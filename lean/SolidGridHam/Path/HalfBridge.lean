/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import SolidGridHam.Path.UndoCount

@[expose] public section

/-!
# S4: the half bridge (docs/S4_UNDO.md §III)

`join_apply`: an intact odd strip whose end pairs are apart lowers the count by one, keeps the
factor, and merges the two end classes (off its interior points). The half bridge of each success
branch is such a strip:
* (a) a merging cell (`merge_join`): a strip of one cell;
* (b) an odd row (`oddRow_pat`);
* (c) an even row whose last flip does not split (`twist_count`).
-/

namespace SolidGridHam

namespace HP

open Finset Classical

section half

variable {W : Finset Pt} {d : Pt → ℕ} {s0 p0 : Pt}

theorem join_apply (hd2 : ∀ z ∈ W, z ≠ s0 → z ≠ p0 → d z = 2) (hds : d s0 = 1) (hs0 : s0 ∈ W)
    {G : Finset Edge} (hG : IsFactor W d G) {o : Join} (pat : StripPat G o.c o.a o.n)
    (odd : o.n % 2 = 1) (cells : ∀ j < o.n, IsCell W (cellJ o.c o.a j))
    (corners : ∀ j < o.n, ¬ IsCorner s0 (cellJ o.c o.a j) ∧ ¬ IsCorner p0 (cellJ o.c o.a j))
    (hnp : ¬ Conn G (back1 o.c o.a) (front1 o.c o.a)) :
    IsFactor W d (o.apply G) ∧ ncomp W (o.apply G) + 1 = ncomp W G ∧
      ∀ x y, ¬ IsMid o.c o.a (o.n - 1) x → ¬ IsMid o.c o.a (o.n - 1) y →
        (Conn (o.apply G) x y ↔ merge (Conn G) (back1 o.c o.a) (front1 o.c o.a) x y) := by
  have hD : Deg2Off W G s0 p0 := ⟨fun e he => by
      have := hG.1 e he
      exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem this.1),
        Finset.mem_insert_of_mem (Finset.mem_insert_of_mem this.2)⟩,
    fun z hz h1 h2 => by rw [hG.2 z hz, hd2 z hz h1 h2]⟩
  have hdeg : deg G s0 = 1 := by rw [hG.2 s0 hs0, hds]
  have hst : Conn G s0 p0 := conn_st hD hs0 hdeg
  have hn1 : o.n - 1 + 1 = o.n := by omega
  obtain ⟨cnt, crel⟩ := strip_odd_pf (V := W) (c := o.c) (s := o.a) (o.n - 1) (by omega) G hD
    hst (fun j hj => cells j (by omega)) (fun j hj => corners j (by omega))
    (by rw [hn1]; exact pat) hnp
  rw [hn1] at cnt crel
  obtain ⟨hin, hdg⟩ := degs_flipCol o.n G (Inside.of_factor hG) pat cells
  exact ⟨⟨fun e he => hin e he, fun z hz => by unfold Join.apply; rw [hdg z, hG.2 z hz]⟩,
    cnt, fun x y hx hy => crel x y hx hy⟩

-- **(a)** A cut alternating cell is a strip of one cell in the frame of its dark sides.
--
theorem merge_join {G : Finset Edge} {c : Pt} (ha : Alt G c) (hcut : CutSq G c) :
    ∃ a, StripPat G c a 1 ∧ ¬ Conn G (back1 c a) (front1 c a) := by
  have frame : ∃ a, back c a ∈ G ∧ front c a ∈ G ∧ lat1 c a ∉ G ∧ lat2 c a ∉ G := by
    unfold Alt at ha
    rcases ha with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
    · exact ⟨.t, h1, h2, h3, h4⟩
    · exact ⟨.r, h3, h4, h1, h2⟩
  obtain ⟨a, hb, hf, hl1, hl2⟩ := frame
  refine ⟨a, ⟨hb, fun j hj => ?_, fun j hj => ?_⟩, fun h => ?_⟩
  · obtain rfl : j = 0 := by omega
    rw [cellJ_zero]
    exact ⟨⟨fun h => absurd h hl1, fun h => by omega⟩, ⟨fun h => absurd h hl2, fun h => by omega⟩⟩
  · obtain rfl : j = 0 := by omega
    rw [cellJ_zero]; exact ⟨fun _ => by omega, fun _ => hf⟩
  · have kb := (ends_back (c := c) (s := a)).conn hb
    have kf := (ends_front (c := c) (s := a)).conn hf
    exact uncut_of kb h ((kb.symm.trans h).trans kf) hcut

end half

section oddrow

variable {V : Finset Pt} {H : Finset Edge}

-- **(b)** The strip pattern of an odd row.
--
theorem oddRow_pat {BS : List Bridge} {b : Bridge} (mf : MoveFacts V H BS b) (ho : b.r % 2 = 1)
    (hdegc : ∀ f, IsCell V f → ∀ z, IsCorner z f → deg H z = 2) :
    StripPat H b.q b.a b.r ∧ ¬ Conn H (back1 b.q b.a) (front1 b.q b.a) := by
  obtain ⟨hq, crit, bk, _, two, cells, _, arcs, last⟩ := mf
  obtain ⟨q, a, r⟩ := b
  simp only [Bridge.cell, Bridge.E] at *
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 3 := ⟨r - 3, by omega⟩
  have dF1 : ∀ j < m + 3, deg H (front1 (cellJ q a j) a) = 2 := fun j hj =>
    hdegc _ (cells j hj) _ (isCorner_front1 _ _)
  have dF2 : ∀ j < m + 3, deg H (front2 (cellJ q a j) a) = 2 := fun j hj =>
    hdegc _ (cells j hj) _ (isCorner_front2 _ _)
  have rp := run_pat crit bk (n := m + 1) (fun j hj => ⟨dF1 j (by omega), dF2 j (by omega)⟩)
    (fun j hj => arcs j (by omega))
  obtain ⟨l1, l2, f1⟩ := rp (m + 1) le_rfl
  have hodd : (m + 1) % 2 = 1 := by omega
  have ll1 : lat1 (cellJ q a (m + 2)) a ∉ H := by
    rw [← nb_cellJ]; exact forcedA' (l1.2 hodd) (f1.2 hodd) (dF1 _ (by omega))
  have ll2 : lat2 (cellJ q a (m + 2)) a ∉ H := by
    rw [← nb_cellJ]; exact forcedB' (l2.2 hodd) (f1.2 hodd) (dF2 _ (by omega))
  have hf0 : front q a ∉ H := fun h => by
    rcases crit.2.2.2 with ⟨_, h2⟩ | ⟨_, h1⟩
    · exact h2 h
    · exact h1 bk
  have flast : front (cellJ q a (m + 2)) a ∈ H := by
    by_contra h
    exact last (by
      rw [show m + 3 - 1 = m + 2 by omega]
      exact run_front' hf0 ⟨fun h' => absurd h' h, fun h' => by omega⟩)
  refine ⟨⟨bk, fun j hj => ?_, fun j hj => ?_⟩, crit.2.2.1⟩
  · rcases Nat.lt_or_ge j (m + 2) with h | h
    · obtain ⟨a1, a2, _⟩ := rp j (by omega); exact ⟨a1, a2⟩
    · obtain rfl : j = m + 2 := by omega
      exact ⟨⟨fun h => absurd h ll1, fun h => by omega⟩, ⟨fun h => absurd h ll2, fun h => by omega⟩⟩
  · rcases Nat.lt_or_ge j (m + 2) with h | h
    · obtain ⟨_, _, a3⟩ := rp j (by omega); rw [a3]; omega
    · obtain rfl : j = m + 2 := by omega
      exact ⟨fun _ => by omega, fun _ => flast⟩

end oddrow

section twist

variable {V W : Finset Pt} {d : Pt → ℕ} {s0 p0 : Pt} {H : Finset Edge}

-- **(c)** An even row whose last flip does not split: lowering the whole row lowers the count by
-- one and merges the start pair.
--
theorem twist_count (hVW : V ⊆ W) (hd2 : ∀ z ∈ W, z ≠ s0 → z ≠ p0 → d z = 2) (hds : d s0 = 1)
    (hs0 : s0 ∈ W) (hH : IsFactor W d H) {BS : List Bridge} {b : Bridge}
    (mf : MoveFacts V H BS b) (he : b.r % 2 = 0)
    (htw : Conn (flip H b.E) (back1 b.E b.a) (front1 b.E b.a))
    (hdegc : ∀ f, IsCell V f → ∀ z, IsCorner z f → deg H z = 2)
    (hcor : ∀ j < b.r, ¬ IsCorner s0 (b.cell j) ∧ ¬ IsCorner p0 (b.cell j)) :
    IsFactor W d (flipCol H b.q b.a b.r) ∧ ncomp W (flipCol H b.q b.a b.r) + 1 = ncomp W H ∧
      ∀ x y, ¬ IsMid b.q b.a (b.r - 2) x → ¬ IsMid b.q b.a (b.r - 2) y →
        (Conn (flipCol H b.q b.a b.r) x y ↔ merge (Conn H) (back1 b.q b.a) (front1 b.q b.a) x y) := by
  obtain ⟨hq, crit, bk, _, two, cells, uncut, arcs, last⟩ := mf
  obtain ⟨q, a, r⟩ := b
  simp only [Bridge.cell, Bridge.E] at *
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 2 := ⟨r - 2, by omega⟩
  simp only [show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega] at *
  have meven : m % 2 = 0 := by omega
  have dF1 : ∀ j < m + 2, deg H (front1 (cellJ q a j) a) = 2 := fun j hj =>
    hdegc _ (cells j hj) _ (isCorner_front1 _ _)
  have dF2 : ∀ j < m + 2, deg H (front2 (cellJ q a j) a) = 2 := fun j hj =>
    hdegc _ (cells j hj) _ (isCorner_front2 _ _)
  have rp := run_pat crit bk (n := m) (fun j hj => ⟨dF1 j (by omega), dF2 j (by omega)⟩)
    (fun j hj => arcs j (by omega))
  obtain ⟨l1, l2, f1⟩ := rp m le_rfl
  have l1m : lat1 (cellJ q a m) a ∉ H := fun h => by have := l1.1 h; omega
  have l2m : lat2 (cellJ q a m) a ∉ H := fun h => by have := l2.1 h; omega
  have f_m : front (cellJ q a m) a ∉ H := fun h => by have := f1.1 h; omega
  obtain ⟨_, lE1⟩ := forcedA l1m f_m (dF1 m (by omega))
  obtain ⟨_, lE2⟩ := forcedB l2m f_m (dF2 m (by omega))
  rw [nb_cellJ] at lE1 lE2
  have hf0 : front q a ∉ H := fun h => by
    rcases crit.2.2.2 with ⟨_, h2⟩ | ⟨_, h1⟩
    · exact h2 h
    · exact h1 bk
  have fE : front (cellJ q a (m + 1)) a ∉ H := by
    intro h; apply last; exact run_front' hf0 ⟨fun _ => by omega, fun _ => h⟩
  have pat : StripPat H q a (m + 2) := by
    refine ⟨bk, fun j hj => ?_, fun j hj => ?_⟩
    · rcases Nat.lt_or_ge j (m + 1) with h | h
      · obtain ⟨a1, a2, _⟩ := rp j (by omega); exact ⟨a1, a2⟩
      · obtain rfl : j = m + 1 := by omega
        exact ⟨⟨fun _ => by omega, fun _ => lE1⟩, ⟨fun _ => by omega, fun _ => lE2⟩⟩
    · rcases Nat.lt_or_ge j (m + 1) with h | h
      · obtain ⟨_, _, a3⟩ := rp j (by omega); rw [a3]; omega
      · obtain rfl : j = m + 1 := by omega
        exact ⟨fun h' => absurd h' fE, fun h' => by omega⟩
  have hD : Deg2Off W H s0 p0 := ⟨fun e he => by
      have := hH.1 e he
      exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem this.1),
        Finset.mem_insert_of_mem (Finset.mem_insert_of_mem this.2)⟩,
    fun z hz h1 h2 => by rw [hH.2 z hz, hd2 z hz h1 h2]⟩
  have hdeg : deg H s0 = 1 := by rw [hH.2 s0 hs0, hds]
  have hsame : Conn H (back1 (cellJ q a (m + 1)) a) (back2 (cellJ q a (m + 1)) a) :=
    conn_of_uncut (uncut (m + 1) (by omega) (by omega)) (isCorner_back1 _ _) (isCorner_back2 _ _)
  obtain ⟨F1, rfl, heq, _, hrel, hcrel, hcnt, _⟩ := strip_even_rel_pf (V := W) (c := q) (s := a)
    (s0 := s0) (t0 := p0) m meven H hD hs0 hdeg (fun j hj => isCell_mono (cells j (by omega)) hVW)
    (fun j hj => hcor j (by omega)) pat crit.2.2.1 hsame
  -- The twist: connections before and after the flip of `E` agree.
  --
  have same : ∀ x y, Conn H x y ↔ Conn (flip H (cellJ q a (m + 1))) x y := by
    intro x y
    rw [hrel]
    constructor
    · rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact h
      · exact (h1.trans htw).trans h2
      · exact (h1.trans htw.symm).trans h2
    · exact fun h => Or.inl h
  have hn : ncomp W (flip H (cellJ q a (m + 1))) = ncomp W H :=
    ncomp_congr (fun x _ y _ => (same x y).symm)
  obtain ⟨hin, hdg⟩ := degs_flipCol (m + 2) H (Inside.of_factor hH) pat
    (fun j hj => isCell_mono (cells j hj) hVW)
  refine ⟨⟨fun e he => hin e he, fun z hz => by rw [hdg z, hH.2 z hz]⟩, by omega,
    fun x y hx hy => ?_⟩
  rw [hcrel x y hx hy]
  unfold merge
  rw [← same, ← same, ← same, ← same, ← same]

end twist

section evenrow

variable {V : Finset Pt} {H : Finset Edge}

-- **(c)** The strip pattern of an even row before its last flip (last cell: dark laterals).
--
theorem evenRow_pat {BS : List Bridge} {b : Bridge} (mf : MoveFacts V H BS b) (he : b.r % 2 = 0)
    (hdegc : ∀ f, IsCell V f → ∀ z, IsCorner z f → deg H z = 2) :
    StripPat H b.q b.a b.r ∧ lat1 b.E b.a ∈ H ∧ lat2 b.E b.a ∈ H := by
  obtain ⟨hq, crit, bk, _, two, cells, uncut, arcs, last⟩ := mf
  obtain ⟨q, a, r⟩ := b
  simp only [Bridge.cell, Bridge.E] at *
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 2 := ⟨r - 2, by omega⟩
  simp only [show m + 2 - 1 = m + 1 by omega] at *
  have meven : m % 2 = 0 := by omega
  have dF1 : ∀ j < m + 2, deg H (front1 (cellJ q a j) a) = 2 := fun j hj =>
    hdegc _ (cells j hj) _ (isCorner_front1 _ _)
  have dF2 : ∀ j < m + 2, deg H (front2 (cellJ q a j) a) = 2 := fun j hj =>
    hdegc _ (cells j hj) _ (isCorner_front2 _ _)
  have rp := run_pat crit bk (n := m) (fun j hj => ⟨dF1 j (by omega), dF2 j (by omega)⟩)
    (fun j hj => arcs j (by omega))
  obtain ⟨l1, l2, f1⟩ := rp m le_rfl
  have l1m : lat1 (cellJ q a m) a ∉ H := fun h => by have := l1.1 h; omega
  have l2m : lat2 (cellJ q a m) a ∉ H := fun h => by have := l2.1 h; omega
  have f_m : front (cellJ q a m) a ∉ H := fun h => by have := f1.1 h; omega
  obtain ⟨_, lE1⟩ := forcedA l1m f_m (dF1 m (by omega))
  obtain ⟨_, lE2⟩ := forcedB l2m f_m (dF2 m (by omega))
  rw [nb_cellJ] at lE1 lE2
  have hf0 : front q a ∉ H := fun h => by
    rcases crit.2.2.2 with ⟨_, h2⟩ | ⟨_, h1⟩
    · exact h2 h
    · exact h1 bk
  have fE : front (cellJ q a (m + 1)) a ∉ H := by
    intro h; apply last; exact run_front' hf0 ⟨fun _ => by omega, fun _ => h⟩
  refine ⟨⟨bk, fun j hj => ?_, fun j hj => ?_⟩, lE1, lE2⟩
  · rcases Nat.lt_or_ge j (m + 1) with h | h
    · obtain ⟨a1, a2, _⟩ := rp j (by omega); exact ⟨a1, a2⟩
    · obtain rfl : j = m + 1 := by omega
      exact ⟨⟨fun _ => by omega, fun _ => lE1⟩, ⟨fun _ => by omega, fun _ => lE2⟩⟩
  · rcases Nat.lt_or_ge j (m + 1) with h | h
    · obtain ⟨_, _, a3⟩ := rp j (by omega); rw [a3]; omega
    · obtain rfl : j = m + 1 := by omega
      exact ⟨fun h' => absurd h' fE, fun h' => by omega⟩

end evenrow

end HP

end SolidGridHam
