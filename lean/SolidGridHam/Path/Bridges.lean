/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import SolidGridHam.Path.Run
import SolidGridHam.Path.StuckL4

/-!
# Sheffield's phase: bridges

A **bridge** `b = (q, a, r)` is the row `cellJ q a 0 … cellJ q a (r−1)` from a critical square `q`
(frame `a`, dark back). A **bridge step** (`RowStep`) applies when the arcs across side `a` agree
along the row up to `cellJ (r−2)` and turn at `E = cellJ (r−1)`, `r` is even, the squares after `q`
are not cut, and flipping `E` splits its piece (`split`). The step flips `E`.

The split condition is checked by the algorithm. A row whose last flip does not split is a success
instead (lowering the whole row joins two pieces), so no planarity argument is needed here.

This file: the region facts right after the flip (`RegionOK`, `regionOK_new`) and flips of uncut
squares only split pieces (`conn_of_flip_uncut`).
-/

namespace SolidGridHam

namespace HP

open Finset Classical

structure Bridge where
  q : Pt
  a : Side
  r : ℕ

namespace Bridge

def cell (b : Bridge) (j : ℕ) : Pt := cellJ b.q b.a j

def E (b : Bridge) : Pt := b.cell (b.r - 1)

end Bridge

-- The bridge step's conditions in state `H`.
--
structure RowStep (V : Finset Pt) (H : Finset Edge) (b : Bridge) : Prop where
  two : 2 ≤ b.r
  even : b.r % 2 = 0
  cells : ∀ j < b.r, IsCell V (b.cell j)
  crit : CriticalIn H b.q b.a
  bk : back b.q b.a ∈ H
  uncut : ∀ j, 1 ≤ j → j < b.r → ¬ CutSq H (b.cell j)
  arcs : ∀ j, j + 1 < b.r → outArc H (b.cell j) b.a = outArc H b.q b.a
  last : outArc H b.E b.a ≠ outArc H b.q b.a
  split : ¬ Conn (flip H b.E) (back1 b.E b.a) (front1 b.E b.a)

-- The edge pattern of a bridge region after its flip (docs/PAIRS_PARTNER.md, (E0)–(E3)), with
-- the two cut facts (PF1, PF2).
--
structure RegionOK (H : Finset Edge) (b : Bridge) : Prop where
  bk : back b.q b.a ∈ H
  lat : ∀ j, 1 ≤ j → j + 2 ≤ b.r →
    (lat1 (b.cell j) b.a ∈ H ↔ j % 2 = 1) ∧ (lat2 (b.cell j) b.a ∈ H ↔ j % 2 = 1)
  lat0 : lat1 b.q b.a ∉ H ∧ lat2 b.q b.a ∉ H
  latE : lat1 b.E b.a ∉ H ∧ lat2 b.E b.a ∉ H
  fr : ∀ j, j + 3 ≤ b.r → (front (b.cell j) b.a ∈ H ↔ j % 2 = 1)
  frA : front (b.cell (b.r - 2)) b.a ∈ H
  frE : front b.E b.a ∈ H
  outer : ∀ j, j + 2 ≤ b.r →
    (outer1 (b.cell j) b.a ∈ H ↔ j % 2 = 0) ∧ (outer2 (b.cell j) b.a ∈ H ↔ j % 2 = 0)
  cut0 : ¬ Conn H (back1 b.q b.a) (front1 b.q b.a)
  cut0' : ¬ Conn H (back2 b.q b.a) (front2 b.q b.a)
  cutE : ¬ Conn H (back1 b.E b.a) (front1 b.E b.a)

section basic

-- A side of `c` is a side of exactly the two cells it separates.
--
lemma sideEdge_mem_cellE (c F : Pt) (s : Side) :
    sideEdge c s ∈ cellE F ↔ F = c ∨ F = nb c s := by
  obtain ⟨x, y⟩ := c
  obtain ⟨u, w⟩ := F
  cases s <;> simp only [cellE, sideEdge, bot, top, lft, rgt, nb, Finset.mem_insert,
    Finset.mem_singleton, Edge.mk.injEq, Prod.mk.injEq, reduceCtorEq, false_and,
    true_and, or_false, false_or] <;> omega

lemma corners_of_cellE {c : Pt} {e : Edge} (he : e ∈ cellE c) : IsCorner e.p c ∧ IsCorner e.q c := by
  obtain ⟨x, y⟩ := c
  simp only [cellE, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl <;> simp [IsCorner, bot, top, lft, rgt, Edge.q]

-- **Flips of uncut squares only split pieces.**
--
lemma conn_of_flip_uncut {F : Finset Edge} {c : Pt} (hc : ¬ CutSq F c) {u v : Pt}
    (h : Conn (flip F c) u v) : Conn F u v := by
  have hall : ∀ z, IsCorner z c → Conn F c z := by
    unfold CutSq at hc
    obtain ⟨h1, h2, h3⟩ := not_not.1 hc
    intro z hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact Conn.refl _ _
    · exact h1
    · exact h3
    · exact h2
  induction h with
  | refl => exact Conn.refl _ _
  | tail _ hst ih =>
    obtain ⟨e, he, hends⟩ := hst
    have step : Conn F e.p e.q := by
      unfold flip at he
      rcases Finset.mem_symmDiff.1 he with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact Conn.of_edge h1
      · obtain ⟨cp, cq⟩ := corners_of_cellE h1
        exact (hall _ cp).symm.trans (hall _ cq)
    rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2] at step; exact ih.trans step
    · rw [h1, h2] at step; exact ih.trans step.symm

-- The converse of `run_front`: fronts alternating from a light front give equal arcs.
--
lemma run_front' {F : Finset Edge} {q : Pt} {a : Side} (hf0 : front q a ∉ F) {j : ℕ}
    (hj : front (cellJ q a j) a ∈ F ↔ j % 2 = 1) :
    outArc F (cellJ q a j) a = outArc F q a := by
  rw [outArc_eq, outArc_eq, par_cellJ]
  have m0 : decide (sideEdge q a ∈ F) = false := by simp only [front] at hf0; simp [hf0]
  have mj : decide (sideEdge (cellJ q a j) a ∈ F) = decide (j % 2 = 1) := by
    simp only [front] at hj; simp only [hj]
  rw [m0, mj]
  cases par q <;> cases h : decide (j % 2 = 1) <;> cases a.horiz <;> simp

-- Degree 2 at `front1 c s` when `c`'s two sides there agree.
--
lemma outer1_gen {F : Finset Edge} {c : Pt} {s : Side} {P : Prop} (hd : deg F (front1 c s) = 2)
    (h1 : lat1 c s ∈ F ↔ P) (h2 : front c s ∈ F ↔ P) (h3 : lat1 (nb c s) s ∈ F ↔ ¬ P) :
    (outer1 c s ∈ F ↔ ¬ P) := by
  rw [deg_front1] at hd
  by_cases hP : P
  · rw [ind_of_mem (h1.2 hP), ind_of_mem (h2.2 hP), ind_of_not_mem (fun h => h3.1 h hP)] at hd
    constructor
    · intro ho; rw [ind_of_mem ho] at hd; omega
    · intro h; exact absurd hP h
  · rw [ind_of_not_mem (fun h => hP (h1.1 h)), ind_of_not_mem (fun h => hP (h2.1 h)),
      ind_of_mem (h3.2 hP)] at hd
    constructor
    · intro _; exact hP
    · intro _; by_contra ho; rw [ind_of_not_mem ho] at hd; omega

lemma outer2_gen {F : Finset Edge} {c : Pt} {s : Side} {P : Prop} (hd : deg F (front2 c s) = 2)
    (h1 : lat2 c s ∈ F ↔ P) (h2 : front c s ∈ F ↔ P) (h3 : lat2 (nb c s) s ∈ F ↔ ¬ P) :
    (outer2 c s ∈ F ↔ ¬ P) := by
  rw [deg_front2] at hd
  by_cases hP : P
  · rw [ind_of_mem (h1.2 hP), ind_of_mem (h2.2 hP), ind_of_not_mem (fun h => h3.1 h hP)] at hd
    constructor
    · intro ho; rw [ind_of_mem ho] at hd; omega
    · intro h; exact absurd hP h
  · rw [ind_of_not_mem (fun h => hP (h1.1 h)), ind_of_not_mem (fun h => hP (h2.1 h)),
      ind_of_mem (h3.2 hP)] at hd
    constructor
    · intro _; exact hP
    · intro _; by_contra ho; rw [ind_of_not_mem ho] at hd; omega

end basic

section creation

variable {V : Finset Pt} {H : Finset Edge}

-- **The region right after the bridge flip.**
--
theorem regionOK_new {b : Bridge} (hrs : RowStep V H b)
    (hdegc : ∀ f, IsCell V f → ∀ z, IsCorner z f → deg H z = 2) :
    RegionOK (flip H b.E) b := by
  obtain ⟨q, a, r⟩ := b
  obtain ⟨two, even, cells, crit, bk, uncut, arcs, last, split⟩ := hrs
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 2 := ⟨r - 2, by simp only at two; omega⟩
  simp only [Bridge.cell, Bridge.E, show m + 2 - 1 = m + 1 by omega] at *
  have meven : m % 2 = 0 := by omega
  have dF1 : ∀ j < m + 2, deg H (front1 (cellJ q a j) a) = 2 := fun j hj =>
    hdegc _ (cells j hj) _ (isCorner_front1 _ _)
  have dF2 : ∀ j < m + 2, deg H (front2 (cellJ q a j) a) = 2 := fun j hj =>
    hdegc _ (cells j hj) _ (isCorner_front2 _ _)
  have rp := run_pat crit bk (n := m) (fun j hj => ⟨dF1 j (by omega), dF2 j (by omega)⟩)
    (fun j hj => arcs j (by omega))
  obtain ⟨lm1, lm2, fm⟩ := rp m le_rfl
  have l1m : lat1 (cellJ q a m) a ∉ H := fun h => by have := lm1.1 h; omega
  have l2m : lat2 (cellJ q a m) a ∉ H := fun h => by have := lm2.1 h; omega
  have f_m : front (cellJ q a m) a ∉ H := fun h => by have := fm.1 h; omega
  obtain ⟨oA, lE1⟩ := forcedA l1m f_m (dF1 m (by omega))
  obtain ⟨oB, lE2⟩ := forcedB l2m f_m (dF2 m (by omega))
  rw [nb_cellJ] at lE1 lE2
  have hf0 : front q a ∉ H := fun h => by
    rcases crit.2.2.2 with ⟨_, h2⟩ | ⟨_, h1⟩
    · exact h2 h
    · exact h1 bk
  have fE : front (cellJ q a (m + 1)) a ∉ H := by
    intro h
    apply last
    exact run_front' hf0 ⟨fun _ => by omega, fun _ => h⟩
  have keep : ∀ e, e ∉ cellE (cellJ q a (m + 1)) → (e ∈ flip H (cellJ q a (m + 1)) ↔ e ∈ H) :=
    fun e he => by rw [mem_flip_iff]; tauto
  have tog : ∀ e, e ∈ cellE (cellJ q a (m + 1)) → (e ∈ flip H (cellJ q a (m + 1)) ↔ e ∉ H) :=
    fun e he => by rw [mem_flip_iff]; tauto
  have outs : ∀ j ≤ m, (outer1 (cellJ q a j) a ∈ H ↔ j % 2 = 0) ∧
      (outer2 (cellJ q a j) a ∈ H ↔ j % 2 = 0) := by
    intro j hj
    rcases Nat.lt_or_ge j m with hlt | hge
    · obtain ⟨l1, l2, f1⟩ := rp j (by omega)
      obtain ⟨l1', l2', _⟩ := rp (j + 1) (by omega)
      rw [← nb_cellJ] at l1' l2'
      have o1 := outer1_gen (dF1 j (by omega)) l1 f1 (by rw [l1']; omega)
      have o2 := outer2_gen (dF2 j (by omega)) l2 f1 (by rw [l2']; omega)
      exact ⟨by rw [o1]; omega, by rw [o2]; omega⟩
    · obtain rfl : j = m := by omega
      exact ⟨⟨fun _ => meven, fun _ => oA⟩, ⟨fun _ => meven, fun _ => oB⟩⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, split⟩ <;>
    simp only [Bridge.cell, Bridge.E, show m + 2 - 1 = m + 1 by omega,
      show m + 2 - 2 = m by omega]
  · rw [keep]
    · exact bk
    · unfold back
      rw [sideEdge_mem_cellE]
      rintro (h | h)
      · have := cellJ_inj (c := q) (s := a) (i := m + 1) (j := 0) (by rw [h, cellJ_zero])
        omega
      · have h2 : nb (cellJ q a (m + 1)) a = q := by
          have := nb_nb_opp q a.opp; rw [opp_opp] at this; rw [h]; exact this
        rw [nb_cellJ] at h2
        have := cellJ_inj (c := q) (s := a) (i := m + 1 + 1) (j := 0) (by rw [h2, cellJ_zero])
        omega
  · intro j hj1 hj2
    obtain ⟨l1, l2, _⟩ := rp j (by omega)
    rw [keep _ (fun h => by rw [lat1_mem_cellE_iff] at h; omega),
      keep _ (fun h => by rw [lat2_mem_cellE_iff] at h; omega)]
    exact ⟨l1, l2⟩
  · obtain ⟨l1, l2, _⟩ := rp 0 (by omega)
    rw [cellJ_zero] at l1 l2
    have n1 : lat1 q a ∉ cellE (cellJ q a (m + 1)) := by
      have := lat1_mem_cellE_iff (c := q) (s := a) 0 (m + 1)
      rw [cellJ_zero] at this; rw [this]; omega
    have n2 : lat2 q a ∉ cellE (cellJ q a (m + 1)) := by
      have := lat2_mem_cellE_iff (c := q) (s := a) 0 (m + 1)
      rw [cellJ_zero] at this; rw [this]; omega
    rw [keep _ n1, keep _ n2]
    exact ⟨fun h => by have := l1.1 h; omega, fun h => by have := l2.1 h; omega⟩
  · rw [tog _ (by rw [lat1_mem_cellE_iff]), tog _ (by rw [lat2_mem_cellE_iff])]
    exact ⟨not_not.2 lE1, not_not.2 lE2⟩
  · intro j hj
    obtain ⟨_, _, f1⟩ := rp j (by omega)
    rw [keep _ (fun h => by rw [front_mem_cellE_iff] at h; omega)]
    exact f1
  · rw [tog _ (by rw [front_mem_cellE_iff]; omega)]; exact f_m
  · rw [tog _ (by rw [front_mem_cellE_iff]; omega)]; exact fE
  · intro j hj
    rw [keep _ (outer1_not_mem (c := q) (s := a) j (m + 1)), keep _ (outer2_not_mem (c := q) (s := a) j (m + 1))]
    exact outs j (by omega)
  · intro h
    exact crit.2.2.1 (conn_of_flip_uncut (uncut (m + 1) (by omega) (by omega)) h)
  · intro h
    exact crit.2.2.1 (crit.1.trans ((conn_of_flip_uncut (uncut (m + 1) (by omega) (by omega)) h).trans
      crit.2.1.symm))

end creation

end HP

end SolidGridHam
