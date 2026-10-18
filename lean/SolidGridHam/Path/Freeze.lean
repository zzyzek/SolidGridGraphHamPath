/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import SolidGridHam.Path.Bridges

@[expose] public section

/-!
# The region freeze

A later bridge step flips a square `F` that is uncut, alternating with dark laterals, and whose
back side continues past both ends in dark edges (`rowStep_pre`). No square of an existing bridge
region has all of that (docs/PAIRS_PARTNER.md Theorem 1, docs/COL_SIDE.md Lemma B):
* `q`, the side squares beside `q` and beside `E`: cut;
* the inner squares and inner side squares: not alternating;
* `A = cellJ (r−2)`, `E`, the square beyond `E` and the square before `q`: a continuation of the
  back side of `F` would be a light lateral side (`not_flip_cell`).

So every edge of the region keeps its status, and `RegionOK` persists (`regionOK_step`).
-/

namespace SolidGridHam

namespace HP

open Finset Classical

section geo

lemma geomA (X : Pt) (a : Side) :
    (outer1 (nb X (latA a).opp) (latA a) = lat2 (nb X a) a ∧
      outer2 (nb X (latA a).opp) (latA a) = lat2 (nb X a.opp) a) ∨
    (outer1 (nb X (latA a).opp) (latA a) = lat2 (nb X a.opp) a ∧
      outer2 (nb X (latA a).opp) (latA a) = lat2 (nb X a) a) := by
  obtain ⟨x, y⟩ := X
  cases a <;> simp only [outer1, outer2, lat2, nb, latA, Side.opp, rgt, top,
    Edge.mk.injEq, Prod.mk.injEq, true_and] <;> simp

lemma geomB (X : Pt) (a : Side) :
    (outer1 (nb X (latB a).opp) (latB a) = lat1 (nb X a) a ∧
      outer2 (nb X (latB a).opp) (latB a) = lat1 (nb X a.opp) a) ∨
    (outer1 (nb X (latB a).opp) (latB a) = lat1 (nb X a.opp) a ∧
      outer2 (nb X (latB a).opp) (latB a) = lat1 (nb X a) a) := by
  obtain ⟨x, y⟩ := X
  cases a <;> simp only [outer1, outer2, lat1, nb, latB, Side.opp, lft, bot,
    Edge.mk.injEq, Prod.mk.injEq, true_and] <;> simp

lemma alt_of_lats {F : Finset Edge} {c : Pt} {s : Side} (h1 : lat1 c s ∈ F) (h2 : lat2 c s ∈ F)
    (hb : back c s ∉ F) (hf : front c s ∉ F) : Alt F c := by
  unfold Alt
  cases s <;> simp only [back, front, lat1, lat2, sideEdge, Side.opp] at h1 h2 hb hf <;> tauto

end geo

section freeze

variable {V : Finset Pt} {H : Finset Edge}

-- The flipped square of a bridge step, before the flip.
--
theorem rowStep_pre {b : Bridge} (hrs : RowStep V H b)
    (hdegc : ∀ f, IsCell V f → ∀ z, IsCorner z f → deg H z = 2) :
    lat1 b.E b.a ∈ H ∧ lat2 b.E b.a ∈ H ∧ back b.E b.a ∉ H ∧ front b.E b.a ∉ H ∧
      outer1 (nb b.E b.a.opp) b.a ∈ H ∧ outer2 (nb b.E b.a.opp) b.a ∈ H ∧ ¬ CutSq H b.E := by
  obtain ⟨q, a, r⟩ := b
  obtain ⟨two, even, cells, crit, bk, uncut, arcs, last, split⟩ := hrs
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 2 := ⟨r - 2, by simp only at two; omega⟩
  simp only [Bridge.cell, Bridge.E, show m + 2 - 1 = m + 1 by omega] at *
  have hun := uncut (m + 1) (by omega) (by omega)
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
  rw [nb_cellJ_opp, back_cellJ_succ]
  exact ⟨lE1, lE2, f_m, fE, oA, oB, hun⟩

-- **A square with a frozen continuation is not flipped.** `F = X` would be alternating with
-- dark laterals in frame `a'`, its back side continuing in dark edges past both ends; `X` has a
-- light lateral or a dark back/front in frame `a`, and the two laterals of a neighbour in frame `a`
-- are light.
--
lemma not_flip_cell {F : Pt} {a' a : Side} (l1 : lat1 F a' ∈ H) (l2 : lat2 F a' ∈ H)
    (bk : back F a' ∉ H) (fr : front F a' ∉ H) (o1 : outer1 (nb F a'.opp) a' ∈ H)
    (o2 : outer2 (nb F a'.opp) a' ∈ H)
    (hpar : (lat1 F a ∉ H ∨ lat2 F a ∉ H) ∨ (sideEdge F a ∈ H ∨ sideEdge F a.opp ∈ H))
    (hperp : ∃ d, (d = a ∨ d = a.opp) ∧ lat1 (nb F d) a ∉ H ∧ lat2 (nb F d) a ∉ H) : False := by
  obtain ⟨d, hd, hd1, hd2⟩ := hperp
  rcases side_cases a a' with rfl | rfl | rfl | rfl
  · rcases hpar with (h | h) | (h | h)
    · exact h l1
    · exact h l2
    · exact fr h
    · exact bk h
  · rw [lat1_sopp] at l1; rw [lat2_sopp] at l2
    rcases hpar with (h | h) | (h | h)
    · exact h l1
    · exact h l2
    · exact bk (by unfold back; rw [opp_opp]; exact h)
    · exact fr h
  · rcases geomA F a with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1] at o1 <;> rw [e2] at o2 <;>
      rcases hd with rfl | rfl <;> first | exact hd2 o1 | exact hd2 o2
  · rcases geomB F a with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1] at o1 <;> rw [e2] at o2 <;>
      rcases hd with rfl | rfl <;> first | exact hd1 o1 | exact hd1 o2

lemma keep_of {F c : Pt} {s : Side} (h1 : F ≠ c) (h2 : F ≠ nb c s) :
    sideEdge c s ∈ flip H F ↔ sideEdge c s ∈ H := by
  rw [mem_flip_iff, sideEdge_mem_cellE]
  constructor
  · intro h; exact h.2 (by rintro (h' | h') <;> [exact h1 h'; exact h2 h'])
  · intro h; exact ⟨fun _ => by rintro (h' | h') <;> [exact h1 h'; exact h2 h'], fun _ => h⟩

lemma cutSq_of_ne {F : Finset Edge} {c u v : Pt} (hu : IsCorner u c) (hv : IsCorner v c)
    (h : ¬ Conn F u v) {X : Pt} (hX : ¬ CutSq F X) : X ≠ c := by
  rintro rfl; exact hX (cutSq_of_corners hu hv h)

-- **No later step flips a square of a bridge region.**
--
theorem flip_not_region {b b' : Bridge} (hR : RegionOK H b) (htwo : 2 ≤ b.r) (hev : b.r % 2 = 0)
    (hrs : RowStep V H b') (hdegc : ∀ f, IsCell V f → ∀ z, IsCorner z f → deg H z = 2) :
    (∀ j ≤ b.r, b'.E ≠ b.cell j) ∧ b'.E ≠ nb b.q b.a.opp ∧
      (∀ j, j + 1 ≤ b.r → b'.E ≠ nb (b.cell j) (latA b.a) ∧ b'.E ≠ nb (b.cell j) (latB b.a)) := by
  obtain ⟨Fl1, Fl2, Fbk, Ffr, Fo1, Fo2, Fun⟩ := rowStep_pre hrs hdegc
  have Falt := alt_of_lats Fl1 Fl2 Fbk Ffr
  set F := b'.E with hFdef
  set a' := b'.a
  obtain ⟨q, a, r⟩ := b
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 2 := ⟨r - 2, by simp only at htwo; omega⟩
  obtain ⟨bk, lat, lat0, latE, fr, frA, frE, outer, cut0, cut0', cutE⟩ := hR
  simp only [Bridge.cell, Bridge.E, show m + 2 - 1 = m + 1 by omega,
    show m + 2 - 2 = m by omega] at *
  have meven : m % 2 = 0 := by omega
  -- Lateral sides of the column squares `1 … m` (the last is `A`).
  --
  have latL : ∀ j, 1 ≤ j → j ≤ m → (lat1 (cellJ q a j) a ∈ H ↔ j % 2 = 1) ∧
      (lat2 (cellJ q a j) a ∈ H ↔ j % 2 = 1) := fun j h1 h2 => lat j h1 (by omega)
  -- `A`'s laterals are light (for `m = 0`, `A = q`).
  --
  have latA' : lat1 (cellJ q a m) a ∉ H ∧ lat2 (cellJ q a m) a ∉ H := by
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · subst h0; rw [cellJ_zero]; exact lat0
    · obtain ⟨a1, a2⟩ := latL m hpos le_rfl
      exact ⟨fun h => by have := a1.1 h; omega, fun h => by have := a2.1 h; omega⟩
  have bE : back (cellJ q a (m + 1)) a ∈ H := by rw [back_cellJ_succ]; exact frA
  have cutE' : ¬ Conn H (back2 (cellJ q a (m + 1)) a) (front2 (cellJ q a (m + 1)) a) :=
    fun h => cutE (((ends_back (c := cellJ q a (m + 1)) (s := a)).conn bE).trans
      (h.trans ((ends_front (c := cellJ q a (m + 1)) (s := a)).conn frE).symm))
  -- `F` is none of the region's squares.
  --
  have nq : F ≠ q := by
    have := cutSq_of_ne (isCorner_back1 q a) (isCorner_front1 q a) cut0 Fun; exact this
  have ncol : ∀ j ≤ m + 2, F ≠ cellJ q a j := by
    intro j hj hFj
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · subst h0; rw [cellJ_zero] at hFj; exact nq hFj
    rcases (show (j < m ∨ j = m) ∨ j = m + 1 ∨ j = m + 2 by omega) with (hlt | rfl) | rfl | rfl
    · -- inner squares: not alternating
      rw [hFj] at Falt
      rcases Nat.mod_two_eq_zero_or_one j with he | ho
      · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        apply not_alt_of_ne (s' := a) _ Falt
        have h1 : sideEdge (cellJ q a (j' + 1)) a ∉ H := fun h => by
          have := (fr (j' + 1) (by omega)).1 h; omega
        have h2 : sideEdge (cellJ q a (j' + 1)) a.opp ∈ H := by
          have := back_cellJ_succ (c := q) (s := a) j'; unfold back at this; rw [this]
          exact (fr j' (by omega)).2 (by omega)
        tauto
      · have h1 : sideEdge (cellJ q a j) a ∈ H := (fr j (by omega)).2 ho
        have h2 : lat1 (cellJ q a j) a ∈ H := ((latL j hpos (by omega)).1).2 ho
        rw [lat1_eq] at h2
        exact (alt_lats Falt h1).1 h2
    · -- `A`, for `m ≥ 2`
      rw [hFj] at Fl1 Fl2 Fbk Ffr Fo1 Fo2
      exact not_flip_cell Fl1 Fl2 Fbk Ffr Fo1 Fo2 (a := a) (Or.inl (Or.inl latA'.1))
        ⟨a, Or.inl rfl, by rw [nb_cellJ]; exact latE.1, by rw [nb_cellJ]; exact latE.2⟩
    · -- `E`
      rw [hFj] at Fl1 Fl2 Fbk Ffr Fo1 Fo2
      exact not_flip_cell Fl1 Fl2 Fbk Ffr Fo1 Fo2 (a := a) (Or.inr (Or.inl frE))
        ⟨a.opp, Or.inr rfl, by rw [nb_cellJ_opp]; exact latA'.1,
          by rw [nb_cellJ_opp]; exact latA'.2⟩
    · -- the square beyond `E`
      rw [hFj] at Fl1 Fl2 Fbk Ffr Fo1 Fo2
      have h1 : sideEdge (cellJ q a (m + 2)) a.opp ∈ H := by
        rw [← nb_cellJ, sideEdge_nb_opp]; exact frE
      exact not_flip_cell Fl1 Fl2 Fbk Ffr Fo1 Fo2 (a := a) (Or.inr (Or.inr h1))
        ⟨a.opp, Or.inr rfl, by rw [nb_cellJ_opp]; exact latE.1,
          by rw [nb_cellJ_opp]; exact latE.2⟩
  have nm1 : F ≠ nb q a.opp := by
    intro hF
    rw [hF] at Fl1 Fl2 Fbk Ffr Fo1 Fo2
    have hq : nb (nb q a.opp) a = q := by
      have := nb_nb_opp q a.opp; rw [opp_opp] at this; exact this
    have h1 : sideEdge (nb q a.opp) a ∈ H := by
      have := sideEdge_nb_opp q a.opp; rw [opp_opp] at this; rw [this]; exact bk
    exact not_flip_cell Fl1 Fl2 Fbk Ffr Fo1 Fo2 (a := a) (Or.inr (Or.inl h1))
      ⟨a, Or.inl rfl, by rw [hq]; exact lat0.1, by rw [hq]; exact lat0.2⟩
  -- Side squares.
  --
  have sideBack : ∀ j, 1 ≤ j → sideEdge (nb (cellJ q a j) (latA a)) a.opp =
      outer1 (cellJ q a (j - 1)) a := by
    intro j hj
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    rw [show j' + 1 - 1 = j' by omega, ← nb_cellJ, ← nb_side_comm, sideEdge_nb_opp]
    exact side_front _ _
  have sideBackB : ∀ j, 1 ≤ j → sideEdge (nb (cellJ q a j) (latB a)) a.opp =
      outer2 (cellJ q a (j - 1)) a := by
    intro j hj
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    rw [show j' + 1 - 1 = j' by omega, ← nb_cellJ, ← nb_sideB_comm, sideEdge_nb_opp]
    exact sideB_front _ _
  have nS : ∀ j ≤ m + 1, F ≠ nb (cellJ q a j) (latA a) := by
    intro j hj hF
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · subst h0
      apply cutSq_of_ne (isCorner_back2 _ a) (isCorner_front2 _ a) _ Fun hF
      rw [sideA_back2, sideA_front2, cellJ_zero]; exact cut0
    rcases (show j ≤ m ∨ j = m + 1 by omega) with hle | rfl
    · rw [hF] at Falt
      rcases Nat.mod_two_eq_zero_or_one j with he | ho
      · apply not_alt_of_ne (s' := a) _ Falt
        have h1 : sideEdge (nb (cellJ q a j) (latA a)) a ∈ H := by
          rw [← front, side_front]; exact (outer j (by omega)).1.2 he
        have h2 : sideEdge (nb (cellJ q a j) (latA a)) a.opp ∉ H := by
          rw [sideBack j hpos]; intro h; have := (outer (j - 1) (by omega)).1.1 h; omega
        tauto
      · have h1 : sideEdge (nb (cellJ q a j) (latA a)) a.opp ∈ H := by
          rw [sideBack j hpos]; exact (outer (j - 1) (by omega)).1.2 (by omega)
        have h2 : lat2 (nb (cellJ q a j) (latA a)) a ∈ H := by
          rw [side_near]; exact ((latL j hpos hle).1).2 ho
        rw [lat2_eq, ← latB_opp] at h2
        exact (alt_lats Falt h1).2 h2
    · apply cutSq_of_ne (isCorner_back2 _ a) (isCorner_front2 _ a) _ Fun hF
      rw [sideA_back2, sideA_front2]; exact cutE
  have nS' : ∀ j ≤ m + 1, F ≠ nb (cellJ q a j) (latB a) := by
    intro j hj hF
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · subst h0
      apply cutSq_of_ne (isCorner_back1 _ a) (isCorner_front1 _ a) _ Fun hF
      rw [sideB_back1, sideB_front1, cellJ_zero]; exact cut0'
    rcases (show j ≤ m ∨ j = m + 1 by omega) with hle | rfl
    · rw [hF] at Falt
      rcases Nat.mod_two_eq_zero_or_one j with he | ho
      · apply not_alt_of_ne (s' := a) _ Falt
        have h1 : sideEdge (nb (cellJ q a j) (latB a)) a ∈ H := by
          rw [← front, sideB_front]; exact (outer j (by omega)).2.2 he
        have h2 : sideEdge (nb (cellJ q a j) (latB a)) a.opp ∉ H := by
          rw [sideBackB j hpos]; intro h; have := (outer (j - 1) (by omega)).2.1 h; omega
        tauto
      · have h1 : sideEdge (nb (cellJ q a j) (latB a)) a.opp ∈ H := by
          rw [sideBackB j hpos]; exact (outer (j - 1) (by omega)).2.2 (by omega)
        have h2 : lat1 (nb (cellJ q a j) (latB a)) a ∈ H := by
          rw [sideB_near]; exact ((latL j hpos hle).2).2 ho
        rw [lat1_eq, ← latA_opp] at h2
        exact (alt_lats Falt h1).1 h2
    · apply cutSq_of_ne (isCorner_back1 _ a) (isCorner_front1 _ a) _ Fun hF
      rw [sideB_back1, sideB_front1]; exact cutE'
  exact ⟨fun j hj => ncol j hj, nm1, fun j hj => ⟨nS j (by omega), nS' j (by omega)⟩⟩

-- **The region freeze.**
--
theorem regionOK_step {b b' : Bridge} (hR : RegionOK H b) (htwo : 2 ≤ b.r) (hev : b.r % 2 = 0)
    (hrs : RowStep V H b') (hdegc : ∀ f, IsCell V f → ∀ z, IsCorner z f → deg H z = 2) :
    RegionOK (flip H b'.E) b := by
  obtain ⟨Fl1, Fl2, Fbk, Ffr, Fo1, Fo2, Fun⟩ := rowStep_pre hrs hdegc
  have Falt := alt_of_lats Fl1 Fl2 Fbk Ffr
  set F := b'.E with hFdef
  set a' := b'.a
  obtain ⟨q, a, r⟩ := b
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 2 := ⟨r - 2, by simp only at htwo; omega⟩
  obtain ⟨bk, lat, lat0, latE, fr, frA, frE, outer, cut0, cut0', cutE⟩ := hR
  simp only [Bridge.cell, Bridge.E, show m + 2 - 1 = m + 1 by omega,
    show m + 2 - 2 = m by omega] at *
  have meven : m % 2 = 0 := by omega
  -- Lateral sides of the column squares `1 … m` (the last is `A`).
  --
  have latL : ∀ j, 1 ≤ j → j ≤ m → (lat1 (cellJ q a j) a ∈ H ↔ j % 2 = 1) ∧
      (lat2 (cellJ q a j) a ∈ H ↔ j % 2 = 1) := fun j h1 h2 => lat j h1 (by omega)
  -- `A`'s laterals are light (for `m = 0`, `A = q`).
  --
  have latA' : lat1 (cellJ q a m) a ∉ H ∧ lat2 (cellJ q a m) a ∉ H := by
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · subst h0; rw [cellJ_zero]; exact lat0
    · obtain ⟨a1, a2⟩ := latL m hpos le_rfl
      exact ⟨fun h => by have := a1.1 h; omega, fun h => by have := a2.1 h; omega⟩
  have bE : back (cellJ q a (m + 1)) a ∈ H := by rw [back_cellJ_succ]; exact frA
  have cutE' : ¬ Conn H (back2 (cellJ q a (m + 1)) a) (front2 (cellJ q a (m + 1)) a) :=
    fun h => cutE (((ends_back (c := cellJ q a (m + 1)) (s := a)).conn bE).trans
      (h.trans ((ends_front (c := cellJ q a (m + 1)) (s := a)).conn frE).symm))
  -- `F` is none of the region's squares.
  --
  have nq : F ≠ q := by
    have := cutSq_of_ne (isCorner_back1 q a) (isCorner_front1 q a) cut0 Fun; exact this
  have ncol : ∀ j ≤ m + 2, F ≠ cellJ q a j := by
    intro j hj hFj
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · subst h0; rw [cellJ_zero] at hFj; exact nq hFj
    rcases (show (j < m ∨ j = m) ∨ j = m + 1 ∨ j = m + 2 by omega) with (hlt | rfl) | rfl | rfl
    · -- inner squares: not alternating
      rw [hFj] at Falt
      rcases Nat.mod_two_eq_zero_or_one j with he | ho
      · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        apply not_alt_of_ne (s' := a) _ Falt
        have h1 : sideEdge (cellJ q a (j' + 1)) a ∉ H := fun h => by
          have := (fr (j' + 1) (by omega)).1 h; omega
        have h2 : sideEdge (cellJ q a (j' + 1)) a.opp ∈ H := by
          have := back_cellJ_succ (c := q) (s := a) j'; unfold back at this; rw [this]
          exact (fr j' (by omega)).2 (by omega)
        tauto
      · have h1 : sideEdge (cellJ q a j) a ∈ H := (fr j (by omega)).2 ho
        have h2 : lat1 (cellJ q a j) a ∈ H := ((latL j hpos (by omega)).1).2 ho
        rw [lat1_eq] at h2
        exact (alt_lats Falt h1).1 h2
    · -- `A`, for `m ≥ 2`
      rw [hFj] at Fl1 Fl2 Fbk Ffr Fo1 Fo2
      exact not_flip_cell Fl1 Fl2 Fbk Ffr Fo1 Fo2 (a := a) (Or.inl (Or.inl latA'.1))
        ⟨a, Or.inl rfl, by rw [nb_cellJ]; exact latE.1, by rw [nb_cellJ]; exact latE.2⟩
    · -- `E`
      rw [hFj] at Fl1 Fl2 Fbk Ffr Fo1 Fo2
      exact not_flip_cell Fl1 Fl2 Fbk Ffr Fo1 Fo2 (a := a) (Or.inr (Or.inl frE))
        ⟨a.opp, Or.inr rfl, by rw [nb_cellJ_opp]; exact latA'.1,
          by rw [nb_cellJ_opp]; exact latA'.2⟩
    · -- the square beyond `E`
      rw [hFj] at Fl1 Fl2 Fbk Ffr Fo1 Fo2
      have h1 : sideEdge (cellJ q a (m + 2)) a.opp ∈ H := by
        rw [← nb_cellJ, sideEdge_nb_opp]; exact frE
      exact not_flip_cell Fl1 Fl2 Fbk Ffr Fo1 Fo2 (a := a) (Or.inr (Or.inr h1))
        ⟨a.opp, Or.inr rfl, by rw [nb_cellJ_opp]; exact latE.1,
          by rw [nb_cellJ_opp]; exact latE.2⟩
  have nm1 : F ≠ nb q a.opp := by
    intro hF
    rw [hF] at Fl1 Fl2 Fbk Ffr Fo1 Fo2
    have hq : nb (nb q a.opp) a = q := by
      have := nb_nb_opp q a.opp; rw [opp_opp] at this; exact this
    have h1 : sideEdge (nb q a.opp) a ∈ H := by
      have := sideEdge_nb_opp q a.opp; rw [opp_opp] at this; rw [this]; exact bk
    exact not_flip_cell Fl1 Fl2 Fbk Ffr Fo1 Fo2 (a := a) (Or.inr (Or.inl h1))
      ⟨a, Or.inl rfl, by rw [hq]; exact lat0.1, by rw [hq]; exact lat0.2⟩
  -- Side squares.
  --
  have sideBack : ∀ j, 1 ≤ j → sideEdge (nb (cellJ q a j) (latA a)) a.opp =
      outer1 (cellJ q a (j - 1)) a := by
    intro j hj
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    rw [show j' + 1 - 1 = j' by omega, ← nb_cellJ, ← nb_side_comm, sideEdge_nb_opp]
    exact side_front _ _
  have sideBackB : ∀ j, 1 ≤ j → sideEdge (nb (cellJ q a j) (latB a)) a.opp =
      outer2 (cellJ q a (j - 1)) a := by
    intro j hj
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    rw [show j' + 1 - 1 = j' by omega, ← nb_cellJ, ← nb_sideB_comm, sideEdge_nb_opp]
    exact sideB_front _ _
  have nS : ∀ j ≤ m + 1, F ≠ nb (cellJ q a j) (latA a) := by
    intro j hj hF
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · subst h0
      apply cutSq_of_ne (isCorner_back2 _ a) (isCorner_front2 _ a) _ Fun hF
      rw [sideA_back2, sideA_front2, cellJ_zero]; exact cut0
    rcases (show j ≤ m ∨ j = m + 1 by omega) with hle | rfl
    · rw [hF] at Falt
      rcases Nat.mod_two_eq_zero_or_one j with he | ho
      · apply not_alt_of_ne (s' := a) _ Falt
        have h1 : sideEdge (nb (cellJ q a j) (latA a)) a ∈ H := by
          rw [← front, side_front]; exact (outer j (by omega)).1.2 he
        have h2 : sideEdge (nb (cellJ q a j) (latA a)) a.opp ∉ H := by
          rw [sideBack j hpos]; intro h; have := (outer (j - 1) (by omega)).1.1 h; omega
        tauto
      · have h1 : sideEdge (nb (cellJ q a j) (latA a)) a.opp ∈ H := by
          rw [sideBack j hpos]; exact (outer (j - 1) (by omega)).1.2 (by omega)
        have h2 : lat2 (nb (cellJ q a j) (latA a)) a ∈ H := by
          rw [side_near]; exact ((latL j hpos hle).1).2 ho
        rw [lat2_eq, ← latB_opp] at h2
        exact (alt_lats Falt h1).2 h2
    · apply cutSq_of_ne (isCorner_back2 _ a) (isCorner_front2 _ a) _ Fun hF
      rw [sideA_back2, sideA_front2]; exact cutE
  have nS' : ∀ j ≤ m + 1, F ≠ nb (cellJ q a j) (latB a) := by
    intro j hj hF
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · subst h0
      apply cutSq_of_ne (isCorner_back1 _ a) (isCorner_front1 _ a) _ Fun hF
      rw [sideB_back1, sideB_front1, cellJ_zero]; exact cut0'
    rcases (show j ≤ m ∨ j = m + 1 by omega) with hle | rfl
    · rw [hF] at Falt
      rcases Nat.mod_two_eq_zero_or_one j with he | ho
      · apply not_alt_of_ne (s' := a) _ Falt
        have h1 : sideEdge (nb (cellJ q a j) (latB a)) a ∈ H := by
          rw [← front, sideB_front]; exact (outer j (by omega)).2.2 he
        have h2 : sideEdge (nb (cellJ q a j) (latB a)) a.opp ∉ H := by
          rw [sideBackB j hpos]; intro h; have := (outer (j - 1) (by omega)).2.1 h; omega
        tauto
      · have h1 : sideEdge (nb (cellJ q a j) (latB a)) a.opp ∈ H := by
          rw [sideBackB j hpos]; exact (outer (j - 1) (by omega)).2.2 (by omega)
        have h2 : lat1 (nb (cellJ q a j) (latB a)) a ∈ H := by
          rw [sideB_near]; exact ((latL j hpos hle).2).2 ho
        rw [lat1_eq, ← latA_opp] at h2
        exact (alt_lats Falt h1).1 h2
    · apply cutSq_of_ne (isCorner_back1 _ a) (isCorner_front1 _ a) _ Fun hF
      rw [sideB_back1, sideB_front1]; exact cutE'
  -- Every edge of the region keeps its status.
  --
  have kLat1 : ∀ j ≤ m + 1, (lat1 (cellJ q a j) a ∈ flip H F ↔ lat1 (cellJ q a j) a ∈ H) :=
    fun j hj => by rw [lat1_eq]; exact keep_of (ncol j (by omega)) (nS j hj)
  have kLat2 : ∀ j ≤ m + 1, (lat2 (cellJ q a j) a ∈ flip H F ↔ lat2 (cellJ q a j) a ∈ H) :=
    fun j hj => by rw [lat2_eq]; exact keep_of (ncol j (by omega)) (nS' j hj)
  have kFr : ∀ j ≤ m + 1, (front (cellJ q a j) a ∈ flip H F ↔ front (cellJ q a j) a ∈ H) :=
    fun j hj => by
      unfold front; exact keep_of (ncol j (by omega)) (by rw [nb_cellJ]; exact ncol _ (by omega))
  have kOut1 : ∀ j ≤ m, (outer1 (cellJ q a j) a ∈ flip H F ↔ outer1 (cellJ q a j) a ∈ H) :=
    fun j hj => by
      rw [← side_front]; unfold front
      exact keep_of (nS j (by omega)) (by rw [nb_side_comm, nb_cellJ]; exact nS _ (by omega))
  have kOut2 : ∀ j ≤ m, (outer2 (cellJ q a j) a ∈ flip H F ↔ outer2 (cellJ q a j) a ∈ H) :=
    fun j hj => by
      rw [← sideB_front]; unfold front
      exact keep_of (nS' j (by omega)) (by rw [nb_sideB_comm, nb_cellJ]; exact nS' _ (by omega))
  have hq0 : ∀ {P : Pt → Prop}, P (cellJ q a 0) → P q := fun h => by rw [cellJ_zero] at h; exact h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [Bridge.cell, Bridge.E, show m + 2 - 1 = m + 1 by omega,
      show m + 2 - 2 = m by omega]
  · unfold back; rw [keep_of nq nm1]; exact bk
  · intro j h1 h2
    rw [kLat1 j (by omega), kLat2 j (by omega)]; exact lat j h1 h2
  · have k1 := kLat1 0 (by omega); have k2 := kLat2 0 (by omega)
    rw [cellJ_zero] at k1 k2
    rw [k1, k2]; exact lat0
  · rw [kLat1 _ le_rfl, kLat2 _ le_rfl]; exact latE
  · intro j hj; rw [kFr j (by omega)]; exact fr j hj
  · rw [kFr m (by omega)]; exact frA
  · rw [kFr (m + 1) le_rfl]; exact frE
  · intro j hj; rw [kOut1 j (by omega), kOut2 j (by omega)]; exact outer j hj
  · exact fun h => cut0 (conn_of_flip_uncut Fun h)
  · exact fun h => cut0' (conn_of_flip_uncut Fun h)
  · exact fun h => cutE (conn_of_flip_uncut Fun h)

end freeze

end HP

end SolidGridHam
