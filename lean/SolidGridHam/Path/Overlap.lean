/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import SolidGridHam.Path.Compat0

/-!
# Overlap (docs/S4_UNDO.md §II.1)

An inner square of a row (run pattern: laterals and front dark iff the index is odd, back dark iff
even) has that pattern in only one frame and parity (`pat_unique`). So an inner square of a later
row that is an inner square of an earlier bridge lies on the same line in the same direction;
walking back, the later row's start is a square of the bridge (against the start rule), or the
bridge's start is an uncut inner square of the row (against its cut).
-/

namespace SolidGridHam

namespace HP

open Finset Classical

-- The inner pattern of a square in a frame, with parity `p`.
--
def InnerPat (F : Finset Edge) (Y : Pt) (a : Side) (p : Prop) : Prop :=
  (lat1 Y a ∈ F ↔ p) ∧ (lat2 Y a ∈ F ↔ p) ∧ (front Y a ∈ F ↔ p) ∧ (back Y a ∈ F ↔ ¬ p)

lemma iff_not_self {p q : Prop} (h1 : p ↔ q) (h2 : p ↔ ¬ q) : False := by
  by_cases hq : q
  · exact (h2.1 (h1.2 hq)) hq
  · exact hq (h1.1 (h2.2 hq))

lemma pat_unique {F : Finset Edge} {Y : Pt} {a a' : Side} {p p' : Prop} (h : InnerPat F Y a p)
    (h' : InnerPat F Y a' p') : a' = a ∧ (p ↔ p') := by
  obtain ⟨l1, l2, f, b⟩ := h
  obtain ⟨l1', l2', f', b'⟩ := h'
  rcases side_cases a a' with h | h | h | h <;> subst h
  · exact ⟨rfl, f.symm.trans f'⟩
  · exfalso
    rw [lat1_sopp] at l1'
    unfold front at f'; unfold back at b
    have e1 := l1.symm.trans l1'
    have e2 := f'.symm.trans b
    by_cases hp : p
    · exact (e2.1 (e1.1 hp)) hp
    · exact (fun h => hp (e1.2 h)) (e2.2 hp)
  · exfalso
    unfold front at f'; rw [← lat1_eq] at f'
    unfold back at b'; rw [latA_opp', ← lat2_eq] at b'
    exact iff_not_self (l1.symm.trans f') (l2.symm.trans b')
  · exfalso
    unfold front at f'; rw [← lat2_eq] at f'
    unfold back at b'; rw [latB_opp', ← lat1_eq] at b'
    exact iff_not_self (l2.symm.trans f') (l1.symm.trans b')

lemma cellJ_eq_back {q q' : Pt} {a : Side} {m l : ℕ} (h : cellJ q a m = cellJ q' a l) (hml : m ≤ l) :
    q = cellJ q' a (l - m) := by
  obtain ⟨x, y⟩ := q; obtain ⟨x', y'⟩ := q'
  cases a <;> simp only [cellJ, Prod.mk.injEq] at h ⊢ <;> push_cast [Nat.cast_sub hml] <;>
    constructor <;> omega

-- The inner pattern of a frozen bridge square.
--
lemma region_inner {H : Finset Edge} {b : Bridge} (hR : RegionOK H b) {l : ℕ} (h1 : 1 ≤ l)
    (h2 : l + 3 ≤ b.r) : InnerPat H (b.cell l) b.a (l % 2 = 1) := by
  obtain ⟨l1, l2⟩ := hR.lat l h1 (by omega)
  refine ⟨l1, l2, hR.fr l h2, ?_⟩
  obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
  unfold Bridge.cell; rw [back_cellJ_succ]
  have := hR.fr l' (by omega); unfold Bridge.cell at this; rw [this]; omega

-- The inner pattern of a run square.
--
lemma run_inner {F : Finset Edge} {q : Pt} {a : Side} {n : ℕ}
    (hrun : ∀ j ≤ n, (lat1 (cellJ q a j) a ∈ F ↔ j % 2 = 1) ∧ (lat2 (cellJ q a j) a ∈ F ↔ j % 2 = 1) ∧
      (front (cellJ q a j) a ∈ F ↔ j % 2 = 1)) {m : ℕ} (h1 : 1 ≤ m) (h2 : m ≤ n) :
    InnerPat F (cellJ q a m) a (m % 2 = 1) := by
  obtain ⟨l1, l2, f⟩ := hrun m h2
  refine ⟨l1, l2, f, ?_⟩
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [back_cellJ_succ, (hrun m' (by omega)).2.2]; omega

-- **Overlap.** An inner square of a row (start not a square of `b`, inner squares uncut) is not
-- an inner square of the frozen bridge `b`.
--
theorem overlap {F : Finset Edge} {q : Pt} {a : Side} {n : ℕ}
    (hrun : ∀ j ≤ n, (lat1 (cellJ q a j) a ∈ F ↔ j % 2 = 1) ∧ (lat2 (cellJ q a j) a ∈ F ↔ j % 2 = 1) ∧
      (front (cellJ q a j) a ∈ F ↔ j % 2 = 1))
    (huncut : ∀ j, 1 ≤ j → j ≤ n → ¬ CutSq F (cellJ q a j)) {b : Bridge} (hR : RegionOK F b)
    (hstart : ∀ j < b.r, q ≠ b.cell j) {m l : ℕ} (hm1 : 1 ≤ m) (hm2 : m ≤ n) (hl1 : 1 ≤ l)
    (hl2 : l + 3 ≤ b.r) : cellJ q a m ≠ b.cell l := by
  intro he
  have p1 := run_inner hrun hm1 hm2
  have p2 := region_inner hR hl1 hl2
  rw [he] at p1
  obtain ⟨ha, _⟩ := pat_unique p2 p1
  subst ha
  unfold Bridge.cell at he
  rcases Nat.lt_or_ge l m with hlm | hml
  swap
  · exact hstart (l - m) (by omega) (cellJ_eq_back he hml)
  · have hq := cellJ_eq_back he.symm hlm.le
    apply huncut (m - l) (by omega) (by omega)
    rw [← hq]
    exact fun h => hR.cut0 (by
      have := conn_of_uncut (F := F) (c := b.q) (not_not.2 ?_) (isCorner_back1 b.q b.a)
        (isCorner_front1 b.q b.a)
      · exact this
      · exact h)

-- A row at a state: start critical with dark back and not a square of the given bridges, cells,
-- uncut after the start, equal arcs up to the second-to-last square.
--
structure RowAt (V : Finset Pt) (F : Finset Edge) (BS : List Bridge) (q : Pt) (a : Side) (n : ℕ) :
    Prop where
  two : 2 ≤ n
  cells : ∀ j < n, IsCell V (cellJ q a j)
  crit : CriticalIn F q a
  bk : back q a ∈ F
  nbs : ∀ b ∈ BS, ∀ j < b.r, q ≠ b.cell j
  uncut : ∀ j, 1 ≤ j → j < n → ¬ CutSq F (cellJ q a j)
  arcs : ∀ j, j + 1 < n → outArc F (cellJ q a j) a = outArc F q a

lemma RowAt.run {V : Finset Pt} {F : Finset Edge} {BS : List Bridge} {q : Pt} {a : Side} {n : ℕ}
    (h : RowAt V F BS q a n) (hdegc : ∀ f, IsCell V f → ∀ z, IsCorner z f → deg F z = 2) :
    ∀ j ≤ n - 2, (lat1 (cellJ q a j) a ∈ F ↔ j % 2 = 1) ∧ (lat2 (cellJ q a j) a ∈ F ↔ j % 2 = 1) ∧
      (front (cellJ q a j) a ∈ F ↔ j % 2 = 1) :=
  run_pat h.crit h.bk (fun j hj => ⟨hdegc _ (h.cells j (by omega)) _ (isCorner_front1 _ _),
    hdegc _ (h.cells j (by omega)) _ (isCorner_front2 _ _)⟩)
    (fun j hj => h.arcs j (by have := h.two; omega))

lemma InnerPat.not_alt {F : Finset Edge} {Y : Pt} {a : Side} {p : Prop} (h : InnerPat F Y a p) :
    ¬ Alt F Y := by
  apply not_alt_of_ne (s' := a)
  obtain ⟨_, _, f, b⟩ := h
  unfold front at f; unfold back at b
  rw [f, b]; tauto

lemma cutSq_q {F : Finset Edge} {b : Bridge} (hR : RegionOK F b) : CutSq F b.q :=
  cutSq_of_corners (isCorner_back1 b.q b.a) (isCorner_front1 b.q b.a) hR.cut0

lemma cutSq_E {F : Finset Edge} {b : Bridge} (hR : RegionOK F b) : CutSq F b.E :=
  cutSq_of_corners (isCorner_back1 b.E b.a) (isCorner_front1 b.E b.a) hR.cutE

-- **The start and inner squares of a row avoid every square of a frozen bridge.**
--
theorem rowAvoid {V : Finset Pt} {F : Finset Edge} {BS : List Bridge} {q : Pt} {a : Side} {n : ℕ}
    (hrow : RowAt V F BS q a n) (hdegc : ∀ f, IsCell V f → ∀ z, IsCorner z f → deg F z = 2)
    {b : Bridge} (hb : b ∈ BS) (hR : RegionOK F b) (htwo : 2 ≤ b.r) (hev : b.r % 2 = 0)
    {j : ℕ} (hj : j ≤ n - 2) {l : ℕ} (hl : l < b.r) : cellJ q a j ≠ b.cell l := by
  intro he
  rcases Nat.eq_zero_or_pos j with h0 | hjpos
  · subst h0; rw [cellJ_zero] at he; exact hrow.nbs b hb l hl he
  have hpat := run_inner (hrow.run hdegc) hjpos hj
  have hunc := hrow.uncut j hjpos (by have := hrow.two; omega)
  rw [he] at hpat hunc
  rcases (show l = 0 ∨ (1 ≤ l ∧ l + 3 ≤ b.r) ∨ l = b.r - 2 ∨ l = b.r - 1 by omega) with
    h | ⟨h1, h2⟩ | h | h
  · subst h; unfold Bridge.cell at hunc; rw [cellJ_zero] at hunc; exact hunc (cutSq_q hR)
  · exact overlap (hrow.run hdegc) (fun j' h1' h2' => hrow.uncut j' h1' (by omega)) hR
      (fun j' hj' => hrow.nbs b hb j' hj') hjpos hj h1 h2 (by rw [he])
  · subst h
    exact hpat.not_alt (region_alt hR htwo hev).1
  · subst h
    exact hunc (cutSq_E hR)

end HP

end SolidGridHam
