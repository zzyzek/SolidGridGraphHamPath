/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.Strip

/-!
# Flipping a strip: the component count (thesis Lemmas 5.4, 5.5)

A strip of length `n` from cell `c` in direction `s` has cells `c_j = cellJ c s j`. In `F`:
* `back c_0` is dark;
* the lateral sides of `c_j` are dark exactly for odd `j`;
* the front of `c_j` is dark exactly for odd `j`, except the last cell, whose front is
  dark exactly for even `j`. So `c_(n−1)` is alternating and the others are not.

Flipping the cells from the last to the first (`flipCol`):
* odd `n`: the count drops by one, if `back1 c_0` and `front1 c_0` are in different
  classes (pairs of cells change nothing, then the first cell merges);
* even `n`: the count is unchanged, if the last cell's two dark sides are in one class
  (it splits, then the rest is an odd strip).
-/

namespace ULHC

open Finset Classical

def StripPat (F : Finset Edge) (c : Pt) (s : Side) (n : ℕ) : Prop :=
  back c s ∈ F ∧
  (∀ j < n, (lat1 (cellJ c s j) s ∈ F ↔ j % 2 = 1) ∧ (lat2 (cellJ c s j) s ∈ F ↔ j % 2 = 1)) ∧
  (∀ j < n, (front (cellJ c s j) s ∈ F ↔ (j % 2 = 1 ↔ j + 1 < n)))

def flipCol (F : Finset Edge) (c : Pt) (s : Side) : ℕ → Finset Edge
  | 0 => F
  | n + 1 => flipCol (flip F (cellJ c s n)) c s n

/-! ## Edge-set bookkeeping -/

lemma cellE_frame (c : Pt) (s : Side) :
    cellE c = {back c s, front c s, lat1 c s, lat2 c s} := by
  cases s <;> ext e <;>
    simp only [cellE, back, front, lat1, lat2, sideEdge, Side.opp, Finset.mem_insert,
      Finset.mem_singleton] <;> tauto

lemma symmDiff_four {F E : Finset Edge} {e1 e2 l1 l2 : Edge} (hE : E = {e1, e2, l1, l2})
    (h1 : e1 ∈ F) (h2 : e2 ∈ F) (h3 : l1 ∉ F) (h4 : l2 ∉ F) :
    symmDiff F E = insert l2 (insert l1 ((F.erase e1).erase e2)) := by
  subst hE
  ext e
  simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton, Finset.mem_erase]
  constructor
  · rintro (⟨he, hn⟩ | ⟨hn, he⟩)
    · push Not at hn; exact Or.inr (Or.inr ⟨hn.2.1, hn.1, he⟩)
    · rcases hn with rfl | rfl | rfl | rfl
      · exact absurd h1 he
      · exact absurd h2 he
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl rfl
  · rintro (rfl | rfl | ⟨hne2, hne1, he⟩)
    · exact Or.inr ⟨Or.inr (Or.inr (Or.inr rfl)), h4⟩
    · exact Or.inr ⟨Or.inr (Or.inr (Or.inl rfl)), h3⟩
    · refine Or.inl ⟨he, ?_⟩
      rintro (rfl | rfl | rfl | rfl)
      · exact hne1 rfl
      · exact hne2 rfl
      · exact h3 he
      · exact h4 he

lemma ACell.flip_eq (C : ACell) {F : Finset Edge} {c : Pt}
    (hE : cellE c = {C.e1, C.e2, C.l1, C.l2})
    (h1 : C.e1 ∈ F) (h2 : C.e2 ∈ F) (h3 : C.l1 ∉ F) (h4 : C.l2 ∉ F) :
    flip F c = C.res F := symmDiff_four hE h1 h2 h3 h4

lemma deg_insert {F : Finset Edge} {e : Edge} (he : e ∉ F) (z : Pt) :
    deg (insert e F) z = deg F z + (if e.p = z ∨ e.q = z then 1 else 0) := by
  have := ULHC.deg_erase (Finset.mem_insert_self e F) z
  rw [Finset.erase_insert he] at this
  omega

-- Flipping an alternating cell keeps every degree.
--
lemma ACell.deg_res (C : ACell) {F : Finset Edge}
    (h1 : C.e1 ∈ F) (h2 : C.e2 ∈ F) (h3 : C.l1 ∉ F) (h4 : C.l2 ∉ F) (z : Pt) :
    deg (C.res F) z = deg F z := by
  have he2 : C.e2 ∈ F.erase C.e1 := Finset.mem_erase.2 ⟨C.e2_ne_e1, h2⟩
  have hl1 : C.l1 ∉ (F.erase C.e1).erase C.e2 := fun h => h3 (by
    simp only [Finset.mem_erase] at h; exact h.2.2)
  have l12 : C.l2 ≠ C.l1 := (C.h3.ne_of C.h4 C.ak.symm C.dk.symm).symm
  have hl2 : C.l2 ∉ insert C.l1 ((F.erase C.e1).erase C.e2) := by
    simp only [Finset.mem_insert, Finset.mem_erase, not_or]
    exact ⟨l12, fun h => h4 h.2.2⟩
  have d1 := C.h1.deg_erase h1 z
  have d2 := C.h2.deg_erase he2 z
  have d3 := deg_insert hl1 z
  have d4 := deg_insert hl2 z
  simp only [C.h3.inc_iff z] at d3
  simp only [C.h4.inc_iff z] at d4
  unfold ACell.res
  rw [d4, d3]
  have ab := C.ab
  have ad := C.ad
  have ak := C.ak
  have bd := C.bd
  have bk := C.bk
  have dk := C.dk
  by_cases za : z = C.a <;> by_cases zb : z = C.b <;> by_cases zd : z = C.d <;>
    by_cases zk : z = C.k <;> simp_all

/-! ## Instances: the cell types met in a strip, and the pair -/

-- An alternating cell whose back and front are dark.
--
def mkBF (c : Pt) (s : Side) : ACell where
  a := back1 c s
  b := back2 c s
  d := front1 c s
  k := front2 c s
  e1 := back c s
  e2 := front c s
  l1 := lat1 c s
  l2 := lat2 c s
  h1 := ends_back c s
  h2 := ends_front c s
  h3 := ends_lat1 c s
  h4 := ends_lat2 c s
  ad := by obtain ⟨x, y⟩ := c; cases s <;> simp [back1, front1]
  ak := by obtain ⟨x, y⟩ := c; cases s <;> simp [back1, front2]
  bd := by obtain ⟨x, y⟩ := c; cases s <;> simp [back2, front1]
  bk := by obtain ⟨x, y⟩ := c; cases s <;> simp [back2, front2]

-- An alternating cell whose lateral sides are dark.
--
def mkLat (c : Pt) (s : Side) : ACell where
  a := back1 c s
  b := front1 c s
  d := back2 c s
  k := front2 c s
  e1 := lat1 c s
  e2 := lat2 c s
  l1 := back c s
  l2 := front c s
  h1 := ends_lat1 c s
  h2 := ends_lat2 c s
  h3 := ends_back c s
  h4 := ends_front c s
  ad := by obtain ⟨x, y⟩ := c; cases s <;> simp [back1, back2]
  ak := by obtain ⟨x, y⟩ := c; cases s <;> simp [back1, front2]
  bd := by obtain ⟨x, y⟩ := c; cases s <;> simp [front1, back2]
  bk := by obtain ⟨x, y⟩ := c; cases s <;> simp [front1, front2]

lemma mkBF_cellE (c : Pt) (s : Side) :
    cellE c = {(mkBF c s).e1, (mkBF c s).e2, (mkBF c s).l1, (mkBF c s).l2} :=
  cellE_frame c s

lemma mkLat_cellE (c : Pt) (s : Side) :
    cellE c = {(mkLat c s).e1, (mkLat c s).e2, (mkLat c s).l1, (mkLat c s).l2} := by
  rw [cellE_frame c s]; ext e; simp [mkLat]; tauto

-- A U-shaped cell `c` (dark laterals and front) and the alternating cell after it.
--
def mkPair (c : Pt) (s : Side) : APair where
  a := back1 c s
  b := back2 c s
  m1 := front1 c s
  m2 := front2 c s
  t1 := front1 (nb c s) s
  t2 := front2 (nb c s) s
  eab := back c s
  eam := lat1 c s
  ebm := lat2 c s
  em := front c s
  et := front (nb c s) s
  emt1 := lat1 (nb c s) s
  emt2 := lat2 (nb c s) s
  hab := ends_back c s
  ham := ends_lat1 c s
  hbm := ends_lat2 c s
  hm := ends_front c s
  ht := ends_front (nb c s) s
  hmt1 := by have := ends_lat1 (nb c s) s; rwa [back1_nb] at this
  hmt2 := by have := ends_lat2 (nb c s) s; rwa [back2_nb] at this
  m1a := by obtain ⟨x, y⟩ := c; cases s <;> simp [back1, front1]
  m1b := by obtain ⟨x, y⟩ := c; cases s <;> simp [back2, front1]
  m1t1 := by obtain ⟨x, y⟩ := c; cases s <;> simp [nb, front1] <;> omega
  m1t2 := by obtain ⟨x, y⟩ := c; cases s <;> simp [nb, front1, front2]
  m2a := by obtain ⟨x, y⟩ := c; cases s <;> simp [back1, front2]
  m2b := by obtain ⟨x, y⟩ := c; cases s <;> simp [back2, front2]
  m2t1 := by obtain ⟨x, y⟩ := c; cases s <;> simp [nb, front1, front2]
  m2t2 := by obtain ⟨x, y⟩ := c; cases s <;> simp [nb, front2] <;> omega

/-! ## The pair flip as two cell flips -/

lemma symmDiff_six {F : Finset Edge} {a1 a2 a3 b1 b2 b3 : Edge}
    (ha1 : a1 ∈ F) (ha2 : a2 ∈ F) (ha3 : a3 ∈ F) (hb1 : b1 ∉ F) (hb2 : b2 ∉ F) (hb3 : b3 ∉ F) :
    symmDiff F {b1, a1, a2, a3, b2, b3} =
      (insert b3 (insert b2 (((insert b1 F).erase a1).erase a2))).erase a3 := by
  ext e
  simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton, Finset.mem_erase]
  constructor
  · rintro (⟨he, hn⟩ | ⟨hn, he⟩)
    · push Not at hn
      exact ⟨hn.2.2.2.1, Or.inr (Or.inr ⟨hn.2.2.1, hn.2.1, Or.inr he⟩)⟩
    · rcases hn with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨fun h => he (h ▸ ha3), Or.inr (Or.inr ⟨fun h => he (h ▸ ha2),
          fun h => he (h ▸ ha1), Or.inl rfl⟩)⟩
      · exact absurd ha1 he
      · exact absurd ha2 he
      · exact absurd ha3 he
      · exact ⟨fun h => he (h ▸ ha3), Or.inr (Or.inl rfl)⟩
      · exact ⟨fun h => he (h ▸ ha3), Or.inl rfl⟩
  · rintro ⟨h3, rfl | rfl | ⟨h2, h1, rfl | he⟩⟩
    · exact Or.inr ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))), hb3⟩
    · exact Or.inr ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))), hb2⟩
    · exact Or.inr ⟨Or.inl rfl, hb1⟩
    · refine Or.inl ⟨he, ?_⟩
      rintro (rfl | rfl | rfl | rfl | rfl | rfl)
      · exact hb1 he
      · exact h1 rfl
      · exact h2 rfl
      · exact h3 rfl
      · exact hb2 he
      · exact hb3 he

lemma symmDiff_cells_frame {f x1 x2 x3 y1 y2 y3 : Edge} {E1 E2 : Finset Edge}
    (hE1 : E1 = {f, y1, y2, y3}) (hE2 : E2 = {x1, f, x2, x3})
    (hx : ∀ x ∈ ({x1, x2, x3} : Finset Edge), x ∉ E1)
    (hy : ∀ y ∈ ({y1, y2, y3} : Finset Edge), y ∉ E2) :
    symmDiff E1 E2 = {x1, x2, x3, y1, y2, y3} := by
  subst hE1 hE2
  ext e
  simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq] at hx hy
  constructor
  · rintro (⟨h | h | h | h, hn⟩ | ⟨h | h | h | h, hn⟩)
    · exact absurd (Or.inr (Or.inl h)) hn
    all_goals first
      | (subst h; tauto)
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl) <;> tauto

lemma pair_cells (c : Pt) (s : Side) :
    symmDiff (cellE (nb c s)) (cellE c) =
      {back c s, lat1 c s, lat2 c s, front (nb c s) s, lat1 (nb c s) s, lat2 (nb c s) s} := by
  apply symmDiff_cells_frame (f := front c s)
  · rw [cellE_frame (nb c s) s, back_nb]
  · rw [cellE_frame c s]
  · obtain ⟨x, y⟩ := c
    cases s <;> simp [cellE, back, lat1, lat2, nb, sideEdge, Side.opp, bot, top, lft, rgt] <;>
      omega
  · obtain ⟨x, y⟩ := c
    cases s <;> simp [cellE, front, lat1, lat2, nb, sideEdge, bot, top, lft, rgt] <;> omega

lemma pair_flip_eq {F : Finset Edge} (c : Pt) (s : Side)
    (h1 : lat1 c s ∈ F) (h2 : lat2 c s ∈ F) (h3 : front (nb c s) s ∈ F)
    (h4 : back c s ∉ F) (h5 : lat1 (nb c s) s ∉ F) (h6 : lat2 (nb c s) s ∉ F) :
    flip (flip F (nb c s)) c = (mkPair c s).res F := by
  unfold flip
  rw [symmDiff_assoc, pair_cells]
  exact symmDiff_six h1 h2 h3 h4 h5 h6

/-! ## Which strip edges a cell flip touches -/

lemma mem_flip_iff {F : Finset Edge} {c : Pt} {e : Edge} :
    e ∈ flip F c ↔ (e ∈ F ↔ e ∉ cellE c) := by
  unfold flip; rw [Finset.mem_symmDiff]; tauto

section geo2

variable (c : Pt) (s : Side)

lemma lat1_not_mem {j m : ℕ} (h : j ≠ m) : lat1 (cellJ c s j) s ∉ cellE (cellJ c s m) := by
  obtain ⟨x, y⟩ := c
  cases s <;> simp [cellE, lat1, cellJ, bot, top, lft, rgt] <;> omega

lemma lat2_not_mem {j m : ℕ} (h : j ≠ m) : lat2 (cellJ c s j) s ∉ cellE (cellJ c s m) := by
  obtain ⟨x, y⟩ := c
  cases s <;> simp [cellE, lat2, cellJ, bot, top, lft, rgt] <;> omega

lemma front_not_mem {j m : ℕ} (h1 : j ≠ m) (h2 : m ≠ j + 1) :
    front (cellJ c s j) s ∉ cellE (cellJ c s m) := by
  obtain ⟨x, y⟩ := c
  cases s <;> simp [cellE, front, sideEdge, cellJ, bot, top, lft, rgt] <;> omega

lemma front_mem_self (j : ℕ) : front (cellJ c s j) s ∈ cellE (cellJ c s j) := by
  rw [cellE_frame _ s]; simp

lemma front_mem_next (j : ℕ) : front (cellJ c s j) s ∈ cellE (cellJ c s (j + 1)) := by
  rw [← nb_cellJ, cellE_frame _ s, back_nb]; simp

lemma lat1_mem_self (j : ℕ) : lat1 (cellJ c s j) s ∈ cellE (cellJ c s j) := by
  rw [cellE_frame _ s]; simp

lemma lat2_mem_self (j : ℕ) : lat2 (cellJ c s j) s ∈ cellE (cellJ c s j) := by
  rw [cellE_frame _ s]; simp

lemma back_not_mem {m : ℕ} (h : m ≠ 0) : back c s ∉ cellE (cellJ c s m) := by
  obtain ⟨x, y⟩ := c
  cases s <;> simp [cellE, back, Side.opp, sideEdge, cellJ, bot, top, lft, rgt] <;> omega

lemma back_cellJ_succ (j : ℕ) : back (cellJ c s (j + 1)) s = front (cellJ c s j) s := by
  rw [← nb_cellJ, back_nb]

-- The first cell's back corners and `front1` are not front corners of a later cell.
--
lemma corner_ne {m : ℕ} (h : m ≠ 0) :
    back1 c s ≠ front1 (cellJ c s m) s ∧ back1 c s ≠ front2 (cellJ c s m) s ∧
      front1 c s ≠ front1 (cellJ c s m) s ∧ front1 c s ≠ front2 (cellJ c s m) s := by
  obtain ⟨x, y⟩ := c
  cases s <;> simp [back1, front1, front2, cellJ] <;> omega

end geo2

/-! ## The pattern after flipping the end -/

section pat

variable {F : Finset Edge} {c : Pt} {s : Side}

-- Even length `k + 2`: flipping the last cell leaves an odd strip of length `k + 1`.
--
lemma pat_flip_last {k : ℕ} (hk : k % 2 = 0) (h : StripPat F c s (k + 2)) :
    StripPat (flip F (cellJ c s (k + 1))) c s (k + 1) := by
  obtain ⟨hb, hl, hf⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [mem_flip_iff]; have := back_not_mem c s (m := k + 1) (by omega); tauto
  · intro j hj
    have e1 := lat1_not_mem c s (j := j) (m := k + 1) (by omega)
    have e2 := lat2_not_mem c s (j := j) (m := k + 1) (by omega)
    rw [mem_flip_iff, mem_flip_iff]
    have := hl j (by omega)
    tauto
  · intro j hj
    rw [mem_flip_iff]
    rcases (show j < k ∨ j = k by omega) with hjk | rfl
    · have e := front_not_mem c s (j := j) (m := k + 1) (by omega) (by omega)
      have := hf j (by omega)
      have q1 : j + 1 < k + 2 := by omega
      have q2 : j + 1 < k + 1 := by omega
      simp only [q1, q2, iff_true] at this ⊢
      tauto
    · have e := front_mem_next c s j
      have := hf j (by omega)
      have q1 : j + 1 < j + 2 := by omega
      simp only [q1, iff_true, hk, lt_self_iff_false, iff_false] at this ⊢
      simp only [zero_ne_one, not_false_eq_true, iff_true] at this ⊢
      tauto

-- Odd length `k + 3`: flipping the last two cells leaves an odd strip of length `k + 1`.
--
lemma pat_flip_pair {k : ℕ} (hk : k % 2 = 0) (h : StripPat F c s (k + 3)) :
    StripPat (flip (flip F (cellJ c s (k + 2))) (cellJ c s (k + 1))) c s (k + 1) := by
  obtain ⟨hb, hl, hf⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [mem_flip_iff, mem_flip_iff]
    have := back_not_mem c s (m := k + 2) (by omega)
    have := back_not_mem c s (m := k + 1) (by omega)
    tauto
  · intro j hj
    have e1 := lat1_not_mem c s (j := j) (m := k + 2) (by omega)
    have e2 := lat2_not_mem c s (j := j) (m := k + 2) (by omega)
    have e3 := lat1_not_mem c s (j := j) (m := k + 1) (by omega)
    have e4 := lat2_not_mem c s (j := j) (m := k + 1) (by omega)
    rw [mem_flip_iff, mem_flip_iff, mem_flip_iff, mem_flip_iff]
    have := hl j (by omega)
    tauto
  · intro j hj
    rw [mem_flip_iff, mem_flip_iff]
    rcases (show j < k ∨ j = k by omega) with hjk | rfl
    · have e1 := front_not_mem c s (j := j) (m := k + 2) (by omega) (by omega)
      have e2 := front_not_mem c s (j := j) (m := k + 1) (by omega) (by omega)
      have := hf j (by omega)
      have q1 : j + 1 < k + 3 := by omega
      have q2 : j + 1 < k + 1 := by omega
      simp only [q1, q2, iff_true] at this ⊢
      tauto
    · have e1 := front_not_mem c s (j := j) (m := j + 2) (by omega) (by omega)
      have e2 := front_mem_next c s j
      have := hf j (by omega)
      have q1 : j + 1 < j + 3 := by omega
      simp only [q1, iff_true, hk, lt_self_iff_false, iff_false] at this ⊢
      simp only [zero_ne_one, not_false_eq_true, iff_true] at this ⊢
      tauto

end pat

/-! ## Helpers for factors on `V` -/

lemma isCell_corners {V : Finset Pt} {c : Pt} (h : IsCell V c) (s : Side) :
    back1 c s ∈ V ∧ back2 c s ∈ V ∧ front1 c s ∈ V ∧ front2 c s ∈ V := by
  obtain ⟨x, y⟩ := c
  obtain ⟨h1, h2, h3, h4⟩ := h
  cases s <;> simp only [back1, back2, front1, front2] <;> exact ⟨by assumption, by assumption,
    by assumption, by assumption⟩

lemma inside_flip {V : Finset Pt} {F : Finset Edge} {c : Pt} (hV : Inside V F) (hc : IsCell V c) :
    Inside V (flip F c) := by
  intro e he
  rw [mem_flip_iff] at he
  by_cases hE : e ∈ cellE c
  · obtain ⟨x, y⟩ := c
    obtain ⟨h1, h2, h3, h4⟩ := hc
    simp only [cellE, Finset.mem_insert, Finset.mem_singleton] at hE
    rcases hE with rfl | rfl | rfl | rfl <;> simp [bot, top, lft, rgt, Edge.q] <;>
      exact ⟨by assumption, by assumption⟩
  · exact hV e (he.2 hE)

lemma conn_mem {V : Finset Pt} {F : Finset Edge} (hV : Inside V F) {a z : Pt} (ha : a ∈ V)
    (h : Conn F a z) : z ∈ V := by
  induction h with
  | refl => exact ha
  | tail _ hyz _ =>
    obtain ⟨e, he, h⟩ := hyz
    rcases h with ⟨_, h⟩ | ⟨h, _⟩ <;> rw [← h]
    · exact (hV e he).2
    · exact (hV e he).1

lemma deg_zero_of_inside {V : Finset Pt} {F : Finset Edge} (hV : Inside V F) {z : Pt}
    (hz : z ∉ V) : deg F z = 0 := by
  by_contra h
  obtain ⟨e, he, hi⟩ := exists_inc_of_deg (F := F) (y := z) (by omega)
  rcases hi with hi | hi
  · exact hz (hi ▸ (hV e he).1)
  · exact hz (hi ▸ (hV e he).2)

-- `F` has degree 2 at every vertex of `V` and no edge leaves `V`.
--
def Deg2 (V : Finset Pt) (F : Finset Edge) : Prop := Inside V F ∧ ∀ z ∈ V, deg F z = 2

lemma Deg2.le_two {V : Finset Pt} {F : Finset Edge} (h : Deg2 V F) (z : Pt) : deg F z ≤ 2 := by
  by_cases hz : z ∈ V
  · rw [h.2 z hz]
  · rw [deg_zero_of_inside h.1 hz]; omega

lemma Deg2.class {V : Finset Pt} {F : Finset Edge} (h : Deg2 V F) {a : Pt} (ha : a ∈ V) {z : Pt}
    (hz : Conn F a z) : deg F z = 2 := h.2 z (conn_mem h.1 ha hz)

lemma Deg2.flip {V : Finset Pt} {F : Finset Edge} (h : Deg2 V F) (C : ACell) {c : Pt}
    (hc : IsCell V c) (hE : cellE c = {C.e1, C.e2, C.l1, C.l2})
    (h1 : C.e1 ∈ F) (h2 : C.e2 ∈ F) (h3 : C.l1 ∉ F) (h4 : C.l2 ∉ F) : Deg2 V (ULHC.flip F c) := by
  refine ⟨inside_flip h.1 hc, fun z hz => ?_⟩
  rw [C.flip_eq hE h1 h2 h3 h4, C.deg_res h1 h2 h3 h4]
  exact h.2 z hz

/-! ## The count theorems -/

-- Middle corners of the pairs flipped in an odd strip of length `k + 1`: the front
-- corners of the odd cells before the last.
--
def IsMid (c : Pt) (s : Side) (k : ℕ) (z : Pt) : Prop :=
  ∃ j, j % 2 = 1 ∧ j < k ∧ (z = front1 (cellJ c s j) s ∨ z = front2 (cellJ c s j) s)

section count

variable {V : Finset Pt} {c : Pt} {s : Side}

lemma flipCol_succ (F : Finset Edge) (n : ℕ) :
    flipCol F c s (n + 1) = flipCol (flip F (cellJ c s n)) c s n := rfl

-- **Odd strip** (thesis Lemma 5.4): the count drops by one.
--
theorem strip_odd : ∀ k : ℕ, k % 2 = 0 → ∀ F : Finset Edge, Deg2 V F →
    (∀ j ≤ k, IsCell V (cellJ c s j)) → StripPat F c s (k + 1) →
    ¬ Conn F (back1 c s) (front1 c s) → ncomp V (flipCol F c s (k + 1)) + 1 = ncomp V F ∧
      ∀ x y, ¬ IsMid c s k x → ¬ IsMid c s k y →
        (Conn (flipCol F c s (k + 1)) x y ↔ Conn F x y ∨
          (Conn F x (back1 c s) ∧ Conn F (front1 c s) y) ∨
          (Conn F x (front1 c s) ∧ Conn F (back1 c s) y)) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro hk F hF hcell hpat hsep
  rcases (show k = 0 ∨ 2 ≤ k by omega) with rfl | hk2
  · -- One alternating cell: a merge.
    rw [flipCol_succ]
    simp only [flipCol]
    rw [cellJ_zero]
    have hc : IsCell V c := by have := hcell 0 le_rfl; rwa [cellJ_zero] at this
    obtain ⟨hb, hl, hf⟩ := hpat
    have l1 := (hl 0 (by omega)).1
    have l2 := (hl 0 (by omega)).2
    have f0 := hf 0 (by omega)
    rw [cellJ_zero] at l1 l2 f0
    simp at l1 l2 f0
    have C := mkBF c s
    rw [(mkBF c s).flip_eq (mkBF_cellE c s) hb f0 l1 l2]
    obtain ⟨cb1, cb2, cf1, cf2⟩ := isCell_corners hc s
    obtain ⟨h1, h2⟩ := (mkBF c s).merge hF.1 cb1 cf1 hb f0
      (fun z hz => by rcases hz with hz | hz
                      · exact hF.class cb1 hz
                      · exact hF.class cf1 hz) hsep
    exact ⟨h1, fun x y _ _ => h2 x y⟩
  · -- Two more cells: the pair changes nothing.
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
    have hm : m % 2 = 0 := by omega
    rw [show m + 2 + 1 = m + 3 from rfl, flipCol_succ, flipCol_succ]
    set u := cellJ c s (m + 1)
    have hnb : nb u s = cellJ c s (m + 2) := nb_cellJ c s (m + 1)
    obtain ⟨hb, hl, hf⟩ := hpat
    -- Memberships around the pair.
    have uL1 : lat1 u s ∈ F := (hl (m + 1) (by omega)).1.2 (by omega)
    have uL2 : lat2 u s ∈ F := (hl (m + 1) (by omega)).2.2 (by omega)
    have uF : front u s ∈ F := (hf (m + 1) (by omega)).2 (by omega)
    have uB : back u s ∉ F := by
      rw [back_cellJ_succ]
      intro h; have := (hf m (by omega)).1 h; omega
    have wL1 : lat1 (nb u s) s ∉ F := by
      rw [hnb]; intro h; have := (hl (m + 2) (by omega)).1.1 h; omega
    have wL2 : lat2 (nb u s) s ∉ F := by
      rw [hnb]; intro h; have := (hl (m + 2) (by omega)).2.1 h; omega
    have wF : front (nb u s) s ∈ F := by
      rw [hnb]; exact (hf (m + 2) (by omega)).2 (by omega)
    have hdouble : flip (flip F (cellJ c s (m + 2))) (cellJ c s (m + 1)) = (mkPair u s).res F := by
      rw [← hnb]; exact pair_flip_eq u s uL1 uL2 wF uB wL1 wL2
    have hcu : IsCell V u := hcell (m + 1) (by omega)
    have hcw : IsCell V (nb u s) := by rw [hnb]; exact hcell (m + 2) (by omega)
    obtain ⟨ub1, ub2, uf1, uf2⟩ := isCell_corners hcu s
    obtain ⟨_, _, wf1, wf2⟩ := isCell_corners hcw s
    obtain ⟨hcount, hrel⟩ := (mkPair u s).flip ub2 uf1 uf2 wf1 uL1 uL2 uF wF
      (hF.2 _ uf1) (hF.2 _ uf2)
    -- The new factor.
    rw [hdouble]
    have hF2' : Deg2 V ((mkPair u s).res F) := by
      rw [← hdouble]
      have hw : cellJ c s (m + 2) = nb u s := hnb.symm
      have d1 : Deg2 V (flip F (cellJ c s (m + 2))) := by
        rw [hw]
        exact hF.flip (mkBF (nb u s) s) hcw (mkBF_cellE _ s)
          (by show back (nb u s) s ∈ F; rw [back_nb]; exact uF) wF wL1 wL2
      have m1 : lat1 u s ∈ flip F (cellJ c s (m + 2)) := by
        rw [mem_flip_iff]; have := lat1_not_mem c s (j := m + 1) (m := m + 2) (by omega); tauto
      have m2 : lat2 u s ∈ flip F (cellJ c s (m + 2)) := by
        rw [mem_flip_iff]; have := lat2_not_mem c s (j := m + 1) (m := m + 2) (by omega); tauto
      have m3 : back u s ∉ flip F (cellJ c s (m + 2)) := by
        rw [mem_flip_iff, back_cellJ_succ]
        have := front_not_mem c s (j := m) (m := m + 2) (by omega) (by omega)
        rw [back_cellJ_succ] at uB; tauto
      have m4 : front u s ∉ flip F (cellJ c s (m + 2)) := by
        rw [mem_flip_iff]; have := front_mem_next c s (m + 1); tauto
      exact d1.flip (mkLat u s) hcu (mkLat_cellE u s) m1 m2 m3 m4
    have hpat2 : StripPat ((mkPair u s).res F) c s (m + 1) := by
      rw [← hdouble]; exact pat_flip_pair hm ⟨hb, hl, hf⟩
    have hsep2 : ¬ Conn ((mkPair u s).res F) (back1 c s) (front1 c s) := by
      obtain ⟨n1, n2, n3, n4⟩ := corner_ne c s (m := m + 1) (by omega)
      rw [hrel _ _ n1 n2 n3 n4]; exact hsep
    obtain ⟨ihc, ihr⟩ := ih m (by omega) hm _ hF2' (fun j hj => hcell j (by omega)) hpat2 hsep2
    refine ⟨by omega, fun x y hx hy => ?_⟩
    have nm : ∀ z, ¬ IsMid c s (m + 2) z → z ≠ front1 u s ∧ z ≠ front2 u s := by
      intro z hz
      exact ⟨fun h => hz ⟨m + 1, by omega, by omega, Or.inl h⟩,
        fun h => hz ⟨m + 1, by omega, by omega, Or.inr h⟩⟩
    have sub : ∀ z, ¬ IsMid c s (m + 2) z → ¬ IsMid c s m z := by
      intro z hz ⟨j, h1, h2, h3⟩; exact hz ⟨j, h1, by omega, h3⟩
    obtain ⟨n1, n2, n3, n4⟩ := corner_ne c s (m := m + 1) (by omega)
    obtain ⟨x1, x2⟩ := nm x hx
    obtain ⟨y1, y2⟩ := nm y hy
    rw [ihr x y (sub x hx) (sub y hy), hrel _ _ x1 x2 y1 y2, hrel _ _ x1 x2 n1 n2,
      hrel _ _ n3 n4 y1 y2, hrel _ _ x1 x2 n3 n4, hrel _ _ n1 n2 y1 y2]

-- **Even strip** (thesis Lemma 5.5): if the last cell's dark sides are in one class (it is
-- not a Type III cell), the count is unchanged.
--
theorem strip_even (k : ℕ) (hk : k % 2 = 0) (F : Finset Edge) (hF : Deg2 V F)
    (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat F c s (k + 2))
    (hsep : ¬ Conn F (back1 c s) (front1 c s))
    (hsame : Conn F (back1 (cellJ c s (k + 1)) s) (back2 (cellJ c s (k + 1)) s)) :
    ncomp V (flipCol F c s (k + 2)) = ncomp V F := by
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
  obtain ⟨hcount, hrel, _⟩ := (mkLat u s).split hF.1 ub1 uf1 ub2 uf2 uL1 uL2 uB
    (fun z hz => by rcases hz with hz | hz
                    · exact hF.class ub1 hz
                    · exact hF.class ub2 hz) hsame hF.le_two
    (fun G h1 h2 h3 h4 h5 => planar_lat G u s h1 h2 h3 h4 h5)
  have hF' : Deg2 V ((mkLat u s).res F) := by
    rw [← (mkLat u s).flip_eq hE uL1 uL2 uB uF]
    exact hF.flip (mkLat u s) hcu hE uL1 uL2 uB uF
  have hpat' : StripPat ((mkLat u s).res F) c s (k + 1) := by
    rw [← (mkLat u s).flip_eq hE uL1 uL2 uB uF]; exact pat_flip_last hk ⟨hb, hl, hf⟩
  have hsep' : ¬ Conn ((mkLat u s).res F) (back1 c s) (front1 c s) :=
    fun h => hsep (hrel _ _ h)
  have := (strip_odd k hk _ hF' (fun j hj => hcell j (by omega)) hpat' hsep').1
  omega

end count

end ULHC
