/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import SolidGridHam.Path.Stuck

/-!
# The invariants after a move

`H₁ = lowerCol H c s n` flips `c_1 … c_n`. A square *near the move* is one of these cells or a
neighbour of one (`NearM`): the column `c_0 … c_(n+1)` and the side squares beside `c_1 … c_n`.
A square that is not near the move keeps its four sides, and its corners are not even-height
interior column vertices, so its corners keep their connections (`lowerCol_factor`). Hence it keeps
being alternating, being cut, and everything else the invariants say about it.
-/

namespace SolidGridHam

namespace HP

open Finset Classical

section near

variable {c : Pt} {s : Side}

-- One of `c_1 … c_n`, or a neighbour of one.
--
def NearM (c : Pt) (s : Side) (n : ℕ) (q : Pt) : Prop :=
  ∃ j, 1 ≤ j ∧ j ≤ n ∧ (q = cellJ c s j ∨ ∃ s', q = nb (cellJ c s j) s')

lemma side_hi_lo (q : Pt) (s' : Side) :
    ((sideEdge q s').hi = q ∧ (sideEdge q s').lo = nb q s') ∨
      ((sideEdge q s').hi = nb q s' ∧ (sideEdge q s').lo = q) := by
  obtain ⟨x, y⟩ := q
  cases s' <;> simp [sideEdge, bot, top, lft, rgt, Edge.hi, Edge.lo, nb]

lemma side_mem_cellE {q c' : Pt} {s' : Side} (h : sideEdge q s' ∈ cellE c') :
    c' = q ∨ c' = nb q s' := by
  rw [mem_cellE_iff] at h
  rcases side_hi_lo q s' with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] at h <;>
    rcases h with h | h
  · exact Or.inl h.symm
  · exact Or.inr h.symm
  · exact Or.inr h.symm
  · exact Or.inl h.symm

lemma nb_nb_opp (q : Pt) (s' : Side) : nb (nb q s') s'.opp = q := by
  obtain ⟨x, y⟩ := q; cases s' <;> simp [nb, Side.opp]

-- **Sides of a square away from the move are unchanged.**
--
lemma side_after {F : Finset Edge} {n : ℕ} {q : Pt} (hq : ¬ NearM c s n q) (s' : Side) :
    sideEdge q s' ∈ lowerCol F c s n ↔ sideEdge q s' ∈ F := by
  apply mem_lowerCol_off
  intro j h1 h2 he
  rcases side_mem_cellE he with h | h
  · exact hq ⟨j, h1, h2, Or.inl h.symm⟩
  · exact hq ⟨j, h1, h2, Or.inr ⟨s'.opp, by rw [h, nb_nb_opp]⟩⟩

-- The four squares at a front corner.
--
lemma squares_at_front1 {c' q : Pt} (h : IsCorner (front1 c' s) q) :
    q = c' ∨ q = nb c' s ∨ q = nb c' (latA s) ∨ q = nb (nb c' s) (latA s) := by
  obtain ⟨x, y⟩ := c'
  obtain ⟨a, b⟩ := q
  cases s <;> simp only [IsCorner, front1, nb, latA, Prod.mk.injEq] at h ⊢ <;> omega

lemma squares_at_front2 {c' q : Pt} (h : IsCorner (front2 c' s) q) :
    q = c' ∨ q = nb c' s ∨ q = nb c' (latB s) ∨ q = nb (nb c' s) (latB s) := by
  obtain ⟨x, y⟩ := c'
  obtain ⟨a, b⟩ := q
  cases s <;> simp only [IsCorner, front2, nb, latB, Prod.mk.injEq] at h ⊢ <;> omega

-- **Corners of a square away from the move are not even-height interior column vertices.**
--
lemma corner_not_mid {n : ℕ} {q z : Pt} (hq : ¬ NearM c s n q) (hz : IsCorner z q) :
    ¬ IsMid c s n z := by
  rintro ⟨j, hj1, hj2, hz'⟩
  have n1 : NearM c s n (cellJ c s j) := ⟨j, by omega, by omega, Or.inl rfl⟩
  have n2 : NearM c s n (nb (cellJ c s j) s) := ⟨j + 1, by omega, by omega,
    Or.inl (nb_cellJ c s j)⟩
  have n3 : ∀ s', NearM c s n (nb (cellJ c s j) s') := fun s' =>
    ⟨j, by omega, by omega, Or.inr ⟨s', rfl⟩⟩
  have n4 : ∀ s', NearM c s n (nb (nb (cellJ c s j) s) s') := fun s' =>
    ⟨j + 1, by omega, by omega, Or.inr ⟨s', by rw [nb_cellJ]⟩⟩
  rcases hz' with rfl | rfl
  · rcases squares_at_front1 hz with h | h | h | h <;> rw [h] at hq
    · exact hq n1
    · exact hq n2
    · exact hq (n3 _)
    · exact hq (n4 _)
  · rcases squares_at_front2 hz with h | h | h | h <;> rw [h] at hq
    · exact hq n1
    · exact hq n2
    · exact hq (n3 _)
    · exact hq (n4 _)

end near

/-! ## Squares away from the move keep their shape -/

section away

variable {V W : Finset Pt} {d : Pt → ℕ} {H : Finset Edge} {c : Pt} {s : Side} {n : ℕ}
  (hconn : ∀ x y, ¬ IsMid c s n x → ¬ IsMid c s n y → (Conn (lowerCol H c s n) x y ↔ Conn H x y))
include hconn

omit hconn in
lemma alt_after {q : Pt} (hq : ¬ NearM c s n q) : Alt (lowerCol H c s n) q ↔ Alt H q := by
  have hb := side_after (F := H) hq .b
  have ht := side_after (F := H) hq .t
  have hl := side_after (F := H) hq .l
  have hr := side_after (F := H) hq .r
  simp only [sideEdge] at hb ht hl hr
  unfold Alt
  rw [hb, ht, hl, hr]

lemma conn_corners_after {q u v : Pt} (hq : ¬ NearM c s n q) (hu : IsCorner u q)
    (hv : IsCorner v q) : Conn (lowerCol H c s n) u v ↔ Conn H u v :=
  hconn u v (corner_not_mid hq hu) (corner_not_mid hq hv)

lemma cut_after {q : Pt} (hq : ¬ NearM c s n q) : CutSq (lowerCol H c s n) q ↔ CutSq H q := by
  have c0 : IsCorner q q := Or.inl rfl
  have c1 : IsCorner (q.1 + 1, q.2) q := Or.inr (Or.inl rfl)
  have c2 : IsCorner (q.1, q.2 + 1) q := Or.inr (Or.inr (Or.inl rfl))
  have c3 : IsCorner (q.1 + 1, q.2 + 1) q := Or.inr (Or.inr (Or.inr rfl))
  unfold CutSq
  rw [conn_corners_after hconn hq c0 c1, conn_corners_after hconn hq c0 c3,
    conn_corners_after hconn hq c0 c2]

end away

/-! ## Squares near the move -/

section nearSq

variable {c : Pt} {s : Side} {n : ℕ}

lemma near_cases {q : Pt} (h : NearM c s n q) :
    (∃ j ≤ n + 1, q = cellJ c s j) ∨
      ∃ j, 1 ≤ j ∧ j ≤ n ∧ (q = nb (cellJ c s j) (latA s) ∨ q = nb (cellJ c s j) (latB s)) := by
  obtain ⟨j, h1, h2, h | ⟨s', rfl⟩⟩ := h
  · exact Or.inl ⟨j, by omega, h⟩
  · rcases side_cases s s' with h | h | h | h <;> rw [h]
    · exact Or.inl ⟨j + 1, by omega, (nb_cellJ c s j)⟩
    · refine Or.inl ⟨j - 1, by omega, ?_⟩
      have := nb_cellJ_opp c s (j - 1)
      rw [show j - 1 + 1 = j by omega] at this
      exact this
    · exact Or.inr ⟨j, h1, h2, Or.inl rfl⟩
    · exact Or.inr ⟨j, h1, h2, Or.inr rfl⟩

lemma alt_lats {F : Finset Edge} {q : Pt} {s' : Side} (h : Alt F q) (hs : sideEdge q s' ∈ F) :
    sideEdge q (latA s') ∉ F ∧ sideEdge q (latB s') ∉ F := by
  unfold Alt at h
  cases s' <;> simp only [sideEdge, latA, latB] at hs ⊢ <;> tauto

lemma not_alt_of_ne {F : Finset Edge} {q : Pt} {s' : Side}
    (h : ¬ (sideEdge q s' ∈ F ↔ sideEdge q s'.opp ∈ F)) : ¬ Alt F q :=
  fun ha => h (alt_opp_iff ha s')

lemma dark_of_ne {F : Finset Edge} {q : Pt} {s' : Side}
    (h : ¬ (sideEdge q s' ∈ F ↔ sideEdge q s'.opp ∈ F)) : ∃ s'', sideEdge q s'' ∈ F := by
  by_cases h1 : sideEdge q s' ∈ F
  · exact ⟨s', h1⟩
  · exact ⟨s'.opp, by by_contra h2; exact h ⟨fun h3 => absurd h3 h1, fun h3 => absurd h3 h2⟩⟩

variable {H : Finset Edge} (hn : n % 2 = 0) (hn2 : 2 ≤ n) (hp : StripPat H c s (n + 1))
  (hd1 : ∀ j ≤ n, deg H (front1 (cellJ c s j) s) = 2)
  (hd2 : ∀ j ≤ n, deg H (front2 (cellJ c s j) s) = 2)
  (hB : Alt H (cellJ c s (n + 1)))
include hn hn2 hp hd1 hd2 hB

set_option linter.unusedSectionVars false

lemma frontn_mem : front (cellJ c s n) s ∈ H := (hp.2.2 n (by omega)).2 (by omega)

-- The outer edges beside the column, including the top one at `front1 c_n`.
--
lemma outer1_all {j : ℕ} (hj : j ≤ n) : outer1 (cellJ c s j) s ∈ H ↔ j % 2 = 0 := by
  rcases Nat.lt_or_ge j n with h | h
  · exact outer1_forced hp (by omega) (hd1 j (by omega))
  · have hjn : j = n := by omega
    subst hjn
    have hd := hd1 j le_rfl
    rw [deg_front1, nb_cellJ] at hd
    have l1 : lat1 (cellJ c s j) s ∉ H := fun h' => by
      have := (hp.2.1 j (by omega)).1.1 h'; omega
    have bB : back (cellJ c s (j + 1)) s ∈ H := by
      rw [back_cellJ_succ]; exact frontn_mem hn hn2 hp hd1 hd2 hB
    have l1B : lat1 (cellJ c s (j + 1)) s ∉ H := by
      have := (alt_lats hB (s' := s.opp) bB).1; rwa [latA_opp, ← lat1_eq] at this
    rw [ind_of_not_mem l1, ind_of_mem (frontn_mem hn hn2 hp hd1 hd2 hB), ind_of_not_mem l1B] at hd
    constructor
    · intro _; exact hn
    · intro _; by_contra ho; rw [ind_of_not_mem ho] at hd; omega

lemma outer2_all {j : ℕ} (hj : j ≤ n) : outer2 (cellJ c s j) s ∈ H ↔ j % 2 = 0 := by
  rcases Nat.lt_or_ge j n with h | h
  · exact outer2_forced hp (by omega) (hd2 j (by omega))
  · have hjn : j = n := by omega
    subst hjn
    have hd := hd2 j le_rfl
    rw [deg_front2, nb_cellJ] at hd
    have l2 : lat2 (cellJ c s j) s ∉ H := fun h' => by
      have := (hp.2.1 j (by omega)).2.1 h'; omega
    have bB : back (cellJ c s (j + 1)) s ∈ H := by
      rw [back_cellJ_succ]; exact frontn_mem hn hn2 hp hd1 hd2 hB
    have l2B : lat2 (cellJ c s (j + 1)) s ∉ H := by
      have := (alt_lats hB (s' := s.opp) bB).2
      rwa [show latB s.opp = latB s by cases s <;> rfl, ← lat2_eq] at this
    rw [ind_of_not_mem l2, ind_of_mem (frontn_mem hn hn2 hp hd1 hd2 hB), ind_of_not_mem l2B] at hd
    constructor
    · intro _; exact hn
    · intro _; by_contra ho; rw [ind_of_not_mem ho] at hd; omega

-- **Side squares** `S_j`, `R_j` (`1 ≤ j ≤ n`): their two sides along the column are outer edges of
-- opposite membership, before and after the move.
--
lemma sideA_ne (F : Finset Edge) (hF : ∀ j ≤ n, outer1 (cellJ c s j) s ∈ F ↔ outer1 (cellJ c s j) s ∈ H)
    {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ n) :
    ¬ (sideEdge (nb (cellJ c s j) (latA s)) s ∈ F ↔
      sideEdge (nb (cellJ c s j) (latA s)) s.opp ∈ F) := by
  have hb : outer1 (cellJ c s (j - 1)) s = sideEdge (nb (cellJ c s j) (latA s)) s.opp := by
    rw [outer1_side_nb_next, nb_cellJ, show j - 1 + 1 = j by omega]
  have hf : outer1 (cellJ c s j) s = sideEdge (nb (cellJ c s j) (latA s)) s := outer1_side_nb _ _
  rw [← hb, ← hf, hF j h2, hF (j - 1) (by omega), outer1_all hn hn2 hp hd1 hd2 hB h2,
    outer1_all hn hn2 hp hd1 hd2 hB (by omega)]
  omega

lemma sideB_ne (F : Finset Edge) (hF : ∀ j ≤ n, outer2 (cellJ c s j) s ∈ F ↔ outer2 (cellJ c s j) s ∈ H)
    {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ n) :
    ¬ (sideEdge (nb (cellJ c s j) (latB s)) s ∈ F ↔
      sideEdge (nb (cellJ c s j) (latB s)) s.opp ∈ F) := by
  have hb : outer2 (cellJ c s (j - 1)) s = sideEdge (nb (cellJ c s j) (latB s)) s.opp := by
    rw [outer2_side_nb_next, nb_cellJ, show j - 1 + 1 = j by omega]
  have hf : outer2 (cellJ c s j) s = sideEdge (nb (cellJ c s j) (latB s)) s := outer2_side_nb _ _
  rw [← hb, ← hf, hF j h2, hF (j - 1) (by omega), outer2_all hn hn2 hp hd1 hd2 hB h2,
    outer2_all hn hn2 hp hd1 hd2 hB (by omega)]
  omega

-- Column squares before the move: back dark exactly at even index, front exactly at odd index.
--
lemma col_ne_H {j : ℕ} (hj : j < n) :
    ¬ (sideEdge (cellJ c s j) s ∈ H ↔ sideEdge (cellJ c s j) s.opp ∈ H) := by
  have hf : sideEdge (cellJ c s j) s ∈ H ↔ j % 2 = 1 := by
    have := hp.2.2 j (by omega); show front _ _ ∈ H ↔ _; rw [this]; omega
  have hb : sideEdge (cellJ c s j) s.opp ∈ H ↔ j % 2 = 0 := by
    show back _ _ ∈ H ↔ _
    rcases j with _ | j
    · rw [cellJ_zero]; simp [hp.1]
    · rw [back_cellJ_succ]; have := hp.2.2 j (by omega); rw [this]; omega
  rw [hf, hb]; omega

-- Column squares after the move (`2 ≤ j ≤ n + 1`): back and front of opposite membership.
--
lemma col_ne_H1 {j : ℕ} (h1 : 2 ≤ j) (h2 : j ≤ n + 1) :
    ¬ (sideEdge (cellJ c s j) s ∈ lowerCol H c s n ↔
      sideEdge (cellJ c s j) s.opp ∈ lowerCol H c s n) := by
  have hb : sideEdge (cellJ c s j) s.opp = front (cellJ c s (j - 1)) s := by
    have := back_cellJ_succ c s (j - 1)
    rw [show j - 1 + 1 = j by omega] at this
    exact this
  rw [hb]
  rcases Nat.lt_or_ge j n with h | h
  · rw [show sideEdge (cellJ c s j) s = front (cellJ c s j) s from rfl,
      front_inner_after hn hn2 hp (by omega) (by omega),
      front_inner_after hn hn2 hp (by omega) (by omega)]
    omega
  · rcases Nat.lt_or_ge j (n + 1) with h' | h'
    · have hjn : j = n := by omega
      subst hjn
      rw [front_inner_after hn hn2 hp (by omega) (by omega)]
      have := frontk_after hn hn2 hp
      intro hiff
      exact this (hiff.2 (by omega))
    · have hjn : j = n + 1 := by omega
      subst hjn
      rw [show n + 1 - 1 = n by omega]
      have hfB : front (cellJ c s (n + 1)) s ∈ H := by
        have bB : sideEdge (cellJ c s (n + 1)) s.opp ∈ H := by
          show back _ _ ∈ H; rw [back_cellJ_succ]; exact frontn_mem hn hn2 hp hd1 hd2 hB
        exact (alt_opp_iff hB s).2 bB
      have hfB' : front (cellJ c s (n + 1)) s ∈ lowerCol H c s n := by
        rw [mem_lowerCol_off (fun m h1 h2 => by rw [front_mem_cellE_iff]; omega)]; exact hfB
      have := frontk_after hn hn2 hp
      exact fun hiff => this (hiff.1 hfB')

omit hn hn2 hp hd1 hd2 hB in
lemma outer_after1 (j : ℕ) :
    outer1 (cellJ c s j) s ∈ lowerCol H c s n ↔ outer1 (cellJ c s j) s ∈ H :=
  mem_lowerCol_off (fun m _ _ => outer1_not_mem c s j m)

omit hn hn2 hp hd1 hd2 hB in
lemma outer_after2 (j : ℕ) :
    outer2 (cellJ c s j) s ∈ lowerCol H c s n ↔ outer2 (cellJ c s j) s ∈ H :=
  mem_lowerCol_off (fun m _ _ => outer2_not_mem c s j m)

-- **Near the move, after it**: only `c_0` and `c_1` are alternating, and every square has a dark
-- side.
--
lemma near_H1 {q : Pt} (hq : NearM c s n q) :
    (Alt (lowerCol H c s n) q → q = c ∨ q = cellJ c s 1) ∧
      ∃ s'', sideEdge q s'' ∈ lowerCol H c s n := by
  rcases near_cases hq with ⟨j, hj, rfl⟩ | ⟨j, h1, h2, rfl | rfl⟩
  · rcases (show j = 0 ∨ j = 1 ∨ 2 ≤ j by omega) with rfl | rfl | h
    · rw [cellJ_zero]
      exact ⟨fun _ => Or.inl rfl, ⟨s, front0_after hn hn2 hp⟩⟩
    · exact ⟨fun _ => Or.inr rfl,
        ⟨s, (front_inner_after hn hn2 hp le_rfl (by omega)).2 rfl⟩⟩
    · have hne := col_ne_H1 hn hn2 hp hd1 hd2 hB h hj
      exact ⟨fun ha => absurd ha (not_alt_of_ne hne), dark_of_ne hne⟩
  · have hne := sideA_ne hn hn2 hp hd1 hd2 hB (lowerCol H c s n)
      (fun m _ => outer_after1 m) h1 h2
    exact ⟨fun ha => absurd ha (not_alt_of_ne hne), dark_of_ne hne⟩
  · have hne := sideB_ne hn hn2 hp hd1 hd2 hB (lowerCol H c s n)
      (fun m _ => outer_after2 m) h1 h2
    exact ⟨fun ha => absurd ha (not_alt_of_ne hne), dark_of_ne hne⟩

-- **Near the move, before it**: only `c_n` and `c_(n+1)` (the old pair) are alternating.
--
lemma near_H {q : Pt} (hq : NearM c s n q) (ha : Alt H q) :
    q = cellJ c s n ∨ q = cellJ c s (n + 1) := by
  rcases near_cases hq with ⟨j, hj, rfl⟩ | ⟨j, h1, h2, rfl | rfl⟩
  · rcases Nat.lt_or_ge j n with h | h
    · exact absurd ha (not_alt_of_ne (col_ne_H hn hn2 hp hd1 hd2 hB h))
    · rcases (show j = n ∨ j = n + 1 by omega) with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
  · exact absurd ha (not_alt_of_ne (sideA_ne hn hn2 hp hd1 hd2 hB H (fun _ _ => Iff.rfl) h1 h2))
  · exact absurd ha (not_alt_of_ne (sideB_ne hn hn2 hp hd1 hd2 hB H (fun _ _ => Iff.rfl) h1 h2))

end nearSq

-- A square with a dark side satisfies L4 in every frame: a dark lateral side would join the back
-- pair to the front pair.
--
lemma l4_of_dark {F : Finset Edge} {q : Pt} (hd : ∃ s'', sideEdge q s'' ∈ F) (s' : Side)
    (hb : Conn F (back1 q s') (back2 q s')) (hf : Conn F (front1 q s') (front2 q s'))
    (hn : ¬ Conn F (back1 q s') (front1 q s')) : back q s' ∈ F ∨ front q s' ∈ F := by
  obtain ⟨s'', h⟩ := hd
  rcases side_cases s' s'' with h' | h' | h' | h' <;> rw [h'] at h
  · exact Or.inr h
  · exact Or.inl h
  · rw [← lat1_eq] at h; exact absurd ((ends_lat1 q s').conn h) hn
  · rw [← lat2_eq] at h
    exact absurd (hb.trans (((ends_lat2 q s').conn h).trans hf.symm)) hn

end HP

end SolidGridHam

namespace SolidGridHam

namespace HP

open Finset Classical

/-! ## Assembling the invariants after a move -/

-- The data of a move: a column `c_0 … c_n` (`n` even, `n ≥ 2`) from a movable square, ending at the
-- pair `i` whose squares are `c_n`, `c_(n+1)`.
--
structure MoveCtx (V W : Finset Pt) (d : Pt → ℕ) (H H' : Finset Edge) (FP : List FixedPr)
    (c : Pt) (s : Side) (n : ℕ) (i : FixedPr) (t0 u0 : Pt) : Prop where
  inv : Inv V H H' FP t0 u0
  hVW : V ⊆ W
  hH : IsFactor W d H
  hdc : ∀ q, IsCell V q → ∀ z, IsCorner z q → d z = 2
  cell : ∀ j ≤ n + 1, IsCell V (cellJ c s j)
  pat : StripPat H c s (n + 1)
  hi : i ∈ FP
  ev : n % 2 = 0
  two : 2 ≤ n
  pi : (i.top = cellJ c s n ∧ i.bot = cellJ c s (n + 1)) ∨
    (i.bot = cellJ c s n ∧ i.top = cellJ c s (n + 1))
  c0 : ∀ j ∈ FP, c ≠ j.top ∧ c ≠ j.bot
  po : (outArc H c s = true ∧ i.top = cellJ c s n ∧ i.bot = cellJ c s (n + 1)) ∨
    (outArc H c s = false ∧ i.bot = cellJ c s n ∧ i.top = cellJ c s (n + 1))

noncomputable def npair (o : Bool) (c : Pt) (s : Side) : FixedPr :=
  if o then newPair c s else newPairF c s

noncomputable def fpAfter (FP : List FixedPr) (i np : FixedPr) : List FixedPr :=
  FP.map (fun j => if j = i then np else j)

lemma mem_fpAfter {FP : List FixedPr} {i np j : FixedPr} (hi : i ∈ FP) :
    j ∈ fpAfter FP i np ↔ j = np ∨ (j ∈ FP ∧ j ≠ i) := by
  unfold fpAfter
  rw [List.mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩
    by_cases h : a = i
    · simp [h]
    · simp only [h, ite_false]; exact Or.inr ⟨ha, h⟩
  · rintro (rfl | ⟨hj, hne⟩)
    · exact ⟨i, hi, by simp⟩
    · exact ⟨j, hj, by simp [hne]⟩

lemma fpAfter_length (FP : List FixedPr) (i np : FixedPr) :
    (fpAfter FP i np).length = FP.length := by simp [fpAfter]

lemma npair_sq (o : Bool) (c : Pt) (s : Side) :
    ((npair o c s).top = c ∧ (npair o c s).bot = cellJ c s 1) ∨
      ((npair o c s).bot = c ∧ (npair o c s).top = cellJ c s 1) := by
  cases o
  · right; simp only [npair, Bool.false_eq_true, ↓reduceIte]; exact ⟨rfl, newPairF_top⟩
  · left; simp only [npair, ↓reduceIte]; exact ⟨newPair_top, rfl⟩

section ctx

variable {V W : Finset Pt} {d : Pt → ℕ} {H H' : Finset Edge} {FP : List FixedPr} {c : Pt}
  {s : Side} {n : ℕ} {i : FixedPr} {t0 u0 : Pt} (M : MoveCtx V W d H H' FP c s n i t0 u0)
include M

lemma MoveCtx.d1 : ∀ j ≤ n, deg H (front1 (cellJ c s j) s) = 2 := fun j hj => by
  have hc := M.cell j (by omega)
  rw [M.hH.2 _ (M.hVW (isCell_corners hc s).2.2.1)]
  exact M.hdc _ hc _ (isCorner_front1 _ s)

lemma MoveCtx.d2 : ∀ j ≤ n, deg H (front2 (cellJ c s j) s) = 2 := fun j hj => by
  have hc := M.cell j (by omega)
  rw [M.hH.2 _ (M.hVW (isCell_corners hc s).2.2.2)]
  exact M.hdc _ hc _ (isCorner_front2 _ s)

lemma MoveCtx.altB : Alt H (cellJ c s (n + 1)) := by
  have := M.inv.palt i M.hi
  rcases M.pi with ⟨_, h⟩ | ⟨_, h⟩
  · rw [← h]; exact this.2
  · rw [← h]; exact this.1

lemma MoveCtx.conn :
    ∀ x y, ¬ IsMid c s n x → ¬ IsMid c s n y → (Conn (lowerCol H c s n) x y ↔ Conn H x y) :=
  (lowerCol_factor M.hVW n M.ev H M.hH (fun j hj => M.cell j (by omega))
    (fun j hj => M.hdc _ (M.cell j (by omega))) M.pat).2.2

lemma MoveCtx.factor : IsFactor W d (lowerCol H c s n) :=
  (lowerCol_factor M.hVW n M.ev H M.hH (fun j hj => M.cell j (by omega))
    (fun j hj => M.hdc _ (M.cell j (by omega))) M.pat).1

lemma MoveCtx.count : ncomp W (lowerCol H c s n) = ncomp W H :=
  (lowerCol_factor M.hVW n M.ev H M.hH (fun j hj => M.cell j (by omega))
    (fun j hj => M.hdc _ (M.cell j (by omega))) M.pat).2.1

lemma MoveCtx.near_n : NearM c s n (cellJ c s n) :=
  ⟨n, by have := M.two; omega, le_rfl, Or.inl rfl⟩

lemma MoveCtx.near_n1 : NearM c s n (cellJ c s (n + 1)) :=
  ⟨n, by have := M.two; omega, le_rfl, Or.inr ⟨s, (nb_cellJ c s n).symm⟩⟩

lemma MoveCtx.near_0 : NearM c s n c :=
  ⟨1, le_rfl, by have := M.two; omega, Or.inr ⟨s.opp, by rw [nb_cellJ_opp, cellJ_zero]⟩⟩

lemma MoveCtx.near_1 : NearM c s n (cellJ c s 1) :=
  ⟨1, le_rfl, by have := M.two; omega, Or.inl rfl⟩

-- Squares of other pairs are away from the move.
--
lemma MoveCtx.other_away {j : FixedPr} (hj : j ∈ FP) (hne : j ≠ i) :
    ¬ NearM c s n j.top ∧ ¬ NearM c s n j.bot := by
  have hpa := M.inv.palt j hj
  have key : ∀ q, (q = j.top ∨ q = j.bot) → Alt H q → ¬ NearM c s n q := by
    intro q hq ha hn
    rcases near_H M.ev M.two M.pat M.d1 M.d2 M.altB hn ha with h | h <;>
    · apply hne
      apply M.inv.pdisj j hj i M.hi
      rcases M.pi with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hq with rfl | rfl <;>
        first
        | exact Or.inl (h.trans h1.symm)
        | exact Or.inr (Or.inl (h.trans h2.symm))
        | exact Or.inr (Or.inl (h.trans h1.symm))
        | exact Or.inl (h.trans h2.symm)
        | exact Or.inr (Or.inr (Or.inl (h.trans h1.symm)))
        | exact Or.inr (Or.inr (Or.inr (h.trans h2.symm)))
        | exact Or.inr (Or.inr (Or.inl (h.trans h2.symm)))
        | exact Or.inr (Or.inr (Or.inr (h.trans h1.symm)))
  exact ⟨key _ (Or.inl rfl) hpa.1, key _ (Or.inr rfl) hpa.2⟩

-- The new pair is valid after the move.
--
lemma MoveCtx.np_ok : PairOK (lowerCol H c s n) (npair (outArc H c s) c s) := by
  cases h : outArc H c s
  · simp only [npair, Bool.false_eq_true, ↓reduceIte]
    exact newPairF_ok M.ev M.two M.pat h
  · simp only [npair, ↓reduceIte]
    exact newPair_ok M.ev M.two M.pat h

lemma MoveCtx.np_alt (o : Bool) : Alt (lowerCol H c s n) (npair o c s).top ∧
    Alt (lowerCol H c s n) (npair o c s).bot := by
  have a0 := alt0_after M.ev M.two M.pat
  have a1 := alt1_after M.ev M.two M.pat
  rcases npair_sq o c s with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
  · exact ⟨a0, a1⟩
  · exact ⟨a1, a0⟩

lemma MoveCtx.np_dark (o : Bool) :
    sideEdge (npair o c s).bot (npair o c s).s ∈ lowerCol H c s n := by
  have hf0 := front0_after M.ev M.two M.pat
  cases o
  · simp only [npair, newPairF, Bool.false_eq_true, ↓reduceIte]; exact hf0
  · simp only [npair, newPair, ↓reduceIte]
    have := back_cellJ_succ c s 0
    rw [cellJ_zero] at this
    show back (cellJ c s 1) s ∈ _
    rw [this]; exact hf0

omit M in
lemma MoveCtx.np_corn (o : Bool) :
    IsCorner (npair o c s).tx (npair o c s).top ∧ IsCorner (npair o c s).ty (npair o c s).top ∧
      IsCorner (npair o c s).bx (npair o c s).bot ∧ IsCorner (npair o c s).by' (npair o c s).bot := by
  cases o
  · simp only [npair, Bool.false_eq_true, ↓reduceIte]
    rw [newPairF_top]
    exact ⟨isCorner_back1 _ _, isCorner_front1 _ _, isCorner_back1 _ _, isCorner_front1 _ _⟩
  · simp only [npair, ↓reduceIte]
    rw [newPair_top]
    exact ⟨isCorner_back1 _ _, isCorner_front1 _ _, isCorner_back1 _ _, isCorner_front1 _ _⟩

lemma MoveCtx.np_near (o : Bool) : NearM c s n (npair o c s).top ∧ NearM c s n (npair o c s).bot := by
  rcases npair_sq o c s with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
  · exact ⟨M.near_0, M.near_1⟩
  · exact ⟨M.near_1, M.near_0⟩

-- `PairOK` carries over for a pair away from the move.
--
lemma MoveCtx.pairOK_away {j : FixedPr} (hj : j ∈ FP) (hne : j ≠ i) :
    PairOK (lowerCol H c s n) j := by
  obtain ⟨ht, hb⟩ := M.other_away hj hne
  obtain ⟨o1, o2, o3, o4, o5⟩ := M.inv.f4 j hj
  obtain ⟨k1, k2, k3, k4⟩ := M.inv.pcorn j hj
  have arcs : ∀ q, ¬ NearM c s n q → ∀ s', outArc (lowerCol H c s n) q s' = outArc H q s' :=
    fun q hq s' => outArc_congr (side_after hq s')
  have cc : ∀ {q u v : Pt}, ¬ NearM c s n q → IsCorner u q → IsCorner v q →
      (Conn (lowerCol H c s n) u v ↔ Conn H u v) := fun hq hu hv =>
    conn_corners_after M.conn hq hu hv
  refine ⟨fun s' hs' => ?_, fun s' hs' => ?_, ?_, fun u v hu hv huv => ?_,
    fun u v hu hv huv => ?_⟩
  · rw [arcs _ ht]; exact o1 s' (by rwa [side_after ht] at hs')
  · rw [arcs _ hb]; exact o2 s' (by rwa [side_after hb] at hs')
  · rw [arcs _ hb]; exact o3
  · have := o4 u v hu hv (by rwa [cc ht hu hv] at huv)
    unfold PEq at this ⊢
    rw [cc ht hu k1, cc ht hv k2, cc ht hu k2, cc ht hv k1]; exact this
  · have := o5 u v hu hv (by rwa [cc hb hu hv] at huv)
    unfold PEq at this ⊢
    rw [cc hb hu k3, cc hb hv k4, cc hb hu k4, cc hb hv k3]; exact this

-- **The invariants after the move**, given the column invariant and the E1 condition.
--
theorem MoveCtx.inv_after
    (hthree : ∀ f, IsCell V f → Three (lowerCol H c s n) f →
      TriOK V (lowerCol H c s n) t0 u0 f)
    (hout : ∀ e ∈ lowerCol H c s n, (e.p ∉ V → e.q = t0 ∨ e.q = u0) ∧ (e.q ∉ V → e.p = t0 ∨ e.p = u0))
    (hcol : ∀ q s', IsCell V q → CriticalIn (lowerCol H c s n) q s' →
      back q s' ∈ lowerCol H c s n →
      (∀ j ∈ fpAfter FP i (npair (outArc H c s) c s), q ≠ j.top ∧ q ≠ j.bot) →
      0 < sgnD (outArc (lowerCol H c s n) q s') (D (lowerCol H c s n) H' q) →
      ColEnds V (lowerCol H c s n) (fpAfter FP i (npair (outArc H c s) c s)) q s'
        (outArc (lowerCol H c s n) q s'))
    (hside : SideInv V (lowerCol H c s n) H' (fpAfter FP i (npair (outArc H c s) c s))) :
    Inv V (lowerCol H c s n) H' (fpAfter FP i (npair (outArc H c s) c s)) t0 u0 := by
  set o := outArc H c s
  set np := npair o c s
  set H₁ := lowerCol H c s n
  have mem := fun (j : FixedPr) => mem_fpAfter (np := np) (j := j) M.hi
  have hnpm : np ∈ fpAfter FP i np := (mem np).2 (Or.inl rfl)
  refine ⟨?_, ?_, hthree, hout, ?_, ?_, ?_, ?_, ?_, hcol, hside⟩
  -- F2
  · intro q hq ha hcut
    by_cases hn : NearM c s n q
    · rcases (near_H1 M.ev M.two M.pat M.d1 M.d2 M.altB hn).1 ha with rfl | rfl
      · refine ⟨np, hnpm, ?_⟩
        rcases npair_sq o q s with ⟨h1, _⟩ | ⟨h1, _⟩
        · exact Or.inl h1.symm
        · exact Or.inr h1.symm
      · refine ⟨np, hnpm, ?_⟩
        rcases npair_sq o c s with ⟨_, h2⟩ | ⟨_, h2⟩
        · exact Or.inr h2.symm
        · exact Or.inl h2.symm
    · obtain ⟨j, hj, hq'⟩ := M.inv.f2 q hq ((alt_after hn).1 ha) ((cut_after M.conn hn).1 hcut)
      have hne : j ≠ i := by
        rintro rfl
        rcases M.pi with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hq' with h | h <;> rw [h] at hn
        · exact hn (by rw [h1]; exact M.near_n)
        · exact hn (by rw [h2]; exact M.near_n1)
        · exact hn (by rw [h2]; exact M.near_n1)
        · exact hn (by rw [h1]; exact M.near_n)
      exact ⟨j, (mem j).2 (Or.inr ⟨hj, hne⟩), hq'⟩
  -- F4
  · intro j hj
    rcases (mem j).1 hj with rfl | ⟨hj, hne⟩
    · exact M.np_ok
    · exact M.pairOK_away hj hne
  -- L4
  · intro q s' hq hb hf hn'
    by_cases hn : NearM c s n q
    · exact l4_of_dark (near_H1 M.ev M.two M.pat M.d1 M.d2 M.altB hn).2 s' hb hf hn'
    · have cc : ∀ {u v : Pt}, IsCorner u q → IsCorner v q → (Conn H₁ u v ↔ Conn H u v) :=
        fun hu hv => conn_corners_after M.conn hn hu hv
      have r := M.inv.l4 q s' hq ((cc (isCorner_back1 q s') (isCorner_back2 q s')).1 hb)
        ((cc (isCorner_front1 q s') (isCorner_front2 q s')).1 hf)
        (by rwa [cc (isCorner_back1 q s') (isCorner_front1 q s')] at hn')
      have e1 : back q s' ∈ H₁ ↔ back q s' ∈ H := side_after hn s'.opp
      have e2 : front q s' ∈ H₁ ↔ front q s' ∈ H := side_after hn s'
      rw [e1, e2]; exact r
  -- palt
  · intro j hj
    rcases (mem j).1 hj with rfl | ⟨hj, hne⟩
    · exact M.np_alt o
    · obtain ⟨ht, hb⟩ := M.other_away hj hne
      exact ⟨(alt_after ht).2 (M.inv.palt j hj).1, (alt_after hb).2 (M.inv.palt j hj).2⟩
  -- pdark
  · intro j hj
    rcases (mem j).1 hj with rfl | ⟨hj, hne⟩
    · exact M.np_dark o
    · exact (side_after (M.other_away hj hne).2 _).2 (M.inv.pdark j hj)
  -- pcorn
  · intro j hj
    rcases (mem j).1 hj with rfl | ⟨hj, _⟩
    · exact MoveCtx.np_corn o
    · exact M.inv.pcorn j hj
  -- pdisj
  · intro j hj j' hj' hov
    rcases (mem j).1 hj with rfl | ⟨hj, hne⟩ <;> rcases (mem j').1 hj' with rfl | ⟨hj', hne'⟩
    · rfl
    · exfalso
      obtain ⟨t1, b1⟩ := M.np_near o
      obtain ⟨t2, b2⟩ := M.other_away hj' hne'
      rcases hov with h | h | h | h
      · rw [h] at t1; exact t2 t1
      · rw [h] at t1; exact b2 t1
      · rw [h] at b1; exact t2 b1
      · rw [h] at b1; exact b2 b1
    · exfalso
      obtain ⟨t1, b1⟩ := M.np_near o
      obtain ⟨t2, b2⟩ := M.other_away hj hne
      rcases hov with h | h | h | h
      · rw [h] at t2; exact t2 t1
      · rw [h] at t2; exact t2 b1
      · rw [h] at b2; exact b2 t1
      · rw [h] at b2; exact b2 b1
    · exact M.inv.pdisj j hj j' hj' hov

end ctx

end HP

end SolidGridHam
