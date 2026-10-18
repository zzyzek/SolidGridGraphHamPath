/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import SolidGridHam.Cycle.V2Seq

/-!
# Rerouting even light sets across an even strip

Let `a` be an even strip of `F` (cells `c_0 … c_(k+1)`) and `F' = F ⊕ a`. An even set of
light sides of `F'` that avoids the sides of the first and last cells crosses the strip only
laterally through odd cells. Each such crossing at `c_j` can be moved to `c_(j+1)` by adding
the six sides `Tsw j` (an even set: the sum of the stars of `c_j`'s two front corners). The
result is an even set of light sides of `F`, equal to the original away from the strip.

This is the precise form of the thesis's Lemma 7.1 (dual paths survive a strip flip unless
they use its end cells).
-/

namespace SolidGridHam

open Finset Classical

/-! ## The six-side swap -/

lemma ind_insert {e : Edge} {B : Finset Edge} (he : e ∉ B) (f : Edge) :
    ind (insert e B) f = ind B f + if e = f then 1 else 0 := by
  unfold ind
  by_cases h : e = f
  · subst h; simp [he]
  · have : f ≠ e := fun h' => h h'.symm
    simp [Finset.mem_insert, this, h]

lemma sidesIn_insert (e : Edge) (B : Finset Edge) (x : Pt) (he : e ∉ B) :
    sidesIn (insert e B) x = sidesIn B x + if e ∈ cellE x then 1 else 0 := by
  unfold sidesIn
  rw [ind_insert he, ind_insert he, ind_insert he, ind_insert he]
  obtain ⟨p, q⟩ := x
  have key : (if e = bot (p, q) then 1 else 0) + (if e = top (p, q) then 1 else 0) +
      (if e = lft (p, q) then 1 else 0) + (if e = rgt (p, q) then 1 else 0) =
      (if e ∈ cellE (p, q) then 1 else 0 : ℕ) := by
    unfold cellE
    by_cases h1 : e = bot (p, q)
    · subst h1; simp [bot, top, lft, rgt]
    by_cases h2 : e = top (p, q)
    · subst h2; simp [bot, top, lft, rgt]
    by_cases h3 : e = lft (p, q)
    · subst h3; simp [bot, top, lft, rgt]
    by_cases h4 : e = rgt (p, q)
    · subst h4; simp [bot, top, lft, rgt]
    simp [h1, h2, h3, h4]
  omega

lemma ite_or_ne {x A B : Pt} (h : A ≠ B) :
    (if x = A ∨ x = B then 1 else 0 : ℕ) = (if x = A then 1 else 0) + (if x = B then 1 else 0) := by
  by_cases h1 : x = A
  · subst h1; simp [h]
  · simp [h1]

section swap

variable (c : Pt) (s : Side)

lemma nb_comm_lat (j : ℕ) :
    nb (nb (cellJ c s j) (latA s)) s = nb (cellJ c s (j + 1)) (latA s) ∧
      nb (nb (cellJ c s j) (latB s)) s = nb (cellJ c s (j + 1)) (latB s) := by
  obtain ⟨a, b⟩ := c
  cases s <;> simp [nb, cellJ, latA, latB] <;> ring

lemma Tsw_distinct (j : ℕ) :
    lat1 (cellJ c s j) s ≠ lat2 (cellJ c s j) s ∧ lat1 (cellJ c s j) s ≠ lat1 (cellJ c s (j + 1)) s ∧
    lat1 (cellJ c s j) s ≠ lat2 (cellJ c s (j + 1)) s ∧ lat1 (cellJ c s j) s ≠ outer1 (cellJ c s j) s ∧
    lat1 (cellJ c s j) s ≠ outer2 (cellJ c s j) s ∧
    lat2 (cellJ c s j) s ≠ lat1 (cellJ c s (j + 1)) s ∧ lat2 (cellJ c s j) s ≠ lat2 (cellJ c s (j + 1)) s ∧
    lat2 (cellJ c s j) s ≠ outer1 (cellJ c s j) s ∧ lat2 (cellJ c s j) s ≠ outer2 (cellJ c s j) s ∧
    lat1 (cellJ c s (j + 1)) s ≠ lat2 (cellJ c s (j + 1)) s ∧
    lat1 (cellJ c s (j + 1)) s ≠ outer1 (cellJ c s j) s ∧ lat1 (cellJ c s (j + 1)) s ≠ outer2 (cellJ c s j) s ∧
    lat2 (cellJ c s (j + 1)) s ≠ outer1 (cellJ c s j) s ∧ lat2 (cellJ c s (j + 1)) s ≠ outer2 (cellJ c s j) s ∧
    outer1 (cellJ c s j) s ≠ outer2 (cellJ c s j) s := by
  obtain ⟨a, b⟩ := c
  cases s <;> simp [lat1, lat2, outer1, outer2, cellJ, bot, top, lft, rgt] <;> omega

-- Sides swapped when a lateral crossing moves from cell `j` to cell `j + 1`.
--
def Tsw (j : ℕ) : Finset Edge :=
  {lat1 (cellJ c s j) s, lat2 (cellJ c s j) s, lat1 (cellJ c s (j + 1)) s,
    lat2 (cellJ c s (j + 1)) s, outer1 (cellJ c s j) s, outer2 (cellJ c s j) s}

lemma Tsw_even (j : ℕ) (x : Pt) : sidesIn (Tsw c s j) x % 2 = 0 := by
  have l1 := lat1_eq (cellJ c s j) s
  have l2 := lat2_eq (cellJ c s j) s
  have l3 := lat1_eq (cellJ c s (j + 1)) s
  have l4 := lat2_eq (cellJ c s (j + 1)) s
  have o1 := outer1_side_nb (cellJ c s j) s
  have o2 := outer2_side_nb (cellJ c s j) s
  have n1 := nb_comm_lat c s j
  -- the six sides are distinct
  have d := Tsw_distinct c s j
  obtain ⟨d12, d13, d14, d15, d16, d23, d24, d25, d26, d34, d35, d36, d45, d46, d56⟩ := d
  unfold Tsw
  rw [sidesIn_insert _ _ _ (by simp [d12, d13, d14, d15, d16]),
    sidesIn_insert _ _ _ (by simp [d23, d24, d25, d26]),
    sidesIn_insert _ _ _ (by simp [d34, d35, d36]),
    sidesIn_insert _ _ _ (by simp [d45, d46]),
    sidesIn_insert _ _ _ (by simp [d56]), sidesIn_single]
  rw [l1, l2, l3, l4, o1, o2]
  simp only [side_mem_cellE_iff]
  rw [n1.1, n1.2]
  have e1 : nb (cellJ c s j) (latA s) ≠ nb (cellJ c s (j + 1)) (latA s) := by
    rw [← n1.1]; exact nb_ne _ _
  have e2 : nb (cellJ c s j) (latB s) ≠ nb (cellJ c s (j + 1)) (latB s) := by
    rw [← n1.2]; exact nb_ne _ _
  rw [ite_or_ne (nb_ne _ _), ite_or_ne (nb_ne _ _), ite_or_ne (nb_ne _ _), ite_or_ne (nb_ne _ _),
    ite_or_ne e1, ite_or_ne e2]
  omega

lemma Tsw_disj {j j' : ℕ} (hj : j % 2 = 1) (hj' : j' % 2 = 1) (h : j ≠ j') :
    Disjoint (Tsw c s j) (Tsw c s j') := by
  rw [Finset.disjoint_left]
  intro e h1 h2
  obtain ⟨a, b⟩ := c
  cases s <;>
    simp only [Tsw, Finset.mem_insert, Finset.mem_singleton, lat1, lat2, outer1, outer2, cellJ,
      bot, top, lft, rgt] at h1 h2 <;>
    rcases h1 with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [Edge.mk.injEq, Prod.mk.injEq, reduceCtorEq, true_and, false_and, or_false,
      false_or] at h2 <;> omega

end swap

lemma ind_union_disj {A B : Finset Edge} (h : Disjoint A B) (e : Edge) :
    ind (A ∪ B) e = ind A e + ind B e := by
  unfold ind
  by_cases ha : e ∈ A <;> by_cases hb : e ∈ B <;> simp [ha, hb]
  exact Finset.disjoint_left.1 h ha hb

lemma sidesIn_biUnion_even (J : Finset ℕ) (f : ℕ → Finset Edge)
    (hd : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → Disjoint (f i) (f j))
    (he : ∀ j ∈ J, ∀ x, sidesIn (f j) x % 2 = 0) (x : Pt) :
    sidesIn (J.biUnion f) x % 2 = 0 := by
  induction J using Finset.induction_on with
  | empty => simp [sidesIn, ind]
  | insert a J ha ih =>
    rw [Finset.biUnion_insert]
    have hdis : Disjoint (f a) (J.biUnion f) := by
      rw [Finset.disjoint_biUnion_right]
      intro j hj
      exact hd a (Finset.mem_insert_self a J) j (Finset.mem_insert_of_mem hj)
        (fun h => ha (h ▸ hj))
    have ih' := ih (fun i hi j hj => hd i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj))
      (fun j hj => he j (Finset.mem_insert_of_mem hj))
    have h0 := he a (Finset.mem_insert_self a J) x
    unfold sidesIn at *
    rw [ind_union_disj hdis, ind_union_disj hdis, ind_union_disj hdis, ind_union_disj hdis]
    omega

lemma sidesIn_frame (B : Finset Edge) (d : Pt) (s : Side) :
    sidesIn B d = ind B (back d s) + ind B (front d s) + ind B (lat1 d s) + ind B (lat2 d s) := by
  cases s <;> simp only [sidesIn, back, front, lat1, lat2, sideEdge, Side.opp] <;> ring

/-! ## Rerouting from `F ⊕ a` back to `F` -/

section reroute

variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hF : Deg2 V F) (hk : k % 2 = 0) (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j))
  (hpat : StripPat F c s (k + 2))
include hF hk hcell hpat

theorem reroute_back {B : Finset Edge} (heven : ∀ x, IsCell V x → sidesIn B x % 2 = 0)
    (hlight : ∀ e ∈ B, e ∉ flipCol F c s (k + 2)) (h0 : ∀ e ∈ B, e ∉ cellE c)
    (hu : ∀ e ∈ B, e ∉ cellE (cellJ c s (k + 1))) :
    ∃ B' : Finset Edge, (∀ x, IsCell V x → sidesIn B' x % 2 = 0) ∧ (∀ e ∈ B', e ∉ F) ∧
      (∀ e ∈ B', e ∉ cellE c ∧ e ∉ cellE (cellJ c s (k + 1))) ∧
      (∀ e, (∀ j, e ∉ Tsw c s j) → (e ∈ B' ↔ e ∈ B)) := by
  set F' := flipCol F c s (k + 2)
  -- Even cells' lateral sides and interior fronts are dark in `F'`; fronts are unchanged.
  have latE : ∀ j ≤ k + 1, j % 2 = 0 → lat1 (cellJ c s j) s ∉ B ∧ lat2 (cellJ c s j) s ∉ B :=
    fun j hj he => ⟨fun h => hlight _ h ((lat1_after hk hpat hj).2 he),
      fun h => hlight _ h ((lat2_after hk hpat hj).2 he)⟩
  have frO : ∀ j ≤ k, j % 2 = 1 → front (cellJ c s j) s ∉ B :=
    fun j hj ho h => hlight _ h ((front_after hk hpat hj).2 ho)
  -- Interior fronts of even cells are not in `B` (parity at the even cell).
  have frE : ∀ j ≤ k, j % 2 = 0 → front (cellJ c s j) s ∉ B := by
    intro j hj he hfB
    rcases j with _ | j
    · exact h0 _ hfB (by have h := front_mem_self c s 0; rw [cellJ_zero] at h ⊢; exact h)
    · have hev := heven _ (hcell (j + 1) (by omega))
      rw [sidesIn_frame B _ s, back_cellJ_succ] at hev
      have i1 : ind B (front (cellJ c s j) s) = 0 := by
        simp [ind, frO j (by omega) (by omega)]
      have i2 : ind B (lat1 (cellJ c s (j + 1)) s) = 0 := by
        simp [ind, (latE (j + 1) (by omega) he).1]
      have i3 : ind B (lat2 (cellJ c s (j + 1)) s) = 0 := by
        simp [ind, (latE (j + 1) (by omega) he).2]
      have i4 : ind B (front (cellJ c s (j + 1)) s) = 1 := by simp [ind, hfB]
      omega
  -- At an odd cell, both lateral sides or neither.
  have pair : ∀ j ≤ k, j % 2 = 1 →
      (lat1 (cellJ c s j) s ∈ B ↔ lat2 (cellJ c s j) s ∈ B) := by
    intro j hj ho
    obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
    have hev := heven _ (hcell (m + 1) (by omega))
    rw [sidesIn_frame B _ s, back_cellJ_succ] at hev
    have i1 : ind B (front (cellJ c s m) s) = 0 := by simp [ind, frE m (by omega) (by omega)]
    have i2 : ind B (front (cellJ c s (m + 1)) s) = 0 := by simp [ind, frO (m + 1) hj ho]
    rw [i1, i2] at hev
    by_cases h1 : lat1 (cellJ c s (m + 1)) s ∈ B <;> by_cases h2 : lat2 (cellJ c s (m + 1)) s ∈ B <;>
      simp [ind, h1, h2] at hev ⊢
  set J := (Finset.range (k + 1)).filter (fun j => j % 2 = 1 ∧ lat1 (cellJ c s j) s ∈ B)
  set T := J.biUnion (Tsw c s)
  have memJ : ∀ j, j ∈ J ↔ j ≤ k ∧ j % 2 = 1 ∧ lat1 (cellJ c s j) s ∈ B := by
    intro j; simp only [J, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨a, b, c⟩; exact ⟨by omega, b, c⟩
    · rintro ⟨a, b, c⟩; exact ⟨by omega, b, c⟩
  have hTev : ∀ x, sidesIn T x % 2 = 0 :=
    sidesIn_biUnion_even J (Tsw c s)
      (fun i hi j hj hij => Tsw_disj c s ((memJ i).1 hi).2.1 ((memJ j).1 hj).2.1 hij)
      (fun j _ x => Tsw_even c s j x)
  refine ⟨symmDiff B T, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [sidesIn_symmDiff]
    have := heven x hx
    have := hTev x
    omega
  · intro e he
    rcases Finset.mem_symmDiff.1 he with ⟨heB, heT⟩ | ⟨heT, heB⟩
    · -- In `B` and not swapped: an unchanged side.
      by_cases hs : ∃ m ≤ k + 1, e ∈ cellE (cellJ c s m)
      · obtain ⟨m, hm, hem⟩ := hs
        rw [cellE_frame _ s] at hem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hem
        rcases hem with rfl | rfl | rfl | rfl
        · -- a back side: the front of the cell before
          rcases m with _ | m
          · exact absurd (by rw [cellJ_zero]; rw [cellE_frame _ s]; simp) (h0 _ heB)
          · rw [back_cellJ_succ] at heB ⊢
            intro hF'
            have hm' : m ≤ k := by omega
            have e1 := (front_after hk hpat hm')
            have e2 := hpat.2.2 m (by omega)
            have q : m + 1 < k + 2 := by omega
            simp only [q, iff_true] at e2
            exact hlight _ heB (e1.2 (e2.1 hF'))
        · rcases (show m ≤ k ∨ m = k + 1 by omega) with hm' | rfl
          · intro hF'
            have e1 := (front_after hk hpat hm')
            have e2 := hpat.2.2 m (by omega)
            have q : m + 1 < k + 2 := by omega
            simp only [q, iff_true] at e2
            exact hlight _ heB (e1.2 (e2.1 hF'))
          · exact absurd (by rw [cellE_frame _ s]; simp) (hu _ heB)
        · rcases Nat.mod_two_eq_zero_or_one m with he' | ho
          · exact absurd heB (latE m hm he').1
          · rcases (show m ≤ k ∨ m = k + 1 by omega) with hm' | rfl
            · exact absurd (Finset.mem_biUnion.2 ⟨m, (memJ m).2 ⟨hm', ho, heB⟩, by simp [Tsw]⟩) heT
            · exact absurd (lat1_mem_self c s (k + 1)) (hu _ heB)
        · rcases Nat.mod_two_eq_zero_or_one m with he' | ho
          · exact absurd heB (latE m hm he').2
          · rcases (show m ≤ k ∨ m = k + 1 by omega) with hm' | rfl
            · exact absurd (Finset.mem_biUnion.2 ⟨m, (memJ m).2 ⟨hm', ho, (pair m hm' ho).2 heB⟩,
                by simp [Tsw]⟩) heT
            · exact absurd (lat2_mem_self c s (k + 1)) (hu _ heB)
      · push Not at hs
        intro hF'
        apply hlight e heB
        rw [mem_after, nOn_zero c s (fun m hm => hs m (by omega))]
        simp [hF']
    · -- Swapped in: a lateral side of an even cell, or an outer side.
      obtain ⟨j, hj, heT'⟩ := Finset.mem_biUnion.1 heT
      obtain ⟨hjk, hjo, hjB⟩ := (memJ j).1 hj
      have hjk' : j + 1 ≤ k := by omega
      simp only [Tsw, Finset.mem_insert, Finset.mem_singleton] at heT'
      rcases heT' with rfl | rfl | rfl | rfl | rfl | rfl
      · exact absurd hjB heB
      · exact absurd ((pair j hjk hjo).1 hjB) heB
      · intro h; have := (hpat.2.1 (j + 1) (by omega)).1.1 h; omega
      · intro h; have := (hpat.2.1 (j + 1) (by omega)).2.1 h; omega
      · -- degree count at `front1 c_j`
        intro hO
        obtain ⟨_, _, f1V, _⟩ := isCell_corners (hcell j (by omega)) s
        have d1 := deg_front1 (cellJ c s j) s F
        rw [hF.2 _ f1V, nb_cellJ] at d1
        have a1 : ind F (lat1 (cellJ c s j) s) = 1 := by
          simp [ind, (hpat.2.1 j (by omega)).1.2 hjo]
        have a2 : ind F (front (cellJ c s j) s) = 1 := by
          have q : j + 1 < k + 2 := by omega
          simp [ind, (hpat.2.2 j (by omega)).2 (by simp [q]; exact hjo)]
        have a3 : ind F (outer1 (cellJ c s j) s) = 1 := by simp [ind, hO]
        have := ind_le_one F (lat1 (cellJ c s (j + 1)) s)
        omega
      · intro hO
        obtain ⟨_, _, _, f2V⟩ := isCell_corners (hcell j (by omega)) s
        have d2 := deg_front2 (cellJ c s j) s F
        rw [hF.2 _ f2V, nb_cellJ] at d2
        have a1 : ind F (lat2 (cellJ c s j) s) = 1 := by
          simp [ind, (hpat.2.1 j (by omega)).2.2 hjo]
        have a2 : ind F (front (cellJ c s j) s) = 1 := by
          have q : j + 1 < k + 2 := by omega
          simp [ind, (hpat.2.2 j (by omega)).2 (by simp [q]; exact hjo)]
        have a3 : ind F (outer2 (cellJ c s j) s) = 1 := by simp [ind, hO]
        have := ind_le_one F (lat2 (cellJ c s (j + 1)) s)
        omega
  · intro e he
    rcases Finset.mem_symmDiff.1 he with ⟨heB, _⟩ | ⟨heT, _⟩
    · exact ⟨h0 e heB, hu e heB⟩
    · obtain ⟨j, hj, heT'⟩ := Finset.mem_biUnion.1 heT
      obtain ⟨hjk, hjo, _⟩ := (memJ j).1 hj
      have z1 := lat1_not_mem c s (j := j) (m := 0) (by omega)
      have z2 := lat2_not_mem c s (j := j) (m := 0) (by omega)
      have z3 := lat1_not_mem c s (j := j + 1) (m := 0) (by omega)
      have z4 := lat2_not_mem c s (j := j + 1) (m := 0) (by omega)
      have z5 := outer1_not_mem c s j 0
      have z6 := outer2_not_mem c s j 0
      rw [cellJ_zero] at z1 z2 z3 z4 z5 z6
      simp only [Tsw, Finset.mem_insert, Finset.mem_singleton] at heT'
      rcases heT' with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨z1, lat1_not_mem c s (by omega)⟩
      · exact ⟨z2, lat2_not_mem c s (by omega)⟩
      · exact ⟨z3, lat1_not_mem c s (by omega)⟩
      · exact ⟨z4, lat2_not_mem c s (by omega)⟩
      · exact ⟨z5, outer1_not_mem c s j (k + 1)⟩
      · exact ⟨z6, outer2_not_mem c s j (k + 1)⟩
  · intro e he
    have : e ∉ T := fun h => by
      obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.1 h
      exact he j hj
    rw [Finset.mem_symmDiff]
    tauto

/-! ## Rerouting from `F` to `F ⊕ a` -/

theorem reroute_fwd {B : Finset Edge} (heven : ∀ x, IsCell V x → sidesIn B x % 2 = 0)
    (hlight : ∀ e ∈ B, e ∉ F) (h0 : ∀ e ∈ B, e ∉ cellE c)
    (hu : ∀ e ∈ B, e ∉ cellE (cellJ c s (k + 1))) :
    ∃ B' : Finset Edge, (∀ x, IsCell V x → sidesIn B' x % 2 = 0) ∧
      (∀ e ∈ B', e ∉ flipCol F c s (k + 2)) ∧
      (∀ e ∈ B', e ∉ cellE c ∧ e ∉ cellE (cellJ c s (k + 1))) ∧
      (∀ e, (∀ j, e ∉ Tsw c s j) → (e ∈ B' ↔ e ∈ B)) := by
  set F' := flipCol F c s (k + 2)
  -- Odd cells' lateral sides and fronts are dark in `F`.
  have latO : ∀ j ≤ k + 1, j % 2 = 1 → lat1 (cellJ c s j) s ∉ B ∧ lat2 (cellJ c s j) s ∉ B :=
    fun j hj ho => ⟨fun h => hlight _ h ((hpat.2.1 j (by omega)).1.2 ho),
      fun h => hlight _ h ((hpat.2.1 j (by omega)).2.2 ho)⟩
  have frO : ∀ j ≤ k, j % 2 = 1 → front (cellJ c s j) s ∉ B := by
    intro j hj ho h
    have q : j + 1 < k + 2 := by omega
    exact hlight _ h ((hpat.2.2 j (by omega)).2 (by simp [q]; exact ho))
  -- Fronts of even cells are not in `B` (parity at the next, odd, cell).
  have frE : ∀ j ≤ k, j % 2 = 0 → front (cellJ c s j) s ∉ B := by
    intro j hj he hfB
    rcases (show j + 1 ≤ k ∨ j = k by omega) with hjk | rfl
    · have hev := heven _ (hcell (j + 1) (by omega))
      rw [sidesIn_frame B _ s, back_cellJ_succ] at hev
      have i1 : ind B (front (cellJ c s (j + 1)) s) = 0 := by
        simp [ind, frO (j + 1) hjk (by omega)]
      have i2 : ind B (lat1 (cellJ c s (j + 1)) s) = 0 := by
        simp [ind, (latO (j + 1) (by omega) (by omega)).1]
      have i3 : ind B (lat2 (cellJ c s (j + 1)) s) = 0 := by
        simp [ind, (latO (j + 1) (by omega) (by omega)).2]
      have i4 : ind B (front (cellJ c s j) s) = 1 := by simp [ind, hfB]
      omega
    · exact hu _ hfB (front_mem_next c s j)
  -- At an even interior cell, both lateral sides or neither.
  have pair : ∀ j ≤ k, j % 2 = 0 → 1 ≤ j →
      (lat1 (cellJ c s j) s ∈ B ↔ lat2 (cellJ c s j) s ∈ B) := by
    intro j hj he h1
    obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
    have hev := heven _ (hcell (m + 1) (by omega))
    rw [sidesIn_frame B _ s, back_cellJ_succ] at hev
    have i1 : ind B (front (cellJ c s m) s) = 0 := by simp [ind, frO m (by omega) (by omega)]
    have i2 : ind B (front (cellJ c s (m + 1)) s) = 0 := by
      simp [ind, frE (m + 1) hj he]
    rw [i1, i2] at hev
    by_cases h1 : lat1 (cellJ c s (m + 1)) s ∈ B <;> by_cases h2 : lat2 (cellJ c s (m + 1)) s ∈ B <;>
      simp [ind, h1, h2] at hev ⊢
  set J := (Finset.range (k + 1)).filter (fun j => j % 2 = 0 ∧ 1 ≤ j ∧ lat1 (cellJ c s j) s ∈ B)
  have memJ : ∀ j, j ∈ J ↔ j ≤ k ∧ j % 2 = 0 ∧ 1 ≤ j ∧ lat1 (cellJ c s j) s ∈ B := by
    intro j; simp only [J, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨a, b, c, d⟩; exact ⟨by omega, b, c, d⟩
    · rintro ⟨a, b, c, d⟩; exact ⟨by omega, b, c, d⟩
  set T := J.biUnion (fun j => Tsw c s (j - 1))
  have hTev : ∀ x, sidesIn T x % 2 = 0 :=
    sidesIn_biUnion_even J (fun j => Tsw c s (j - 1))
      (fun i hi j hj hij => by
        obtain ⟨_, a1, a2, _⟩ := (memJ i).1 hi
        obtain ⟨_, b1, b2, _⟩ := (memJ j).1 hj
        exact Tsw_disj c s (by omega) (by omega) (by omega))
      (fun j _ x => Tsw_even c s (j - 1) x)
  refine ⟨symmDiff B T, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [sidesIn_symmDiff]
    have := heven x hx
    have := hTev x
    omega
  · intro e he
    rcases Finset.mem_symmDiff.1 he with ⟨heB, heT⟩ | ⟨heT, heB⟩
    · by_cases hs : ∃ m ≤ k + 1, e ∈ cellE (cellJ c s m)
      · obtain ⟨m, hm, hem⟩ := hs
        rw [cellE_frame _ s] at hem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hem
        rcases hem with rfl | rfl | rfl | rfl
        · rcases m with _ | m
          · exact absurd (by rw [cellJ_zero]; rw [cellE_frame _ s]; simp) (h0 _ heB)
          · rw [back_cellJ_succ] at heB ⊢
            rcases Nat.mod_two_eq_zero_or_one m with he' | ho
            · exact absurd heB (frE m (by omega) he')
            · exact absurd heB (frO m (by omega) ho)
        · rcases (show m ≤ k ∨ m = k + 1 by omega) with hm' | rfl
          · rcases Nat.mod_two_eq_zero_or_one m with he' | ho
            · exact absurd heB (frE m hm' he')
            · exact absurd heB (frO m hm' ho)
          · exact absurd (by rw [cellE_frame _ s]; simp) (hu _ heB)
        · rcases Nat.mod_two_eq_zero_or_one m with he' | ho
          · rcases m with _ | m
            · exact absurd (by have h := lat1_mem_self c s 0; rw [cellJ_zero] at h ⊢; exact h) (h0 _ heB)
            · rcases (show m + 1 ≤ k ∨ m + 1 = k + 1 by omega) with hm' | hm'
              · exact absurd (Finset.mem_biUnion.2 ⟨m + 1, (memJ (m + 1)).2 ⟨hm', he', by omega, heB⟩,
                  by simp [Tsw]⟩) heT
              · omega
          · exact absurd heB (latO m hm ho).1
        · rcases Nat.mod_two_eq_zero_or_one m with he' | ho
          · rcases m with _ | m
            · exact absurd (by have h := lat2_mem_self c s 0; rw [cellJ_zero] at h ⊢; exact h) (h0 _ heB)
            · rcases (show m + 1 ≤ k ∨ m + 1 = k + 1 by omega) with hm' | hm'
              · exact absurd (Finset.mem_biUnion.2 ⟨m + 1,
                  (memJ (m + 1)).2 ⟨hm', he', by omega, (pair (m + 1) hm' he' (by omega)).2 heB⟩,
                  by simp [Tsw]⟩) heT
              · omega
          · exact absurd heB (latO m hm ho).2
      · push Not at hs
        intro hF'
        apply hlight e heB
        have := (mem_after e).1 hF'
        rw [nOn_zero c s (fun m hm => hs m (by omega))] at this
        simpa using this
    · obtain ⟨j, hj, heT'⟩ := Finset.mem_biUnion.1 heT
      obtain ⟨hjk, hje, hj1, hjB⟩ := (memJ j).1 hj
      obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      simp only [Nat.add_sub_cancel, Tsw, Finset.mem_insert, Finset.mem_singleton] at heT'
      rcases heT' with rfl | rfl | rfl | rfl | rfl | rfl
      · intro h; have := (lat1_after hk hpat (j := i) (by omega)).1 h; omega
      · intro h; have := (lat2_after hk hpat (j := i) (by omega)).1 h; omega
      · exact absurd hjB heB
      · exact absurd ((pair (i + 1) hjk hje hj1).1 hjB) heB
      · -- outer sides of odd cells are light and unchanged
        intro hO
        have hO' := (mem_after _).1 hO
        rw [nOn_zero c s (fun m _ => outer1_not_mem c s i m)] at hO'
        simp only [Nat.zero_mod, iff_true] at hO'
        obtain ⟨_, _, f1V, _⟩ := isCell_corners (hcell i (by omega)) s
        have d1 := deg_front1 (cellJ c s i) s F
        rw [hF.2 _ f1V, nb_cellJ] at d1
        have a1 : ind F (lat1 (cellJ c s i) s) = 1 := by
          simp [ind, (hpat.2.1 i (by omega)).1.2 (by omega)]
        have a2 : ind F (front (cellJ c s i) s) = 1 := by
          have q : i + 1 < k + 2 := by omega
          simp [ind, (hpat.2.2 i (by omega)).2 (by simp [q]; omega)]
        have a3 : ind F (outer1 (cellJ c s i) s) = 1 := by simp [ind, hO']
        have := ind_le_one F (lat1 (cellJ c s (i + 1)) s)
        omega
      · intro hO
        have hO' := (mem_after _).1 hO
        rw [nOn_zero c s (fun m _ => outer2_not_mem c s i m)] at hO'
        simp only [Nat.zero_mod, iff_true] at hO'
        obtain ⟨_, _, _, f2V⟩ := isCell_corners (hcell i (by omega)) s
        have d2 := deg_front2 (cellJ c s i) s F
        rw [hF.2 _ f2V, nb_cellJ] at d2
        have a1 : ind F (lat2 (cellJ c s i) s) = 1 := by
          simp [ind, (hpat.2.1 i (by omega)).2.2 (by omega)]
        have a2 : ind F (front (cellJ c s i) s) = 1 := by
          have q : i + 1 < k + 2 := by omega
          simp [ind, (hpat.2.2 i (by omega)).2 (by simp [q]; omega)]
        have a3 : ind F (outer2 (cellJ c s i) s) = 1 := by simp [ind, hO']
        have := ind_le_one F (lat2 (cellJ c s (i + 1)) s)
        omega
  · intro e he
    rcases Finset.mem_symmDiff.1 he with ⟨heB, _⟩ | ⟨heT, _⟩
    · exact ⟨h0 e heB, hu e heB⟩
    · obtain ⟨j, hj, heT'⟩ := Finset.mem_biUnion.1 heT
      obtain ⟨hjk, hje, hj1, _⟩ := (memJ j).1 hj
      obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      have z1 := lat1_not_mem c s (j := i) (m := 0) (by omega)
      have z2 := lat2_not_mem c s (j := i) (m := 0) (by omega)
      have z3 := lat1_not_mem c s (j := i + 1) (m := 0) (by omega)
      have z4 := lat2_not_mem c s (j := i + 1) (m := 0) (by omega)
      have z5 := outer1_not_mem c s i 0
      have z6 := outer2_not_mem c s i 0
      rw [cellJ_zero] at z1 z2 z3 z4 z5 z6
      simp only [Nat.add_sub_cancel, Tsw, Finset.mem_insert, Finset.mem_singleton] at heT'
      rcases heT' with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨z1, lat1_not_mem c s (by omega)⟩
      · exact ⟨z2, lat2_not_mem c s (by omega)⟩
      · exact ⟨z3, lat1_not_mem c s (by omega)⟩
      · exact ⟨z4, lat2_not_mem c s (by omega)⟩
      · exact ⟨z5, outer1_not_mem c s i (k + 1)⟩
      · exact ⟨z6, outer2_not_mem c s i (k + 1)⟩
  · intro e he
    have : e ∉ T := fun h => by
      obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.1 h
      exact he (j - 1) hj
    rw [Finset.mem_symmDiff]
    tauto

/-! ## Rerouting from `F` to `F ⊕ a`, through the new rung at the end cell -/

theorem reroute_fwd_rung {B : Finset Edge} (heven : ∀ x, IsCell V x → sidesIn B x % 2 = 0)
    (hlight0 : ∀ e ∈ B, e ∉ F ∨ e = lat1 (cellJ c s (k + 1)) s ∨ e = lat2 (cellJ c s (k + 1)) s)
    (h0 : ∀ e ∈ B, e ∉ cellE c)
    (hu : ∀ e ∈ B, e ∈ cellE (cellJ c s (k + 1)) →
      e = lat1 (cellJ c s (k + 1)) s ∨ e = lat2 (cellJ c s (k + 1)) s) :
    ∃ B' : Finset Edge, (∀ x, IsCell V x → sidesIn B' x % 2 = 0) ∧
      (∀ e ∈ B', e ∉ flipCol F c s (k + 2)) ∧
      (∀ e ∈ B', e ∉ cellE c ∧ (e ∈ cellE (cellJ c s (k + 1)) →
        e = lat1 (cellJ c s (k + 1)) s ∨ e = lat2 (cellJ c s (k + 1)) s)) ∧
      (∀ e, (∀ j, e ∉ Tsw c s j) → (e ∈ B' ↔ e ∈ B)) := by
  set F' := flipCol F c s (k + 2)
  have uL1n : ∀ j ≤ k, lat1 (cellJ c s j) s ≠ lat1 (cellJ c s (k + 1)) s ∧
      lat1 (cellJ c s j) s ≠ lat2 (cellJ c s (k + 1)) s ∧
      lat2 (cellJ c s j) s ≠ lat1 (cellJ c s (k + 1)) s ∧
      lat2 (cellJ c s j) s ≠ lat2 (cellJ c s (k + 1)) s := by
    intro j hj
    refine ⟨fun h => lat1_not_mem c s (j := j) (m := k + 1) (by omega) (h ▸ lat1_mem_self c s (k + 1)),
      fun h => lat1_not_mem c s (j := j) (m := k + 1) (by omega) (h ▸ lat2_mem_self c s (k + 1)),
      fun h => lat2_not_mem c s (j := j) (m := k + 1) (by omega) (h ▸ lat1_mem_self c s (k + 1)),
      fun h => lat2_not_mem c s (j := j) (m := k + 1) (by omega) (h ▸ lat2_mem_self c s (k + 1))⟩
  have hlight : ∀ e ∈ B, e ∉ cellE (cellJ c s (k + 1)) → e ∉ F := by
    intro e he hn
    rcases hlight0 e he with h | rfl | rfl
    · exact h
    · exact absurd (lat1_mem_self c s (k + 1)) hn
    · exact absurd (lat2_mem_self c s (k + 1)) hn
  have huB : ∀ e ∈ B, e ≠ back (cellJ c s (k + 1)) s ∧ e ≠ front (cellJ c s (k + 1)) s := by
    intro e he
    have hb : back (cellJ c s (k + 1)) s ∈ cellE (cellJ c s (k + 1)) := by rw [cellE_frame _ s]; simp
    have hf : front (cellJ c s (k + 1)) s ∈ cellE (cellJ c s (k + 1)) := by rw [cellE_frame _ s]; simp
    have nb1 : back (cellJ c s (k + 1)) s ≠ lat1 (cellJ c s (k + 1)) s ∧
        back (cellJ c s (k + 1)) s ≠ lat2 (cellJ c s (k + 1)) s ∧
        front (cellJ c s (k + 1)) s ≠ lat1 (cellJ c s (k + 1)) s ∧
        front (cellJ c s (k + 1)) s ≠ lat2 (cellJ c s (k + 1)) s := by
      generalize cellJ c s (k + 1) = r; obtain ⟨x, y⟩ := r
      cases s <;> simp [back, front, lat1, lat2, sideEdge, Side.opp, bot, top, lft, rgt]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · subst h; rcases hu _ he hb with h | h
      · exact nb1.1 h
      · exact nb1.2.1 h
    · subst h; rcases hu _ he hf with h | h
      · exact nb1.2.2.1 h
      · exact nb1.2.2.2 h
  -- Odd cells' lateral sides and fronts are dark in `F`.
  have latO : ∀ j ≤ k, j % 2 = 1 → lat1 (cellJ c s j) s ∉ B ∧ lat2 (cellJ c s j) s ∉ B :=
    fun j hj ho => ⟨fun h => hlight _ h (lat1_not_mem c s (by omega)) ((hpat.2.1 j (by omega)).1.2 ho),
      fun h => hlight _ h (lat2_not_mem c s (by omega)) ((hpat.2.1 j (by omega)).2.2 ho)⟩
  have frO : ∀ j ≤ k, j % 2 = 1 → front (cellJ c s j) s ∉ B := by
    intro j hj ho h
    have q : j + 1 < k + 2 := by omega
    have hn : front (cellJ c s j) s ∉ cellE (cellJ c s (k + 1)) :=
      front_not_mem c s (by omega) (by omega)
    exact hlight _ h hn ((hpat.2.2 j (by omega)).2 (by simp [q]; exact ho))
  -- Fronts of even cells are not in `B` (parity at the next, odd, cell).
  have frE : ∀ j ≤ k, j % 2 = 0 → front (cellJ c s j) s ∉ B := by
    intro j hj he hfB
    rcases (show j + 1 ≤ k ∨ j = k by omega) with hjk | rfl
    · have hev := heven _ (hcell (j + 1) (by omega))
      rw [sidesIn_frame B _ s, back_cellJ_succ] at hev
      have i1 : ind B (front (cellJ c s (j + 1)) s) = 0 := by
        simp [ind, frO (j + 1) hjk (by omega)]
      have i2 : ind B (lat1 (cellJ c s (j + 1)) s) = 0 := by
        simp [ind, (latO (j + 1) (by omega) (by omega)).1]
      have i3 : ind B (lat2 (cellJ c s (j + 1)) s) = 0 := by
        simp [ind, (latO (j + 1) (by omega) (by omega)).2]
      have i4 : ind B (front (cellJ c s j) s) = 1 := by simp [ind, hfB]
      omega
    · exact (huB _ hfB).1 (by rw [back_cellJ_succ])
  -- At an even interior cell, both lateral sides or neither.
  have pair : ∀ j ≤ k, j % 2 = 0 → 1 ≤ j →
      (lat1 (cellJ c s j) s ∈ B ↔ lat2 (cellJ c s j) s ∈ B) := by
    intro j hj he h1
    obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
    have hev := heven _ (hcell (m + 1) (by omega))
    rw [sidesIn_frame B _ s, back_cellJ_succ] at hev
    have i1 : ind B (front (cellJ c s m) s) = 0 := by simp [ind, frO m (by omega) (by omega)]
    have i2 : ind B (front (cellJ c s (m + 1)) s) = 0 := by
      simp [ind, frE (m + 1) hj he]
    rw [i1, i2] at hev
    by_cases h1 : lat1 (cellJ c s (m + 1)) s ∈ B <;> by_cases h2 : lat2 (cellJ c s (m + 1)) s ∈ B <;>
      simp [ind, h1, h2] at hev ⊢
  set J := (Finset.range (k + 1)).filter (fun j => j % 2 = 0 ∧ 1 ≤ j ∧ lat1 (cellJ c s j) s ∈ B)
  have memJ : ∀ j, j ∈ J ↔ j ≤ k ∧ j % 2 = 0 ∧ 1 ≤ j ∧ lat1 (cellJ c s j) s ∈ B := by
    intro j; simp only [J, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨a, b, c, d⟩; exact ⟨by omega, b, c, d⟩
    · rintro ⟨a, b, c, d⟩; exact ⟨by omega, b, c, d⟩
  set T := J.biUnion (fun j => Tsw c s (j - 1))
  have hTev : ∀ x, sidesIn T x % 2 = 0 :=
    sidesIn_biUnion_even J (fun j => Tsw c s (j - 1))
      (fun i hi j hj hij => by
        obtain ⟨_, a1, a2, _⟩ := (memJ i).1 hi
        obtain ⟨_, b1, b2, _⟩ := (memJ j).1 hj
        exact Tsw_disj c s (by omega) (by omega) (by omega))
      (fun j _ x => Tsw_even c s (j - 1) x)
  refine ⟨symmDiff B T, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [sidesIn_symmDiff]
    have := heven x hx
    have := hTev x
    omega
  · intro e he
    rcases Finset.mem_symmDiff.1 he with ⟨heB, heT⟩ | ⟨heT, heB⟩
    · by_cases hs : ∃ m ≤ k + 1, e ∈ cellE (cellJ c s m)
      · obtain ⟨m, hm, hem⟩ := hs
        rw [cellE_frame _ s] at hem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hem
        rcases hem with rfl | rfl | rfl | rfl
        · rcases m with _ | m
          · exact absurd (by rw [cellJ_zero]; rw [cellE_frame _ s]; simp) (h0 _ heB)
          · rw [back_cellJ_succ] at heB ⊢
            rcases Nat.mod_two_eq_zero_or_one m with he' | ho
            · exact absurd heB (frE m (by omega) he')
            · exact absurd heB (frO m (by omega) ho)
        · rcases (show m ≤ k ∨ m = k + 1 by omega) with hm' | rfl
          · rcases Nat.mod_two_eq_zero_or_one m with he' | ho
            · exact absurd heB (frE m hm' he')
            · exact absurd heB (frO m hm' ho)
          · exact absurd rfl (huB _ heB).2
        · rcases Nat.mod_two_eq_zero_or_one m with he' | ho
          · rcases m with _ | m
            · exact absurd (by have h := lat1_mem_self c s 0; rw [cellJ_zero] at h ⊢; exact h) (h0 _ heB)
            · rcases (show m + 1 ≤ k ∨ m + 1 = k + 1 by omega) with hm' | hm'
              · exact absurd (Finset.mem_biUnion.2 ⟨m + 1, (memJ (m + 1)).2 ⟨hm', he', by omega, heB⟩,
                  by simp [Tsw]⟩) heT
              · omega
          · rcases (show m ≤ k ∨ m = k + 1 by omega) with hm' | rfl
            · exact absurd heB (latO m hm' ho).1
            · exact (lat1_after hk hpat (j := k + 1) le_rfl).not.2 (by omega)
        · rcases Nat.mod_two_eq_zero_or_one m with he' | ho
          · rcases m with _ | m
            · exact absurd (by have h := lat2_mem_self c s 0; rw [cellJ_zero] at h ⊢; exact h) (h0 _ heB)
            · rcases (show m + 1 ≤ k ∨ m + 1 = k + 1 by omega) with hm' | hm'
              · exact absurd (Finset.mem_biUnion.2 ⟨m + 1,
                  (memJ (m + 1)).2 ⟨hm', he', by omega, (pair (m + 1) hm' he' (by omega)).2 heB⟩,
                  by simp [Tsw]⟩) heT
              · omega
          · rcases (show m ≤ k ∨ m = k + 1 by omega) with hm' | rfl
            · exact absurd heB (latO m hm' ho).2
            · exact (lat2_after hk hpat (j := k + 1) le_rfl).not.2 (by omega)
      · push Not at hs
        intro hF'
        apply hlight e heB (hs (k + 1) le_rfl)
        have := (mem_after e).1 hF'
        rw [nOn_zero c s (fun m hm => hs m (by omega))] at this
        simpa using this
    · obtain ⟨j, hj, heT'⟩ := Finset.mem_biUnion.1 heT
      obtain ⟨hjk, hje, hj1, hjB⟩ := (memJ j).1 hj
      obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      simp only [Nat.add_sub_cancel, Tsw, Finset.mem_insert, Finset.mem_singleton] at heT'
      rcases heT' with rfl | rfl | rfl | rfl | rfl | rfl
      · intro h; have := (lat1_after hk hpat (j := i) (by omega)).1 h; omega
      · intro h; have := (lat2_after hk hpat (j := i) (by omega)).1 h; omega
      · exact absurd hjB heB
      · exact absurd ((pair (i + 1) hjk hje hj1).1 hjB) heB
      · -- outer sides of odd cells are light and unchanged
        intro hO
        have hO' := (mem_after _).1 hO
        rw [nOn_zero c s (fun m _ => outer1_not_mem c s i m)] at hO'
        simp only [Nat.zero_mod, iff_true] at hO'
        obtain ⟨_, _, f1V, _⟩ := isCell_corners (hcell i (by omega)) s
        have d1 := deg_front1 (cellJ c s i) s F
        rw [hF.2 _ f1V, nb_cellJ] at d1
        have a1 : ind F (lat1 (cellJ c s i) s) = 1 := by
          simp [ind, (hpat.2.1 i (by omega)).1.2 (by omega)]
        have a2 : ind F (front (cellJ c s i) s) = 1 := by
          have q : i + 1 < k + 2 := by omega
          simp [ind, (hpat.2.2 i (by omega)).2 (by simp [q]; omega)]
        have a3 : ind F (outer1 (cellJ c s i) s) = 1 := by simp [ind, hO']
        have := ind_le_one F (lat1 (cellJ c s (i + 1)) s)
        omega
      · intro hO
        have hO' := (mem_after _).1 hO
        rw [nOn_zero c s (fun m _ => outer2_not_mem c s i m)] at hO'
        simp only [Nat.zero_mod, iff_true] at hO'
        obtain ⟨_, _, _, f2V⟩ := isCell_corners (hcell i (by omega)) s
        have d2 := deg_front2 (cellJ c s i) s F
        rw [hF.2 _ f2V, nb_cellJ] at d2
        have a1 : ind F (lat2 (cellJ c s i) s) = 1 := by
          simp [ind, (hpat.2.1 i (by omega)).2.2 (by omega)]
        have a2 : ind F (front (cellJ c s i) s) = 1 := by
          have q : i + 1 < k + 2 := by omega
          simp [ind, (hpat.2.2 i (by omega)).2 (by simp [q]; omega)]
        have a3 : ind F (outer2 (cellJ c s i) s) = 1 := by simp [ind, hO']
        have := ind_le_one F (lat2 (cellJ c s (i + 1)) s)
        omega
  · intro e he
    rcases Finset.mem_symmDiff.1 he with ⟨heB, _⟩ | ⟨heT, _⟩
    · exact ⟨h0 e heB, hu e heB⟩
    · obtain ⟨j, hj, heT'⟩ := Finset.mem_biUnion.1 heT
      obtain ⟨hjk, hje, hj1, _⟩ := (memJ j).1 hj
      obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      have z1 := lat1_not_mem c s (j := i) (m := 0) (by omega)
      have z2 := lat2_not_mem c s (j := i) (m := 0) (by omega)
      have z3 := lat1_not_mem c s (j := i + 1) (m := 0) (by omega)
      have z4 := lat2_not_mem c s (j := i + 1) (m := 0) (by omega)
      have z5 := outer1_not_mem c s i 0
      have z6 := outer2_not_mem c s i 0
      rw [cellJ_zero] at z1 z2 z3 z4 z5 z6
      simp only [Nat.add_sub_cancel, Tsw, Finset.mem_insert, Finset.mem_singleton] at heT'
      rcases heT' with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨z1, fun h => absurd h (lat1_not_mem c s (by omega))⟩
      · exact ⟨z2, fun h => absurd h (lat2_not_mem c s (by omega))⟩
      · exact ⟨z3, fun h => absurd h (lat1_not_mem c s (by omega))⟩
      · exact ⟨z4, fun h => absurd h (lat2_not_mem c s (by omega))⟩
      · exact ⟨z5, fun h => absurd h (outer1_not_mem c s i (k + 1))⟩
      · exact ⟨z6, fun h => absurd h (outer2_not_mem c s i (k + 1))⟩
  · intro e he
    have : e ∉ T := fun h => by
      obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.1 h
      exact he (j - 1) hj
    rw [Finset.mem_symmDiff]
    tauto

theorem reroute_back_rung {B : Finset Edge} (heven : ∀ x, IsCell V x → sidesIn B x % 2 = 0)
    (hlight : ∀ e ∈ B, e ∉ flipCol F c s (k + 2)) (h0 : ∀ e ∈ B, e ∉ cellE c)
    (hu : ∀ e ∈ B, e ∈ cellE (cellJ c s (k + 1)) →
      e = lat1 (cellJ c s (k + 1)) s ∨ e = lat2 (cellJ c s (k + 1)) s) :
    ∃ B' : Finset Edge, (∀ x, IsCell V x → sidesIn B' x % 2 = 0) ∧
      (∀ e ∈ B', e ∉ F ∨ e = lat1 (cellJ c s (k + 1)) s ∨ e = lat2 (cellJ c s (k + 1)) s) ∧
      (∀ e ∈ B', e ∉ cellE c ∧ (e ∈ cellE (cellJ c s (k + 1)) →
        e = lat1 (cellJ c s (k + 1)) s ∨ e = lat2 (cellJ c s (k + 1)) s)) ∧
      (∀ e, (∀ j, e ∉ Tsw c s j) → (e ∈ B' ↔ e ∈ B)) := by
  set F' := flipCol F c s (k + 2)
  have hfu : ∀ e ∈ B, e ≠ front (cellJ c s (k + 1)) s := by
    intro e he h
    subst h
    have hf : front (cellJ c s (k + 1)) s ∈ cellE (cellJ c s (k + 1)) := by rw [cellE_frame _ s]; simp
    have nb1 : front (cellJ c s (k + 1)) s ≠ lat1 (cellJ c s (k + 1)) s ∧
        front (cellJ c s (k + 1)) s ≠ lat2 (cellJ c s (k + 1)) s := by
      generalize cellJ c s (k + 1) = r; obtain ⟨x, y⟩ := r
      cases s <;> simp [front, lat1, lat2, sideEdge, bot, top, lft, rgt]
    rcases hu _ he hf with h | h
    · exact nb1.1 h
    · exact nb1.2 h
  -- Even cells' lateral sides and interior fronts are dark in `F'`; fronts are unchanged.
  have latE : ∀ j ≤ k + 1, j % 2 = 0 → lat1 (cellJ c s j) s ∉ B ∧ lat2 (cellJ c s j) s ∉ B :=
    fun j hj he => ⟨fun h => hlight _ h ((lat1_after hk hpat hj).2 he),
      fun h => hlight _ h ((lat2_after hk hpat hj).2 he)⟩
  have frO : ∀ j ≤ k, j % 2 = 1 → front (cellJ c s j) s ∉ B :=
    fun j hj ho h => hlight _ h ((front_after hk hpat hj).2 ho)
  -- Interior fronts of even cells are not in `B` (parity at the even cell).
  have frE : ∀ j ≤ k, j % 2 = 0 → front (cellJ c s j) s ∉ B := by
    intro j hj he hfB
    rcases j with _ | j
    · exact h0 _ hfB (by have h := front_mem_self c s 0; rw [cellJ_zero] at h ⊢; exact h)
    · have hev := heven _ (hcell (j + 1) (by omega))
      rw [sidesIn_frame B _ s, back_cellJ_succ] at hev
      have i1 : ind B (front (cellJ c s j) s) = 0 := by
        simp [ind, frO j (by omega) (by omega)]
      have i2 : ind B (lat1 (cellJ c s (j + 1)) s) = 0 := by
        simp [ind, (latE (j + 1) (by omega) he).1]
      have i3 : ind B (lat2 (cellJ c s (j + 1)) s) = 0 := by
        simp [ind, (latE (j + 1) (by omega) he).2]
      have i4 : ind B (front (cellJ c s (j + 1)) s) = 1 := by simp [ind, hfB]
      omega
  -- At an odd cell, both lateral sides or neither.
  have pair : ∀ j ≤ k, j % 2 = 1 →
      (lat1 (cellJ c s j) s ∈ B ↔ lat2 (cellJ c s j) s ∈ B) := by
    intro j hj ho
    obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
    have hev := heven _ (hcell (m + 1) (by omega))
    rw [sidesIn_frame B _ s, back_cellJ_succ] at hev
    have i1 : ind B (front (cellJ c s m) s) = 0 := by simp [ind, frE m (by omega) (by omega)]
    have i2 : ind B (front (cellJ c s (m + 1)) s) = 0 := by simp [ind, frO (m + 1) hj ho]
    rw [i1, i2] at hev
    by_cases h1 : lat1 (cellJ c s (m + 1)) s ∈ B <;> by_cases h2 : lat2 (cellJ c s (m + 1)) s ∈ B <;>
      simp [ind, h1, h2] at hev ⊢
  set J := (Finset.range (k + 1)).filter (fun j => j % 2 = 1 ∧ lat1 (cellJ c s j) s ∈ B)
  set T := J.biUnion (Tsw c s)
  have memJ : ∀ j, j ∈ J ↔ j ≤ k ∧ j % 2 = 1 ∧ lat1 (cellJ c s j) s ∈ B := by
    intro j; simp only [J, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨a, b, c⟩; exact ⟨by omega, b, c⟩
    · rintro ⟨a, b, c⟩; exact ⟨by omega, b, c⟩
  have hTev : ∀ x, sidesIn T x % 2 = 0 :=
    sidesIn_biUnion_even J (Tsw c s)
      (fun i hi j hj hij => Tsw_disj c s ((memJ i).1 hi).2.1 ((memJ j).1 hj).2.1 hij)
      (fun j _ x => Tsw_even c s j x)
  refine ⟨symmDiff B T, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [sidesIn_symmDiff]
    have := heven x hx
    have := hTev x
    omega
  · intro e he
    by_cases hl : e = lat1 (cellJ c s (k + 1)) s ∨ e = lat2 (cellJ c s (k + 1)) s
    · exact Or.inr hl
    left
    rcases Finset.mem_symmDiff.1 he with ⟨heB, heT⟩ | ⟨heT, heB⟩
    · -- In `B` and not swapped: an unchanged side.
      by_cases hs : ∃ m ≤ k + 1, e ∈ cellE (cellJ c s m)
      · obtain ⟨m, hm, hem⟩ := hs
        rw [cellE_frame _ s] at hem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hem
        rcases hem with rfl | rfl | rfl | rfl
        · -- a back side: the front of the cell before
          rcases m with _ | m
          · exact absurd (by rw [cellJ_zero]; rw [cellE_frame _ s]; simp) (h0 _ heB)
          · rw [back_cellJ_succ] at heB ⊢
            intro hF'
            have hm' : m ≤ k := by omega
            have e1 := (front_after hk hpat hm')
            have e2 := hpat.2.2 m (by omega)
            have q : m + 1 < k + 2 := by omega
            simp only [q, iff_true] at e2
            exact hlight _ heB (e1.2 (e2.1 hF'))
        · rcases (show m ≤ k ∨ m = k + 1 by omega) with hm' | rfl
          · intro hF'
            have e1 := (front_after hk hpat hm')
            have e2 := hpat.2.2 m (by omega)
            have q : m + 1 < k + 2 := by omega
            simp only [q, iff_true] at e2
            exact hlight _ heB (e1.2 (e2.1 hF'))
          · exact absurd rfl (hfu _ heB)
        · rcases Nat.mod_two_eq_zero_or_one m with he' | ho
          · exact absurd heB (latE m hm he').1
          · rcases (show m ≤ k ∨ m = k + 1 by omega) with hm' | rfl
            · exact absurd (Finset.mem_biUnion.2 ⟨m, (memJ m).2 ⟨hm', ho, heB⟩, by simp [Tsw]⟩) heT
            · exact absurd (Or.inl rfl) hl
        · rcases Nat.mod_two_eq_zero_or_one m with he' | ho
          · exact absurd heB (latE m hm he').2
          · rcases (show m ≤ k ∨ m = k + 1 by omega) with hm' | rfl
            · exact absurd (Finset.mem_biUnion.2 ⟨m, (memJ m).2 ⟨hm', ho, (pair m hm' ho).2 heB⟩,
                by simp [Tsw]⟩) heT
            · exact absurd (Or.inr rfl) hl
      · push Not at hs
        intro hF'
        apply hlight e heB
        rw [mem_after, nOn_zero c s (fun m hm => hs m (by omega))]
        simp [hF']
    · -- Swapped in: a lateral side of an even cell, or an outer side.
      obtain ⟨j, hj, heT'⟩ := Finset.mem_biUnion.1 heT
      obtain ⟨hjk, hjo, hjB⟩ := (memJ j).1 hj
      have hjk' : j + 1 ≤ k := by omega
      simp only [Tsw, Finset.mem_insert, Finset.mem_singleton] at heT'
      rcases heT' with rfl | rfl | rfl | rfl | rfl | rfl
      · exact absurd hjB heB
      · exact absurd ((pair j hjk hjo).1 hjB) heB
      · intro h; have := (hpat.2.1 (j + 1) (by omega)).1.1 h; omega
      · intro h; have := (hpat.2.1 (j + 1) (by omega)).2.1 h; omega
      · -- degree count at `front1 c_j`
        intro hO
        obtain ⟨_, _, f1V, _⟩ := isCell_corners (hcell j (by omega)) s
        have d1 := deg_front1 (cellJ c s j) s F
        rw [hF.2 _ f1V, nb_cellJ] at d1
        have a1 : ind F (lat1 (cellJ c s j) s) = 1 := by
          simp [ind, (hpat.2.1 j (by omega)).1.2 hjo]
        have a2 : ind F (front (cellJ c s j) s) = 1 := by
          have q : j + 1 < k + 2 := by omega
          simp [ind, (hpat.2.2 j (by omega)).2 (by simp [q]; exact hjo)]
        have a3 : ind F (outer1 (cellJ c s j) s) = 1 := by simp [ind, hO]
        have := ind_le_one F (lat1 (cellJ c s (j + 1)) s)
        omega
      · intro hO
        obtain ⟨_, _, _, f2V⟩ := isCell_corners (hcell j (by omega)) s
        have d2 := deg_front2 (cellJ c s j) s F
        rw [hF.2 _ f2V, nb_cellJ] at d2
        have a1 : ind F (lat2 (cellJ c s j) s) = 1 := by
          simp [ind, (hpat.2.1 j (by omega)).2.2 hjo]
        have a2 : ind F (front (cellJ c s j) s) = 1 := by
          have q : j + 1 < k + 2 := by omega
          simp [ind, (hpat.2.2 j (by omega)).2 (by simp [q]; exact hjo)]
        have a3 : ind F (outer2 (cellJ c s j) s) = 1 := by simp [ind, hO]
        have := ind_le_one F (lat2 (cellJ c s (j + 1)) s)
        omega
  · intro e he
    rcases Finset.mem_symmDiff.1 he with ⟨heB, _⟩ | ⟨heT, _⟩
    · exact ⟨h0 e heB, hu e heB⟩
    · obtain ⟨j, hj, heT'⟩ := Finset.mem_biUnion.1 heT
      obtain ⟨hjk, hjo, _⟩ := (memJ j).1 hj
      have z1 := lat1_not_mem c s (j := j) (m := 0) (by omega)
      have z2 := lat2_not_mem c s (j := j) (m := 0) (by omega)
      have z3 := lat1_not_mem c s (j := j + 1) (m := 0) (by omega)
      have z4 := lat2_not_mem c s (j := j + 1) (m := 0) (by omega)
      have z5 := outer1_not_mem c s j 0
      have z6 := outer2_not_mem c s j 0
      rw [cellJ_zero] at z1 z2 z3 z4 z5 z6
      simp only [Tsw, Finset.mem_insert, Finset.mem_singleton] at heT'
      rcases heT' with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨z1, fun h => absurd h (lat1_not_mem c s (by omega))⟩
      · exact ⟨z2, fun h => absurd h (lat2_not_mem c s (by omega))⟩
      · exact ⟨z3, fun h => absurd h (lat1_not_mem c s (by omega))⟩
      · exact ⟨z4, fun h => absurd h (lat2_not_mem c s (by omega))⟩
      · exact ⟨z5, fun h => absurd h (outer1_not_mem c s j (k + 1))⟩
      · exact ⟨z6, fun h => absurd h (outer2_not_mem c s j (k + 1))⟩
  · intro e he
    have : e ∉ T := fun h => by
      obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.1 h
      exact he j hj
    rw [Finset.mem_symmDiff]
    tauto

end reroute

end SolidGridHam
