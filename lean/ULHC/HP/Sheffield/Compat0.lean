/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.HP.Sheffield.Reduce

/-!
# Lemma 4 infrastructure

* `plan_getElem`: the plan's operation at index `k` lowers or re-flips the bridge at `k`, as
  decided by `lowAt`.
* `tog_side`: a toggled side of a strip cell is a lateral, the start's back, or the last front
  (inner fronts are sides of two strip cells and are not toggled).
-/

namespace ULHC

namespace HP

open Finset Classical

def lowJ (b : Bridge) : Join := ⟨b.q, b.a, b.r - 1⟩

def undoJ (b : Bridge) : Join := ⟨b.E, b.a, 1⟩

lemma plan_eq (H : Finset Edge) : ∀ (BS : List Bridge) (uv : Pt × Pt),
    plan H BS uv = List.zipWith (fun b e => if e.1 then lowJ b else undoJ b) BS (planA H BS uv)
  | [], _ => rfl
  | b :: BS, uv => by
    simp only [plan, planA]
    split_ifs
    · simp only [List.zipWith_cons_cons, ↓reduceIte, lowJ]
      rw [plan_eq]; rfl
    · simp only [List.zipWith_cons_cons, Bool.false_eq_true, ↓reduceIte]
      rw [plan_eq]; rfl

lemma plan_length (H : Finset Edge) (BS : List Bridge) (uv : Pt × Pt) :
    (plan H BS uv).length = BS.length := by
  rw [plan_eq]; simp [planA_length]

lemma plan_getElem (H : Finset Edge) (BS : List Bridge) (uv : Pt × Pt) {k : ℕ}
    (hk : k < BS.length) :
    (plan H BS uv)[k]'(by rw [plan_length]; exact hk) =
      if lowAt H BS uv k then lowJ (BS[k]'hk) else undoJ (BS[k]'hk) := by
  have hl : k < (planA H BS uv).length := by rw [planA_length]; exact hk
  simp only [plan_eq, List.getElem_zipWith, lowAt]
  simp only [List.getD_eq_getElem _ _ hl]

-- A toggled edge is a side of some strip cell.
--
lemma tog_cell {o : Join} {e : Edge} (h : o.tog e) : ∃ j < o.n, e ∈ cellE (cellJ o.c o.a j) := by
  unfold Join.tog nOn at h
  by_contra hn
  push Not at hn
  have : ((Finset.range o.n).filter (fun j => e ∈ cellE (cellJ o.c o.a j))) = ∅ := by
    ext j; simp only [Finset.mem_filter, Finset.mem_range, Finset.notMem_empty, iff_false,
      not_and]
    exact fun hj => hn j hj
  rw [this] at h; simp at h

-- **Toggled sides.**
--
lemma tog_side {o : Join} {e : Edge} (h : o.tog e) {j : ℕ} (hj : j < o.n)
    (he : e ∈ cellE (cellJ o.c o.a j)) :
    e = lat1 (cellJ o.c o.a j) o.a ∨ e = lat2 (cellJ o.c o.a j) o.a ∨
      (j = 0 ∧ e = back o.c o.a) ∨ (j + 1 = o.n ∧ e = front (cellJ o.c o.a j) o.a) := by
  rw [cellE_frame _ o.a] at he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl
  · -- the back of cell `j`
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · subst h0; rw [cellJ_zero]; exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
    · exfalso
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      unfold Join.tog at h
      rw [back_cellJ_succ, nOn_eq o.c o.a o.n _ {j', j' + 1}] at h
      · simp at h
      · intro m hm
        simp only [Finset.mem_insert, Finset.mem_singleton]
        constructor
        · intro hmem
          by_contra hne; push Not at hne
          exact front_not_mem o.c o.a (j := j') (m := m) (Ne.symm hne.1) hne.2 hmem
        · rintro (rfl | rfl)
          · exact front_mem_self o.c o.a _
          · exact front_mem_next o.c o.a _
      · intro m hm; simp only [Finset.mem_insert, Finset.mem_singleton] at hm; omega
  · -- the front of cell `j`
    by_cases hl : j + 1 = o.n
    · exact Or.inr (Or.inr (Or.inr ⟨hl, rfl⟩))
    · exfalso
      unfold Join.tog at h
      rw [nOn_eq o.c o.a o.n _ {j, j + 1}] at h
      · simp at h
      · intro m hm
        simp only [Finset.mem_insert, Finset.mem_singleton]
        constructor
        · intro hmem
          by_contra hne; push Not at hne
          exact front_not_mem o.c o.a (j := j) (m := m) (Ne.symm hne.1) hne.2 hmem
        · rintro (rfl | rfl)
          · exact front_mem_self o.c o.a _
          · exact front_mem_next o.c o.a _
      · intro m hm; simp only [Finset.mem_insert, Finset.mem_singleton] at hm; omega
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)

section pats

variable {H : Finset Edge}

-- The lowering of a frozen bridge is an intact odd strip.
--
lemma lowJ_pat {b : Bridge} (hR : RegionOK H b) (htwo : 2 ≤ b.r) (hev : b.r % 2 = 0) :
    StripPat H (lowJ b).c (lowJ b).a (lowJ b).n := by
  obtain ⟨q, a, r⟩ := b
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 2 := ⟨r - 2, by simp only at htwo; omega⟩
  obtain ⟨bk, lat, lat0, _, fr, frA, _, _, _, _, _⟩ := hR
  simp only [lowJ, Bridge.cell, Bridge.E, show m + 2 - 1 = m + 1 by omega,
    show m + 2 - 2 = m by omega] at *
  have meven : m % 2 = 0 := by omega
  refine ⟨bk, fun j hj => ?_, fun j hj => ?_⟩
  · rcases Nat.eq_zero_or_pos j with h0 | hpos
    · subst h0; rw [cellJ_zero]
      exact ⟨⟨fun h => absurd h lat0.1, fun h => by omega⟩, ⟨fun h => absurd h lat0.2, fun h => by omega⟩⟩
    · exact lat j hpos (by omega)
  · rcases (show j + 3 ≤ m + 2 ∨ j = m by omega) with h | rfl
    · rw [fr j h]; omega
    · exact ⟨fun _ => by omega, fun _ => frA⟩

-- The re-flip of a frozen bridge's `E` is an intact strip of one cell.
--
lemma undoJ_pat {b : Bridge} (hR : RegionOK H b) (htwo : 2 ≤ b.r) :
    StripPat H (undoJ b).c (undoJ b).a (undoJ b).n := by
  have bE : back b.E b.a ∈ H := by
    have := hR.frA
    unfold Bridge.E Bridge.cell at *
    rw [show b.r - 1 = b.r - 2 + 1 by omega, back_cellJ_succ]; exact this
  refine ⟨bE, fun j hj => ?_, fun j hj => ?_⟩
  · obtain rfl : j = 0 := by simp [undoJ] at hj; omega
    simp only [undoJ, cellJ_zero]
    exact ⟨⟨fun h => absurd h hR.latE.1, fun h => by omega⟩, ⟨fun h => absurd h hR.latE.2, fun h => by omega⟩⟩
  · obtain rfl : j = 0 := by simp [undoJ] at hj; omega
    simp only [undoJ, cellJ_zero]
    exact ⟨fun _ => by omega, fun _ => hR.frE⟩

end pats

-- A side of a cell is `sideEdge` of that cell.
--
lemma cellE_side {Y : Pt} {e : Edge} (h : e ∈ cellE Y) : ∃ s, e = sideEdge Y s := by
  unfold cellE at h
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with rfl | rfl | rfl | rfl
  · exact ⟨.b, rfl⟩
  · exact ⟨.t, rfl⟩
  · exact ⟨.l, rfl⟩
  · exact ⟨.r, rfl⟩

-- **II.2.** The flipped square of a newer bridge shares no side with a square of an older one.
--
lemma notZ_shared {b1 b2 : Bridge} (hz : NotZ b1 b2) {j : ℕ} (hj : j < b2.r) {e : Edge}
    (he : e ∈ cellE (b2.cell j)) : e ∉ cellE b1.E := by
  obtain ⟨s', rfl⟩ := cellE_side he
  rw [sideEdge_mem_cellE]
  obtain ⟨hcol, hm1, hside⟩ := hz
  rintro (h | h)
  · exact hcol j (by omega) h
  · rcases side_cases b2.a s' with rfl | rfl | rfl | rfl
    · apply hcol (j + 1) (by omega); rw [h]; unfold Bridge.cell; rw [nb_cellJ]
    · rcases Nat.eq_zero_or_pos j with h0 | hpos
      · subst h0; apply hm1; rw [h]; unfold Bridge.cell; rw [cellJ_zero]
      · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        apply hcol j' (by omega); rw [h]; unfold Bridge.cell; rw [nb_cellJ_opp]
    · exact (hside j (by omega)).1 h
    · exact (hside j (by omega)).2 h

end HP

end ULHC
