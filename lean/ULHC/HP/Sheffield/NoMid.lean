/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.HP.Sheffield.Assemble

/-!
# Lemma I.7: pair points are not interior points of other operations

An interior point of a strip (a front corner of an odd, non-last strip square) is a corner of four
cells: two strip squares and two squares beside them. A cell of another operation with that corner
is beside the strip (C1) and shares a toggled lateral with it, against (C2) in either order.
-/

namespace ULHC

namespace HP

open Finset Classical

lemma cells_at_front1 (X : Pt) (a : Side) {Y : Pt} (hY : IsCorner (front1 X a) Y) :
    Y = X ∨ Y = nb X a ∨ Y = nb X (latA a) ∨ Y = nb (nb X a) (latA a) := by
  obtain ⟨x, y⟩ := X; obtain ⟨u, w⟩ := Y
  cases a <;> simp only [IsCorner, front1, nb, latA, Prod.mk.injEq] at hY ⊢ <;> omega

lemma cells_at_front2 (X : Pt) (a : Side) {Y : Pt} (hY : IsCorner (front2 X a) Y) :
    Y = X ∨ Y = nb X a ∨ Y = nb X (latB a) ∨ Y = nb (nb X a) (latB a) := by
  obtain ⟨x, y⟩ := X; obtain ⟨u, w⟩ := Y
  cases a <;> simp only [IsCorner, front2, nb, latB, Prod.mk.injEq] at hY ⊢ <;> omega

lemma tog_lat1 {O : Join} {j : ℕ} (hj : j < O.n) : O.tog (lat1 (cellJ O.c O.a j) O.a) := by
  unfold Join.tog; rw [nOn_lat1 _ _ hj]

lemma tog_lat2 {O : Join} {j : ℕ} (hj : j < O.n) : O.tog (lat2 (cellJ O.c O.a j) O.a) := by
  unfold Join.tog; rw [nOn_lat2 _ _ hj]

-- A side of a strip's first cell, on no later strip cell, is toggled.
--
lemma tog_first {O : Join} {e : Edge} (hn : 1 ≤ O.n) (he : e ∈ cellE O.c)
    (hother : ∀ j < O.n, 1 ≤ j → e ∉ cellE (cellJ O.c O.a j)) : O.tog e := by
  unfold Join.tog
  rw [nOn_eq O.c O.a O.n e {0}]
  · simp
  · intro j hj
    simp only [Finset.mem_singleton]
    constructor
    · intro h; by_contra hne; exact hother j hj (by omega) h
    · rintro rfl; rw [cellJ_zero]; exact he
  · intro j hj; simp at hj; omega

-- The shared lateral argument: a cell of `O'` beside a strip square `Z` of `O`, across `Z`'s
-- lateral `e`, contradicts (C1)/(C2).
--
lemma beside_contra {O O' : Join} (hn' : 1 ≤ O'.n)
    (hc1 : ∀ j < O.n, ∀ j' < O'.n, cellJ O.c O.a j ≠ cellJ O'.c O'.a j')
    (hc2 : (∀ j' < O'.n, ∀ e ∈ cellE (cellJ O'.c O'.a j'), ¬ O.tog e) ∨
      (∀ j < O.n, ∀ e ∈ cellE (cellJ O.c O.a j), ¬ O'.tog e))
    {k : ℕ} (hk : k < O.n) {ℓ : Side} (hℓ : ℓ = latA O.a ∨ ℓ = latB O.a)
    (hY : O'.c = nb (cellJ O.c O.a k) ℓ) : False := by
  set Z := cellJ O.c O.a k with hZ
  have hez : sideEdge Z ℓ ∈ cellE Z := by rw [sideEdge_mem_cellE]; left; rfl
  have hey : sideEdge Z ℓ ∈ cellE O'.c := by rw [hY, sideEdge_mem_cellE]; right; rfl
  have htogO : O.tog (sideEdge Z ℓ) := by
    rcases hℓ with rfl | rfl
    · rw [← lat1_eq]; exact tog_lat1 hk
    · rw [← lat2_eq]; exact tog_lat2 hk
  rcases hc2 with h | h
  · exact h 0 hn' _ (by rw [cellJ_zero]; exact hey) htogO
  · apply h k hk _ hez
    apply tog_first hn' hey
    intro j hj hj1 hmem
    rw [sideEdge_mem_cellE] at hmem
    rcases hmem with hm | hm
    · exact hc1 k hk j hj hm.symm
    · rw [← hY] at hm
      have := cellJ_inj (c := O'.c) (s := O'.a) (i := j) (j := 0) (by rw [hm, cellJ_zero])
      omega

-- **Lemma I.7.**
--
theorem noMid {O O' : Join} (hn' : 1 ≤ O'.n)
    (hc1 : ∀ j < O.n, ∀ j' < O'.n, cellJ O.c O.a j ≠ cellJ O'.c O'.a j')
    (hc2 : (∀ j' < O'.n, ∀ e ∈ cellE (cellJ O'.c O'.a j'), ¬ O.tog e) ∨
      (∀ j < O.n, ∀ e ∈ cellE (cellJ O.c O.a j), ¬ O'.tog e))
    {z : Pt} (hz : IsCorner z O'.c) : ¬ IsMid O.c O.a (O.n - 1) z := by
  rintro ⟨j, _, hjl, hz' | hz'⟩
  · rw [hz'] at hz
    rcases cells_at_front1 _ _ hz with h | h | h | h
    · exact hc1 j (by omega) 0 hn' (by rw [cellJ_zero, h])
    · exact hc1 (j + 1) (by omega) 0 hn' (by rw [cellJ_zero, h, nb_cellJ])
    · exact beside_contra hn' hc1 hc2 (k := j) (by omega) (Or.inl rfl) h
    · exact beside_contra hn' hc1 hc2 (k := j + 1) (by omega) (Or.inl rfl) (by rw [h, nb_cellJ])
  · rw [hz'] at hz
    rcases cells_at_front2 _ _ hz with h | h | h | h
    · exact hc1 j (by omega) 0 hn' (by rw [cellJ_zero, h])
    · exact hc1 (j + 1) (by omega) 0 hn' (by rw [cellJ_zero, h, nb_cellJ])
    · exact beside_contra hn' hc1 hc2 (k := j) (by omega) (Or.inr rfl) h
    · exact beside_contra hn' hc1 hc2 (k := j + 1) (by omega) (Or.inr rfl) (by rw [h, nb_cellJ])

-- A strip's own pair points are not its interior points.
--
lemma noMid_self (O : Join) {z : Pt} (hz : z = back1 O.c O.a ∨ z = front1 O.c O.a) :
    ¬ IsMid O.c O.a (O.n - 1) z := by
  obtain ⟨⟨x, y⟩, a, n⟩ := O
  rintro ⟨j, hjo, _, hz' | hz'⟩ <;> rcases hz with rfl | rfl <;> cases a <;>
    simp [back1, front1, front2, cellJ, Prod.ext_iff] at hz' <;> omega

end HP

end ULHC
