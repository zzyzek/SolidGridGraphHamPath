/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.NearGeo

/-!
# Chains of contacts and suffix strips

* `reach_end`: a strip through a cell of `a` runs to `a`'s end cell.
* `side_chain1`, `side_chain2`: a strip beside the body runs against `s` down to the cell beside
  `c_0`, which it meets at an even index.
* `suf z i`: the suffix of `z` from an even index `i`. It is a strip of the same factor with the
  same end cell (`suf_pat`, `suf_end`), and it keeps every link of `z` (`suf_cr2`).
-/

namespace ULHC

open Finset

lemma cellJ_add (z : Pt) (tf : Side) (i j : ℕ) : cellJ (cellJ z tf i) tf j = cellJ z tf (i + j) := by
  obtain ⟨x, y⟩ := z
  cases tf <;> simp only [cellJ, Nat.cast_add] <;> ring_nf

lemma side1_down (c : Pt) (s : Side) (j : ℕ) :
    nb (nb (cellJ c s (j + 1)) (latA s)) s.opp = nb (cellJ c s j) (latA s) := by
  rw [← (nb_comm_lat c s j).1, nb_nb_opp]

lemma side2_down (c : Pt) (s : Side) (j : ℕ) :
    nb (nb (cellJ c s (j + 1)) (latB s)) s.opp = nb (cellJ c s j) (latB s) := by
  rw [← (nb_comm_lat c s j).2, nb_nb_opp]

section chain

variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hF : Deg2 V F) (hT : NoTypeIII V F) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat F c s (k + 2))
  (hsep : ¬ Conn F (back1 c s) (front1 c s))
  {z : Pt} {tf : Side} {m i0 : ℕ} (hz : SigFrom F z tf m i0)

include hk hpat hz in
theorem reach_end : ∀ d i j, j + d = k + 1 → i0 ≤ i → i < m → cellJ z tf i = cellJ c s j →
    ∃ i', i ≤ i' ∧ i' < m ∧ cellJ z tf i' = cellJ c s (k + 1) := by
  intro d
  induction d with
  | zero => intro i j hd h0 hi hq; exact ⟨i, le_rfl, hi, by rw [hq, show j = k + 1 by omega]⟩
  | succ d ih =>
    intro i j hd h0 hi hq
    obtain ⟨ht, _, hi1⟩ := touch_body hpat hz h0 hi (j := j) (by omega) hq
    obtain ⟨i', h1, h2, h3⟩ := ih (i + 1) (j + 1) (by omega) (by omega) hi1 (by
      rw [← nb_cellJ, hq, ht, nb_cellJ])
    exact ⟨i', by omega, h2, h3⟩

include hF hT hk hcell hpat hsep hz in
theorem side_chain1 : ∀ j i, j ≤ k → i0 ≤ i → i < m → cellJ z tf i = nb (cellJ c s j) (latA s) →
    tf = s.opp ∧ ∃ ie, i ≤ ie ∧ ie < m ∧ ie % 2 = 0 ∧ cellJ z tf ie = nb c (latA s) := by
  intro j
  induction j with
  | zero =>
    intro i _ h0 hi hq
    obtain ⟨ht, hp, _⟩ := touch_side1 hF hT hk hcell hpat hsep hz h0 hi (j := 0) (by omega) hq
    exact ⟨ht, i, le_rfl, hi, by omega, by rw [hq, cellJ_zero]⟩
  | succ j ih =>
    intro i hj h0 hi hq
    obtain ⟨ht, _, hi1⟩ := touch_side1 hF hT hk hcell hpat hsep hz h0 hi (j := j + 1) hj hq
    obtain ⟨ht', ie, h1, h2⟩ := ih (i + 1) (by omega) (by omega) hi1 (by
      rw [← nb_cellJ, hq, ht, side1_down])
    exact ⟨ht', ie, by omega, h2⟩

include hF hT hk hcell hpat hsep hz in
theorem side_chain2 : ∀ j i, j ≤ k → i0 ≤ i → i < m → cellJ z tf i = nb (cellJ c s j) (latB s) →
    tf = s.opp ∧ ∃ ie, i ≤ ie ∧ ie < m ∧ ie % 2 = 0 ∧ cellJ z tf ie = nb c (latB s) := by
  intro j
  induction j with
  | zero =>
    intro i _ h0 hi hq
    obtain ⟨ht, hp, _⟩ := touch_side2 hF hT hk hcell hpat hsep hz h0 hi (j := 0) (by omega) hq
    exact ⟨ht, i, le_rfl, hi, by omega, by rw [hq, cellJ_zero]⟩
  | succ j ih =>
    intro i hj h0 hi hq
    obtain ⟨ht, _, hi1⟩ := touch_side2 hF hT hk hcell hpat hsep hz h0 hi (j := j + 1) hj hq
    obtain ⟨ht', ie, h1, h2⟩ := ih (i + 1) (by omega) (by omega) hi1 (by
      rw [← nb_cellJ, hq, ht, side2_down])
    exact ⟨ht', ie, by omega, h2⟩

end chain

section suffix

-- The suffix of `z` from index `i`.
--
def suf (z : StripSpec) (i : ℕ) : StripSpec := ⟨cellJ z.c z.s i, z.s, z.n - i⟩

variable {V : Finset Pt} {F : Finset Edge} {z : StripSpec} {i i0 : ℕ}

lemma suf_cellJ (j : ℕ) : cellJ (suf z i).c (suf z i).s j = cellJ z.c z.s (i + j) :=
  cellJ_add z.c z.s i j

lemma suf_end (hi : i < z.n) : endCell (suf z i) = endCell z := by
  unfold endCell; rw [suf_cellJ]; simp only [suf]; congr 1; omega

lemma suf_pat (hp : StripPat F z.c z.s z.n) (he : i % 2 = 0) (hi : i < z.n) :
    StripPat F (suf z i).c (suf z i).s (suf z i).n := by
  obtain ⟨_, _, gb, _⟩ := strip_sig hp hi
  obtain ⟨_, hl, hf⟩ := hp
  refine ⟨gb.2 he, fun j hj => ?_, fun j hj => ?_⟩
  · simp only [suf] at hj
    rw [suf_cellJ]
    have := hl (i + j) (by omega)
    simp only [suf]; constructor
    · rw [this.1]; omega
    · rw [this.2]; omega
  · simp only [suf] at hj ⊢
    rw [cellJ_add, hf (i + j) (by omega)]
    omega

lemma suf_cells (hc : ∀ j < z.n, IsCell V (cellJ z.c z.s j)) :
    ∀ j < (suf z i).n, IsCell V (cellJ (suf z i).c (suf z i).s j) := by
  intro j hj; rw [suf_cellJ]; simp only [suf] at hj; exact hc _ (by omega)

lemma suf_mid {p : Pt} (he : i % 2 = 0)
    (h : IsMid (suf z i).c (suf z i).s ((suf z i).n - 2) p) : IsMid z.c z.s (z.n - 2) p := by
  obtain ⟨j, hj, hjk, hp⟩ := h
  simp only [suf] at hjk
  refine ⟨i + j, by omega, by omega, ?_⟩
  have := suf_cellJ (z := z) (i := i) j
  simp only [suf] at this hp ⊢
  rw [this] at hp; exact hp

theorem suf_cr2 {G : Finset Edge} {w : StripSpec} (h : CR2 V G z w) (he : i % 2 = 0)
    (hin : i + 2 ≤ z.n) : CR2 V G (suf z i) w := by
  obtain ⟨h2, hev, h1, hp, hc, hso, hne, hen, hm1, hm2, hcg, hcu⟩ := h
  have hend := suf_end (z := z) (i := i) (by omega)
  refine ⟨by simp only [suf]; omega, by simp only [suf]; omega, h1, by rw [hend]; exact hp, hc,
    ?_, by rw [hend]; exact hne, by rw [hend]; exact hen,
    fun hm => hm1 (suf_mid he hm), fun hm => hm2 (suf_mid he hm), hcg, by rw [hend]; exact hcu⟩
  intro j hj i' hi' e he1
  rw [suf_cellJ]
  simp only [suf] at hi'
  exact hso j hj (i + i') (by omega) e he1

lemma suf_valid (hp : StripPat F z.c z.s z.n) (hc : ∀ j < z.n, IsCell V (cellJ z.c z.s j))
    (he : i % 2 = 0) (hi : i < z.n)
    (hsep : ¬ Conn F (back1 (cellJ z.c z.s i) z.s) (front1 (cellJ z.c z.s i) z.s)) :
    ValidStrip V F (suf z i) :=
  ⟨by simp only [suf]; omega, suf_pat hp he hi, suf_cells hc, hsep⟩

lemma suf_patW (hp : SigFrom F z.c z.s z.n i0) (hii : i0 ≤ i) (he : i % 2 = 0) (hi : i < z.n) :
    StripPat F (suf z i).c (suf z i).s (suf z i).n := by
  obtain ⟨_, _, gb, _⟩ := hp i hii hi
  refine ⟨gb.2 he, fun j hj => ?_, fun j hj => ?_⟩
  · simp only [suf] at hj
    rw [suf_cellJ]
    have := hp (i + j) (by omega) (by omega)
    simp only [suf]; constructor
    · rw [this.1]; omega
    · rw [this.2.1]; omega
  · simp only [suf] at hj ⊢
    rw [cellJ_add, (hp (i + j) (by omega) (by omega)).2.2.2]
    omega

lemma suf_validW (hp : SigFrom F z.c z.s z.n i0) (hc : ∀ j < z.n, IsCell V (cellJ z.c z.s j))
    (hii : i0 ≤ i) (he : i % 2 = 0) (hi : i < z.n)
    (hsep : ¬ Conn F (back1 (cellJ z.c z.s i) z.s) (front1 (cellJ z.c z.s i) z.s)) :
    ValidStrip V F (suf z i) :=
  ⟨by simp only [suf]; omega, suf_patW hp hii he hi, suf_cells hc, hsep⟩

end suffix

end ULHC
