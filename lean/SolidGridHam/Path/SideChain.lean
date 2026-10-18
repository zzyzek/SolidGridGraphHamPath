/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import SolidGridHam.Path.MoveInv

/-!
# The chain lemma: side columns become strips

Beside a column `c_0, c_1, …` (direction `s`) lies the side line `S_i = nb c_i (latA s)`. Its sides:
* near side `lat2 S_i = lat1 c_i` (shared with the column);
* far side `lat1 S_i`;
* back and front `outer1 c_(i−1)`, `outer1 c_i` (the edges leaving the column sideways).

**Chain lemma** (`far_chain`). If the outer edges alternate (`outer1 c_(j+r)` dark iff `r` odd) and
the far side at `S_j` is light, degree 2 at the outer vertices `front1 S_(j+r)` forces the far sides to
alternate too: at even `r` two light edges leave one way out, at odd `r` two dark edges fill the
vertex. With the near sides alternating the same way (after a move), the side line is a strip
(`StripRun`).

`StripRun F q a m`: the strip pattern on `q_0 … q_(m−1)` with every front following the inner rule
(dark iff odd), i.e. a strip that has not ended yet.
-/

namespace SolidGridHam

namespace HP

open Finset Classical

def StripRun (F : Finset Edge) (q : Pt) (a : Side) (m : ℕ) : Prop :=
  back q a ∈ F ∧
  (∀ r < m, (lat1 (cellJ q a r) a ∈ F ↔ r % 2 = 1) ∧ (lat2 (cellJ q a r) a ∈ F ↔ r % 2 = 1)) ∧
  (∀ r < m, front (cellJ q a r) a ∈ F ↔ r % 2 = 1)

lemma cellJ_add (q : Pt) (a : Side) (i r : ℕ) : cellJ (cellJ q a i) a r = cellJ q a (i + r) := by
  obtain ⟨x, y⟩ := q
  cases a <;> simp [cellJ] <;> ring_nf

-- **Concatenation.** A run of even length `m`, then a strip from `q_m`, is a strip from `q`.
--
lemma stripPat_append {F : Finset Edge} {q : Pt} {a : Side} {m n : ℕ} (hm : m % 2 = 0)
    (hn : 1 ≤ n) (hr : StripRun F q a m) (hp : StripPat F (cellJ q a m) a n) :
    StripPat F q a (m + n) := by
  obtain ⟨hb, hl, hf⟩ := hr
  obtain ⟨hb', hl', hf'⟩ := hp
  refine ⟨hb, fun r hr' => ?_, fun r hr' => ?_⟩
  · rcases Nat.lt_or_ge r m with h | h
    · exact hl r h
    · obtain ⟨t, rfl⟩ : ∃ t, r = m + t := ⟨r - m, by omega⟩
      have := hl' t (by omega)
      rw [cellJ_add] at this
      constructor <;> [rw [this.1]; rw [this.2]] <;> omega
  · rcases Nat.lt_or_ge r m with h | h
    · rw [hf r h]; omega
    · obtain ⟨t, rfl⟩ : ∃ t, r = m + t := ⟨r - m, by omega⟩
      have := hf' t (by omega)
      rw [cellJ_add] at this
      rw [this]; omega

lemma cellJ_side (c : Pt) (s : Side) (i : ℕ) :
    cellJ (nb c (latA s)) s i = nb (cellJ c s i) (latA s) := by
  obtain ⟨x, y⟩ := c
  cases s <;> simp [cellJ, nb, latA]

lemma cellJ_sideB (c : Pt) (s : Side) (i : ℕ) :
    cellJ (nb c (latB s)) s i = nb (cellJ c s i) (latB s) := by
  obtain ⟨x, y⟩ := c
  cases s <;> simp [cellJ, nb, latB]

lemma latB_eq_opp (s : Side) : latB s = (latA s).opp := by cases s <;> rfl

lemma latA_eq_opp (s : Side) : latA s = (latB s).opp := by cases s <;> rfl

-- Sides of the side square `S_i` in terms of the column.
--
lemma side_front (c : Pt) (s : Side) : front (nb c (latA s)) s = outer1 c s :=
  (outer1_side_nb c s).symm

lemma side_near (c : Pt) (s : Side) : lat2 (nb c (latA s)) s = lat1 c s := by
  rw [lat2_eq, lat1_eq, latB_eq_opp, sideEdge_nb_opp]

lemma sideB_front (c : Pt) (s : Side) : front (nb c (latB s)) s = outer2 c s :=
  (outer2_side_nb c s).symm

lemma sideB_near (c : Pt) (s : Side) : lat1 (nb c (latB s)) s = lat2 c s := by
  rw [lat1_eq, lat2_eq, latA_eq_opp, sideEdge_nb_opp]

lemma nb_side_comm (c : Pt) (s : Side) : nb (nb c (latA s)) s = nb (nb c s) (latA s) := by
  obtain ⟨x, y⟩ := c; cases s <;> simp [nb, latA]

lemma nb_sideB_comm (c : Pt) (s : Side) : nb (nb c (latB s)) s = nb (nb c s) (latB s) := by
  obtain ⟨x, y⟩ := c; cases s <;> simp [nb, latB]

section chain

variable {F : Finset Edge} {c : Pt} {s : Side} {j : ℕ}

-- **Chain lemma, side `latA`.**
--
theorem far_chain (hfar0 : lat1 (nb (cellJ c s j) (latA s)) s ∉ F) :
    ∀ m, (∀ r < m, outer1 (cellJ c s (j + r)) s ∈ F ↔ r % 2 = 1) →
      (∀ r < m, deg F (front1 (nb (cellJ c s (j + r)) (latA s)) s) = 2) →
      (lat1 (nb (cellJ c s (j + m)) (latA s)) s ∈ F ↔ m % 2 = 1)
  | 0, _, _ => by simpa using hfar0
  | m + 1, ho, hd => by
    have ih := far_chain hfar0 m (fun r hr => ho r (by omega)) (fun r hr => hd r (by omega))
    have hdeg := hd m (by omega)
    rw [deg_front1, side_front, nb_side_comm, nb_cellJ, show j + m + 1 = j + (m + 1) by omega]
      at hdeg
    have hom := ho m (by omega)
    rcases Nat.mod_two_eq_zero_or_one m with h | h
    · rw [ind_of_not_mem (fun h' => by have := ih.1 h'; omega),
        ind_of_not_mem (fun h' => by have := hom.1 h'; omega)] at hdeg
      have : ind F (lat1 (nb (cellJ c s (j + (m + 1))) (latA s)) s) = 1 := by
        have := ind_le_one F (lat1 (nb (cellJ c s (j + (m + 1))) (latA s)) s)
        have := ind_le_one F (outer1 (nb (cellJ c s (j + m)) (latA s)) s)
        omega
      constructor
      · intro _; omega
      · intro _; unfold ind at this; split_ifs at this with hh; exact hh
    · rw [ind_of_mem (ih.2 h), ind_of_mem (hom.2 h)] at hdeg
      constructor
      · intro hh; rw [ind_of_mem hh] at hdeg; omega
      · intro hh; omega

-- **Chain lemma, side `latB`.**
--
theorem far_chainB (hfar0 : lat2 (nb (cellJ c s j) (latB s)) s ∉ F) :
    ∀ m, (∀ r < m, outer2 (cellJ c s (j + r)) s ∈ F ↔ r % 2 = 1) →
      (∀ r < m, deg F (front2 (nb (cellJ c s (j + r)) (latB s)) s) = 2) →
      (lat2 (nb (cellJ c s (j + m)) (latB s)) s ∈ F ↔ m % 2 = 1)
  | 0, _, _ => by simpa using hfar0
  | m + 1, ho, hd => by
    have ih := far_chainB hfar0 m (fun r hr => ho r (by omega)) (fun r hr => hd r (by omega))
    have hdeg := hd m (by omega)
    rw [deg_front2, sideB_front, nb_sideB_comm, nb_cellJ, show j + m + 1 = j + (m + 1) by omega]
      at hdeg
    have hom := ho m (by omega)
    rcases Nat.mod_two_eq_zero_or_one m with h | h
    · rw [ind_of_not_mem (fun h' => by have := ih.1 h'; omega),
        ind_of_not_mem (fun h' => by have := hom.1 h'; omega)] at hdeg
      have : ind F (lat2 (nb (cellJ c s (j + (m + 1))) (latB s)) s) = 1 := by
        have := ind_le_one F (lat2 (nb (cellJ c s (j + (m + 1))) (latB s)) s)
        have := ind_le_one F (outer2 (nb (cellJ c s (j + m)) (latB s)) s)
        omega
      constructor
      · intro _; omega
      · intro _; unfold ind at this; split_ifs at this with hh; exact hh
    · rw [ind_of_mem (ih.2 h), ind_of_mem (hom.2 h)] at hdeg
      constructor
      · intro hh; rw [ind_of_mem hh] at hdeg; omega
      · intro hh; omega

end chain

end HP

end SolidGridHam

namespace SolidGridHam

namespace HP

open Finset Classical

section sideafter

variable {V W : Finset Pt} {d : Pt → ℕ} {H H' : Finset Edge} {FP : List FixedPr} {c : Pt}
  {s : Side} {n : ℕ} {i : FixedPr} {t0 u0 : Pt} (M : MoveCtx V W d H H' FP c s n i t0 u0)
include M

lemma MoveCtx.outer1_H1 {k : ℕ} (hk : k ≤ n) :
    outer1 (cellJ c s k) s ∈ lowerCol H c s n ↔ k % 2 = 0 := by
  rw [outer_after1]; exact outer1_all M.ev M.two M.pat M.d1 M.d2 M.altB hk

lemma MoveCtx.outer2_H1 {k : ℕ} (hk : k ≤ n) :
    outer2 (cellJ c s k) s ∈ lowerCol H c s n ↔ k % 2 = 0 := by
  rw [outer_after2]; exact outer2_all M.ev M.two M.pat M.d1 M.d2 M.altB hk

lemma MoveCtx.latB_lats_H1 :
    lat1 (cellJ c s (n + 1)) s ∉ lowerCol H c s n ∧ lat2 (cellJ c s (n + 1)) s ∉ lowerCol H c s n := by
  have bB : back (cellJ c s (n + 1)) s ∈ H := by
    rw [back_cellJ_succ]; exact frontn_mem M.ev M.two M.pat M.d1 M.d2 M.altB
  have h := alt_lats M.altB (s' := s.opp) bB
  rw [latA_opp, show latB s.opp = latB s by cases s <;> rfl, ← lat1_eq, ← lat2_eq] at h
  rw [mem_lowerCol_off (fun m _ _ => by rw [lat1_mem_cellE_iff]; omega),
    mem_lowerCol_off (fun m _ _ => by rw [lat2_mem_cellE_iff]; omega)]
  exact h

-- **The side line after the move is a strip** from an odd `S_j` with light far side, up to `S_n`;
-- the next square `S_(n+1)` (beside the old `B`) has both lateral sides light.
--
theorem MoveCtx.side_run {j : ℕ} (hj1 : 1 ≤ j) (hjn : j ≤ n) (hjo : j % 2 = 1)
    (hcellS : ∀ k, j ≤ k → k ≤ n → IsCell V (nb (cellJ c s k) (latA s)))
    (hfar : lat1 (nb (cellJ c s j) (latA s)) s ∉ lowerCol H c s n) :
    StripRun (lowerCol H c s n) (nb (cellJ c s j) (latA s)) s (n + 1 - j) ∧
      lat1 (nb (cellJ c s (n + 1)) (latA s)) s ∉ lowerCol H c s n ∧
      lat2 (nb (cellJ c s (n + 1)) (latA s)) s ∉ lowerCol H c s n := by
  set H₁ := lowerCol H c s n
  have hdeg : ∀ r < n + 1 - j, deg H₁ (front1 (nb (cellJ c s (j + r)) (latA s)) s) = 2 := by
    intro r hr
    have hc := hcellS (j + r) (by omega) (by omega)
    rw [M.factor.2 _ (M.hVW (isCell_corners hc s).2.2.1)]
    exact M.hdc _ hc _ (isCorner_front1 _ s)
  have hout : ∀ r < n + 1 - j, outer1 (cellJ c s (j + r)) s ∈ H₁ ↔ r % 2 = 1 := by
    intro r hr; rw [M.outer1_H1 (by omega)]; omega
  have far := fun m (hm : m ≤ n + 1 - j) => far_chain hfar m (fun r hr => hout r (by omega))
    (fun r hr => hdeg r (by omega))
  have ec : ∀ r, cellJ (nb (cellJ c s j) (latA s)) s r = nb (cellJ c s (j + r)) (latA s) := by
    intro r; rw [← cellJ_side, cellJ_add, cellJ_side]
  refine ⟨⟨?_, fun r hr => ?_, fun r hr => ?_⟩, ?_, ?_⟩
  · have hb : back (nb (cellJ c s j) (latA s)) s = outer1 (cellJ c s (j - 1)) s := by
      rw [outer1_side_nb_next, nb_cellJ, show j - 1 + 1 = j by omega]; rfl
    rw [hb, M.outer1_H1 (by omega)]; omega
  · rw [ec]
    refine ⟨far r (by omega), ?_⟩
    rw [side_near, lat1_after M.ev M.two M.pat (by omega) (by omega)]; omega
  · rw [ec, side_front, M.outer1_H1 (by omega)]; omega
  · have := far (n + 1 - j) le_rfl
    rw [show j + (n + 1 - j) = n + 1 by omega] at this
    intro h; have := this.1 h; have := M.ev; omega
  · rw [side_near]; exact M.latB_lats_H1.1

theorem MoveCtx.side_runB {j : ℕ} (hj1 : 1 ≤ j) (hjn : j ≤ n) (hjo : j % 2 = 1)
    (hcellS : ∀ k, j ≤ k → k ≤ n → IsCell V (nb (cellJ c s k) (latB s)))
    (hfar : lat2 (nb (cellJ c s j) (latB s)) s ∉ lowerCol H c s n) :
    StripRun (lowerCol H c s n) (nb (cellJ c s j) (latB s)) s (n + 1 - j) ∧
      lat1 (nb (cellJ c s (n + 1)) (latB s)) s ∉ lowerCol H c s n ∧
      lat2 (nb (cellJ c s (n + 1)) (latB s)) s ∉ lowerCol H c s n := by
  set H₁ := lowerCol H c s n
  have hdeg : ∀ r < n + 1 - j, deg H₁ (front2 (nb (cellJ c s (j + r)) (latB s)) s) = 2 := by
    intro r hr
    have hc := hcellS (j + r) (by omega) (by omega)
    rw [M.factor.2 _ (M.hVW (isCell_corners hc s).2.2.2)]
    exact M.hdc _ hc _ (isCorner_front2 _ s)
  have hout : ∀ r < n + 1 - j, outer2 (cellJ c s (j + r)) s ∈ H₁ ↔ r % 2 = 1 := by
    intro r hr; rw [M.outer2_H1 (by omega)]; omega
  have far := fun m (hm : m ≤ n + 1 - j) => far_chainB hfar m (fun r hr => hout r (by omega))
    (fun r hr => hdeg r (by omega))
  have ec : ∀ r, cellJ (nb (cellJ c s j) (latB s)) s r = nb (cellJ c s (j + r)) (latB s) := by
    intro r; rw [← cellJ_sideB, cellJ_add, cellJ_sideB]
  refine ⟨⟨?_, fun r hr => ?_, fun r hr => ?_⟩, ?_, ?_⟩
  · have hb : back (nb (cellJ c s j) (latB s)) s = outer2 (cellJ c s (j - 1)) s := by
      rw [outer2_side_nb_next, nb_cellJ, show j - 1 + 1 = j by omega]; rfl
    rw [hb, M.outer2_H1 (by omega)]; omega
  · rw [ec]
    refine ⟨?_, far r (by omega)⟩
    rw [sideB_near, lat2_after M.ev M.two M.pat (by omega) (by omega)]; omega
  · rw [ec, sideB_front, M.outer2_H1 (by omega)]; omega
  · rw [sideB_near]; exact M.latB_lats_H1.2
  · have := far (n + 1 - j) le_rfl
    rw [show j + (n + 1 - j) = n + 1 by omega] at this
    intro h; have := this.1 h; have := M.ev; omega

end sideafter

end HP

end SolidGridHam
