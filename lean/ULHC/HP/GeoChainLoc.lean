/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.NearGeo
import ULHC.NearChain
import ULHC.HP.TouchLoc

/-!
# ULHC's `mid_touch` (NearGeo) and the side chains (NearChain) with local hypotheses
`mid_touch` needs only degree at most 2; the side chains use the local `touch_side*_L`.
-/

namespace ULHC

namespace HP

open Finset Classical

section mid

variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hle : ∀ z, deg F z ≤ 2) (hpat : StripPat F c s (k + 2))
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j))
include hle hpat hcell

-- A dark edge at a middle corner of `a` is a side of a cell of `a`.
--
omit hcell in
theorem mid_touch_L {p : Pt} (hm : IsMid c s k p) {x : Edge} (hx : x ∈ F) (hxp : x.p = p ∨ x.q = p) :
    ∃ j < k + 2, x ∈ cellE (cellJ c s j) := by
  obtain ⟨j, hj, hjk, hp⟩ := hm
  obtain ⟨a1, a2, _, af⟩ := strip_sig hpat (show j < k + 2 by omega)
  have l1 := a1.2 hj
  have l2 := a2.2 hj
  have fr : front (cellJ c s j) s ∈ F := af.2 ⟨fun _ => by omega, fun _ => hj⟩
  have hdeg := hle (front1 (cellJ c s j) s)
  have hdeg2 := hle (front2 (cellJ c s j) s)
  set d := cellJ c s j
  have mem : ∀ y, y = lat1 d s ∨ y = lat2 d s ∨ y = front d s → y ∈ cellE d := by
    intro y hy; rw [cellE_frame d s]; rcases hy with rfl | rfl | rfl <;> simp
  refine ⟨j, by omega, ?_⟩
  rcases hp with rfl | rfl
  · by_contra hn
    have n1 : x ≠ lat1 d s := fun h => hn (mem _ (Or.inl h))
    have n2 : x ≠ front d s := fun h => hn (mem _ (Or.inr (Or.inr h)))
    have n12 : lat1 d s ≠ front d s :=
      (ends_lat1 d s).ne_at (ends_front d s) (stk_b1_f2 d s)
    have := three_le_deg l1 fr hx ((ends_lat1 d s).inc_iff _ |>.2 (Or.inr rfl))
      ((ends_front d s).inc_iff _ |>.2 (Or.inl rfl)) hxp n12 n1.symm n2.symm
    omega
  · by_contra hn
    have n1 : x ≠ lat2 d s := fun h => hn (mem _ (Or.inr (Or.inl h)))
    have n2 : x ≠ front d s := fun h => hn (mem _ (Or.inr (Or.inr h)))
    have n12 : lat2 d s ≠ front d s :=
      (ends_lat2 d s).ne_at (ends_front d s).swap (stk_b2_f1 d s)
    have := three_le_deg l2 fr hx ((ends_lat2 d s).inc_iff _ |>.2 (Or.inr rfl))
      ((ends_front d s).inc_iff _ |>.2 (Or.inr rfl)) hxp n12 n1.symm n2.symm
    omega

end mid

section chain

variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hV : Inside V F) (hDc : ∀ j ≤ k + 1, ∀ z, IsCorner z (cellJ c s j) → deg F z = 2)
  (hTs : ∀ tf, (tf = latA s ∨ tf = latB s) → IsCell V (nb c tf) → NotTypeIII V F (nb c tf))
  (hTr : IsCell V (nb c s) → NotTypeIII V F (nb c s)) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat F c s (k + 2))
  (hsep : ¬ Conn F (back1 c s) (front1 c s))
  {z : Pt} {tf : Side} {m i0 : ℕ} (hz : SigFrom F z tf m i0)

include hk hpat hz in
theorem reach_end_L : ∀ d i j, j + d = k + 1 → i0 ≤ i → i < m → cellJ z tf i = cellJ c s j →
    ∃ i', i ≤ i' ∧ i' < m ∧ cellJ z tf i' = cellJ c s (k + 1) := by
  intro d
  induction d with
  | zero => intro i j hd h0 hi hq; exact ⟨i, le_rfl, hi, by rw [hq, show j = k + 1 by omega]⟩
  | succ d ih =>
    intro i j hd h0 hi hq
    obtain ⟨ht, _, hi1⟩ := touch_body_L hpat hz h0 hi (j := j) (by omega) hq
    obtain ⟨i', h1, h2, h3⟩ := ih (i + 1) (j + 1) (by omega) (by omega) hi1 (by
      rw [← nb_cellJ, hq, ht, nb_cellJ])
    exact ⟨i', by omega, h2, h3⟩

include hV hDc hTs hk hcell hpat hsep hz in
theorem side_chain1_L : ∀ j i, j ≤ k → i0 ≤ i → i < m → cellJ z tf i = nb (cellJ c s j) (latA s) →
    tf = s.opp ∧ ∃ ie, i ≤ ie ∧ ie < m ∧ ie % 2 = 0 ∧ cellJ z tf ie = nb c (latA s) := by
  intro j
  induction j with
  | zero =>
    intro i _ h0 hi hq
    obtain ⟨ht, hp, _⟩ := touch_side1_L hV hDc hTs hk hcell hpat hsep hz h0 hi (j := 0) (by omega) hq
    exact ⟨ht, i, le_rfl, hi, by omega, by rw [hq, cellJ_zero]⟩
  | succ j ih =>
    intro i hj h0 hi hq
    obtain ⟨ht, _, hi1⟩ := touch_side1_L hV hDc hTs hk hcell hpat hsep hz h0 hi (j := j + 1) hj hq
    obtain ⟨ht', ie, h1, h2⟩ := ih (i + 1) (by omega) (by omega) hi1 (by
      rw [← nb_cellJ, hq, ht, side1_down])
    exact ⟨ht', ie, by omega, h2⟩

include hV hDc hTs hTr hk hcell hpat hsep hz in
theorem side_chain2_L : ∀ j i, j ≤ k → i0 ≤ i → i < m → cellJ z tf i = nb (cellJ c s j) (latB s) →
    tf = s.opp ∧ ∃ ie, i ≤ ie ∧ ie < m ∧ ie % 2 = 0 ∧ cellJ z tf ie = nb c (latB s) := by
  intro j
  induction j with
  | zero =>
    intro i _ h0 hi hq
    obtain ⟨ht, hp, _⟩ := touch_side2_L hV hDc hTs hTr hk hcell hpat hsep hz h0 hi (j := 0) (by omega) hq
    exact ⟨ht, i, le_rfl, hi, by omega, by rw [hq, cellJ_zero]⟩
  | succ j ih =>
    intro i hj h0 hi hq
    obtain ⟨ht, _, hi1⟩ := touch_side2_L hV hDc hTs hTr hk hcell hpat hsep hz h0 hi (j := j + 1) hj hq
    obtain ⟨ht', ie, h1, h2⟩ := ih (i + 1) (by omega) (by omega) hi1 (by
      rw [← nb_cellJ, hq, ht, side2_down])
    exact ⟨ht', ie, by omega, h2⟩

end chain

end HP

end ULHC
