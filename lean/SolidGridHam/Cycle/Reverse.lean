/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import SolidGridHam.Cycle.NearLemma

@[expose] public section

/-!
# The reversed strip

After an even strip `a = (c, s, k + 2)` is flipped, the same cells, read from the end cell
`e` against `s`, form an even strip `rev a` of the new factor (`rev_pat`). Flipping it restores
the old factor (`rev_flip`). It is proper when the new factor is Type III-free
(`rev_valid`): the end cell's `lat1` corners are separated after the flip (`end_corners`).
-/

namespace SolidGridHam

open Finset

def rev (a : StripSpec) : StripSpec := ⟨endCell a, a.s.opp, a.n⟩

lemma rev_cellJ_add (c : Pt) (s : Side) (i m : ℕ) :
    cellJ (cellJ c s (i + m)) s.opp i = cellJ c s m := by
  obtain ⟨x, y⟩ := c
  cases s <;> simp only [cellJ, Side.opp, Nat.cast_add] <;> ring_nf

lemma rev_cellJ (c : Pt) (s : Side) {i k : ℕ} (hi : i ≤ k + 1) :
    cellJ (cellJ c s (k + 1)) s.opp i = cellJ c s (k + 1 - i) := by
  have := rev_cellJ_add c s i (k + 1 - i)
  rwa [show i + (k + 1 - i) = k + 1 by omega] at this

lemma nOn_rev (c : Pt) (s : Side) (k : ℕ) (x : Edge) :
    nOn (cellJ c s (k + 1)) s.opp (k + 2) x = nOn c s (k + 2) x := by
  unfold nOn
  apply Finset.card_bij (fun i _ => k + 1 - i)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
    refine ⟨by omega, ?_⟩
    rw [← rev_cellJ c s (by omega)]; exact hi.2
  · intro i hi j hj h
    simp only [Finset.mem_filter, Finset.mem_range] at hi hj
    omega
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj
    refine ⟨k + 1 - j, ?_, by omega⟩
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_⟩
    rw [rev_cellJ c s (by omega), show k + 1 - (k + 1 - j) = j by omega]; exact hj.2

theorem rev_flip (F : Finset Edge) (c : Pt) (s : Side) (k : ℕ) :
    flipCol (flipCol F c s (k + 2)) (cellJ c s (k + 1)) s.opp (k + 2) = F := by
  ext x
  rw [mem_flipCol, mem_flipCol, nOn_rev]
  tauto

section rev

variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hk : k % 2 = 0) (hpat : StripPat F c s (k + 2))
include hk hpat

theorem rev_pat : StripPat (flipCol F c s (k + 2)) (cellJ c s (k + 1)) s.opp (k + 2) := by
  refine ⟨?_, fun i hi => ?_, fun i hi => ?_⟩
  · rw [(frame_opp _ s).2.2.1]; exact front_end_after hk hpat
  · rw [rev_cellJ c s (by omega), (frame_opp _ s).1, (frame_opp _ s).2.1,
      lat1_after hk hpat (by omega), lat2_after hk hpat (by omega)]
    omega
  · rw [rev_cellJ c s (by omega), (frame_opp _ s).2.2.2]
    by_cases hj : i ≤ k
    · rw [back_after_j hk hpat (by omega) (by omega)]; omega
    · rw [show k + 1 - i = 0 by omega, cellJ_zero]
      simp only [back_after hk hpat, false_iff]
      omega

end rev

section revvalid

variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hs : Solid V) (x0 : Pt) (hconn : ∀ z ∈ V, Conn (GE V) x0 z)
  (hF : Deg2 V F) (hT : NoTypeIII V F) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat F c s (k + 2))
  (hsep : ¬ Conn F (back1 c s) (front1 c s)) (hT' : NoTypeIII V (flipCol F c s (k + 2)))
include hs x0 hconn hF hT hk hcell hpat hsep hT'

omit hs x0 hconn hT' in
theorem rev_valid :
    ValidStrip V (flipCol F c s (k + 2)) ⟨cellJ c s (k + 1), s.opp, k + 2⟩ := by
  refine ⟨by show 1 ≤ k + 2; omega, rev_pat hk hpat, fun i hi => ?_, ?_⟩
  · change i < k + 2 at hi
    show IsCell V (cellJ (cellJ c s (k + 1)) s.opp i)
    rw [rev_cellJ c s (by omega)]; exact hcell _ (by omega)
  · exact conn_lat1_opp (end_corners hF hT hk hcell hpat hsep).2.2

end revvalid

end SolidGridHam
