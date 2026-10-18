/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.HP.AlgPF

/-!
# Zeros at the endpoints' cells

`ZeroAt F H s t`: `D · H` vanishes on the endpoints' cells. Flipping an alternating cell changes
`D` only at that cell, so flips and strip flips avoiding the endpoints' cells keep it.
-/

namespace ULHC

namespace HP

open Finset Classical

variable {V : Finset Pt} {d : Pt → ℕ} {s t : Pt}

def ZeroAt (F H : Finset Edge) (s t : Pt) : Prop := ∀ w, IsCorner s w ∨ IsCorner t w → D F H w = 0

/-! ## Flips of alternating cells change `D` only at the cell -/

lemma alt_sink_or_source {F : Finset Edge} {c : Pt} (h : Alt F c) : Sink F c ∨ Source F c := by
  obtain ⟨x, y⟩ := c
  have pB : par (x, y - 1) = !par (x, y) := par_sub_snd (x, y)
  have pL : par (x - 1, y) = !par (x, y) := par_sub_fst (x, y)
  have oB : outArc F (x, y) .b = !up F (bot (x, y)) := rfl
  have oT : outArc F (x, y) .t = up F (top (x, y)) := rfl
  have oL : outArc F (x, y) .l = !up F (lft (x, y)) := rfl
  have oR : outArc F (x, y) .r = up F (rgt (x, y)) := rfl
  have uB : up F (bot (x, y)) = (par (x, y - 1) == decide (bot (x, y) ∈ F)) := by
    simp [up, inE1, bot, Edge.lo]
  have uT : up F (top (x, y)) = (par (x, y) == decide (top (x, y) ∈ F)) := by
    simp [up, inE1, top, Edge.lo]
  have uL : up F (lft (x, y)) = (par (x - 1, y) == !decide (lft (x, y) ∈ F)) := by
    simp [up, inE1, lft, Edge.lo]
  have uR : up F (rgt (x, y)) = (par (x, y) == !decide (rgt (x, y) ∈ F)) := by
    simp [up, inE1, rgt, Edge.lo]
  rw [pB] at uB; rw [pL] at uL
  rcases h with ⟨hb, ht, hl, hr⟩ | ⟨hb, ht, hl, hr⟩ <;>
  cases hp : par (x, y) <;>
  · first
    | (left; intro sd; cases sd <;> simp_all <;> done)
    | (right; intro sd; cases sd <;> simp_all)

lemma D_flip_alt {F H : Finset Edge} {c : Pt} (h : Alt F c) {x : Pt} (hx : x ≠ c) :
    D (ULHC.flip F c) H x = D F H x := by
  rcases alt_sink_or_source h with hs | hs
  · rw [D_flip_sink hs]; simp [hx]
  · rw [D_flip_source hs]; simp [hx]

lemma zero_flip {F H : Finset Edge} {c : Pt} (h : Alt F c) (hcs : ¬ IsCorner s c)
    (hct : ¬ IsCorner t c) (hz : ZeroAt F H s t) : ZeroAt (ULHC.flip F c) H s t := by
  intro w hw
  have hwc : w ≠ c := by rintro rfl; rcases hw with hw | hw <;> contradiction
  rw [D_flip_alt h hwc]; exact hz w hw

lemma alt_of_bf {F : Finset Edge} {c : Pt} {sd : Side} (hb : back c sd ∈ F) (hf : front c sd ∈ F)
    (h1 : lat1 c sd ∉ F) (h2 : lat2 c sd ∉ F) : Alt F c := by
  unfold Alt
  cases sd <;> simp only [back, front, lat1, lat2, sideEdge, Side.opp] at hb hf h1 h2 <;> tauto

lemma alt_of_lat {F : Finset Edge} {c : Pt} {sd : Side} (hb : back c sd ∉ F) (hf : front c sd ∉ F)
    (h1 : lat1 c sd ∈ F) (h2 : lat2 c sd ∈ F) : Alt F c := by
  unfold Alt
  cases sd <;> simp only [back, front, lat1, lat2, sideEdge, Side.opp] at hb hf h1 h2 <;> tauto

lemma cornerB_of {z c : Pt} (h : IsCorner z c) : cornerB z c = true := by
  unfold IsCorner at h; unfold cornerB
  rcases h with h | h | h | h <;> simp [h]

lemma zero_flipCol {F H : Finset Edge} {c : Pt} {sd : Side} :
    ∀ n, StripPat F c sd n → (∀ j < n, ¬ IsCorner s (cellJ c sd j) ∧ ¬ IsCorner t (cellJ c sd j)) →
      ZeroAt F H s t → ZeroAt (flipCol F c sd n) H s t := by
  intro n
  induction n generalizing F with
  | zero => intro _ _ hz; exact hz
  | succ n ih =>
    intro hpat hav hz
    rw [flipCol_succ]
    obtain ⟨hb, hl, hf⟩ := hpat
    have mF : front (cellJ c sd n) sd ∈ F ↔ n % 2 = 0 := by
      have := hf n (by omega); simp only [lt_self_iff_false, iff_false] at this; rw [this]; omega
    have mB : back (cellJ c sd n) sd ∈ F ↔ n % 2 = 0 := by
      rcases n with _ | n
      · simp only [cellJ_zero]; simp [hb]
      · rw [back_cellJ_succ]
        have := hf n (by omega)
        have q : n + 1 < n + 1 + 1 := by omega
        simp only [q, iff_true] at this
        rw [this]; omega
    have mL1 := (hl n (by omega)).1
    have mL2 := (hl n (by omega)).2
    have halt : Alt F (cellJ c sd n) := by
      rcases Nat.mod_two_eq_zero_or_one n with h | h
      · exact alt_of_bf (mB.2 h) (mF.2 h) (fun h' => by have := mL1.1 h'; omega)
          (fun h' => by have := mL2.1 h'; omega)
      · exact alt_of_lat (fun h' => by have := mB.1 h'; omega) (fun h' => by have := mF.1 h'; omega)
          (mL1.2 h) (mL2.2 h)
    have hz' := zero_flip halt (hav n (by omega)).1 (hav n (by omega)).2 hz
    rcases n with _ | n
    · simpa [flipCol] using hz'
    · exact ih (pat_flip_end ⟨hb, hl, hf⟩) (fun j hj => hav j (by omega)) hz'

lemma zero_strip {F H : Finset Edge} {σ : StripSpec} (hσ : σ ∈ allStrips V F)
    (hav : avoidB s t σ = true) (hz : ZeroAt F H s t) : ZeroAt (applyS F σ) H s t := by
  obtain ⟨_, hpat, _⟩ := mem_allStrips.1 hσ
  refine zero_flipCol σ.n hpat (fun j hj => ?_) hz
  unfold avoidB at hav
  have := List.all_eq_true.1 hav j (List.mem_range.2 hj)
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at this
  exact ⟨fun h => by rw [cornerB_of h] at this; simp at this,
    fun h => by rw [cornerB_of h] at this; simp at this⟩

end HP

end ULHC
