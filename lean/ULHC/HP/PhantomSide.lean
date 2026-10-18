/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.HP.NearLemmaPF

/-!
# When the hypothesis `hTsP` fails (phantom endpoint beside a strip's start)

`hTsP` says the square `X` beside the start cell `c` of a strip, when it has the endpoint `t0`
as a corner, is not Type III. `phantom_sideA` describes the failing case across `latA`: `X` is no
cell, `t0` is outside `V` at one of `X`'s two far corners, `X`'s back side is dark, and the edge
behind `back1 c` is light. `t0` at the far back corner is configuration A, at the far front
corner configuration B.

`behind_free_A` / `behind_free_B`: in either configuration no strip of `V` passes through the cell
behind `c` (in configuration B, unless it does so at an odd first index of its pattern).
-/

namespace ULHC

namespace HP

open Finset Classical

-- Corners of the square beside `c` across `latA s`: its two far corners, or corners of `c`.
--
lemma corner_sideA {t0 c : Pt} {s : Side} (h : IsCorner t0 (nb c (latA s))) :
    t0 = back1 (nb c (latA s)) s ∨ t0 = front1 (nb c (latA s)) s ∨ IsCorner t0 c := by
  obtain ⟨x, y⟩ := c; obtain ⟨a, b⟩ := t0
  cases s <;> rcases h with h | h | h | h <;>
    simp only [nb, latA, Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h <;>
    simp [IsCorner, nb, latA, back1, front1]

lemma corner_sideB {t0 c : Pt} {s : Side} (h : IsCorner t0 (nb c (latB s))) :
    t0 = back2 (nb c (latB s)) s ∨ t0 = front2 (nb c (latB s)) s ∨ IsCorner t0 c := by
  obtain ⟨x, y⟩ := c; obtain ⟨a, b⟩ := t0
  cases s <;> rcases h with h | h | h | h <;>
    simp only [nb, latB, Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h <;>
    simp [IsCorner, nb, latB, back2, front2]

-- The squares beside `c` on its two sides share no corner.
--
lemma corner_sides_disj {t0 c : Pt} {s : Side} (hA : IsCorner t0 (nb c (latA s)))
    (hB : IsCorner t0 (nb c (latB s))) : False := by
  obtain ⟨x, y⟩ := c; obtain ⟨a, b⟩ := t0
  cases s <;> rcases hA with h | h | h | h <;>
    simp only [nb, latA, Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h <;>
    rcases hB with h' | h' | h' | h' <;> simp only [nb, latB, Prod.mk.injEq] at h' <;> omega

-- The far back corner of the square beside `c` is the far front corner of the square behind it.
--
lemma front1_diag (c : Pt) (s : Side) :
    front1 (nb (nb c s.opp) (latA s)) s = back1 (nb c (latA s)) s := by
  obtain ⟨x, y⟩ := c; cases s <;> simp [front1, back1, nb, latA, Side.opp]

-- A square whose side `lat2 · s` is light is Type III only with dark back and front in frame `s`.
--
lemma t3_backfront {V : Finset Pt} {F : Finset Edge} {X : Pt} {s : Side} (hl : lat2 X s ∉ F)
    (hT : ¬ NotTypeIII V F X) : back X s ∈ F ∧ front X s ∈ F := by
  unfold NotTypeIII at hT; push Not at hT
  obtain ⟨s', hb, hf, _, _, _⟩ := hT
  rcases side_cases s s' with rfl | rfl | rfl | rfl
  · exact ⟨hb, hf⟩
  · obtain ⟨_, _, e1, e2⟩ := frame_opp X s
    rw [e1] at hb; rw [e2] at hf; exact ⟨hf, hb⟩
  · obtain ⟨_, e2, _⟩ := frame_latA X s
    rw [e2] at hb; exact absurd hb hl
  · obtain ⟨e1, _, _⟩ := frame_latB X s
    rw [e1] at hf; exact absurd hf hl

lemma front2_diag (c : Pt) (s : Side) :
    front2 (nb (nb c s.opp) (latB s)) s = back2 (nb c (latB s)) s := by
  obtain ⟨x, y⟩ := c; cases s <;> simp [front2, back2, nb, latB, Side.opp]

-- Mirror of `t3_backfront` with the side `lat1 · s` light.
--
lemma t3_backfront1 {V : Finset Pt} {F : Finset Edge} {X : Pt} {s : Side} (hl : lat1 X s ∉ F)
    (hT : ¬ NotTypeIII V F X) : back X s ∈ F ∧ front X s ∈ F := by
  unfold NotTypeIII at hT; push Not at hT
  obtain ⟨s', hb, hf, _, _, _⟩ := hT
  rcases side_cases s s' with rfl | rfl | rfl | rfl
  · exact ⟨hb, hf⟩
  · obtain ⟨_, _, e1, e2⟩ := frame_opp X s
    rw [e1] at hb; rw [e2] at hf; exact ⟨hf, hb⟩
  · obtain ⟨e1, _, _⟩ := frame_latA X s
    rw [e1] at hf; exact absurd hf hl
  · obtain ⟨_, e2, _⟩ := frame_latB X s
    rw [e2] at hb; exact absurd hb hl

section side

variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {n : ℕ} {s0 t0 : Pt}
  (hF : Deg2Off V F s0 t0) (hs0 : s0 ∈ V) (hp : StripPat F c s n) (hn : 2 ≤ n)
  (hc : IsCell V c) (hc0 : ¬ IsCorner t0 c) (hd0 : ∀ z, IsCorner z c → deg F z = 2)
  (hTs : IsCell V (nb c (latA s)) → NotTypeIII V F (nb c (latA s)))

include hF hs0 hp hn hc hc0 hd0 hTs in
-- **When `hTsP` fails across `latA`.**
--
theorem phantom_sideA (ht : IsCorner t0 (nb c (latA s))) (hT : ¬ NotTypeIII V F (nb c (latA s))) :
    ¬ IsCell V (nb c (latA s)) ∧ t0 ∉ V ∧ back (nb c (latA s)) s ∈ F ∧
      lat1 (nb c s.opp) s ∉ F ∧
      (t0 = back1 (nb c (latA s)) s ∨ t0 = front1 (nb c (latA s)) s) := by
  set X := nb c (latA s)
  have hl0 : lat1 c s ∉ F := by
    have := (hp.2.1 0 (by omega)).1; rw [cellJ_zero] at this; simpa using this
  have hl : lat2 X s ∉ F := by rw [side_lat2]; exact hl0
  obtain ⟨hbX, hfX⟩ := t3_backfront hl hT
  have hL0 : ¬ IsCell V X := fun h => hT (hTs h)
  have hfar : t0 = back1 X s ∨ t0 = front1 X s := by
    rcases corner_sideA ht with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h hc0
  have hn1 : lat1 (nb c s.opp) s ∉ F := by
    have hd := hd0 _ (isCorner_back1 c s)
    rw [deg_back1, ind_of_not_mem hl0, ind_of_mem hp.1, ind_of_mem hbX] at hd
    intro h; rw [ind_of_mem h] at hd; omega
  have ht0V : t0 ∉ V := by
    intro ht0
    apply hL0
    obtain ⟨cb1, _, cf1, _⟩ := isCell_corners hc s
    have hVb := (side_back_ends c s).inV (hF.1 _ hbX)
    have hVf := (side_front_ends c s).inV (hF.1 _ (by rw [← side_front]; exact hfX))
    refine isCell_of_corners X s (memW hVb.1 hs0 (fun _ => ht0)) ?_
      (memW hVf.1 hs0 (fun _ => ht0)) ?_
    · rw [side_back2]; exact cb1
    · rw [side_front2]; exact cf1
  exact ⟨hL0, ht0V, hbX, hn1, hfar⟩

include hF hs0 hp hn hc hc0 hd0 in
-- **When `hTsP` fails across `latB`** (mirror).
--
theorem phantom_sideB (hTsB : IsCell V (nb c (latB s)) → NotTypeIII V F (nb c (latB s)))
    (ht : IsCorner t0 (nb c (latB s))) (hT : ¬ NotTypeIII V F (nb c (latB s))) :
    ¬ IsCell V (nb c (latB s)) ∧ t0 ∉ V ∧ back (nb c (latB s)) s ∈ F ∧
      lat2 (nb c s.opp) s ∉ F ∧
      (t0 = back2 (nb c (latB s)) s ∨ t0 = front2 (nb c (latB s)) s) := by
  set X := nb c (latB s)
  have hl0 : lat2 c s ∉ F := by
    have := (hp.2.1 0 (by omega)).2; rw [cellJ_zero] at this; simpa using this
  have hl : lat1 X s ∉ F := by rw [side2_lat1]; exact hl0
  obtain ⟨hbX, hfX⟩ := t3_backfront1 hl hT
  have hL0 : ¬ IsCell V X := fun h => hT (hTsB h)
  have hfar : t0 = back2 X s ∨ t0 = front2 X s := by
    rcases corner_sideB ht with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h hc0
  have hn2 : lat2 (nb c s.opp) s ∉ F := by
    have hd := hd0 _ (isCorner_back2 c s)
    rw [deg_back2, ind_of_not_mem hl0, ind_of_mem hp.1, ind_of_mem hbX] at hd
    intro h; rw [ind_of_mem h] at hd; omega
  have ht0V : t0 ∉ V := by
    intro ht0
    apply hL0
    obtain ⟨_, cb2, _, cf2⟩ := isCell_corners hc s
    have hVb := (side2_back_ends c s).inV (hF.1 _ hbX)
    have hVf := (side2_front_ends c s).inV (hF.1 _ (by rw [← side2_front]; exact hfX))
    refine isCell_of_corners X s ?_ (memW hVb.2 hs0 (fun _ => ht0)) ?_
      (memW hVf.2 hs0 (fun _ => ht0))
    · rw [side2_back1]; exact cb2
    · rw [side2_front1]; exact cf2
  exact ⟨hL0, ht0V, hbX, hn2, hfar⟩

end side

section behind

variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {n : ℕ} {s0 t0 : Pt}
  (hF : Deg2Off V F s0 t0) (hp : StripPat F c s n) (hn : 2 ≤ n)
  (hc0W : IsCell (insert s0 (insert t0 V)) c) (hd0 : ∀ z, IsCorner z c → deg F z = 2)
  (hsep : ¬ Conn F (back1 c s) (front1 c s))
  (hTrW : IsCell (insert s0 (insert t0 V)) (nb c s) →
    NotTypeIII (insert s0 (insert t0 V)) F (nb c s))
  (hTBW : IsCell (insert s0 (insert t0 V)) (nb c (latB s)) →
    NotTypeIII (insert s0 (insert t0 V)) F (nb c (latB s)))
  (hn1 : lat1 (nb c s.opp) s ∉ F)
  {z : Pt} {tf : Side} {m i0 i : ℕ} (hz : SigFrom F z tf m i0) (hi0 : i0 ≤ i) (hi : i < m)
  (hq : cellJ z tf i = nb c s.opp)
include hF hp hn hc0W hd0 hsep hTrW hTBW hn1 hz hi0 hi hq

-- **Configuration A**: no strip of `V` passes through the cell behind `c`.
--
theorem behind_free_A (hA : t0 = back1 (nb c (latA s)) s) (ht0V : t0 ∉ V)
    (hzc : ∀ j < m, IsCell V (cellJ z tf j)) : False := by
  have d2 := back_down2_loc hF.1 hp hn hc0W hsep (hd0 _ (isCorner_back2 c s))
    (hd0 _ (isCorner_front1 c s)) (hd0 _ (isCorner_front2 c s)) hTrW hTBW
  refine touch_behind_phantom hz hi0 hi hq hp.1 hn1 d2 hzc (fun h => ht0V ?_)
  rw [hA, ← front1_diag]; exact corner_mem h (isCorner_front1 _ s)

-- **A dark back side beside `c`** (configuration B, and A): no strip passes through the cell
-- behind `c`, except possibly at an odd first index of its pattern.
--
theorem behind_free_B (hB : back (nb c (latA s)) s ∈ F) (hprev : i % 2 = 1 → i0 < i) :
    False := by
  have d2 := back_down2_loc hF.1 hp hn hc0W hsep (hd0 _ (isCorner_back2 c s))
    (hd0 _ (isCorner_front1 c s)) (hd0 _ (isCorner_front2 c s)) hTrW hTBW
  exact touch_behind_outer hz hi0 hi hq hp.1 hn1 d2 hB hprev

end behind

section behindB

variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {n : ℕ} {s0 t0 : Pt}
  (hF : Deg2Off V F s0 t0) (hp : StripPat F c s n) (hn : 2 ≤ n)
  (hd0 : ∀ z, IsCorner z c → deg F z = 2)
  (hsep : ¬ Conn F (back1 c s) (front1 c s))
  (hTAW : IsCell (insert s0 (insert t0 V)) (nb c (latA s)) →
    NotTypeIII (insert s0 (insert t0 V)) F (nb c (latA s)))
  (hn2 : lat2 (nb c s.opp) s ∉ F)
  {z : Pt} {tf : Side} {m i0 i : ℕ} (hz : SigFrom F z tf m i0) (hi0 : i0 ≤ i) (hi : i < m)
  (hq : cellJ z tf i = nb c s.opp)
include hF hp hn hd0 hsep hTAW hn2 hz hi0 hi hq

-- **Configuration A across `latB`**: no strip of `V` passes through the cell behind `c`.
--
theorem behind_free_AB (hA : t0 = back2 (nb c (latB s)) s) (ht0V : t0 ∉ V)
    (hzc : ∀ j < m, IsCell V (cellJ z tf j)) : False := by
  have d1 := back_down_loc hF.1 hp hn hsep (hd0 _ (isCorner_back1 c s))
    (hd0 _ (isCorner_front1 c s)) hTAW
  refine touch_behind_phantomB hz hi0 hi hq hp.1 hn2 d1 hzc (fun h => ht0V ?_)
  rw [hA, ← front2_diag]; exact corner_mem h (isCorner_front2 _ s)

-- **A dark back side beside `c` across `latB`** (mirror of `behind_free_B`).
--
theorem behind_free_BB (hB : back (nb c (latB s)) s ∈ F) (hprev : i % 2 = 1 → i0 < i) :
    False := by
  have d1 := back_down_loc hF.1 hp hn hsep (hd0 _ (isCorner_back1 c s))
    (hd0 _ (isCorner_front1 c s)) hTAW
  exact touch_behind_outerB hz hi0 hi hq hp.1 hn2 d1 hB hprev

end behindB

section dispatch

variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  {s0 t0 : Pt} (hF : Deg2Off V F s0 t0) (hs0 : s0 ∈ V) (hds : deg F s0 = 1)
  (hle : ∀ z, deg F z ≤ 2) (hTR : NoTypeIIIR V F s0 t0) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j))
  (hcor : ∀ j ≤ k + 1, ¬ IsCorner s0 (cellJ c s j) ∧ ¬ IsCorner t0 (cellJ c s j))
  (hpat : StripPat F c s (k + 2))
  (hsep : ¬ Conn F (back1 c s) (front1 c s)) (hT' : NoTypeIIIR V (flipCol F c s (k + 2)) s0 t0)
  (hneut : ncomp V (flipCol F c s (k + 2)) = ncomp V F)
  (hTs : ∀ tf, (tf = latA s ∨ tf = latB s) → IsCell V (nb c tf) → NotTypeIII V F (nb c tf))
  {z : Pt} {tf : Side} {m i0 : ℕ} (hzw : SigFrom F z tf m i0)
  (hzR : ∀ j < m, ¬ IsCorner s0 (cellJ z tf j) ∧ ¬ IsCorner t0 (cellJ z tf j))
  (hzc : ∀ j < m, IsCell V (cellJ z tf j))
include hF hs0 hds hle hTR hk hcell hcor hpat hsep hT' hneut hTs hzw hzR hzc

omit hle in
-- **`touch_outcomeW` without `hTsP`.** When the square beside `c` on one side has `t0` as a corner
-- and is Type III, it is no cell and nothing passes through the cell behind `c`
-- (configuration A, or configuration B under `hBprev`), and the configuration-A proof applies;
-- otherwise `hTsP` holds and ULHC's proof applies. `hBprev` holds when the touching strip's
-- pattern starts at index 0.
--
theorem touch_outcomeW_pfD (hBprev : t0 ∉ V → ¬ PDang V t0 → ∀ i, i0 ≤ i → i % 2 = 1 → i0 < i)
    {i j : ℕ} (hi0 : i0 ≤ i) (hi : i < m) (hj : j < k + 2) {x : Edge}
    (hx1 : x ∈ cellE (cellJ z tf i)) (hx2 : x ∈ cellE (cellJ c s j)) :
    (∃ i', i ≤ i' ∧ i' < m ∧ cellJ z tf i' = cellJ c s (k + 1)) ∨
      (∃ i', i ≤ i' ∧ i' < m ∧ cellJ z tf i' = nb (cellJ c s (k + 1)) s) ∨
      (tf = s.opp ∧ ∃ ie, i ≤ ie ∧ ie < m ∧ ie % 2 = 0 ∧
        (cellJ z tf ie = nb c (latA s) ∨ cellJ z tf ie = nb c (latB s))) := by
  have hDc := corners_deg2 hF hcell hcor
  have hc0 : IsCell V c := by have := hcell 0 (by omega); rwa [cellJ_zero] at this
  have hc0W := isCell_mono hc0 (sub_insST V s0 t0)
  have hd0 : ∀ z, IsCorner z c → deg F z = 2 := fun z hz => hDc 0 (by omega) z (by rw [cellJ_zero]; exact hz)
  have hc0t : ¬ IsCorner t0 c := by have := (hcor 0 (by omega)).2; rwa [cellJ_zero] at this
  have hTr := ahead_notT3 hTR hcell hcor hk
  have hTrW := notT3W (t0 := t0) hs0 hTr (fun ht => absurd
    (show IsCorner t0 (cellJ c s 1) by rw [← nb_cellJ, cellJ_zero]; exact ht) (hcor 1 (by omega)).2)
  by_cases hA : IsCorner t0 (nb c (latA s)) ∧ ¬ NotTypeIII V F (nb c (latA s))
  · obtain ⟨hL0, ht0V, hbX, hn1, hfar⟩ := phantom_sideA hF hs0 hpat (by omega) hc0 hc0t hd0
      (hTs _ (Or.inl rfl)) hA.1 hA.2
    have hTsPB : IsCorner t0 (nb c (latB s)) → NotTypeIII V F (nb c (latB s)) :=
      fun hB => (corner_sides_disj hA.1 hB).elim
    have hTBW := notT3W (t0 := t0) hs0 (hTs (latB s) (Or.inr rfl)) hTsPB
    have hbeh : ∀ i, i0 ≤ i → i < m → cellJ z tf i = nb c s.opp → False := fun i h0 h1 hq => by
      rcases hfar with hA' | _
      · exact behind_free_A hF hpat (by omega) hc0W hd0 hsep hTrW hTBW hn1 hzw h0 h1 hq hA' ht0V hzc
      · exact behind_free_B hF hpat (by omega) hc0W hd0 hsep hTrW hTBW hn1 hzw h0 h1 hq hbX
          (hBprev ht0V (fun hpd => hA.2 (notT3_pdang hF hs0 hpd hA.1)) i h0)
    rcases touch_outcomeW_pfA hF hs0 hds hTR hk hcell hcor hpat hsep hT' hneut hTs hzw hzR
        hTsPB hzc hL0 hbeh hi0 hi hj hx1 hx2 with h | h | ⟨ht, ie, h1, h2, h3, h4⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨ht, ie, h1, h2, h3, Or.inr h4⟩)
  by_cases hB : IsCorner t0 (nb c (latB s)) ∧ ¬ NotTypeIII V F (nb c (latB s))
  · obtain ⟨hL0, ht0V, hbX, hn2, hfar⟩ := phantom_sideB hF hs0 hpat (by omega) hc0 hc0t hd0
      (hTs _ (Or.inr rfl)) hB.1 hB.2
    have hTsPA : IsCorner t0 (nb c (latA s)) → NotTypeIII V F (nb c (latA s)) :=
      fun hA' => (corner_sides_disj hA' hB.1).elim
    have hTAW := notT3W (t0 := t0) hs0 (hTs (latA s) (Or.inl rfl)) hTsPA
    have hbeh : ∀ i, i0 ≤ i → i < m → cellJ z tf i = nb c s.opp → False := fun i h0 h1 hq => by
      rcases hfar with hA' | _
      · exact behind_free_AB hF hpat (by omega) hd0 hsep hTAW hn2 hzw h0 h1 hq hA' ht0V hzc
      · exact behind_free_BB hF hpat (by omega) hd0 hsep hTAW hn2 hzw h0 h1 hq hbX
          (hBprev ht0V (fun hpd => hB.2 (notT3_pdang hF hs0 hpd hB.1)) i h0)
    rcases touch_outcomeW_pfAB hF hs0 hds hTR hk hcell hcor hpat hsep hT' hneut hTs hzw hzR
        hTsPA hzc hL0 hbeh hi0 hi hj hx1 hx2 with h | h | ⟨ht, ie, h1, h2, h3, h4⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨ht, ie, h1, h2, h3, Or.inl h4⟩)
  have hTsP : ∀ tf, (tf = latA s ∨ tf = latB s) → IsCorner t0 (nb c tf) → NotTypeIII V F (nb c tf) := by
    rintro tf (rfl | rfl) hc
    · by_contra h; exact hA ⟨hc, h⟩
    · by_contra h; exact hB ⟨hc, h⟩
  exact touch_outcomeW_pf hF hs0 hds hTR hk hcell hcor hpat hsep hT' hneut hTs hTsP hzw hzR
    hi0 hi hj hx1 hx2

end dispatch

section dispatchAlt

variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  {s0 t0 : Pt} (hF : Deg2Off V F s0 t0) (hs0 : s0 ∈ V) (hds : deg F s0 = 1)
  (hle : ∀ z, deg F z ≤ 2) (hTR : NoTypeIIIR V F s0 t0) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j))
  (hcor : ∀ j ≤ k + 1, ¬ IsCorner s0 (cellJ c s j) ∧ ¬ IsCorner t0 (cellJ c s j))
  (hpat : StripPat F c s (k + 2))
  (hsep : ¬ Conn F (back1 c s) (front1 c s)) (hT' : NoTypeIIIR V (flipCol F c s (k + 2)) s0 t0)
  (hneut : ncomp V (flipCol F c s (k + 2)) = ncomp V F)
  (hTs : ∀ tf, (tf = latA s ∨ tf = latB s) → IsCell V (nb c tf) → NotTypeIII V F (nb c tf))
  (hTend : ∀ tf, (tf = latA s ∨ tf = latB s) → IsCell V (nb (cellJ c s (k + 1)) tf) →
    NotTypeIII V (flipCol F c s (k + 2)) (nb (cellJ c s (k + 1)) tf))
include hF hs0 hds hle hTR hk hcell hcor hpat hsep hT' hneut hTs hTend

omit hds hle hT' hneut hTend in
-- **`alt_touch` without `hTsP`** (dispatch as in `touch_outcomeW_pfD`; no condition needed).
--
theorem alt_touch_pfD {w : Pt} {tw : Side} (hwc : IsCell V w) (l1 : lat1 w tw ∈ F)
    (l2 : lat2 w tw ∈ F) (bw : back w tw ∉ F) (fw : front w tw ∉ F) {j : ℕ} (hj : j < k + 2)
    {x : Edge} (hx1 : x ∈ cellE w) (hx2 : x ∈ cellE (cellJ c s j)) :
    w = cellJ c s (k + 1) ∨ w = nb (cellJ c s (k + 1)) s := by
  have hDc := corners_deg2 hF hcell hcor
  have hc0 : IsCell V c := by have := hcell 0 (by omega); rwa [cellJ_zero] at this
  have hd0 : ∀ z, IsCorner z c → deg F z = 2 := fun z hz => hDc 0 (by omega) z (by rw [cellJ_zero]; exact hz)
  have hc0t : ¬ IsCorner t0 c := by have := (hcor 0 (by omega)).2; rwa [cellJ_zero] at this
  by_cases hA : IsCorner t0 (nb c (latA s)) ∧ ¬ NotTypeIII V F (nb c (latA s))
  · obtain ⟨hL0, _, _, hn1, _⟩ := phantom_sideA hF hs0 hpat (by omega) hc0 hc0t hd0
      (hTs _ (Or.inl rfl)) hA.1 hA.2
    exact alt_touch_pfA hF hs0 hTR hk hcell hcor hpat hsep hTs
      (fun hB => (corner_sides_disj hA.1 hB).elim) hL0 hn1 hwc l1 l2 bw fw hj hx1 hx2
  by_cases hB : IsCorner t0 (nb c (latB s)) ∧ ¬ NotTypeIII V F (nb c (latB s))
  · obtain ⟨hL0, _, _, hn2, _⟩ := phantom_sideB hF hs0 hpat (by omega) hc0 hc0t hd0
      (hTs _ (Or.inr rfl)) hB.1 hB.2
    exact alt_touch_pfAB hF hs0 hk hcell hcor hpat hsep hTs
      (fun hA' => (corner_sides_disj hA' hB.1).elim) hL0 hn2 hwc l1 l2 bw fw hj hx1 hx2
  have hTsP : ∀ tf, (tf = latA s ∨ tf = latB s) → IsCorner t0 (nb c tf) → NotTypeIII V F (nb c tf) := by
    rintro tf (rfl | rfl) hc
    · by_contra h; exact hA ⟨hc, h⟩
    · by_contra h; exact hB ⟨hc, h⟩
  exact alt_touch_pf hF hs0 hTR hk hcell hcor hpat hsep hTs hTsP
    l1 l2 bw fw hj hx1 hx2

end dispatchAlt

-- **`touch_outcome` without `hTsP`** (pattern from index 0, so configuration B needs nothing more).
--
theorem touch_outcome_pfD {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
    {s0 t0 : Pt} (hF : Deg2Off V F s0 t0) (hs0 : s0 ∈ V) (hds : deg F s0 = 1)
    (_hle : ∀ z, deg F z ≤ 2) (hTR : NoTypeIIIR V F s0 t0) (hk : k % 2 = 0)
    (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j))
    (hcor : ∀ j ≤ k + 1, ¬ IsCorner s0 (cellJ c s j) ∧ ¬ IsCorner t0 (cellJ c s j))
    (hpat : StripPat F c s (k + 2))
    (hsep : ¬ Conn F (back1 c s) (front1 c s)) (hT' : NoTypeIIIR V (flipCol F c s (k + 2)) s0 t0)
    (hneut : ncomp V (flipCol F c s (k + 2)) = ncomp V F)
    (hTs : ∀ tf, (tf = latA s ∨ tf = latB s) → IsCell V (nb c tf) → NotTypeIII V F (nb c tf))
    {z : Pt} {tf : Side} {m : ℕ} (hz : StripPat F z tf m)
    (hzR : ∀ j < m, ¬ IsCorner s0 (cellJ z tf j) ∧ ¬ IsCorner t0 (cellJ z tf j))
    (hzc : ∀ j < m, IsCell V (cellJ z tf j))
    {i j : ℕ} (hi : i < m) (hj : j < k + 2) {x : Edge}
    (hx1 : x ∈ cellE (cellJ z tf i)) (hx2 : x ∈ cellE (cellJ c s j)) :
    (∃ i' < m, cellJ z tf i' = cellJ c s (k + 1)) ∨
      (∃ i' < m, cellJ z tf i' = nb (cellJ c s (k + 1)) s) ∨
      (tf = s.opp ∧ ∃ i0 < m, i0 % 2 = 0 ∧
        (cellJ z tf i0 = nb c (latA s) ∨ cellJ z tf i0 = nb c (latB s))) := by
  rcases touch_outcomeW_pfD hF hs0 hds hTR hk hcell hcor hpat hsep hT' hneut hTs (sig_of_pat hz)
      hzR hzc (fun _ _ i _ ho => by omega) (Nat.zero_le i) hi hj hx1 hx2 with
    ⟨i', _, h1, h2⟩ | ⟨i', _, h1, h2⟩ | ⟨ht, ie, _, h1, h2, h3⟩
  · exact Or.inl ⟨i', h1, h2⟩
  · exact Or.inr (Or.inl ⟨i', h1, h2⟩)
  · exact Or.inr (Or.inr ⟨ht, ie, h1, h2, h3⟩)

end HP

end ULHC
