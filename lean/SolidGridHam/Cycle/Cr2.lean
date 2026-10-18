/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import SolidGridHam.Cycle.Created

@[expose] public section

/-!
# The class-based link rule

For an even strip `b` with end cell `u`, a strip `c` is *created* by `b` when the start
corners `x = back1 c`, `y = front1 c` are in one class of `G` but in different classes of
`G ⊕ u` (the end cell flipped alone).

* `created_step`: if `b` is a proper even strip of `G`, a pair separated by the split at `u`
  (and joined in `G`) stays separated in `G ⊕ b`. The start merge of a proper strip joins
  two classes of `G`, never two pieces of one class.
* `flip_alt_count`: flipping an alternating cell with dark lateral sides changes the count
  by +1 when those sides are in one class, by −1 otherwise.
* `split_symm`: for two such cells `u`, `v` without a common side, `v`'s lateral sides are
  split apart by flipping `u` exactly when `u`'s are split apart by flipping `v`.
-/

namespace SolidGridHam

open Finset Classical

section step

variable {V : Finset Pt} {G : Finset Edge} {c : Pt} {s : Side} {k : ℕ}

theorem created_step (hk : k % 2 = 0) (hG : Deg2 V G)
    (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat G c s (k + 2))
    (hsep : ¬ Conn G (back1 c s) (front1 c s))
    (hsame : Conn G (back1 (cellJ c s (k + 1)) s) (back2 (cellJ c s (k + 1)) s))
    {x y : Pt} (hxy : Conn G x y) (hsplit : ¬ Conn (flip G (cellJ c s (k + 1))) x y)
    (hx : ¬ IsMid c s k x) (hy : ¬ IsMid c s k y) :
    ¬ Conn (flipCol G c s (k + 2)) x y := by
  obtain ⟨F1, hF1, _, _, hrel, _, hodd⟩ := strip_even_rel k hk G hG hcell hpat hsep hsame
  rw [hodd x y hx hy]
  subst hF1
  rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
  · exact hsplit h
  · exact hsep (((hrel _ _ h1).symm.trans hxy).trans (hrel _ _ h2).symm)
  · exact hsep (((hrel _ _ h2).trans hxy.symm).trans (hrel _ _ h1))

end step

section count

variable {V : Finset Pt} {G : Finset Edge}

-- Flipping an alternating cell with dark lateral sides.
--
theorem flip_alt_count (hG : Deg2 V G) {u : Pt} {s : Side} (hu : IsCell V u)
    (l1 : lat1 u s ∈ G) (l2 : lat2 u s ∈ G) (hb : back u s ∉ G) (hf : front u s ∉ G) :
    (Conn G (back1 u s) (back2 u s) → ncomp V (flip G u) = ncomp V G + 1) ∧
      (¬ Conn G (back1 u s) (back2 u s) → ncomp V (flip G u) + 1 = ncomp V G) := by
  obtain ⟨ub1, ub2, uf1, uf2⟩ := isCell_corners hu s
  have hE := mkLat_cellE u s
  rw [(mkLat u s).flip_eq hE l1 l2 hb hf]
  refine ⟨fun hsame => ?_, fun hn => ?_⟩
  · exact ((mkLat u s).split hG.1 ub1 uf1 ub2 uf2 l1 l2 hb
      (fun z hz => by rcases hz with hz | hz
                      · exact hG.class ub1 hz
                      · exact hG.class ub2 hz) hsame hG.le_two
      (fun H h1 h2 h3 h4 h5 => planar_lat H u s h1 h2 h3 h4 h5)).1
  · exact ((mkLat u s).merge hG.1 ub1 ub2 l1 l2
      (fun z hz => by rcases hz with hz | hz
                      · exact hG.class ub1 hz
                      · exact hG.class ub2 hz) hn).1

lemma flip_flip_comm (G : Finset Edge) (u v : Pt) : flip (flip G u) v = flip (flip G v) u := by
  unfold flip
  rw [symmDiff_assoc, symmDiff_comm (cellE u), ← symmDiff_assoc]

lemma mem_flip_off {G : Finset Edge} {u : Pt} {e : Edge} (h : e ∉ cellE u) :
    e ∈ flip G u ↔ e ∈ G := by
  rw [mem_flip_iff]; tauto

-- Two end cells without a common side split each other symmetrically.
--
theorem split_symm (hG : Deg2 V G) {u v : Pt} {s tf : Side} (hu : IsCell V u) (hv : IsCell V v)
    (lu1 : lat1 u s ∈ G) (lu2 : lat2 u s ∈ G) (bu : back u s ∉ G) (fu : front u s ∉ G)
    (lv1 : lat1 v tf ∈ G) (lv2 : lat2 v tf ∈ G) (bv : back v tf ∉ G) (fv : front v tf ∉ G)
    (hsu : Conn G (back1 u s) (back2 u s)) (hsv : Conn G (back1 v tf) (back2 v tf))
    (hdisj : ∀ e, e ∈ cellE u → e ∉ cellE v) :
    Conn (flip G u) (back1 v tf) (back2 v tf) ↔ Conn (flip G v) (back1 u s) (back2 u s) := by
  have hdisj' : ∀ e, e ∈ cellE v → e ∉ cellE u := fun e h1 h2 => hdisj e h2 h1
  have mv : ∀ e, e ∈ cellE v → (e ∈ flip G u ↔ e ∈ G) := fun e he => mem_flip_off (hdisj' e he)
  have mu : ∀ e, e ∈ cellE u → (e ∈ flip G v ↔ e ∈ G) := fun e he => mem_flip_off (hdisj e he)
  have sv : ∀ e, e = lat1 v tf ∨ e = lat2 v tf ∨ e = back v tf ∨ e = front v tf → e ∈ cellE v := by
    intro e he; rw [cellE_frame v tf]; rcases he with rfl | rfl | rfl | rfl <;> simp
  have su : ∀ e, e = lat1 u s ∨ e = lat2 u s ∨ e = back u s ∨ e = front u s → e ∈ cellE u := by
    intro e he; rw [cellE_frame u s]; rcases he with rfl | rfl | rfl | rfl <;> simp
  have hGu : Deg2 V (flip G u) := hG.flip (mkLat u s) hu (mkLat_cellE u s) lu1 lu2 bu fu
  have hGv : Deg2 V (flip G v) := hG.flip (mkLat v tf) hv (mkLat_cellE v tf) lv1 lv2 bv fv
  have cu := (flip_alt_count hG hu lu1 lu2 bu fu).1 hsu
  have cv := (flip_alt_count hG hv lv1 lv2 bv fv).1 hsv
  have A := flip_alt_count hGu hv ((mv _ (sv _ (Or.inl rfl))).2 lv1)
    ((mv _ (sv _ (Or.inr (Or.inl rfl)))).2 lv2)
    (fun h => bv ((mv _ (sv _ (Or.inr (Or.inr (Or.inl rfl))))).1 h))
    (fun h => fv ((mv _ (sv _ (Or.inr (Or.inr (Or.inr rfl))))).1 h))
  have B := flip_alt_count hGv hu ((mu _ (su _ (Or.inl rfl))).2 lu1)
    ((mu _ (su _ (Or.inr (Or.inl rfl)))).2 lu2)
    (fun h => bu ((mu _ (su _ (Or.inr (Or.inr (Or.inl rfl))))).1 h))
    (fun h => fu ((mu _ (su _ (Or.inr (Or.inr (Or.inr rfl))))).1 h))
  rw [flip_flip_comm] at A
  constructor
  · intro h
    by_contra h'
    have := A.1 h; have := B.2 h'; omega
  · intro h
    by_contra h'
    have := A.2 h'; have := B.1 h; omega

end count

/-! ## One-strip invariance of the link rule, far case -/

lemma alt_of_lats {F : Finset Edge} {u : Pt} {tf : Side} (l1 : lat1 u tf ∈ F) (l2 : lat2 u tf ∈ F)
    (b : back u tf ∉ F) (f : front u tf ∉ F) : Alt F u := by
  rw [lat1_eq] at l1; rw [lat2_eq] at l2
  simp only [back, front] at b f
  cases tf <;> simp only [latA, latB, sideEdge, Side.opp] at l1 l2 b f <;> unfold Alt <;> tauto

lemma flipCol_flip_comm (G : Finset Edge) (c : Pt) (s : Side) (u : Pt) :
    ∀ n, flip (flipCol G c s n) u = flipCol (flip G u) c s n := by
  intro n
  induction n generalizing G with
  | zero => rfl
  | succ n ih =>
    simp only [flipCol]
    rw [ih, flip_flip_comm]

lemma stripPat_congr {G G' : Finset Edge} {c : Pt} {s : Side} {n : ℕ}
    (h : ∀ j < n + 1, ∀ e ∈ cellE (cellJ c s j), (e ∈ G' ↔ e ∈ G)) :
    StripPat G' c s (n + 1) ↔ StripPat G c s (n + 1) := by
  have hb : back c s ∈ cellE (cellJ c s 0) := back_mem_zero c s
  unfold StripPat
  rw [h 0 (by omega) _ hb]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, fun j hj => ?_, fun j hj => ?_⟩
    · rw [← h j hj _ (lat1_mem_self c s j), ← h j hj _ (lat2_mem_self c s j)]; exact h2 j hj
    · rw [← h j hj _ (front_mem_self c s j)]; exact h3 j hj
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, fun j hj => ?_, fun j hj => ?_⟩
    · rw [h j hj _ (lat1_mem_self c s j), h j hj _ (lat2_mem_self c s j)]; exact h2 j hj
    · rw [h j hj _ (front_mem_self c s j)]; exact h3 j hj

section osi

variable {V : Finset Pt} {G : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hG : Deg2 V G) (hk : k % 2 = 0) (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j))
  (hpat : StripPat G c s (k + 2)) (hsep : ¬ Conn G (back1 c s) (front1 c s))
  (hsame : Conn G (back1 (cellJ c s (k + 1)) s) (back2 (cellJ c s (k + 1)) s))
  (hT' : NoTypeIII V (flipCol G c s (k + 2)))
include hG hk hcell hpat hsep hsame hT'

-- **Far case.** `u` is the end cell of another even strip, far from `a = (c, s, k + 2)`;
-- `x, y` are the start corners of a strip created by `u`. After flipping `a`, either `x, y`
-- are still joined and still split by `u`, or `a`'s own end cell already splits them.
--
-- The split half: after flipping `a`, `u` still splits `x, y`.
--
theorem osi_split {u : Pt} {tf : Side} (hu : IsCell V u)
    (lu1 : lat1 u tf ∈ G) (lu2 : lat2 u tf ∈ G) (bu : back u tf ∉ G) (fu : front u tf ∉ G)
    (hsu : Conn G (back1 u tf) (back2 u tf))
    (hfar : ∀ j ≤ k + 1, ∀ e ∈ cellE u, e ∉ cellE (cellJ c s j))
    (hmu1 : ¬ IsMid c s k (back1 u tf)) (hmu2 : ¬ IsMid c s k (back2 u tf))
    {x y : Pt} (hxy : Conn G x y) (hsplit : ¬ Conn (flip G u) x y)
    (hx : ¬ IsMid c s k x) (hy : ¬ IsMid c s k y) :
    ¬ Conn (flip (flipCol G c s (k + 2)) u) x y := by
  obtain ⟨F1, hF1, _, _, hrel, _, hodd⟩ := strip_even_rel k hk G hG hcell hpat hsep hsame
  rw [flipCol_flip_comm]
  set H := flip G u
  -- `u`'s flip is a split of `G`: connections of `H` are connections of `G`.
  obtain ⟨ub1, ub2, uf1, uf2⟩ := isCell_corners hu tf
  have hE := mkLat_cellE u tf
  obtain ⟨_, hHG, _⟩ := (mkLat u tf).split hG.1 ub1 uf1 ub2 uf2 lu1 lu2 bu
    (fun z hz => by rcases hz with hz | hz
                    · exact hG.class ub1 hz
                    · exact hG.class ub2 hz) hsu hG.le_two
    (fun K h1 h2 h3 h4 h5 => planar_lat K u tf h1 h2 h3 h4 h5)
  rw [← (mkLat u tf).flip_eq hE lu1 lu2 bu fu] at hHG
  have hH : Deg2 V H := hG.flip (mkLat u tf) hu hE lu1 lu2 bu fu
  -- `a` is still a proper strip of `H`.
  have hcong : ∀ j < k + 2, ∀ e ∈ cellE (cellJ c s j), (e ∈ H ↔ e ∈ G) := by
    intro j hj e he
    exact mem_flip_off (fun h => hfar j (by omega) e h he)
  have hpatH : StripPat H c s (k + 2) := (stripPat_congr hcong).2 hpat
  have hsepH : ¬ Conn H (back1 c s) (front1 c s) := fun h => hsep (hHG _ _ h)
  set ua := cellJ c s (k + 1)
  by_cases hsameH : Conn H (back1 ua s) (back2 ua s)
  · obtain ⟨F2, hF2, _, _, hrel2, _, hodd2⟩ := strip_even_rel k hk H hH hcell hpatH hsepH hsameH
    rw [hodd2 x y hx hy]
    rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact hsplit (hrel2 _ _ h)
    · exact hsep (((hHG _ _ (hrel2 _ _ h1)).symm.trans hxy).trans (hHG _ _ (hrel2 _ _ h2)).symm)
    · exact hsep (((hHG _ _ (hrel2 _ _ h2)).trans hxy.symm).trans (hHG _ _ (hrel2 _ _ h1)))
  · -- `a`'s end cell is split by `u`: then `u` is split by `a`'s end cell, and `u` would be a
    -- Type III cell of `G ⊕ a`.
    exfalso
    have hcua := hcell (k + 1) le_rfl
    obtain ⟨_, hl, hf⟩ := hpat
    have la1 : lat1 ua s ∈ G := (hl (k + 1) (by omega)).1.2 (by omega)
    have la2 : lat2 ua s ∈ G := (hl (k + 1) (by omega)).2.2 (by omega)
    have ba : back ua s ∉ G := by
      rw [back_cellJ_succ]; intro h; have := (hf k (by omega)).1 h; omega
    have fa : front ua s ∉ G := by
      intro h; have := (hf (k + 1) (by omega)).1 h; omega
    have hsym := split_symm hG hu hcua lu1 lu2 bu fu la1 la2 ba fa hsu hsame
      (fun e h1 h2 => hfar (k + 1) le_rfl e h1 h2)
    have hn : ¬ Conn (flip G ua) (back1 u tf) (back2 u tf) := fun h => hsameH (hsym.2 h)
    have hn' : ¬ Conn (flipCol G c s (k + 2)) (back1 u tf) (back2 u tf) := by
      rw [hodd _ _ hmu1 hmu2]
      rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact hn (hF1 ▸ h)
      · exact hsep (((hrel _ _ h1).symm.trans hsu).trans (hrel _ _ h2).symm)
      · exact hsep (((hrel _ _ h2).trans hsu.symm).trans (hrel _ _ h1))
    -- `u` is alternating in `G ⊕ a` with the same sides.
    have hc' : ∀ e ∈ cellE u, (e ∈ flipCol G c s (k + 2) ↔ e ∈ G) := by
      intro e he
      rw [mem_flipCol, nOn_zero c s (fun j hj => hfar j (by omega) e he)]
      simp
    have mem : ∀ e, e = lat1 u tf ∨ e = lat2 u tf ∨ e = back u tf ∨ e = front u tf → e ∈ cellE u := by
      intro e he; rw [cellE_frame u tf]; rcases he with rfl | rfl | rfl | rfl <;> simp
    have l1' := (hc' _ (mem _ (Or.inl rfl))).2 lu1
    have l2' := (hc' _ (mem _ (Or.inr (Or.inl rfl)))).2 lu2
    have b' : back u tf ∉ flipCol G c s (k + 2) :=
      fun h => bu ((hc' _ (mem _ (Or.inr (Or.inr (Or.inl rfl))))).1 h)
    have f' : front u tf ∉ flipCol G c s (k + 2) :=
      fun h => fu ((hc' _ (mem _ (Or.inr (Or.inr (Or.inr rfl))))).1 h)
    have ha : Alt (flipCol G c s (k + 2)) u := alt_of_lats l1' l2' b' f'
    have hall : AllConn (flipCol G c s (k + 2)) u := by
      unfold AllConn; exact alt_corners_conn' (V := V) (hT' u hu) ha
    exact hn' (frame_of_allConn hall tf).1

theorem osi_far {u : Pt} {tf : Side} (hu : IsCell V u)
    (lu1 : lat1 u tf ∈ G) (lu2 : lat2 u tf ∈ G) (bu : back u tf ∉ G) (fu : front u tf ∉ G)
    (hsu : Conn G (back1 u tf) (back2 u tf))
    (hfar : ∀ j ≤ k + 1, ∀ e ∈ cellE u, e ∉ cellE (cellJ c s j))
    (hmu1 : ¬ IsMid c s k (back1 u tf)) (hmu2 : ¬ IsMid c s k (back2 u tf))
    {x y : Pt} (hxy : Conn G x y) (hsplit : ¬ Conn (flip G u) x y)
    (hx : ¬ IsMid c s k x) (hy : ¬ IsMid c s k y) :
    (Conn (flipCol G c s (k + 2)) x y ∧ ¬ Conn (flip (flipCol G c s (k + 2)) u) x y) ∨
      ¬ Conn (flip G (cellJ c s (k + 1))) x y := by
  obtain ⟨F1, hF1, _, _, hrel, _, hodd⟩ := strip_even_rel k hk G hG hcell hpat hsep hsame
  by_cases hC : Conn (flipCol G c s (k + 2)) x y
  · exact Or.inl ⟨hC, osi_split hG hk hcell hpat hsep hsame hT' hu lu1 lu2 bu fu hsu hfar hmu1 hmu2
      hxy hsplit hx hy⟩
  · right
    intro h; exact hC ((hodd x y hx hy).2 (Or.inl (hF1 ▸ h)))

end osi

end SolidGridHam
