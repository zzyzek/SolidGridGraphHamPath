/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.HP.Sheffield.ColAfter

/-!
# New critical squares beside a moved column

After a move, a critical square `S_j` beside the moved column (odd `j`, far side light) climbs (or
descends, mirror) along the side line: degree forcing makes the side line a strip up to `S_n`
(`MoveCtx.side_run`); the next square `S_(n+1)` lies beside the old pair's square beyond the
column, so I5 for the old pair (`SideInv`) continues the strip to a pair square, unchanged by the
move (`MoveCtx.transfer`).
-/

namespace ULHC

namespace HP

open Finset Classical

section sidecol

variable {V W : Finset Pt} {d : Pt → ℕ} {H H' : Finset Edge} {FP : List FixedPr} {c : Pt}
  {s : Side} {n : ℕ} {i : FixedPr} {t0 u0 : Pt}

-- The move changes only edges of cells of `V`.
--
lemma MoveCtx.symm_inside (M : MoveCtx V W d H H' FP c s n i t0 u0)
    (hFH : ∀ e ∈ symmDiff H H', e.p ∈ V ∧ e.q ∈ V) :
    ∀ e ∈ symmDiff (lowerCol H c s n) H', e.p ∈ V ∧ e.q ∈ V := by
  intro e he
  by_cases h : ∃ j, 1 ≤ j ∧ j ≤ n ∧ e ∈ cellE (cellJ c s j)
  · obtain ⟨j, _, h2, he'⟩ := h
    exact isEdge_of_cellE (M.cell j (by omega)) he'
  · push Not at h
    have e1 := mem_lowerCol_off (F := H) (c := c) (s := s) (k := n) (e := e) h
    apply hFH
    rw [Finset.mem_symmDiff] at he ⊢
    rw [e1] at he
    exact he

-- `D` is unchanged off the moved squares.
--
lemma MoveCtx.D_off (M : MoveCtx V W d H H' FP c s n i t0 u0) {x : Pt}
    (hx : ¬ ∃ j, 1 ≤ j ∧ j ≤ n ∧ x = cellJ c s j) : D (lowerCol H c s n) H' x = D H H' x := by
  have lat0 := (lat_arc_first M.pat (by have := M.two; omega)).1
  cases ho : outArc H c s
  · rw [ho] at lat0
    rw [lowerCol_D_src H' n M.ev H M.pat (fun j hj => by
      rw [lat_arcA M.pat (by omega), lat0]; rfl) x, ite_eq_right hx, add_zero]
  · rw [ho] at lat0
    rw [lowerCol_D H' n M.ev H M.pat (fun j hj => by
      rw [lat_arcA M.pat (by omega), lat0]; rfl) x, ite_eq_right hx, sub_zero]

lemma MoveCtx.solid1 (M : MoveCtx V W d H H' FP c s n i t0 u0) (_hH' : IsFactor W d H')
    (_hFH : ∀ e ∈ symmDiff H H', e.p ∈ V ∧ e.q ∈ V) (hs : SolidFor V H H') :
    SolidFor V (lowerCol H c s n) H' :=
  SolidFor.of_off hs (fun x hx => M.D_off (fun ⟨j, _, h2, hj⟩ => hx (hj ▸ M.cell j (by omega))))

-- The arc across the side along `s` of `S_k` (outer edges alternating) and of `c` (front light).
--
lemma sideA_arc_eq {F : Finset Edge} {k : ℕ} (hm : outer1 (cellJ c s k) s ∈ F ↔ k % 2 = 0) :
    outArc F (nb (cellJ c s k) (latA s)) s = if s.horiz then !par c else par c := by
  rw [outArc_eq, par_nb, par_cellJ, show sideEdge (nb (cellJ c s k) (latA s)) s =
    outer1 (cellJ c s k) s from (outer1_side_nb _ _).symm]
  by_cases h : k % 2 = 0
  · have h' : outer1 (cellJ c s k) s ∈ F := hm.2 h
    simp only [h', decide_true, show ¬ (k % 2 = 1) by omega, decide_false]
    cases par c <;> cases s.horiz <;> simp
  · have h' : outer1 (cellJ c s k) s ∉ F := fun hh => h (hm.1 hh)
    simp only [h', decide_false, show k % 2 = 1 by omega, decide_true]
    cases par c <;> cases s.horiz <;> simp

lemma sideB_arc_eq {F : Finset Edge} {k : ℕ} (hm : outer2 (cellJ c s k) s ∈ F ↔ k % 2 = 0) :
    outArc F (nb (cellJ c s k) (latB s)) s = if s.horiz then !par c else par c := by
  rw [outArc_eq, par_nb, par_cellJ, show sideEdge (nb (cellJ c s k) (latB s)) s =
    outer2 (cellJ c s k) s from (outer2_side_nb _ _).symm]
  by_cases h : k % 2 = 0
  · have h' : outer2 (cellJ c s k) s ∈ F := hm.2 h
    simp only [h', decide_true, show ¬ (k % 2 = 1) by omega, decide_false]
    cases par c <;> cases s.horiz <;> simp
  · have h' : outer2 (cellJ c s k) s ∉ F := fun hh => h (hm.1 hh)
    simp only [h', decide_false, show k % 2 = 1 by omega, decide_true]
    cases par c <;> cases s.horiz <;> simp

lemma col_arc_eq {F : Finset Edge} (hf : front c s ∉ F) :
    outArc F c s = if s.horiz then !par c else par c := by
  have hf' : sideEdge c s ∉ F := hf
  rw [outArc_eq]; simp only [hf', decide_false]
  cases par c <;> cases s.horiz <;> simp

-- Arcs across the sides along `s` of the side line are all the same.
--
lemma sideA_arc_const {F : Finset Edge} (hF : ∀ k ≤ n, outer1 (cellJ c s k) s ∈ F ↔ k % 2 = 0)
    {j k : ℕ} (hk : k ≤ n) (hj : j ≤ n) :
    outArc F (nb (cellJ c s k) (latA s)) s = outArc F (nb (cellJ c s j) (latA s)) s := by
  have e : ∀ k ≤ n, outArc F (nb (cellJ c s k) (latA s)) s =
      if s.horiz then !par c else par c := by
    intro k hk
    rw [outArc_eq, par_nb, par_cellJ, show sideEdge (nb (cellJ c s k) (latA s)) s =
      outer1 (cellJ c s k) s from (outer1_side_nb _ _).symm]
    have hm := hF k hk
    by_cases h : k % 2 = 0
    · have h' : outer1 (cellJ c s k) s ∈ F := hm.2 h
      simp only [h', decide_true, show ¬ (k % 2 = 1) by omega, decide_false]
      cases par c <;> cases s.horiz <;> simp
    · have h' : outer1 (cellJ c s k) s ∉ F := fun hh => h (hm.1 hh)
      simp only [h', decide_false, show k % 2 = 1 by omega, decide_true]
      cases par c <;> cases s.horiz <;> simp
  rw [e k hk, e j hj]

lemma not_near_sideA (c : Pt) (s : Side) (n : ℕ) : ¬ NearM c s n (nb (cellJ c s (n + 1)) (latA s)) := by
  rintro ⟨k, h1, h2, h | ⟨s', h⟩⟩ <;> obtain ⟨x, y⟩ := c
  · cases s <;> simp [cellJ, nb, latA] at h
  · cases s <;> cases s' <;> simp [cellJ, nb, latA] at h <;> omega

lemma not_near_sideB (c : Pt) (s : Side) (n : ℕ) : ¬ NearM c s n (nb (cellJ c s (n + 1)) (latB s)) := by
  rintro ⟨k, h1, h2, h | ⟨s', h⟩⟩ <;> obtain ⟨x, y⟩ := c
  · cases s <;> simp [cellJ, nb, latB] at h
  · cases s <;> cases s' <;> simp [cellJ, nb, latB] at h <;> omega

lemma not_col_sideA (c : Pt) (s : Side) (k : ℕ) :
    ¬ ∃ j, 1 ≤ j ∧ j ≤ n ∧ nb (cellJ c s k) (latA s) = cellJ c s j := by
  rintro ⟨j, _, _, h⟩; obtain ⟨x, y⟩ := c; cases s <;> simp [cellJ, nb, latA] at h

lemma not_col_sideB (c : Pt) (s : Side) (k : ℕ) :
    ¬ ∃ j, 1 ≤ j ∧ j ≤ n ∧ nb (cellJ c s k) (latB s) = cellJ c s j := by
  rintro ⟨j, _, _, h⟩; obtain ⟨x, y⟩ := c; cases s <;> simp [cellJ, nb, latB] at h

lemma side_line (c : Pt) (s : Side) (j t : ℕ) :
    cellJ (nb (cellJ c s j) (latA s)) s t = nb (cellJ c s (j + t)) (latA s) := by
  rw [← cellJ_side, cellJ_add, cellJ_side]

lemma side_lineB (c : Pt) (s : Side) (j t : ℕ) :
    cellJ (nb (cellJ c s j) (latB s)) s t = nb (cellJ c s (j + t)) (latB s) := by
  rw [← cellJ_sideB, cellJ_add, cellJ_sideB]

-- **A new critical square beside the moved column (side `latA`) has a column ending at a pair.**
--
theorem MoveCtx.sideA_col (M : MoveCtx V W d H H' FP c s n i t0 u0) (hH' : IsFactor W d H')
    (hFH : ∀ e ∈ symmDiff H H', e.p ∈ V ∧ e.q ∈ V) (hs : SolidFor V H H')
    (hpos : 0 < sgnD (outArc H c s) (D H H' c)) {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ n)
    (hjo : j % 2 = 1) (hfar : lat1 (nb (cellJ c s j) (latA s)) s ∉ lowerCol H c s n)
    (hrel : 0 < sgnD (outArc (lowerCol H c s n) (nb (cellJ c s j) (latA s)) s)
      (D (lowerCol H c s n) H' (nb (cellJ c s j) (latA s)))) :
    ColEnds V (lowerCol H c s n) (fpAfter FP i (npair (outArc H c s) c s))
      (nb (cellJ c s j) (latA s)) s (outArc (lowerCol H c s n) (nb (cellJ c s j) (latA s)) s) := by
  have hO1 : ∀ k ≤ n, outer1 (cellJ c s k) s ∈ (lowerCol H c s n) ↔ k % 2 = 0 := fun k hk => M.outer1_H1 hk
  have hO0 : ∀ k ≤ n, outer1 (cellJ c s k) s ∈ H ↔ k % 2 = 0 := fun k hk =>
    outer1_all M.ev M.two M.pat M.d1 M.d2 M.altB hk
  -- The side line points the move's way.
  --
  have hfc : front c s ∉ H := by
    intro h; have := (M.pat.2.2 0 (by have := M.two; omega)).1; rw [cellJ_zero] at this
    have := (this h).2 (by have := M.two; omega); omega
  have harc : ∀ k ≤ n, outArc (lowerCol H c s n) (nb (cellJ c s k) (latA s)) s = (outArc H c s) := fun k hk => by
    rw [sideA_arc_eq (hO1 k hk), col_arc_eq hfc]
  rw [harc j h2] at hrel ⊢
  -- `D` along the side line, and its cells.
  --
  have hsol := M.solid1 hH' hFH hs
  have hD : ∀ t ≤ n + 1 - j, sgnD (outArc H c s) (D (lowerCol H c s n) H' (nb (cellJ c s j) (latA s))) ≤
      sgnD (outArc H c s) (D (lowerCol H c s n) H' (nb (cellJ c s (j + t)) (latA s))) := by
    intro t ht
    have fr : ∀ t' < t, outArc (lowerCol H c s n) (cellJ (nb (cellJ c s j) (latA s)) s t') s = (outArc H c s) := by
      intro t' ht'; rw [side_line]; exact harc (j + t') (by omega)
    cases ho : (outArc H c s)
    · rw [ho] at fr
      have := D_anti_row M.factor hH' (c := nb (cellJ c s j) (latA s)) (s := s) t fr
      rw [cellJ_zero, side_line] at this
      simp only [sgnD, Bool.false_eq_true, ↓reduceIte]; omega
    · rw [ho] at fr
      have := D_mono_row M.factor hH' (c := nb (cellJ c s j) (latA s)) (s := s) t fr
      rw [cellJ_zero, side_line] at this
      simp only [sgnD, ↓reduceIte]; omega
  have hcell : ∀ t ≤ n + 1 - j, IsCell V (nb (cellJ c s (j + t)) (latA s)) := by
    intro t ht
    by_contra hc
    have := hD t ht
    rw [hsol _ hc] at this
    simp only [sgnD] at this hrel
    split_ifs at this hrel <;> omega
  -- The run up the side line, then the old pair's I5 strip.
  --
  obtain ⟨hrun, hl1, hl2⟩ := M.side_run h1 h2 hjo (fun k hk1 hk2 => by
      have := hcell (k - j) (by omega); rwa [show j + (k - j) = k by omega] at this) hfar
  have hSc : IsCell V (nb (cellJ c s (n + 1)) (latA s)) := by
    have := hcell (n + 1 - j) le_rfl; rwa [show j + (n + 1 - j) = n + 1 by omega] at this
  have hSn : ¬ NearM c s n (nb (cellJ c s (n + 1)) (latA s)) := not_near_sideA c s n
  have hDS : D (lowerCol H c s n) H' (nb (cellJ c s (n + 1)) (latA s)) = D H H' (nb (cellJ c s (n + 1)) (latA s)) := M.D_off (not_col_sideA c s (n + 1))
  have hDS' : 0 < sgnD (outArc H c s) (D H H' (nb (cellJ c s (n + 1)) (latA s))) := by
    have := hD (n + 1 - j) le_rfl
    rw [show j + (n + 1 - j) = n + 1 by omega] at this
    rw [← hDS]; omega
  have hbS : back (nb (cellJ c s (n + 1)) (latA s)) s ∈ H := by
    have := outer1_side_nb_next (cellJ c s n) s
    rw [nb_cellJ] at this
    show sideEdge (nb (cellJ c s (n + 1)) (latA s)) s.opp ∈ H
    rw [← this]; exact (hO0 n le_rfl).2 M.ev
  have hl1H : lat1 (nb (cellJ c s (n + 1)) (latA s)) s ∉ H := by
    rw [lat1_eq]; rw [lat1_eq] at hl1; rwa [← side_after hSn]
  have hl2H : lat2 (nb (cellJ c s (n + 1)) (latA s)) s ∉ H := by
    rw [lat2_eq]; rw [lat2_eq] at hl2; rwa [← side_after hSn]
  have harrS : outArc H (nb (cellJ c s (n + 1)) (latA s)) s.opp = !(outArc H c s) := by
    have e1 : nb (nb (cellJ c s n) (latA s)) s = (nb (cellJ c s (n + 1)) (latA s)) := by rw [nb_side_comm, nb_cellJ]
    rw [← e1, outArc_nb_opp]
    congr 1
    rw [outArc_congr (F' := (lowerCol H c s n)) (by
      rw [show sideEdge (nb (cellJ c s n) (latA s)) s = outer1 (cellJ c s n) s from
        (outer1_side_nb _ _).symm, outer_after1])]
    exact harc n le_rfl
  have hupS : ColEnds V H FP (nb (cellJ c s (n + 1)) (latA s)) s (outArc H c s) := by
    have hi := M.hi
    have hside := M.inv.side i hi (latA s)
    rcases M.po with ⟨hc, g1, g2⟩ | ⟨hc, g1, g2⟩
    · have his : i.s = s.opp := by
        apply nb_inj_side (x := cellJ c s (n + 1))
        have : nb i.bot i.s = i.top := rfl
        rw [g2] at this; rw [this, g1, nb_cellJ_opp]
      have h := (hside (Or.inl (by rw [his, latA_opp]))).1
      rw [g2, his, opp_opp] at h
      have hDt : 0 < D H H' i.top := by
        have := M.Dn hH' hpos; rw [hc] at this; rw [g1]; simpa [sgnD] using this
      rw [hc] at harrS hDS'
      rw [hc]
      exact h hDt hSc hbS hl1H hl2H (by simpa using harrS) (by simpa [sgnD] using hDS')
    · have his : i.s = s := by
        apply nb_inj_side (x := cellJ c s n)
        have : nb i.bot i.s = i.top := rfl
        rw [g1] at this; rw [this, g2, nb_cellJ]
      have h := (hside (Or.inl (by rw [his]))).2
      rw [g2, his] at h
      have hDb : D H H' i.bot < 0 := by
        have := M.Dn hH' hpos; rw [hc] at this; rw [g1]; simpa [sgnD] using this
      rw [hc] at harrS hDS'
      rw [hc]
      exact h hDb hSc hbS hl1H hl2H (by simpa using harrS) (by simpa [sgnD] using hDS')
  have htr := M.transfer hH' hpos hSn hbS harrS hDS' hupS
  obtain ⟨m', hcells', hpat', jj, hjj, hend'⟩ := htr
  -- Concatenate.
  --
  have hS : cellJ (nb (cellJ c s j) (latA s)) s (n + 1 - j) = (nb (cellJ c s (n + 1)) (latA s)) := by
    rw [side_line, show j + (n + 1 - j) = n + 1 by omega]
  have heven : (n + 1 - j) % 2 = 0 := by have := M.ev; omega
  refine ⟨(n + 1 - j) + m', fun t ht => ?_, ?_, jj, hjj, ?_⟩
  · rcases Nat.lt_or_ge t (n + 1 - j) with h | h
    · rw [side_line]; exact hcell t (by omega)
    · have := hcells' (t - (n + 1 - j)) (by omega)
      rwa [← hS, cellJ_add, show n + 1 - j + (t - (n + 1 - j)) = t by omega] at this
  · rw [show n + 1 - j + m' + 1 = (n + 1 - j) + (m' + 1) by omega]
    apply stripPat_append heven (by omega) hrun
    rw [hS]; exact hpat'
  · rcases hend' with ⟨h1', h2', h3'⟩ | ⟨h1', h2', h3'⟩
    · left; refine ⟨h1', ?_, h3'⟩
      rw [h2', ← hS, cellJ_add]; congr 1
    · right; refine ⟨h1', ?_, h3'⟩
      rw [h2', ← hS, cellJ_add]

-- **A new critical square beside the moved column (side `latB`) has a column ending at a pair.**
--
theorem MoveCtx.sideB_col (M : MoveCtx V W d H H' FP c s n i t0 u0) (hH' : IsFactor W d H')
    (hFH : ∀ e ∈ symmDiff H H', e.p ∈ V ∧ e.q ∈ V) (hs : SolidFor V H H')
    (hpos : 0 < sgnD (outArc H c s) (D H H' c)) {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ n)
    (hjo : j % 2 = 1) (hfar : lat2 (nb (cellJ c s j) (latB s)) s ∉ lowerCol H c s n)
    (hrel : 0 < sgnD (outArc (lowerCol H c s n) (nb (cellJ c s j) (latB s)) s)
      (D (lowerCol H c s n) H' (nb (cellJ c s j) (latB s)))) :
    ColEnds V (lowerCol H c s n) (fpAfter FP i (npair (outArc H c s) c s))
      (nb (cellJ c s j) (latB s)) s (outArc (lowerCol H c s n) (nb (cellJ c s j) (latB s)) s) := by
  have hO1 : ∀ k ≤ n, outer2 (cellJ c s k) s ∈ (lowerCol H c s n) ↔ k % 2 = 0 := fun k hk => M.outer2_H1 hk
  have hO0 : ∀ k ≤ n, outer2 (cellJ c s k) s ∈ H ↔ k % 2 = 0 := fun k hk =>
    outer2_all M.ev M.two M.pat M.d1 M.d2 M.altB hk
  -- The side line points the move's way.
  --
  have hfc : front c s ∉ H := by
    intro h; have := (M.pat.2.2 0 (by have := M.two; omega)).1; rw [cellJ_zero] at this
    have := (this h).2 (by have := M.two; omega); omega
  have harc : ∀ k ≤ n, outArc (lowerCol H c s n) (nb (cellJ c s k) (latB s)) s = (outArc H c s) := fun k hk => by
    rw [sideB_arc_eq (hO1 k hk), col_arc_eq hfc]
  rw [harc j h2] at hrel ⊢
  -- `D` along the side line, and its cells.
  --
  have hsol := M.solid1 hH' hFH hs
  have hD : ∀ t ≤ n + 1 - j, sgnD (outArc H c s) (D (lowerCol H c s n) H' (nb (cellJ c s j) (latB s))) ≤
      sgnD (outArc H c s) (D (lowerCol H c s n) H' (nb (cellJ c s (j + t)) (latB s))) := by
    intro t ht
    have fr : ∀ t' < t, outArc (lowerCol H c s n) (cellJ (nb (cellJ c s j) (latB s)) s t') s = (outArc H c s) := by
      intro t' ht'; rw [side_lineB]; exact harc (j + t') (by omega)
    cases ho : (outArc H c s)
    · rw [ho] at fr
      have := D_anti_row M.factor hH' (c := nb (cellJ c s j) (latB s)) (s := s) t fr
      rw [cellJ_zero, side_lineB] at this
      simp only [sgnD, Bool.false_eq_true, ↓reduceIte]; omega
    · rw [ho] at fr
      have := D_mono_row M.factor hH' (c := nb (cellJ c s j) (latB s)) (s := s) t fr
      rw [cellJ_zero, side_lineB] at this
      simp only [sgnD, ↓reduceIte]; omega
  have hcell : ∀ t ≤ n + 1 - j, IsCell V (nb (cellJ c s (j + t)) (latB s)) := by
    intro t ht
    by_contra hc
    have := hD t ht
    rw [hsol _ hc] at this
    simp only [sgnD] at this hrel
    split_ifs at this hrel <;> omega
  -- The run up the side line, then the old pair's I5 strip.
  --
  obtain ⟨hrun, hl1, hl2⟩ := M.side_runB h1 h2 hjo (fun k hk1 hk2 => by
      have := hcell (k - j) (by omega); rwa [show j + (k - j) = k by omega] at this) hfar
  have hSc : IsCell V (nb (cellJ c s (n + 1)) (latB s)) := by
    have := hcell (n + 1 - j) le_rfl; rwa [show j + (n + 1 - j) = n + 1 by omega] at this
  have hSn : ¬ NearM c s n (nb (cellJ c s (n + 1)) (latB s)) := not_near_sideB c s n
  have hDS : D (lowerCol H c s n) H' (nb (cellJ c s (n + 1)) (latB s)) = D H H' (nb (cellJ c s (n + 1)) (latB s)) := M.D_off (not_col_sideB c s (n + 1))
  have hDS' : 0 < sgnD (outArc H c s) (D H H' (nb (cellJ c s (n + 1)) (latB s))) := by
    have := hD (n + 1 - j) le_rfl
    rw [show j + (n + 1 - j) = n + 1 by omega] at this
    rw [← hDS]; omega
  have hbS : back (nb (cellJ c s (n + 1)) (latB s)) s ∈ H := by
    have := outer2_side_nb_next (cellJ c s n) s
    rw [nb_cellJ] at this
    show sideEdge (nb (cellJ c s (n + 1)) (latB s)) s.opp ∈ H
    rw [← this]; exact (hO0 n le_rfl).2 M.ev
  have hl1H : lat1 (nb (cellJ c s (n + 1)) (latB s)) s ∉ H := by
    rw [lat1_eq]; rw [lat1_eq] at hl1; rwa [← side_after hSn]
  have hl2H : lat2 (nb (cellJ c s (n + 1)) (latB s)) s ∉ H := by
    rw [lat2_eq]; rw [lat2_eq] at hl2; rwa [← side_after hSn]
  have harrS : outArc H (nb (cellJ c s (n + 1)) (latB s)) s.opp = !(outArc H c s) := by
    have e1 : nb (nb (cellJ c s n) (latB s)) s = (nb (cellJ c s (n + 1)) (latB s)) := by rw [nb_sideB_comm, nb_cellJ]
    rw [← e1, outArc_nb_opp]
    congr 1
    rw [outArc_congr (F' := (lowerCol H c s n)) (by
      rw [show sideEdge (nb (cellJ c s n) (latB s)) s = outer2 (cellJ c s n) s from
        (outer2_side_nb _ _).symm, outer_after2])]
    exact harc n le_rfl
  have hupS : ColEnds V H FP (nb (cellJ c s (n + 1)) (latB s)) s (outArc H c s) := by
    have hi := M.hi
    have hside := M.inv.side i hi (latB s)
    rcases M.po with ⟨hc, g1, g2⟩ | ⟨hc, g1, g2⟩
    · have his : i.s = s.opp := by
        apply nb_inj_side (x := cellJ c s (n + 1))
        have : nb i.bot i.s = i.top := rfl
        rw [g2] at this; rw [this, g1, nb_cellJ_opp]
      have h := (hside (Or.inr (by rw [his]; cases s <;> rfl))).1
      rw [g2, his, opp_opp] at h
      have hDt : 0 < D H H' i.top := by
        have := M.Dn hH' hpos; rw [hc] at this; rw [g1]; simpa [sgnD] using this
      rw [hc] at harrS hDS'
      rw [hc]
      exact h hDt hSc hbS hl1H hl2H (by simpa using harrS) (by simpa [sgnD] using hDS')
    · have his : i.s = s := by
        apply nb_inj_side (x := cellJ c s n)
        have : nb i.bot i.s = i.top := rfl
        rw [g1] at this; rw [this, g2, nb_cellJ]
      have h := (hside (Or.inr (by rw [his]))).2
      rw [g2, his] at h
      have hDb : D H H' i.bot < 0 := by
        have := M.Dn hH' hpos; rw [hc] at this; rw [g1]; simpa [sgnD] using this
      rw [hc] at harrS hDS'
      rw [hc]
      exact h hDb hSc hbS hl1H hl2H (by simpa using harrS) (by simpa [sgnD] using hDS')
  have htr := M.transfer hH' hpos hSn hbS harrS hDS' hupS
  obtain ⟨m', hcells', hpat', jj, hjj, hend'⟩ := htr
  -- Concatenate.
  --
  have hS : cellJ (nb (cellJ c s j) (latB s)) s (n + 1 - j) = (nb (cellJ c s (n + 1)) (latB s)) := by
    rw [side_lineB, show j + (n + 1 - j) = n + 1 by omega]
  have heven : (n + 1 - j) % 2 = 0 := by have := M.ev; omega
  refine ⟨(n + 1 - j) + m', fun t ht => ?_, ?_, jj, hjj, ?_⟩
  · rcases Nat.lt_or_ge t (n + 1 - j) with h | h
    · rw [side_lineB]; exact hcell t (by omega)
    · have := hcells' (t - (n + 1 - j)) (by omega)
      rwa [← hS, cellJ_add, show n + 1 - j + (t - (n + 1 - j)) = t by omega] at this
  · rw [show n + 1 - j + m' + 1 = (n + 1 - j) + (m' + 1) by omega]
    apply stripPat_append heven (by omega) hrun
    rw [hS]; exact hpat'
  · rcases hend' with ⟨h1', h2', h3'⟩ | ⟨h1', h2', h3'⟩
    · left; refine ⟨h1', ?_, h3'⟩
      rw [h2', ← hS, cellJ_add]; congr 1
    · right; refine ⟨h1', ?_, h3'⟩
      rw [h2', ← hS, cellJ_add]

lemma crit_lats {F : Finset Edge} {q : Pt} {s' : Side} (h : CriticalIn F q s') :
    lat1 q s' ∉ F ∧ lat2 q s' ∉ F := by
  obtain ⟨hb, hf, hn, _⟩ := h
  exact ⟨fun h' => hn ((ends_lat1 q s').conn h'),
    fun h' => hn (hb.trans (((ends_lat2 q s').conn h').trans hf.symm))⟩

-- `D` on the moved column, after the move, measured in the move's direction.
--
lemma MoveCtx.D_on (M : MoveCtx V W d H H' FP c s n i t0 u0) {k : ℕ} (h1 : 1 ≤ k) (h2 : k ≤ n) :
    sgnD (outArc H c s) (D (lowerCol H c s n) H' (cellJ c s k)) =
      sgnD (outArc H c s) (D H H' (cellJ c s k)) - 2 := by
  have lat0 := (lat_arc_first M.pat (by have := M.two; omega)).1
  have hex : ∃ j, 1 ≤ j ∧ j ≤ n ∧ cellJ c s k = cellJ c s j := ⟨k, h1, h2, rfl⟩
  cases ho : outArc H c s
  · rw [ho] at lat0
    rw [lowerCol_D_src H' n M.ev H M.pat (fun j hj => by
      rw [lat_arcA M.pat (by omega), lat0]; rfl) _, ite_eq_left hex]
    simp [sgnD]; ring
  · rw [ho] at lat0
    rw [lowerCol_D H' n M.ev H M.pat (fun j hj => by
      rw [lat_arcA M.pat (by omega), lat0]; rfl) _, ite_eq_left hex]
    simp [sgnD]

-- `D` along the moved column, before the move.
--
lemma MoveCtx.D_col (M : MoveCtx V W d H H' FP c s n i t0 u0) (hH' : IsFactor W d H') {k : ℕ}
    (hk : k ≤ n) :
    sgnD (outArc H c s) (D H H' c) ≤ sgnD (outArc H c s) (D H H' (cellJ c s k)) := by
  have fr : ∀ j < k, outArc H (cellJ c s j) s = outArc H c s := fun j hj =>
    front_arc M.pat (by omega)
  cases ho : outArc H c s
  · rw [ho] at fr
    have := D_anti_row M.hH hH' k fr
    rw [cellJ_zero] at this
    simp only [sgnD, Bool.false_eq_true, ↓reduceIte]; omega
  · rw [ho] at fr
    have := D_mono_row M.hH hH' (c := c) (s := s) k fr
    rw [cellJ_zero] at this
    simp only [sgnD, ↓reduceIte]; omega

lemma sgnD_two {o : Bool} {F G : Finset Edge} {x : Pt} (h : 0 < sgnD o (D F G x)) :
    2 ≤ sgnD o (D F G x) := by
  obtain ⟨k, hk⟩ := D_even F G x
  cases o <;> simp only [sgnD, Bool.false_eq_true, ↓reduceIte] at h ⊢ <;> omega

end sidecol

end HP

end ULHC
