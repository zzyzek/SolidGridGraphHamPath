/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import SolidGridHam.Path.E1After

/-!
# Stuck ⇒ minimal (repaired §4.8): the induction

The proof is by induction on `μ = Σ |D H H'|`:
* no movable square: the final count (`count_final`);
* a movable square: a generalized move (`move_step`) keeps `Inv`, the number of pieces and the
  number of fixed pairs, and lowers `μ`.

All parts are proved (docs/STUCK_MINIMAL.md §§20–22).
-/

namespace SolidGridHam

namespace HP

open Finset Classical

section minimal

variable {V W : Finset Pt} {d : Pt → ℕ} {H H' : Finset Edge}

variable {FP : List FixedPr} {c : Pt} {s : Side} {n : ℕ} {i : FixedPr} {t0 u0 : Pt}

-- **The column invariant after a move.**
--
theorem col_after (M : MoveCtx V W d H H' FP c s n i t0 u0) (hH' : IsFactor W d H')
    (hFH : ∀ e ∈ symmDiff H H', e.p ∈ V ∧ e.q ∈ V) (hs : SolidFor V H H')
    (hpos : 0 < sgnD (outArc H c s) (D H H' c)) :
    ∀ q s', IsCell V q → CriticalIn (lowerCol H c s n) q s' →
      back q s' ∈ lowerCol H c s n →
      (∀ j ∈ fpAfter FP i (npair (outArc H c s) c s), q ≠ j.top ∧ q ≠ j.bot) →
      0 < sgnD (outArc (lowerCol H c s n) q s') (D (lowerCol H c s n) H' q) →
      ColEnds V (lowerCol H c s n) (fpAfter FP i (npair (outArc H c s) c s)) q s'
        (outArc (lowerCol H c s n) q s') := by
  intro q s' hq hcrit hb hnp hrel
  have hnpm : npair (outArc H c s) c s ∈ fpAfter FP i (npair (outArc H c s) c s) :=
    (mem_fpAfter M.hi).2 (Or.inl rfl)
  have hlats := crit_lats hcrit
  by_cases hn : NearM c s n q
  · rcases near_cases hn with ⟨k, hk, rfl⟩ | ⟨k, h1, h2, rfl | rfl⟩
    · -- `q` on the moved column.
      exfalso
      rcases (show k = 0 ∨ k = 1 ∨ 2 ≤ k by omega) with rfl | rfl | hk2
      · have := hnp _ hnpm
        rcases npair_sq (outArc H c s) c s with ⟨g1, _⟩ | ⟨g1, _⟩
        · rw [cellJ_zero] at this; exact this.1 g1.symm
        · rw [cellJ_zero] at this; exact this.2 g1.symm
      · have := hnp _ hnpm
        rcases npair_sq (outArc H c s) c s with ⟨_, g2⟩ | ⟨_, g2⟩
        · exact this.2 g2.symm
        · exact this.1 g2.symm
      · have hne := col_ne_H1 M.ev M.two M.pat M.d1 M.d2 M.altB hk2 hk
        rcases side_cases s s' with h | h | h | h <;> subst s'
        · -- frame `s`: the back would be light
          rcases (show k ≤ n ∨ k = n + 1 by omega) with hkn | rfl
          · rcases Nat.mod_two_eq_zero_or_one k with he | ho
            · exact hlats.1 ((lat1_after M.ev M.two M.pat (by omega) hkn).2 he)
            · have : back (cellJ c s k) s = front (cellJ c s (k - 1)) s := by
                have := back_cellJ_succ c s (k - 1); rwa [show k - 1 + 1 = k by omega] at this
              rw [this, front_inner_after M.ev M.two M.pat (by omega) (by omega)] at hb
              omega
          · rw [back_cellJ_succ] at hb; exact frontk_after M.ev M.two M.pat hb
        · -- frame `s.opp`: descending; `D` has the wrong sign
          rcases (show k ≤ n ∨ k = n + 1 by omega) with hkn | rfl
          · rcases Nat.mod_two_eq_zero_or_one k with he | ho
            · rw [lat1_opp] at hlats
              exact hlats.1 ((lat1_after M.ev M.two M.pat (by omega) hkn).2 he)
            · have hkn' : k + 1 ≤ n := by have := M.ev; omega
              have hbk : sideEdge (cellJ c s k) s.opp = front (cellJ c s (k - 1)) s := by
                have := back_cellJ_succ c s (k - 1); rwa [show k - 1 + 1 = k by omega] at this
              have harc : outArc (lowerCol H c s n) (cellJ c s k) s.opp = !outArc H c s := by
                rw [outArc_congr (F' := H) (by
                  rw [hbk, front_inner_after M.ev M.two M.pat (by omega) (by omega),
                    (M.pat.2.2 (k - 1) (by omega))]; omega)]
                have e1 : nb (cellJ c s (k - 1)) s = cellJ c s k := by
                  rw [nb_cellJ, show k - 1 + 1 = k by omega]
                rw [← e1, outArc_nb_opp, front_arc M.pat (by omega)]
              rw [harc] at hrel
              have hon := M.D_on (k := k) (by omega) hkn
              have hcol := M.D_col hH' (k := k) hkn
              have h2 := sgnD_two hpos
              cases ho' : outArc H c s <;> rw [ho'] at hrel hon hcol h2 <;>
                simp only [sgnD, Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.not_true]
                  at hrel hon hcol h2 <;> omega
          · -- `B`: the old pair would carry `D` of both signs
            have hDB := M.D_off (x := cellJ c s (n + 1)) (by
              rintro ⟨j, _, hj2, h⟩; have := cellJ_inj' h; omega)
            have hup := (M.inv.f4 i M.hi).2.2.1
            have hDc := M.Dn hH' hpos
            have hbB : sideEdge (cellJ c s (n + 1)) s.opp = front (cellJ c s n) s :=
              back_cellJ_succ c s n
            have htog : outArc (lowerCol H c s n) (cellJ c s (n + 1)) s.opp =
                !outArc H (cellJ c s (n + 1)) s.opp := by
              apply outArc_toggle
              rw [hbB]
              exact ⟨fun h => absurd h (frontk_after M.ev M.two M.pat),
                fun h => absurd (frontn_mem M.ev M.two M.pat M.d1 M.d2 M.altB) h⟩
            rw [htog, hDB] at hrel
            rcases M.po with ⟨hc, g1, g2⟩ | ⟨hc, g1, g2⟩
            · have his : i.s = s.opp := by
                apply nb_inj_side (x := cellJ c s (n + 1))
                have : nb i.bot i.s = i.top := rfl
                rw [g2] at this; rw [this, g1, nb_cellJ_opp]
              have hupB : outArc H (cellJ c s (n + 1)) s.opp = true := by rw [← g2, ← his]; exact hup
              rw [hupB] at hrel; rw [hc] at hDc
              simp only [sgnD, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hrel hDc
              exact pair_one_side M.hH hH' hup (by show 0 < D H H' i.top; rw [g1]; omega)
                (by rw [g2]; omega)
            · have his : i.s = s := by
                apply nb_inj_side (x := cellJ c s n)
                have : nb i.bot i.s = i.top := rfl
                rw [g1] at this; rw [this, g2, nb_cellJ]
              have hupB : outArc H (cellJ c s (n + 1)) s.opp = false := by
                rw [← nb_cellJ, outArc_nb_opp, ← g1, ← his, hup]; rfl
              rw [hupB] at hrel; rw [hc] at hDc
              simp only [sgnD, Bool.not_false, ↓reduceIte, Bool.false_eq_true] at hrel hDc
              exact pair_one_side M.hH hH' hup (by show 0 < D H H' i.top; rw [g2]; omega)
                (by rw [g1]; omega)
        · -- perpendicular frames: the lateral sides differ
          rcases perp_lats (cellJ c s k) (s := s) (a := latA s) (Or.inl rfl) with
            ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2] at hlats
          · exact hne ⟨fun h => absurd h hlats.1, fun h => absurd h hlats.2⟩
          · exact hne ⟨fun h => absurd h hlats.2, fun h => absurd h hlats.1⟩
        · rcases perp_lats (cellJ c s k) (s := s) (a := latB s) (Or.inr rfl) with
            ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2] at hlats
          · exact hne ⟨fun h => absurd h hlats.1, fun h => absurd h hlats.2⟩
          · exact hne ⟨fun h => absurd h hlats.2, fun h => absurd h hlats.1⟩
    · -- `S_k`
      have hne := sideA_ne M.ev M.two M.pat M.d1 M.d2 M.altB (lowerCol H c s n)
        (fun m _ => outer_after1 m) h1 h2
      rcases side_cases s s' with h | h | h | h <;> subst s'
      · have hodd : k % 2 = 1 := by
          by_contra he
          exact hlats.2 (by rw [side_near]; exact (lat1_after M.ev M.two M.pat h1 h2).2 (by omega))
        exact M.sideA_col hH' hFH hs hpos h1 h2 hodd hlats.1 hrel
      · exfalso
        rw [lat1_opp, lat2_opp] at hlats
        have hodd : k % 2 = 1 := by
          by_contra he
          exact hlats.2 (by rw [side_near]; exact (lat1_after M.ev M.two M.pat h1 h2).2 (by omega))
        have hb' : outer1 (cellJ c s k) s ∈ lowerCol H c s n := by
          rw [← side_front]; have := hb; unfold back at this; rw [opp_opp] at this; exact this
        have := (M.outer1_H1 h2).1 hb'; omega
      · rcases perp_lats (nb (cellJ c s k) (latA s)) (s := s) (a := latA s) (Or.inl rfl) with
          ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2] at hlats
        · exact absurd ⟨fun h => absurd h hlats.1, fun h => absurd h hlats.2⟩ hne
        · exact absurd ⟨fun h => absurd h hlats.2, fun h => absurd h hlats.1⟩ hne
      · rcases perp_lats (nb (cellJ c s k) (latA s)) (s := s) (a := latB s) (Or.inr rfl) with
          ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2] at hlats
        · exact absurd ⟨fun h => absurd h hlats.1, fun h => absurd h hlats.2⟩ hne
        · exact absurd ⟨fun h => absurd h hlats.2, fun h => absurd h hlats.1⟩ hne
    · -- `R_k`
      have hne := sideB_ne M.ev M.two M.pat M.d1 M.d2 M.altB (lowerCol H c s n)
        (fun m _ => outer_after2 m) h1 h2
      rcases side_cases s s' with h | h | h | h <;> subst s'
      · have hodd : k % 2 = 1 := by
          by_contra he
          exact hlats.1 (by rw [sideB_near]; exact (lat2_after M.ev M.two M.pat h1 h2).2 (by omega))
        exact M.sideB_col hH' hFH hs hpos h1 h2 hodd hlats.2 hrel
      · exfalso
        rw [lat1_opp, lat2_opp] at hlats
        have hodd : k % 2 = 1 := by
          by_contra he
          exact hlats.1 (by rw [sideB_near]; exact (lat2_after M.ev M.two M.pat h1 h2).2 (by omega))
        have hb' : outer2 (cellJ c s k) s ∈ lowerCol H c s n := by
          rw [← sideB_front]; have := hb; unfold back at this; rw [opp_opp] at this; exact this
        have := (M.outer2_H1 h2).1 hb'; omega
      · rcases perp_lats (nb (cellJ c s k) (latB s)) (s := s) (a := latA s) (Or.inl rfl) with
          ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2] at hlats
        · exact absurd ⟨fun h => absurd h hlats.1, fun h => absurd h hlats.2⟩ hne
        · exact absurd ⟨fun h => absurd h hlats.2, fun h => absurd h hlats.1⟩ hne
      · rcases perp_lats (nb (cellJ c s k) (latB s)) (s := s) (a := latB s) (Or.inr rfl) with
          ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2] at hlats
        · exact absurd ⟨fun h => absurd h hlats.1, fun h => absurd h hlats.2⟩ hne
        · exact absurd ⟨fun h => absurd h hlats.2, fun h => absurd h hlats.1⟩ hne
  · -- `q` away from the move: its column before the move, transferred.
    have cc : ∀ {u v : Pt}, IsCorner u q → IsCorner v q →
        (Conn (lowerCol H c s n) u v ↔ Conn H u v) := fun hu hv =>
      conn_corners_after M.conn hn hu hv
    have sa := fun (s'' : Side) => side_after (F := H) hn s''
    obtain ⟨k1, k2, k3, k4⟩ := hcrit
    have hcritH : CriticalIn H q s' := by
      refine ⟨(cc (isCorner_back1 q s') (isCorner_back2 q s')).1 k1,
        (cc (isCorner_front1 q s') (isCorner_front2 q s')).1 k2,
        fun h => k3 ((cc (isCorner_back1 q s') (isCorner_front1 q s')).2 h), ?_⟩
      have eb : back q s' ∈ lowerCol H c s n ↔ back q s' ∈ H := sa s'.opp
      have ef : front q s' ∈ lowerCol H c s n ↔ front q s' ∈ H := sa s'
      rw [eb, ef] at k4; exact k4
    have hbH : back q s' ∈ H := (sa s'.opp).1 hb
    have hfH : front q s' ∉ H := by
      rcases hcritH.2.2.2 with ⟨_, h⟩ | ⟨_, h⟩
      · exact h
      · exact absurd hbH h
    have harc : outArc (lowerCol H c s n) q s' = outArc H q s' := outArc_congr (sa s')
    have hDq : D (lowerCol H c s n) H' q = D H H' q := M.D_off (by
      rintro ⟨j, h1, h2, rfl⟩; exact hn ⟨j, h1, h2, Or.inl rfl⟩)
    have hnpH : ∀ p ∈ FP, q ≠ p.top ∧ q ≠ p.bot := by
      intro p hp
      by_cases hpi : p = i
      · subst hpi
        rcases M.pi with ⟨g1, g2⟩ | ⟨g1, g2⟩
        · exact ⟨fun h => hn (by rw [h, g1]; exact M.near_n),
            fun h => hn (by rw [h, g2]; exact M.near_n1)⟩
        · exact ⟨fun h => hn (by rw [h, g2]; exact M.near_n1),
            fun h => hn (by rw [h, g1]; exact M.near_n)⟩
      · exact hnp p ((mem_fpAfter M.hi).2 (Or.inr ⟨hp, hpi⟩))
    rw [harc, hDq] at hrel
    have hce := M.inv.col q s' hq hcritH hbH hnpH hrel
    have harr : outArc H q s'.opp = !(outArc H q s') := by
      rw [bf_arc hbH hfH]; simp
    rw [harc]
    exact M.transfer hH' hpos hn hbH harr hrel hce

-- **I5 after a move.**
--
theorem sideInv_after (M : MoveCtx V W d H H' FP c s n i t0 u0) (hH' : IsFactor W d H')
    (hFH : ∀ e ∈ symmDiff H H', e.p ∈ V ∧ e.q ∈ V) (hs : SolidFor V H H')
    (hpos : 0 < sgnD (outArc H c s) (D H H' c)) :
    SideInv V (lowerCol H c s n) H' (fpAfter FP i (npair (outArc H c s) c s)) :=
  M.sideInv hH' hFH hs hpos

-- **E1's shape after a move.**
--
theorem three_after (M : MoveCtx V W d H H' FP c s n i t0 u0) :
    ∀ f, IsCell V f → Three (lowerCol H c s n) f → TriOK V (lowerCol H c s n) t0 u0 f :=
  M.tri_after

-- Edges leaving `V` are not moved.
--
lemma MoveCtx.out_after (M : MoveCtx V W d H H' FP c s n i t0 u0) :
    ∀ e ∈ lowerCol H c s n, (e.p ∉ V → e.q = t0 ∨ e.q = u0) ∧ (e.q ∉ V → e.p = t0 ∨ e.p = u0) := by
  intro e he
  by_cases h : ∃ j, 1 ≤ j ∧ j ≤ n ∧ e ∈ cellE (cellJ c s j)
  · obtain ⟨j, _, h2, he'⟩ := h
    have := isEdge_of_cellE (M.cell j (by omega)) he'
    exact ⟨fun h' => absurd this.1 h', fun h' => absurd this.2 h'⟩
  · push Not at h
    exact M.inv.out e ((mem_lowerCol_off (F := H) (c := c) (s := s) (k := n) h).1 he)

-- The move lowers `μ`.
--
lemma MoveCtx.mu_lt (M : MoveCtx V W d H H' FP c s n i t0 u0) (hH' : IsFactor W d H')
    (hpos : 0 < sgnD (outArc H c s) (D H H' c)) :
    mu V (lowerCol H c s n) H' < mu V H H' := by
  have hp := M.pat
  have lat0 := (lat_arc_first hp (by have := M.two; omega)).1
  have hcells : ∀ j ≤ n, IsCell V (cellJ c s j) := fun j hj => M.cell j (by omega)
  have fr : ∀ j < n, outArc H (cellJ c s j) s = outArc H c s := fun j hj =>
    front_arc hp (by omega)
  cases ho : outArc H c s
  · rw [ho] at hpos lat0 fr
    simp only [sgnD, Bool.false_eq_true, ↓reduceIte] at hpos
    have h := lowerCol_mu_src (V := V) H' n M.ev H hcells hp (fun j h1 h2 => by
        have := D_anti_row M.hH hH' j (fun j' hj' => fr j' (by omega))
        rw [cellJ_zero] at this; omega)
      (fun j hj => by rw [lat_arcA hp (by omega), lat0]; rfl)
    have := M.two; omega
  · rw [ho] at hpos lat0 fr
    simp only [sgnD, ↓reduceIte] at hpos
    have h := lowerCol_mu (V := V) H' n M.ev H hcells hp (fun j h1 h2 => by
        have := D_mono_row M.hH hH' (c := c) (s := s) j (fun j' hj' => fr j' (by omega))
        rw [cellJ_zero] at this; omega)
      (fun j hj => by rw [lat_arcA hp (by omega), lat0]; rfl)
    have := M.two; omega

end minimal

section stuck

variable {V W : Finset Pt} {d : Pt → ℕ} {H' : Finset Edge} {t0 u0 : Pt}

-- **The move step.**
--
theorem move_step {H : Finset Edge} {FP : List FixedPr} (hVW : V ⊆ W) (hH : IsFactor W d H)
    (hH' : IsFactor W d H') (hFH : ∀ e ∈ symmDiff H H', e.p ∈ V ∧ e.q ∈ V) (hs : SolidFor V H H')
    (hdc : ∀ q, IsCell V q → ∀ z, IsCorner z q → d z = 2)
    (hinv : Inv V H H' FP t0 u0) (hmove : ¬ NoMove V H H') :
    ∃ H₁ FP₁, IsFactor W d H₁ ∧ (∀ e ∈ symmDiff H₁ H', e.p ∈ V ∧ e.q ∈ V) ∧
      Inv V H₁ H' FP₁ t0 u0 ∧ ncomp W H₁ = ncomp W H ∧ FP₁.length = FP.length ∧
      mu V H₁ H' < mu V H H' ∧ SolidFor V H₁ H' := by
  obtain ⟨c, s, n, i, hc, hcrit, hb, hnp, hpos, hcell, hpat, hi, hend, hev, hn2⟩ :=
    movable_column hinv hmove
  have hpi : (i.top = cellJ c s n ∧ i.bot = cellJ c s (n + 1)) ∨
      (i.bot = cellJ c s n ∧ i.top = cellJ c s (n + 1)) := by
    rcases hend with ⟨_, e1, e2⟩ | ⟨_, e1, e2⟩
    · left; refine ⟨?_, e1⟩
      unfold FixedPr.top; rw [e1, e2, nb_cellJ_opp]
    · right; refine ⟨e1, ?_⟩
      unfold FixedPr.top; rw [e1, e2, nb_cellJ]
  have hpo : (outArc H c s = true ∧ i.top = cellJ c s n ∧ i.bot = cellJ c s (n + 1)) ∨
      (outArc H c s = false ∧ i.bot = cellJ c s n ∧ i.top = cellJ c s (n + 1)) := by
    rcases hend with ⟨h0, e1, e2⟩ | ⟨h0, e1, e2⟩
    · left; refine ⟨h0, ?_, e1⟩
      unfold FixedPr.top; rw [e1, e2, nb_cellJ_opp]
    · right; refine ⟨h0, e1, ?_⟩
      unfold FixedPr.top; rw [e1, e2, nb_cellJ]
  have M : MoveCtx V W d H H' FP c s n i t0 u0 :=
    ⟨hinv, hVW, hH, hdc, hcell, hpat, hi, hev, hn2, hpi, hnp, hpo⟩
  refine ⟨lowerCol H c s n, fpAfter FP i (npair (outArc H c s) c s), M.factor,
    M.symm_inside hFH, M.inv_after (three_after M) M.out_after (col_after M hH' hFH hs hpos)
      (sideInv_after M hH' hFH hs hpos),
    M.count, fpAfter_length _ _ _, M.mu_lt hH' hpos, M.solid1 hH' hFH hs⟩

-- **Stuck ⇒ minimal.**
--
theorem stuck_minimal (hH' : IsFactor W d H') (hac : ∀ G, IsFactor W d G → ClimbAcyc V G)
    (hVW : V ⊆ W) (hdc : ∀ q, IsCell V q → ∀ z, IsCorner z q → d z = 2) :
    ∀ (n : ℕ) (H : Finset Edge) (FP : List FixedPr), mu V H H' = n → IsFactor W d H →
      (∀ e ∈ symmDiff H H', e.p ∈ V ∧ e.q ∈ V) → SolidFor V H H' → Inv V H H' FP t0 u0 →
      ncomp W H ≤ ncomp W H' + FP.length := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro H FP hmu hH hFH hsol hinv
  by_cases hno : NoMove V H H'
  · exact count_final hH hH' (hac H hH) hsol hinv.f2
      (threeOK_of_tri hH hH' hsol hinv.f2 hinv.f4 hno
        (fun f hf h3 => (hinv.tri f hf h3).imp (fun h => h.elim (fun h => ⟨t0, h⟩) (fun h => ⟨u0, h⟩)) id)) hinv.f4 hno
  · obtain ⟨H₁, FP₁, hH₁, hFH₁, hinv₁, hc, hl, hmu₁, hsol₁⟩ :=
      move_step hVW hH hH' hFH hsol hdc hinv hno
    have := ih _ (hmu ▸ hmu₁) H₁ FP₁ rfl hH₁ hFH₁ hsol₁ hinv₁
    omega

end stuck

end HP

end SolidGridHam
