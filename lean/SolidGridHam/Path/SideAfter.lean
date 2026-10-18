/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import SolidGridHam.Path.SideCol

/-!
# I5 after a move

The strips of I5 start beside a pair square. After a move:
* for the new pair they are side chains from `S_1` or `R_1` (`MoveCtx.sideA_col` with `j = 1`), or
  vacuous (`D` has the wrong sign at the square they need);
* for an old pair away from the move, a strip start off the moved region is transferred
  (`MoveCtx.transfer`); a strip start on the moved region is `c_0` (a one-square strip, ending at the
  new pair), `B` (the strip runs down the lowered column to `c_1`, the new pair), or a side square
  with odd index (a side chain).
-/

namespace SolidGridHam

namespace HP

open Finset Classical

section sideafter

variable {V W : Finset Pt} {d : Pt → ℕ} {H H' : Finset Edge} {FP : List FixedPr} {c : Pt}
  {s : Side} {n : ℕ} {i : FixedPr} {t0 u0 : Pt}

lemma latA_par {a s : Side} (h : a = s ∨ a = s.opp) : latA a = latA s ∧ latB a = latB s := by
  rcases h with rfl | rfl
  · exact ⟨rfl, rfl⟩
  · exact ⟨latA_opp s, by cases s <;> rfl⟩

-- **Strip starts on the moved region.** A square `S` near the move, with its back dark and its
-- lateral sides light in frame `a`, next to a pair (squares `nb S ℓ.opp` and the one beyond along
-- `a.opp`) away from the move, is `c_0` (frame `s`), `B` (frame `s.opp`), or an odd side square
-- (frame `s`) with its far side light.
--
theorem MoveCtx.start_cases (M : MoveCtx V W d H H' FP c s n i t0 u0) {S : Pt} {a ℓ : Side}
    (hℓ : ℓ = latA a ∨ ℓ = latB a) (hS : NearM c s n S) (hX : ¬ NearM c s n (nb S ℓ.opp))
    (hY : ¬ NearM c s n (nb (nb S ℓ.opp) a.opp)) (hb : back S a ∈ lowerCol H c s n)
    (hl1 : lat1 S a ∉ lowerCol H c s n) (hl2 : lat2 S a ∉ lowerCol H c s n) :
    (S = c ∧ a = s) ∨ (S = cellJ c s (n + 1) ∧ a = s.opp) ∨
      (∃ k, 1 ≤ k ∧ k ≤ n ∧ k % 2 = 1 ∧ S = nb (cellJ c s k) (latA s) ∧ a = s) ∨
      (∃ k, 1 ≤ k ∧ k ≤ n ∧ k % 2 = 1 ∧ S = nb (cellJ c s k) (latB s) ∧ a = s) := by
  have mk : ∀ k, 1 ≤ k → k ≤ n → ∀ a', NearM c s n (nb (cellJ c s k) a') :=
    fun k h1 h2 a' => ⟨k, h1, h2, Or.inr ⟨a', rfl⟩⟩
  rcases near_cases hS with ⟨k, hk, rfl⟩ | ⟨k, h1, h2, rfl | rfl⟩
  · rcases (show k = 0 ∨ (1 ≤ k ∧ k ≤ n) ∨ k = n + 1 by omega) with rfl | ⟨k1, k2⟩ | rfl
    · rw [cellJ_zero] at hX hY hb hl1 hl2 ⊢
      have hb0 := back0_after M.ev M.two M.pat
      have hf0 := front0_after M.ev M.two M.pat
      rcases side_cases s a with h | h | h | h <;> subst a
      · exact Or.inl ⟨rfl, rfl⟩
      · exfalso
        have hℓ' : ℓ = latA s ∨ ℓ = latB s := by
          rcases hℓ with rfl | rfl
          · exact Or.inl (latA_opp s)
          · exact Or.inr (by cases s <;> rfl)
        rw [opp_opp, nb_comm, show nb c s = cellJ c s 1 by rw [← nb_cellJ, cellJ_zero]] at hY
        exact hY (mk 1 le_rfl (by have := M.two; omega) _)
      · exfalso
        rcases perp_lats c (s := s) (a := latA s) (Or.inl rfl) with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · rw [e1] at hl1; exact hl1 hf0
        · rw [e1] at hl1; exact hl1 hb0
      · exfalso
        rcases perp_lats c (s := s) (a := latB s) (Or.inr rfl) with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · rw [e1] at hl1; exact hl1 hf0
        · rw [e1] at hl1; exact hl1 hb0
    · exact absurd (mk k k1 k2 ℓ.opp) hX
    · have hbB : sideEdge (cellJ c s (n + 1)) s.opp ∉ lowerCol H c s n := by
        rw [show sideEdge (cellJ c s (n + 1)) s.opp = front (cellJ c s n) s from
          back_cellJ_succ c s n]
        exact frontk_after M.ev M.two M.pat
      have hfB : sideEdge (cellJ c s (n + 1)) s ∈ lowerCol H c s n := by
        rw [mem_lowerCol_off (fun m _ _ => by
          rw [show sideEdge (cellJ c s (n + 1)) s = front (cellJ c s (n + 1)) s from rfl,
            front_mem_cellE_iff]; omega)]
        exact (alt_opp_iff M.altB s).2 (by
          show back _ _ ∈ H; rw [back_cellJ_succ]
          exact frontn_mem M.ev M.two M.pat M.d1 M.d2 M.altB)
      rcases side_cases s a with h | h | h | h <;> subst a
      · exact absurd hb hbB
      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · exfalso
        rcases perp_lats (cellJ c s (n + 1)) (s := s) (a := latA s) (Or.inl rfl) with
          ⟨e1, e2⟩ | ⟨e1, e2⟩
        · rw [e1] at hl1; exact hl1 hfB
        · rw [e2] at hl2; exact hl2 hfB
      · exfalso
        rcases perp_lats (cellJ c s (n + 1)) (s := s) (a := latB s) (Or.inr rfl) with
          ⟨e1, e2⟩ | ⟨e1, e2⟩
        · rw [e1] at hl1; exact hl1 hfB
        · rw [e2] at hl2; exact hl2 hfB
  · -- `S_k`
    have hne := sideA_ne M.ev M.two M.pat M.d1 M.d2 M.altB (lowerCol H c s n)
      (fun m _ => outer_after1 m) h1 h2
    rcases side_cases s a with h | h | h | h <;> subst a
    · rcases hℓ with rfl | rfl
      · exfalso
        rw [latA_opp', show nb (nb (cellJ c s k) (latA s)) (latB s) = cellJ c s k by
          rw [← latA_opp', nb_nb_opp]] at hX
        exact hX ⟨k, h1, h2, Or.inl rfl⟩
      · have hodd : k % 2 = 1 := by
          by_contra he
          exact hl2 (by rw [side_near]; exact (lat1_after M.ev M.two M.pat h1 h2).2 (by omega))
        exact Or.inr (Or.inr (Or.inl ⟨k, h1, h2, hodd, rfl, rfl⟩))
    · exfalso
      rw [lat1_opp] at hl1; rw [lat2_opp] at hl2
      have hodd : k % 2 = 1 := by
        by_contra he
        exact hl2 (by rw [side_near]; exact (lat1_after M.ev M.two M.pat h1 h2).2 (by omega))
      have hb' : outer1 (cellJ c s k) s ∈ lowerCol H c s n := by
        rw [← side_front]; have := hb; unfold back at this; rw [opp_opp] at this; exact this
      have := (M.outer1_H1 h2).1 hb'; omega
    · exfalso
      rcases perp_lats (nb (cellJ c s k) (latA s)) (s := s) (a := latA s) (Or.inl rfl) with
        ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1] at hl1 <;> rw [e2] at hl2
      · exact hne ⟨fun h => absurd h hl1, fun h => absurd h hl2⟩
      · exact hne ⟨fun h => absurd h hl2, fun h => absurd h hl1⟩
    · exfalso
      rcases perp_lats (nb (cellJ c s k) (latA s)) (s := s) (a := latB s) (Or.inr rfl) with
        ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1] at hl1 <;> rw [e2] at hl2
      · exact hne ⟨fun h => absurd h hl1, fun h => absurd h hl2⟩
      · exact hne ⟨fun h => absurd h hl2, fun h => absurd h hl1⟩
  · -- `R_k`
    have hne := sideB_ne M.ev M.two M.pat M.d1 M.d2 M.altB (lowerCol H c s n)
      (fun m _ => outer_after2 m) h1 h2
    rcases side_cases s a with h | h | h | h <;> subst a
    · rcases hℓ with rfl | rfl
      · have hodd : k % 2 = 1 := by
          by_contra he
          exact hl1 (by rw [sideB_near]; exact (lat2_after M.ev M.two M.pat h1 h2).2 (by omega))
        exact Or.inr (Or.inr (Or.inr ⟨k, h1, h2, hodd, rfl, rfl⟩))
      · exfalso
        rw [latB_opp', show nb (nb (cellJ c s k) (latB s)) (latA s) = cellJ c s k by
          rw [← latB_opp', nb_nb_opp]] at hX
        exact hX ⟨k, h1, h2, Or.inl rfl⟩
    · exfalso
      rw [lat1_opp] at hl1; rw [lat2_opp] at hl2
      have hodd : k % 2 = 1 := by
        by_contra he
        exact hl1 (by rw [sideB_near]; exact (lat2_after M.ev M.two M.pat h1 h2).2 (by omega))
      have hb' : outer2 (cellJ c s k) s ∈ lowerCol H c s n := by
        rw [← sideB_front]; have := hb; unfold back at this; rw [opp_opp] at this; exact this
      have := (M.outer2_H1 h2).1 hb'; omega
    · exfalso
      rcases perp_lats (nb (cellJ c s k) (latB s)) (s := s) (a := latA s) (Or.inl rfl) with
        ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1] at hl1 <;> rw [e2] at hl2
      · exact hne ⟨fun h => absurd h hl1, fun h => absurd h hl2⟩
      · exact hne ⟨fun h => absurd h hl2, fun h => absurd h hl1⟩
    · exfalso
      rcases perp_lats (nb (cellJ c s k) (latB s)) (s := s) (a := latB s) (Or.inr rfl) with
        ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1] at hl1 <;> rw [e2] at hl2
      · exact hne ⟨fun h => absurd h hl1, fun h => absurd h hl2⟩
      · exact hne ⟨fun h => absurd h hl2, fun h => absurd h hl1⟩

lemma cellJ_back (c : Pt) (s : Side) {m t : ℕ} (h : t ≤ m) :
    cellJ (cellJ c s m) s.opp t = cellJ c s (m - t) := by
  obtain ⟨x, y⟩ := c
  cases s <;> simp [cellJ, Side.opp, Nat.cast_sub h] <;> ring

-- **The strip from `B` down the lowered column**, ending at `c_1`.
--
lemma MoveCtx.stripB (M : MoveCtx V W d H H' FP c s n i t0 u0) :
    StripPat (lowerCol H c s n) (cellJ c s (n + 1)) s.opp (n + 1) := by
  have hfB : sideEdge (cellJ c s (n + 1)) s ∈ lowerCol H c s n := by
    rw [mem_lowerCol_off (fun m _ _ => by
      rw [show sideEdge (cellJ c s (n + 1)) s = front (cellJ c s (n + 1)) s from rfl,
        front_mem_cellE_iff]; omega)]
    exact (alt_opp_iff M.altB s).2 (by
      show back _ _ ∈ H; rw [back_cellJ_succ]
      exact frontn_mem M.ev M.two M.pat M.d1 M.d2 M.altB)
  have hev := M.ev
  refine ⟨by unfold back; rw [opp_opp]; exact hfB, fun t ht => ?_, fun t ht => ?_⟩
  · rw [cellJ_back c s (show t ≤ n + 1 by omega), lat1_opp, lat2_opp]
    rcases (show t = 0 ∨ 1 ≤ t by omega) with rfl | h1
    · have := M.latB_lats_H1
      exact ⟨⟨fun h => absurd h this.1, fun h => by omega⟩,
        ⟨fun h => absurd h this.2, fun h => by omega⟩⟩
    · rw [lat1_after M.ev M.two M.pat (by omega) (by omega),
        lat2_after M.ev M.two M.pat (by omega) (by omega)]
      constructor <;> omega
  · rw [cellJ_back c s (show t ≤ n + 1 by omega)]
    have hb : front (cellJ c s (n + 1 - t)) s.opp = front (cellJ c s (n - t)) s := by
      have := back_cellJ_succ c s (n - t)
      rw [show n - t + 1 = n + 1 - t by omega] at this
      exact this
    rw [hb]
    rcases (show t = 0 ∨ (1 ≤ t ∧ t < n) ∨ t = n by omega) with h | ⟨h1, h⟩ | h
    · subst h
      rw [show n - 0 = n by omega]
      have := frontk_after M.ev M.two M.pat
      exact ⟨fun hh => absurd hh this, fun hh => by have := M.two; omega⟩
    · rw [front_inner_after M.ev M.two M.pat (by omega) (by omega)]; omega
    · rw [h, show n - n = 0 by omega, cellJ_zero]
      have := front0_after M.ev M.two M.pat
      simp only [lt_self_iff_false, iff_false]
      exact ⟨fun _ => by omega, fun _ => this⟩

-- `B`'s arc along `s` is the move's direction (it is the old pair's bottom, a source, when the
-- move climbs; its top, a sink, when it descends).
--
lemma MoveCtx.arcB (M : MoveCtx V W d H H' FP c s n i t0 u0) :
    outArc (lowerCol H c s n) (cellJ c s (n + 1)) s = outArc H c s := by
  rw [outArc_congr (F' := H) (mem_lowerCol_off (fun m _ _ => by
    rw [show sideEdge (cellJ c s (n + 1)) s = front (cellJ c s (n + 1)) s from rfl,
      front_mem_cellE_iff]; omega))]
  have hok := M.inv.f4 i M.hi
  have hlB := M.latB_lats_H1
  have hl : sideEdge (cellJ c s (n + 1)) (latA s) ∉ H := by
    rw [← lat1_eq]; intro h
    exact hlB.1 ((mem_lowerCol_off (fun m _ _ => by rw [lat1_mem_cellE_iff]; omega)).2 h)
  rcases M.po with ⟨hc, _, g2⟩ | ⟨hc, _, g2⟩
  · rw [hc]
    have hsrc : Source H (cellJ c s (n + 1)) := by
      apply source_of_alt M.altB (s := latA s)
      rw [← g2]; exact hok.2.1 _ (by rw [g2]; exact hl)
    exact hsrc s
  · rw [hc]
    have hsnk : Sink H (cellJ c s (n + 1)) := by
      apply sink_of_alt M.altB (s := latA s)
      rw [← g2]; exact hok.1 _ (by rw [g2]; exact hl)
    exact hsnk s

lemma opp_inj {a a' : Side} (h : a.opp = a'.opp) : a = a' := by
  cases a <;> cases a' <;> simp_all [Side.opp]

lemma MoveCtx.cellsB (M : MoveCtx V W d H H' FP c s n i t0 u0) :
    ∀ t ≤ n + 1, IsCell V (cellJ (cellJ c s (n + 1)) s.opp t) := fun t ht => by
  rw [cellJ_back c s ht]; exact M.cell _ (by omega)

lemma MoveCtx.strip_c (M : MoveCtx V W d H H' FP c s n i t0 u0) :
    StripPat (lowerCol H c s n) c s 1 := by
  have l0 := lat0_after M.ev M.two M.pat
  refine ⟨back0_after M.ev M.two M.pat, fun t ht => ?_, fun t ht => ?_⟩
  · have : t = 0 := by omega
    subst this; rw [cellJ_zero]
    exact ⟨⟨fun h => absurd h l0.1, fun h => by omega⟩, ⟨fun h => absurd h l0.2, fun h => by omega⟩⟩
  · have : t = 0 := by omega
    subst this; rw [cellJ_zero]
    exact ⟨fun _ => by simp, fun _ => front0_after M.ev M.two M.pat⟩

-- **I5 after the move, climbing half.**
--
theorem MoveCtx.side_up (M : MoveCtx V W d H H' FP c s n i t0 u0) (hH' : IsFactor W d H')
    (hFH : ∀ e ∈ symmDiff H H', e.p ∈ V ∧ e.q ∈ V) (hs : SolidFor V H H')
    (hpos : 0 < sgnD (outArc H c s) (D H H' c))
    {p : FixedPr} (hp : p ∈ fpAfter FP i (npair (outArc H c s) c s)) {ℓ : Side}
    (hℓ : ℓ = latA p.s ∨ ℓ = latB p.s)
    (hDt : 0 < D (lowerCol H c s n) H' p.top) (hcS : IsCell V (nb p.bot ℓ))
    (hbS : back (nb p.bot ℓ) p.s.opp ∈ lowerCol H c s n)
    (hl1 : lat1 (nb p.bot ℓ) p.s.opp ∉ lowerCol H c s n)
    (hl2 : lat2 (nb p.bot ℓ) p.s.opp ∉ lowerCol H c s n)
    (harr : outArc (lowerCol H c s n) (nb p.bot ℓ) p.s = false)
    (hDS : 0 < D (lowerCol H c s n) H' (nb p.bot ℓ)) :
    ColEnds V (lowerCol H c s n) (fpAfter FP i (npair (outArc H c s) c s)) (nb p.bot ℓ)
      p.s.opp true := by
  have hnpm : npair (outArc H c s) c s ∈ fpAfter FP i (npair (outArc H c s) c s) :=
    (mem_fpAfter M.hi).2 (Or.inl rfl)
  have hc0 : ¬ ∃ j, 1 ≤ j ∧ j ≤ n ∧ c = cellJ c s j := by
    rintro ⟨j, h1, _, h⟩
    have := cellJ_inj' ((cellJ_zero (c := c) (s := s)).trans h); omega
  have hD0 := M.D_off hc0
  have hD1 := M.D_on (k := 1) le_rfl (by have := M.two; omega)
  have hD1' := M.D_col hH' (k := 1) (by have := M.two; omega)
  have h2 := sgnD_two hpos
  -- Turning the arrival arc into the strip's arc.
  --
  have toArc : ∀ {S : Pt}, back S s ∈ lowerCol H c s n → front S s ∉ lowerCol H c s n →
      outArc (lowerCol H c s n) S s.opp = false → outArc (lowerCol H c s n) S s = true := by
    intro S hb hf ha; rw [bf_arc hb hf, ha]; rfl
  rcases (mem_fpAfter M.hi).1 hp with rfl | ⟨hpF, hpi⟩
  · -- The new pair.
    by_cases ho : outArc H c s = true
    · have hbot : (npair (outArc H c s) c s).bot = cellJ c s 1 := by rw [ho]; rfl
      have hsd : (npair (outArc H c s) c s).s = s.opp := by rw [ho]; rfl
      rw [hbot] at hcS hDS
      rw [hbot, hsd] at hbS hl1 hl2 harr
      rw [hsd] at hℓ
      rw [hbot, hsd]
      rw [opp_opp] at hbS hl1 hl2 ⊢
      rw [latA_opp, show latB s.opp = latB s by cases s <;> rfl] at hℓ
      have h1n : 1 ≤ n := by have := M.two; omega
      rcases hℓ with rfl | rfl
      · have hf : front (nb (cellJ c s 1) (latA s)) s ∉ lowerCol H c s n := by
          rw [side_front]; intro h; have := (M.outer1_H1 h1n).1 h; omega
        have ha := toArc hbS hf harr
        have := M.sideA_col hH' hFH hs hpos le_rfl h1n (by norm_num) hl1
          (by rw [ha]; simpa [sgnD] using hDS)
        rwa [ha] at this
      · have hf : front (nb (cellJ c s 1) (latB s)) s ∉ lowerCol H c s n := by
          rw [sideB_front]; intro h; have := (M.outer2_H1 h1n).1 h; omega
        have ha := toArc hbS hf harr
        have := M.sideB_col hH' hFH hs hpos le_rfl h1n (by norm_num) hl2
          (by rw [ha]; simpa [sgnD] using hDS)
        rwa [ha] at this
    · exfalso
      have ho' : outArc H c s = false := by simpa using ho
      have e : (npair (outArc H c s) c s).top = cellJ c s 1 := by
        rw [ho']; simp only [npair, Bool.false_eq_true, ↓reduceIte]; exact newPairF_top
      rw [e] at hDt
      rw [ho'] at hD1 hD1' h2
      simp only [sgnD, Bool.false_eq_true, ↓reduceIte] at hD1 hD1' h2
      omega
  · -- An old pair away from the move.
    obtain ⟨hta, hba⟩ := M.other_away hpF hpi
    have hDt' : 0 < D H H' p.top := by
      rw [← M.D_off (x := p.top) (by rintro ⟨j, h1, h2, h⟩; exact hta ⟨j, h1, h2, Or.inl h⟩)]
      exact hDt
    have hX : nb (nb p.bot ℓ) ℓ.opp = p.bot := nb_nb_opp _ _
    have hY : nb p.bot p.s.opp.opp = p.top := by rw [opp_opp]; rfl
    by_cases hSn : NearM c s n (nb p.bot ℓ)
    · have hℓ' : ℓ = latA p.s.opp ∨ ℓ = latB p.s.opp := by
        rw [latA_opp, show latB p.s.opp = latB p.s by cases p.s <;> rfl]; exact hℓ
      rcases M.start_cases hℓ' hSn (by rw [hX]; exact hba) (by rw [hX, hY]; exact hta)
          hbS hl1 hl2 with ⟨hSc, ha⟩ | ⟨hSB, ha⟩ | ⟨k, k1, k2, kodd, hSk, ha⟩ |
          ⟨k, k1, k2, kodd, hSk, ha⟩
      · -- `c`: a one-square strip, the new pair's top.
        rw [hSc, ha]
        rw [hSc, hD0] at hDS
        by_cases ho : outArc H c s = true
        swap
        · have ho' : outArc H c s = false := by simpa using ho
          rw [ho'] at hpos; simp [sgnD] at hpos; omega
        · refine ⟨0, fun t ht => ?_, M.strip_c, npair (outArc H c s) c s, hnpm, Or.inl ⟨rfl, ?_, ?_⟩⟩
          · rcases (show t = 0 ∨ t = 1 by omega) with rfl | rfl
            · rw [cellJ_zero, ← cellJ_zero c s]; exact M.cell 0 (by omega)
            · exact M.cell 1 (by have := M.two; omega)
          · rw [ho]; rfl
          · rw [ho]; rfl
      · -- `B`: the strip runs down the lowered column to `c_1`.
        have hps : p.s = s := opp_inj ha
        rw [hSB, hps, M.arcB] at harr
        rw [hSB, ha]
        have hnp : npair (outArc H c s) c s = newPairF c s := by rw [harr]; rfl
        refine ⟨n, M.cellsB, M.stripB, npair (outArc H c s) c s, hnpm, Or.inl ⟨rfl, ?_, ?_⟩⟩
        · rw [hnp, cellJ_back c s le_rfl, show n + 1 - (n + 1) = 0 by omega, cellJ_zero]; rfl
        · rw [hnp, opp_opp]; rfl
      · -- an odd side square: a side chain
        rw [hSk, ha]
        rw [hSk] at hl1 hbS harr hDS
        rw [ha] at hl1 hbS
        have hps : p.s = s.opp := by rw [← ha, opp_opp]
        rw [hps] at harr
        have hf : front (nb (cellJ c s k) (latA s)) s ∉ lowerCol H c s n := by
          rw [side_front]; intro h; have := (M.outer1_H1 k2).1 h; omega
        have har := toArc hbS hf harr
        have := M.sideA_col hH' hFH hs hpos k1 k2 kodd hl1 (by rw [har]; simpa [sgnD] using hDS)
        rwa [har] at this
      · rw [hSk, ha]
        rw [hSk] at hl2 hbS harr hDS
        rw [ha] at hl2 hbS
        have hps : p.s = s.opp := by rw [← ha, opp_opp]
        rw [hps] at harr
        have hf : front (nb (cellJ c s k) (latB s)) s ∉ lowerCol H c s n := by
          rw [sideB_front]; intro h; have := (M.outer2_H1 k2).1 h; omega
        have har := toArc hbS hf harr
        have := M.sideB_col hH' hFH hs hpos k1 k2 kodd hl2 (by rw [har]; simpa [sgnD] using hDS)
        rwa [har] at this
    · -- away from the move: I5 before the move, transferred.
      have sa := fun (s'' : Side) => side_after (F := H) hSn s''
      have hbS' : back (nb p.bot ℓ) p.s.opp ∈ H := (sa _).1 hbS
      have hl1' : lat1 (nb p.bot ℓ) p.s.opp ∉ H := by rw [lat1_eq, ← sa]; rwa [lat1_eq] at hl1
      have hl2' : lat2 (nb p.bot ℓ) p.s.opp ∉ H := by rw [lat2_eq, ← sa]; rwa [lat2_eq] at hl2
      have harr' : outArc H (nb p.bot ℓ) p.s = false := by rw [← outArc_congr (sa _)]; exact harr
      have hDS' : 0 < D H H' (nb p.bot ℓ) := by
        rw [← M.D_off (x := nb p.bot ℓ) (by rintro ⟨j, h1, h2, h⟩; exact hSn ⟨j, h1, h2, Or.inl h⟩)]
        exact hDS
      have hce := (M.inv.side p hpF ℓ hℓ).1 hDt' hcS hbS' hl1' hl2' harr' hDS'
      exact M.transfer hH' hpos hSn hbS' (by rw [opp_opp, harr']; rfl) (by simpa [sgnD] using hDS')
        hce

-- **I5 after the move, descending half.**
--
theorem MoveCtx.side_down (M : MoveCtx V W d H H' FP c s n i t0 u0) (hH' : IsFactor W d H')
    (hFH : ∀ e ∈ symmDiff H H', e.p ∈ V ∧ e.q ∈ V) (hs : SolidFor V H H')
    (hpos : 0 < sgnD (outArc H c s) (D H H' c))
    {p : FixedPr} (hp : p ∈ fpAfter FP i (npair (outArc H c s) c s)) {ℓ : Side}
    (hℓ : ℓ = latA p.s ∨ ℓ = latB p.s)
    (hDb : D (lowerCol H c s n) H' p.bot < 0) (hcS : IsCell V (nb p.top ℓ))
    (hbS : back (nb p.top ℓ) p.s ∈ lowerCol H c s n)
    (hl1 : lat1 (nb p.top ℓ) p.s ∉ lowerCol H c s n)
    (hl2 : lat2 (nb p.top ℓ) p.s ∉ lowerCol H c s n)
    (harr : outArc (lowerCol H c s n) (nb p.top ℓ) p.s.opp = true)
    (hDS : D (lowerCol H c s n) H' (nb p.top ℓ) < 0) :
    ColEnds V (lowerCol H c s n) (fpAfter FP i (npair (outArc H c s) c s)) (nb p.top ℓ)
      p.s false := by
  have hnpm : npair (outArc H c s) c s ∈ fpAfter FP i (npair (outArc H c s) c s) :=
    (mem_fpAfter M.hi).2 (Or.inl rfl)
  have hc0 : ¬ ∃ j, 1 ≤ j ∧ j ≤ n ∧ c = cellJ c s j := by
    rintro ⟨j, h1, _, h⟩
    have := cellJ_inj' ((cellJ_zero (c := c) (s := s)).trans h); omega
  have hD0 := M.D_off hc0
  have hD1 := M.D_on (k := 1) le_rfl (by have := M.two; omega)
  have hD1' := M.D_col hH' (k := 1) (by have := M.two; omega)
  have h2 := sgnD_two hpos
  have toArc : ∀ {S : Pt}, back S s ∈ lowerCol H c s n → front S s ∉ lowerCol H c s n →
      outArc (lowerCol H c s n) S s.opp = true → outArc (lowerCol H c s n) S s = false := by
    intro S hb hf ha; rw [bf_arc hb hf, ha]; rfl
  rcases (mem_fpAfter M.hi).1 hp with rfl | ⟨hpF, hpi⟩
  · by_cases ho : outArc H c s = true
    · exfalso
      have e : (npair (outArc H c s) c s).bot = cellJ c s 1 := by rw [ho]; rfl
      rw [e] at hDb
      rw [ho] at hD1 hD1' h2
      simp only [sgnD, ↓reduceIte] at hD1 hD1' h2
      omega
    · have ho' : outArc H c s = false := by simpa using ho
      have htop : (npair (outArc H c s) c s).top = cellJ c s 1 := by
        rw [ho']; simp only [npair, Bool.false_eq_true, ↓reduceIte]; exact newPairF_top
      have hsd : (npair (outArc H c s) c s).s = s := by rw [ho']; rfl
      rw [htop] at hcS hDS
      rw [htop, hsd] at hbS hl1 hl2 harr
      rw [hsd] at hℓ
      rw [htop, hsd]
      have h1n : 1 ≤ n := by have := M.two; omega
      rcases hℓ with rfl | rfl
      · have hf : front (nb (cellJ c s 1) (latA s)) s ∉ lowerCol H c s n := by
          rw [side_front]; intro h; have := (M.outer1_H1 h1n).1 h; omega
        have ha := toArc hbS hf harr
        have := M.sideA_col hH' hFH hs hpos le_rfl h1n (by norm_num) hl1
          (by rw [ha]; simp [sgnD]; omega)
        rwa [ha] at this
      · have hf : front (nb (cellJ c s 1) (latB s)) s ∉ lowerCol H c s n := by
          rw [sideB_front]; intro h; have := (M.outer2_H1 h1n).1 h; omega
        have ha := toArc hbS hf harr
        have := M.sideB_col hH' hFH hs hpos le_rfl h1n (by norm_num) hl2
          (by rw [ha]; simp [sgnD]; omega)
        rwa [ha] at this
  · obtain ⟨hta, hba⟩ := M.other_away hpF hpi
    have hDb' : D H H' p.bot < 0 := by
      rw [← M.D_off (x := p.bot) (by rintro ⟨j, h1, h2, h⟩; exact hba ⟨j, h1, h2, Or.inl h⟩)]
      exact hDb
    have hX : nb (nb p.top ℓ) ℓ.opp = p.top := nb_nb_opp _ _
    have hY : nb p.top p.s.opp = p.bot := nb_nb_opp _ _
    by_cases hSn : NearM c s n (nb p.top ℓ)
    · rcases M.start_cases hℓ hSn (by rw [hX]; exact hta) (by rw [hX, hY]; exact hba)
          hbS hl1 hl2 with ⟨hSc, ha⟩ | ⟨hSB, ha⟩ | ⟨k, k1, k2, kodd, hSk, ha⟩ |
          ⟨k, k1, k2, kodd, hSk, ha⟩
      · rw [hSc, ha]
        rw [hSc, hD0] at hDS
        by_cases ho : outArc H c s = true
        · rw [ho] at hpos; simp [sgnD] at hpos; omega
        · have ho' : outArc H c s = false := by simpa using ho
          refine ⟨0, fun t ht => ?_, M.strip_c, npair (outArc H c s) c s, hnpm,
            Or.inr ⟨rfl, ?_, ?_⟩⟩
          · rcases (show t = 0 ∨ t = 1 by omega) with rfl | rfl
            · rw [cellJ_zero, ← cellJ_zero c s]; exact M.cell 0 (by omega)
            · exact M.cell 1 (by have := M.two; omega)
          · rw [ho', cellJ_zero]; rfl
          · rw [ho']; rfl
      · rw [hSB, ha, opp_opp, M.arcB] at harr
        rw [hSB, ha]
        have hnp : npair (outArc H c s) c s = newPair c s := by rw [harr]; rfl
        refine ⟨n, fun t ht => M.cellsB t (by omega), ?_, npair (outArc H c s) c s, hnpm,
          Or.inr ⟨rfl, ?_, ?_⟩⟩
        · exact M.stripB
        · rw [hnp, cellJ_back c s (by omega), show n + 1 - n = 1 by omega]; rfl
        · rw [hnp]; rfl
      · rw [hSk, ha]
        rw [hSk, ha] at hl1 hbS harr
        rw [hSk] at hDS
        have hf : front (nb (cellJ c s k) (latA s)) s ∉ lowerCol H c s n := by
          rw [side_front]; intro h; have := (M.outer1_H1 k2).1 h; omega
        have har := toArc hbS hf harr
        have := M.sideA_col hH' hFH hs hpos k1 k2 kodd hl1 (by rw [har]; simp [sgnD]; omega)
        rwa [har] at this
      · rw [hSk, ha]
        rw [hSk, ha] at hl2 hbS harr
        rw [hSk] at hDS
        have hf : front (nb (cellJ c s k) (latB s)) s ∉ lowerCol H c s n := by
          rw [sideB_front]; intro h; have := (M.outer2_H1 k2).1 h; omega
        have har := toArc hbS hf harr
        have := M.sideB_col hH' hFH hs hpos k1 k2 kodd hl2 (by rw [har]; simp [sgnD]; omega)
        rwa [har] at this
    · have sa := fun (s'' : Side) => side_after (F := H) hSn s''
      have hbS' : back (nb p.top ℓ) p.s ∈ H := (sa _).1 hbS
      have hl1' : lat1 (nb p.top ℓ) p.s ∉ H := by rw [lat1_eq, ← sa]; rwa [lat1_eq] at hl1
      have hl2' : lat2 (nb p.top ℓ) p.s ∉ H := by rw [lat2_eq, ← sa]; rwa [lat2_eq] at hl2
      have harr' : outArc H (nb p.top ℓ) p.s.opp = true := by rw [← outArc_congr (sa _)]; exact harr
      have hDS' : D H H' (nb p.top ℓ) < 0 := by
        rw [← M.D_off (x := nb p.top ℓ) (by rintro ⟨j, h1, h2, h⟩; exact hSn ⟨j, h1, h2, Or.inl h⟩)]
        exact hDS
      have hce := (M.inv.side p hpF ℓ hℓ).2 hDb' hcS hbS' hl1' hl2' harr' hDS'
      exact M.transfer hH' hpos hSn hbS' (by rw [harr']; rfl) (by simp [sgnD]; omega) hce

-- **I5 after the move.**
--
theorem MoveCtx.sideInv (M : MoveCtx V W d H H' FP c s n i t0 u0) (hH' : IsFactor W d H')
    (hFH : ∀ e ∈ symmDiff H H', e.p ∈ V ∧ e.q ∈ V) (hs : SolidFor V H H')
    (hpos : 0 < sgnD (outArc H c s) (D H H' c)) :
    SideInv V (lowerCol H c s n) H' (fpAfter FP i (npair (outArc H c s) c s)) :=
  fun _ hp _ hℓ => ⟨fun a b c' d' e f g => M.side_up hH' hFH hs hpos hp hℓ a b c' d' e f g,
    fun a b c' d' e f g => M.side_down hH' hFH hs hpos hp hℓ a b c' d' e f g⟩

end sideafter

end HP

end SolidGridHam
