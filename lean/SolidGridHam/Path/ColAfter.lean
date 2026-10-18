/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import SolidGridHam.Path.SideChain

@[expose] public section

/-!
# Columns after a move

Two facts give the column invariant after a move (docs/STUCK_MINIMAL.md §§20–21):
* **transfer** (`MoveCtx.transfer`): a strip from a square away from the move that ended at a pair
  square before the move still does. The strip can meet the changed region only by running into
  `c_0` from below (it then ends at `c_0`, the new pair square) or into `B = c_(n+1)` from beyond
  (then `D` has opposite signs at the two squares of the old pair, against `pair_one_side`); every
  other entry breaks the strip pattern.
* **side chains** (`SideChain.lean`): new critical squares beside the moved column.
-/

namespace SolidGridHam

namespace HP

open Finset Classical

section strip

variable {F : Finset Edge} {q : Pt} {a : Side} {m : ℕ}

-- The strip pattern at one cell.
--
lemma strip_cell (hp : StripPat F q a (m + 1)) {t : ℕ} (ht : t ≤ m) :
    (lat1 (cellJ q a t) a ∈ F ↔ t % 2 = 1) ∧ (lat2 (cellJ q a t) a ∈ F ↔ t % 2 = 1) ∧
      (front (cellJ q a t) a ∈ F ↔ (t % 2 = 1 ↔ t < m)) ∧
      (1 ≤ t → (back (cellJ q a t) a ∈ F ↔ t % 2 = 0)) := by
  refine ⟨(hp.2.1 t (by omega)).1, (hp.2.1 t (by omega)).2, ?_, fun h1 => ?_⟩
  · rw [hp.2.2 t (by omega)]; omega
  · obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
    rw [back_cellJ_succ, hp.2.2 u (by omega)]; omega

end strip

-- Cells of a column are distinct along it.
--
lemma cellJ_inj' {c : Pt} {s : Side} {a b : ℕ} (h : cellJ c s a = cellJ c s b) : a = b := by
  obtain ⟨x0, y0⟩ := c
  cases s <;> simp [cellJ] at h <;> omega

-- The lateral sides in a perpendicular frame are the back and front.
--
lemma perp_lats (c : Pt) {s a : Side} (ha : a = latA s ∨ a = latB s) :
    (lat1 c a = sideEdge c s ∧ lat2 c a = sideEdge c s.opp) ∨
      (lat1 c a = sideEdge c s.opp ∧ lat2 c a = sideEdge c s) := by
  rcases ha with rfl | rfl <;> cases s <;> simp [lat1, lat2, latA, latB, sideEdge, Side.opp]

section ends

variable {V : Finset Pt} {H H' : Finset Edge} {FP : List FixedPr}

-- Where a column ends: the last strip cell and the cell beyond are the two squares of a pair.
--
lemma colEnds_sq {q : Pt} {a : Side} {o : Bool} {m : ℕ} {j : FixedPr}
    (hend : (o = true ∧ j.bot = cellJ q a (m + 1) ∧ j.s = a.opp) ∨
      (o = false ∧ j.bot = cellJ q a m ∧ j.s = a)) :
    (o = true ∧ j.top = cellJ q a m ∧ j.bot = cellJ q a (m + 1)) ∨
      (o = false ∧ j.bot = cellJ q a m ∧ j.top = cellJ q a (m + 1)) := by
  rcases hend with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · left; refine ⟨h1, ?_, h2⟩
    unfold FixedPr.top; rw [h2, h3, nb_cellJ_opp]
  · right; refine ⟨h1, h2, ?_⟩
    unfold FixedPr.top; rw [h2, h3, nb_cellJ]

-- The last strip cell's front is the pair's shared dark side, so the strip has odd length.
--
lemma colEnds_front {q : Pt} {a : Side} {o : Bool} {m : ℕ} {j : FixedPr}
    (hdark : sideEdge j.bot j.s ∈ H) (hp : StripPat H q a (m + 1))
    (hend : (o = true ∧ j.bot = cellJ q a (m + 1) ∧ j.s = a.opp) ∨
      (o = false ∧ j.bot = cellJ q a m ∧ j.s = a)) :
    front (cellJ q a m) a ∈ H ∧ m % 2 = 0 := by
  have hf : front (cellJ q a m) a ∈ H := by
    rcases hend with ⟨_, h2, h3⟩ | ⟨_, h2, h3⟩
    · rw [h2, h3] at hdark
      have e3 : sideEdge (cellJ q a (m + 1)) a.opp = front (cellJ q a m) a := back_cellJ_succ q a m
      rw [e3] at hdark; exact hdark
    · rw [h2, h3] at hdark; exact hdark
  refine ⟨hf, ?_⟩
  have := (hp.2.2 m (by omega)).1 hf; omega

end ends

lemma bf_arc {F : Finset Edge} {q : Pt} {a : Side} (hb : back q a ∈ F) (hf : front q a ∉ F) :
    outArc F q a = !outArc F q a.opp := by
  have hb' : sideEdge q a.opp ∈ F := hb
  have hf' : sideEdge q a ∉ F := hf
  rw [outArc_eq, outArc_eq]
  cases a <;> simp only [Side.opp, Side.horiz] at hb' hf' ⊢ <;>
    simp only [hb', hf', decide_true, decide_false, ↓reduceIte, Bool.false_eq_true] <;>
    cases par q <;> rfl

lemma nb_inj_side {x : Pt} {a a' : Side} (h : nb x a = nb x a') : a = a' := by
  obtain ⟨u, v⟩ := x
  cases a <;> cases a' <;> simp [nb] at h <;> first | rfl | omega

lemma lat1_opp (x : Pt) (a : Side) : lat1 x a.opp = lat1 x a := by cases a <;> rfl
lemma lat2_opp (x : Pt) (a : Side) : lat2 x a.opp = lat2 x a := by cases a <;> rfl

section transfer

variable {V W : Finset Pt} {d : Pt → ℕ} {H H' : Finset Edge} {FP : List FixedPr} {c : Pt}
  {s : Side} {n : ℕ} {i : FixedPr} {t0 u0 : Pt} (M : MoveCtx V W d H H' FP c s n i t0 u0)
include M

-- `D` at the old pair's column end has the move's sign.
--
lemma MoveCtx.Dn (hH' : IsFactor W d H') (hpos : 0 < sgnD (outArc H c s) (D H H' c)) :
    0 < sgnD (outArc H c s) (D H H' (cellJ c s n)) := by
  have fr : ∀ j < n, outArc H (cellJ c s j) s = outArc H c s := fun j hj =>
    front_arc M.pat (by omega)
  cases ho : outArc H c s
  · rw [ho] at hpos fr
    have := D_anti_row M.hH hH' n fr
    rw [cellJ_zero] at this
    simp only [sgnD, Bool.false_eq_true, ↓reduceIte] at hpos ⊢; omega
  · rw [ho] at hpos fr
    have := D_mono_row M.hH hH' (c := c) (s := s) n fr
    rw [cellJ_zero] at this
    simp only [sgnD, ↓reduceIte] at hpos ⊢; omega

-- A pair sharing a square with the old pair is the old pair.
--
lemma MoveCtx.eq_i {j : FixedPr} (hj : j ∈ FP)
    (h : j.top = cellJ c s n ∨ j.top = cellJ c s (n + 1) ∨ j.bot = cellJ c s n ∨
      j.bot = cellJ c s (n + 1)) : j = i := by
  apply M.inv.pdisj j hj i M.hi
  rcases M.pi with ⟨g1, g2⟩ | ⟨g1, g2⟩ <;> rcases h with h | h | h | h
  · exact Or.inl (h.trans g1.symm)
  · exact Or.inr (Or.inl (h.trans g2.symm))
  · exact Or.inr (Or.inr (Or.inl (h.trans g1.symm)))
  · exact Or.inr (Or.inr (Or.inr (h.trans g2.symm)))
  · exact Or.inr (Or.inl (h.trans g1.symm))
  · exact Or.inl (h.trans g2.symm)
  · exact Or.inr (Or.inr (Or.inr (h.trans g1.symm)))
  · exact Or.inr (Or.inr (Or.inl (h.trans g2.symm)))

-- A strip whose cells are away from the move keeps its pattern.
--
omit M in
lemma strip_keep {F : Finset Edge} {q : Pt} {a : Side} {m : ℕ}
    (hnear : ∀ t ≤ m, ¬ NearM c s n (cellJ q a t)) :
    StripPat (lowerCol F c s n) q a (m + 1) ↔ StripPat F q a (m + 1) := by
  have sa := fun t (ht : t ≤ m) (s' : Side) => side_after (F := F) (hnear t ht) s'
  have h0 := sa 0 (by omega)
  rw [cellJ_zero] at h0
  unfold StripPat
  constructor
  · rintro ⟨hb, hl, hf⟩
    refine ⟨(h0 a.opp).1 hb, fun t ht => ?_, fun t ht => ?_⟩
    · rw [lat1_eq, lat2_eq, ← (sa t (by omega) _), ← (sa t (by omega) _), ← lat1_eq, ← lat2_eq]
      exact hl t ht
    · rw [show front (cellJ q a t) a = sideEdge (cellJ q a t) a from rfl, ← sa t (by omega)]
      exact hf t ht
  · rintro ⟨hb, hl, hf⟩
    refine ⟨(h0 a.opp).2 hb, fun t ht => ?_, fun t ht => ?_⟩
    · rw [lat1_eq, lat2_eq, sa t (by omega), sa t (by omega), ← lat1_eq, ← lat2_eq]
      exact hl t ht
    · rw [show front (cellJ q a t) a = sideEdge (cellJ q a t) a from rfl, sa t (by omega)]
      exact hf t ht

omit M in
lemma nb_comm (x : Pt) (a a' : Side) : nb (nb x a) a' = nb (nb x a') a := by
  obtain ⟨u, v⟩ := x; cases a <;> cases a' <;> simp [nb]

omit M in
lemma opp_opp (a : Side) : a.opp.opp = a := by cases a <;> rfl

omit M in
lemma latA_opp' (s : Side) : (latA s).opp = latB s := by cases s <;> rfl

omit M in
lemma latB_opp' (s : Side) : (latB s).opp = latA s := by cases s <;> rfl

omit M in
lemma nb_col_prev (c : Pt) (s : Side) {k : ℕ} (hk : 1 ≤ k) :
    nb (cellJ c s k) s.opp = cellJ c s (k - 1) := by
  have := nb_cellJ_opp c s (k - 1); rwa [show k - 1 + 1 = k by omega] at this

-- **Entry lemma.** A strip from a square away from the move first meets the move (at an index
-- inside the strip) either at `c_0` heading along `s`, or at `B = c_(n+1)` heading against `s`.
--
lemma MoveCtx.entry {q : Pt} {a : Side} {m t0 : ℕ} (hp : StripPat H q a (m + 1))
    (hm : m % 2 = 0) (ht1 : 1 ≤ t0) (htm : t0 ≤ m)
    (hprev : ¬ NearM c s n (cellJ q a (t0 - 1))) (he : NearM c s n (cellJ q a t0)) :
    (cellJ q a t0 = c ∧ a = s) ∨ (cellJ q a t0 = cellJ c s (n + 1) ∧ a = s.opp) := by
  have hpe : cellJ q a (t0 - 1) = nb (cellJ q a t0) a.opp := by
    have := nb_cellJ q a (t0 - 1)
    rw [show t0 - 1 + 1 = t0 by omega] at this
    show _ = nb (cellJ q a t0) a.opp
    rw [← this, nb_nb_opp]
  rw [hpe] at hprev
  obtain ⟨L1, L2, FR, BK⟩ := strip_cell hp htm
  have BK' := BK ht1
  have prev_l2 := (strip_cell hp (t := t0 - 1) (by omega)).2.1
  have prev_l1 := (strip_cell hp (t := t0 - 1) (by omega)).1
  rw [hpe] at prev_l2 prev_l1
  have mk : ∀ k, 1 ≤ k → k ≤ n → ∀ a', NearM c s n (nb (cellJ c s k) a') :=
    fun k h1 h2 a' => ⟨k, h1, h2, Or.inr ⟨a', rfl⟩⟩
  have mkc : ∀ k, 1 ≤ k → k ≤ n → NearM c s n (cellJ c s k) :=
    fun k h1 h2 => ⟨k, h1, h2, Or.inl rfl⟩
  have hd1 := M.d1
  have hd2 := M.d2
  rcases near_cases he with ⟨k, hk, hek⟩ | ⟨k, h1, h2, hek | hek⟩
  · rw [hek] at hprev L1 L2 FR BK'
    rcases (show k = 0 ∨ (1 ≤ k ∧ k ≤ n) ∨ k = n + 1 by omega) with rfl | ⟨k1, k2⟩ | rfl
    · rw [cellJ_zero] at hprev L1 L2 FR BK' hek
      rcases side_cases s a with rfl | rfl | rfl | rfl
      · exact Or.inl ⟨hek, rfl⟩
      · exfalso; rw [opp_opp] at hprev
        have e1 : nb c s = cellJ c s 1 := by rw [← nb_cellJ, cellJ_zero]
        rw [e1] at hprev
        exact hprev (mkc 1 le_rfl (by have := M.two; omega))
      · exfalso
        have hf : sideEdge c s ∉ H := fun h => by
          have h0 := (M.pat.2.2 0 (by have := M.two; omega)).1; rw [cellJ_zero] at h0
          exact absurd ((h0 h).2 (by have := M.two; omega)) (by omega)
        have hb : sideEdge c s.opp ∈ H := M.pat.1
        rcases perp_lats c (s := s) (a := latA s) (Or.inl rfl) with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;>
          rw [e1] at L1 <;> rw [e2] at L2
        · exact hf (L1.2 (L2.1 hb))
        · exact hf (L2.2 (L1.1 hb))
      · exfalso
        have hf : sideEdge c s ∉ H := fun h => by
          have h0 := (M.pat.2.2 0 (by have := M.two; omega)).1; rw [cellJ_zero] at h0
          exact absurd ((h0 h).2 (by have := M.two; omega)) (by omega)
        have hb : sideEdge c s.opp ∈ H := M.pat.1
        rcases perp_lats c (s := s) (a := latB s) (Or.inr rfl) with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;>
          rw [e1] at L1 <;> rw [e2] at L2
        · exact hf (L1.2 (L2.1 hb))
        · exact hf (L2.2 (L1.1 hb))
    · exact absurd (mk k k1 k2 a.opp) hprev
    · have bB : sideEdge (cellJ c s (n + 1)) s.opp ∈ H := by
        show back _ _ ∈ H; rw [back_cellJ_succ]; exact frontn_mem M.ev M.two M.pat hd1 hd2 M.altB
      have fB : sideEdge (cellJ c s (n + 1)) s ∈ H := (alt_opp_iff M.altB s).2 bB
      have lB := alt_lats M.altB (s' := s.opp) bB
      rw [latA_opp, show latB s.opp = latB s by cases s <;> rfl] at lB
      rcases side_cases s a with rfl | rfl | rfl | rfl
      · exfalso
        rw [nb_col_prev c a (by omega)] at hprev
        exact hprev (mkc n (by have := M.two; omega) le_rfl)
      · exact Or.inr ⟨hek, rfl⟩
      · exfalso
        rcases perp_lats (cellJ c s (n + 1)) (s := s) (a := latA s) (Or.inl rfl) with
          ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1] at L1
        · have ho := L1.1 fB
          have := FR.1; have hfr : front (cellJ c s (n + 1)) (latA s) ∉ H := lB.1
          have : ¬ (t0 % 2 = 1 ↔ t0 < m) := fun h => hfr (FR.2 h)
          omega
        · have ho := L1.1 bB
          have hfr : front (cellJ c s (n + 1)) (latA s) ∉ H := lB.1
          have : ¬ (t0 % 2 = 1 ↔ t0 < m) := fun h => hfr (FR.2 h)
          omega
      · exfalso
        rcases perp_lats (cellJ c s (n + 1)) (s := s) (a := latB s) (Or.inr rfl) with
          ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1] at L1
        · have ho := L1.1 fB
          have hfr : front (cellJ c s (n + 1)) (latB s) ∉ H := lB.2
          have : ¬ (t0 % 2 = 1 ↔ t0 < m) := fun h => hfr (FR.2 h)
          omega
        · have ho := L1.1 bB
          have hfr : front (cellJ c s (n + 1)) (latB s) ∉ H := lB.2
          have : ¬ (t0 % 2 = 1 ↔ t0 < m) := fun h => hfr (FR.2 h)
          omega
  · -- `S_k`
    rw [hek] at hprev L1 L2 FR BK' prev_l2 prev_l1
    exfalso
    have hne := sideA_ne M.ev M.two M.pat hd1 hd2 M.altB H (fun _ _ => Iff.rfl) h1 h2
    have bB : back (cellJ c s (n + 1)) s ∈ H := by
      rw [back_cellJ_succ]; exact frontn_mem M.ev M.two M.pat hd1 hd2 M.altB
    have lBH := alt_lats M.altB (s' := s.opp) bB
    rw [latA_opp, show latB s.opp = latB s by cases s <;> rfl, ← lat1_eq, ← lat2_eq] at lBH
    rcases side_cases s a with h | h | h | h <;> subst a
    · rw [nb_comm, nb_col_prev c s h1] at hprev
      rcases (show k = 1 ∨ 2 ≤ k by omega) with rfl | hk2
      · have l2 : lat2 (nb (cellJ c s 1) (latA s)) s ∈ H := by
          rw [side_near]; exact (M.pat.2.1 1 (by omega)).1.2 rfl
        have b1 : back (nb (cellJ c s 1) (latA s)) s ∈ H := by
          have := outer1_side_nb_next c s
          rw [show nb c s = cellJ c s 1 by rw [← nb_cellJ, cellJ_zero]] at this
          show sideEdge _ s.opp ∈ H
          rw [← this, ← cellJ_zero c s]
          exact (outer1_all M.ev M.two M.pat hd1 hd2 M.altB (by omega)).2 rfl
        have := L2.1 l2; have := BK'.1 b1; omega
      · exact hprev (mk (k - 1) (by omega) (by omega) _)
    · rw [opp_opp, nb_comm, nb_cellJ] at hprev prev_l2
      rcases (show k = n ∨ k + 1 ≤ n by omega) with rfl | hk2
      · have l2 : lat2 (nb (cellJ c s k) (latA s)) s.opp ∉ H := by
          rw [lat2_opp, side_near]
          intro h; have := (M.pat.2.1 k (by omega)).1.1 h; have := M.ev; omega
        have l2p : lat2 (nb (cellJ c s (k + 1)) (latA s)) s.opp ∉ H := by
          rw [lat2_opp, side_near]; exact lBH.1
        have h0 : ¬ (t0 % 2 = 1) := fun h => l2 (L2.2 h)
        have : ¬ ((t0 - 1) % 2 = 1) := fun h => l2p (prev_l2.2 h)
        omega
      · exact hprev (mk (k + 1) (by omega) hk2 _)
    · rw [latA_opp', show nb (nb (cellJ c s k) (latA s)) (latB s) = cellJ c s k by
        rw [← latA_opp', nb_nb_opp]] at hprev
      exact hprev (mkc k h1 h2)
    · rcases perp_lats (nb (cellJ c s k) (latA s)) (s := s) (a := latB s) (Or.inr rfl) with
        ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1] at L1 <;> rw [e2] at L2
      · exact hne (L1.trans L2.symm)
      · exact hne (L2.trans L1.symm)
  · -- `R_k`
    rw [hek] at hprev L1 L2 FR BK' prev_l2 prev_l1
    exfalso
    have hne := sideB_ne M.ev M.two M.pat hd1 hd2 M.altB H (fun _ _ => Iff.rfl) h1 h2
    have bB : back (cellJ c s (n + 1)) s ∈ H := by
      rw [back_cellJ_succ]; exact frontn_mem M.ev M.two M.pat hd1 hd2 M.altB
    have lBH := alt_lats M.altB (s' := s.opp) bB
    rw [latA_opp, show latB s.opp = latB s by cases s <;> rfl, ← lat1_eq, ← lat2_eq] at lBH
    rcases side_cases s a with h | h | h | h <;> subst a
    · rw [nb_comm, nb_col_prev c s h1] at hprev
      rcases (show k = 1 ∨ 2 ≤ k by omega) with rfl | hk2
      · have l1 : lat1 (nb (cellJ c s 1) (latB s)) s ∈ H := by
          rw [sideB_near]; exact (M.pat.2.1 1 (by omega)).2.2 rfl
        have b1 : back (nb (cellJ c s 1) (latB s)) s ∈ H := by
          have := outer2_side_nb_next c s
          rw [show nb c s = cellJ c s 1 by rw [← nb_cellJ, cellJ_zero]] at this
          show sideEdge _ s.opp ∈ H
          rw [← this, ← cellJ_zero c s]
          exact (outer2_all M.ev M.two M.pat hd1 hd2 M.altB (by omega)).2 rfl
        have := L1.1 l1; have := BK'.1 b1; omega
      · exact hprev (mk (k - 1) (by omega) (by omega) _)
    · rw [opp_opp, nb_comm, nb_cellJ] at hprev prev_l1
      rcases (show k = n ∨ k + 1 ≤ n by omega) with rfl | hk2
      · have l1 : lat1 (nb (cellJ c s k) (latB s)) s.opp ∉ H := by
          rw [lat1_opp, sideB_near]
          intro h; have := (M.pat.2.1 k (by omega)).2.1 h; have := M.ev; omega
        have l1p : lat1 (nb (cellJ c s (k + 1)) (latB s)) s.opp ∉ H := by
          rw [lat1_opp, sideB_near]; exact lBH.2
        have h0 : ¬ (t0 % 2 = 1) := fun h => l1 (L1.2 h)
        have : ¬ ((t0 - 1) % 2 = 1) := fun h => l1p (prev_l1.2 h)
        omega
      · exact hprev (mk (k + 1) (by omega) hk2 _)
    · rcases perp_lats (nb (cellJ c s k) (latB s)) (s := s) (a := latA s) (Or.inl rfl) with
        ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1] at L1 <;> rw [e2] at L2
      · exact hne (L1.trans L2.symm)
      · exact hne (L2.trans L1.symm)
    · rw [latB_opp', show nb (nb (cellJ c s k) (latB s)) (latA s) = cellJ c s k by
        rw [← latB_opp', nb_nb_opp]] at hprev
      exact hprev (mkc k h1 h2)

-- **Transfer.** A strip from a square away from the move, ending at a pair square before the move,
-- still ends at a pair square after it.
--
theorem MoveCtx.transfer (hH' : IsFactor W d H') (hpos : 0 < sgnD (outArc H c s) (D H H' c))
    {q : Pt} {a : Side} {o : Bool} (hq : ¬ NearM c s n q) (hb : back q a ∈ H)
    (harr : outArc H q a.opp = !o) (hrel : 0 < sgnD o (D H H' q))
    (hce : ColEnds V H FP q a o) :
    ColEnds V (lowerCol H c s n) (fpAfter FP i (npair (outArc H c s) c s)) q a o := by
  obtain ⟨m, hcells, hpat, j, hj, hend⟩ := hce
  obtain ⟨hfm, hmev⟩ := colEnds_front (M.inv.pdark j hj) hpat hend
  have hsq := colEnds_sq hend
  have hjalt := M.inv.palt j hj
  -- Direction and `D` along the strip.
  --
  have hdir : 1 ≤ m → outArc H q a = o := by
    intro hm1
    have hf : front q a ∉ H := by
      have := (strip_cell hpat (t := 0) (by omega)).2.2.1
      rw [cellJ_zero] at this
      intro h; have := this.1 h; omega
    rw [bf_arc hb hf, harr]; simp
  have hfa : ∀ t < m, outArc H (cellJ q a t) a = o := fun t ht => by
    rw [front_arc hpat (by omega)]; exact hdir (by omega)
  have hD : ∀ t ≤ m, sgnD o (D H H' q) ≤ sgnD o (D H H' (cellJ q a t)) := by
    intro t ht
    cases o
    · have := D_anti_row M.hH hH' (c := q) (s := a) t (fun t' ht' => hfa t' (by omega))
      rw [cellJ_zero] at this; simp only [sgnD, Bool.false_eq_true, ↓reduceIte]; omega
    · have := D_mono_row M.hH hH' (c := q) (s := a) t (fun t' ht' => hfa t' (by omega))
      rw [cellJ_zero] at this; simp only [sgnD, ↓reduceIte]; omega
  have mem := fun (k : FixedPr) => mem_fpAfter (np := npair (outArc H c s) c s) (j := k) M.hi
  by_cases hnone : ∀ t ≤ m + 1, ¬ NearM c s n (cellJ q a t)
  · -- The strip never meets the move.
    have hji : j ≠ i := by
      intro hji
      subst hji
      rcases M.pi with ⟨g1, g2⟩ | ⟨g1, g2⟩ <;> rcases hsq with ⟨_, h1, h2⟩ | ⟨_, h1, h2⟩
      · exact hnone m (by omega) (by rw [← h1, g1]; exact M.near_n)
      · exact hnone m (by omega) (by rw [← h1, g2]; exact M.near_n1)
      · exact hnone m (by omega) (by rw [← h1, g2]; exact M.near_n1)
      · exact hnone m (by omega) (by rw [← h1, g1]; exact M.near_n)
    exact ⟨m, hcells, (strip_keep (fun t ht => hnone t (by omega))).2 hpat, j,
      (mem j).2 (Or.inr ⟨hj, hji⟩), hend⟩
  push Not at hnone
  have hex : ∃ t, t ≤ m + 1 ∧ NearM c s n (cellJ q a t) := hnone
  obtain ⟨t0, ht0s, hmin0⟩ : ∃ t0, (t0 ≤ m + 1 ∧ NearM c s n (cellJ q a t0)) ∧
      ∀ t < t0, ¬ (t ≤ m + 1 ∧ NearM c s n (cellJ q a t)) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun t ht => Nat.find_min hex ht⟩
  have hmin : ∀ t < t0, ¬ NearM c s n (cellJ q a t) := fun t ht h =>
    hmin0 t ht ⟨by omega, h⟩
  have t0pos : 1 ≤ t0 := by
    by_contra h0
    have : t0 = 0 := by omega
    have := ht0s.2; rw [‹t0 = 0›, cellJ_zero] at this; exact hq this
  -- The square beyond the strip is a pair square: it cannot be met first.
  --
  rcases (show t0 ≤ m ∨ t0 = m + 1 by omega) with htm | htm
  swap
  · exfalso
    have hen := ht0s.2
    rw [htm] at hen
    have halt : Alt H (cellJ q a (m + 1)) := by
      rcases hsq with ⟨_, _, h2⟩ | ⟨_, _, h2⟩
      · rw [← h2]; exact hjalt.2
      · rw [← h2]; exact hjalt.1
    have hji : j = i := by
      apply M.eq_i hj
      rcases near_H M.ev M.two M.pat M.d1 M.d2 M.altB hen halt with h | h <;>
        rcases hsq with ⟨_, _, h2⟩ | ⟨_, _, h2⟩
      · exact Or.inr (Or.inr (Or.inl (h2.trans h)))
      · exact Or.inl (h2.trans h)
      · exact Or.inr (Or.inr (Or.inr (h2.trans h)))
      · exact Or.inr (Or.inl (h2.trans h))
    subst hji
    have hpm : ¬ NearM c s n (cellJ q a m) := hmin m (by omega)
    apply hpm
    rcases M.pi with ⟨g1, g2⟩ | ⟨g1, g2⟩ <;> rcases hsq with ⟨_, h1, _⟩ | ⟨_, h1, _⟩
    · rw [← h1, g1]; exact M.near_n
    · rw [← h1, g2]; exact M.near_n1
    · rw [← h1, g2]; exact M.near_n1
    · rw [← h1, g1]; exact M.near_n
  rcases M.entry hpat hmev t0pos htm (hmin (t0 - 1) (by omega)) ht0s.2 with ⟨he, rfl⟩ | ⟨he, rfl⟩
  · -- Into `c_0` along `s`: the strip now ends at `c_0`, a square of the new pair.
    have hl0 := (strip_cell hpat htm).1
    rw [he] at hl0
    have l0 : lat1 c a ∉ H := by
      have := (M.pat.2.1 0 (by omega)).1; rw [cellJ_zero] at this
      intro h; have := this.1 h; omega
    have hev0 : t0 % 2 = 0 := by
      by_contra hc; exact l0 (hl0.2 (by omega))
    have hlt : t0 < m := by
      by_contra hc
      have : t0 = m := by omega
      have hf := hfm; rw [← this, he] at hf
      have := (M.pat.2.2 0 (by have := M.two; omega)).1; rw [cellJ_zero] at this
      have := this hf; have := M.two; omega
    have hoc : outArc H c a = o := by rw [← he]; exact hfa t0 hlt
    have hcellc : ∀ t ≤ t0 + 1, IsCell V (cellJ q a t) := fun t ht => hcells t (by omega)
    refine ⟨t0, hcellc, ?_, npair o c a, ?_, ?_⟩
    · -- The strip pattern up to `c_0`.
      have l0' := lat0_after M.ev M.two M.pat
      have f0' := front0_after M.ev M.two M.pat
      have sa : ∀ t < t0, ∀ s', sideEdge (cellJ q a t) s' ∈ lowerCol H c a n ↔
          sideEdge (cellJ q a t) s' ∈ H := fun t ht s' => side_after (hmin t ht) s'
      refine ⟨?_, fun t ht => ?_, fun t ht => ?_⟩
      · have := sa 0 (by omega) a.opp
        rw [cellJ_zero] at this
        exact this.2 hpat.1
      · rcases Nat.lt_or_ge t t0 with h | h
        · rw [lat1_eq, lat2_eq, sa t h, sa t h, ← lat1_eq, ← lat2_eq]
          exact hpat.2.1 t (by omega)
        · have : t = t0 := by omega
          subst this; rw [he]
          exact ⟨⟨fun hh => absurd hh l0'.1, fun hh => by omega⟩,
            ⟨fun hh => absurd hh l0'.2, fun hh => by omega⟩⟩
      · rcases Nat.lt_or_ge t t0 with h | h
        · rw [show front (cellJ q a t) a = sideEdge (cellJ q a t) a from rfl, sa t h]
          rw [show sideEdge (cellJ q a t) a = front (cellJ q a t) a from rfl,
            hpat.2.2 t (by omega)]
          simp only [show t + 1 < m + 1 by omega, show t + 1 < t0 + 1 by omega]
        · have : t = t0 := by omega
          subst this; rw [he]
          simp only [lt_self_iff_false, iff_false]
          exact ⟨fun _ => by omega, fun _ => f0'⟩
    · exact (mem _).2 (Or.inl (by rw [hoc]))
    · have e1 : cellJ q a (t0 + 1) = cellJ c a 1 := by rw [← nb_cellJ, he, ← nb_cellJ, cellJ_zero]
      cases o
      · right; refine ⟨rfl, ?_, rfl⟩
        simp only [npair, Bool.false_eq_true, ↓reduceIte, newPairF]; exact he.symm
      · left; refine ⟨rfl, ?_, rfl⟩
        simp only [npair, ↓reduceIte, newPair]; exact e1.symm
  · -- Into `B` against `s`: the old pair would carry `D` of both signs.
    exfalso
    have hlB := (strip_cell hpat htm)
    rw [he] at hlB
    have bB : back (cellJ c s (n + 1)) s ∈ H := by
      rw [back_cellJ_succ]; exact frontn_mem M.ev M.two M.pat M.d1 M.d2 M.altB
    have lB := alt_lats M.altB (s' := s.opp) bB
    rw [latA_opp, show latB s.opp = latB s by cases s <;> rfl, ← lat1_eq] at lB
    have hev0 : t0 % 2 = 0 := by
      by_contra hc; rw [lat1_opp] at hlB; exact lB.1 (hlB.1.2 (by omega))
    have heqm : t0 = m := by
      by_contra hc
      have hfr : front (cellJ c s (n + 1)) s.opp ∈ H := bB
      have := hlB.2.2.1.1 hfr; omega
    subst heqm
    have hnext : cellJ q s.opp (t0 + 1) = cellJ c s n := by
      rw [← nb_cellJ, he, nb_cellJ_opp]
    have hDB := hD t0 le_rfl
    rw [he] at hDB
    have hDc := M.Dn hH' hpos
    have hup := (M.inv.f4 i M.hi).2.2.1
    rcases hsq with ⟨ho, h1, h2⟩ | ⟨ho, h1, h2⟩
    · rw [he] at h1; rw [hnext] at h2
      have hji : j = i := M.eq_i hj (Or.inr (Or.inr (Or.inl h2)))
      subst hji
      rcases M.po with ⟨hc, g1, _⟩ | ⟨hc, _, _⟩
      · exact absurd (cellJ_inj' (h1.symm.trans g1)) (by omega)
      · rw [ho] at hDB hrel; rw [hc] at hDc
        simp only [sgnD, Bool.false_eq_true, ↓reduceIte] at hDc hDB hrel
        exact pair_one_side M.hH hH' hup (by show 0 < D H H' j.top; rw [h1]; omega) (by rw [h2]; omega)
    · rw [he] at h1; rw [hnext] at h2
      have hji : j = i := M.eq_i hj (Or.inl h2)
      subst hji
      rcases M.po with ⟨hc, _, _⟩ | ⟨hc, g1, _⟩
      · rw [ho] at hDB hrel; rw [hc] at hDc
        simp only [sgnD, Bool.false_eq_true, ↓reduceIte] at hDc hDB hrel
        exact pair_one_side M.hH hH' hup (by show 0 < D H H' j.top; rw [h2]; omega) (by rw [h1]; omega)
      · exact absurd (cellJ_inj' (h1.symm.trans g1)) (by omega)

end transfer

end HP

end SolidGridHam
