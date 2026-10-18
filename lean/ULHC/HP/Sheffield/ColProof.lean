/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.HP.Sheffield.ColC

/-!
# The column field `col` at the end of a phase (docs/COL_SIDE.md §4)

`Stuck V H BS`: every critical square (dark back) is a bridge square or stuck: its run of equal
arcs through uncut cells ends at a non-cell or a cut square.

`col_of_stuck`: for a critical square `q` that is not a pair square,
* `q` a bridge square: it is an even square of its bridge, and its column runs to the pair;
* `q` stuck: the run forces the strip pattern; an odd end contradicts degree 2; an even end is
  Lemma C's cut square, which continues the column (induction on the cells of `V` on the ray).
-/

namespace ULHC

namespace HP

open Finset Classical

def BridgeSq (BS : List Bridge) (q : Pt) : Prop := ∃ b ∈ BS, ∃ j < b.r, q = b.cell j

def StuckAt (V : Finset Pt) (H : Finset Edge) (q : Pt) (a : Side) : Prop :=
  ∃ k, 1 ≤ k ∧ (∀ j, 1 ≤ j → j < k → IsCell V (cellJ q a j) ∧ ¬ CutSq H (cellJ q a j)) ∧
    (∀ j < k, outArc H (cellJ q a j) a = outArc H q a) ∧
    (¬ IsCell V (cellJ q a k) ∨ CutSq H (cellJ q a k))

def Stuck (V : Finset Pt) (H : Finset Edge) (BS : List Bridge) : Prop :=
  ∀ q a, IsCell V q → CriticalIn H q a → back q a ∈ H → BridgeSq BS q ∨ StuckAt V H q a

section colproof

variable {V W : Finset Pt} {d : Pt → ℕ} {H : Finset Edge} {t0 u0 : Pt}

lemma conn_of_uncut {F : Finset Edge} {c u v : Pt} (h : ¬ CutSq F c) (hu : IsCorner u c)
    (hv : IsCorner v c) : Conn F u v := by
  unfold CutSq at h
  obtain ⟨h1, h2, h3⟩ := not_not.1 h
  have all : ∀ z, IsCorner z c → Conn F c z := by
    intro z hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact Conn.refl _ _
    · exact h1
    · exact h3
    · exact h2
  exact (all u hu).symm.trans (all v hv)

lemma one_dark {q : Pt} {s : Side} (hcr : CriticalIn H q s) (hb : back q s ∈ H) {s' : Side}
    (h : sideEdge q s' ∈ H) : s' = s.opp := by
  obtain ⟨hbb, hff, hbf, hx⟩ := hcr
  have hf : front q s ∉ H := fun h' => by
    rcases hx with ⟨_, h2⟩ | ⟨_, h1⟩
    · exact h2 h'
    · exact h1 hb
  rcases side_cases s s' with rfl | rfl | rfl | rfl
  · exact absurd h hf
  · rfl
  · rw [← lat1_eq] at h; exact absurd ((ends_lat1 (c := q) (s := s)).conn h) hbf
  · rw [← lat2_eq] at h
    exact absurd (hbb.trans (((ends_lat2 (c := q) (s := s)).conn h).trans hff.symm)) hbf

-- Degree 2 at `front1 c` with both of `c`'s sides there dark.
--
lemma forcedA' {c : Pt} {s : Side} (hl : lat1 c s ∈ H) (hf : front c s ∈ H)
    (hd : deg H (front1 c s) = 2) : lat1 (nb c s) s ∉ H := by
  rw [deg_front1, ind_of_mem hl, ind_of_mem hf] at hd
  intro h; rw [ind_of_mem h] at hd; omega

lemma forcedB' {c : Pt} {s : Side} (hl : lat2 c s ∈ H) (hf : front c s ∈ H)
    (hd : deg H (front2 c s) = 2) : lat2 (nb c s) s ∉ H := by
  rw [deg_front2, ind_of_mem hl, ind_of_mem hf] at hd
  intro h; rw [ind_of_mem h] at hd; omega

-- Points of `V` on the ray of `q` in direction `a`.
--
noncomputable def rayN (V : Finset Pt) (q : Pt) (a : Side) : ℕ :=
  (V.filter (fun z => ∃ j, z = cellJ q a j)).card

lemma rayN_lt {q : Pt} {a : Side} (hq : q ∈ V) {k : ℕ} (hk : 1 ≤ k) :
    rayN V (cellJ q a k) a < rayN V q a := by
  unfold rayN
  apply Finset.card_lt_card
  refine ⟨fun z hz => ?_, fun hsub => ?_⟩
  · simp only [Finset.mem_filter] at hz ⊢
    obtain ⟨hzV, j, rfl⟩ := hz
    exact ⟨hzV, k + j, by rw [cellJ_add]⟩
  · have : q ∈ V.filter (fun z => ∃ j, z = cellJ q a j) :=
      Finset.mem_filter.2 ⟨hq, 0, by rw [cellJ_zero]⟩
    have h2 := hsub this
    simp only [Finset.mem_filter] at h2
    obtain ⟨_, j, hj⟩ := h2
    rw [cellJ_add] at hj
    have := cellJ_inj (c := q) (s := a) (i := k + j) (j := 0) (by rw [← hj, cellJ_zero])
    omega

-- Arcs of two squares of one column with the same parity: opposite exactly when their fronts
-- differ.
--
lemma arc_par {F : Finset Edge} {c : Pt} {a : Side} {i j : ℕ} (hij : i % 2 = j % 2)
    (h1 : front (cellJ c a i) a ∉ F) (h2 : front (cellJ c a j) a ∈ F) :
    outArc F (cellJ c a j) a = !outArc F (cellJ c a i) a := by
  rw [outArc_eq, outArc_eq, par_cellJ, par_cellJ]
  have e : decide (i % 2 = 1) = decide (j % 2 = 1) := by rw [hij]
  unfold front at h1 h2
  simp only [h1, h2, decide_true, decide_false, e]
  cases par c <;> cases decide (j % 2 = 1) <;> cases a.horiz <;> rfl

-- **A critical bridge square** is an even square before `A`, in the bridge's frame, and its
-- column runs to the pair.
--
theorem bridge_col {BS : List Bridge} {b : Bridge} (hbBS : b ∈ BS) (hR : RegionOK H b)
    (htwo : 2 ≤ b.r) (hev : b.r % 2 = 0) (hcells : ∀ j < b.r, IsCell V (b.cell j)) {j : ℕ}
    (hj : j < b.r) {s : Side} (hcr : CriticalIn H (b.cell j) s) (hbk : back (b.cell j) s ∈ H) :
    ColEnds V H (BS.map (Bridge.pairOf H)) (b.cell j) s (outArc H (b.cell j) s) := by
  have hmem : b.pairOf H ∈ BS.map (Bridge.pairOf H) := List.mem_map.2 ⟨b, hbBS, rfl⟩
  revert hmem
  obtain ⟨q, a, r⟩ := b
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 2 := ⟨r - 2, by simp only at htwo; omega⟩
  obtain ⟨bk, lat, lat0, latE, fr, frA, frE, _, _, _, _⟩ := hR
  simp only [Bridge.pairOf, Bridge.cell, Bridge.E, show m + 2 - 1 = m + 1 by omega,
    show m + 2 - 2 = m by omega] at *
  intro hmem
  have meven : m % 2 = 0 := by omega
  have od : ∀ {s'}, sideEdge (cellJ q a j) s' ∈ H → s' = s.opp := fun h => one_dark hcr hbk h
  have bJ : ∀ i, 1 ≤ i → i ≤ m + 1 → (back (cellJ q a i) a ∈ H ↔ front (cellJ q a (i - 1)) a ∈ H) :=
    fun i hi _ => by
      obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      rw [back_cellJ_succ, show i' + 1 - 1 = i' by omega]
  have noA : ∀ {x : Side}, x = x.opp → False := fun {x} h => by cases x <;> simp [Side.opp] at h
  rcases (show (j + 3 ≤ m + 2) ∨ j = m ∨ j = m + 1 by omega) with hlt | hjm | hjm
  · rcases Nat.mod_two_eq_zero_or_one j with je | jo
    · -- even: the frame is `a`
      have hb : sideEdge (cellJ q a j) a.opp ∈ H := by
        rcases Nat.eq_zero_or_pos j with h0 | hpos
        · subst h0; rw [cellJ_zero]; exact bk
        · have := (bJ j hpos (by omega)).2 ((fr (j - 1) (by omega)).2 (by omega))
          unfold back at this; exact this
      have hsa : s = a := by have := od hb; exact (opp_inj this).symm
      subst s
      have fj : front (cellJ q a j) a ∉ H := fun h => by have := (fr j hlt).1 h; omega
      have harc := arc_par (c := q) (a := a) (i := j) (j := m) (by omega) fj frA
      refine ⟨m - j, fun i hi => ?_, ⟨?_, fun i hi => ?_, fun i hi => ?_⟩, ?_⟩
      · rw [cellJ_add]; exact hcells _ (by omega)
      · rcases Nat.eq_zero_or_pos j with h0 | hpos
        · subst h0; rw [cellJ_zero]; exact bk
        · rw [bJ j hpos (by omega)]; exact (fr (j - 1) (by omega)).2 (by omega)
      · rw [cellJ_add]
        rcases Nat.eq_zero_or_pos (j + i) with h0 | hpos
        · rw [h0, cellJ_zero]
          exact ⟨⟨fun h => absurd h lat0.1, fun h => by omega⟩,
            ⟨fun h => absurd h lat0.2, fun h => by omega⟩⟩
        · obtain ⟨l1, l2⟩ := lat (j + i) hpos (by omega)
          exact ⟨by rw [l1]; omega, by rw [l2]; omega⟩
      · rw [cellJ_add]
        rcases (show j + i + 3 ≤ m + 2 ∨ j + i = m by omega) with h' | h'
        · rw [fr (j + i) h']; omega
        · rw [h']; exact ⟨fun _ => by omega, fun _ => frA⟩
      · refine ⟨_, hmem, ?_⟩
        rw [cellJ_add, cellJ_add, show j + (m - j) = m by omega,
          show j + (m - j + 1) = m + 1 by omega]
        cases ho : outArc H (cellJ q a j) a
        · rw [ho] at harc; simp only [Bool.not_false] at harc
          simp only [harc, Bool.true_eq_false, ↓reduceIte]
          simp
        · rw [ho] at harc; simp only [Bool.not_true] at harc
          simp only [harc, ↓reduceIte]
          simp
    · -- odd: two dark sides
      exfalso
      have h1 : sideEdge (cellJ q a j) a ∈ H := (fr j hlt).2 jo
      have h2 : sideEdge (cellJ q a j) (latA a) ∈ H := by
        rw [← lat1_eq]; exact ((lat j (by omega) (by omega)).1).2 jo
      have e1 := od h1; have e2 := od h2
      rw [← e1] at e2; cases a <;> simp [latA] at e2
  · subst j
    exfalso
    have h1 : sideEdge (cellJ q a m) a ∈ H := frA
    have h2 : sideEdge (cellJ q a m) a.opp ∈ H := by
      rcases Nat.eq_zero_or_pos m with h0 | hpos
      · rw [h0, cellJ_zero]; exact bk
      · have := (bJ m hpos (by omega)).2 ((fr (m - 1) (by omega)).2 (by omega))
        unfold back at this; exact this
    have e1 := od h1; have e2 := od h2
    rw [← e1] at e2; exact noA e2.symm
  · subst j
    exfalso
    have h1 : sideEdge (cellJ q a (m + 1)) a ∈ H := frE
    have h2 : sideEdge (cellJ q a (m + 1)) a.opp ∈ H := by
      have := (bJ (m + 1) (by omega) le_rfl).2 (by rw [show m + 1 - 1 = m by omega]; exact frA)
      unfold back at this; exact this
    have e1 := od h1; have e2 := od h2
    rw [← e1] at e2; exact noA e2.symm

-- The pair facts at a phase state, for `FP = BS.map (pairOf H)`.
--
theorem phase_fp (_hVW : V ⊆ W) (_hdc : ∀ q, IsCell V q → ∀ z, IsCorner z q → d z = 2)
    {BS : List Bridge} (hinv : PInv V W d H BS t0 u0) (hmerge : MergeOK V H BS) :
    (∀ q, IsCell V q → Alt H q → CutSq H q →
      ∃ i ∈ BS.map (Bridge.pairOf H), q = i.top ∨ q = i.bot) ∧
    (∀ i ∈ BS.map (Bridge.pairOf H), PairOK H i) ∧
    (∀ i ∈ BS.map (Bridge.pairOf H), Alt H i.top ∧ Alt H i.bot) ∧
    (∀ i ∈ BS.map (Bridge.pairOf H), sideEdge i.bot i.s ∈ H) ∧
    (∀ i ∈ BS.map (Bridge.pairOf H), IsCell V i.top ∧ IsCell V i.bot) := by
  have facts : ∀ i ∈ BS.map (Bridge.pairOf H), ∃ b ∈ BS, i = b.pairOf H := by
    intro i hi; obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hi; exact ⟨b, hb, rfl⟩
  refine ⟨?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · intro q hq ha hc
    obtain ⟨b, hb, hqb⟩ := hmerge q hq ha hc
    obtain ⟨hR, h2, he, _⟩ := hinv.reg b hb
    refine ⟨b.pairOf H, List.mem_map.2 ⟨b, hb, rfl⟩, ?_⟩
    rcases pair_squares hR h2 he with ⟨ht, hbt⟩ | ⟨ht, hbt⟩ <;> rcases hqb with rfl | rfl
    · exact Or.inl ht.symm
    · exact Or.inr hbt.symm
    · exact Or.inr hbt.symm
    · exact Or.inl ht.symm
  all_goals
    obtain ⟨b, hb, rfl⟩ := facts i hi
    obtain ⟨hR, h2, he, hc⟩ := hinv.reg b hb
  · exact (pair_facts hR h2 he).1
  · exact (pair_facts hR h2 he).2.1
  · exact (pair_facts hR h2 he).2.2.1
  · have cA := hc (b.r - 2) (by omega)
    have cE : IsCell V b.E := hc (b.r - 1) (by omega)
    rcases pair_squares hR h2 he with ⟨ht, hbt⟩ | ⟨ht, hbt⟩ <;> rw [ht, hbt]
    · exact ⟨cA, cE⟩
    · exact ⟨cE, cA⟩

-- **The column field at the end of a phase.**
--
theorem col_of_stuck (hVW : V ⊆ W) (hdc : ∀ q, IsCell V q → ∀ z, IsCorner z q → d z = 2)
    {BS : List Bridge} (hinv : PInv V W d H BS t0 u0) (hmerge : MergeOK V H BS)
    (hstuck : Stuck V H BS) :
    ∀ q s, IsCell V q → CriticalIn H q s → back q s ∈ H →
      (∀ i ∈ BS.map (Bridge.pairOf H), q ≠ i.top ∧ q ≠ i.bot) →
      ColEnds V H (BS.map (Bridge.pairOf H)) q s (outArc H q s) ∨
        ColOut V H q s (outArc H q s) := by
  have hdegc := degc_of hVW hdc hinv.fac
  obtain ⟨hf2, hpok, hpalt, hpdark, hpcell⟩ := phase_fp hVW hdc hinv hmerge
  suffices key : ∀ N q s, rayN V q s = N → IsCell V q → CriticalIn H q s → back q s ∈ H →
      (∀ i ∈ BS.map (Bridge.pairOf H), q ≠ i.top ∧ q ≠ i.bot) →
      ColEnds V H (BS.map (Bridge.pairOf H)) q s (outArc H q s) ∨
        ColOut V H q s (outArc H q s) from
    fun q s => key _ q s rfl
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro q s hN hq hcr hb hnp
  rcases hstuck q s hq hcr hb with ⟨b, hbBS, j, hj, rfl⟩ | ⟨k, hk1, hrun, harcs, hend⟩
  · obtain ⟨hR, two, ev, cells⟩ := hinv.reg b hbBS
    exact Or.inl (bridge_col hbBS hR two ev cells hj hcr hb)
  have cellsk : ∀ j < k, IsCell V (cellJ q s j) := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · rw [h0, cellJ_zero]; exact hq
    · exact (hrun j hpos hj).1
  have rp := run_pat hcr hb (n := k - 1)
    (fun j hj => ⟨hdegc _ (cellsk j (by omega)) _ (isCorner_front1 _ _),
      hdegc _ (cellsk j (by omega)) _ (isCorner_front2 _ _)⟩)
    (fun j hj => harcs j (by omega))
  by_cases hck : IsCell V (cellJ q s k)
  swap
  · right
    exact ⟨k - 1, fun j hj => cellsk j (by omega), fun j hj => harcs j (by omega),
      by rw [show k - 1 + 1 = k by omega]; exact hck⟩
  have hcut : CutSq H (cellJ q s k) := hend.resolve_left (not_not.2 hck)
  have hprev : cellJ q s k = nb (cellJ q s (k - 1)) s := by
    rw [nb_cellJ, show k - 1 + 1 = k by omega]
  have dk1 := hdegc _ (cellsk (k - 1) (by omega)) _ (isCorner_front1 (cellJ q s (k - 1)) s)
  have dk2 := hdegc _ (cellsk (k - 1) (by omega)) _ (isCorner_front2 (cellJ q s (k - 1)) s)
  obtain ⟨r1, r2, rf⟩ := rp (k - 1) le_rfl
  rcases Nat.mod_two_eq_zero_or_one k with ke | ko
  · -- `k` even: Lemma C at `c_k`.
    have l1 : lat1 (cellJ q s (k - 1)) s ∈ H := r1.2 (by omega)
    have l2 : lat2 (cellJ q s (k - 1)) s ∈ H := r2.2 (by omega)
    have f1 : front (cellJ q s (k - 1)) s ∈ H := rf.2 (by omega)
    have lk1 : lat1 (cellJ q s k) s ∉ H := by rw [hprev]; exact forcedA' l1 f1 dk1
    have lk2 : lat2 (cellJ q s k) s ∉ H := by rw [hprev]; exact forcedB' l2 f1 dk2
    have bk : back (cellJ q s k) s ∈ H := by rw [hprev, back_nb]; exact f1
    have harc : outArc H (cellJ q s k) s.opp = !outArc H q s := by
      rw [hprev, outArc_nb_opp, harcs (k - 1) (by omega)]
    have nAlt : ¬ Alt H (cellJ q s (k - 1)) := fun ha => by
      have := (alt_lats ha (s' := s) f1).1; rw [← lat1_eq] at this; exact this l1
    have hHb : ∀ i ∈ BS.map (Bridge.pairOf H), ¬ ((cellJ q s k = i.top ∧
        nb (cellJ q s k) s.opp = i.bot) ∨ (cellJ q s k = i.bot ∧ nb (cellJ q s k) s.opp = i.top)) := by
      intro i hi h
      have hb' : nb (cellJ q s k) s.opp = cellJ q s (k - 1) := by rw [hprev, nb_nb_opp]
      rcases h with ⟨_, h⟩ | ⟨_, h⟩ <;> rw [hb'] at h
      · exact nAlt (h ▸ (hpalt i hi).2)
      · exact nAlt (h ▸ (hpalt i hi).1)
    have hcolg := fun (hcrg : CriticalIn H (cellJ q s k) s)
        (hnpg : ∀ i ∈ BS.map (Bridge.pairOf H), cellJ q s k ≠ i.top ∧ cellJ q s k ≠ i.bot) =>
      ih (rayN V (cellJ q s k) s) (by rw [← hN]; exact rayN_lt hq.1 hk1) (cellJ q s k) s rfl
        hck hcrg bk hnpg
    have hrun' : StripRun H q s k := ⟨hb, fun r hr => ⟨(rp r (by omega)).1, (rp r (by omega)).2.1⟩,
      fun r hr => (rp r (by omega)).2.2⟩
    rcases lemmaC hdegc hf2 hpok hpalt hpdark hpcell hck bk lk1 lk2 hcut harc hHb hcolg with
      ⟨n', cells', pat', i, hi, hpair⟩ | ⟨n', cells', arcs', out'⟩
    · left
      refine ⟨k + n', fun j hj => ?_, ?_, i, hi, ?_⟩
      · rcases Nat.lt_or_ge j k with hlt | hge
        · exact cellsk j hlt
        · have := cells' (j - k) (by omega); rwa [cellJ_add, show k + (j - k) = j by omega] at this
      · have := stripPat_append ke (by omega) hrun' pat'
        rwa [show k + (n' + 1) = k + n' + 1 by omega] at this
      · rw [cellJ_add, cellJ_add] at hpair
        rwa [show k + (n' + 1) = k + n' + 1 by omega] at hpair
    · right
      refine ⟨k + n', fun j hj => ?_, fun j hj => ?_, ?_⟩
      · rcases Nat.lt_or_ge j k with hlt | hge
        · exact cellsk j hlt
        · have := cells' (j - k) (by omega); rwa [cellJ_add, show k + (j - k) = j by omega] at this
      · rcases Nat.lt_or_ge j k with hlt | hge
        · exact harcs j hlt
        · have := arcs' (j - k) (by omega); rwa [cellJ_add, show k + (j - k) = j by omega] at this
      · rw [cellJ_add] at out'; rwa [show k + (n' + 1) = k + n' + 1 by omega] at out'
  · -- `k` odd: `c_k` would be uncut.
    exfalso
    have l1 : lat1 (cellJ q s (k - 1)) s ∉ H := fun h => by have := r1.1 h; omega
    have l2 : lat2 (cellJ q s (k - 1)) s ∉ H := fun h => by have := r2.1 h; omega
    have f1 : front (cellJ q s (k - 1)) s ∉ H := fun h => by have := rf.1 h; omega
    obtain ⟨_, lk1⟩ := forcedA l1 f1 dk1
    obtain ⟨_, lk2⟩ := forcedB l2 f1 dk2
    rw [← hprev] at lk1 lk2
    have hfc : Conn H (front1 (cellJ q s (k - 1)) s) (front2 (cellJ q s (k - 1)) s) := by
      rcases Nat.eq_zero_or_pos (k - 1) with h0 | hpos
      · rw [h0, cellJ_zero]; exact hcr.2.1
      · exact conn_of_uncut (hrun (k - 1) hpos (by omega)).2 (isCorner_front1 _ _)
          (isCorner_front2 _ _)
    apply uncut_of (s := s) _ ((ends_lat1 (c := cellJ q s k) (s := s)).conn lk1)
      ((ends_lat2 (c := cellJ q s k) (s := s)).conn lk2) hcut
    rw [back1_col hk1, back2_col hk1]; exact hfc

end colproof

end HP

end ULHC
