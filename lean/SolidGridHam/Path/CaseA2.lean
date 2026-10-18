/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import SolidGridHam.Path.CaseA1

@[expose] public section

/-!
# Lemma 4, case A2′ (docs/S4_UNDO.md §II.3)

Let `X` be the square beyond `E_i` (across its dark front), with light laterals. Degree 2 at the
front corners of `E_i` darkens the outer edges there, so each side square of `E_i` is merging if it
is a cell, and one of them is. By `MergeOK` it is a pair square, and the region freeze and `NotZ`
leave only: it is the start of a length-2 bridge `j` (newer than `i`) whose `E_j` is beside `X`.
Then the start pair of `j` has node `i`. If `X` is the start of the chain operation, its pair has
node `j`, so `j` is lowered and the pending pair after `j` has node `i`, which is undone: impossible.
If `X` is uncut, `E_j`'s back and front corners on `X`'s side are joined: impossible.
-/

namespace SolidGridHam

namespace HP

open Finset Classical

lemma outer1_eq_side (X : Pt) (a : Side) :
    outer1 (nb X a.opp) a = sideEdge (nb X (latA a)) a.opp := by
  obtain ⟨x, y⟩ := X
  cases a <;> simp [outer1, nb, latA, Side.opp, sideEdge, bot, top, lft, rgt]

lemma outer2_eq_side (X : Pt) (a : Side) :
    outer2 (nb X a.opp) a = sideEdge (nb X (latB a)) a.opp := by
  obtain ⟨x, y⟩ := X
  cases a <;> simp [outer2, nb, latB, Side.opp, sideEdge, bot, top, lft, rgt]

lemma mem_drop_index {BS : List Bridge} {m : ℕ} {b : Bridge} (h : b ∈ BS.drop m) :
    ∃ j, m ≤ j ∧ ∃ hj : j < BS.length, BS[j]'hj = b := by
  rw [List.mem_iff_getElem] at h
  obtain ⟨t, ht, rfl⟩ := h
  simp only [List.length_drop] at ht
  exact ⟨m + t, by omega, by omega, by simp [List.getElem_drop]⟩

-- The frame of a pair square of `b'` sitting where a cell has dark back and front in frame `a`.
--
lemma pair_frame {F : Finset Edge} {b' : Bridge} (hR' : RegionOK F b') (_htwo : 2 ≤ b'.r)
    {S : Pt} {a : Side} (hl1 : lat1 S a ∉ F) (hl2 : lat2 S a ∉ F)
    (hS : S = b'.cell (b'.r - 2) ∨ S = b'.E) : b'.a = a ∨ b'.a = a.opp := by
  have hfr : front S b'.a ∈ F := by
    rcases hS with rfl | rfl
    · exact hR'.frA
    · exact hR'.frE
  rcases perp_or (a := a) (a' := b'.a) with h | hperp
  · exact h
  · exfalso
    unfold front at hfr
    rcases lat_of_perp (Y := S) hperp with h | h <;> rw [h] at hfr
    · exact hl1 hfr
    · exact hl2 hfr

-- `E`'s side cell, the cell beyond `E`, and the cell beyond the side cell.
--
lemma beyond_side (E : Pt) (a : Side) : nb (nb E a) (latA a) = nb (nb E (latA a)) a :=
  (side_comm E a (Or.inl rfl)).symm

lemma beyond_sideB (E : Pt) (a : Side) : nb (nb E a) (latB a) = nb (nb E (latB a)) a :=
  (side_comm E a (Or.inr rfl)).symm

-- **Ext.** A row square at an odd index (or an even row's last square), whose lateral `lat1` is
-- the front of `E`, would need a dark edge at its back corner that is a light lateral of `E`.
--
lemma ext1 {F : Finset Edge} {q : Pt} {a : Side} {j : ℕ} (hj : 1 ≤ j)
    (hdeg : deg F (front1 (cellJ q a (j - 1)) a) = 2)
    (hl : lat1 (cellJ q a (j - 1)) a ∉ F) (hf : front (cellJ q a (j - 1)) a ∉ F)
    (he : lat1 (cellJ q a j) a ∈ F)
    (hout : sideEdge (nb (cellJ q a j) (latA a)) a.opp ∉ F) : False := by
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hdeg hl hf
  rw [deg_front1, nb_cellJ, ind_of_not_mem hl, ind_of_not_mem hf, ind_of_mem he] at hdeg
  have : outer1 (cellJ q a j') a = sideEdge (nb (cellJ q a (j' + 1)) (latA a)) a.opp := by
    rw [← outer1_eq_side, ← nb_cellJ, nb_nb_opp]
  rw [this, ind_of_not_mem hout] at hdeg
  omega

lemma ext2 {F : Finset Edge} {q : Pt} {a : Side} {j : ℕ} (hj : 1 ≤ j)
    (hdeg : deg F (front2 (cellJ q a (j - 1)) a) = 2)
    (hl : lat2 (cellJ q a (j - 1)) a ∉ F) (hf : front (cellJ q a (j - 1)) a ∉ F)
    (he : lat2 (cellJ q a j) a ∈ F)
    (hout : sideEdge (nb (cellJ q a j) (latB a)) a.opp ∉ F) : False := by
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hdeg hl hf
  rw [deg_front2, nb_cellJ, ind_of_not_mem hl, ind_of_not_mem hf, ind_of_mem he] at hdeg
  have : outer2 (cellJ q a j') a = sideEdge (nb (cellJ q a (j' + 1)) (latB a)) a.opp := by
    rw [← outer2_eq_side, ← nb_cellJ, nb_nb_opp]
  rw [this, ind_of_not_mem hout] at hdeg
  omega

lemma perpA_opp {a c : Side} (h : latA a = c.opp) : a.opp = latA c ∨ a.opp = latB c := by
  cases a <;> cases c <;> simp_all [latA, latB, Side.opp]

lemma perpB_opp {a c : Side} (h : latB a = c.opp) : a.opp = latA c ∨ a.opp = latB c := by
  cases a <;> cases c <;> simp_all [latA, latB, Side.opp]

section a2p

variable {V W : Finset Pt} {d : Pt → ℕ} {t0 u0 : Pt} {H0 : Finset Edge}
  (hVW : V ⊆ W) (hdc : ∀ q, IsCell V q → ∀ z, IsCorner z q → d z = 2)
  (h0 : IsFactor W d H0) (hout0 : ∀ e ∈ H0, (e.p ∉ V → e.q = t0 ∨ e.q = u0) ∧ (e.q ∉ V → e.p = t0 ∨ e.p = u0))
include hVW hdc h0 hout0

-- **A2′ core, side `latA`.** The side cell of `E_i` on the `latA` side is merging and not a
-- pair square.
--
theorem sideA_merging {BS : List Bridge} {H : Finset Edge} (hr : Reach V H0 H BS) {uv : Pt × Pt}
    (hn : ¬ Conn H uv.1 uv.2) {i : ℕ} (hi : i < BS.length) (hlow : lowAt H BS uv i = false)
    {m : ℕ} (hm : m ≤ i)
    (hXl1 : lat1 (nb (BS[i]'hi).E (BS[i]'hi).a) (BS[i]'hi).a ∉ seqH H0 (BS.drop m))
    (hkind : (∃ j', j' ≤ m ∧ pendAt H BS uv j' = (back1 (nb (BS[i]'hi).E (BS[i]'hi).a) (BS[i]'hi).a,
        front1 (nb (BS[i]'hi).E (BS[i]'hi).a) (BS[i]'hi).a) ∧
        Conn (seqH H0 (BS.drop m)) (back1 (nb (BS[i]'hi).E (BS[i]'hi).a) (BS[i]'hi).a)
          (back2 (nb (BS[i]'hi).E (BS[i]'hi).a) (BS[i]'hi).a) ∧
        Conn (seqH H0 (BS.drop m)) (front1 (nb (BS[i]'hi).E (BS[i]'hi).a) (BS[i]'hi).a)
          (front2 (nb (BS[i]'hi).E (BS[i]'hi).a) (BS[i]'hi).a)) ∨
      ¬ CutSq (seqH H0 (BS.drop m)) (nb (BS[i]'hi).E (BS[i]'hi).a)) :
    Alt (seqH H0 (BS.drop m)) (nb (BS[i]'hi).E (latA (BS[i]'hi).a)) ∧
      CutSq (seqH H0 (BS.drop m)) (nb (BS[i]'hi).E (latA (BS[i]'hi).a)) ∧
      ¬ ∃ b' ∈ BS.drop m, nb (BS[i]'hi).E (latA (BS[i]'hi).a) = b'.cell (b'.r - 2) ∨
        nb (BS[i]'hi).E (latA (BS[i]'hi).a) = b'.E := by
  obtain ⟨hrm, hmemb, hR, htwo, hev⟩ := frozen_at hVW hdc h0 hout0 hr hm hi
  set F := seqH H0 (BS.drop m) with hF
  set b := BS[i]'hi with hb
  have hinvF := pinv_reach (t0 := t0) (u0 := u0) hVW hdc h0 hout0 hrm
  have hdegcF := degc_of hVW hdc hinvF.fac
  have hEcell : IsCell V b.E := (hinvF.reg b hmemb).2.2.2 _ (by omega)
  obtain ⟨c1, c2⟩ := cutE_both hR htwo
  have bE : back b.E b.a ∈ F := by
    have := hR.frA
    unfold Bridge.E Bridge.cell at *
    rw [show b.r - 1 = b.r - 2 + 1 by omega, back_cellJ_succ]; exact this
  -- The outer edge at `E`'s front corner on the `latA` side is dark.
  --
  have oA : outer1 b.E b.a ∈ F := by
    have dF1 := hdegcF _ hEcell (front1 b.E b.a) (isCorner_front1 _ _)
    rw [deg_front1, ind_of_not_mem hR.latE.1, ind_of_mem hR.frE, ind_of_not_mem hXl1] at dF1
    by_contra h; rw [ind_of_not_mem h] at dF1; omega
  -- The side cell `S` is merging.
  --
  set S := nb b.E (latA b.a) with hSdef
  have frS : front S b.a ∈ F := by rw [hSdef, side_front]; exact oA
  have bkS : back S b.a ∈ F := by
    unfold back
    have := side_backA b.q b.a (i := b.r - 1) (by omega)
    have hE : b.E = cellJ b.q b.a (b.r - 1) := rfl
    rw [hSdef, hE, this, show b.r - 1 - 1 = b.r - 2 by omega]
    have := (hR.outer (b.r - 2) (by omega)).1.2 (by omega)
    unfold Bridge.cell at this; exact this
  have l2S : lat2 S b.a ∉ F := by rw [hSdef, side_near]; exact hR.latE.1
  have l1S : lat1 S b.a ∉ F := by
    intro h
    have e1 := (ends_lat1 (c := S) (s := b.a)).conn h
    have e2 := (ends_back (c := S) (s := b.a)).conn bkS
    have e3 := (ends_front (c := S) (s := b.a)).conn frS
    rw [hSdef, sideA_back2] at e2; rw [hSdef, sideA_front2] at e3
    exact c1 ((e2.symm.trans e1).trans e3)
  have altS := alt_of_bf bkS frS l1S l2S
  have isCutCell : CutSq F S := cutSq_of_corners (isCorner_back2 S b.a) (isCorner_front2 S b.a)
    (by rw [hSdef, sideA_back2, sideA_front2]; exact c1)
  refine ⟨altS, isCutCell, ?_⟩
  rintro ⟨b', hb', hSb'⟩
  obtain ⟨hR', two', ev', cells'⟩ := hinvF.reg b' hb'
  obtain ⟨j, hjm, hj, hbj⟩ := mem_drop_index hb'
  have hframe := pair_frame hR' two' l1S l2S hSb'
  -- `S` is not a square of `b`.
  have hji : j ≠ i := by
    intro h
    subst h
    have hbb : b' = b := hbj.symm
    rw [hbb] at hSb'
    have hE : b.E = cellJ b.q b.a (b.r - 1) := rfl
    rcases hSb' with h | h
    · exact side_ne_col b.q b.a (Or.inl rfl) (b.r - 1) (b.r - 2) (by rw [← hE]; exact h)
    · exact side_ne_col b.q b.a (Or.inl rfl) (b.r - 1) (b.r - 1) (by rw [← hE]; exact h)
  have hsep := (pinv_reach (t0 := t0) (u0 := u0) hVW hdc h0 hout0 hr).sep
  have Eb_side : b.E = nb S (latB b.a) := by
    rw [hSdef, latB_eq_opp, nb_nb_opp]
  have hEb' : b'.E = nb (b'.cell (b'.r - 2)) b'.a := by
    unfold Bridge.E Bridge.cell; rw [nb_cellJ, show b'.r - 2 + 1 = b'.r - 1 by omega]
  rcases Nat.lt_or_gt_of_ne hji with hlt | hgt
  · -- `b'` is newer than `b`
    have hz : NotZ (BS[j]'hj) (BS[i]'hi) := List.pairwise_iff_getElem.1 hsep j i hj hi hlt
    rw [hbj] at hz
    obtain ⟨_, _, hside⟩ := hz
    rcases hSb' with hA | hE'
    · rcases hframe with ha' | ha'
      · -- `E'` beyond `S`: a length-2 bridge started at `S`
        have hE'S : b'.E = nb S b.a := by rw [hEb', ← hA, ha']
        by_cases r4 : 4 ≤ b'.r
        · obtain ⟨_, _, hRj, htwoj, _⟩ := frozen_at hVW hdc h0 hout0 hr (m := j + 1) (by omega) hi
          have hrow := rowAt_at hVW hdc h0 hout0 hr hj
          rw [hbj] at hrow
          have hun := hrow.uncut (b'.r - 2) (by omega) (by omega)
          have hA' : cellJ b'.q b'.a (b'.r - 2) = S := hA.symm
          rw [hA'] at hun
          obtain ⟨c1', _⟩ := cutE_both hRj htwoj
          exact hun (cutSq_of_corners (isCorner_back2 S b.a) (isCorner_front2 S b.a)
            (by rw [hSdef, sideA_back2, sideA_front2]; exact c1'))
        · have hr2 : b'.r = 2 := by omega
          have hq : b'.q = S := by
            have := hA.symm; unfold Bridge.cell at this; rw [hr2, Nat.sub_self, cellJ_zero] at this
            exact this
          have hrow := rowAt_at hVW hdc h0 hout0 hr hj
          rw [hbj] at hrow
          rw [hq, ha'] at hrow
          have hR2 := isEqv_conn (seqH H0 (BS.drop (j + 1)))
          have hmS : Matched (Conn (seqH H0 (BS.drop (j + 1)))) (back1 S b.a) (front1 S b.a)
              (back1 b.E b.a) (front1 b.E b.a) := by
            have hu : Ends (lat2 S b.a) (back1 b.E b.a) (front1 b.E b.a) := by
              have := ends_lat2 S b.a; rwa [hSdef, sideA_back2, sideA_front2] at this
            exact lat_matched hrow.crit.1 hrow.crit.2.1 (Or.inr rfl) hu
          have hn1 := sameNodeI' hVW hdc h0 hout0 hr hi (m := j + 1) (by omega) hmS
          set X := nb b.E b.a with hXdef
          have hlatX : lat1 X b.a = lat2 b'.E b.a := by
            rw [hE'S, hSdef, ← beyond_side, side_near]
          have bE' : back b'.E b'.a ∈ F := by
            have := hR'.frA
            unfold Bridge.E Bridge.cell at *
            rw [show b'.r - 1 = b'.r - 2 + 1 by omega, back_cellJ_succ]; exact this
          have hmE' : Matched (Conn F) (back2 b'.E b.a) (front2 b'.E b.a) (back1 b'.E b'.a)
              (front1 b'.E b'.a) := by
            rw [ha']
            rw [ha'] at bE'
            have := hR'.frE; rw [ha'] at this
            exact Or.inl ⟨((ends_back (c := b'.E) (s := b.a)).conn bE').symm,
              ((ends_front (c := b'.E) (s := b.a)).conn this).symm⟩
          have hEX : Ends (lat1 X b.a) (back2 b'.E b.a) (front2 b'.E b.a) := by
            rw [hlatX]; exact ends_lat2 _ _
          rcases hkind with ⟨j', hj'm, hpend, hb1, hf1⟩ | hunc
          · have hmX := Matched.trans (isEqv_conn F)
              (lat_matched hb1 hf1 (Or.inl rfl) hEX) hmE'
            have hmX' : Matched (Conn F) (back1 X b.a) (front1 X b.a)
                (back1 (BS[j]'hj).E (BS[j]'hj).a) (front1 (BS[j]'hj).E (BS[j]'hj).a) := by
              rw [hbj]; exact hmX
            have hnj0 := sameNodeI' hVW hdc h0 hout0 hr hj hjm hmX'
            have hnj : nodeI H0 BS (pendAt H BS uv j').1 (pendAt H BS uv j').2 = j := by
              rw [hpend]; exact hnj0
            have hlowj : lowAt H BS uv j = true := by
              by_contra hl
              have := (node_pend hVW hdc h0 hout0 hr hn (j - j') j' j rfl (by omega) hj).1
                (by simpa using hl)
              exact this hnj
            obtain ⟨_, _, _, f4⟩ := pend_facts hVW hdc h0 hout0 hr hn (k := j) hj
            have hp1 := f4 (by omega)
            rw [ite_eq_left hlowj] at hp1
            have hne := (node_pend hVW hdc h0 hout0 hr hn (i - (j + 1)) (j + 1) i rfl (by omega)
              hi).1 hlow
            rw [hp1] at hne
            apply hne
            simp only [rowStartPair]
            rw [hbj, hq, ha']
            exact hn1
          · have hc := conn_of_uncut hunc (isCorner_back1 X b.a) (isCorner_front1 X b.a)
            have hm1 := Matched.of_ends (isEqv_conn F) (ends_lat1 X b.a) hEX
            have hc2 : Conn F (back2 b'.E b.a) (front2 b'.E b.a) := by
              rcases hm1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
              · exact (h1.symm.trans hc).trans h2
              · exact (h2.symm.trans hc.symm).trans h1
            obtain ⟨c1', _⟩ := cutE_both hR' two'
            apply c1'
            rcases hmE' with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · exact (h1.symm.trans hc2).trans h2
            · exact (h2.symm.trans hc2.symm).trans h1
      · -- `E'` before `S`: a side cell of `b` at `r - 2`
        apply (hside (b.r - 2) (by show b.r - 2 + 1 ≤ b.r; omega)).1
        rw [hEb', ← hA, ha', hSdef, side_comm _ _ (latAB_opp (Or.inl rfl))]
        unfold Bridge.E Bridge.cell
        rw [show b.r - 1 = b.r - 2 + 1 by omega, nb_cellJ_opp]
    · exact (hside (b.r - 1) (by show b.r - 1 + 1 ≤ b.r; omega)).1 (by rw [← hE', hSdef]; rfl)
  · -- `b` is newer than `b'`: `E_b` beside `S` is a side cell of `b'`
    have hz : NotZ (BS[i]'hi) b' := by
      have := List.pairwise_iff_getElem.1 hsep i j hi hj hgt; rwa [hbj] at this
    obtain ⟨_, _, hside⟩ := hz
    have hl : latB b.a = latB b'.a := by
      rcases hframe with h | h <;> rw [h]; exact (latB_opp b.a).symm
    rcases hSb' with hA | hE'
    · exact (hside (b'.r - 2) (by have := two'; omega)).2 (by rw [← hA, ← hl]; exact Eb_side)
    · exact (hside (b'.r - 1) (by have := two'; omega)).2 (by
        have : b'.cell (b'.r - 1) = b'.E := rfl
        rw [this, ← hE', ← hl]; exact Eb_side)

-- **A2′, side `latA`.** The side cell of `E_i` on the `latA` side is not a cell.
--
theorem a2p_sideA {BS : List Bridge} {H : Finset Edge} (hr : Reach V H0 H BS) {uv : Pt × Pt}
    (hn : ¬ Conn H uv.1 uv.2) {i : ℕ} (hi : i < BS.length) (hlow : lowAt H BS uv i = false)
    {m : ℕ} (hm : m ≤ i) (hmerge : MergeOK V (seqH H0 (BS.drop m)) (BS.drop m))
    (hXl1 : lat1 (nb (BS[i]'hi).E (BS[i]'hi).a) (BS[i]'hi).a ∉ seqH H0 (BS.drop m))
    (hkind : (∃ j', j' ≤ m ∧ pendAt H BS uv j' = (back1 (nb (BS[i]'hi).E (BS[i]'hi).a) (BS[i]'hi).a,
        front1 (nb (BS[i]'hi).E (BS[i]'hi).a) (BS[i]'hi).a) ∧
        Conn (seqH H0 (BS.drop m)) (back1 (nb (BS[i]'hi).E (BS[i]'hi).a) (BS[i]'hi).a)
          (back2 (nb (BS[i]'hi).E (BS[i]'hi).a) (BS[i]'hi).a) ∧
        Conn (seqH H0 (BS.drop m)) (front1 (nb (BS[i]'hi).E (BS[i]'hi).a) (BS[i]'hi).a)
          (front2 (nb (BS[i]'hi).E (BS[i]'hi).a) (BS[i]'hi).a)) ∨
      ¬ CutSq (seqH H0 (BS.drop m)) (nb (BS[i]'hi).E (BS[i]'hi).a))
    (hS : IsCell V (nb (BS[i]'hi).E (latA (BS[i]'hi).a))) : False := by
  obtain ⟨altS, isCutCell, hnp⟩ := sideA_merging hVW hdc h0 hout0 hr hn hi hlow hm hXl1 hkind
  exact hnp (hmerge _ hS altS isCutCell)

-- **A2′ core, side `latB`.** The side cell of `E_i` on the `latB` side is merging and not a
-- pair square.
--
theorem sideB_merging {BS : List Bridge} {H : Finset Edge} (hr : Reach V H0 H BS) {uv : Pt × Pt}
    (hn : ¬ Conn H uv.1 uv.2) {i : ℕ} (hi : i < BS.length) (hlow : lowAt H BS uv i = false)
    {m : ℕ} (hm : m ≤ i)
    (hXl2 : lat2 (nb (BS[i]'hi).E (BS[i]'hi).a) (BS[i]'hi).a ∉ seqH H0 (BS.drop m))
    (hkind : (∃ j', j' ≤ m ∧ pendAt H BS uv j' = (back1 (nb (BS[i]'hi).E (BS[i]'hi).a) (BS[i]'hi).a,
        front1 (nb (BS[i]'hi).E (BS[i]'hi).a) (BS[i]'hi).a) ∧
        Conn (seqH H0 (BS.drop m)) (back1 (nb (BS[i]'hi).E (BS[i]'hi).a) (BS[i]'hi).a)
          (back2 (nb (BS[i]'hi).E (BS[i]'hi).a) (BS[i]'hi).a) ∧
        Conn (seqH H0 (BS.drop m)) (front1 (nb (BS[i]'hi).E (BS[i]'hi).a) (BS[i]'hi).a)
          (front2 (nb (BS[i]'hi).E (BS[i]'hi).a) (BS[i]'hi).a)) ∨
      ¬ CutSq (seqH H0 (BS.drop m)) (nb (BS[i]'hi).E (BS[i]'hi).a)) :
    Alt (seqH H0 (BS.drop m)) (nb (BS[i]'hi).E (latB (BS[i]'hi).a)) ∧
      CutSq (seqH H0 (BS.drop m)) (nb (BS[i]'hi).E (latB (BS[i]'hi).a)) ∧
      ¬ ∃ b' ∈ BS.drop m, nb (BS[i]'hi).E (latB (BS[i]'hi).a) = b'.cell (b'.r - 2) ∨
        nb (BS[i]'hi).E (latB (BS[i]'hi).a) = b'.E := by
  obtain ⟨hrm, hmemb, hR, htwo, hev⟩ := frozen_at hVW hdc h0 hout0 hr hm hi
  set F := seqH H0 (BS.drop m) with hF
  set b := BS[i]'hi with hb
  have hinvF := pinv_reach (t0 := t0) (u0 := u0) hVW hdc h0 hout0 hrm
  have hdegcF := degc_of hVW hdc hinvF.fac
  have hEcell : IsCell V b.E := (hinvF.reg b hmemb).2.2.2 _ (by omega)
  obtain ⟨c1, c2⟩ := cutE_both hR htwo
  have bE : back b.E b.a ∈ F := by
    have := hR.frA
    unfold Bridge.E Bridge.cell at *
    rw [show b.r - 1 = b.r - 2 + 1 by omega, back_cellJ_succ]; exact this
  -- The outer edge at `E`'s front corner on the `latB` side is dark.
  --
  have oA : outer2 b.E b.a ∈ F := by
    have dF1 := hdegcF _ hEcell (front2 b.E b.a) (isCorner_front2 _ _)
    rw [deg_front2, ind_of_not_mem hR.latE.2, ind_of_mem hR.frE, ind_of_not_mem hXl2] at dF1
    by_contra h; rw [ind_of_not_mem h] at dF1; omega
  -- The side cell `S` is merging.
  --
  set S := nb b.E (latB b.a) with hSdef
  have frS : front S b.a ∈ F := by rw [hSdef, sideB_front]; exact oA
  have bkS : back S b.a ∈ F := by
    unfold back
    have := side_backB b.q b.a (i := b.r - 1) (by omega)
    have hE : b.E = cellJ b.q b.a (b.r - 1) := rfl
    rw [hSdef, hE, this, show b.r - 1 - 1 = b.r - 2 by omega]
    have := (hR.outer (b.r - 2) (by omega)).2.2 (by omega)
    unfold Bridge.cell at this; exact this
  have l1S : lat1 S b.a ∉ F := by rw [hSdef, sideB_near]; exact hR.latE.2
  have l2S : lat2 S b.a ∉ F := by
    intro h
    have e1 := (ends_lat2 (c := S) (s := b.a)).conn h
    have e2 := (ends_back (c := S) (s := b.a)).conn bkS
    have e3 := (ends_front (c := S) (s := b.a)).conn frS
    rw [hSdef, sideB_back1] at e2; rw [hSdef, sideB_front1] at e3
    exact c2 (e2.trans (e1.trans e3.symm))
  have altS := alt_of_bf bkS frS l1S l2S
  have isCutCell : CutSq F S := cutSq_of_corners (isCorner_back1 S b.a) (isCorner_front1 S b.a)
    (by rw [hSdef, sideB_back1, sideB_front1]; exact c2)
  refine ⟨altS, isCutCell, ?_⟩
  rintro ⟨b', hb', hSb'⟩
  obtain ⟨hR', two', ev', cells'⟩ := hinvF.reg b' hb'
  obtain ⟨j, hjm, hj, hbj⟩ := mem_drop_index hb'
  have hframe := pair_frame hR' two' l1S l2S hSb'
  -- `S` is not a square of `b`.
  have hji : j ≠ i := by
    intro h
    subst h
    have hbb : b' = b := hbj.symm
    rw [hbb] at hSb'
    have hE : b.E = cellJ b.q b.a (b.r - 1) := rfl
    rcases hSb' with h | h
    · exact side_ne_col b.q b.a (Or.inr rfl) (b.r - 1) (b.r - 2) (by rw [← hE]; exact h)
    · exact side_ne_col b.q b.a (Or.inr rfl) (b.r - 1) (b.r - 1) (by rw [← hE]; exact h)
  have hsep := (pinv_reach (t0 := t0) (u0 := u0) hVW hdc h0 hout0 hr).sep
  have Eb_side : b.E = nb S (latA b.a) := by
    rw [hSdef, latA_eq_opp, nb_nb_opp]
  have hEb' : b'.E = nb (b'.cell (b'.r - 2)) b'.a := by
    unfold Bridge.E Bridge.cell; rw [nb_cellJ, show b'.r - 2 + 1 = b'.r - 1 by omega]
  rcases Nat.lt_or_gt_of_ne hji with hlt | hgt
  · -- `b'` is newer than `b`
    have hz : NotZ (BS[j]'hj) (BS[i]'hi) := List.pairwise_iff_getElem.1 hsep j i hj hi hlt
    rw [hbj] at hz
    obtain ⟨_, _, hside⟩ := hz
    rcases hSb' with hA | hE'
    · rcases hframe with ha' | ha'
      · -- `E'` beyond `S`: a length-2 bridge started at `S`
        have hE'S : b'.E = nb S b.a := by rw [hEb', ← hA, ha']
        by_cases r4 : 4 ≤ b'.r
        · obtain ⟨_, _, hRj, htwoj, _⟩ := frozen_at hVW hdc h0 hout0 hr (m := j + 1) (by omega) hi
          have hrow := rowAt_at hVW hdc h0 hout0 hr hj
          rw [hbj] at hrow
          have hun := hrow.uncut (b'.r - 2) (by omega) (by omega)
          have hA' : cellJ b'.q b'.a (b'.r - 2) = S := hA.symm
          rw [hA'] at hun
          obtain ⟨_, c2'⟩ := cutE_both hRj htwoj
          exact hun (cutSq_of_corners (isCorner_back1 S b.a) (isCorner_front1 S b.a)
            (by rw [hSdef, sideB_back1, sideB_front1]; exact c2'))
        · have hr2 : b'.r = 2 := by omega
          have hq : b'.q = S := by
            have := hA.symm; unfold Bridge.cell at this; rw [hr2, Nat.sub_self, cellJ_zero] at this
            exact this
          have hrow := rowAt_at hVW hdc h0 hout0 hr hj
          rw [hbj] at hrow
          rw [hq, ha'] at hrow
          have hR2 := isEqv_conn (seqH H0 (BS.drop (j + 1)))
          have hmS : Matched (Conn (seqH H0 (BS.drop (j + 1)))) (back1 S b.a) (front1 S b.a)
              (back1 b.E b.a) (front1 b.E b.a) := by
            have hu : Ends (lat1 S b.a) (back2 b.E b.a) (front2 b.E b.a) := by
              have := ends_lat1 S b.a; rwa [hSdef, sideB_back1, sideB_front1] at this
            have m1 := lat_matched hrow.crit.1 hrow.crit.2.1 (Or.inl rfl) hu
            obtain ⟨_, _, hRj, htwoj, _⟩ := frozen_at hVW hdc h0 hout0 hr (m := j + 1) (by omega) hi
            have bEj : back b.E b.a ∈ seqH H0 (BS.drop (j + 1)) := by
              have := hRj.frA
              unfold Bridge.E Bridge.cell at *
              rw [show b.r - 1 = b.r - 2 + 1 by omega, back_cellJ_succ]; exact this
            have m2 : Matched (Conn (seqH H0 (BS.drop (j + 1)))) (back2 b.E b.a) (front2 b.E b.a)
                (back1 b.E b.a) (front1 b.E b.a) :=
              Or.inl ⟨((ends_back (c := b.E) (s := b.a)).conn bEj).symm,
                ((ends_front (c := b.E) (s := b.a)).conn hRj.frE).symm⟩
            exact Matched.trans hR2 m1 m2
          have hn1 := sameNodeI' hVW hdc h0 hout0 hr hi (m := j + 1) (by omega) hmS
          set X := nb b.E b.a with hXdef
          have hlatX : lat2 X b.a = lat1 b'.E b.a := by
            rw [hE'S, hSdef, ← beyond_sideB, sideB_near]
          have bE' : back b'.E b'.a ∈ F := by
            have := hR'.frA
            unfold Bridge.E Bridge.cell at *
            rw [show b'.r - 1 = b'.r - 2 + 1 by omega, back_cellJ_succ]; exact this
          have hmE' : Matched (Conn F) (back1 b'.E b.a) (front1 b'.E b.a) (back1 b'.E b'.a)
              (front1 b'.E b'.a) := by
            rw [ha']; exact Or.inl ⟨Conn.refl _ _, Conn.refl _ _⟩
          have hEX : Ends (lat2 X b.a) (back1 b'.E b.a) (front1 b'.E b.a) := by
            rw [hlatX]; exact ends_lat1 _ _
          rcases hkind with ⟨j', hj'm, hpend, hb1, hf1⟩ | hunc
          · have hmX := Matched.trans (isEqv_conn F)
              (lat_matched hb1 hf1 (Or.inr rfl) hEX) hmE'
            have hmX' : Matched (Conn F) (back1 X b.a) (front1 X b.a)
                (back1 (BS[j]'hj).E (BS[j]'hj).a) (front1 (BS[j]'hj).E (BS[j]'hj).a) := by
              rw [hbj]; exact hmX
            have hnj0 := sameNodeI' hVW hdc h0 hout0 hr hj hjm hmX'
            have hnj : nodeI H0 BS (pendAt H BS uv j').1 (pendAt H BS uv j').2 = j := by
              rw [hpend]; exact hnj0
            have hlowj : lowAt H BS uv j = true := by
              by_contra hl
              have := (node_pend hVW hdc h0 hout0 hr hn (j - j') j' j rfl (by omega) hj).1
                (by simpa using hl)
              exact this hnj
            obtain ⟨_, _, _, f4⟩ := pend_facts hVW hdc h0 hout0 hr hn (k := j) hj
            have hp1 := f4 (by omega)
            rw [ite_eq_left hlowj] at hp1
            have hne := (node_pend hVW hdc h0 hout0 hr hn (i - (j + 1)) (j + 1) i rfl (by omega)
              hi).1 hlow
            rw [hp1] at hne
            apply hne
            simp only [rowStartPair]
            rw [hbj, hq, ha']
            exact hn1
          · have hc := conn_of_uncut hunc (isCorner_back2 X b.a) (isCorner_front2 X b.a)
            have hm1 := Matched.of_ends (isEqv_conn F) (ends_lat2 X b.a) hEX
            have hc2 : Conn F (back1 b'.E b.a) (front1 b'.E b.a) := by
              rcases hm1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
              · exact (h1.symm.trans hc).trans h2
              · exact (h2.symm.trans hc.symm).trans h1
            obtain ⟨c1', _⟩ := cutE_both hR' two'
            apply c1'
            rcases hmE' with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · exact (h1.symm.trans hc2).trans h2
            · exact (h2.symm.trans hc2.symm).trans h1
      · -- `E'` before `S`: a side cell of `b` at `r - 2`
        apply (hside (b.r - 2) (by show b.r - 2 + 1 ≤ b.r; omega)).2
        rw [hEb', ← hA, ha', hSdef, side_comm _ _ (latAB_opp (Or.inr rfl))]
        unfold Bridge.E Bridge.cell
        rw [show b.r - 1 = b.r - 2 + 1 by omega, nb_cellJ_opp]
    · exact (hside (b.r - 1) (by show b.r - 1 + 1 ≤ b.r; omega)).2 (by rw [← hE', hSdef]; rfl)
  · -- `b` is newer than `b'`: `E_b` beside `S` is a side cell of `b'`
    have hz : NotZ (BS[i]'hi) b' := by
      have := List.pairwise_iff_getElem.1 hsep i j hi hj hgt; rwa [hbj] at this
    obtain ⟨_, _, hside⟩ := hz
    have hl : latA b.a = latA b'.a := by
      rcases hframe with h | h <;> rw [h]; exact (latA_opp b.a).symm
    rcases hSb' with hA | hE'
    · exact (hside (b'.r - 2) (by have := two'; omega)).1 (by rw [← hA, ← hl]; exact Eb_side)
    · exact (hside (b'.r - 1) (by have := two'; omega)).1 (by
        have : b'.cell (b'.r - 1) = b'.E := rfl
        rw [this, ← hE', ← hl]; exact Eb_side)

-- **A2′, side `latB`.** The side cell of `E_i` on the `latB` side is not a cell.
--
theorem a2p_sideB {BS : List Bridge} {H : Finset Edge} (hr : Reach V H0 H BS) {uv : Pt × Pt}
    (hn : ¬ Conn H uv.1 uv.2) {i : ℕ} (hi : i < BS.length) (hlow : lowAt H BS uv i = false)
    {m : ℕ} (hm : m ≤ i) (hmerge : MergeOK V (seqH H0 (BS.drop m)) (BS.drop m))
    (hXl2 : lat2 (nb (BS[i]'hi).E (BS[i]'hi).a) (BS[i]'hi).a ∉ seqH H0 (BS.drop m))
    (hkind : (∃ j', j' ≤ m ∧ pendAt H BS uv j' = (back1 (nb (BS[i]'hi).E (BS[i]'hi).a) (BS[i]'hi).a,
        front1 (nb (BS[i]'hi).E (BS[i]'hi).a) (BS[i]'hi).a) ∧
        Conn (seqH H0 (BS.drop m)) (back1 (nb (BS[i]'hi).E (BS[i]'hi).a) (BS[i]'hi).a)
          (back2 (nb (BS[i]'hi).E (BS[i]'hi).a) (BS[i]'hi).a) ∧
        Conn (seqH H0 (BS.drop m)) (front1 (nb (BS[i]'hi).E (BS[i]'hi).a) (BS[i]'hi).a)
          (front2 (nb (BS[i]'hi).E (BS[i]'hi).a) (BS[i]'hi).a)) ∨
      ¬ CutSq (seqH H0 (BS.drop m)) (nb (BS[i]'hi).E (BS[i]'hi).a))
    (hS : IsCell V (nb (BS[i]'hi).E (latB (BS[i]'hi).a))) : False := by
  obtain ⟨altS, isCutCell, hnp⟩ := sideB_merging hVW hdc h0 hout0 hr hn hi hlow hm hXl2 hkind
  exact hnp (hmerge _ hS altS isCutCell)

-- **A2′.** The square beyond `E_i`, with light laterals, is neither the start of a chain operation
-- nor an uncut square of one.
--
theorem a2p (hfar : Far t0 u0) {BS : List Bridge} {H : Finset Edge} (hr : Reach V H0 H BS) {uv : Pt × Pt}
    (hn : ¬ Conn H uv.1 uv.2) {i : ℕ} (hi : i < BS.length) (hlow : lowAt H BS uv i = false)
    {m : ℕ} (hm : m ≤ i) (hmerge : MergeOK V (seqH H0 (BS.drop m)) (BS.drop m))
    (hXl1 : lat1 (nb (BS[i]'hi).E (BS[i]'hi).a) (BS[i]'hi).a ∉ seqH H0 (BS.drop m))
    (hXl2 : lat2 (nb (BS[i]'hi).E (BS[i]'hi).a) (BS[i]'hi).a ∉ seqH H0 (BS.drop m))
    (hkind : (∃ j', j' ≤ m ∧ pendAt H BS uv j' = (back1 (nb (BS[i]'hi).E (BS[i]'hi).a) (BS[i]'hi).a,
        front1 (nb (BS[i]'hi).E (BS[i]'hi).a) (BS[i]'hi).a) ∧
        Conn (seqH H0 (BS.drop m)) (back1 (nb (BS[i]'hi).E (BS[i]'hi).a) (BS[i]'hi).a)
          (back2 (nb (BS[i]'hi).E (BS[i]'hi).a) (BS[i]'hi).a) ∧
        Conn (seqH H0 (BS.drop m)) (front1 (nb (BS[i]'hi).E (BS[i]'hi).a) (BS[i]'hi).a)
          (front2 (nb (BS[i]'hi).E (BS[i]'hi).a) (BS[i]'hi).a)) ∨
      ¬ CutSq (seqH H0 (BS.drop m)) (nb (BS[i]'hi).E (BS[i]'hi).a)) : False := by
  by_cases hA : IsCell V (nb (BS[i]'hi).E (latA (BS[i]'hi).a))
  · exact a2p_sideA hVW hdc h0 hout0 hr hn hi hlow hm hmerge hXl1 hkind hA
  by_cases hB : IsCell V (nb (BS[i]'hi).E (latB (BS[i]'hi).a))
  · exact a2p_sideB hVW hdc h0 hout0 hr hn hi hlow hm hmerge hXl2 hkind hB
  -- Neither side cell is a cell: `t0` would be on both sides of `E`.
  --
  obtain ⟨hrm, hmemb, hR, htwo, _⟩ := frozen_at hVW hdc h0 hout0 hr hm hi
  set F := seqH H0 (BS.drop m) with hF
  set b := BS[i]'hi with hb
  have hinvF := pinv_reach (t0 := t0) (u0 := u0) hVW hdc h0 hout0 hrm
  have hdegcF := degc_of hVW hdc hinvF.fac
  have hEcell : IsCell V b.E := (hinvF.reg b hmemb).2.2.2 _ (by omega)
  have oA : outer1 b.E b.a ∈ F := by
    have dF1 := hdegcF _ hEcell (front1 b.E b.a) (isCorner_front1 _ _)
    rw [deg_front1, ind_of_not_mem hR.latE.1, ind_of_mem hR.frE, ind_of_not_mem hXl1] at dF1
    by_contra h; rw [ind_of_not_mem h] at dF1; omega
  have oB : outer2 b.E b.a ∈ F := by
    have dF2 := hdegcF _ hEcell (front2 b.E b.a) (isCorner_front2 _ _)
    rw [deg_front2, ind_of_not_mem hR.latE.2, ind_of_mem hR.frE, ind_of_not_mem hXl2] at dF2
    by_contra h; rw [ind_of_not_mem h] at dF2; omega
  have hE : b.E = cellJ b.q b.a (b.r - 1) := rfl
  have bkA : back (nb b.E (latA b.a)) b.a ∈ F := by
    unfold back
    rw [hE, side_backA b.q b.a (by omega), show b.r - 1 - 1 = b.r - 2 by omega]
    have := (hR.outer (b.r - 2) (by omega)).1.2 (by omega)
    unfold Bridge.cell at this; exact this
  have bkB : back (nb b.E (latB b.a)) b.a ∈ F := by
    unfold back
    rw [hE, side_backB b.q b.a (by omega), show b.r - 1 - 1 = b.r - 2 by omega]
    have := (hR.outer (b.r - 2) (by omega)).2.2 (by omega)
    unfold Bridge.cell at this; exact this
  have EV := isCell_corners hEcell b.a
  have hout := hinvF.out
  -- An out-vertex on the `latA` side and one on the `latB` side.
  have tA : ∃ w, (w = t0 ∨ w = u0) ∧ (w = front1 b.E b.a ∨ w = back1 b.E b.a) := by
    by_contra hne; push Not at hne
    apply hA
    apply isCell_of_corners (a := b.a)
    · by_contra hx
      have e := ends_back (c := nb b.E (latA b.a)) (s := b.a)
      rw [sideA_back2] at e
      rcases out_end hout e bkA hx with h | h
      · exact (hne _ (Or.inl rfl)).2 h.symm
      · exact (hne _ (Or.inr rfl)).2 h.symm
    · rw [sideA_back2]; exact EV.1
    · by_contra hx
      have e := ends_front (c := nb b.E (latA b.a)) (s := b.a)
      rw [side_front, sideA_front2] at e
      rcases out_end hout e oA hx with h | h
      · exact (hne _ (Or.inl rfl)).1 h.symm
      · exact (hne _ (Or.inr rfl)).1 h.symm
    · rw [sideA_front2]; exact EV.2.2.1
  have tB : ∃ w, (w = t0 ∨ w = u0) ∧ (w = front2 b.E b.a ∨ w = back2 b.E b.a) := by
    by_contra hne; push Not at hne
    apply hB
    apply isCell_of_corners (a := b.a)
    · rw [sideB_back1]; exact EV.2.1
    · by_contra hx
      have e := ends_swap (ends_back (c := nb b.E (latB b.a)) (s := b.a))
      rw [sideB_back1] at e
      rcases out_end hout e bkB hx with h | h
      · exact (hne _ (Or.inl rfl)).2 h.symm
      · exact (hne _ (Or.inr rfl)).2 h.symm
    · rw [sideB_front1]; exact EV.2.2.2
    · by_contra hx
      have e := ends_swap (ends_front (c := nb b.E (latB b.a)) (s := b.a))
      rw [sideB_front, sideB_front1] at e
      rcases out_end hout e oB hx with h | h
      · exact (hne _ (Or.inl rfl)).1 h.symm
      · exact (hne _ (Or.inr rfl)).1 h.symm
  exact two_sides hfar tA tB

-- **Case A2.** No square of an earlier chain operation lies beyond `E_i` (across its dark front)
-- with that front toggled.
--
theorem caseA2 (hfar : Far t0 u0) {BS : List Bridge} {H : Finset Edge} (hr : Reach V H0 H BS)
    {uv : Pt × Pt}
    (hn : ¬ Conn H uv.1 uv.2) {i : ℕ} (hi : i < BS.length) (hlow : lowAt H BS uv i = false)
    {m j' : ℕ} (hm : m ≤ i) (hj' : j' ≤ m) (hmerge : MergeOK V (seqH H0 (BS.drop m)) (BS.drop m))
    {q : Pt} {a : Side} {n : ℕ} (hrow : RowAt V (seqH H0 (BS.drop m)) (BS.drop m) q a n)
    (hpair : pendAt H BS uv j' = (back1 q a, front1 q a)) {nO : ℕ} (hnO : nO ≤ n)
    (hlast : nO = n →
      (lat1 (cellJ q a (n - 1)) a ∉ seqH H0 (BS.drop m) ∧
        lat2 (cellJ q a (n - 1)) a ∉ seqH H0 (BS.drop m)) ∨
      (n % 2 = 0 ∧ lat1 (cellJ q a (n - 1)) a ∈ seqH H0 (BS.drop m) ∧
        lat2 (cellJ q a (n - 1)) a ∈ seqH H0 (BS.drop m) ∧
        front (cellJ q a (n - 1)) a ∉ seqH H0 (BS.drop m)))
    {j : ℕ} (hj : j < nO) (hX : cellJ q a j = nb (BS[i]'hi).E (BS[i]'hi).a)
    (hrole : sideEdge (BS[i]'hi).E (BS[i]'hi).a = lat1 (cellJ q a j) a ∨
      sideEdge (BS[i]'hi).E (BS[i]'hi).a = lat2 (cellJ q a j) a ∨
      (j = 0 ∧ sideEdge (BS[i]'hi).E (BS[i]'hi).a = back q a) ∨
      (j + 1 = nO ∧ sideEdge (BS[i]'hi).E (BS[i]'hi).a = front (cellJ q a j) a)) : False := by
  obtain ⟨hrm, hmemb, hR, htwo, _⟩ := frozen_at hVW hdc h0 hout0 hr hm hi
  set F := seqH H0 (BS.drop m) with hF
  set b := BS[i]'hi with hb
  have hinvF := pinv_reach (t0 := t0) (u0 := u0) hVW hdc h0 hout0 hrm
  have hdegcF := degc_of hVW hdc hinvF.fac
  have two := hrow.two
  have hdark : sideEdge b.E b.a ∈ F := hR.frE
  have heX : sideEdge b.E b.a = sideEdge (cellJ q a j) b.a.opp := by rw [hX, sideEdge_nb_opp]
  have hrun := hrow.run hdegcF
  have l1q : lat1 q a ∉ F := fun h => hrow.crit.2.2.1 ((ends_lat1 (c := q) (s := a)).conn h)
  have l2q : lat2 q a ∉ F := fun h => hrow.crit.2.2.1
    (hrow.crit.1.trans (((ends_lat2 (c := q) (s := a)).conn h).trans hrow.crit.2.1.symm))
  -- The lateral of `E` toward `a.opp` (for `a ⟂ b.a`) is light.
  have Elat : ∀ s, (s = latA b.a ∨ s = latB b.a) → sideEdge b.E s ∉ F := by
    rintro s (rfl | rfl)
    · rw [← lat1_eq]; exact hR.latE.1
    · rw [← lat2_eq]; exact hR.latE.2
  -- A lateral of a row square cannot be the front of `E`.
  --
  have lateral : ∀ (e1 : sideEdge b.E b.a = lat1 (cellJ q a j) a ∨
      sideEdge b.E b.a = lat2 (cellJ q a j) a), False := by
    intro hl
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · subst h0; rw [cellJ_zero] at hl
      rcases hl with h | h <;> rw [h] at hdark
      · exact l1q hdark
      · exact l2q hdark
    -- the lateral is dark: odd index, or an even row's last square
    have hodd : (j ≤ n - 2 ∧ j % 2 = 1) ∨ (j = n - 1 ∧ nO = n ∧ n % 2 = 0) := by
      rcases (show j ≤ n - 2 ∨ j = n - 1 by omega) with hjn | hjn
      · obtain ⟨r1, r2, _⟩ := hrun j hjn
        left; refine ⟨hjn, ?_⟩
        rcases hl with h | h
        · rw [h] at hdark; exact r1.1 hdark
        · rw [h] at hdark; exact r2.1 hdark
      · have hnO : nO = n := by omega
        rcases hlast hnO with ⟨ll1, ll2⟩ | ⟨hev, _, _, _⟩
        · exfalso; subst hjn
          rcases hl with h | h <;> rw [h] at hdark
          · exact ll1 hdark
          · exact ll2 hdark
        · exact Or.inr ⟨hjn, hnO, hev⟩
    have hprev : ((j - 1) % 2 = 0) ∧ j - 1 ≤ n - 2 := by omega
    obtain ⟨p1, p2, pf⟩ := hrun (j - 1) hprev.2
    have hc := hrow.cells (j - 1) (by omega)
    rcases hl with h | h
    · have hA : latA a = b.a.opp := by rw [lat1_eq, heX] at h; exact (sideEdge_inj h).symm
      rw [h] at hdark
      apply ext1 hpos (hdegcF _ hc _ (isCorner_front1 _ _))
        (fun h' => by have := p1.1 h'; omega) (fun h' => by have := pf.1 h'; omega) hdark
      rw [hA, hX, nb_nb_opp]
      exact Elat _ (perpA_opp hA)
    · have hB : latB a = b.a.opp := by rw [lat2_eq, heX] at h; exact (sideEdge_inj h).symm
      rw [h] at hdark
      apply ext2 hpos (hdegcF _ hc _ (isCorner_front2 _ _))
        (fun h' => by have := p2.1 h'; omega) (fun h' => by have := pf.1 h'; omega) hdark
      rw [hB, hX, nb_nb_opp]
      exact Elat _ (perpB_opp hB)
  rcases hrole with h | h | ⟨hj0, h⟩ | ⟨hjl, h⟩
  · exact lateral (Or.inl h)
  · exact lateral (Or.inr h)
  · -- the start's back: the row runs in direction `b.a` from beyond `E`
    subst hj0
    rw [cellJ_zero] at hX heX
    have ha : a = b.a := by
      have : sideEdge q a.opp = sideEdge q b.a.opp := by unfold back at h; rw [← h, heX]
      exact opp_inj (sideEdge_inj this)
    subst ha
    have hXq : nb b.E b.a = q := hX.symm
    exact a2p hVW hdc h0 hout0 hfar hr hn hi hlow hm hmerge (by rw [hXq]; exact l1q)
      (by rw [hXq]; exact l2q) (Or.inl ⟨j', hj', by rw [hXq]; exact hpair,
        by rw [hXq]; exact hrow.crit.1, by rw [hXq]; exact hrow.crit.2.1⟩)
  · -- the front of the last square
    have ha : a = b.a.opp := by
      have : sideEdge (cellJ q a j) a = sideEdge (cellJ q a j) b.a.opp := by
        unfold front at h; rw [← h, heX]
      exact sideEdge_inj this
    rcases (show nO < n ∨ nO = n by omega) with hlt | heq
    · -- the next row square is `E`, cut
      have hnext : cellJ q a (j + 1) = b.E := by
        rw [← nb_cellJ, hX, ha, nb_nb_opp]
      exact hrow.uncut (j + 1) (by omega) (by omega) (hnext ▸ cutSq_E hR)
    · rcases hlast heq with ⟨ll1, ll2⟩ | ⟨_, _, _, lf⟩
      · have hj1 : j = n - 1 := by omega
        subst hj1
        have e : b.a = a.opp := by rw [ha, opp_opp]
        have hl1 : lat1 (nb b.E b.a) b.a ∉ F := by
          rw [← hX, e, lat1_sopp]; exact ll1
        have hl2 : lat2 (nb b.E b.a) b.a ∉ F := by
          rw [← hX, e, lat2_sopp]; exact ll2
        refine a2p hVW hdc h0 hout0 hfar hr hn hi hlow hm hmerge hl1 hl2 (Or.inr ?_)
        rw [← hX]; exact hrow.uncut (n - 1) (by omega) (by omega)
      · have hj1 : j = n - 1 := by omega
        subst hj1
        rw [← h] at lf; exact lf hdark

end a2p

end HP

end SolidGridHam
