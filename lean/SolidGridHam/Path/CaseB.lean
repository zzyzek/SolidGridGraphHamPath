/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import SolidGridHam.Path.CaseA2

@[expose] public section

/-!
# Lemma 4, case B (docs/S4_UNDO.md §II.4): the later operation lowers bridge `i`

* B2: a square of an earlier chain row beside `q_i` (across `q_i`'s light lateral) is cut, so it
  is the row's start; its pair is matched with `q_i`'s start pair, which is apart before `i`, so its
  node is older than `i`; but a chain pair pending at or before a lowered `i` has node at most `i`.
-/

namespace SolidGridHam

namespace HP

open Finset Classical

-- The uncut cells of a row join its start's front corner to the back corner of each later cell.
--
lemma row_chain {V : Finset Pt} {F : Finset Edge} {BS : List Bridge} {q : Pt} {a : Side} {n : ℕ}
    (hrow : RowAt V F BS q a n) : ∀ j, 1 ≤ j → j < n →
      Conn F (front1 q a) (back1 (cellJ q a j) a) ∧ Conn F (front1 q a) (front1 (cellJ q a j) a)
  | 0, h, _ => absurd h (by omega)
  | j + 1, _, hj => by
    have hb : back1 (cellJ q a (j + 1)) a = front1 (cellJ q a j) a := by
      have := back1_col (c := q) (s := a) (k := j + 1) (by omega); simpa using this
    have hun := hrow.uncut (j + 1) (by omega) hj
    have hin := conn_of_uncut hun (isCorner_back1 (cellJ q a (j + 1)) a)
      (isCorner_front1 (cellJ q a (j + 1)) a)
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · subst h0; rw [cellJ_zero] at hb
      rw [hb]; exact ⟨Conn.refl _ _, by rw [← hb]; exact hin⟩
    · obtain ⟨_, h2⟩ := row_chain hrow j hpos (by omega)
      rw [hb]; exact ⟨h2, h2.trans (by rw [← hb]; exact hin)⟩

lemma perpA_eq {a c : Side} (h : latA a = c) : a.opp = latA c ∨ a.opp = latB c := by
  cases a <;> cases c <;> simp_all [latA, latB, Side.opp]

lemma perpB_eq {a c : Side} (h : latB a = c) : a.opp = latA c ∨ a.opp = latB c := by
  cases a <;> cases c <;> simp_all [latA, latB, Side.opp]

lemma front1_before (c : Pt) (s : Side) : front1 (nb c s.opp) s = back1 c s := by
  have := back1_nb (nb c s.opp) s
  rw [show nb (nb c s.opp) s = c by
    have h := nb_nb_opp c s.opp; rwa [opp_opp] at h] at this
  exact this.symm

section caseB

variable {V W : Finset Pt} {d : Pt → ℕ} {t0 u0 : Pt} {H0 : Finset Edge}
  (hVW : V ⊆ W) (hdc : ∀ q, IsCell V q → ∀ z, IsCorner z q → d z = 2)
  (h0 : IsFactor W d H0) (hout0 : ∀ e ∈ H0, (e.p ∉ V → e.q = t0 ∨ e.q = u0) ∧ (e.q ∉ V → e.p = t0 ∨ e.p = u0))
include hVW hdc h0 hout0

-- A finer state's connections hold in a coarser one.
--
lemma conn_mono {BS : List Bridge} {H : Finset Edge} (hr : Reach V H0 H BS) {m k : ℕ}
    (hmk : m ≤ k) {x y : Pt} (h : Conn (seqH H0 (BS.drop m)) x y) :
    Conn (seqH H0 (BS.drop k)) x y := by
  have hrm : Reach V H0 (seqH H0 (BS.drop m)) (BS.drop m) := by
    have e := List.take_append_drop m BS
    have hr2 : Reach V H0 H (BS.take m ++ BS.drop m) := by rw [e]; exact hr
    exact reach_suffix hr2
  have e : List.drop (k - m) (List.drop m BS) = List.drop k BS := by
    rw [List.drop_drop, show m + (k - m) = k by omega]
  rw [← e]
  exact conn_drop hVW hdc h0 hout0 hrm (k - m) h

-- **Case B2.**
--
theorem caseB2 {BS : List Bridge} {H : Finset Edge} (hr : Reach V H0 H BS) {uv : Pt × Pt}
    (hn : ¬ Conn H uv.1 uv.2) {i : ℕ} (hi : i < BS.length) (hlow : lowAt H BS uv i = true)
    {m j' : ℕ} (hm : m ≤ i) (hj' : j' ≤ i) {q : Pt} {a : Side} {n : ℕ}
    (hrow : RowAt V (seqH H0 (BS.drop m)) (BS.drop m) q a n)
    (hpair : pendAt H BS uv j' = (back1 q a, front1 q a)) {nO : ℕ} (hnO : nO ≤ n) {j : ℕ}
    (hj : j < nO) {s' : Side} (hs' : s' = latA (BS[i]'hi).a ∨ s' = latB (BS[i]'hi).a)
    (hX : cellJ q a j = nb (BS[i]'hi).q s')
    (hrole : sideEdge (BS[i]'hi).q s' = lat1 (cellJ q a j) a ∨
      sideEdge (BS[i]'hi).q s' = lat2 (cellJ q a j) a ∨
      (j = 0 ∧ sideEdge (BS[i]'hi).q s' = back q a) ∨
      (j + 1 = nO ∧ sideEdge (BS[i]'hi).q s' = front (cellJ q a j) a)) : False := by
  obtain ⟨_, _, hR, htwo, _⟩ := frozen_at hVW hdc h0 hout0 hr hm hi
  set F := seqH H0 (BS.drop m) with hF
  set b := BS[i]'hi with hb
  -- The square beside `q_i` is cut, so it is the start.
  have hcut : CutSq F (cellJ q a j) := by
    rw [hX]
    rcases hs' with h | h <;> rw [h]
    · refine cutSq_of_corners (isCorner_back2 _ b.a) (isCorner_front2 _ b.a) ?_
      rw [sideA_back2, sideA_front2]; exact hR.cut0
    · refine cutSq_of_corners (isCorner_back1 _ b.a) (isCorner_front1 _ b.a) ?_
      rw [sideB_back1, sideB_front1]; exact hR.cut0'
  have hj0 : j = 0 := by
    by_contra hne
    exact hrow.uncut j (by omega) (by omega) hcut
  subst hj0
  rw [cellJ_zero] at hX hrole
  have hlight : sideEdge b.q s' ∉ F := by
    rcases hs' with h | h <;> rw [h]
    · rw [← lat1_eq]; exact hR.lat0.1
    · rw [← lat2_eq]; exact hR.lat0.2
  have lateral : sideEdge b.q s' = lat1 q a ∨ sideEdge b.q s' = lat2 q a → False := by
    intro hl
    have hR' := isEqv_conn F
    -- the start pair is matched, before bridge `i`, with `q_i`'s start pair
    have hrowi := rowAt_at hVW hdc h0 hout0 hr hi
    set G := seqH H0 (BS.drop (i + 1)) with hG
    have hRG := isEqv_conn G
    have up : ∀ x y, Conn F x y → Conn G x y := fun x y h =>
      conn_mono hVW hdc h0 hout0 hr (by omega) h
    have hmq : Matched (Conn G) (back1 q a) (front1 q a) (back1 b.q b.a) (front1 b.q b.a) := by
      have lift : ∀ {u v}, Matched (Conn F) (back1 q a) (front1 q a) u v →
          Matched (Conn G) (back1 q a) (front1 q a) u v := by
        intro u v hm'
        rcases hm' with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨up _ _ h1, up _ _ h2⟩
        · exact Or.inr ⟨up _ _ h1, up _ _ h2⟩
      rcases hs' with h | h
      · have he : Ends (sideEdge b.q s') (back1 b.q b.a) (front1 b.q b.a) := by
          rw [h, ← lat1_eq]; exact ends_lat1 _ _
        exact lift (lat_matched hrow.crit.1 hrow.crit.2.1 hl he)
      · have he : Ends (sideEdge b.q s') (back2 b.q b.a) (front2 b.q b.a) := by
          rw [h, ← lat2_eq]; exact ends_lat2 _ _
        have m1 := lift (lat_matched hrow.crit.1 hrow.crit.2.1 hl he)
        have m2 : Matched (Conn G) (back2 b.q b.a) (front2 b.q b.a) (back1 b.q b.a)
            (front1 b.q b.a) := Or.inl ⟨hrowi.crit.1.symm, hrowi.crit.2.1.symm⟩
        exact Matched.trans hRG m1 m2
    have hapart : ¬ Conn G (back1 q a) (front1 q a) := by
      intro hc
      apply hrowi.crit.2.2.1
      rcases hmq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact (h1.symm.trans hc).trans h2
      · exact (h2.symm.trans hc.symm).trans h1
    have hge := nodeI_ge hVW hdc h0 hout0 BS H hr (i + 1) _ _ (by omega) hapart
    have hle := (node_pend hVW hdc h0 hout0 hr hn (i - j') j' i rfl hj' hi).2 hlow
    simp only [hpair] at hle
    omega
  rcases hrole with h | h | ⟨_, h⟩ | ⟨h1, h⟩
  · exact lateral (Or.inl h)
  · exact lateral (Or.inr h)
  · rw [h] at hlight; exact hlight hrow.bk
  · have e1 : sideEdge q s'.opp = sideEdge q a := by
      rw [hX, sideEdge_nb_opp]; unfold front at h; rw [← hX]; exact h
    have ha := sideEdge_inj e1
    have hnext : cellJ q a 1 = b.q := by
      rw [show (1 : ℕ) = 0 + 1 from rfl, ← nb_cellJ, cellJ_zero, ← ha, hX, nb_nb_opp]
    exact hrow.uncut 1 le_rfl (by have := hrow.two; omega) (hnext ▸ cutSq_q hR)

-- **Subtree.** For a lowered bridge `i`, every pending pair at or before `i` has both points
-- joined to `β_i` before bridge `i`.
--
theorem subtree {BS : List Bridge} {H : Finset Edge} (hr : Reach V H0 H BS) {uv : Pt × Pt}
    (hn : ¬ Conn H uv.1 uv.2) {i : ℕ} (hi : i < BS.length) (hlow : lowAt H BS uv i = true) :
    ∀ d j', i - j' = d → j' ≤ i →
      Conn (seqH H0 (BS.drop (i + 1))) (pendAt H BS uv j').1 (back1 (BS[i]'hi).E (BS[i]'hi).a) ∧
      Conn (seqH H0 (BS.drop (i + 1))) (pendAt H BS uv j').2 (back1 (BS[i]'hi).E (BS[i]'hi).a) := by
  intro dd
  induction dd using Nat.strong_induction_on with
  | _ dd ih =>
  intro j' hd hj'
  have hj'l : j' < BS.length := by omega
  obtain ⟨f1, f2, _, f4⟩ := pend_facts hVW hdc h0 hout0 hr hn hj'l
  set w := pendAt H BS uv j' with hw
  obtain ⟨hrk, hrs, he⟩ := reach_at hVW hdc h0 hout0 hr hj'l
  have hinv := pinv_reach (t0 := t0) (u0 := u0) hVW hdc h0 hout0 hrk
  have rel := step_rel hrs (degc_of hVW hdc hinv.fac)
  rw [← he] at rel
  by_cases hl : lowAt H BS uv j' = true
  · -- `w` is matched with `(β, φ)` of bridge `j'`, and joined to `β` before it
    have hc := f1.1 hl
    rw [rel] at hc
    have hbf : Conn (seqH H0 (BS.drop (j' + 1))) (back1 (BS[j']'hj'l).E (BS[j']'hj'l).a)
        (front1 (BS[j']'hj'l).E (BS[j']'hj'l).a) := (rel _ _).2 (merge_self (isEqv_conn _) _ _)
    have sub : ∀ x y, Conn (seqH H0 (BS.drop j')) x y → Conn (seqH H0 (BS.drop (j' + 1))) x y :=
      fun x y h => (rel x y).2 (Or.inl h)
    have hβ : Conn (seqH H0 (BS.drop (j' + 1))) w.1 (back1 (BS[j']'hj'l).E (BS[j']'hj'l).a) ∧
        Conn (seqH H0 (BS.drop (j' + 1))) w.2 (back1 (BS[j']'hj'l).E (BS[j']'hj'l).a) := by
      rcases hc with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact absurd h f2
      · exact ⟨sub _ _ h1, (sub _ _ h2).symm.trans hbf.symm⟩
      · exact ⟨(sub _ _ h1).trans hbf.symm, (sub _ _ h2).symm⟩
    rcases Nat.eq_or_lt_of_le hj' with heq | hlt
    · subst heq; exact hβ
    · -- through the start pair of bridge `j'`, which is pending next
      have hrow := rowAt_at hVW hdc h0 hout0 hr hj'l
      have hint := (row_chain hrow ((BS[j']'hj'l).r - 1) (by have := hrow.two; omega)
        (by have := hrow.two; omega)).1
      have hE : back1 (BS[j']'hj'l).E (BS[j']'hj'l).a =
          back1 (cellJ (BS[j']'hj'l).q (BS[j']'hj'l).a ((BS[j']'hj'l).r - 1)) (BS[j']'hj'l).a := rfl
      rw [← hE] at hint
      have hp1 := f4 (by omega)
      rw [ite_eq_left hl] at hp1
      obtain ⟨n1, n2⟩ := ih (i - (j' + 1)) (by omega) (j' + 1) rfl (by omega)
      rw [hp1] at n1 n2
      simp only [rowStartPair] at n1 n2
      have up : ∀ x y, Conn (seqH H0 (BS.drop (j' + 1))) x y →
          Conn (seqH H0 (BS.drop (i + 1))) x y := fun x y h =>
        conn_mono hVW hdc h0 hout0 hr (by omega) h
      exact ⟨(up _ _ (hβ.1.trans hint.symm)).trans n2, (up _ _ (hβ.2.trans hint.symm)).trans n2⟩
  · rcases Nat.eq_or_lt_of_le hj' with heq | hlt
    · subst heq; exact absurd hlow hl
    · have hj1 : pendAt H BS uv (j' + 1) = w := by
        rw [f4 (by omega)]; simp [hl]
      have := ih (i - (j' + 1)) (by omega) (j' + 1) rfl (by omega)
      rw [hj1] at this; exact this

-- **Case B4.**
--
theorem caseB4 {BS : List Bridge} {H : Finset Edge} (hr : Reach V H0 H BS) {uv : Pt × Pt}
    (hn : ¬ Conn H uv.1 uv.2) {i : ℕ} (hi : i < BS.length) (hlow : lowAt H BS uv i = true)
    {m j' : ℕ} (hm : m ≤ i) (hj' : j' ≤ i) {q : Pt} {a : Side} {n : ℕ}
    (hrow : RowAt V (seqH H0 (BS.drop m)) (BS.drop m) q a n)
    (hpair : pendAt H BS uv j' = (back1 q a, front1 q a)) {nO : ℕ} (hnO : nO ≤ n)
    (hlast : nO = n →
      (lat1 (cellJ q a (n - 1)) a ∉ seqH H0 (BS.drop m) ∧
        lat2 (cellJ q a (n - 1)) a ∉ seqH H0 (BS.drop m)) ∨
      (n % 2 = 0 ∧ lat1 (cellJ q a (n - 1)) a ∈ seqH H0 (BS.drop m) ∧
        lat2 (cellJ q a (n - 1)) a ∈ seqH H0 (BS.drop m) ∧
        front (cellJ q a (n - 1)) a ∉ seqH H0 (BS.drop m)))
    {j : ℕ} (hj : j < nO) (hX : cellJ q a j = nb (BS[i]'hi).q (BS[i]'hi).a.opp)
    (hrole : sideEdge (BS[i]'hi).q (BS[i]'hi).a.opp = lat1 (cellJ q a j) a ∨
      sideEdge (BS[i]'hi).q (BS[i]'hi).a.opp = lat2 (cellJ q a j) a ∨
      (j = 0 ∧ sideEdge (BS[i]'hi).q (BS[i]'hi).a.opp = back q a) ∨
      (j + 1 = nO ∧ sideEdge (BS[i]'hi).q (BS[i]'hi).a.opp = front (cellJ q a j) a)) :
    False := by
  obtain ⟨hrm, _, hR, htwo, _⟩ := frozen_at hVW hdc h0 hout0 hr hm hi
  set F := seqH H0 (BS.drop m) with hF
  set b := BS[i]'hi with hb
  have hinvF := pinv_reach (t0 := t0) (u0 := u0) hVW hdc h0 hout0 hrm
  have hdegcF := degc_of hVW hdc hinvF.fac
  have two := hrow.two
  have hdark : sideEdge b.q b.a.opp ∈ F := hR.bk
  have heX : sideEdge b.q b.a.opp = sideEdge (cellJ q a j) b.a := by
    rw [hX]; have := sideEdge_nb_opp b.q b.a.opp; rw [opp_opp] at this; exact this.symm
  have hXq : nb (cellJ q a j) b.a = b.q := by
    rw [hX]; have := nb_nb_opp b.q b.a.opp; rwa [opp_opp] at this
  have hrun := hrow.run hdegcF
  have l1q : lat1 q a ∉ F := fun h => hrow.crit.2.2.1 ((ends_lat1 (c := q) (s := a)).conn h)
  have l2q : lat2 q a ∉ F := fun h => hrow.crit.2.2.1
    (hrow.crit.1.trans (((ends_lat2 (c := q) (s := a)).conn h).trans hrow.crit.2.1.symm))
  have qlat : ∀ s, (s = latA b.a ∨ s = latB b.a) → sideEdge b.q s ∉ F := by
    rintro s (rfl | rfl)
    · rw [← lat1_eq]; exact hR.lat0.1
    · rw [← lat2_eq]; exact hR.lat0.2
  -- the contradiction through `q_i`'s critical start: its back corner joined to its front corner
  have hrowi := rowAt_at hVW hdc h0 hout0 hr hi
  set G := seqH H0 (BS.drop (i + 1)) with hG
  have hβ : Conn G (front1 b.q b.a) (back1 b.E b.a) :=
    (row_chain hrowi (b.r - 1) (by show 1 ≤ b.r - 1; omega) (by show b.r - 1 < b.r; omega)).1
  have hsub := subtree hVW hdc h0 hout0 hr hn hi hlow (i - j') j' rfl hj'
  rw [hpair] at hsub
  have up : ∀ x y, Conn F x y → Conn G x y := fun x y h =>
    conn_mono hVW hdc h0 hout0 hr (by omega) h
  have viaβ : ∀ z, Conn G z (back1 b.E b.a) → Conn G (back1 b.q b.a) z → False := by
    intro z hz hbz
    exact hrowi.crit.2.2.1 ((hbz.trans hz).trans hβ.symm)
  have lateral : ∀ (e1 : sideEdge b.q b.a.opp = lat1 (cellJ q a j) a ∨
      sideEdge b.q b.a.opp = lat2 (cellJ q a j) a), False := by
    intro hl
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · subst h0; rw [cellJ_zero] at hl
      rcases hl with h | h <;> rw [h] at hdark
      · exact l1q hdark
      · exact l2q hdark
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
    obtain ⟨p1, p2, pf⟩ := hrun (j - 1) (by omega)
    have hc := hrow.cells (j - 1) (by omega)
    rcases hl with h | h
    · have hA : latA a = b.a := by rw [lat1_eq, heX] at h; exact (sideEdge_inj h).symm
      rw [h] at hdark
      apply ext1 hpos (hdegcF _ hc _ (isCorner_front1 _ _))
        (fun h' => by have := p1.1 h'; omega) (fun h' => by have := pf.1 h'; omega) hdark
      rw [hA, hXq]
      exact qlat _ (perpA_eq hA)
    · have hB : latB a = b.a := by rw [lat2_eq, heX] at h; exact (sideEdge_inj h).symm
      rw [h] at hdark
      apply ext2 hpos (hdegcF _ hc _ (isCorner_front2 _ _))
        (fun h' => by have := p2.1 h'; omega) (fun h' => by have := pf.1 h'; omega) hdark
      rw [hB, hXq]
      exact qlat _ (perpB_eq hB)
  rcases hrole with h | h | ⟨hj0, h⟩ | ⟨hjl, h⟩
  · exact lateral (Or.inl h)
  · exact lateral (Or.inr h)
  · -- the start's back is `q_i`'s back: the row runs down from before `q_i`
    subst hj0
    rw [cellJ_zero] at hX heX
    have ha : a = b.a.opp := by
      have : sideEdge q a.opp = sideEdge q b.a := by unfold back at h; rw [← h, heX]
      have := sideEdge_inj this
      rw [← this, opp_opp]
    have hpt : back1 q a = back1 b.q b.a := by
      rw [ha, back1_sopp, hX, front1_before]
    rw [hpt] at hsub
    exact viaβ _ hsub.1 (Conn.refl _ _)
  · -- the front of the last square faces `q_i`
    have ha : a = b.a := by
      have : sideEdge (cellJ q a j) a = sideEdge (cellJ q a j) b.a := by
        unfold front at h; rw [← h, heX]
      exact sideEdge_inj this
    rcases (show nO < n ∨ nO = n by omega) with hlt | heq
    · have hnext : cellJ q a (j + 1) = b.q := by
        have e : nb (cellJ q a j) a = nb (cellJ q a j) b.a := by rw [ha]
        rw [← nb_cellJ, e, hXq]
      exact hrow.uncut (j + 1) (by omega) (by omega) (hnext ▸ cutSq_q hR)
    · rcases hlast heq with _ | ⟨_, _, _, lf⟩
      · have hj1 : j = n - 1 := by omega
        subst hj1
        have hch := (row_chain hrow (n - 1) (by omega) (by omega)).2
        have hpt : front1 (cellJ q a (n - 1)) a = back1 b.q b.a := by
          rw [hX, ha, front1_before]
        rw [hpt] at hch
        exact viaβ _ hsub.2 (up _ _ hch).symm
      · have hj1 : j = n - 1 := by omega
        subst hj1
        rw [← h] at lf; exact lf hdark

end caseB

end HP

end SolidGridHam
