/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import SolidGridHam.Path.S4Merge

@[expose] public section

/-!
# Theorem II for a merging cell (docs/S4_RESIDUAL.md §0, §4)

A merging cell `X` (alternating, cut, not a pair square) as a one-square half bridge, followed by
the undo plan of its pair. The half bridge toggles no side of a plan operation's squares, except
when `X` is the square beyond `E_i` of an undone bridge `i` (`X` not good). So for a good `X` the
plan passes `candOK`.

The cases, by the operation and the side of its square that `X` lies across:
* undo of `i` (square `E_i`): across `E_i`'s front, `X` is not good; across its back, `X` is a
  pair square; across a lateral, Lemma 1 gives `X`'s node `= i`, but `i` is undone (A1).
* lowering of `i` (square `f_t`): across front or back, `X` is a bridge square (C1), except
  behind `q_i`, where Subtree contradicts `q_i` critical (B4); across a lateral of `q_i`, `X`'s node
  is older than `i` (B2); across a lateral of an inner square, `X` is not alternating.
-/

namespace SolidGridHam

namespace HP

open Finset Classical

-- A merging cell in frame `a`: dark back and front, light laterals, pair apart.
--
structure MCell (V : Finset Pt) (H : Finset Edge) (X : Pt) (a : Side) : Prop where
  cell : IsCell V X
  bk : back X a ∈ H
  fr : front X a ∈ H
  l1 : lat1 X a ∉ H
  l2 : lat2 X a ∉ H
  apart : ¬ Conn H (back1 X a) (front1 X a)

-- Side squares beside the inner squares of a frozen bridge are not alternating.
--
lemma side_not_alt {F : Finset Edge} {b : Bridge} {ℓ : Side} {S : ℕ → Pt} {O : ℕ → Edge}
    (hsl : SideLine F b ℓ S O) {t : ℕ} (h1 : 1 ≤ t) (h2 : t + 2 ≤ b.r) : ¬ Alt F (S t) := by
  apply not_alt_of_ne (s' := b.a)
  rw [hsl.front t h2, hsl.back t h1 h2, hsl.hO t h2, hsl.hO (t - 1) (by omega)]
  intro h
  by_cases ht : t % 2 = 0
  · have := h.1 ht; omega
  · have := mt h.2 ht; omega

-- A cut alternating cell of `V` is a merging cell in its `altFrame`.
--
theorem mcell_of {V : Finset Pt} {H : Finset Edge} {X : Pt} (hX : IsCell V X) (ha : Alt H X) (hcut : CutSq H X) :
    MCell V H X (altFrame H X) := by
  obtain ⟨⟨hb, hl, hf⟩, hnc⟩ := merge_join_alt ha hcut
  obtain ⟨l1, l2⟩ := hl 0 one_pos
  have f0 := hf 0 one_pos
  rw [cellJ_zero] at l1 l2 f0
  exact ⟨hX, hb, f0.2 (by decide), fun h => by have := l1.1 h; omega,
    fun h => by have := l2.1 h; omega, hnc⟩

section mergeII

variable {V W : Finset Pt} {d : Pt → ℕ} {t0 u0 : Pt} {H0 : Finset Edge}
  (hVW : V ⊆ W) (hdc : ∀ q, IsCell V q → ∀ z, IsCorner z q → d z = 2)
  (h0 : IsFactor W d H0) (hout0 : ∀ e ∈ H0, (e.p ∉ V → e.q = t0 ∨ e.q = u0) ∧ (e.q ∉ V → e.p = t0 ∨ e.p = u0))
include hVW hdc h0 hout0

lemma pend_zero {BS : List Bridge} {H : Finset Edge} (hr : Reach V H0 H BS) {uv : Pt × Pt}
    (hn : ¬ Conn H uv.1 uv.2) (hpos : 0 < BS.length) : pendAt H BS uv 0 = uv :=
  (pend_facts hVW hdc h0 hout0 hr hn hpos).2.2.1 rfl

-- **Case A1 for a merging cell** (Lemma 1).
--
theorem caseA1m {BS : List Bridge} {H : Finset Edge} (hr : Reach V H0 H BS) {X : Pt} {a : Side}
    (hc : MCell V H X a) {i : ℕ} (hi : i < BS.length)
    (hlow : lowAt H BS (back1 X a, front1 X a) i = false)
    {s' : Side} (hs' : s' = latA (BS[i]'hi).a ∨ s' = latB (BS[i]'hi).a)
    (hrole : sideEdge (BS[i]'hi).E s' = lat1 X a ∨ sideEdge (BS[i]'hi).E s' = lat2 X a ∨
      sideEdge (BS[i]'hi).E s' = back X a ∨ sideEdge (BS[i]'hi).E s' = front X a) : False := by
  have hH := seqH_of_reach hr
  have hF : seqH H0 (BS.drop 0) = H := by rw [List.drop_zero, ← hH]
  obtain ⟨_, _, hR, htwo, _⟩ := frozen_at hVW hdc h0 hout0 hr (Nat.zero_le i) hi
  rw [hF] at hR
  set b := BS[i]'hi with hb
  have bE : back b.E b.a ∈ H := by
    have := hR.frA
    unfold Bridge.E Bridge.cell at *
    rw [show b.r - 1 = b.r - 2 + 1 by omega, back_cellJ_succ]; exact this
  have hlight : sideEdge b.E s' ∉ H := by
    rcases hs' with h | h <;> rw [h]
    · rw [← lat1_eq]; exact hR.latE.1
    · rw [← lat2_eq]; exact hR.latE.2
  have kb := (ends_back (c := X) (s := a)).conn hc.bk
  have kf := (ends_front (c := X) (s := a)).conn hc.fr
  have lateral : sideEdge b.E s' = lat1 X a ∨ sideEdge b.E s' = lat2 X a → False := by
    intro hl
    have hR' := isEqv_conn H
    have hmE : Matched (Conn H) (back1 X a) (front1 X a) (back1 b.E b.a) (front1 b.E b.a) := by
      rcases hs' with h | h
      · have he : Ends (sideEdge b.E s') (back1 b.E b.a) (front1 b.E b.a) := by
          rw [h, ← lat1_eq]; exact ends_lat1 _ _
        exact lat_matched kb kf hl he
      · have he : Ends (sideEdge b.E s') (back2 b.E b.a) (front2 b.E b.a) := by
          rw [h, ← lat2_eq]; exact ends_lat2 _ _
        have m1 := lat_matched kb kf hl he
        have m2 : Matched (Conn H) (back2 b.E b.a) (front2 b.E b.a) (back1 b.E b.a)
            (front1 b.E b.a) :=
          Or.inl ⟨((ends_back (c := b.E) (s := b.a)).conn bE).symm,
            ((ends_front (c := b.E) (s := b.a)).conn hR.frE).symm⟩
        exact Matched.trans hR' m1 m2
    rw [← hF] at hmE
    have hnode := sameNodeI' hVW hdc h0 hout0 hr hi (Nat.zero_le _) hmE
    have hne := (node_pend hVW hdc h0 hout0 hr (uv := (back1 X a, front1 X a)) hc.apart
      (i - 0) 0 i rfl (Nat.zero_le _) hi).1 hlow
    rw [pend_zero hVW hdc h0 hout0 hr (uv := (back1 X a, front1 X a)) hc.apart (by omega)] at hne
    exact hne hnode
  rcases hrole with h | h | h | h
  · exact lateral (Or.inl h)
  · exact lateral (Or.inr h)
  · rw [h] at hlight; exact hlight hc.bk
  · rw [h] at hlight; exact hlight hc.fr

-- **Case B2 for a merging cell.**
--
theorem caseB2m {BS : List Bridge} {H : Finset Edge} (hr : Reach V H0 H BS) {X : Pt} {a : Side}
    (hc : MCell V H X a) {i : ℕ} (hi : i < BS.length)
    (hlow : lowAt H BS (back1 X a, front1 X a) i = true)
    {s' : Side} (hs' : s' = latA (BS[i]'hi).a ∨ s' = latB (BS[i]'hi).a)
    (hrole : sideEdge (BS[i]'hi).q s' = lat1 X a ∨ sideEdge (BS[i]'hi).q s' = lat2 X a ∨
      sideEdge (BS[i]'hi).q s' = back X a ∨ sideEdge (BS[i]'hi).q s' = front X a) : False := by
  have hH := seqH_of_reach hr
  have hF : seqH H0 (BS.drop 0) = H := by rw [List.drop_zero, ← hH]
  obtain ⟨_, _, hR, htwo, _⟩ := frozen_at hVW hdc h0 hout0 hr (Nat.zero_le i) hi
  rw [hF] at hR
  set b := BS[i]'hi with hb
  have hlight : sideEdge b.q s' ∉ H := by
    rcases hs' with h | h <;> rw [h]
    · rw [← lat1_eq]; exact hR.lat0.1
    · rw [← lat2_eq]; exact hR.lat0.2
  have kb := (ends_back (c := X) (s := a)).conn hc.bk
  have kf := (ends_front (c := X) (s := a)).conn hc.fr
  have lateral : sideEdge b.q s' = lat1 X a ∨ sideEdge b.q s' = lat2 X a → False := by
    intro hl
    have hrowi := rowAt_at hVW hdc h0 hout0 hr hi
    set G := seqH H0 (BS.drop (i + 1)) with hG
    have hRG := isEqv_conn G
    have up : ∀ x y, Conn H x y → Conn G x y := fun x y h =>
      conn_mono hVW hdc h0 hout0 hr (Nat.zero_le (i + 1)) (by rw [hF]; exact h)
    have lift : ∀ {u v}, Matched (Conn H) (back1 X a) (front1 X a) u v →
        Matched (Conn G) (back1 X a) (front1 X a) u v := by
      intro u v hm'
      rcases hm' with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨up _ _ h1, up _ _ h2⟩
      · exact Or.inr ⟨up _ _ h1, up _ _ h2⟩
    have hmq : Matched (Conn G) (back1 X a) (front1 X a) (back1 b.q b.a) (front1 b.q b.a) := by
      rcases hs' with h | h
      · have he : Ends (sideEdge b.q s') (back1 b.q b.a) (front1 b.q b.a) := by
          rw [h, ← lat1_eq]; exact ends_lat1 _ _
        exact lift (lat_matched kb kf hl he)
      · have he : Ends (sideEdge b.q s') (back2 b.q b.a) (front2 b.q b.a) := by
          rw [h, ← lat2_eq]; exact ends_lat2 _ _
        have m1 := lift (lat_matched kb kf hl he)
        have m2 : Matched (Conn G) (back2 b.q b.a) (front2 b.q b.a) (back1 b.q b.a)
            (front1 b.q b.a) := Or.inl ⟨hrowi.crit.1.symm, hrowi.crit.2.1.symm⟩
        exact Matched.trans hRG m1 m2
    have hapart : ¬ Conn G (back1 X a) (front1 X a) := by
      intro hcn
      apply hrowi.crit.2.2.1
      rcases hmq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact (h1.symm.trans hcn).trans h2
      · exact (h2.symm.trans hcn.symm).trans h1
    have hge := nodeI_ge hVW hdc h0 hout0 BS H hr (i + 1) _ _ (by omega) hapart
    have hle := (node_pend hVW hdc h0 hout0 hr (uv := (back1 X a, front1 X a)) hc.apart
      (i - 0) 0 i rfl (Nat.zero_le _) hi).2 hlow
    rw [pend_zero hVW hdc h0 hout0 hr (uv := (back1 X a, front1 X a)) hc.apart (by omega)] at hle
    simp only at hle
    omega
  rcases hrole with h | h | h | h
  · exact lateral (Or.inl h)
  · exact lateral (Or.inr h)
  · rw [h] at hlight; exact hlight hc.bk
  · rw [h] at hlight; exact hlight hc.fr

-- **Case B4 for a merging cell.**
--
theorem caseB4m {BS : List Bridge} {H : Finset Edge} (hr : Reach V H0 H BS) {X : Pt} {a : Side}
    (hc : MCell V H X a) {i : ℕ} (hi : i < BS.length)
    (hlow : lowAt H BS (back1 X a, front1 X a) i = true)
    (hX : X = nb (BS[i]'hi).q (BS[i]'hi).a.opp)
    (hrole : sideEdge (BS[i]'hi).q (BS[i]'hi).a.opp = lat1 X a ∨
      sideEdge (BS[i]'hi).q (BS[i]'hi).a.opp = lat2 X a ∨
      sideEdge (BS[i]'hi).q (BS[i]'hi).a.opp = back X a ∨
      sideEdge (BS[i]'hi).q (BS[i]'hi).a.opp = front X a) : False := by
  have hH := seqH_of_reach hr
  have hF : seqH H0 (BS.drop 0) = H := by rw [List.drop_zero, ← hH]
  obtain ⟨_, _, hR, htwo, _⟩ := frozen_at hVW hdc h0 hout0 hr (Nat.zero_le i) hi
  rw [hF] at hR
  set b := BS[i]'hi with hb
  have hdark : sideEdge b.q b.a.opp ∈ H := hR.bk
  have heX : sideEdge b.q b.a.opp = sideEdge X b.a := by
    rw [hX]; have := sideEdge_nb_opp b.q b.a.opp; rw [opp_opp] at this; exact this.symm
  have hrowi := rowAt_at hVW hdc h0 hout0 hr hi
  set G := seqH H0 (BS.drop (i + 1)) with hG
  have hβ : Conn G (front1 b.q b.a) (back1 b.E b.a) :=
    (row_chain hrowi (b.r - 1) (by show 1 ≤ b.r - 1; omega) (by show b.r - 1 < b.r; omega)).1
  have hsub := subtree hVW hdc h0 hout0 hr (uv := (back1 X a, front1 X a)) hc.apart hi hlow
    (i - 0) 0 rfl (Nat.zero_le _)
  rw [pend_zero hVW hdc h0 hout0 hr (uv := (back1 X a, front1 X a)) hc.apart (by omega)] at hsub
  simp only at hsub
  have viaβ : ∀ z, Conn G z (back1 b.E b.a) → Conn G (back1 b.q b.a) z → False := by
    intro z hz hbz
    exact hrowi.crit.2.2.1 ((hbz.trans hz).trans hβ.symm)
  rcases hrole with h | h | h | h
  · rw [h] at hdark; exact hc.l1 hdark
  · rw [h] at hdark; exact hc.l2 hdark
  · have ha : a = b.a.opp := by
      have : sideEdge X a.opp = sideEdge X b.a := by unfold back at h; rw [← h, heX]
      have := sideEdge_inj this
      rw [← this, opp_opp]
    have hpt : back1 X a = back1 b.q b.a := by
      rw [ha, back1_sopp, hX, front1_before]
    rw [hpt] at hsub
    exact viaβ _ hsub.1 (Conn.refl _ _)
  · have ha : a = b.a := by
      have : sideEdge X a = sideEdge X b.a := by unfold front at h; rw [← h, heX]
      exact sideEdge_inj this
    have hpt : front1 X a = back1 b.q b.a := by
      rw [ha, hX, front1_before]
    rw [hpt] at hsub
    exact viaβ _ hsub.2 (Conn.refl _ _)

-- **(C2) for a merging cell** against every plan operation, when `X` is good.
--
theorem c2_merge {BS : List Bridge} {H : Finset Edge} (hr : Reach V H0 H BS) {X : Pt} {a : Side}
    (hc : MCell V H X a) (ha : Alt H X) (hnp : ¬ ∃ b ∈ BS, X = b.cell (b.r - 2) ∨ X = b.E)
    (hgood : ∀ i (hi : i < BS.length), lowAt H BS (back1 X a, front1 X a) i = false →
      X ≠ nb (BS[i]'hi).E (BS[i]'hi).a)
    {i : ℕ} (hi : i < BS.length) {t : ℕ}
    (ht : t < (opAt H BS (back1 X a, front1 X a) i hi).n) {e : Edge}
    (he : e ∈ cellE (cellJ (opAt H BS (back1 X a, front1 X a) i hi).c
      (opAt H BS (back1 X a, front1 X a) i hi).a t))
    (htog : (⟨X, a, 1⟩ : Join).tog e) : False := by
  have hH := seqH_of_reach hr
  have hF : seqH H0 (BS.drop 0) = H := by rw [List.drop_zero, ← hH]
  have hinv := pinv_reach (t0 := t0) (u0 := u0) hVW hdc h0 hout0 hr
  have hreg : ∀ b ∈ BS, RegionOK H b ∧ 2 ≤ b.r ∧ b.r % 2 = 0 :=
    fun b hb => let h := hinv.reg b hb; ⟨h.1, h.2.1, h.2.2.1⟩
  obtain ⟨hR, htwo, hev⟩ := hreg _ (List.getElem_mem hi)
  have c1 : ∀ l < (BS[i]'hi).r, X ≠ (BS[i]'hi).cell l :=
    fun l hl => c1_merge ha hnp hreg (List.getElem_mem hi) hl
  have roles : ∀ {jj : ℕ} {Y : Pt} {s' : Side}, jj < 1 →
      (sideEdge Y s' = lat1 (cellJ X a jj) a ∨ sideEdge Y s' = lat2 (cellJ X a jj) a ∨
        (jj = 0 ∧ sideEdge Y s' = back X a) ∨
        (jj + 1 = 1 ∧ sideEdge Y s' = front (cellJ X a jj) a)) →
      (sideEdge Y s' = lat1 X a ∨ sideEdge Y s' = lat2 X a ∨
        sideEdge Y s' = back X a ∨ sideEdge Y s' = front X a) := by
    intro jj Y s' hjj h
    obtain rfl : jj = 0 := by omega
    rw [cellJ_zero] at h
    rcases h with h | h | ⟨_, h⟩ | ⟨_, h⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  unfold opAt at ht he
  cases hlow : lowAt H BS (back1 X a, front1 X a) i
  · -- `U_i`: the square is `E_i`
    simp only [hlow, Bool.false_eq_true, ↓reduceIte, undoJ] at ht he
    obtain rfl : t = 0 := by omega
    rw [cellJ_zero] at he
    obtain ⟨jj, hjj, s', hes, hXs, hrole⟩ := c2_reduce htog he
      (fun jj hjj h => by
        obtain rfl : jj = 0 := by simp at hjj; omega
        rw [cellJ_zero] at h
        exact c1 ((BS[i]'hi).r - 1) (by omega) h)
    simp only at hjj hXs hrole
    rw [hes] at hrole
    have hrole' := roles hjj hrole
    obtain rfl : jj = 0 := by omega
    rw [cellJ_zero] at hXs
    rcases side_cases (BS[i]'hi).a s' with rfl | rfl | rfl | rfl
    · exact hgood i hi hlow hXs
    · apply c1 ((BS[i]'hi).r - 2) (by omega)
      rw [hXs]; unfold Bridge.E Bridge.cell
      rw [show (BS[i]'hi).r - 1 = (BS[i]'hi).r - 2 + 1 by omega, nb_cellJ_opp]
    · exact caseA1m hVW hdc h0 hout0 hr hc hi hlow (Or.inl rfl) hrole'
    · exact caseA1m hVW hdc h0 hout0 hr hc hi hlow (Or.inr rfl) hrole'
  · -- `L_i`: the square is a row square `f_t`
    simp only [hlow, ↓reduceIte, lowJ] at ht he
    obtain ⟨jj, hjj, s', hes, hXs, hrole⟩ := c2_reduce htog he
      (fun jj hjj h => by
        obtain rfl : jj = 0 := by simp at hjj; omega
        rw [cellJ_zero] at h
        exact c1 t (by omega) h)
    simp only at hjj hXs hrole
    rw [hes] at hrole
    have hrole' := roles hjj hrole
    obtain rfl : jj = 0 := by omega
    rw [cellJ_zero] at hXs
    rcases side_cases (BS[i]'hi).a s' with rfl | rfl | rfl | rfl
    · exact c1 (t + 1) (by omega) (by rw [hXs]; unfold Bridge.cell; rw [nb_cellJ])
    · rcases Nat.eq_zero_or_pos t with h0 | hpos
      · subst h0
        rw [cellJ_zero] at hXs hrole'
        exact caseB4m hVW hdc h0 hout0 hr hc hi hlow hXs hrole'
      · apply c1 (t - 1) (by omega)
        rw [hXs]; unfold Bridge.cell
        rw [show t = t - 1 + 1 by omega, nb_cellJ_opp, show t - 1 + 1 - 1 = t - 1 by omega]
    all_goals
      rcases Nat.eq_zero_or_pos t with h0 | hpos
      · subst h0
        rw [cellJ_zero] at hXs hrole'
        first
          | exact caseB2m hVW hdc h0 hout0 hr hc hi hlow (Or.inl rfl) hrole'
          | exact caseB2m hVW hdc h0 hout0 hr hc hi hlow (Or.inr rfl) hrole'
      · first
          | exact side_not_alt (sideLine_A hR htwo hev) hpos (by omega) (by unfold Bridge.cell; rw [← hXs]; exact ha)
          | exact side_not_alt (sideLine_B hR htwo hev) hpos (by omega) (by unfold Bridge.cell; rw [← hXs]; exact ha)

-- **`OpsOK` for the plan after a good merging cell.**
--
theorem opsOK_merge (hfar : Far t0 u0) {s0 p0 : Pt} (hsD : ∀ c, IsCell V c → ¬ IsCorner s0 c) (hp0 : p0 ∉ V)
    {BS : List Bridge} {H : Finset Edge} (hr : Reach V H0 H BS) {X : Pt} {a : Side}
    (hc : MCell V H X a) (ha : Alt H X) (hnp : ¬ ∃ b ∈ BS, X = b.cell (b.r - 2) ∨ X = b.E)
    (hgood : ∀ i (hi : i < BS.length), lowAt H BS (back1 X a, front1 X a) i = false →
      X ≠ nb (BS[i]'hi).E (BS[i]'hi).a) :
    OpsOK W (Join.apply H ⟨X, a, 1⟩) (plan H BS (back1 X a, front1 X a))
        (relPts ((⟨X, a, 1⟩ : Join) :: plan H BS (back1 X a, front1 X a))) s0 p0 ∧
      ∀ x, relPts ((⟨X, a, 1⟩ : Join) :: plan H BS (back1 X a, front1 X a)) x →
        ¬ IsMid X a 0 x := by
  set M : Join := ⟨X, a, 1⟩ with hM
  set uv : Pt × Pt := (back1 X a, front1 X a) with huv
  have hn : ¬ Conn H uv.1 uv.2 := hc.apart
  have hinv := pinv_reach (t0 := t0) (u0 := u0) hVW hdc h0 hout0 hr
  have reg := fun k (hk : k < BS.length) => hinv.reg _ (List.getElem_mem hk)
  have hreg : ∀ b ∈ BS, RegionOK H b ∧ 2 ≤ b.r ∧ b.r % 2 = 0 :=
    fun b hb => let h := hinv.reg b hb; ⟨h.1, h.2.1, h.2.2.1⟩
  -- (F1) the half bridge toggles no side of a plan operation
  have F1 : ∀ k (hk : k < BS.length), ∀ t < (opAt H BS uv k hk).n,
      ∀ e ∈ cellE (cellJ (opAt H BS uv k hk).c (opAt H BS uv k hk).a t), ¬ M.tog e :=
    fun k hk t ht e he htog => c2_merge hVW hdc h0 hout0 hr hc ha hnp hgood hk ht he htog
  -- (F3) the half bridge's cell avoids every bridge square
  have F3 : ∀ k (hk : k < BS.length), ∀ j < M.n, ∀ t < (opAt H BS uv k hk).n,
      cellJ M.c M.a j ≠ cellJ (opAt H BS uv k hk).c (opAt H BS uv k hk).a t := by
    intro k hk j hj t ht
    obtain ⟨l, hl, hY⟩ := opAt_cells hk (reg k hk).2.1 ht
    rw [hY]
    obtain rfl : j = 0 := by simp [M] at hj; omega
    rw [cellJ_zero]
    exact c1_merge ha hnp hreg (List.getElem_mem hk) hl
  -- (F4) cells of different plan operations are disjoint
  have F4 : ∀ k i (hk : k < BS.length) (hi : i < BS.length), k < i →
      ∀ j < (opAt H BS uv k hk).n, ∀ t < (opAt H BS uv i hi).n,
      cellJ (opAt H BS uv k hk).c (opAt H BS uv k hk).a j ≠
        cellJ (opAt H BS uv i hi).c (opAt H BS uv i hi).a t := by
    intro k i hk hi hki j hj t ht
    obtain ⟨l, hl, hY⟩ := opAt_cells hi (reg i hi).2.1 ht
    rw [hY]
    exact c1_newer hVW hdc h0 hout0 hr hki hi _ hj hl
  have corner_of : ∀ {O : Join} {x : Pt}, (x = back1 O.c O.a ∨ x = front1 O.c O.a) →
      IsCorner x O.c := by
    intro O x hx; rcases hx with rfl | rfl
    · exact isCorner_back1 _ _
    · exact isCorner_front1 _ _
  -- pair points of any operation are not interior points of another
  have nomidOp : ∀ k (hk : k < BS.length) {x : Pt},
      relPts (M :: plan H BS uv) x → ¬ IsMid (opAt H BS uv k hk).c (opAt H BS uv k hk).a
        ((opAt H BS uv k hk).n - 1) x := by
    intro k hk x hx
    obtain ⟨O', hO', hxO⟩ := hx
    by_cases hOO : O' = opAt H BS uv k hk
    · subst hOO; exact noMid_self _ hxO
    rcases List.mem_cons.1 hO' with rfl | hO'
    · exact noMid (by simp [M])
        (fun j hj j' hj' h => F3 k hk j' hj' j hj h.symm) (Or.inr (F1 k hk)) (corner_of hxO)
    · obtain ⟨i, hi, rfl⟩ := mem_plan hO'
      have hik : i ≠ k := fun h => hOO (by subst h; rfl)
      have hn1 : 1 ≤ (opAt H BS uv i hi).n := by
        unfold opAt; split_ifs <;> simp [lowJ, undoJ]; have := (reg i hi).2.1; omega
      rcases Nat.lt_or_gt_of_ne hik with hlt | hgt
      · exact noMid hn1 (fun j hj j' hj' h => F4 i k hi hk hlt j' hj' j hj h.symm)
          (Or.inr (fun j hj e he => c2_plan hVW hdc h0 hout0 hfar hr hn hlt hk hj he)) (corner_of hxO)
      · exact noMid hn1 (fun j hj j' hj' => F4 k i hk hi hgt j hj j' hj')
          (Or.inl (fun j hj e he => c2_plan hVW hdc h0 hout0 hfar hr hn hgt hi hj he)) (corner_of hxO)
  refine ⟨⟨fun o ho => ?_, ?_⟩, fun x _ ⟨j, _, hj, _⟩ => by omega⟩
  · obtain ⟨k, hk, rfl⟩ := mem_plan ho
    obtain ⟨hR, htwo, hev, cells⟩ := reg k hk
    have patH : StripPat H (opAt H BS uv k hk).c (opAt H BS uv k hk).a (opAt H BS uv k hk).n := by
      unfold opAt; split_ifs
      · exact lowJ_pat hR htwo hev
      · exact undoJ_pat hR htwo
    have hn1 : 1 ≤ (opAt H BS uv k hk).n := by
      unfold opAt; split_ifs <;> simp [lowJ, undoJ]; omega
    refine ⟨stripPat_congr hn1 (fun j hj e he => joinKeep (F1 k hk j hj e he)) patH, ?_,
      fun j hj => ?_, fun j hj => ?_, ⟨_, List.mem_cons_of_mem _ ho, Or.inl rfl⟩,
      ⟨_, List.mem_cons_of_mem _ ho, Or.inr rfl⟩, fun x hx => nomidOp k hk hx⟩
    · unfold opAt; split_ifs <;> simp [lowJ, undoJ]; omega
    · obtain ⟨l, hl, hY⟩ := opAt_cells hk htwo hj
      rw [hY]; exact isCell_mono (cells l hl) hVW
    · obtain ⟨l, hl, hY⟩ := opAt_cells hk htwo hj
      rw [hY]
      have hcl := cells l hl
      refine ⟨hsD _ hcl, fun hz => hp0 ?_⟩
      obtain ⟨x, y⟩ := (BS[k]'hk).cell l
      rcases hz with h | h | h | h <;> rw [h]
      · exact hcl.1
      · exact hcl.2.1
      · exact hcl.2.2.1
      · exact hcl.2.2.2
  · rw [List.pairwise_iff_getElem]
    intro k i hk hi hki
    rw [plan_length] at hk hi
    rw [plan_getElem H BS uv hk, plan_getElem H BS uv hi]
    intro j hj e he
    exact c2_plan hVW hdc h0 hout0 hfar hr hn hki hi hj he

-- **Theorem II for a merging cell**: a merging cell with no bad bridge is good.
--
theorem goodCell_of (hfar : Far t0 u0) {s0 p0 : Pt} (hsD : ∀ c, IsCell V c → ¬ IsCorner s0 c) (hp0 : p0 ∉ V)
    {BS : List Bridge} {H : Finset Edge} (hr : Reach V H0 H BS) {X : Pt} (hX : IsCell V X)
    (ha : Alt H X) (hcut : CutSq H X) (hnp : ¬ ∃ b ∈ BS, X = b.cell (b.r - 2) ∨ X = b.E)
    (hgood : ∀ i (hi : i < BS.length),
      lowAt H BS (back1 X (altFrame H X), front1 X (altFrame H X)) i = false →
      X ≠ nb (BS[i]'hi).E (BS[i]'hi).a) :
    GoodCell W s0 p0 H BS X :=
  ⟨ha, hcut, hnp, opsOK_merge hVW hdc h0 hout0 hfar hsD hp0 hr (mcell_of hX ha hcut) ha hnp hgood⟩

end mergeII

end HP

end SolidGridHam
