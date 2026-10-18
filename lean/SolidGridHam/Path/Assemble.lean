/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import SolidGridHam.Path.SideRun

/-!
# Lemma 4: (C2) for chain rows

`ChainRow`: a chain operation (the half bridge's row, or a lowered bridge's row) seen as a row at
state `S m` whose start pair is the pending pair at `j' ≤ m`. `c2_chain`: such an operation toggles
no side of any square of a later plan operation (cases A1, A2, B2, B3, B4).
-/

namespace SolidGridHam

namespace HP

open Finset Classical

structure ChainRow (V : Finset Pt) (H0 H : Finset Edge) (BS : List Bridge) (uv : Pt × Pt)
    (m j' : ℕ) (q : Pt) (a : Side) (n nO : ℕ) : Prop where
  hj' : j' ≤ m
  merge : MergeOK V (seqH H0 (BS.drop m)) (BS.drop m)
  row : RowAt V (seqH H0 (BS.drop m)) (BS.drop m) q a n
  pair : m < BS.length → pendAt H BS uv j' = (back1 q a, front1 q a)
  nOn : nO + 1 = n ∨ nO = n
  lastArc : outArc (seqH H0 (BS.drop m)) (cellJ q a (n - 1)) a ≠ outArc (seqH H0 (BS.drop m)) q a
  last : nO = n →
    (lat1 (cellJ q a (n - 1)) a ∉ seqH H0 (BS.drop m) ∧
      lat2 (cellJ q a (n - 1)) a ∉ seqH H0 (BS.drop m)) ∨
    (n % 2 = 0 ∧ lat1 (cellJ q a (n - 1)) a ∈ seqH H0 (BS.drop m) ∧
      lat2 (cellJ q a (n - 1)) a ∈ seqH H0 (BS.drop m) ∧
      front (cellJ q a (n - 1)) a ∉ seqH H0 (BS.drop m))
  eavoid : nO < n → ∀ i (hi : i < BS.length), m ≤ i → ∀ l < (BS[i]'hi).r,
    cellJ q a (n - 1) ≠ (BS[i]'hi).cell l
  c1 : ∀ i (hi : i < BS.length), m ≤ i → ∀ j < nO, ∀ l < (BS[i]'hi).r,
    cellJ q a j ≠ (BS[i]'hi).cell l

lemma planOp_cells {b : Bridge} (htwo : 2 ≤ b.r) (low : Bool) {t : ℕ}
    (ht : t < (if low then lowJ b else undoJ b).n) :
    ∃ l < b.r, cellJ (if low then lowJ b else undoJ b).c (if low then lowJ b else undoJ b).a t =
      b.cell l := by
  cases low
  · simp only [Bool.false_eq_true, ↓reduceIte, undoJ] at ht ⊢
    obtain rfl : t = 0 := by omega
    exact ⟨b.r - 1, by omega, by rw [cellJ_zero]; rfl⟩
  · simp only [↓reduceIte, lowJ] at ht ⊢
    exact ⟨t, by omega, rfl⟩

section assemble

variable {V W : Finset Pt} {d : Pt → ℕ} {t0 u0 : Pt} {H0 : Finset Edge}
  (hVW : V ⊆ W) (hdc : ∀ q, IsCell V q → ∀ z, IsCorner z q → d z = 2)
  (h0 : IsFactor W d H0) (hout0 : ∀ e ∈ H0, (e.p ∉ V → e.q = t0 ∨ e.q = u0) ∧ (e.q ∉ V → e.p = t0 ∨ e.p = u0))
include hVW hdc h0 hout0

-- **(C2) for a chain row against a later plan operation.**
--
theorem c2_chain (hfar : Far t0 u0) {BS : List Bridge} {H : Finset Edge} (hr : Reach V H0 H BS)
    {uv : Pt × Pt}
    (hn : ¬ Conn H uv.1 uv.2) {m j' : ℕ} {q : Pt} {a : Side} {n nO : ℕ}
    (hc : ChainRow V H0 H BS uv m j' q a n nO) {i : ℕ} (hi : i < BS.length) (hmi : m ≤ i)
    {t : ℕ} (ht : t < (if lowAt H BS uv i then lowJ (BS[i]'hi) else undoJ (BS[i]'hi)).n)
    {e : Edge} (he : e ∈ cellE (cellJ (if lowAt H BS uv i then lowJ (BS[i]'hi) else
      undoJ (BS[i]'hi)).c (if lowAt H BS uv i then lowJ (BS[i]'hi) else undoJ (BS[i]'hi)).a t))
    (htog : (⟨q, a, nO⟩ : Join).tog e) : False := by
  obtain ⟨_, _, hR, htwo, hev⟩ := frozen_at hVW hdc h0 hout0 hr hmi hi
  have hnOn : nO ≤ n := by rcases hc.nOn with h | h <;> omega
  have c1 := hc.c1 i hi hmi
  -- the last square's laterals, uniform for B3
  have hlast3 : nO = n →
      (lat1 (cellJ q a (n - 1)) a ∉ seqH H0 (BS.drop m) ∧
        lat2 (cellJ q a (n - 1)) a ∉ seqH H0 (BS.drop m)) ∨
      (lat1 (cellJ q a (n - 1)) a ∈ seqH H0 (BS.drop m) ∧
        lat2 (cellJ q a (n - 1)) a ∈ seqH H0 (BS.drop m)) := fun h => by
    rcases hc.last h with h1 | ⟨_, h2, h3, _⟩
    · exact Or.inl h1
    · exact Or.inr ⟨h2, h3⟩
  cases hlow : lowAt H BS uv i
  · -- `U_i`: the square is `E_i`
    simp only [hlow, Bool.false_eq_true, ↓reduceIte, undoJ] at ht he
    obtain rfl : t = 0 := by omega
    rw [cellJ_zero] at he
    obtain ⟨jj, hjj, s', hes, hXs, hrole⟩ := c2_reduce htog he
      (fun jj hjj h => c1 jj hjj ((BS[i]'hi).r - 1) (by omega) h)
    simp only at hjj hXs hrole
    rw [hes] at hrole
    rcases side_cases (BS[i]'hi).a s' with rfl | rfl | rfl | rfl
    · exact caseA2 hVW hdc h0 hout0 hfar hr hn hi hlow hmi hc.hj' hc.merge hc.row (hc.pair (by omega)) hnOn hc.last
        hjj hXs hrole
    · apply c1 jj hjj ((BS[i]'hi).r - 2) (by omega)
      rw [hXs]; unfold Bridge.E Bridge.cell
      rw [show (BS[i]'hi).r - 1 = (BS[i]'hi).r - 2 + 1 by omega, nb_cellJ_opp]
    · exact caseA1 hVW hdc h0 hout0 hr hn hi hlow (le_trans hmi le_rfl) (le_trans hc.hj' hmi)
        hc.row (hc.pair (by omega)) hnOn hjj (Or.inl rfl) hXs hrole
    · exact caseA1 hVW hdc h0 hout0 hr hn hi hlow (le_trans hmi le_rfl) (le_trans hc.hj' hmi)
        hc.row (hc.pair (by omega)) hnOn hjj (Or.inr rfl) hXs hrole
  · -- `L_i`: the square is a row square `f_t`
    simp only [hlow, ↓reduceIte, lowJ] at ht he
    obtain ⟨jj, hjj, s', hes, hXs, hrole⟩ := c2_reduce htog he
      (fun jj hjj h => c1 jj hjj t (by omega) h)
    simp only at hjj hXs hrole
    rw [hes] at hrole
    rcases side_cases (BS[i]'hi).a s' with rfl | rfl | rfl | rfl
    · exact c1 jj hjj (t + 1) (by omega) (by rw [hXs]; unfold Bridge.cell; rw [nb_cellJ])
    · rcases Nat.eq_zero_or_pos t with h0 | hpos
      · subst h0
        rw [cellJ_zero] at hXs hrole
        exact caseB4 hVW hdc h0 hout0 hr hn hi hlow hmi (le_trans hc.hj' hmi) hc.row (hc.pair (by omega))
          hnOn hc.last hjj hXs hrole
      · apply c1 jj hjj (t - 1) (by omega)
        rw [hXs]; unfold Bridge.cell
        rw [show t = t - 1 + 1 by omega, nb_cellJ_opp, show t - 1 + 1 - 1 = t - 1 by omega]
    all_goals
      rcases Nat.eq_zero_or_pos t with h0 | hpos
      · subst h0
        rw [cellJ_zero] at hXs hrole
        first
          | exact caseB2 hVW hdc h0 hout0 hr hn hi hlow hmi (le_trans hc.hj' hmi) hc.row (hc.pair (by omega))
              hnOn hjj (Or.inl rfl) hXs hrole
          | exact caseB2 hVW hdc h0 hout0 hr hn hi hlow hmi (le_trans hc.hj' hmi) hc.row (hc.pair (by omega))
              hnOn hjj (Or.inr rfl) hXs hrole
      · first
          | exact caseB3 (sideLine_A hR htwo hev) (Or.inl rfl) htwo hc.row hc.lastArc hc.nOn
              (fun h l hl => hc.eavoid h i hi hmi l hl) hlast3 hjj hpos (by omega) hXs hrole
          | exact caseB3 (sideLine_B hR htwo hev) (Or.inr rfl) htwo hc.row hc.lastArc hc.nOn
              (fun h l hl => hc.eavoid h i hi hmi l hl) hlast3 hjj hpos (by omega) hXs hrole

-- **A lowered bridge's row is a chain row** at its creation time.
--
theorem chainRow_low {BS : List Bridge} {H : Finset Edge} (hr : Reach V H0 H BS) {uv : Pt × Pt}
    (hn : ¬ Conn H uv.1 uv.2) {k : ℕ} (hk : k < BS.length) (hlow : lowAt H BS uv k = true) :
    ChainRow V H0 H BS uv (k + 1) (k + 1) (BS[k]'hk).q (BS[k]'hk).a (BS[k]'hk).r
      ((BS[k]'hk).r - 1) := by
  obtain ⟨hrk, hrs, _⟩ := reach_at hVW hdc h0 hout0 hr hk
  have hrow := rowAt_at hVW hdc h0 hout0 hr hk
  have e := List.take_append_drop k BS
  have hr2 : Reach V H0 H (BS.take k ++ BS.drop k) := by rw [e]; exact hr
  have hs := reach_suffix hr2
  rw [List.drop_eq_getElem_cons hk] at hs
  obtain ⟨_, hmerge⟩ := reach_cons_nbs hs
  have hsep := (pinv_reach (t0 := t0) (u0 := u0) hVW hdc h0 hout0 hr).sep
  have two := hrs.two
  refine ⟨le_rfl, hmerge, hrow, fun hm => ?_, Or.inl (by omega), ?_, fun h => by omega,
    fun _ i hi hki l hl => ?_, fun i hi hki j hj l hl => ?_⟩
  · obtain ⟨_, _, _, f4⟩ := pend_facts hVW hdc h0 hout0 hr hn hk
    rw [f4 hm, ite_eq_left hlow]; rfl
  · exact hrs.last
  · have hz : NotZ (BS[k]'hk) (BS[i]'hi) := List.pairwise_iff_getElem.1 hsep k i hk hi (by omega)
    exact hz.1 l (by omega)
  · have := c1_newer hVW hdc h0 hout0 hr (k := k) (i := i) (by omega) hi true (j := j)
      (by simp [lowJ]; omega) hl
    simpa [lowJ] using this

-- **The half bridge's row (branches (b), (c)) is a chain row** at the final state.
--
theorem chainRow_half {BS : List Bridge} {H : Finset Edge} (hr : Reach V H0 H BS)
    (hmerge : MergeOK V H BS) {g : Bridge} (mf : MoveFacts V H BS g) :
    ChainRow V H0 H BS (rowStartPair g) 0 0 g.q g.a g.r g.r := by
  have hH := seqH_of_reach hr
  have hinv := pinv_reach (t0 := t0) (u0 := u0) hVW hdc h0 hout0 hr
  have hdegc := degc_of hVW hdc hinv.fac
  have hdrop : seqH H0 (BS.drop 0) = H := by rw [List.drop_zero, ← hH]
  have hn : ¬ Conn H (rowStartPair g).1 (rowStartPair g).2 := mf.2.1.2.2.1
  obtain ⟨lastO, lastE⟩ := last_alt mf hdegc
  have hd0 : BS.drop 0 = BS := List.drop_zero
  refine ⟨le_rfl, by rw [hd0, ← hH]; exact hmerge, by rw [hd0, ← hH]; exact rowAt_move mf,
    fun hm => ?_, Or.inr rfl, by rw [hdrop]; exact mf.2.2.2.2.2.2.2.2,
    fun _ => ?_, fun h => absurd h (lt_irrefl _), fun i hi _ j hj l hl => ?_⟩
  · exact (pend_facts hVW hdc h0 hout0 hr hn hm).2.2.1 rfl
  · rw [hdrop]
    rcases Nat.mod_two_eq_zero_or_one g.r with he | ho
    · obtain ⟨d1, d2, _, d4⟩ := lastE he
      exact Or.inr ⟨he, d1, d2, d4⟩
    · obtain ⟨_, _, d3, d4⟩ := lastO ho
      exact Or.inl ⟨d3, d4⟩
  · have hmem : BS[i]'hi ∈ BS := List.getElem_mem hi
    exact c1_half mf hdegc (fun b hb => let h := hinv.reg b hb; ⟨h.1, h.2.1, h.2.2.1⟩) hmem hj hl

end assemble

end HP

end SolidGridHam
