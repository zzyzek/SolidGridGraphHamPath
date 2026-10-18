/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import SolidGridHam.Path.NoMid
import SolidGridHam.Path.Reduce
import SolidGridHam.Path.PhaseCount
import SolidGridHam.Path.Cert
import SolidGridHam.Path.Prelim.NotchPF

/-!
# S4 for the row branches (odd row, twist)

The undo plan after a row half bridge is intact and compatible (`OpsOK`), so `undo_count` gives
one piece fewer than the start of the phase, and the result is a notch state.
-/

namespace SolidGridHam

namespace HP

open Finset Classical

section s4rows

variable {W : Finset Pt} {d : Pt → ℕ}

-- Applying intact operations keeps the factor.
--
theorem applyAll_factor {s0 p0 : Pt} {P : Pt → Prop} :
    ∀ (ops : List Join) (G : Finset Edge), IsFactor W d G → OpsOK W G ops P s0 p0 →
      IsFactor W d (applyAll G ops)
  | [], _, hG, _ => hG
  | o :: os, G, hG, hops => by
    simp only [applyAll]
    obtain ⟨pat, _, cells, _⟩ := hops.each o List.mem_cons_self
    obtain ⟨hin, hd⟩ := degs_flipCol o.n G (Inside.of_factor hG) pat cells
    exact applyAll_factor os _ ⟨fun e he => hin e he, fun z hz => by
      unfold Join.apply; rw [hd z, hG.2 z hz]⟩ hops.tail

-- Operations on cells of `V` keep the edges at `p ∉ V`.
--
theorem applyAll_pat {V : Finset Pt} {p : Pt} {e0 : Edge} (hpV : p ∉ V) :
    ∀ (ops : List Join) (G : Finset Edge), (∀ o ∈ ops, ∀ j < o.n, IsCell V (cellJ o.c o.a j)) →
      PAt p e0 G → PAt p e0 (applyAll G ops)
  | [], _, _, h => h
  | o :: os, G, hc, h => by
    simp only [applyAll]
    apply applyAll_pat hpV os _ (fun o' ho' => hc o' (List.mem_cons_of_mem _ ho'))
    intro e he
    unfold Join.apply
    rw [mem_flipCol, nOn_zero]
    · simp only [Nat.zero_mod, iff_true]; exact h e he
    · intro j hj hmem
      obtain ⟨cp, cq⟩ := corners_of_cellE hmem
      have hcell := hc o List.mem_cons_self j hj
      have inV : ∀ z, IsCorner z (cellJ o.c o.a j) → z ∈ V := by
        intro z hz
        obtain ⟨x, y⟩ := cellJ o.c o.a j
        rcases hz with rfl | rfl | rfl | rfl
        · exact hcell.1
        · exact hcell.2.1
        · exact hcell.2.2.1
        · exact hcell.2.2.2
      rcases he with h' | h'
      · exact hpV (h' ▸ inV _ cp)
      · exact hpV (h' ▸ inV _ cq)

end s4rows

noncomputable def opAt (H : Finset Edge) (BS : List Bridge) (uv : Pt × Pt) (k : ℕ)
    (hk : k < BS.length) : Join :=
  if lowAt H BS uv k then lowJ (BS[k]'hk) else undoJ (BS[k]'hk)

lemma mem_plan {H : Finset Edge} {BS : List Bridge} {uv : Pt × Pt} {o : Join}
    (h : o ∈ plan H BS uv) : ∃ k, ∃ hk : k < BS.length, o = opAt H BS uv k hk := by
  rw [List.mem_iff_getElem] at h
  obtain ⟨k, hk, rfl⟩ := h
  rw [plan_length] at hk
  exact ⟨k, hk, plan_getElem H BS uv hk⟩

-- Cells of a plan operation are squares of its bridge.
--
lemma opAt_cells {H : Finset Edge} {BS : List Bridge} {uv : Pt × Pt} {k : ℕ} (hk : k < BS.length)
    (htwo : 2 ≤ (BS[k]'hk).r) {t : ℕ} (ht : t < (opAt H BS uv k hk).n) :
    ∃ l < (BS[k]'hk).r, cellJ (opAt H BS uv k hk).c (opAt H BS uv k hk).a t = (BS[k]'hk).cell l :=
  planOp_cells htwo _ ht

section compat

variable {V W : Finset Pt} {d : Pt → ℕ} {t0 u0 : Pt} {H0 : Finset Edge}
  (hVW : V ⊆ W) (hdc : ∀ q, IsCell V q → ∀ z, IsCorner z q → d z = 2)
  (h0 : IsFactor W d H0) (hout0 : ∀ e ∈ H0, (e.p ∉ V → e.q = t0 ∨ e.q = u0) ∧ (e.q ∉ V → e.p = t0 ∨ e.p = u0))
include hVW hdc h0 hout0

-- **(F2)** An earlier plan operation toggles no side of a later one's squares.
--
theorem c2_plan (hfar : Far t0 u0) {BS : List Bridge} {H : Finset Edge} (hr : Reach V H0 H BS)
    {uv : Pt × Pt}
    (hn : ¬ Conn H uv.1 uv.2) {k i : ℕ} (hki : k < i) (hi : i < BS.length)
    {t : ℕ} (ht : t < (opAt H BS uv i hi).n) {e : Edge}
    (he : e ∈ cellE (cellJ (opAt H BS uv i hi).c (opAt H BS uv i hi).a t)) :
    ¬ (opAt H BS uv k (by omega)).tog e := by
  have hk : k < BS.length := by omega
  intro htog
  unfold opAt at htog ht he
  cases hlk : lowAt H BS uv k
  · simp only [hlk, Bool.false_eq_true, ↓reduceIte] at htog
    obtain ⟨j, hj, hmem⟩ := tog_cell htog
    simp only [undoJ] at hj hmem
    obtain rfl : j = 0 := by omega
    rw [cellJ_zero] at hmem
    have hsep := (pinv_reach (t0 := t0) (u0 := u0) hVW hdc h0 hout0 hr).sep
    have hz : NotZ (BS[k]'hk) (BS[i]'hi) := List.pairwise_iff_getElem.1 hsep k i hk hi hki
    obtain ⟨_, two, _, _⟩ := (pinv_reach (t0 := t0) (u0 := u0) hVW hdc h0 hout0 hr).reg _ (List.getElem_mem hi)
    obtain ⟨l, hl, hY⟩ := planOp_cells two (lowAt H BS uv i) ht
    rw [hY] at he
    exact notZ_shared hz hl he hmem
  · simp only [hlk, ↓reduceIte] at htog
    exact c2_chain hVW hdc h0 hout0 hfar hr hn (chainRow_low hVW hdc h0 hout0 hr hn hk hlk) hi
      (by omega) ht he htog

-- **`OpsOK` for the plan after a row half bridge.**
--
theorem opsOK_rows (hfar : Far t0 u0) {s0 p0 : Pt} (hsD : ∀ c, IsCell V c → ¬ IsCorner s0 c) (hp0 : p0 ∉ V)
    {BS : List Bridge} {H : Finset Edge} (hr : Reach V H0 H BS) (hmerge : MergeOK V H BS)
    {g : Bridge} (mf : MoveFacts V H BS g) :
    OpsOK W (Join.apply H ⟨g.q, g.a, g.r⟩) (plan H BS (rowStartPair g))
        (relPts ((⟨g.q, g.a, g.r⟩ : Join) :: plan H BS (rowStartPair g))) s0 p0 ∧
      ∀ x, relPts ((⟨g.q, g.a, g.r⟩ : Join) :: plan H BS (rowStartPair g)) x →
        ¬ IsMid g.q g.a (g.r - 1) x := by
  set M : Join := ⟨g.q, g.a, g.r⟩ with hM
  set uv := rowStartPair g with huv
  have hn : ¬ Conn H uv.1 uv.2 := mf.2.1.2.2.1
  have hinv := pinv_reach (t0 := t0) (u0 := u0) hVW hdc h0 hout0 hr
  have hdegc := degc_of hVW hdc hinv.fac
  have hc := chainRow_half hVW hdc h0 hout0 hr hmerge mf
  have two := mf.2.2.2.2.1
  have reg := fun k (hk : k < BS.length) => hinv.reg _ (List.getElem_mem hk)
  -- (F1) the half bridge toggles no side of a plan operation
  have F1 : ∀ k (hk : k < BS.length), ∀ t < (opAt H BS uv k hk).n,
      ∀ e ∈ cellE (cellJ (opAt H BS uv k hk).c (opAt H BS uv k hk).a t), ¬ M.tog e :=
    fun k hk t ht e he htog => c2_chain hVW hdc h0 hout0 hfar hr hn hc hk (Nat.zero_le _) ht he htog
  -- (F3) the half bridge's cells avoid every bridge square
  have F3 : ∀ k (hk : k < BS.length), ∀ j < M.n, ∀ t < (opAt H BS uv k hk).n,
      cellJ M.c M.a j ≠ cellJ (opAt H BS uv k hk).c (opAt H BS uv k hk).a t := by
    intro k hk j hj t ht
    obtain ⟨l, hl, hY⟩ := opAt_cells hk (reg k hk).2.1 ht
    rw [hY]
    exact c1_half mf hdegc (fun b hb => let h := hinv.reg b hb; ⟨h.1, h.2.1, h.2.2.1⟩)
      (List.getElem_mem hk) hj hl
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
    · exact noMid (by simp [M]; omega)
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
  refine ⟨⟨fun o ho => ?_, ?_⟩, fun x hx => ?_⟩
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
  · obtain ⟨O', hO', hxO⟩ := hx
    rcases List.mem_cons.1 hO' with rfl | hO'
    · exact noMid_self _ hxO
    · obtain ⟨i, hi, rfl⟩ := mem_plan hO'
      have hn1 : 1 ≤ (opAt H BS uv i hi).n := by
        unfold opAt; split_ifs <;> simp [lowJ, undoJ]; have := (reg i hi).2.1; omega
      exact noMid hn1 (fun j hj j' hj' => F3 i hi j hj j' hj') (Or.inl (F1 i hi)) (corner_of hxO)

end compat

end HP

end SolidGridHam
