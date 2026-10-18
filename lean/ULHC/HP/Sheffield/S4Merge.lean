/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.HP.Sheffield.S4RowSpec

/-!
# S4 for the merging-cell outcome, given a good cell

`reduceOut` on `.merge c` takes the first cell of `cellList V` that is alternating, cut, not a
pair square, and whose plan passes `candOK` (rule (a*), docs/S4_RESIDUAL.md). Here: when such a
cell exists, the result is a notch state with one piece fewer than the start of the phase.
Existence of a good cell is Theorem R (separate).
-/

namespace ULHC

namespace HP

open Finset Classical

-- A good merging cell for the state `(H, BS)` (the test in `reduceOut`).
--
def GoodCell (W : Finset Pt) (s0 p0 : Pt) (H : Finset Edge) (BS : List Bridge) (X : Pt) : Prop :=
  Alt H X ∧ CutSq H X ∧ ¬ (∃ b ∈ BS, X = b.cell (b.r - 2) ∨ X = b.E) ∧
    candOK W H ((mergeJoin H X).apply H) BS (mergeJoin H X) 0
      (reduceOut.rowStartPair' (mergeJoin H X)) s0 p0

-- A cut alternating cell is a strip of one cell in its `altFrame`.
--
lemma merge_join_alt {G : Finset Edge} {c : Pt} (ha : Alt G c) (hcut : CutSq G c) :
    StripPat G c (altFrame G c) 1 ∧
      ¬ Conn G (back1 c (altFrame G c)) (front1 c (altFrame G c)) := by
  have frame : back c (altFrame G c) ∈ G ∧ front c (altFrame G c) ∈ G ∧
      lat1 c (altFrame G c) ∉ G ∧ lat2 c (altFrame G c) ∉ G := by
    unfold altFrame
    unfold Alt at ha
    split_ifs with hb
    · rcases ha with ⟨h1, h2, h3, h4⟩ | ⟨h1, _, _, _⟩
      · exact ⟨h1, h2, h3, h4⟩
      · exact absurd hb h1
    · rcases ha with ⟨h1, _, _, _⟩ | ⟨h1, h2, h3, h4⟩
      · exact absurd h1 hb
      · exact ⟨h3, h4, h1, h2⟩
  obtain ⟨hb, hf, hl1, hl2⟩ := frame
  refine ⟨⟨hb, fun j hj => ?_, fun j hj => ?_⟩, fun h => ?_⟩
  · obtain rfl : j = 0 := by omega
    rw [cellJ_zero]
    exact ⟨⟨fun h => absurd h hl1, fun h => by omega⟩, ⟨fun h => absurd h hl2, fun h => by omega⟩⟩
  · obtain rfl : j = 0 := by omega
    rw [cellJ_zero]; exact ⟨fun _ => by omega, fun _ => hf⟩
  · have kb := (ends_back (c := c) (s := altFrame G c)).conn hb
    have kf := (ends_front (c := c) (s := altFrame G c)).conn hf
    exact uncut_of kb h ((kb.symm.trans h).trans kf) hcut

lemma getD_spec {α : Type*} (l : List α) (f : α → Bool) (c : α) (P : α → Prop)
    (h1 : ∀ X ∈ l, f X = true → P X) (h2 : ∃ X ∈ l, f X = true) : P ((l.find? f).getD c) := by
  cases hf : l.find? f with
  | none =>
    obtain ⟨X, hX, hfX⟩ := h2
    exact absurd hfX (by simpa using List.find?_eq_none.1 hf X hX)
  | some X => exact h1 X (List.mem_of_find?_eq_some hf) (List.find?_some hf)

section s4merge

variable {V : Finset Pt} {s t p : Pt} {e0 : Edge}

-- **S4 for a good merging cell.**
--
theorem s4_good (htV : t ∈ V) (hpV : p ∉ V) (he0 : Ends e0 t p)
    (hsD : ∀ c, IsCell V c → ¬ IsCorner s c) {H0 H : Finset Edge} (hN : NotchF V s p e0 H0)
    {BS : List Bridge} (hr : Reach V H0 H BS) {X : Pt} (hX : IsCell V X)
    (hg : GoodCell (insert p V) s p H BS X) :
    NotchF V s p e0 (applyAll ((mergeJoin H X).apply H)
        (plan H BS (reduceOut.rowStartPair' (mergeJoin H X)))) ∧
      ncomp (insert p V) (applyAll ((mergeJoin H X).apply H)
        (plan H BS (reduceOut.rowStartPair' (mergeJoin H X)))) + 1 = ncomp (insert p V) H0 := by
  obtain ⟨ha, hcut, _, hops, hnm⟩ := hg
  have hVW : V ⊆ insert p V := Finset.subset_insert _ _
  have hdc := notch_dc (s := s) hpV hsD
  have hout0 := notch_out htV he0 hN
  have hinv := pinv_reach (t0 := t) (u0 := t) hVW hdc hN.fac hout0 hr
  obtain ⟨pat, hnp⟩ := merge_join_alt ha hcut
  have cellsX : ∀ j < (mergeJoin H X).n, IsCell V (cellJ (mergeJoin H X).c (mergeJoin H X).a j) := by
    intro j hj
    obtain rfl : j = 0 := by simp [mergeJoin] at hj; omega
    rw [cellJ_zero]; exact hX
  have half := join_apply (s0 := p) (p0 := s) (o := mergeJoin H X)
    (fun z _ h1 h2 => dST_two z h1 h2) dST_p (Finset.mem_insert_self _ _) hinv.fac pat rfl
    (fun j hj => isCell_mono (cellsX j hj) hVW)
    (fun j hj => ⟨notCorner_out hpV (cellsX j hj), hsD _ (cellsX j hj)⟩) hnp
  have ops' := hops.swap
  have hd2 : ∀ z ∈ insert p V, z ≠ p → z ≠ s → dST s p z = 2 := fun z _ h1 h2 => dST_two z h1 h2
  have hcount := undo_count (s0 := p) (p0 := s) hVW hdc hN.fac hout0 hd2 dST_p
    (Finset.mem_insert_self _ _) BS H hr ((mergeJoin H X).apply H)
    (reduceOut.rowStartPair' (mergeJoin H X)) _ half.1 half.2.1
    (fun x y hx hy => half.2.2 x y (hnm x hx) (hnm y hy))
    ⟨_, List.mem_cons_self, Or.inl rfl⟩ ⟨_, List.mem_cons_self, Or.inr rfl⟩ hnp ops'
  refine ⟨⟨applyAll_factor _ _ half.1 ops', ?_⟩, hcount⟩
  refine applyAll_pat hpV _ _ ?_
    (PAt.flipCol hpV _ H (reach_pat hpV hr hN.pat) cellsX)
  intro o ho j hj
  obtain ⟨k, hk, rfl⟩ := mem_plan ho
  have reg := hinv.reg _ (List.getElem_mem hk)
  obtain ⟨l, hl, hY⟩ := opAt_cells hk reg.2.1 hj
  rw [hY]
  exact reg.2.2.2 l hl

-- **S4 for the merging-cell outcome**, given that some cell of `V` is good.
--
theorem s4_merge (htV : t ∈ V) (hpV : p ∉ V) (he0 : Ends e0 t p)
    (hsD : ∀ c, IsCell V c → ¬ IsCorner s c) {H0 H : Finset Edge} (hN : NotchF V s p e0 H0)
    {BS : List Bridge} {c : Pt} (hpok : POK V H0 H BS (.merge c))
    (hex : ∃ X, IsCell V X ∧ X ∈ V ∧ GoodCell (insert p V) s p H BS X) :
    NotchF V s p e0 (reduceOut V (insert p V) s p H BS (.merge c)) ∧
      ncomp (insert p V) (reduceOut V (insert p V) s p H BS (.merge c)) + 1 =
        ncomp (insert p V) H0 := by
  obtain ⟨hr, -⟩ := hpok
  unfold reduceOut
  simp only
  refine getD_spec (cellList V) _ c (fun X => NotchF V s p e0 (applyAll ((mergeJoin H X).apply H)
      (plan H BS (reduceOut.rowStartPair' (mergeJoin H X)))) ∧
      ncomp (insert p V) (applyAll ((mergeJoin H X).apply H)
        (plan H BS (reduceOut.rowStartPair' (mergeJoin H X)))) + 1 = ncomp (insert p V) H0) ?_ ?_
  · intro X hX h
    simp only [decide_eq_true_eq] at h
    exact s4_good htV hpV he0 hsD hN hr (mem_cellList.1 hX).2 h
  · obtain ⟨X, hX, hXV, hg⟩ := hex
    refine ⟨X, mem_cellList.2 ⟨hXV, hX⟩, ?_⟩
    simp only [decide_eq_true_eq]
    exact hg

-- **Theorem R (statement).** At a merging-cell outcome some cell of `V` is good.
--
def MergeGoodSpec (V : Finset Pt) (s p : Pt) (e0 : Edge) : Prop :=
  ∀ (H0 H : Finset Edge) (BS : List Bridge) (c : Pt), NotchF V s p e0 H0 →
    2 ≤ ncomp (insert p V) H0 → POK V H0 H BS (.merge c) →
      ∃ X, IsCell V X ∧ X ∈ V ∧ GoodCell (insert p V) s p H BS X

-- **S4** from Theorem R.
--
theorem s4Spec_of (htV : t ∈ V) (hpV : p ∉ V) (he0 : Ends e0 t p)
    (hsD : ∀ c, IsCell V c → ¬ IsCorner s c) (hR : MergeGoodSpec V s p e0) : S4Spec V s p e0 := by
  intro H0 H BS out hN h2 hpok hs hf
  cases out with
  | stuck => exact absurd rfl hs
  | fuel => exact absurd rfl hf
  | merge c => exact s4_merge htV hpV he0 hsD hN hpok (hR H0 H BS c hN h2 hpok)
  | odd g => exact s4_odd htV hpV he0 hsD hN hpok
  | twist g => exact s4_twist htV hpV he0 hsD hN hpok

end s4merge

end HP

end ULHC
