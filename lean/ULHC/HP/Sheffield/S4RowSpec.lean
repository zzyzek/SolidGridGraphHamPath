/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.HP.Sheffield.S4Rows

/-!
# S4 for the row outcomes

For the `.odd` and `.twist` outcomes of a phase, `reduceOut` is a notch state with one piece
fewer than the start of the phase.  The counting runs with the degree-one points in the order
`p`, `s`, since `p ∈ insert p V` holds outright.
-/

namespace ULHC

namespace HP

open Finset Classical

lemma OpsOK.swap {W : Finset Pt} {G : Finset Edge} {ops : List Join} {P : Pt → Prop} {a b : Pt}
    (h : OpsOK W G ops P a b) : OpsOK W G ops P b a :=
  ⟨fun o ho => by
    obtain ⟨h1, h2, h3, h4, h5⟩ := h.each o ho
    exact ⟨h1, h2, h3, fun j hj => (h4 j hj).symm, h5⟩, h.compat⟩

section s4rowspec

variable {V : Finset Pt} {s t p : Pt} {e0 : Edge}

lemma notCorner_out (hpV : p ∉ V) {c : Pt} (hc : IsCell V c) : ¬ IsCorner p c := by
  intro hz
  apply hpV
  obtain ⟨x, y⟩ := c
  rcases hz with h | h | h | h <;> rw [h]
  · exact hc.1
  · exact hc.2.1
  · exact hc.2.2.1
  · exact hc.2.2.2

-- The phase's flips are on cells of `V`, so they keep the edges at `p`.
--
lemma reach_pat (hpV : p ∉ V) {H0 H : Finset Edge} {BS : List Bridge} (hr : Reach V H0 H BS)
    (h : PAt p e0 H0) : PAt p e0 H := by
  induction hr with
  | base => exact h
  | step _ hrs _ _ ih => exact ih.flip hpV (hrs.cells _ (by have := hrs.two; omega))

lemma dST_two (z : Pt) (h1 : z ≠ p) (h2 : z ≠ s) : dST s p z = 2 := by
  unfold dST; rw [ite_eq_right]; tauto

lemma dST_p : dST s p p = 1 := by unfold dST; simp

-- **The common tail.** A row half bridge with its count and its relation off the interior
-- points, followed by the undo plan.
--
theorem s4_row (htV : t ∈ V) (hpV : p ∉ V) (he0 : Ends e0 t p)
    (hsD : ∀ c, IsCell V c → ¬ IsCorner s c) {H0 H : Finset Edge} (hN : NotchF V s p e0 H0)
    {BS : List Bridge} (hr : Reach V H0 H BS) (hmerge : MergeOK V H BS) {g : Bridge}
    (mf : MoveFacts V H BS g)
    (half : IsFactor (insert p V) (dST s p) (flipCol H g.q g.a g.r) ∧
      ncomp (insert p V) (flipCol H g.q g.a g.r) + 1 = ncomp (insert p V) H ∧
      ∀ x y, ¬ IsMid g.q g.a (g.r - 1) x → ¬ IsMid g.q g.a (g.r - 1) y →
        (Conn (flipCol H g.q g.a g.r) x y ↔
          merge (Conn H) (back1 g.q g.a) (front1 g.q g.a) x y)) :
    NotchF V s p e0 (applyAll (flipCol H g.q g.a g.r) (plan H BS (rowStartPair g))) ∧
      ncomp (insert p V) (applyAll (flipCol H g.q g.a g.r) (plan H BS (rowStartPair g))) + 1 =
        ncomp (insert p V) H0 := by
  have hVW : V ⊆ insert p V := Finset.subset_insert _ _
  have hdc := notch_dc (s := s) hpV hsD
  have hout0 := notch_out htV he0 hN
  obtain ⟨ops, nomid⟩ := opsOK_rows (t0 := t) (u0 := t) hVW hdc hN.fac hout0 (Or.inl rfl) hsD hpV hr hmerge mf
  have hinv := pinv_reach (t0 := t) (u0 := t) hVW hdc hN.fac hout0 hr
  have ops' := ops.swap
  have hd2 : ∀ z ∈ insert p V, z ≠ p → z ≠ s → dST s p z = 2 := fun z _ h1 h2 => dST_two z h1 h2
  have hcount := undo_count (s0 := p) (p0 := s) hVW hdc hN.fac hout0 hd2 dST_p
    (Finset.mem_insert_self _ _) BS H hr (flipCol H g.q g.a g.r) (rowStartPair g) _ half.1 half.2.1
    (fun x y hx hy => half.2.2 x y (nomid x hx) (nomid y hy))
    ⟨_, List.mem_cons_self, Or.inl rfl⟩ ⟨_, List.mem_cons_self, Or.inr rfl⟩ mf.2.1.2.2.1 ops'
  refine ⟨⟨applyAll_factor _ _ half.1 ops', ?_⟩, hcount⟩
  refine applyAll_pat hpV _ _ ?_
    (PAt.flipCol hpV g.r H (reach_pat hpV hr hN.pat) mf.2.2.2.2.2.1)
  intro o ho j hj
  obtain ⟨k, hk, rfl⟩ := mem_plan ho
  have reg := hinv.reg _ (List.getElem_mem hk)
  obtain ⟨l, hl, hY⟩ := opAt_cells hk reg.2.1 hj
  rw [hY]
  exact reg.2.2.2 l hl

-- **S4 for an odd row.**
--
theorem s4_odd (htV : t ∈ V) (hpV : p ∉ V) (he0 : Ends e0 t p)
    (hsD : ∀ c, IsCell V c → ¬ IsCorner s c) {H0 H : Finset Edge} (hN : NotchF V s p e0 H0)
    {BS : List Bridge} {g : Bridge} (hpok : POK V H0 H BS (.odd g)) :
    NotchF V s p e0 (reduceOut V (insert p V) s p H BS (.odd g)) ∧
      ncomp (insert p V) (reduceOut V (insert p V) s p H BS (.odd g)) + 1 =
        ncomp (insert p V) H0 := by
  obtain ⟨hr, hmerge, mf, ho⟩ := hpok
  have hVW : V ⊆ insert p V := Finset.subset_insert _ _
  have hdc := notch_dc (s := s) hpV hsD
  have hinv := pinv_reach (t0 := t) (u0 := t) hVW hdc hN.fac (notch_out htV he0 hN) hr
  obtain ⟨pat, hnp⟩ := oddRow_pat mf ho (degc_of hVW hdc hinv.fac)
  have cellsV := mf.2.2.2.2.2.1
  have half := join_apply (s0 := p) (p0 := s) (o := ⟨g.q, g.a, g.r⟩)
    (fun z _ h1 h2 => dST_two z h1 h2) dST_p (Finset.mem_insert_self _ _) hinv.fac pat ho
    (fun j hj => isCell_mono (cellsV j hj) hVW)
    (fun j hj => ⟨notCorner_out hpV (cellsV j hj), hsD _ (cellsV j hj)⟩) hnp
  exact s4_row htV hpV he0 hsD hN hr hmerge mf half

-- **S4 for a twist.**
--
theorem s4_twist (htV : t ∈ V) (hpV : p ∉ V) (he0 : Ends e0 t p)
    (hsD : ∀ c, IsCell V c → ¬ IsCorner s c) {H0 H : Finset Edge} (hN : NotchF V s p e0 H0)
    {BS : List Bridge} {g : Bridge} (hpok : POK V H0 H BS (.twist g)) :
    NotchF V s p e0 (reduceOut V (insert p V) s p H BS (.twist g)) ∧
      ncomp (insert p V) (reduceOut V (insert p V) s p H BS (.twist g)) + 1 =
        ncomp (insert p V) H0 := by
  obtain ⟨hr, hmerge, mf, he, htw⟩ := hpok
  have hVW : V ⊆ insert p V := Finset.subset_insert _ _
  have hdc := notch_dc (s := s) hpV hsD
  have hinv := pinv_reach (t0 := t) (u0 := t) hVW hdc hN.fac (notch_out htV he0 hN) hr
  have cellsV := mf.2.2.2.2.2.1
  obtain ⟨f1, f2, f3⟩ := twist_count (s0 := p) (p0 := s) hVW
    (fun z _ h1 h2 => dST_two z h1 h2) dST_p (Finset.mem_insert_self _ _) hinv.fac mf he htw
    (degc_of hVW hdc hinv.fac)
    (fun j hj => ⟨notCorner_out hpV (cellsV j hj), hsD _ (cellsV j hj)⟩)
  have mono : ∀ x, ¬ IsMid g.q g.a (g.r - 1) x → ¬ IsMid g.q g.a (g.r - 2) x :=
    fun x h ⟨j, h1, h2, h3⟩ => h ⟨j, h1, by omega, h3⟩
  exact s4_row htV hpV he0 hsD hN hr hmerge mf
    ⟨f1, f2, fun x y hx hy => f3 x y (mono x hx) (mono y hy)⟩

end s4rowspec

end HP

end ULHC
