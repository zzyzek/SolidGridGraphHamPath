/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.HP.Sheffield.HoleClass

/-!
# One hole: the run stays in its class

`SolidFor V F H` (`D F H = 0` off the cells of `V`) is kept by each flip the run makes: a flip of
a cell whose two vertical sides have the same status changes `D` only at that cell
(`D_flip_formula`); alternating cells and the cells of a strip at their turn are of this kind
(ported from ulhc-hole ZeroOff.lean). Bridge steps flip alternating cells (`sf_reach`); the
joiners of the undo plan apply strips with their patterns (`sf_applyAll`).
-/

namespace ULHC

namespace HP

open Finset Classical

lemma up_lft_rgt' {F : Finset Edge} {c : Pt} (h : lft c ∈ F ↔ rgt c ∈ F) :
    up F (lft c) = ! up F (rgt c) := by
  obtain ⟨x, y⟩ := c
  unfold up inE1 par
  simp only [lft, rgt, Edge.lo]
  by_cases hl : (⟨.v, (x, y)⟩ : Edge) ∈ F
  · have hr : (⟨.v, (x + 1, y)⟩ : Edge) ∈ F := h.1 hl
    simp only [hl, hr, decide_true, Bool.not_true]
    rcases Int.emod_two_eq_zero_or_one (x - 1 + y) with h1 | h1 <;>
      rcases Int.emod_two_eq_zero_or_one (x + 1 - 1 + y) with h2 | h2 <;> simp [h1] <;> omega
  · have hr : (⟨.v, (x + 1, y)⟩ : Edge) ∉ F := fun h' => hl (h.2 h')
    simp only [hl, hr, decide_false, Bool.not_false]
    rcases Int.emod_two_eq_zero_or_one (x - 1 + y) with h1 | h1 <;>
      rcases Int.emod_two_eq_zero_or_one (x + 1 - 1 + y) with h2 | h2 <;> simp [h1] <;> omega

-- **One flip** of a cell whose vertical sides agree.
--
theorem sf_flip {V : Finset Pt} {F H : Finset Edge} {c : Pt} (hc : IsCell V c)
    (hlr : lft c ∈ F ↔ rgt c ∈ F) (hz : SolidFor V F H) : SolidFor V (flip F c) H := by
  intro x hx
  have hxc : x ≠ c := fun h => hx (h ▸ hc)
  have hf := D_flip_formula F H c x
  have hu := up_lft_rgt' hlr
  rw [hu, hz x hx] at hf
  obtain ⟨x1, x2⟩ := x
  obtain ⟨c1, c2⟩ := c
  simp only [Prod.mk.injEq, ne_eq] at hxc
  cases hr : up F (rgt (c1, c2)) <;> rw [hr] at hf <;> simp only [Bool.not_false, Bool.not_true,
    ite_true, Bool.false_eq_true, ite_false] at hf <;> split_ifs at hf with h1 h2 h2 <;> omega

lemma sf_flip_alt {V : Finset Pt} {F H : Finset Edge} {c : Pt} (hc : IsCell V c) (ha : Alt F c)
    (hz : SolidFor V F H) : SolidFor V (flip F c) H := by
  refine sf_flip hc ?_ hz
  unfold Alt at ha
  tauto

-- **A strip** with its pattern.
--
theorem sf_flipCol {V : Finset Pt} {H : Finset Edge} {c : Pt} {s : Side} :
    ∀ n (F : Finset Edge), StripPat F c s n → (∀ j < n, IsCell V (cellJ c s j)) →
      SolidFor V F H → SolidFor V (flipCol F c s n) H := by
  intro n
  induction n with
  | zero => intro F _ _ hz; exact hz
  | succ n ih =>
    intro F hpat hcell hz
    rw [flipCol_succ]
    have hce := hcell n (by omega)
    obtain ⟨hb, hl, hf⟩ := hpat
    have mF : front (cellJ c s n) s ∈ F ↔ n % 2 = 0 := by
      have := hf n (by omega); simp only [lt_self_iff_false, iff_false] at this; rw [this]; omega
    have mB : back (cellJ c s n) s ∈ F ↔ n % 2 = 0 := by
      rcases n with _ | n
      · simp only [cellJ_zero]; simp [hb]
      · rw [back_cellJ_succ]
        have := hf n (by omega)
        have q : n + 1 < n + 1 + 1 := by omega
        simp only [q, iff_true] at this
        rw [this]; omega
    have mL1 := (hl n (by omega)).1
    have mL2 := (hl n (by omega)).2
    have hlr : lft (cellJ c s n) ∈ F ↔ rgt (cellJ c s n) ∈ F := by
      cases s <;> simp only [front, back, lat1, lat2, sideEdge, Side.opp] at mF mB mL1 mL2 <;>
        first
        | (rw [mL1, mL2])
        | (constructor <;> intro h
           · first | exact mF.2 (mB.1 h) | exact mB.2 (mF.1 h)
           · first | exact mB.2 (mF.1 h) | exact mF.2 (mB.1 h))
    have hz' := sf_flip hce hlr hz
    rcases n with _ | n
    · simpa [flipCol] using hz'
    · exact ih _ (pat_flip_end ⟨hb, hl, hf⟩) (fun j hj => hcell j (by omega)) hz'

-- **The undo plan** (or any intact, compatible operations on cells of `V`).
--
theorem sf_applyAll {V W : Finset Pt} {H : Finset Edge} {P : Pt → Prop} {s0 p0 : Pt} :
    ∀ (ops : List Join) (G : Finset Edge), OpsOK W G ops P s0 p0 →
      (∀ o ∈ ops, ∀ j < o.n, IsCell V (cellJ o.c o.a j)) →
      SolidFor V G H → SolidFor V (applyAll G ops) H
  | [], _, _, _, hz => hz
  | o :: os, G, hops, hc, hz => by
    simp only [applyAll]
    obtain ⟨pat, _, _, _⟩ := hops.each o List.mem_cons_self
    exact sf_applyAll os _ hops.tail (fun o' ho' => hc o' (List.mem_cons_of_mem _ ho'))
      (sf_flipCol o.n G pat (hc o List.mem_cons_self) hz)

section reachSF

variable {V W : Finset Pt} {d : Pt → ℕ} {t0 u0 : Pt} {H0 : Finset Edge}
  (hVW : V ⊆ W) (hdc : ∀ q, IsCell V q → ∀ z, IsCorner z q → d z = 2)
  (h0 : IsFactor W d H0)
  (hout0 : ∀ e ∈ H0, (e.p ∉ V → e.q = t0 ∨ e.q = u0) ∧ (e.q ∉ V → e.p = t0 ∨ e.p = u0))
include hVW hdc h0 hout0

-- **Bridge steps** flip alternating cells.
--
theorem sf_reach {X : Finset Edge} :
    ∀ {H : Finset Edge} {BS : List Bridge}, Reach V H0 H BS → SolidFor V H0 X → SolidFor V H X := by
  intro H BS hr hz
  induction hr with
  | base => exact hz
  | step hr' hrs _ _ ih =>
    have hinv := pinv_reach (t0 := t0) (u0 := u0) hVW hdc h0 hout0 hr'
    obtain ⟨l1, l2, bk, fr, _⟩ := rowStep_pre hrs (degc_of hVW hdc hinv.fac)
    exact sf_flip_alt (hrs.cells _ (by have := hrs.two; omega)) (alt_of_lats l1 l2 bk fr) ih

end reachSF


lemma plan_cells {V : Finset Pt} {s t p : Pt} {e0 : Edge} (hpV : p ∉ V)
    (hsD : ∀ c, IsCell V c → ¬ IsCorner s c) (htV : t ∈ V) (he0 : Ends e0 t p) {H0 H : Finset Edge}
    (hN : NotchF V s p e0 H0) {BS : List Bridge} (hr : Reach V H0 H BS) {uv : Pt × Pt} :
    ∀ o ∈ plan H BS uv, ∀ j < o.n, IsCell V (cellJ o.c o.a j) := by
  have hinv := pinv_reach (t0 := t) (u0 := t) (Finset.subset_insert p V) (notch_dc (s := s) hpV hsD)
    hN.fac (notch_out htV he0 hN) hr
  intro o ho j hj
  obtain ⟨k, hk, rfl⟩ := mem_plan ho
  have reg := hinv.reg _ (List.getElem_mem hk)
  obtain ⟨l, hl, hY⟩ := opAt_cells hk reg.2.1 hj
  rw [hY]
  exact reg.2.2.2 l hl

section reduceSF

variable {V : Finset Pt} {s t p : Pt} {e0 : Edge}

-- **The reduction** keeps `SolidFor` (single phantom; `V` is the inner set).
--
theorem sf_reduceOutC (htV : t ∈ V) (hpV : p ∉ V) (he0 : Ends e0 t p)
    (hsD : ∀ c, IsCell V c → ¬ IsCorner s c) {H0 H X : Finset Edge} {BS : List Bridge}
    {out : POut} (hN : NotchF V s p e0 H0) (hpok : POK V H0 H BS out)
    (hs : out ≠ .stuck) (hf : out ≠ .fuel) (hz : SolidFor V H X) :
    SolidFor V (reduceOutC V (insert p V) H BS out) X := by
  have hVW : V ⊆ insert p V := Finset.subset_insert _ _
  have hdc := notch_dc (s := s) hpV hsD
  have hout0 := notch_out htV he0 hN
  cases out with
  | stuck => exact absurd rfl hs
  | fuel => exact absurd rfl hf
  | odd g =>
    obtain ⟨hr, hmerge, mf, ho⟩ := hpok
    obtain ⟨hHW, hb⟩ := brW_of_reach hpV hsD htV he0 hN hr
    have hc := corners_mem (isCell_mono mf.1 hVW) g.a
    have hinv := pinv_reach (t0 := t) (u0 := t) hVW hdc hN.fac hout0 hr
    obtain ⟨pat, _⟩ := oddRow_pat mf ho (degc_of hVW hdc hinv.fac)
    obtain ⟨ops, _⟩ := opsOK_rows (t0 := t) (u0 := t) hVW hdc hN.fac hout0 (Or.inl rfl) hsD hpV
      hr hmerge mf
    simp only [reduceOutC]
    rw [planB_eq hHW hc.1 hc.2 hb]
    exact sf_applyAll _ _ ops (plan_cells hpV hsD htV he0 hN hr)
      (sf_flipCol g.r H pat mf.2.2.2.2.2.1 hz)
  | twist g =>
    obtain ⟨hr, hmerge, mf, he, _⟩ := hpok
    obtain ⟨hHW, hb⟩ := brW_of_reach hpV hsD htV he0 hN hr
    have hc := corners_mem (isCell_mono mf.1 hVW) g.a
    have hinv := pinv_reach (t0 := t) (u0 := t) hVW hdc hN.fac hout0 hr
    obtain ⟨pat, _⟩ := evenRow_pat mf he (degc_of hVW hdc hinv.fac)
    obtain ⟨ops, _⟩ := opsOK_rows (t0 := t) (u0 := t) hVW hdc hN.fac hout0 (Or.inl rfl) hsD hpV
      hr hmerge mf
    simp only [reduceOutC]
    rw [planB_eq hHW hc.1 hc.2 hb]
    exact sf_applyAll _ _ ops (plan_cells hpV hsD htV he0 hN hr)
      (sf_flipCol g.r H pat mf.2.2.2.2.2.1 hz)
  | merge c =>
    obtain ⟨hr, hc, ha, hcut, hnp⟩ := hpok
    obtain ⟨hHW, hb⟩ := brW_of_reach hpV hsD htV he0 hN hr
    simp only [reduceOutC]
    refine getD_spec (cellList V) _ c (fun Y => SolidFor V (applyAll
        (flipCol H Y (altFrame H Y) 1) (planB (insert p V) H BS (mergePair H Y))) X) ?_ ?_
    · intro Y hYl hg
      have hY := (mem_cellList.1 hYl).2
      obtain ⟨haY, hcY, hnpY, hgY⟩ := (goodB_iff hVW hHW hb hY).1 hg
      have hcc := corners_mem (isCell_mono hY hVW) (altFrame H Y)
      rw [planB_eq hHW hcc.1 hcc.2 hb]
      obtain ⟨pat, _⟩ := merge_join_alt haY hcY
      obtain ⟨ops, _⟩ := opsOK_merge (t0 := t) (u0 := t) hVW hdc hN.fac hout0 (Or.inl rfl) hsD hpV
        hr (mcell_of hY haY hcY) haY hnpY hgY
      refine sf_applyAll _ _ ops (plan_cells hpV hsD htV he0 hN hr) (sf_flipCol 1 H pat ?_ hz)
      intro j hj
      obtain rfl : j = 0 := by omega
      rw [cellJ_zero]; exact hY
    · obtain ⟨Y, hY, haY, hcY, hnpY, hgY⟩ :=
        theoremR (t0 := t) (u0 := t) hVW hdc hN.fac hout0 (Or.inl rfl) (noOpp_same _ _ _) hr hc ha hcut hnp
      exact ⟨Y, mem_cellList.2 ⟨by obtain ⟨x, y⟩ := Y; exact hY.1, hY⟩,
        (goodB_iff hVW hHW hb hY).2 ⟨haY, hcY, hnpY, hgY⟩⟩

end reduceSF

end HP

end ULHC
