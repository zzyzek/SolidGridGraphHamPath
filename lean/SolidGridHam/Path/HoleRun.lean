/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import SolidGridHam.Path.SlitHeight

/-!
# One hole: the run stays in its class

`SolidFor V F H` (`D F H = 0` off the cells of `V`) is kept by each flip the run makes: a flip of
a cell whose two vertical sides have the same status changes `D` only at that cell
(`D_flip_formula`); alternating cells and the cells of a strip at their turn are of this kind
(ported from ulhc-hole ZeroOff.lean). Bridge steps flip alternating cells (`sf_reach`); the
joiners of the undo plan apply strips with their patterns (`sf_applyAll`).
-/

namespace SolidGridHam

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

end HP

end SolidGridHam
