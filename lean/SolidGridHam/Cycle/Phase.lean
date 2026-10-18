/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import SolidGridHam.Cycle.Walk

/-!
# Phase I: the walk along a border terminates at a stop cell

Orientation `o = true`: the walk follows `F`'s arcs and `D ≥ 2` throughout.
Orientation `o = false`: it goes against them and `D ≤ −2` throughout.
-/

namespace SolidGridHam

open Finset Classical

def Good (o : Bool) (d : ℤ) : Prop := if o then 2 ≤ d else d ≤ -2

lemma Deg2.factor {V : Finset Pt} {F : Finset Edge} (h : Deg2 V F) : IsFactor V (fun _ => 2) F :=
  ⟨fun e he => h.1 e he, h.2⟩

lemma sideEdge_nb_opp (c : Pt) (s : Side) : sideEdge (nb c s) s.opp = sideEdge c s := by
  have := back_nb c s; simpa [back, front] using this

lemma outArc_nb_opp (F : Finset Edge) (c : Pt) (s : Side) :
    outArc F (nb c s) s.opp = !outArc F c s := by
  obtain ⟨x, y⟩ := c
  cases s <;> simp [outArc, nb, Side.opp, bot, top, lft, rgt]

section dmono

variable {V : Finset Pt} {F H : Finset Edge} (hF : Deg2 V F) (hH : Deg2 V H)
include hF hH

lemma D_mono (o : Bool) (c : Pt) (s : Side) (h : outArc F c s = o) :
    if o then D F H c ≤ D F H (nb c s) else D F H (nb c s) ≤ D F H c := by
  have := D_step hF.factor hH.factor c s
  rw [h] at this
  cases o <;> simp only [Bool.false_eq_true, ite_false, ite_true] at this ⊢ <;>
    split_ifs at this <;> omega

lemma Good.step {o : Bool} {c : Pt} {s : Side} (h : outArc F c s = o) (hg : Good o (D F H c)) :
    Good o (D F H (nb c s)) := by
  have := D_mono hF hH o c s h
  unfold Good at *
  cases o <;> simp only [Bool.false_eq_true, ite_false, ite_true] at this hg ⊢ <;> omega

lemma Good.isCell (hs : Solid V) {o : Bool} {c : Pt} (hg : Good o (D F H c)) : IsCell V c := by
  by_contra h
  have := D_eq_zero_of_not_cell hF.factor hH.factor hs h
  unfold Good at hg; rw [this] at hg
  cases o <;> simp at hg

end dmono

lemma nb_nb_opp (c : Pt) (s : Side) : nb (nb c s) s.opp = c := by
  obtain ⟨x, y⟩ := c; cases s <;> simp [nb, Side.opp]

/-! ## The walk -/

section phase1

variable {V : Finset Pt} {F H : Finset Edge} {P : Finset Pt}
  (hF : Deg2 V F) (hH : Deg2 V H) (hs : Solid V) (hB : Border V F P) (hT : NoTypeIII V F)
  (o : Bool)

-- A cut side with an outgoing arc (in the walk's orientation).
--
def Out (F : Finset Edge) (P : Finset Pt) (o : Bool) (w : Pt) : Prop :=
  ∃ so, Cut P (sideEdge w so) ∧ outArc F w so = o

-- A cut side with an incoming arc.
--
def Entered (F : Finset Edge) (P : Finset Pt) (o : Bool) (w : Pt) : Prop :=
  ∃ si, Cut P (sideEdge w si) ∧ outArc F w si = !o

noncomputable def sig (F : Finset Edge) (P : Finset Pt) (o : Bool) (w : Pt) : Pt :=
  if h : Out F P o w then nb w (Classical.choose h) else w

lemma sig_spec {w : Pt} (h : Out F P o w) :
    ∃ so, sig F P o w = nb w so ∧ Cut P (sideEdge w so) ∧ outArc F w so = o := by
  refine ⟨Classical.choose h, by simp [sig, h], (Classical.choose_spec h).1,
    (Classical.choose_spec h).2⟩

-- The stop configuration: a Type I cell entered through a lateral side.
--
def Stop (F : Finset Edge) (P : Finset Pt) (o : Bool) (w : Pt) : Prop :=
  ∃ d, sideEdge w d ∈ F ∧ sideEdge w d.opp ∉ F ∧ sideEdge w (latA d) ∉ F ∧
    sideEdge w (latB d) ∉ F ∧
    (∃ si, (si = latA d ∨ si = latB d) ∧ Cut P (sideEdge w si) ∧ outArc F w si = !o) ∧
    ¬ Cut P (sideEdge w d.opp) ∧ outArc F w d.opp = o

include hF hB hT in
-- With a way out, the incoming cut side is unique.
--
lemma uniq_of_out {w : Pt} (hw : IsCell V w) (si : Side) (hcut : Cut P (sideEdge w si))
    (hin : outArc F w si = !o) (hout : Out F P o w) :
    ∀ s1 s2, Cut P (sideEdge w s1) → outArc F w s1 = !o →
      Cut P (sideEdge w s2) → outArc F w s2 = !o → s1 = s2 := by
  rcases step_cell hB w o (fun s h => cut_has_dark_lat hF hB hT hw s h)
      (fun ha => alt_no_cut hB hT hw ha) si hcut hin with
    ⟨so, _, _, _, h4⟩ | ⟨_, _, _, _, _, _, _, _, hall'⟩
  · exact fun s1 s2 c1 o1 c2 o2 => (h4 s1 c1 o1).trans (h4 s2 c2 o2).symm
  · obtain ⟨so', hc', ho'⟩ := hout
    have := hall' so' hc'
    rw [ho'] at this
    cases o <;> simp at this

include hF hB hT in
-- Without a way out, the cell stops the walk.
--
lemma stop_of_not_out {w : Pt} (hw : IsCell V w) (he : Entered F P o w)
    (hno : ¬ Out F P o w) : Stop F P o w := by
  obtain ⟨si, hcut, hin⟩ := he
  rcases step_cell hB w o (fun s h => cut_has_dark_lat hF hB hT hw s h)
      (fun ha => alt_no_cut hB hT hw ha) si hcut hin with
    ⟨so, _, h2, h3, _⟩ | ⟨d, h1, h2, h3, h4, h5, h6, h7, _⟩
  · exact absurd ⟨so, h2, h3⟩ hno
  · exact ⟨d, h1, h2, h3, h4, ⟨si, h5, hcut, hin⟩, h6, h7⟩

include hF hH hs hB hT in
theorem phase1 (v : Pt) (s0 : Side) (hcut : Cut P (sideEdge v s0)) (hin : outArc F v s0 = !o)
    (hjump : if o then D F H v = D F H (nb v s0) + 2 else D F H v = D F H (nb v s0) - 2)
    (hgood : Good o (D F H v)) :
    ∃ w, IsCell V w ∧ Good o (D F H w) ∧ Stop F P o w := by
  set u := nb v s0
  let wk : ℕ → Pt := fun k => (sig F P o)^[k] v
  have wk0 : wk 0 = v := rfl
  have wks : ∀ k, wk (k + 1) = sig F P o (wk k) := fun k => Function.iterate_succ_apply' _ _ _
  -- Invariant along the walk.
  have inv : ∀ k, (∀ i < k, Out F P o (wk i)) →
      Entered F P o (wk k) ∧ Good o (D F H (wk k)) ∧
        (if o then D F H v ≤ D F H (wk k) else D F H (wk k) ≤ D F H v) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨⟨s0, hcut, hin⟩, hgood, ?_⟩
      rw [wk0]; cases o <;> simp
    | succ k ih =>
      intro hall
      obtain ⟨_, hg, hm⟩ := ih (fun i hi => hall i (by omega))
      obtain ⟨so, hsig, hc, ho⟩ := sig_spec o (hall k (by omega))
      rw [wks, hsig]
      refine ⟨⟨so.opp, by rw [sideEdge_nb_opp]; exact hc, by rw [outArc_nb_opp, ho]⟩,
        Good.step hF hH ho hg, ?_⟩
      have := D_mono hF hH o (wk k) so ho
      cases o <;> simp only [Bool.false_eq_true, ite_false, ite_true] at hm this ⊢ <;> omega
  set N := (cells V).card
  by_cases hall : ∀ k ≤ N, Out F P o (wk k)
  · exfalso
    -- No cell repeats.
    have inj : ∀ i j, i < j → j ≤ N → wk i ≠ wk j := by
      intro i
      induction i with
      | zero =>
        intro j hj hjN heq
        obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        obtain ⟨so, hsig, hc, ho⟩ := sig_spec o (hall j' (by omega))
        rw [wk0, wks, hsig] at heq
        -- `v` is entered from `wk j'` through `so.opp`, and from `u` through `s0`.
        have uniq := uniq_of_out hF hB hT o (Good.isCell hF hH hs hgood) s0 hcut hin
          (by have := hall 0 (by omega); rwa [wk0] at this)
        have e := uniq s0 so.opp hcut hin
          (by rw [heq, sideEdge_nb_opp]; exact hc) (by rw [heq, outArc_nb_opp, ho])
        have hwu : wk j' = u := by
          rw [show u = nb v s0 from rfl, e, heq, nb_nb_opp]
        obtain ⟨_, _, hm⟩ := inv j' (fun i hi => hall i (by omega))
        rw [hwu] at hm
        cases o <;> simp only [Bool.false_eq_true, ite_false, ite_true] at hm hjump <;> omega
      | succ i ih =>
        intro j hij hjN heq
        obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        obtain ⟨so1, hs1, hc1, ho1⟩ := sig_spec o (hall i (by omega))
        obtain ⟨so2, hs2, hc2, ho2⟩ := sig_spec o (hall j' (by omega))
        rw [wks, wks, hs1, hs2] at heq
        set z := nb (wk i) so1
        have hzc := (inv (i + 1) (fun k hk => hall k (by omega))).2.1
        rw [wks, hs1] at hzc
        have uniq := uniq_of_out hF hB hT o (Good.isCell hF hH hs hzc) so1.opp
          (by rw [sideEdge_nb_opp]; exact hc1) (by rw [outArc_nb_opp, ho1])
          (by have := hall (i + 1) (by omega); rwa [wks, hs1] at this)
        have e := uniq so1.opp so2.opp (by rw [sideEdge_nb_opp]; exact hc1)
          (by rw [outArc_nb_opp, ho1]) (by rw [heq, sideEdge_nb_opp]; exact hc2)
          (by rw [heq, outArc_nb_opp, ho2])
        apply ih j' (by omega) (by omega)
        have h1 : nb z so1.opp = wk i := nb_nb_opp _ _
        have h2 : nb z so2.opp = wk j' := by rw [heq, nb_nb_opp]
        rw [← h1, ← h2, e]
    -- Pigeonhole.
    have hmaps : ∀ k ∈ Finset.range (N + 1), wk k ∈ cells V := by
      intro k hk
      rw [Finset.mem_range] at hk
      exact mem_cells.2 (Good.isCell hF hH hs
        (inv k (fun i hi => hall i (by omega))).2.1)
    have hinj : Set.InjOn wk (Finset.range (N + 1)) := by
      intro i hi j hj heq
      simp only [Finset.coe_range, Set.mem_Iio] at hi hj
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with h | h
      · exact inj i j h (by omega) heq
      · exact inj j i h (by omega) heq.symm
    have := Finset.card_le_card_of_injOn wk hmaps hinj
    simp only [Finset.card_range] at this
    omega
  · push Not at hall
    obtain ⟨k, hkN, hk⟩ := hall
    -- The first cell with no way out.
    have ex : ∃ k, ¬ Out F P o (wk k) := ⟨k, hk⟩
    let k0 := Nat.find ex
    have hk0 : ¬ Out F P o (wk k0) := Nat.find_spec ex
    have hbefore : ∀ i < k0, Out F P o (wk i) := fun i hi => by
      have := Nat.find_min ex hi; push Not at this; exact this
    obtain ⟨he, hg, _⟩ := inv k0 hbefore
    have hc := Good.isCell hF hH hs hg
    exact ⟨wk k0, hc, hg, stop_of_not_out hF hB hT o hc he hk0⟩

end phase1

end SolidGridHam
