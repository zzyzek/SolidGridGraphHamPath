/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import SolidGridHam.Path.SPhase

/-!
# The certificate at the end of a phase

At a reachable state where every merging cell is a pair square (`MergeOK`, the success check),
the fixed pairs `FP = BS.map (pairOf H)` satisfy every pair field of `Cert`, and `F2`, `out` and
`L4` hold (`cert_of_phase`). The remaining fields (`tri`, `col`, `side`) are hypotheses here.
-/

namespace SolidGridHam

namespace HP

open Finset Classical

section certof

variable {V W : Finset Pt} {d : Pt → ℕ} {H : Finset Edge} {t0 u0 : Pt}

lemma pairwise_of_mem {α : Type*} {R : α → α → Prop} (hR : ∀ x y, R x y → R y x) :
    ∀ {l : List α}, l.Pairwise R → ∀ {x y : α}, x ∈ l → y ∈ l → x ≠ y → R x y
  | [], _, _, _, hx, _, _ => absurd hx List.not_mem_nil
  | z :: l, hp, x, y, hx, hy, hxy => by
    rw [List.pairwise_cons] at hp
    rcases List.mem_cons.1 hx with h1 | h1 <;> rcases List.mem_cons.1 hy with h2 | h2
    · exact absurd (h1.trans h2.symm) hxy
    · rw [h1]; exact hp.1 y h2
    · rw [h2]; exact hR _ _ (hp.1 x h1)
    · exact pairwise_of_mem hR hp.2 h1 h2 hxy

lemma top_ne_bot (i : FixedPr) : i.top ≠ i.bot := by
  unfold FixedPr.top; intro e
  obtain ⟨⟨x, y⟩, s, _, _, _, _⟩ := i
  cases s <;> simp [nb] at e

lemma A_ne_E (b : Bridge) (htwo : 2 ≤ b.r) : b.cell (b.r - 2) ≠ b.E := by
  unfold Bridge.E Bridge.cell
  intro e
  have := cellJ_inj e
  omega

-- The two pair squares of a bridge are its top and bottom.
--
lemma pair_squares {b : Bridge} (hR : RegionOK H b) (htwo : 2 ≤ b.r) (hev : b.r % 2 = 0) :
    ((b.pairOf H).top = b.cell (b.r - 2) ∧ (b.pairOf H).bot = b.E) ∨
      ((b.pairOf H).top = b.E ∧ (b.pairOf H).bot = b.cell (b.r - 2)) := by
  obtain ⟨_, _, _, _, ht, hb⟩ := pair_facts hR htwo hev
  have hne := top_ne_bot (b.pairOf H)
  rcases ht with ht | ht <;> rcases hb with hb | hb
  · exact absurd (ht.trans hb.symm) hne
  · exact Or.inl ⟨ht, hb⟩
  · exact Or.inr ⟨ht, hb⟩
  · exact absurd (ht.trans hb.symm) hne

theorem cert_of_phase (hVW : V ⊆ W) (hdc : ∀ q, IsCell V q → ∀ z, IsCorner z q → d z = 2)
    {BS : List Bridge} (hinv : PInv V W d H BS t0 u0) (hmerge : MergeOK V H BS)
    (hfar : Far t0 u0)
    (htri : ∀ f, IsCell V f → Three H f → TriOK V H t0 u0 f)
    (hcol : ∀ q s, IsCell V q → CriticalIn H q s → back q s ∈ H →
      (∀ i ∈ BS.map (Bridge.pairOf H), q ≠ i.top ∧ q ≠ i.bot) →
      ColEnds V H (BS.map (Bridge.pairOf H)) q s (outArc H q s) ∨ ColOut V H q s (outArc H q s))
    (hside : SideCert V H (BS.map (Bridge.pairOf H))) :
    Cert V H (BS.map (Bridge.pairOf H)) t0 u0 := by
  have hdegc := degc_of hVW hdc hinv.fac
  have facts : ∀ i ∈ BS.map (Bridge.pairOf H), ∃ b ∈ BS, i = b.pairOf H := by
    intro i hi; obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hi; exact ⟨b, hb, rfl⟩
  have pf : ∀ i ∈ BS.map (Bridge.pairOf H), PairOK H i ∧ (Alt H i.top ∧ Alt H i.bot) ∧
      sideEdge i.bot i.s ∈ H ∧ (IsCorner i.tx i.top ∧ IsCorner i.ty i.top ∧
        IsCorner i.bx i.bot ∧ IsCorner i.by' i.bot) := by
    intro i hi
    obtain ⟨b, hb, rfl⟩ := facts i hi
    obtain ⟨hR, h2, he, _⟩ := hinv.reg b hb
    obtain ⟨p1, p2, p3, p4, _⟩ := pair_facts hR h2 he
    exact ⟨p1, p2, p3, p4⟩
  have f2 : ∀ q, IsCell V q → Alt H q → CutSq H q →
      ∃ i ∈ BS.map (Bridge.pairOf H), q = i.top ∨ q = i.bot := by
    intro q hq ha hc
    obtain ⟨b, hb, hqb⟩ := hmerge q hq ha hc
    obtain ⟨hR, h2, he, _⟩ := hinv.reg b hb
    refine ⟨b.pairOf H, List.mem_map.2 ⟨b, hb, rfl⟩, ?_⟩
    rcases pair_squares hR h2 he with ⟨ht, hbt⟩ | ⟨ht, hbt⟩ <;> rcases hqb with rfl | rfl
    · exact Or.inl ht.symm
    · exact Or.inr hbt.symm
    · exact Or.inr hbt.symm
    · exact Or.inl ht.symm
  refine ⟨f2, fun i hi => (pf i hi).1, htri, hinv.out,
    l4_of hfar hdegc f2 (fun i hi => (pf i hi).2.1) (fun i hi => (pf i hi).2.2.1) hinv.out,
    fun i hi => (pf i hi).2.1, fun i hi => (pf i hi).2.2.1, fun i hi => (pf i hi).2.2.2, ?_, hcol,
    hside⟩
  -- Pairs of different bridges are disjoint.
  --
  intro i hi j hj hov
  obtain ⟨b1, hb1, rfl⟩ := facts i hi
  obtain ⟨b2, hb2, rfl⟩ := facts j hj
  by_cases h12 : b1 = b2
  · rw [h12]
  exfalso
  have hD : Disj b1 b2 := pairwise_of_mem (fun _ _ h => Disj.symm h) hinv.disj hb1 hb2 h12
  obtain ⟨hR1, t1, e1, _⟩ := hinv.reg b1 hb1
  obtain ⟨hR2, t2, e2, _⟩ := hinv.reg b2 hb2
  obtain ⟨d1, d2, d3, d4⟩ := hD
  rcases pair_squares hR1 t1 e1 with ⟨x1, y1⟩ | ⟨x1, y1⟩ <;>
    rcases pair_squares hR2 t2 e2 with ⟨x2, y2⟩ | ⟨x2, y2⟩ <;>
    rw [x1, y1, x2, y2] at hov <;>
    rcases hov with h | h | h | h <;> first | exact d1 h | exact d2 h | exact d3 h | exact d4 h
end certof

end HP

end SolidGridHam
