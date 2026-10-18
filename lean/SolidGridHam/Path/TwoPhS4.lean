/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import SolidGridHam.Path.TwoPh

/-!
# Two phantoms: S4, the "no" answer, and the decided loop

The generic S3/S4 results with `W₂ = V ∪ {p, q}`, `d = dST p q` (degree one at `p`, `q`), and
out-vertices `t`, `s` at king distance at least 3 (`Far t s`). `hpSheffC2_correct`: the decided
Sheffield loop on two-phantom states answers the Hamiltonian `s`–`t` path problem.
-/

namespace SolidGridHam

namespace HP

open Finset Classical

section twoS4

variable {V : Finset Pt} {s t p q : Pt} {e0 e1 : Edge}
  (hst : s ≠ t) (hsV : s ∈ V) (htV : t ∈ V) (hpV : p ∉ V) (hqV : q ∉ V) (hpq : p ≠ q)
  (he0 : Ends e0 t p) (he1 : Ends e1 s q) (hfr : FarN t p s q)

lemma vw2 : V ⊆ insert q (insert p V) := (Finset.subset_insert _ _).trans (Finset.subset_insert _ _)

lemma pw2 : p ∈ insert q (insert p V) := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)

include hsV htV hpV hqV he0 he1 hfr

omit hfr in
lemma plan_cells2 {H0 H : Finset Edge} {BS : List Bridge} (hN : NotchF2 V p q e0 e1 H0)
    (hr : Reach V H0 H BS) {uv : Pt × Pt} :
    ∀ o ∈ plan H BS uv, ∀ j < o.n, IsCell V (cellJ o.c o.a j) := by
  have hinv := pinv_reach (t0 := t) (u0 := s) vw2 (two_dc hpV hqV) hN.fac
    (two_out htV hsV he0 he1 hN) hr
  intro o ho j hj
  obtain ⟨k, hk, rfl⟩ := mem_plan ho
  have reg := hinv.reg _ (List.getElem_mem hk)
  obtain ⟨l, hl, hY⟩ := opAt_cells hk reg.2.1 hj
  rw [hY]
  exact reg.2.2.2 l hl

theorem s4_row2 {H0 H : Finset Edge} (hN : NotchF2 V p q e0 e1 H0)
    {BS : List Bridge} (hr : Reach V H0 H BS) (hmerge : MergeOK V H BS) {g : Bridge}
    (mf : MoveFacts V H BS g)
    (half : IsFactor (insert q (insert p V)) (dST p q) (flipCol H g.q g.a g.r) ∧
      ncomp (insert q (insert p V)) (flipCol H g.q g.a g.r) + 1 = ncomp (insert q (insert p V)) H ∧
      ∀ x y, ¬ IsMid g.q g.a (g.r - 1) x → ¬ IsMid g.q g.a (g.r - 1) y →
        (Conn (flipCol H g.q g.a g.r) x y ↔
          merge (Conn H) (back1 g.q g.a) (front1 g.q g.a) x y)) :
    NotchF2 V p q e0 e1 (applyAll (flipCol H g.q g.a g.r) (plan H BS (rowStartPair g))) ∧
      ncomp (insert q (insert p V)) (applyAll (flipCol H g.q g.a g.r) (plan H BS (rowStartPair g))) + 1 =
        ncomp (insert q (insert p V)) H0 := by
  have hdc := two_dc hpV hqV
  have hout0 := two_out htV hsV he0 he1 hN
  obtain ⟨ops, nomid⟩ := opsOK_rows (t0 := t) (u0 := s) (s0 := q) (p0 := p) vw2 hdc hN.fac hout0 hfr.1
    (fun c hc => notCorner_out hqV hc) hpV hr hmerge mf
  have ops' := ops.swap
  have hcount := undo_count (s0 := p) (p0 := q) vw2 hdc hN.fac hout0
    (fun z _ h1 h2 => dST_off h1 h2) (dST_s p q) pw2 BS H hr (flipCol H g.q g.a g.r) (rowStartPair g) _
    half.1 half.2.1 (fun x y hx hy => half.2.2 x y (nomid x hx) (nomid y hy))
    ⟨_, List.mem_cons_self, Or.inl rfl⟩ ⟨_, List.mem_cons_self, Or.inr rfl⟩ mf.2.1.2.2.1 ops'
  have hc := plan_cells2 hsV htV hpV hqV he0 he1 hN hr (uv := rowStartPair g)
  refine ⟨⟨applyAll_factor _ _ half.1 ops', ?_, ?_⟩, hcount⟩
  · exact applyAll_pat hpV _ _ hc (PAt.flipCol hpV g.r H (reach_pat hpV hr hN.patp) mf.2.2.2.2.2.1)
  · exact applyAll_pat hqV _ _ hc (PAt.flipCol hqV g.r H (reach_pat hqV hr hN.patq) mf.2.2.2.2.2.1)

theorem s4_odd2 {H0 H : Finset Edge} (hN : NotchF2 V p q e0 e1 H0) {BS : List Bridge} {g : Bridge}
    (hpok : POK V H0 H BS (.odd g)) :
    NotchF2 V p q e0 e1 (applyAll (flipCol H g.q g.a g.r) (plan H BS (rowStartPair g))) ∧
      ncomp (insert q (insert p V)) (applyAll (flipCol H g.q g.a g.r) (plan H BS (rowStartPair g))) + 1 =
        ncomp (insert q (insert p V)) H0 := by
  obtain ⟨hr, hmerge, mf, ho⟩ := hpok
  have hdc := two_dc hpV hqV
  have hinv := pinv_reach (t0 := t) (u0 := s) vw2 hdc hN.fac (two_out htV hsV he0 he1 hN) hr
  obtain ⟨pat, hnp⟩ := oddRow_pat mf ho (degc_of vw2 hdc hinv.fac)
  have cellsV := mf.2.2.2.2.2.1
  have half := join_apply (s0 := p) (p0 := q) (o := ⟨g.q, g.a, g.r⟩)
    (fun z _ h1 h2 => dST_off h1 h2) (dST_s p q) pw2 hinv.fac pat ho
    (fun j hj => isCell_mono (cellsV j hj) vw2)
    (fun j hj => ⟨notCorner_out hpV (cellsV j hj), notCorner_out hqV (cellsV j hj)⟩) hnp
  exact s4_row2 hsV htV hpV hqV he0 he1 hfr hN hr hmerge mf half

theorem s4_twist2 {H0 H : Finset Edge} (hN : NotchF2 V p q e0 e1 H0) {BS : List Bridge}
    {g : Bridge} (hpok : POK V H0 H BS (.twist g)) :
    NotchF2 V p q e0 e1 (applyAll (flipCol H g.q g.a g.r) (plan H BS (rowStartPair g))) ∧
      ncomp (insert q (insert p V)) (applyAll (flipCol H g.q g.a g.r) (plan H BS (rowStartPair g))) + 1 =
        ncomp (insert q (insert p V)) H0 := by
  obtain ⟨hr, hmerge, mf, he, htw⟩ := hpok
  have hdc := two_dc hpV hqV
  have hinv := pinv_reach (t0 := t) (u0 := s) vw2 hdc hN.fac (two_out htV hsV he0 he1 hN) hr
  have cellsV := mf.2.2.2.2.2.1
  obtain ⟨f1, f2, f3⟩ := twist_count (s0 := p) (p0 := q) vw2
    (fun z _ h1 h2 => dST_off h1 h2) (dST_s p q) pw2 hinv.fac mf he htw
    (degc_of vw2 hdc hinv.fac)
    (fun j hj => ⟨notCorner_out hpV (cellsV j hj), notCorner_out hqV (cellsV j hj)⟩)
  have mono : ∀ x, ¬ IsMid g.q g.a (g.r - 1) x → ¬ IsMid g.q g.a (g.r - 2) x :=
    fun x h ⟨j, h1, h2, h3⟩ => h ⟨j, h1, by omega, h3⟩
  exact s4_row2 hsV htV hpV hqV he0 he1 hfr hN hr hmerge mf
    ⟨f1, f2, fun x y hx hy => f3 x y (mono x hx) (mono y hy)⟩

theorem s4_good2 {H0 H : Finset Edge} (hN : NotchF2 V p q e0 e1 H0)
    {BS : List Bridge} (hr : Reach V H0 H BS) {X : Pt} (hX : IsCell V X) (ha : Alt H X)
    (hcut : CutSq H X) (hnp : ¬ ∃ b ∈ BS, X = b.cell (b.r - 2) ∨ X = b.E)
    (hgood : ∀ i (hi : i < BS.length), lowAt H BS (mergePair H X) i = false →
      X ≠ nb (BS[i]'hi).E (BS[i]'hi).a) :
    NotchF2 V p q e0 e1 (applyAll (flipCol H X (altFrame H X) 1) (plan H BS (mergePair H X))) ∧
      ncomp (insert q (insert p V)) (applyAll (flipCol H X (altFrame H X) 1) (plan H BS (mergePair H X)))
        + 1 = ncomp (insert q (insert p V)) H0 := by
  have hdc := two_dc hpV hqV
  have hout0 := two_out htV hsV he0 he1 hN
  have hinv := pinv_reach (t0 := t) (u0 := s) vw2 hdc hN.fac hout0 hr
  obtain ⟨_, _, _, hops, hnm⟩ := goodCell_of (s0 := q) (p0 := p) vw2 hdc hN.fac hout0 hfr.1
    (fun c hc => notCorner_out hqV hc) hpV hr hX ha hcut hnp hgood
  obtain ⟨pat, hnc⟩ := merge_join_alt ha hcut
  have cellsX : ∀ j < (mergeJoin H X).n,
      IsCell V (cellJ (mergeJoin H X).c (mergeJoin H X).a j) := by
    intro j hj
    obtain rfl : j = 0 := by simp [mergeJoin] at hj; omega
    rw [cellJ_zero]; exact hX
  have half := join_apply (s0 := p) (p0 := q) (o := mergeJoin H X)
    (fun z _ h1 h2 => dST_off h1 h2) (dST_s p q) pw2 hinv.fac pat rfl
    (fun j hj => isCell_mono (cellsX j hj) vw2)
    (fun j hj => ⟨notCorner_out hpV (cellsX j hj), notCorner_out hqV (cellsX j hj)⟩) hnc
  have ops' := hops.swap
  have hcount := undo_count (s0 := p) (p0 := q) vw2 hdc hN.fac hout0
    (fun z _ h1 h2 => dST_off h1 h2) (dST_s p q) pw2 BS H hr ((mergeJoin H X).apply H)
    (reduceOut.rowStartPair' (mergeJoin H X)) _ half.1 half.2.1
    (fun x y hx hy => half.2.2 x y (hnm x hx) (hnm y hy))
    ⟨_, List.mem_cons_self, Or.inl rfl⟩ ⟨_, List.mem_cons_self, Or.inr rfl⟩ hnc ops'
  have hc := plan_cells2 hsV htV hpV hqV he0 he1 hN hr
    (uv := reduceOut.rowStartPair' (mergeJoin H X))
  refine ⟨⟨applyAll_factor _ _ half.1 ops', ?_, ?_⟩, hcount⟩
  · exact applyAll_pat hpV _ _ hc (PAt.flipCol hpV _ H (reach_pat hpV hr hN.patp) cellsX)
  · exact applyAll_pat hqV _ _ hc (PAt.flipCol hqV _ H (reach_pat hqV hr hN.patq) cellsX)

omit hfr in
lemma brW2 {H0 H : Finset Edge} (hN : NotchF2 V p q e0 e1 H0) {BS : List Bridge}
    (hr : Reach V H0 H BS) : Inside (insert q (insert p V)) H ∧ BrW (insert q (insert p V)) BS := by
  have hinv := pinv_reach (t0 := t) (u0 := s) vw2 (two_dc hpV hqV) hN.fac
    (two_out htV hsV he0 he1 hN) hr
  refine ⟨Inside.of_factor hinv.fac, fun b hb => ?_⟩
  obtain ⟨_, htwo, _, cells⟩ := hinv.reg b hb
  refine ⟨isCell_mono (cells _ (by omega)) vw2, ?_⟩
  have := cells 0 (by omega)
  unfold Bridge.cell at this; rw [cellJ_zero] at this
  exact isCell_mono this vw2

-- **S4 for the decided reduction, two phantoms.**
--
theorem s4C2 {H0 H : Finset Edge} {BS : List Bridge} {out : POut}
    (hN : NotchF2 V p q e0 e1 H0) (hpok : POK V H0 H BS out)
    (hs : out ≠ .stuck) (hf : out ≠ .fuel) :
    NotchF2 V p q e0 e1 (reduceOutC V (insert q (insert p V)) H BS out) ∧
      ncomp (insert q (insert p V)) (reduceOutC V (insert q (insert p V)) H BS out) + 1 =
        ncomp (insert q (insert p V)) H0 := by
  cases out with
  | stuck => exact absurd rfl hs
  | fuel => exact absurd rfl hf
  | odd g =>
    obtain ⟨hHW, hb⟩ := brW2 hsV htV hpV hqV he0 he1 hN hpok.1
    have hc := corners_mem (isCell_mono hpok.2.2.1.1 (vw2 (p := p) (q := q))) g.a
    simp only [reduceOutC]
    rw [planB_eq hHW hc.1 hc.2 hb]
    exact s4_odd2 hsV htV hpV hqV he0 he1 hfr hN hpok
  | twist g =>
    obtain ⟨hHW, hb⟩ := brW2 hsV htV hpV hqV he0 he1 hN hpok.1
    have hc := corners_mem (isCell_mono hpok.2.2.1.1 (vw2 (p := p) (q := q))) g.a
    simp only [reduceOutC]
    rw [planB_eq hHW hc.1 hc.2 hb]
    exact s4_twist2 hsV htV hpV hqV he0 he1 hfr hN hpok
  | merge c =>
    obtain ⟨hr, hc, ha, hcut, hnp⟩ := hpok
    obtain ⟨hHW, hb⟩ := brW2 hsV htV hpV hqV he0 he1 hN hr
    have hdc := two_dc hpV hqV
    have hout0 := two_out htV hsV he0 he1 hN
    simp only [reduceOutC]
    refine getD_spec (cellList V) _ c (fun X => NotchF2 V p q e0 e1 (applyAll
        (flipCol H X (altFrame H X) 1) (planB (insert q (insert p V)) H BS (mergePair H X))) ∧
      ncomp (insert q (insert p V)) (applyAll (flipCol H X (altFrame H X) 1)
        (planB (insert q (insert p V)) H BS (mergePair H X))) + 1 =
          ncomp (insert q (insert p V)) H0) ?_ ?_
    · intro X hXl hg
      have hX := (mem_cellList.1 hXl).2
      obtain ⟨haX, hcX, hnpX, hgX⟩ := (goodB_iff vw2 hHW hb hX).1 hg
      have hcc := corners_mem (isCell_mono hX (vw2 (p := p) (q := q))) (altFrame H X)
      rw [planB_eq hHW hcc.1 hcc.2 hb]
      exact s4_good2 hsV htV hpV hqV he0 he1 hfr hN hr hX haX hcX hnpX hgX
    · obtain ⟨X, hX, haX, hcX, hnpX, hgX⟩ :=
        theoremR (t0 := t) (u0 := s) vw2 hdc hN.fac hout0 hfr.1
          (two_noOpp hsV htV hpV hqV he0 he1 hN hfr.2) hr hc ha hcut hnp
      exact ⟨X, mem_cellList.2 ⟨by obtain ⟨x, y⟩ := X; exact hX.1, hX⟩,
        (goodB_iff vw2 hHW hb hX).2 ⟨haX, hcX, hnpX, hgX⟩⟩

omit hfr in
lemma two_pok {G : Finset Edge} (hG : NotchF2 V p q e0 e1 G) (n : ℕ) :
    POK V G (phase V (insert q (insert p V)) n G []).1 (phase V (insert q (insert p V)) n G []).2.1
      (phase V (insert q (insert p V)) n G []).2.2 :=
  phase_spec (t0 := t) (u0 := s) vw2 (two_dc hpV hqV) hG.fac (two_out htV hsV he0 he1 hG) n G []
    Reach.base

include hst hpq

-- **The "no" answer, two phantoms.** A stuck phase from a state with two pieces or more admits no
-- Hamiltonian `s`–`t` path.
--
theorem phase_no_hp2 (hs : Solid V) {H0 : Finset Edge} (h0 : NotchF2 V p q e0 e1 H0)
    (hm : 2 ≤ ncomp V H0) {H : Finset Edge} {BS : List Bridge} (hr : Reach V H0 H BS)
    (hmerge : MergeOK V H BS) (hstuck : Stuck V H BS) :
    ¬ ∃ H', IsFactor V (dST s t) H' ∧ ncomp V H' = 1 := by
  rintro ⟨H', hH', hHam⟩
  have hdc := two_dc hpV hqV
  have hout0 := two_out htV hsV he0 he1 h0
  have hinv := pinv_reach (t0 := t) (u0 := s) vw2 hdc h0.fac hout0 hr
  have hG : NotchF2 V p q e0 e1 H := two_reach hpV hqV hr h0 hinv.fac
  have hc := cert_of_stuck vw2 hdc h0.fac hout0 hr hmerge hstuck hfr.1
  have hcnt := reach_count vw2 hdc h0.fac hout0 hr
  rw [h0.ncomp hsV htV he0 he1, hG.ncomp hsV htV he0 he1] at hcnt
  have hHN := two_up hst hsV htV hpV hqV hpq he0 he1 hH'
  have hHam' : ncomp V (insert e1 (insert e0 H')) = 1 := ncomp_one_of_conn htV (fun x hx y hy =>
    (conn_of_ncomp_one hHam hx hy).mono
      ((Finset.subset_insert _ _).trans (Finset.subset_insert _ _)))
  have hcount := cert_count hG.fac hHN.fac hs vw2 hdc (two_symm hG hHN) hc
  rw [hG.ncomp hsV htV he0 he1, hHN.ncomp hsV htV he0 he1, hHam'] at hcount
  simp only [List.length_map] at hcount
  omega

end twoS4

-- **The decided loop, two phantoms.**
--
def runSC2 (V : Finset Pt) (p q : Pt) : ℕ → Finset Edge → Bool
  | 0, G => cncomp (insert q (insert p V)) G == 1
  | n + 1, G =>
    if cncomp (insert q (insert p V)) G == 1 then true
    else
      match phase V (insert q (insert p V)) ((insert q (insert p V)).card + 1) G [] with
      | (_, _, .stuck) => false
      | (_, _, .fuel) => false
      | (H, BS, out) => runSC2 V p q n (reduceOutC V (insert q (insert p V)) H BS out)

def hpSheffC2 (V : Finset Pt) (s t p q : Pt) (e0 e1 : Edge) : Bool :=
  match findFactor V (dST s t) with
  | none => false
  | some R => runSC2 V p q (V.card + 2) (insert e1 (insert e0 R))

section loop2

variable {V : Finset Pt} {s t p q : Pt} {e0 e1 : Edge}
  (hst : s ≠ t) (hsV : s ∈ V) (htV : t ∈ V) (hpV : p ∉ V) (hqV : q ∉ V) (hpq : p ≠ q)
  (he0 : Ends e0 t p) (he1 : Ends e1 s q) (hfr : FarN t p s q)
include hsV htV hpV hqV he0 he1 hfr

omit hpV hqV hfr in
lemma cncomp_two {G : Finset Edge} (hG : NotchF2 V p q e0 e1 G) :
    cncomp (insert q (insert p V)) G = ncomp V G := by
  rw [cncomp_eq (Inside.of_factor hG.fac), hG.ncomp hsV htV he0 he1]

theorem runSC2_sound :
    ∀ n G, NotchF2 V p q e0 e1 G → runSC2 V p q n G = true →
      ∃ G', NotchF2 V p q e0 e1 G' ∧ ncomp V G' = 1 := by
  intro n
  induction n with
  | zero =>
    intro G hG h
    simp only [runSC2, beq_iff_eq] at h
    exact ⟨G, hG, by rw [← cncomp_two hsV htV he0 he1 hG]; exact h⟩
  | succ n ih =>
    intro G hG h
    by_cases h1 : cncomp (insert q (insert p V)) G = 1
    · exact ⟨G, hG, by rw [← cncomp_two hsV htV he0 he1 hG]; exact h1⟩
    have h1' : (cncomp (insert q (insert p V)) G == 1) = false := by simpa using h1
    simp only [runSC2, h1', Bool.false_eq_true, ↓reduceIte] at h
    have hpok := two_pok hsV htV hpV hqV he0 he1 hG ((insert q (insert p V)).card + 1)
    rcases hph : phase V (insert q (insert p V)) ((insert q (insert p V)).card + 1) G [] with
      ⟨H, BS, out⟩
    rw [hph] at h hpok
    cases out with
    | stuck => simp at h
    | fuel => simp at h
    | merge c =>
      exact ih _ (s4C2 hsV htV hpV hqV he0 he1 hfr hG hpok (by simp) (by simp)).1 h
    | odd b => exact ih _ (s4C2 hsV htV hpV hqV he0 he1 hfr hG hpok (by simp) (by simp)).1 h
    | twist b => exact ih _ (s4C2 hsV htV hpV hqV he0 he1 hfr hG hpok (by simp) (by simp)).1 h

include hst hpq

theorem runSC2_complete (hs : Solid V) (hHP : ∃ H, IsFactor V (dST s t) H ∧ ncomp V H = 1) :
    ∀ n G, NotchF2 V p q e0 e1 G → ncomp V G ≤ n + 1 → runSC2 V p q n G = true := by
  intro n
  induction n with
  | zero =>
    intro G hG hle
    have := ncomp_pos (F := G) htV
    simp only [runSC2, beq_iff_eq, cncomp_two hsV htV he0 he1 hG]; omega
  | succ n ih =>
    intro G hG hle
    by_cases h1 : ncomp V G = 1
    · simp [runSC2, cncomp_two hsV htV he0 he1 hG, h1]
    have h2 : 2 ≤ ncomp V G := by have := ncomp_pos (F := G) htV; omega
    have h1' : (cncomp (insert q (insert p V)) G == 1) = false := by
      simpa [cncomp_two hsV htV he0 he1 hG] using h1
    simp only [runSC2, h1', Bool.false_eq_true, ↓reduceIte]
    have hpok := two_pok hsV htV hpV hqV he0 he1 hG ((insert q (insert p V)).card + 1)
    have hfuel := phase_fuel (t0 := t) (u0 := s) vw2 (two_dc hpV hqV) hG.fac
      (two_out htV hsV he0 he1 hG) ((insert q (insert p V)).card + 1) G [] Reach.base (by omega)
    rcases hph : phase V (insert q (insert p V)) ((insert q (insert p V)).card + 1) G [] with
      ⟨H, BS, out⟩
    rw [hph] at hpok
    dsimp only at hpok
    have hfuel' := fun H' BS' => hfuel H' BS'
    rw [hph] at hfuel'
    cases out with
    | stuck =>
      obtain ⟨hr, hm, hk'⟩ := hpok
      exact absurd hHP (phase_no_hp2 hst hsV htV hpV hqV hpq he0 he1 hfr hs hG h2 hr hm hk')
    | fuel => exact absurd rfl (hfuel' H BS)
    | merge c =>
      obtain ⟨hN, hc⟩ := s4C2 hsV htV hpV hqV he0 he1 hfr hG hpok (by simp) (by simp)
      rw [hN.ncomp hsV htV he0 he1, hG.ncomp hsV htV he0 he1] at hc
      exact ih _ hN (by show ncomp V (reduceOutC V _ H BS (POut.merge c)) ≤ n + 1; omega)
    | odd b =>
      obtain ⟨hN, hc⟩ := s4C2 hsV htV hpV hqV he0 he1 hfr hG hpok (by simp) (by simp)
      rw [hN.ncomp hsV htV he0 he1, hG.ncomp hsV htV he0 he1] at hc
      exact ih _ hN (by show ncomp V (reduceOutC V _ H BS (POut.odd b)) ≤ n + 1; omega)
    | twist b =>
      obtain ⟨hN, hc⟩ := s4C2 hsV htV hpV hqV he0 he1 hfr hG hpok (by simp) (by simp)
      rw [hN.ncomp hsV htV he0 he1, hG.ncomp hsV htV he0 he1] at hc
      exact ih _ hN (by show ncomp V (reduceOutC V _ H BS (POut.twist b)) ≤ n + 1; omega)

-- **Two phantoms, decided.** For solid `V`, `s ≠ t` with missing neighbours `q` (edge `e1`) and
-- `p` (edge `e0`), `p ≠ q`, `s`, `t` equal or at king distance at least 3, `hpSheffC2` answers
-- `true` exactly when `V` has a Hamiltonian `s`–`t` path.
--
theorem hpSheffC2_correct (hs : Solid V) :
    hpSheffC2 V s t p q e0 e1 = true ↔ ∃ H, IsFactor V (dST s t) H ∧ ncomp V H = 1 := by
  constructor
  · intro h
    unfold hpSheffC2 at h
    rcases hR : findFactor V (dST s t) with _ | R
    · rw [hR] at h; simp at h
    rw [hR] at h
    obtain ⟨G, hG, h1⟩ := runSC2_sound hsV htV hpV hqV he0 he1 hfr _ _
      (two_up hst hsV htV hpV hqV hpq he0 he1 (findFactor_some (dST_le s t) hR)) h
    exact two_down hst hsV htV hpV hqV hpq he0 he1 hG h1
  · intro hHP
    unfold hpSheffC2
    rcases hR : findFactor V (dST s t) with _ | R
    · obtain ⟨H, hH, _⟩ := hHP
      exact absurd ⟨H, hH⟩ (findFactor_none (dST_le s t) hR)
    have := ncomp_le_card (X := V) (F := insert e1 (insert e0 R))
    exact runSC2_complete hst hsV htV hpV hqV hpq he0 he1 hfr hs hHP _ _
      (two_up hst hsV htV hpV hqV hpq he0 he1 (findFactor_some (dST_le s t) hR)) (by omega)

end loop2

end HP

end SolidGridHam
