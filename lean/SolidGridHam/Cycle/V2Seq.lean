/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import SolidGridHam.Cycle.Dual

/-!
# Theorem A2: sequences whose strips begin on the created boundary

The thesis's Definition 6.6: after an even strip, the next strip begins on the boundary that
the even strip created. Here the boundary is the chain of the end cell (`chainCells`).

**Theorem A2.** In a solid Hamiltonian grid graph, every 2-factor with at least two
components has such a sequence. The proof is Theorem A's, with the walk run on the chain's
border (`chain_border`) and the Type III ending supplied by Lemma 5.7.
-/

namespace SolidGridHam

open Finset Classical

-- The last cell of a strip.
--
def endCell (σ : StripSpec) : Pt := cellJ σ.c σ.s (σ.n - 1)

-- `c` lies on the chain of the anchor, if there is one.
--
def OnChain (V : Finset Pt) (F : Finset Edge) : Option Pt → Pt → Prop
  | none, _ => True
  | some u, c => c ∈ chainCells V F u

-- Valid sequences in which each strip begins on the chain of the anchor; the anchor of a
-- later strip is the end cell of the strip before it.
--
def ValidSeqA (V : Finset Pt) : Option Pt → Finset Edge → List StripSpec → Prop
  | _, _, [] => False
  | a, F, [σ] => ValidStrip V F σ ∧ σ.n % 2 = 1 ∧ OnChain V F a σ.c
  | a, F, σ :: τ :: L => ValidStrip V F σ ∧ σ.n % 2 = 0 ∧ NoTypeIII V F ∧ OnChain V F a σ.c ∧
      ValidSeqA V (some (endCell σ)) (applyS F σ) (τ :: L)

lemma ValidSeqA.toValidSeq {V : Finset Pt} :
    ∀ (L : List StripSpec) (a : Option Pt) (F : Finset Edge), ValidSeqA V a F L → ValidSeq V F L
  | [], _, _, h => h.elim
  | [_], _, _, h => ⟨h.1, h.2.1⟩
  | _ :: τ :: L, _, _, h => ⟨h.1, h.2.1, h.2.2.1, ValidSeqA.toValidSeq (τ :: L) _ _ h.2.2.2.2⟩

-- A Type III cell is an odd strip of length one starting there.
--
lemma typeIII_strip_at {V : Finset Pt} {F : Finset Edge} {d : Pt} (hd : IsCell V d)
    (h : ¬ NotTypeIII V F d) : ∃ σ : StripSpec, σ.c = d ∧ ValidStrip V F σ ∧ σ.n % 2 = 1 := by
  simp only [NotTypeIII, not_forall] at h
  obtain ⟨s, hb, hf, hl1, hl2, hn⟩ := h
  refine ⟨⟨d, s, 1⟩, rfl, ⟨le_rfl, ⟨hb, fun j hj => ?_, fun j hj => ?_⟩, fun j hj => ?_, hn⟩, rfl⟩
  · obtain rfl : j = 0 := by simp only at hj; omega
    rw [cellJ_zero]; simp [hl1, hl2]
  · obtain rfl : j = 0 := by simp only at hj; omega
    rw [cellJ_zero]; simp [hf]
  · obtain rfl : j = 0 := by simp only at hj; omega
    rw [cellJ_zero]; exact hd

section thmA2

variable {V : Finset Pt} {H : Finset Edge}
  (hs : Solid V) (hH : Deg2 V H) (hHam : ncomp V H = 1)
include hs hH hHam

-- One strip from the walk on any border with a cut: it begins on a cut side.
--
lemma one_strip_P {F : Finset Edge} (hF : Deg2 V F) (hT : NoTypeIII V F) {P : Finset Pt}
    (hB : Border V F P) {x y : Pt} (hx : x ∈ V) (hy : y ∈ V) (hxP : x ∈ P) (hyP : y ∉ P) :
    ∃ σ : StripSpec, ValidStrip V F σ ∧ 2 ≤ σ.n ∧ mu V (applyS F σ) H + 2 * σ.n = mu V F H ∧
      ∃ si, Cut P (sideEdge σ.c si) := by
  obtain ⟨e, heH, hcut⟩ := exists_cut_edge (conn_of_ncomp_one hHam hx hy) hxP hyP
  have heF : e ∉ F := fun h => hB.not_cut h hcut
  obtain ⟨sh, sl, h1, h2', h3, h4, h5, h6⟩ := edge_cells F e
  have hjump := D_jump hF.factor hH.factor e
  have hw : wD F H e = if up F e then 2 else -2 := by
    unfold wD wb; simp [heF, heH]
  rw [hw] at hjump
  have key : ∃ o v s0, Cut P (sideEdge v s0) ∧ outArc F v s0 = !o ∧
      (if o then D F H v = D F H (nb v s0) + 2 else D F H v = D F H (nb v s0) - 2) ∧
      Good o (D F H v) := by
    obtain ⟨a, b, sa, sb, ha1, ha2, ha3, hb1, hb2, hb3, hD⟩ :
        ∃ a b sa sb, sideEdge a sa = e ∧ nb a sa = b ∧ outArc F a sa = true ∧
          sideEdge b sb = e ∧ nb b sb = a ∧ outArc F b sb = false ∧
          D F H b = D F H a + 2 := by
      cases hu : up F e
      · refine ⟨e.hi, e.lo, sh, sl, h1, h2', by rw [h3, hu]; rfl, h4, h5, by rw [h6, hu], ?_⟩
        rw [hu] at hjump; simp at hjump; omega
      · refine ⟨e.lo, e.hi, sl, sh, h4, h5, by rw [h6, hu], h1, h2', by rw [h3, hu]; rfl, ?_⟩
        rw [hu] at hjump; simp at hjump; omega
    by_cases hpos : 0 ≤ D F H a
    · refine ⟨true, b, sb, by rw [hb1]; exact hcut, by rw [hb3]; rfl, ?_, ?_⟩
      · simp only [ite_true]; rw [hb2]; exact hD
      · unfold Good; simp; omega
    · obtain ⟨m, hm⟩ := D_even F H a
      refine ⟨false, a, sa, by rw [ha1]; exact hcut, by rw [ha3]; rfl, ?_, ?_⟩
      · simp only [Bool.false_eq_true, ite_false]; rw [ha2]; omega
      · unfold Good; simp; omega
  obtain ⟨o, v, s0, hc0, hi0, hj0, hg0⟩ := key
  obtain ⟨w, _, hgw, hst⟩ := phase1 hF hH hs hB hT o v s0 hc0 hi0 hj0 hg0
  have hcw : ∃ si, Cut P (sideEdge w si) := by
    obtain ⟨_, _, _, _, _, ⟨si, _, hc, _⟩, _, _⟩ := hst
    exact ⟨si, hc⟩
  obtain ⟨s, n, hn, hpat, hcell, hgood, hp, hsep⟩ := phase2 hF hH hs hB hgw hst
  refine ⟨⟨w, s, n⟩, ⟨show 1 ≤ n by omega, hpat, hcell, hsep⟩, hn, ?_, hcw⟩
  exact strip_mu hp n hpat hcell hgood

-- What an anchor provides: its chain has an inter side, and carries a Type III cell
-- whenever the factor has one.
--
def AnchorOK (V : Finset Pt) (F : Finset Edge) : Option Pt → Prop
  | none => True
  | some u => (∃ e, e ∈ EB V F u) ∧
      (¬ NoTypeIII V F → ∃ d ∈ chainCells V F u, ¬ NotTypeIII V F d)

omit hs hH hHam in
lemma notTypeIII_of_no {F : Finset Edge} (h : ¬ NoTypeIII V F) :
    ∃ d, IsCell V d ∧ ¬ NotTypeIII V F d := by
  unfold NoTypeIII at h
  push Not at h
  obtain ⟨c, hc, s, hb, hf, hl1, hl2, hn⟩ := h
  exact ⟨c, hc, fun h' => hn (h' s hb hf hl1 hl2)⟩

theorem theoremA2_aux : ∀ m (F : Finset Edge) (a : Option Pt), mu V F H = m → Deg2 V F →
    2 ≤ ncomp V F → AnchorOK V F a → ∃ L : List StripSpec, ValidSeqA V a F L := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro F a hm hF h2 ha
  obtain ⟨x, hx, y, hy, hxy⟩ := exists_not_conn h2
  have hconn : ∀ z ∈ V, Conn (GE V) x z := fun z hz =>
    (conn_of_ncomp_one hHam hx hz).mono (fun e he => mem_GE.2 (hH.1 e he))
  by_cases hT : NoTypeIII V F
  · -- The border to walk on: a class, or the anchor's chain.
    obtain ⟨P, hB, x', hx', y', hy', hxP, hyP, hon⟩ : ∃ P, Border V F P ∧ ∃ x' ∈ V, ∃ y' ∈ V,
        x' ∈ P ∧ y' ∉ P ∧ ∀ c si, IsCell V c → Cut P (sideEdge c si) → OnChain V F a c := by
      cases a with
      | none =>
        refine ⟨cls V F x, ⟨Finset.filter_subset _ _, fun u hu w hw => closed_cls hF.1 x u hu w hw⟩,
          x, hx, y, hy, mem_cls_self hx, ?_, fun _ _ _ _ => trivial⟩
        simp only [cls, Finset.mem_filter, not_and]; exact fun _ => hxy
      | some u =>
        obtain ⟨⟨e, he⟩, _⟩ := ha
        obtain ⟨P, hB, hcut⟩ := chain_border hs hF hT x hconn u
        have heE : IsEdge V e := by
          simp only [EB, Finset.mem_filter] at he; exact mem_GE.1 he.1
        have hc := (hcut e heE).2 he
        unfold Cut at hc
        refine ⟨P, hB, ?_⟩
        by_cases hp : e.p ∈ P
        · exact ⟨e.p, heE.1, e.q, heE.2, hp, hc.1 hp, fun c si hcell hct =>
            on_chain_of_side hcell (side_mem_cellE c si) ((hcut _ (isEdge_side hcell si)).1 hct)⟩
        · exact ⟨e.q, heE.2, e.p, heE.1, by tauto, hp, fun c si hcell hct =>
            on_chain_of_side hcell (side_mem_cellE c si) ((hcut _ (isEdge_side hcell si)).1 hct)⟩
    obtain ⟨σ, hv, hn2, hmu, si, hcut⟩ := one_strip_P hs hH hHam hF hT hB hx' hy' hxP hyP
    have hc0 : IsCell V σ.c := by
      have := hv.2.2.1 0 (by omega); rwa [cellJ_zero] at this
    have hσon := hon σ.c si hc0 hcut
    rcases Nat.mod_two_eq_zero_or_one σ.n with hev | hodd
    · -- Even: recurse with the end cell as anchor.
      obtain ⟨_, hpat, hcell, hsep⟩ := hv
      obtain ⟨k, hk⟩ : ∃ k, σ.n = k + 2 := ⟨σ.n - 2, by omega⟩
      have hF' : Deg2 V (applyS F σ) := deg2_flipCol _ F hF hpat hcell
      have hcnt := even_strip_count hF hT ⟨by omega, hpat, hcell, hsep⟩ hev
      have hend : endCell σ = cellJ σ.c σ.s (k + 1) := by
        unfold endCell; rw [hk]; rfl
      have hcell' : ∀ j ≤ k + 1, IsCell V (cellJ σ.c σ.s j) := fun j hj => hcell j (by omega)
      rw [hk] at hpat
      have hk2 : k % 2 = 0 := by omega
      have hA : AnchorOK V (applyS F σ) (some (endCell σ)) := by
        unfold applyS
        rw [hk, hend]
        refine ⟨⟨_, (end_inter hF hT hk2 hcell' hpat hsep).2⟩, fun hT' => ?_⟩
        obtain ⟨d, hd, hd3⟩ := notTypeIII_of_no hT'
        exact lemma57 hF hT hk2 hcell' hpat hsep hs x hconn hd hd3
      obtain ⟨L', hL'⟩ := ih (mu V (applyS F σ) H) (by omega) (applyS F σ) _ rfl hF'
        (by omega) hA
      rcases L' with _ | ⟨τ, L'⟩
      · exact hL'.elim
      · exact ⟨σ :: τ :: L', ⟨by omega, by rw [hk]; exact hpat, hcell, hsep⟩, hev, hT, hσon, hL'⟩
    · exact ⟨[σ], hv, hodd, hσon⟩
  · -- A Type III cell, on the anchor's chain if there is an anchor.
    cases a with
    | none =>
      obtain ⟨d, hd, hd3⟩ := notTypeIII_of_no hT
      obtain ⟨σ, _, hv, hodd⟩ := typeIII_strip_at hd hd3
      exact ⟨[σ], hv, hodd, trivial⟩
    | some u =>
      obtain ⟨d, hdc, hd3⟩ := ha.2 hT
      have hd : IsCell V d := by
        simp only [chainCells, Finset.mem_filter] at hdc; exact mem_cells.1 hdc.1
      obtain ⟨σ, hσc, hv, hodd⟩ := typeIII_strip_at hd hd3
      exact ⟨[σ], hv, hodd, by show σ.c ∈ chainCells V F u; rw [hσc]; exact hdc⟩

/-- **Theorem A2** (thesis Lemma 6.7 with Definition 6.6). In a solid grid graph with a
Hamiltonian cycle, every 2-factor with at least two components has a valid sequence in which
each strip after the first begins on the chain created by the strip before it; flipping it
leaves one component fewer. -/
theorem theoremA2 (F : Finset Edge) (hF : Deg2 V F) (h2 : 2 ≤ ncomp V F) :
    ∃ L : List StripSpec, ValidSeqA V none F L ∧ ncomp V (applySeq F L) + 1 = ncomp V F := by
  obtain ⟨L, hL⟩ := theoremA2_aux hs hH hHam _ F none rfl hF h2 trivial
  exact ⟨L, hL, seq_count L F hF (ValidSeqA.toValidSeq L none F hL)⟩

end thmA2

end SolidGridHam
