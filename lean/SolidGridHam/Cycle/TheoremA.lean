/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import SolidGridHam.Cycle.Phase2

/-!
# Theorem A: alternating strip sequences exist (thesis Lemmas 6.6, 6.7, Theorem 6.1)

A strip is given by its first cell, direction and length. A sequence is valid when
(thesis Definition 6.6, without the "boundary created by" condition, see BLUEPRINT §5):
* the last strip is odd;
* every earlier strip is even, and is flipped when the factor has no Type III cells.

Flipping a valid sequence lowers the number of components by one. If the graph is solid and
Hamiltonian, every 2-factor with at least two components has a valid sequence.
-/

namespace SolidGridHam

open Finset Classical

structure StripSpec where
  c : Pt
  s : Side
  n : ℕ

def applyS (F : Finset Edge) (σ : StripSpec) : Finset Edge := flipCol F σ.c σ.s σ.n

def applySeq (F : Finset Edge) : List StripSpec → Finset Edge
  | [] => F
  | σ :: L => applySeq (applyS F σ) L

def ValidStrip (V : Finset Pt) (F : Finset Edge) (σ : StripSpec) : Prop :=
  1 ≤ σ.n ∧ StripPat F σ.c σ.s σ.n ∧ (∀ j < σ.n, IsCell V (cellJ σ.c σ.s j)) ∧
    ¬ Conn F (back1 σ.c σ.s) (front1 σ.c σ.s)

def ValidSeq (V : Finset Pt) : Finset Edge → List StripSpec → Prop
  | _, [] => False
  | F, [σ] => ValidStrip V F σ ∧ σ.n % 2 = 1
  | F, σ :: τ :: L => ValidStrip V F σ ∧ σ.n % 2 = 0 ∧ NoTypeIII V F ∧
      ValidSeq V (applyS F σ) (τ :: L)

/-! ## Flipping keeps degrees -/

lemma deg2_flipCol {V : Finset Pt} {c : Pt} {s : Side} :
    ∀ n (F : Finset Edge), Deg2 V F → StripPat F c s n → (∀ j < n, IsCell V (cellJ c s j)) →
      Deg2 V (flipCol F c s n) := by
  intro n
  induction n with
  | zero => intro F hF _ _; exact hF
  | succ n ih =>
    intro F hF hpat hcell
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
    have hF' : Deg2 V (SolidGridHam.flip F (cellJ c s n)) := by
      rcases Nat.mod_two_eq_zero_or_one n with h | h
      · exact hF.flip (mkBF _ s) hce (mkBF_cellE _ s) (mB.2 h) (mF.2 h)
          (fun h' => by have := mL1.1 h'; omega) (fun h' => by have := mL2.1 h'; omega)
      · exact hF.flip (mkLat _ s) hce (mkLat_cellE _ s) (mL1.2 h) (mL2.2 h)
          (fun h' => by have := mB.1 h'; omega) (fun h' => by have := mF.1 h'; omega)
    rcases n with _ | n
    · simpa [flipCol] using hF'
    · exact ih _ hF' (pat_flip_end ⟨hb, hl, hf⟩) (fun j hj => hcell j (by omega))

/-! ## An even strip keeps the count when there are no Type III cells -/

theorem even_strip_count {V : Finset Pt} {F : Finset Edge} {σ : StripSpec} (hF : Deg2 V F)
    (hT : NoTypeIII V F) (hv : ValidStrip V F σ) (hev : σ.n % 2 = 0) :
    ncomp V (applyS F σ) = ncomp V F := by
  obtain ⟨hn, hpat, hcell, hsep⟩ := hv
  obtain ⟨k, hk⟩ : ∃ k, σ.n = k + 2 := ⟨σ.n - 2, by omega⟩
  have hsame : Conn F (back1 (cellJ σ.c σ.s (k + 1)) σ.s) (back2 (cellJ σ.c σ.s (k + 1)) σ.s) := by
    rw [hk] at hpat hcell
    have hce := hcell (k + 1) (by omega)
    obtain ⟨_, hl, hf⟩ := hpat
    have ha : Alt F (cellJ σ.c σ.s (k + 1)) := by
      have l1 := (hl (k + 1) (by omega)).1.2 (by omega)
      have l2 := (hl (k + 1) (by omega)).2.2 (by omega)
      have fF : front (cellJ σ.c σ.s (k + 1)) σ.s ∉ F := by
        intro h; have := (hf (k + 1) (by omega)).1 h; omega
      have bF : back (cellJ σ.c σ.s (k + 1)) σ.s ∉ F := by
        rw [back_cellJ_succ]; intro h; have := (hf k (by omega)).1 h; omega
      rw [lat1_eq] at l1
      rw [lat2_eq] at l2
      simp only [back, front] at fF bF
      generalize cellJ σ.c σ.s (k + 1) = r at *
      obtain ⟨x, y⟩ := r
      cases hs : σ.s <;> rw [hs] at l1 l2 fF bF <;>
        simp only [latA, latB, sideEdge, Side.opp] at l1 l2 fF bF <;> unfold Alt <;> tauto
    obtain ⟨k1, k2, k3⟩ := alt_corners_conn hT hce ha
    generalize cellJ σ.c σ.s (k + 1) = r at *
    obtain ⟨x, y⟩ := r
    cases σ.s <;> simp only [back1, back2] at * <;>
      first
      | exact k1
      | exact k2.symm.trans k3
      | exact k1.symm.trans k3
      | exact k2
  unfold applyS
  rw [hk] at hpat hcell ⊢
  exact strip_even k (by omega) F hF (fun j hj => hcell j (by omega)) hpat hsep hsame

/-! ## Lemma 6.6: a valid sequence lowers the count by one -/

theorem seq_count {V : Finset Pt} :
    ∀ (L : List StripSpec) (F : Finset Edge), Deg2 V F → ValidSeq V F L →
      ncomp V (applySeq F L) + 1 = ncomp V F := by
  intro L
  induction L with
  | nil => intro F _ h; exact h.elim
  | cons σ L ih =>
    intro F hF hv
    rcases L with _ | ⟨τ, L⟩
    · obtain ⟨⟨hn, hpat, hcell, hsep⟩, hodd⟩ := hv
      obtain ⟨k, hk⟩ : ∃ k, σ.n = k + 1 := ⟨σ.n - 1, by omega⟩
      simp only [applySeq, applyS]
      rw [hk] at hpat hcell ⊢
      exact (strip_odd k (by omega) F hF (fun j hj => hcell j (by omega)) hpat hsep).1
    · obtain ⟨⟨hn, hpat, hcell, hsep⟩, hev, hT, hrest⟩ := hv
      obtain ⟨k, hk⟩ : ∃ k, σ.n = k + 2 := ⟨σ.n - 2, by omega⟩
      have hF' : Deg2 V (applyS F σ) := deg2_flipCol _ F hF hpat hcell
      have := ih (applyS F σ) hF' hrest
      simp only [applySeq] at this ⊢
      rw [this]
      exact even_strip_count hF hT ⟨hn, hpat, hcell, hsep⟩ hev

/-! ## Theorem A -/

lemma conn_of_ncomp_one {V : Finset Pt} {H : Finset Edge} (h1 : ncomp V H = 1) {x y : Pt}
    (hx : x ∈ V) (hy : y ∈ V) : Conn H x y := by
  unfold ncomp at h1
  obtain ⟨S, hS⟩ := Finset.card_eq_one.1 h1
  have ex : cls V H x ∈ V.image (cls V H) := Finset.mem_image_of_mem _ hx
  have ey : cls V H y ∈ V.image (cls V H) := Finset.mem_image_of_mem _ hy
  rw [hS, Finset.mem_singleton] at ex ey
  have : y ∈ cls V H x := by rw [ex, ← ey]; exact mem_cls_self hy
  simp only [cls, Finset.mem_filter] at this
  exact this.2

lemma exists_not_conn {V : Finset Pt} {F : Finset Edge} (h2 : 2 ≤ ncomp V F) :
    ∃ x ∈ V, ∃ y ∈ V, ¬ Conn F x y := by
  by_contra hall
  push Not at hall
  have : (V.image (cls V F)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro A hA B hB
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hA
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hB
    exact cls_eq_of_conn (hall x hx y hy)
  unfold ncomp at h2
  omega

lemma exists_cut_edge {H : Finset Edge} {P : Finset Pt} {x y : Pt} (h : Conn H x y)
    (hx : x ∈ P) (hy : y ∉ P) : ∃ e ∈ H, Cut P e := by
  induction h with
  | refl => exact absurd hx hy
  | @tail b c _ hbc ih =>
    by_cases hb : b ∈ P
    · obtain ⟨e, he, h⟩ := hbc
      refine ⟨e, he, ?_⟩
      unfold Cut
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> tauto
    · exact ih hb

-- Every edge is a side of its two cells, with arcs read from each side.
--
lemma edge_cells (F : Finset Edge) (e : Edge) :
    ∃ sh sl, sideEdge e.hi sh = e ∧ nb e.hi sh = e.lo ∧ outArc F e.hi sh = !up F e ∧
      sideEdge e.lo sl = e ∧ nb e.lo sl = e.hi ∧ outArc F e.lo sl = up F e := by
  obtain ⟨d, x, y⟩ := e
  cases d
  · refine ⟨.b, .t, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [sideEdge, nb, outArc, bot, top, Edge.lo, Edge.hi]
  · refine ⟨.l, .r, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [sideEdge, nb, outArc, lft, rgt, Edge.lo, Edge.hi]

-- A Type III cell is an odd strip of length one.
--
lemma typeIII_strip {V : Finset Pt} {F : Finset Edge} (h : ¬ NoTypeIII V F) :
    ∃ σ : StripSpec, ValidStrip V F σ ∧ σ.n % 2 = 1 := by
  unfold NoTypeIII at h
  push Not at h
  obtain ⟨c, hc, s, hb, hf, hl1, hl2, hn⟩ := h
  refine ⟨⟨c, s, 1⟩, ⟨le_rfl, ⟨hb, fun j hj => ?_, fun j hj => ?_⟩, fun j hj => ?_, hn⟩, rfl⟩
  · obtain rfl : j = 0 := by simp only at hj; omega
    rw [cellJ_zero]; simp [hl1, hl2]
  · obtain rfl : j = 0 := by simp only at hj; omega
    rw [cellJ_zero]; simp [hf]
  · obtain rfl : j = 0 := by simp only at hj; omega
    rw [cellJ_zero]; exact hc

section thmA

variable {V : Finset Pt} {H : Finset Edge}
  (hs : Solid V) (hH : Deg2 V H) (hHam : ncomp V H = 1)
include hs hH hHam

-- One strip from the walk: odd, or even with `μ` lowered.
--
lemma one_strip {F : Finset Edge} (hF : Deg2 V F) (hT : NoTypeIII V F) (h2 : 2 ≤ ncomp V F) :
    ∃ σ : StripSpec, ValidStrip V F σ ∧ 2 ≤ σ.n ∧ mu V (applyS F σ) H + 2 * σ.n = mu V F H := by
  obtain ⟨x, hx, y, hy, hxy⟩ := exists_not_conn h2
  set P := cls V F x
  have hB : Border V F P := ⟨Finset.filter_subset _ _, fun u hu w hw => closed_cls hF.1 x u hu w hw⟩
  have hxP : x ∈ P := mem_cls_self hx
  have hyP : y ∉ P := by simp only [P, cls, Finset.mem_filter, not_and]; exact fun _ => hxy
  obtain ⟨e, heH, hcut⟩ := exists_cut_edge (conn_of_ncomp_one hHam hx hy) hxP hyP
  have heF : e ∉ F := fun h => hB.not_cut h hcut
  obtain ⟨sh, sl, h1, h2', h3, h4, h5, h6⟩ := edge_cells F e
  have hjump := D_jump hF.factor hH.factor e
  have hw : wD F H e = if up F e then 2 else -2 := by
    unfold wD wb; simp [heF, heH]
  rw [hw] at hjump
  -- Choose the orientation from the sign of `D` at the arc's tail.
  have key : ∃ o v s0, Cut P (sideEdge v s0) ∧ outArc F v s0 = !o ∧
      (if o then D F H v = D F H (nb v s0) + 2 else D F H v = D F H (nb v s0) - 2) ∧
      Good o (D F H v) := by
    -- `a` is the tail of the arc across `e`, `b` its head; `D b = D a + 2`.
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
  obtain ⟨s, n, hn, hpat, hcell, hgood, hp, hsep⟩ := phase2 hF hH hs hB hgw hst
  refine ⟨⟨w, s, n⟩, ⟨show 1 ≤ n by omega, hpat, hcell, hsep⟩, hn, ?_⟩
  exact strip_mu hp n hpat hcell hgood

end thmA

/-- **Theorem A** (thesis Lemma 6.7 with Lemma 6.6). In a solid grid graph with a
Hamiltonian cycle `H`, every 2-factor `F` with at least two components has a valid
alternating strip sequence, and flipping it leaves one component fewer. -/
theorem theoremA {V : Finset Pt} {H : Finset Edge} (hs : Solid V) (hH : Deg2 V H)
    (hHam : ncomp V H = 1) (F : Finset Edge) (hF : Deg2 V F) (h2 : 2 ≤ ncomp V F) :
    ∃ L : List StripSpec, ValidSeq V F L ∧ ncomp V (applySeq F L) + 1 = ncomp V F := by
  suffices h : ∀ m (F : Finset Edge), mu V F H = m → Deg2 V F → 2 ≤ ncomp V F →
      ∃ L : List StripSpec, ValidSeq V F L by
    obtain ⟨L, hL⟩ := h _ F rfl hF h2
    exact ⟨L, hL, seq_count L F hF hL⟩
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro F hm hF h2
  by_cases hT : NoTypeIII V F
  · obtain ⟨σ, hv, hn, hmu⟩ := one_strip hs hH hHam hF hT h2
    rcases Nat.mod_two_eq_zero_or_one σ.n with hev | hodd
    · have hF' := deg2_flipCol σ.n F hF hv.2.1 hv.2.2.1
      have hc := even_strip_count hF hT hv hev
      obtain ⟨L', hL'⟩ := ih (mu V (applyS F σ) H) (by omega) (applyS F σ) rfl hF' (by omega)
      rcases L' with _ | ⟨τ, L'⟩
      · exact hL'.elim
      · exact ⟨σ :: τ :: L', hv, hev, hT, hL'⟩
    · exact ⟨[σ], hv, hodd⟩
  · obtain ⟨σ, hv, hodd⟩ := typeIII_strip hT
    exact ⟨[σ], hv, hodd⟩

/-! ## Theorem 6.1: repeated sequences reach a Hamiltonian cycle -/

-- A chain of sequences, each valid for the factor reached so far.
--
def ValidChain (V : Finset Pt) : Finset Edge → List (List StripSpec) → Prop
  | _, [] => True
  | F, L :: Ls => ValidSeq V F L ∧ ValidChain V (applySeq F L) Ls

def applyChain (F : Finset Edge) : List (List StripSpec) → Finset Edge
  | [] => F
  | L :: Ls => applyChain (applySeq F L) Ls

lemma deg2_applySeq {V : Finset Pt} :
    ∀ (L : List StripSpec) (F : Finset Edge), Deg2 V F → ValidSeq V F L → Deg2 V (applySeq F L) := by
  intro L
  induction L with
  | nil => intro F hF _; exact hF
  | cons σ L ih =>
    intro F hF hv
    rcases L with _ | ⟨τ, L⟩
    · exact deg2_flipCol σ.n F hF hv.1.2.1 hv.1.2.2.1
    · exact ih _ (deg2_flipCol σ.n F hF hv.1.2.1 hv.1.2.2.1) hv.2.2.2

/-- **Theorem 6.1.** In a solid grid graph with a Hamiltonian cycle, every 2-factor is turned
into a single cycle by `ncomp − 1` alternating strip sequences, each valid when applied. -/
theorem theorem61 {V : Finset Pt} {H : Finset Edge} (hs : Solid V) (hH : Deg2 V H)
    (hHam : ncomp V H = 1) :
    ∀ (F : Finset Edge), Deg2 V F → 1 ≤ ncomp V F →
      ∃ Ls : List (List StripSpec), ValidChain V F Ls ∧ Ls.length + 1 = ncomp V F ∧
        ncomp V (applyChain F Ls) = 1 := by
  suffices h : ∀ k (F : Finset Edge), ncomp V F = k + 1 → Deg2 V F →
      ∃ Ls : List (List StripSpec), ValidChain V F Ls ∧ Ls.length = k ∧
        ncomp V (applyChain F Ls) = 1 by
    intro F hF h1
    obtain ⟨Ls, h1', h2', h3'⟩ := h (ncomp V F - 1) F (by omega) hF
    exact ⟨Ls, h1', by omega, h3'⟩
  intro k
  induction k with
  | zero => intro F hk _; exact ⟨[], trivial, rfl, hk⟩
  | succ k ih =>
    intro F hk hF
    obtain ⟨L, hL, hc⟩ := theoremA hs hH hHam F hF (by omega)
    obtain ⟨Ls, h1, h2, h3⟩ := ih (applySeq F L) (by omega) (deg2_applySeq L F hF hL)
    exact ⟨L :: Ls, ⟨hL, h1⟩, by simp [h2], h3⟩

end SolidGridHam
