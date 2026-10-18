/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.HP.Sheffield.Minimal

/-!
# A checkable certificate for "stuck ⇒ minimal"

`Inv V H H' FP t0 u0` mentions the target `H'` only through `D H H'` in the column invariant and in
I5. `Cert V H FP t0 u0` drops `D`: every column it asks about ends at a pair square of its direction
(`ColEnds`) or runs out of `V` with its arcs all pointing one way (`ColOut`). A column running out
of `V` cannot carry `D` of its direction's sign (`D` grows along the arcs and is `0` off the cells),
so `Cert` gives `Inv` for every target (`cert_inv`), and with `stuck_minimal` a lower bound on the
number of pieces of every factor (`cert_count`). `Cert` mentions only `V`, `H`, `FP` and `t0`.
-/

namespace ULHC

namespace HP

open Finset Classical

-- The column from `q` in direction `a` stays in `V` for cells `0 … n`, all its arcs in direction
-- `a` point `o`, and the next square is not a cell.
--
def ColOut (V : Finset Pt) (H : Finset Edge) (q : Pt) (a : Side) (o : Bool) : Prop :=
  ∃ n, (∀ j ≤ n, IsCell V (cellJ q a j)) ∧ (∀ j ≤ n, outArc H (cellJ q a j) a = o) ∧
    ¬ IsCell V (cellJ q a (n + 1))

-- I5 without `D`.
--
def SideCert (V : Finset Pt) (H : Finset Edge) (FP : List FixedPr) : Prop :=
  ∀ p ∈ FP, ∀ ℓ, (ℓ = latA p.s ∨ ℓ = latB p.s) →
    (IsCell V (nb p.bot ℓ) → back (nb p.bot ℓ) p.s.opp ∈ H →
      lat1 (nb p.bot ℓ) p.s.opp ∉ H → lat2 (nb p.bot ℓ) p.s.opp ∉ H →
      outArc H (nb p.bot ℓ) p.s = false →
      ColEnds V H FP (nb p.bot ℓ) p.s.opp true ∨ ColOut V H (nb p.bot ℓ) p.s.opp true) ∧
    (IsCell V (nb p.top ℓ) → back (nb p.top ℓ) p.s ∈ H →
      lat1 (nb p.top ℓ) p.s ∉ H → lat2 (nb p.top ℓ) p.s ∉ H →
      outArc H (nb p.top ℓ) p.s.opp = true →
      ColEnds V H FP (nb p.top ℓ) p.s false ∨ ColOut V H (nb p.top ℓ) p.s false)

-- The certificate: `Inv` with the column invariant and I5 stated without `H'`.
--
structure Cert (V : Finset Pt) (H : Finset Edge) (FP : List FixedPr) (t0 u0 : Pt) : Prop where
  f2 : ∀ q, IsCell V q → Alt H q → CutSq H q → ∃ i ∈ FP, q = i.top ∨ q = i.bot
  f4 : ∀ i ∈ FP, PairOK H i
  tri : ∀ f, IsCell V f → Three H f → TriOK V H t0 u0 f
  out : ∀ e ∈ H, (e.p ∉ V → e.q = t0 ∨ e.q = u0) ∧ (e.q ∉ V → e.p = t0 ∨ e.p = u0)
  l4 : ∀ q s, IsCell V q → Conn H (back1 q s) (back2 q s) → Conn H (front1 q s) (front2 q s) →
    ¬ Conn H (back1 q s) (front1 q s) → back q s ∈ H ∨ front q s ∈ H
  palt : ∀ i ∈ FP, Alt H i.top ∧ Alt H i.bot
  pdark : ∀ i ∈ FP, sideEdge i.bot i.s ∈ H
  pcorn : ∀ i ∈ FP, IsCorner i.tx i.top ∧ IsCorner i.ty i.top ∧ IsCorner i.bx i.bot ∧
    IsCorner i.by' i.bot
  pdisj : ∀ i ∈ FP, ∀ j ∈ FP, (i.top = j.top ∨ i.top = j.bot ∨ i.bot = j.top ∨ i.bot = j.bot) →
    i = j
  col : ∀ q s, IsCell V q → CriticalIn H q s → back q s ∈ H →
    (∀ i ∈ FP, q ≠ i.top ∧ q ≠ i.bot) →
    ColEnds V H FP q s (outArc H q s) ∨ ColOut V H q s (outArc H q s)
  side : SideCert V H FP

section cert

variable {V W : Finset Pt} {d : Pt → ℕ} {H H' : Finset Edge} {FP : List FixedPr} {t0 u0 : Pt}

-- A column running out of `V` carries no `D` of its direction's sign.
--
lemma not_colOut (hH : IsFactor W d H) (hH' : IsFactor W d H') (hsol : SolidFor V H H')
    {q : Pt} {a : Side} {o : Bool} (hpos : 0 < sgnD o (D H H' q)) : ¬ ColOut V H q a o := by
  rintro ⟨n, -, harc, hout⟩
  have key : ∀ j ≤ n + 1, 0 < sgnD o (D H H' (cellJ q a j)) := by
    intro j
    induction j with
    | zero => intro _; rw [cellJ_zero]; exact hpos
    | succ j ih =>
      intro hj
      have h := sgnD_step hH hH' (harc j (by omega))
      rw [nb_cellJ] at h
      exact lt_of_lt_of_le (ih (by omega)) h
  have := key (n + 1) le_rfl
  rw [hsol _ hout] at this
  simp [sgnD] at this

-- **The certificate gives the invariant for every target.**
--
theorem cert_inv (hH : IsFactor W d H) (hH' : IsFactor W d H') (hsol : SolidFor V H H')
    (hc : Cert V H FP t0 u0) : Inv V H H' FP t0 u0 where
  f2 := hc.f2
  f4 := hc.f4
  tri := hc.tri
  out := hc.out
  l4 := hc.l4
  palt := hc.palt
  pdark := hc.pdark
  pcorn := hc.pcorn
  pdisj := hc.pdisj
  col := fun q s hq hcr hb hnp hpos =>
    (hc.col q s hq hcr hb hnp).resolve_right (not_colOut hH hH' hsol hpos)
  side := fun p hp ℓ hℓ =>
    ⟨fun _ hcell hb hl1 hl2 harc hpos =>
      ((hc.side p hp ℓ hℓ).1 hcell hb hl1 hl2 harc).resolve_right
        (not_colOut hH hH' hsol (o := true) (by simpa [sgnD] using hpos)),
     fun _ hcell hb hl1 hl2 harc hneg =>
      ((hc.side p hp ℓ hℓ).2 hcell hb hl1 hl2 harc).resolve_right
        (not_colOut hH hH' hsol (o := false) (by simp [sgnD]; omega))⟩

-- **The certified count.** A certified state has at most `|FP|` more pieces than any factor `H'`
-- that agrees with it off `V`.
--
theorem cert_count_gen (hH : IsFactor W d H) (hH' : IsFactor W d H')
    (hac : ∀ G, IsFactor W d G → ClimbAcyc V G) (hVW : V ⊆ W)
    (hdc : ∀ q, IsCell V q → ∀ z, IsCorner z q → d z = 2)
    (hFH : ∀ e ∈ symmDiff H H', e.p ∈ V ∧ e.q ∈ V) (hsol : SolidFor V H H')
    (hc : Cert V H FP t0 u0) :
    ncomp W H ≤ ncomp W H' + FP.length :=
  stuck_minimal hH' hac hVW hdc _ H FP rfl hH hFH hsol (cert_inv hH hH' hsol hc)

theorem cert_count (hH : IsFactor W d H) (hH' : IsFactor W d H') (hs : Solid V) (hVW : V ⊆ W)
    (hdc : ∀ q, IsCell V q → ∀ z, IsCorner z q → d z = 2)
    (hFH : ∀ e ∈ symmDiff H H', e.p ∈ V ∧ e.q ∈ V) (hc : Cert V H FP t0 u0) :
    ncomp W H ≤ ncomp W H' + FP.length := by
  refine cert_count_gen hH hH' (fun G hG => ?_) hVW hdc hFH
    (fun _ hq => D_eq_zero_of_not_cellW hH hH' hFH hs hq) hc
  obtain ⟨τ, hτ⟩ := height_exists (H := G) hs (fun p hp => by
    have hc := hp.2.2.2
    rw [hG.2 p (hVW hc.1)]
    exact hdc p hc p (Or.inl rfl))
  exact acyc_of_height hτ

end cert

end HP

end ULHC
