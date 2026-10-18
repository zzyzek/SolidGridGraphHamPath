/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import SolidGridHam.Cycle.ChainLinks
public import SolidGridHam.Cycle.MinPath

@[expose] public section

/-!
# The link graph

A computable graph whose minimum paths are exactly the minimum paths with chain links
anywhere (`CRPathCA`).

* Nodes `⟨σ, pos⟩`: a candidate strip `σ` with a position `pos ∈ {1, 2, 3}`. Position `1` is
  the first strip of a path, `2` the second, `3` the third or later.
* Candidate strips `cand V G`: the strips of `G` and the strips of `G ⊕ u` for every cell `u`.
  The first strip of a path is a strip of `G`, a link target from `b` is a strip of
  `G ⊕ endCell b`.
* Sources `gsrc`: position `1` and proper in `G` (`validB`). Middle nodes `gmid`: even strips.
  Targets `gtgt`: odd strips. Edges `gedge x y`: `y.pos = min (x.pos + 1) 3`, a link
  `CR2 V G x.σ y.σ` (`cr2B`), and `ChainOK x.σ y.σ` (`chainOKB`). Positions only count up to
  `3`; they stay from the no-chain version (chain strips only second) and keep the node bound.
  Weights `gw`: strip lengths.
* `crpath_to_path`, `path_to_crpath`: `CRPathCA` paths and graph paths in `candN V G`
  correspond, with equal weights, via `posList`.
* `findPath`: a minimum `CRPathCA` path (`findPath_some`), or `none` when there is none
  (`findPath_none`).

## Cost

By `card_allStrips`, `|cand V G| ≤ 4|V| + |V| · 4|V|`, so `n = |candN V G| ≤ 3 (4|V| + 4|V|²)`.
`SolidGridHam.MP.minPath` makes at most `n³` `gedge` evaluations plus `n` `gsrc` evaluations
Proved as `findPathCost_le` (`CostAlg.lean`).
-/

namespace SolidGridHam

open Finset

/-! ## Deciding `ChainOK` -/

def chainOKB (b c : StripSpec) : Bool :=
  (List.range c.n).all fun j =>
    decide (∀ x ∈ cellE (cellJ c.c c.s j), x ∈ cellE (endCell b) →
      j = 0 ∧ (x = lat1 (endCell b) b.s ∨ x = lat2 (endCell b) b.s))

lemma chainOKB_iff {b c : StripSpec} : chainOKB b c = true ↔ ChainOK b c := by
  simp only [chainOKB, ChainOK, List.all_eq_true, List.mem_range, decide_eq_true_eq]

/-! ## Nodes -/

def sideIdx : Side → ℕ
  | .b => 0
  | .t => 1
  | .l => 2
  | .r => 3

lemma sideIdx_inj : Function.Injective sideIdx := by
  intro a a' h
  cases a <;> cases a' <;> first | rfl | (simp [sideIdx] at h)

structure Node where
  σ : StripSpec
  pos : ℕ
  deriving DecidableEq

-- A lexicographic key, used only to give `Node` a computable linear order
-- (needed by `MP.minPath`).
--
def Node.key (x : Node) : Lex (ℤ × Lex (ℤ × Lex (ℕ × Lex (ℕ × ℕ)))) :=
  toLex (x.σ.c.1, toLex (x.σ.c.2, toLex (sideIdx x.σ.s, toLex (x.σ.n, x.pos))))

lemma Node.key_inj : Function.Injective Node.key := by
  rintro ⟨⟨⟨c1, c2⟩, s, n⟩, p⟩ ⟨⟨⟨d1, d2⟩, s', m⟩, q⟩ h
  simp only [Node.key, toLex_inj, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, hs, rfl, rfl⟩ := h
  rw [sideIdx_inj hs]

instance : LinearOrder Node := LinearOrder.lift' Node.key Node.key_inj

/-! ## Candidates -/

section graph

variable (V : Finset Pt) (G : Finset Edge)

def cand : Finset StripSpec :=
  allStrips V G ∪ (V.filter (IsCell V)).biUnion (fun u => allStrips V (flip G u))

def candN : Finset Node :=
  (cand V G).biUnion fun σ => ({1, 2, 3} : Finset ℕ).image fun p => Node.mk σ p

/-! ## The graph -/

def gsrc (x : Node) : Bool := x.pos == 1 && validB V G x.σ

def gmid (x : Node) : Bool := x.σ.n % 2 == 0

def gtgt (x : Node) : Bool := x.σ.n % 2 == 1

def gedge (x y : Node) : Bool :=
  (y.pos == min (x.pos + 1) 3) && cr2B V G x.σ y.σ && chainOKB x.σ y.σ

def gw (x : Node) : ℕ := x.σ.n

end graph

-- Strips tagged with positions: the first gets `k`, later ones count up to `3`.
--
def posList : ℕ → List StripSpec → List Node
  | _, [] => []
  | k, σ :: L => ⟨σ, k⟩ :: posList (min (k + 1) 3) L

lemma posList_map : ∀ (L : List StripSpec) (k : ℕ), (posList k L).map Node.σ = L
  | [], _ => rfl
  | σ :: L, k => by simp only [posList, List.map_cons, posList_map L]

lemma pw_posList : ∀ (L : List StripSpec) (k : ℕ),
    MP.pw gw (posList k L) = (L.map StripSpec.n).sum
  | [], _ => rfl
  | σ :: L, k => by
    rw [posList, MP.pw_cons, pw_posList L, List.map_cons, List.sum_cons]
    rfl

lemma posList_mem : ∀ (L : List StripSpec) (k : ℕ), k ≤ 3 → ∀ x ∈ posList k L,
    x.σ ∈ L ∧ k ≤ x.pos ∧ x.pos ≤ 3
  | [], _, _, x, hx => by simp [posList] at hx
  | σ :: L, k, hk, x, hx => by
    rw [posList, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ⟨by simp, le_refl _, hk⟩
    · obtain ⟨h1, h2, h3⟩ := posList_mem L (min (k + 1) 3) (min_le_right _ _) x hx
      exact ⟨List.mem_cons_of_mem _ h1, by omega, h3⟩

section facts

variable {V : Finset Pt} {G : Finset Edge}

lemma mem_candN {x : Node} :
    x ∈ candN V G ↔ x.σ ∈ cand V G ∧ x.pos ∈ ({1, 2, 3} : Finset ℕ) := by
  obtain ⟨σ, p⟩ := x
  simp only [candN, Finset.mem_biUnion, Finset.mem_image]
  constructor
  · rintro ⟨τ, hτ, q, hq, he⟩
    cases he
    exact ⟨hτ, hq⟩
  · rintro ⟨hσ, hp⟩
    exact ⟨σ, hσ, p, hp, rfl⟩

-- Every candidate strip has its cells in `V`.
--
lemma cells_of_cand {σ : StripSpec} (h : σ ∈ cand V G) :
    1 ≤ σ.n ∧ ∀ j < σ.n, IsCell V (cellJ σ.c σ.s j) := by
  simp only [cand, Finset.mem_union, Finset.mem_biUnion] at h
  rcases h with h | ⟨_, _, h⟩
  · obtain ⟨h1, _, hc⟩ := mem_allStrips.1 h
    exact ⟨h1, hc⟩
  · obtain ⟨h1, _, hc⟩ := mem_allStrips.1 h
    exact ⟨h1, hc⟩

lemma endCell_isCell {σ : StripSpec} (h1 : 1 ≤ σ.n)
    (hc : ∀ j < σ.n, IsCell V (cellJ σ.c σ.s j)) : IsCell V (endCell σ) :=
  hc (σ.n - 1) (by omega)

lemma valid_cells {σ : StripSpec} (h : ValidStrip V G σ) :
    1 ≤ σ.n ∧ ∀ j < σ.n, IsCell V (cellJ σ.c σ.s j) := by
  obtain ⟨h1, _, hc, _⟩ := h
  exact ⟨h1, hc⟩

lemma link_cells {b c : StripSpec} (h : CR2 V G b c) :
    1 ≤ c.n ∧ ∀ j < c.n, IsCell V (cellJ c.c c.s j) := by
  obtain ⟨_, _, h1, _, hc, _⟩ := h
  exact ⟨h1, hc⟩

lemma cand_of_valid {σ : StripSpec} (h : ValidStrip V G σ) : σ ∈ cand V G := by
  obtain ⟨h1, hp, hc, _⟩ := h
  exact Finset.mem_union_left _ (mem_allStrips.2 ⟨h1, hp, hc⟩)

lemma cand_of_link {b c : StripSpec} (h1 : 1 ≤ b.n)
    (hb : ∀ j < b.n, IsCell V (cellJ b.c b.s j)) (hl : CR2 V G b c) : c ∈ cand V G := by
  obtain ⟨_, _, hc1, hp, hc, _⟩ := hl
  have hu := endCell_isCell h1 hb
  exact Finset.mem_union_right _ (Finset.mem_biUnion.2
    ⟨endCell b, Finset.mem_filter.2 ⟨hu.1, hu⟩, mem_allStrips.2 ⟨hc1, hp, hc⟩⟩)

lemma chain_cand : ∀ (L : List StripSpec) (b : StripSpec), 1 ≤ b.n →
    (∀ j < b.n, IsCell V (cellJ b.c b.s j)) → CRChain V G b L → ∀ c ∈ L, c ∈ cand V G
  | [], _, _, _, _, c, hc => by simp at hc
  | τ :: L, b, h1, hb, hch, c, hc => by
    obtain ⟨_, hl, hrest⟩ := hch
    obtain ⟨hτ1, hτc⟩ := link_cells hl
    rcases List.mem_cons.1 hc with rfl | hc
    · exact cand_of_link h1 hb hl
    · exact chain_cand L τ hτ1 hτc hrest c hc

/-! ## From `CRPathCA` paths to graph paths -/

-- A chain from `b` at position `k` is a tail of the graph.
--
theorem tail_of_chain (hGV : Inside V G) : ∀ (L : List StripSpec) (b : StripSpec) (k : ℕ),
    1 ≤ b.n → (∀ j < b.n, IsCell V (cellJ b.c b.s j)) → CRChain V G b L → CATail (b :: L) →
    MP.IsTail gmid gtgt (gedge V G) ⟨b, k⟩ (posList (min (k + 1) 3) L) := by
  intro L
  induction L with
  | nil =>
    intro b k _ _ hch _
    show gtgt ⟨b, k⟩ = true
    simp only [gtgt, beq_iff_eq]
    exact hch
  | cons c L ih =>
    intro b k h1 hb hch hcat
    obtain ⟨hev, hl, hrest⟩ := hch
    obtain ⟨hc1, hcc⟩ := link_cells hl
    rw [posList, MP.isTail_cons]
    refine ⟨?_, ?_, ih c (min (k + 1) 3) hc1 hcc hrest hcat.2⟩
    · show (b.n % 2 == 0) = true
      simp only [beq_iff_eq]
      exact hev
    · show ((min (k + 1) 3 == min (k + 1) 3) && cr2B V G b c && chainOKB b c) = true
      rw [beq_self_eq_true, (cr2B_iff hGV (endCell_isCell h1 hb)).2 hl, chainOKB_iff.2 hcat.1]
      rfl

theorem crpath_to_path (hGV : Inside V G) {σ : StripSpec} {L : List StripSpec}
    (h : CRPathCA V G σ L) :
    MP.IsPath (gsrc V G) gmid gtgt (gedge V G) (posList 1 (σ :: L)) ∧
      (∀ x ∈ posList 1 (σ :: L), x ∈ candN V G) ∧ MP.pw gw (posList 1 (σ :: L)) = wt σ L := by
  obtain ⟨⟨hv, hch⟩, hnc⟩ := h
  obtain ⟨h1, hc⟩ := valid_cells hv
  refine ⟨?_, ?_, ?_⟩
  · rw [posList, MP.isPath_cons]
    refine ⟨?_, tail_of_chain hGV L σ 1 h1 hc hch hnc⟩
    show ((1 == 1) && validB V G σ) = true
    rw [(validB_iff hGV).2 hv]
    rfl
  · intro x hx
    obtain ⟨hxL, hk1, hk3⟩ := posList_mem (σ :: L) 1 (by omega) x hx
    refine mem_candN.2 ⟨?_, ?_⟩
    · rcases List.mem_cons.1 hxL with he | he
      · rw [he]
        exact cand_of_valid hv
      · exact chain_cand L σ h1 hc hch _ he
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
  · rw [pw_posList]
    rfl

/-! ## From graph paths to `CRPathCA` paths -/

-- A tail from `x` with nodes in `candN` is a chain from `x.σ`, with positions forced by
-- `gedge`.
--
theorem chain_of_tail (hGV : Inside V G) : ∀ (rest : List Node) (x : Node),
    MP.IsTail gmid gtgt (gedge V G) x rest → (∀ y ∈ x :: rest, y ∈ candN V G) →
    ∃ L, rest = posList (min (x.pos + 1) 3) L ∧ CRChain V G x.σ L ∧ CATail (x.σ :: L) := by
  intro rest
  induction rest with
  | nil =>
    intro x ht _
    refine ⟨[], rfl, ?_, trivial⟩
    have h : gtgt x = true := ht
    simp only [gtgt, beq_iff_eq] at h
    exact h
  | cons y rest ih =>
    intro x ht hN
    rw [MP.isTail_cons] at ht
    obtain ⟨hm, he, ht'⟩ := ht
    obtain ⟨L, hL, hch, hcat⟩ :=
      ih y ht' (fun z hz => hN z (List.mem_cons_of_mem _ hz))
    obtain ⟨hxc, _⟩ := mem_candN.1 (hN x (by simp))
    obtain ⟨hx1, hxcells⟩ := cells_of_cand hxc
    simp only [gedge, Bool.and_eq_true, beq_iff_eq, chainOKB_iff] at he
    obtain ⟨⟨hpos, hcr⟩, hok⟩ := he
    rw [cr2B_iff hGV (endCell_isCell hx1 hxcells)] at hcr
    have hev : x.σ.n % 2 = 0 := by
      simp only [gmid, beq_iff_eq] at hm
      exact hm
    refine ⟨y.σ :: L, ?_, ?_, hok, hcat⟩
    · rw [posList, ← hpos, ← hL]
    · show x.σ.n % 2 = 0 ∧ CR2 V G x.σ y.σ ∧ CRChain V G y.σ L
      exact ⟨hev, hcr, hch⟩

theorem path_to_crpath (hGV : Inside V G) {p : List Node}
    (hp : MP.IsPath (gsrc V G) gmid gtgt (gedge V G) p) (hN : ∀ x ∈ p, x ∈ candN V G) :
    ∃ σ L, p = posList 1 (σ :: L) ∧ CRPathCA V G σ L ∧ MP.pw gw p = wt σ L := by
  cases p with
  | nil => exact absurd hp id
  | cons x rest =>
    obtain ⟨σ, k⟩ := x
    rw [MP.isPath_cons] at hp
    obtain ⟨hs, ht⟩ := hp
    simp only [gsrc, Bool.and_eq_true, beq_iff_eq] at hs
    obtain ⟨rfl, hv⟩ := hs
    rw [validB_iff hGV] at hv
    obtain ⟨L, hL, hch, hnc⟩ := chain_of_tail hGV rest ⟨σ, 1⟩ ht hN
    subst hL
    refine ⟨σ, L, rfl, ⟨⟨hv, hch⟩, hnc⟩, ?_⟩
    rw [show (⟨σ, 1⟩ :: posList (min (1 + 1) 3) L : List Node) = posList 1 (σ :: L) from rfl,
      pw_posList]
    rfl

end facts

/-! ## The search -/

def decode : List Node → Option (StripSpec × List StripSpec)
  | [] => none
  | x :: p => some (x.σ, p.map Node.σ)

-- A minimum `CRPathCA` path from `G`, as its first strip and the rest.
--
def findPath (V : Finset Pt) (G : Finset Edge) : Option (StripSpec × List StripSpec) :=
  (MP.minPath (candN V G) (gsrc V G) gmid gtgt (gedge V G) gw).bind decode

lemma decode_posList (σ : StripSpec) (L : List StripSpec) :
    decode (posList 1 (σ :: L)) = some (σ, L) := by
  simp only [posList, decode, posList_map]

section search

variable {V : Finset Pt} {G : Finset Edge}

theorem findPath_some (hGV : Inside V G) {σ : StripSpec} {L : List StripSpec}
    (h : findPath V G = some (σ, L)) :
    CRPathCA V G σ L ∧ ∀ σ' L', CRPathCA V G σ' L' → wt σ L ≤ wt σ' L' := by
  unfold findPath at h
  cases hm : MP.minPath (candN V G) (gsrc V G) gmid gtgt (gedge V G) gw with
  | none =>
    rw [hm] at h
    cases h
  | some q =>
    rw [hm] at h
    change decode q = some (σ, L) at h
    obtain ⟨hq, hqN⟩ := MP.minPath_some _ _ _ _ _ _ hm
    obtain ⟨σ0, L0, rfl, hP, hw⟩ := path_to_crpath hGV hq hqN
    rw [decode_posList] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    refine ⟨hP, fun σ' L' hP' => ?_⟩
    obtain ⟨hq', hqN', hw'⟩ := crpath_to_path hGV hP'
    rw [← hw, ← hw']
    exact MP.minPath_min _ _ _ _ _ _ hm _ hq' hqN'

theorem findPath_none (hGV : Inside V G) (h : findPath V G = none) :
    ∀ σ L, ¬ CRPathCA V G σ L := by
  intro σ L hP
  unfold findPath at h
  cases hm : MP.minPath (candN V G) (gsrc V G) gmid gtgt (gedge V G) gw with
  | none =>
    obtain ⟨hq, hqN, _⟩ := crpath_to_path hGV hP
    exact MP.minPath_none _ _ _ _ _ _ hm _ hq hqN
  | some q =>
    rw [hm] at h
    change decode q = none at h
    obtain ⟨hq, hqN⟩ := MP.minPath_some _ _ _ _ _ _ hm
    obtain ⟨σ0, L0, rfl, _, _⟩ := path_to_crpath hGV hq hqN
    rw [decode_posList] at h
    cases h

end search

/-! ## Example

Points `{0, …, 3} × {0, 1}` (three cells in a row) and the 2-factor of the two squares
around cells `(0, 0)` and `(2, 0)`. Flipping the middle cell `(1, 0)` (a strip of one
cell) joins them, so the minimum path is a single strip with one cell.
-/

-- To run it, in a scratch file that imports `SolidGridHam`:
--
-- #eval
--   let V : Finset Pt := (Finset.range 4 ×ˢ Finset.range 2).image fun q => ((q.1 : ℤ), (q.2 : ℤ))
--   let G : Finset Edge := cellE (0, 0) ∪ cellE (2, 0)
--   (findPath V G).map fun r => (r.1.c, sideIdx r.1.s, r.1.n, r.2.length)

end SolidGridHam
