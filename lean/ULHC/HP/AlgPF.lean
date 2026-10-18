/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.HP.AlgProto
import ULHC.HP.TheoremAT2

/-!
# The path-factor algorithm (frozen design, 2026-10-11) and its soundness

One round from a path-factor `G` with endpoints `s`, `t`:
1. a Type III cell with no endpoint as a corner: flip it;
2. two components and a Type III cell anywhere: flip it;
3. a minimum chain in ULHC's link graph (`cr2B`, `chainOKB`), restricted to strips with no
   endpoint as a corner of any cell, whose end is good: a first strip that lowers the measure
   `Mc` of `G`; a second strip that is a strip of `G` after the first and, applied there, lowers
   `Mc` below that of `G`; a later strip only if odd.  The whole chain is applied, each strip checked to be a strip of the current
   factor (`applyChainChecked`);
4. otherwise stop.

`runPF_sound`: if `runPF` answers `true` from a path-factor, a Hamiltonian s–t path exists.
Completeness (every reached state has such a chain, and it applies) is the open part.
-/

namespace ULHC

namespace HP

open Finset

/-! ## The end test -/

-- The measure, computably: twice the component count, plus 1 unless the next round has a Type III
-- cell to flip (away from the endpoints, or anywhere with two components).
--
def Mc (V : Finset Pt) (G : Finset Edge) (s t : Pt) : ℕ :=
  2 * cncomp V G + (if (findT3R V G s t).isSome || (cncomp V G == 2 && (findT3 V G).isSome) then 0 else 1)

def goodEndB (V : Finset Pt) (S : Finset Edge) (s t : Pt) (σ : StripSpec) : Bool :=
  let S2 := applyS S σ
  σ.n % 2 == 1 || decide (cncomp V S2 < cncomp V S) || (findT3R V S2 s t).isSome ||
    (cncomp V S2 == 2 && (findT3 V S2).isSome)

-- An alternating cell, as a test.
--
def altB (G : Finset Edge) (u : Pt) : Bool :=
  (decide (bot u ∈ G) && decide (top u ∈ G) && !decide (lft u ∈ G) && !decide (rgt u ∈ G)) ||
    (!decide (bot u ∈ G) && !decide (top u ∈ G) && decide (lft u ∈ G) && decide (rgt u ∈ G))

lemma altB_iff {G : Finset Edge} {u : Pt} : altB G u = true ↔ Alt G u := by
  unfold altB Alt
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    decide_eq_false_iff_not]
  tauto

-- A twisting cell: alternating, and its flip keeps the count.
--
def twistB (V : Finset Pt) (G : Finset Edge) (u : Pt) : Bool :=
  altB G u && (cncomp V (ULHC.flip G u) == cncomp V G)

/-! ## Nodes with a predecessor -/

structure PNode where
  σ : StripSpec
  pos : ℕ
  prev : StripSpec
  deriving DecidableEq

def stripKey (σ : StripSpec) : Lex (ℤ × Lex (ℤ × Lex (ℕ × ℕ))) :=
  toLex (σ.c.1, toLex (σ.c.2, toLex (sideIdx σ.s, σ.n)))

lemma stripKey_inj : Function.Injective stripKey := by
  rintro ⟨⟨c1, c2⟩, s, n⟩ ⟨⟨d1, d2⟩, s', m⟩ h
  simp only [stripKey, toLex_inj, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, hs, rfl⟩ := h
  rw [sideIdx_inj hs]

def PNode.key (x : PNode) := toLex (stripKey x.σ, toLex (x.pos, stripKey x.prev))

lemma PNode.key_inj : Function.Injective PNode.key := by
  rintro ⟨σ, p, q⟩ ⟨σ', p', q'⟩ h
  simp only [PNode.key, toLex_inj, Prod.mk.injEq] at h
  obtain ⟨h1, rfl, h3⟩ := h
  rw [stripKey_inj h1, stripKey_inj h3]

instance : LinearOrder PNode := LinearOrder.lift' PNode.key PNode.key_inj

section graph

variable (V : Finset Pt) (G : Finset Edge) (s t : Pt)

-- Candidate strips avoiding the endpoints.
--
def candR : Finset StripSpec := (cand V G).filter fun σ => avoidB s t σ

-- Nodes: position 1 and 3 carry themselves as predecessor; position 2 carries its predecessor.
--
def pnodes : Finset PNode :=
  (candR V G s t).image (fun σ => PNode.mk σ 1 σ) ∪
  (candR V G s t).image (fun σ => PNode.mk σ 3 σ) ∪
  ((candR V G s t) ×ˢ (candR V G s t)).image (fun p => PNode.mk p.1 2 p.2)

def psrc (x : PNode) : Bool := x.pos == 1 && x.prev == x.σ && validB V G x.σ
def pmid (x : PNode) : Bool := x.σ.n % 2 == 0
-- Rule Tg's end test, judged in `G` itself: an odd strip, or an even strip whose end cell,
-- flipped in `G`, keeps the count (twists the path).
--
def tgB (x : PNode) : Bool :=
  x.σ.n % 2 == 1 || (x.σ.n % 2 == 0 && twistB V G (endCell x.σ))
def ptgt (x : PNode) : Bool :=
  if x.pos == 1 then decide (Mc V (applyS G x.σ) s t < Mc V G s t)
  else tgB V G x
def pedge (x y : PNode) : Bool :=
  (y.pos == min (x.pos + 1) 3) && cr2B V G x.σ y.σ && chainOKB x.σ y.σ &&
    (if y.pos == 2 then y.prev == x.σ else y.prev == y.σ)
def pw (x : PNode) : ℕ := x.σ.n

def findChainPF : Option (List StripSpec) :=
  (MP.minPath (pnodes V G s t) (psrc V G) pmid (ptgt V G s t) (pedge V G) pw).map
    (List.map PNode.σ)

end graph

/-! ## Applying a chain, checked -/

def applyChainChecked (V : Finset Pt) : Finset Edge → List StripSpec → Option (Finset Edge)
  | G, [] => some G
  | G, σ :: L => if σ ∈ allStrips V G then applyChainChecked V (applyS G σ) L else none

-- One round: flip a Type III cell to flip, or apply the first strip of a minimum chain (as
-- ULHC does; the next round searches again).
--
def stepPF (V : Finset Pt) (G : Finset Edge) (s t : Pt) : Option (Finset Edge) :=
  match findT3R V G s t with
  | some (d, _) => some (flip G d)
  | none =>
    if cncomp V G == 2 then
      match findT3 V G with
      | some (d, _) => some (flip G d)
      | none =>
        match findChainPF V G s t with
        | some L => applyChainChecked V G (L.take 1)
        | none => none
    else
      match findChainPF V G s t with
      | some L => applyChainChecked V G (L.take 1)
      | none => none

def runPF (V : Finset Pt) (s t : Pt) : ℕ → Finset Edge → Bool
  | 0, G => cncomp V G == 1
  | k + 1, G =>
    if cncomp V G == 1 then true
    else match stepPF V G s t with
      | some G' => runPF V s t k G'
      | none => false

/-! ## Soundness -/

section sound

variable {V : Finset Pt} {d : Pt → ℕ} {s t : Pt}

lemma findT3R_some {G : Finset Edge} (hGV : Inside V G) {c : Pt} {tf : Side}
    (h : findT3R V G s t = some (c, tf)) : IsCell V c ∧ back c tf ∈ G ∧ front c tf ∈ G ∧
      lat1 c tf ∉ G ∧ lat2 c tf ∉ G ∧ ¬ Conn G (back1 c tf) (front1 c tf) := by
  unfold findT3R at h
  have hm := List.mem_of_find?_eq_some h
  have hp := List.find?_some h
  simp only [List.mem_flatMap, List.mem_map] at hm
  obtain ⟨c', hc', t', _, he⟩ := hm
  cases he
  have hc := (mem_cellList.1 hc').2
  simp only [Bool.and_eq_true] at hp
  exact ⟨hc, (t3B_iff hGV hc).1 hp.2⟩

lemma flip_t3_factor {G : Finset Edge} (hG : IsFactor V d G) (hd : ∀ z, z ≠ s → z ≠ t → d z = 2)
    (hds : d s = 1) (hsV : s ∈ V) {c : Pt} {tf : Side}
    (h : IsCell V c ∧ back c tf ∈ G ∧ front c tf ∈ G ∧ lat1 c tf ∉ G ∧ lat2 c tf ∉ G ∧
      ¬ Conn G (back1 c tf) (front1 c tf)) : IsFactor V d (ULHC.flip G c) := by
  obtain ⟨hc, hb, hf, hl1, hl2, hn⟩ := h
  exact (typeIII_flip (H := G) hG hd hds hsV hc (fun hT => hn (hT tf hb hf hl1 hl2))).1

lemma applyChainChecked_factor : ∀ (L : List StripSpec) (G G' : Finset Edge), IsFactor V d G →
    applyChainChecked V G L = some G' → IsFactor V d G'
  | [], G, G', hG, h => by simp only [applyChainChecked, Option.some.injEq] at h; exact h ▸ hG
  | σ :: L, G, G', hG, h => by
    simp only [applyChainChecked] at h
    split_ifs at h with hσ
    obtain ⟨_, hpat, hcell⟩ := mem_allStrips.1 hσ
    exact applyChainChecked_factor L _ G' (factor_flipCol σ.n G hG hpat hcell) h

theorem stepPF_factor {G G' : Finset Edge} (hG : IsFactor V d G)
    (hd : ∀ z, z ≠ s → z ≠ t → d z = 2) (hds : d s = 1) (hsV : s ∈ V)
    (h : stepPF V G s t = some G') : IsFactor V d G' := by
  have hGV := Inside.of_factor hG
  unfold stepPF at h
  rcases hr : findT3R V G s t with _ | ⟨c, tf⟩
  · rw [hr] at h
    simp only at h
    split_ifs at h
    · rcases ht : findT3 V G with _ | ⟨c, tf⟩
      · rw [ht] at h
        simp only at h
        rcases hp : findChainPF V G s t with _ | L
        · rw [hp] at h; simp at h
        · rw [hp] at h; exact applyChainChecked_factor (L.take 1) G G' hG h
      · rw [ht] at h
        simp only [Option.some.injEq] at h
        subst h
        exact flip_t3_factor hG hd hds hsV (findT3_some hGV ht)
    · rcases hp : findChainPF V G s t with _ | L
      · rw [hp] at h; simp at h
      · rw [hp] at h; exact applyChainChecked_factor (L.take 1) G G' hG h
  · rw [hr] at h
    simp only [Option.some.injEq] at h
    subst h
    exact flip_t3_factor hG hd hds hsV (findT3R_some hGV hr)

-- **Soundness.** A `true` answer from a path-factor gives a Hamiltonian s–t path.
--
theorem runPF_sound (hd : ∀ z, z ≠ s → z ≠ t → d z = 2) (hds : d s = 1) (hsV : s ∈ V) :
    ∀ (k : ℕ) (G : Finset Edge), IsFactor V d G → runPF V s t k G = true →
      ∃ H, IsFactor V d H ∧ ncomp V H = 1 := by
  intro k
  induction k with
  | zero =>
    intro G hG h
    simp only [runPF, beq_iff_eq] at h
    exact ⟨G, hG, by rw [← cncomp_eq (Inside.of_factor hG)]; exact h⟩
  | succ k ih =>
    intro G hG h
    simp only [runPF] at h
    by_cases h1 : cncomp V G = 1
    · exact ⟨G, hG, by rw [← cncomp_eq (Inside.of_factor hG)]; exact h1⟩
    · rw [ite_eq_right (by simpa using h1)] at h
      rcases hs : stepPF V G s t with _ | G'
      · rw [hs] at h; simp at h
      · rw [hs] at h
        exact ih G' (stepPF_factor hG hd hds hsV hs) h

end sound

end HP

end ULHC
