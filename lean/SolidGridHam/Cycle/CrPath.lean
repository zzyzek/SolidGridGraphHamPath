/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import SolidGridHam.Cycle.Cr2

@[expose] public section

/-!
# Paths of the search graph

A *link* `CR2 V G b c` from an even strip `b` (end cell `u`) to a strip `c`:
* `c` is a strip of `G ⊕ u` (so a chain strip may use a lateral side of `u`);
* `c`'s cells share no side with the cells of `b` other than `u`, and none of them is `u`;
* if `c` is even, its end cell shares no side with `u`;
* `c`'s start corners are not middle corners of `b`;
* `c`'s start corners are joined in `G` and split apart in `G ⊕ u` (`c` is created by `u`).

A path from `G` is a strip that is proper in `G`, followed by links relative to `G`, the
last strip odd and the others even.

* `link_step`: after a proper even strip `b` of a Type III-free `G`, a linked strip is a
  proper strip of `G ⊕ b`.
-/

namespace SolidGridHam

open Finset Classical

-- `c`'s cells share no side with the cells of `b` before its end cell.
--
def SideOff (b c : StripSpec) : Prop :=
  ∀ j < c.n, ∀ i, i + 1 < b.n → ∀ e ∈ cellE (cellJ c.c c.s j), e ∉ cellE (cellJ b.c b.s i)

def CR2 (V : Finset Pt) (G : Finset Edge) (b c : StripSpec) : Prop :=
  2 ≤ b.n ∧ b.n % 2 = 0 ∧ 1 ≤ c.n ∧ StripPat (flip G (endCell b)) c.c c.s c.n ∧
    (∀ j < c.n, IsCell V (cellJ c.c c.s j)) ∧ SideOff b c ∧
    (∀ j < c.n, cellJ c.c c.s j ≠ endCell b) ∧
    (c.n % 2 = 0 → ∀ e ∈ cellE (endCell c), e ∉ cellE (endCell b)) ∧
    ¬ IsMid b.c b.s (b.n - 2) (back1 c.c c.s) ∧ ¬ IsMid b.c b.s (b.n - 2) (front1 c.c c.s) ∧
    Conn G (back1 c.c c.s) (front1 c.c c.s) ∧
    ¬ Conn (flip G (endCell b)) (back1 c.c c.s) (front1 c.c c.s)

-- A chain of links ending in an odd strip.
--
def CRChain (V : Finset Pt) (G : Finset Edge) : StripSpec → List StripSpec → Prop
  | σ, [] => σ.n % 2 = 1
  | σ, τ :: L => σ.n % 2 = 0 ∧ CR2 V G σ τ ∧ CRChain V G τ L

def CRPath (V : Finset Pt) (G : Finset Edge) (σ : StripSpec) (L : List StripSpec) : Prop :=
  ValidStrip V G σ ∧ CRChain V G σ L

def wt (σ : StripSpec) (L : List StripSpec) : ℕ := σ.n + (L.map StripSpec.n).sum

-- Away from the cells before the end, a strip flip acts as the end cell's flip.
--
lemma flipCol_off (G : Finset Edge) (c : Pt) (s : Side) (n : ℕ) {e : Edge}
    (h : ∀ i, i + 1 < n + 1 → e ∉ cellE (cellJ c s i)) :
    e ∈ flipCol G c s (n + 1) ↔ e ∈ flip G (cellJ c s n) := by
  rw [mem_flipCol, mem_flip_iff]
  by_cases he : e ∈ cellE (cellJ c s n)
  · rw [nOn_eq c s (n + 1) e {n} (fun j hj => by
      constructor
      · intro h'
        by_contra hne
        exact h j (by simp at hne; omega) h'
      · intro h'; simp at h'; subst h'; exact he) (by simp)]
    simp [he]
  · rw [nOn_eq c s (n + 1) e ∅ (fun j hj => by
      constructor
      · intro h'
        rcases (show j < n ∨ j = n by omega) with hj' | rfl
        · exact absurd h' (h j (by omega))
        · exact absurd h' he
      · intro h'; simp at h') (by simp)]
    simp [he]

theorem link_step {V : Finset Pt} {G : Finset Edge} (hG : Deg2 V G) (hT : NoTypeIII V G)
    {b c : StripSpec} (hb : ValidStrip V G b) (hl : CR2 V G b c) : ValidStrip V (applyS G b) c := by
  obtain ⟨h2, hev, hc1, hpatc, hcellc, hoff, hne, _, hm1, hm2, hxy, hsplit⟩ := hl
  obtain ⟨_, hpatb, hcellb, hsepb⟩ := hb
  obtain ⟨k, hk⟩ : ∃ k, b.n = k + 2 := ⟨b.n - 2, by omega⟩
  have hk2 : k % 2 = 0 := by omega
  have hend : endCell b = cellJ b.c b.s (k + 1) := by unfold endCell; rw [hk]; rfl
  rw [hk] at hpatb hcellb hm1 hm2
  rw [hend] at hpatc hsplit
  have hcellb' : ∀ j ≤ k + 1, IsCell V (cellJ b.c b.s j) := fun j hj => hcellb j (by omega)
  have hsame := end_same hT hk2 hcellb' hpatb
  have hm1' : ¬ IsMid b.c b.s k (back1 c.c c.s) := by simpa using hm1
  have hm2' : ¬ IsMid b.c b.s k (front1 c.c c.s) := by simpa using hm2
  unfold applyS
  rw [hk]
  refine ⟨hc1, ?_, hcellc, created_step hk2 hG hcellb' hpatb hsepb hsame hxy hsplit hm1' hm2'⟩
  obtain ⟨n, hn⟩ : ∃ n, c.n = n + 1 := ⟨c.n - 1, by omega⟩
  rw [hn] at hpatc ⊢
  refine (stripPat_congr (fun j hj e he => ?_)).2 hpatc
  exact flipCol_off G b.c b.s (k + 1) (fun i hi => hoff j (by omega) i (by omega) e he)

/-! ## Progress: one round keeps the rest of a path -/

section progress

-- An even strip's end cell, read in a factor where its pattern holds.
--
lemma end_alt {F : Finset Edge} {σ : StripSpec} (h2 : 2 ≤ σ.n) (he : σ.n % 2 = 0)
    (hp : StripPat F σ.c σ.s σ.n) :
    lat1 (endCell σ) σ.s ∈ F ∧ lat2 (endCell σ) σ.s ∈ F ∧ back (endCell σ) σ.s ∉ F ∧
      front (endCell σ) σ.s ∉ F := by
  obtain ⟨k, hk⟩ : ∃ k, σ.n = k + 2 := ⟨σ.n - 2, by omega⟩
  have hend : endCell σ = cellJ σ.c σ.s (k + 1) := by unfold endCell; rw [hk]; rfl
  rw [hend]
  rw [hk] at hp
  obtain ⟨_, hl, hf⟩ := hp
  refine ⟨(hl (k + 1) (by omega)).1.2 (by omega), (hl (k + 1) (by omega)).2.2 (by omega), ?_, ?_⟩
  · rw [back_cellJ_succ]; intro h; have := (hf k (by omega)).1 h; omega
  · intro h; have := (hf (k + 1) (by omega)).1 h; omega

-- The end cell of an even strip, as seen in `G`.
--
def EndOK (V : Finset Pt) (G : Finset Edge) (σ : StripSpec) : Prop :=
  σ.n % 2 = 0 → IsCell V (endCell σ) ∧ lat1 (endCell σ) σ.s ∈ G ∧ lat2 (endCell σ) σ.s ∈ G ∧
    back (endCell σ) σ.s ∉ G ∧ front (endCell σ) σ.s ∉ G

lemma endOK_of_link {V : Finset Pt} {G : Finset Edge} {σ τ : StripSpec} (hl : CR2 V G σ τ) :
    EndOK V G τ := by
  intro hev
  obtain ⟨_, _, hc1, hpatc, hcellc, _, _, hendc, _⟩ := hl
  have h2 : 2 ≤ τ.n := by omega
  obtain ⟨l1, l2, b, f⟩ := end_alt h2 hev hpatc
  have tr : ∀ e ∈ cellE (endCell τ), (e ∈ flip G (endCell σ) ↔ e ∈ G) :=
    fun e he => mem_flip_off (hendc hev e he)
  have mem : ∀ e, e = lat1 (endCell τ) τ.s ∨ e = lat2 (endCell τ) τ.s ∨ e = back (endCell τ) τ.s ∨
      e = front (endCell τ) τ.s → e ∈ cellE (endCell τ) := by
    intro e he; rw [cellE_frame _ τ.s]; rcases he with rfl | rfl | rfl | rfl <;> simp
  refine ⟨hcellc _ (by omega), (tr _ (mem _ (Or.inl rfl))).1 l1,
    (tr _ (mem _ (Or.inr (Or.inl rfl)))).1 l2,
    fun h => b ((tr _ (mem _ (Or.inr (Or.inr (Or.inl rfl))))).2 h),
    fun h => f ((tr _ (mem _ (Or.inr (Or.inr (Or.inr rfl))))).2 h)⟩

end progress

end SolidGridHam
