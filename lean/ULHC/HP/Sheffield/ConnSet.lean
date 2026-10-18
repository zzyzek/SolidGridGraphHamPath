/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.HP.Sheffield.SheffCost

/-!
# All connections of a state at once

`comps W H`: one sweep over the points of `W`, computing the class `ccls W H x` only for points not
yet covered, gives the list of components. `connectedPairs W H` is the set of connected pairs, the union of
`C ×ˢ C` over the components. Membership in it decides `connB W H x y` for every `x ∈ W`
(`isConnected_eq`), and building it takes `O(|W|²)` steps (`connectedPairsCost_le`), against `O(|W|²)` for a
single `connB`.
-/

namespace ULHC

namespace HP

open Finset Classical

def compsAux (W : Finset Pt) (H : Finset Edge) : List Pt → Finset Pt → List (Finset Pt)
  | [], _ => []
  | x :: xs, cov =>
    if x ∈ cov then compsAux W H xs cov
    else ccls W H x :: compsAux W H xs (cov ∪ ccls W H x)

-- The points of `W` in lexicographic order.
--
def ptList (W : Finset Pt) : List Pt := ((W.map toLex.toEmbedding).sort (· ≤ ·)).map ofLex

lemma mem_ptList {W : Finset Pt} {x : Pt} : x ∈ ptList W ↔ x ∈ W := by
  unfold ptList
  simp only [List.mem_map, Finset.mem_sort, Finset.mem_map]
  constructor
  · rintro ⟨a, ⟨b, hb, rfl⟩, rfl⟩; exact hb
  · intro h; exact ⟨toLex x, ⟨x, h, rfl⟩, rfl⟩

def comps (W : Finset Pt) (H : Finset Edge) : List (Finset Pt) := compsAux W H (ptList W) ∅

def connectedPairs (W : Finset Pt) (H : Finset Edge) : Finset (Pt × Pt) :=
  (comps W H).toFinset.biUnion fun C => C ×ˢ C

def isConnected (S : Finset (Pt × Pt)) (x y : Pt) : Bool := decide ((x, y) ∈ S)

section connectedPairs

variable {W : Finset Pt} {H : Finset Edge}

lemma mem_ccls_self (x : Pt) : x ∈ ccls W H x := by
  unfold ccls
  exact creach_mono (Nat.zero_le _) (by simp [creach])

lemma ccls_eq_of_mem (hHW : Inside W H) {x a : Pt} (hx : x ∈ W) (ha : a ∈ ccls W H x) :
    ccls W H a = ccls W H x := by
  rw [ccls_eq hHW hx] at ha
  simp only [cls, Finset.mem_filter] at ha
  obtain ⟨haW, hxa⟩ := ha
  rw [ccls_eq hHW haW, ccls_eq hHW hx]
  ext y
  simp only [cls, Finset.mem_filter]
  exact ⟨fun ⟨h1, h2⟩ => ⟨h1, hxa.trans h2⟩, fun ⟨h1, h2⟩ => ⟨h1, hxa.symm.trans h2⟩⟩

lemma ccls_sub (hHW : Inside W H) {x : Pt} (hx : x ∈ W) : ccls W H x ⊆ W :=
  creach_sub hHW hx _

-- The sweep: components found so far are closed classes covering `cov`.
--
lemma compsAux_spec (hHW : Inside W H) :
    ∀ (l : List Pt) (cov : Finset Pt), (∀ x ∈ l, x ∈ W) → cov ⊆ W →
      (∀ x ∈ cov, ccls W H x ⊆ cov) →
      (∀ C ∈ compsAux W H l cov, ∃ x ∈ W, x ∉ cov ∧ C = ccls W H x) ∧
      ∀ x ∈ l, x ∉ cov → ∃ C ∈ compsAux W H l cov, x ∈ C := by
  intro l
  induction l with
  | nil => intro _ _ _ _; simp [compsAux]
  | cons y ys ih =>
    intro cov hl hcov hcl
    have hyW := hl y (by simp)
    have hys : ∀ x ∈ ys, x ∈ W := fun x hx => hl x (by simp [hx])
    simp only [compsAux]
    by_cases hy : y ∈ cov
    · rw [ite_eq_left hy]
      obtain ⟨a, b⟩ := ih cov hys hcov hcl
      refine ⟨a, fun x hx hxc => ?_⟩
      rcases List.mem_cons.1 hx with rfl | hx
      · exact absurd hy hxc
      · exact b x hx hxc
    · rw [ite_eq_right hy]
      have hcov' : cov ∪ ccls W H y ⊆ W := Finset.union_subset hcov (ccls_sub hHW hyW)
      have hcl' : ∀ x ∈ cov ∪ ccls W H y, ccls W H x ⊆ cov ∪ ccls W H y := by
        intro x hx
        rcases Finset.mem_union.1 hx with hx | hx
        · exact (hcl x hx).trans Finset.subset_union_left
        · rw [ccls_eq_of_mem hHW hyW hx]; exact Finset.subset_union_right
      obtain ⟨a, b⟩ := ih _ hys hcov' hcl'
      refine ⟨fun C hC => ?_, fun x hx hxc => ?_⟩
      · rcases List.mem_cons.1 hC with rfl | hC
        · exact ⟨y, hyW, hy, rfl⟩
        · obtain ⟨z, hzW, hz, rfl⟩ := a C hC
          exact ⟨z, hzW, fun h => hz (Finset.mem_union_left _ h), rfl⟩
      · by_cases hxy : x ∈ ccls W H y
        · exact ⟨_, List.mem_cons_self, hxy⟩
        · rcases List.mem_cons.1 hx with rfl | hx
          · exact absurd (mem_ccls_self x) hxy
          · obtain ⟨C, hC, hxC⟩ := b x hx (by simp [hxc, hxy])
            exact ⟨C, List.mem_cons_of_mem _ hC, hxC⟩

lemma mem_connSet (hHW : Inside W H) {x y : Pt} :
    (x, y) ∈ connectedPairs W H ↔ x ∈ W ∧ y ∈ ccls W H x := by
  obtain ⟨a, b⟩ := compsAux_spec hHW (ptList W) ∅ (fun x hx => mem_ptList.1 hx)
    (Finset.empty_subset _) (by simp)
  unfold connectedPairs comps
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨C, hC, hxy⟩
    obtain ⟨z, hzW, _, rfl⟩ := a C (List.mem_toFinset.1 hC)
    rw [Finset.mem_product] at hxy
    obtain ⟨hx, hy⟩ := hxy
    refine ⟨ccls_sub hHW hzW hx, ?_⟩
    rw [ccls_eq_of_mem hHW hzW hx]; exact hy
  · rintro ⟨hx, hy⟩
    obtain ⟨C, hC, hxC⟩ := b x (mem_ptList.2 hx) (by simp)
    refine ⟨C, List.mem_toFinset.2 hC, ?_⟩
    obtain ⟨z, hzW, _, rfl⟩ := a C hC
    rw [Finset.mem_product]
    refine ⟨hxC, ?_⟩
    rw [← ccls_eq_of_mem hHW hzW hxC]; exact hy

-- **One membership test decides a connection.**
--
theorem isConnected_eq (hHW : Inside W H) {x : Pt} (hx : x ∈ W) (y : Pt) :
    isConnected (connectedPairs W H) x y = connB W H x y := by
  unfold isConnected connB
  exact decide_eq_decide.2 (by rw [mem_connSet hHW]; exact ⟨fun h => h.2, fun h => ⟨hx, h⟩⟩)

end connectedPairs

end HP

end ULHC
