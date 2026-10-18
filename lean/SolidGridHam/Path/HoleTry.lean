/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import SolidGridHam.Path.HoleRelax

/-!
# Hole classes: an initial factor in each class (B-3, docs/HOLE_CLASSES.md §3.2 P8)

Fix the inner set `V ⊆ W` and a reference factor `F` on `W`. The class of a factor `G` on `W`
agreeing with `F` off the edges of `V` is `D F G t / 2` at the hole point `t`.

* `classSearch V F as hs`: relax to the least admissible potential with the prescribed values `hs` at
  the points `as`, check it, and return `F ⊕ X` (`X` its jump set).
* `classSearchOne V F t h = classSearch V F [t] [h]`.

Results:

* `classSearchOne_sound`: a returned `G` is a factor on `W`, agrees with `F` off `V`, and has class `h`;
* `classSearchOne_complete`: if some such factor has class `h`, `classSearchOne` returns one;
* `classSearchOne_solidFor`: with one hole at `t`, the returned factor and any factor of the same class
  have `D = 0` off the cells of `V` (B-1);
* `hClass_bound`, `mem_hRange`: classes lie in `[-|V|, |V|]` (and in `[-boxWidth V, boxWidth V]`), so the
  list `classRange V` of `2|V| + 1` values covers them.
-/

namespace SolidGridHam

namespace HP

open Finset

def classSearch (V : Finset Pt) (F : Finset Edge) (as : List Pt) (hs : List ℤ) :
    Option (Finset Edge) :=
  let f := classPotential V F as hs
  if isAdmissible V F as hs f then some (symmDiff F (jumpEdges V f)) else none

-- The one-hole try: the least admissible potential with value `h` at `t`.
--
def classSearchOne (V : Finset Pt) (F : Finset Edge) (t : Pt) (h : ℤ) : Option (Finset Edge) :=
  classSearch V F [t] [h]

-- The candidate classes `-|V|, …, |V|`.
--
def classRange (V : Finset Pt) : List ℤ :=
  (List.range (2 * V.card + 1)).map fun (i : ℕ) => (i : ℤ) - V.card

section find

variable {V W : Finset Pt} {d : Pt → ℕ} {F G : Finset Edge} {as : List Pt} {hs : List ℤ}

theorem classSearch_sound (hVW : V ⊆ W) (hF : IsFactor W d F) (h : classSearch V F as hs = some G) :
    IsFactor W d G ∧ (∀ e ∈ symmDiff F G, IsEdge V e) ∧
      ∀ ah ∈ as.zip hs, D F G ah.1 = 2 * ah.2 := by
  unfold classSearch at h
  simp only at h
  split_ifs at h with hc
  simp only [Option.some.injEq] at h
  subst h
  set f := classPotential V F as hs
  have hf0 : ∀ c, c ∉ boxSquares V → f c = 0 := toF_kPot_off
  obtain ⟨hA, hhole⟩ := (check_iff hf0).1 hc
  have hX := mem_kX hf0
  obtain ⟨hG, hw⟩ := adm_factorW hVW hF hA hX
  have hFG : ∀ e ∈ symmDiff F (symmDiff F (jumpEdges V f)), IsEdge V e := by
    intro e he
    rw [symmDiff_symmDiff_cancel_left] at he
    exact ((hX e).1 he).1
  have hDG : ∀ c, D F (symmDiff F (jumpEdges V f)) c = 2 * f c := by
    apply D_of_admW hF hG hFG hw (B := bx0 V - 1)
    · intro p hp; have := box_mem hp; omega
    · intro c hc; apply hf0; rw [mem_kSq]; omega
  refine ⟨hG, hFG, fun ah hm => ?_⟩
  rw [hDG, hhole ah hm]

theorem classSearch_complete (hF : IsFactor W d F) (hG : IsFactor W d G)
    (hFG : ∀ e ∈ symmDiff F G, IsEdge V e) (hD : ∀ ah ∈ as.zip hs, D F G ah.1 = 2 * ah.2) :
    classSearch V F as hs ≠ none := by
  obtain ⟨hAψ, hev⟩ := adm_of_factorW hF hG hFG
  obtain ⟨hψ0r, hψWr⟩ := half_propsW hF hG hFG
  set ψ : Pt → ℤ := fun c => D F G c / 2 with hψdef
  have hψ0 : ∀ c, c ∉ boxSquares V → ψ c = 0 := hψ0r
  have hψW : ∀ c, |ψ c| ≤ boxWidth V := hψWr
  set S := boxSquares V
  set L0 := kInit V as hs
  have hL0 : Shape S L0 := shape_map _
  have hzip : ∀ ah ∈ as.zip hs, ah.2 = ψ ah.1 := by
    intro ah hm
    simp only [ψ, hD ah hm]
    omega
  have hle0 : ∀ c, toF L0 c ≤ ψ c := by
    intro c
    simp only [L0, kInit]
    rw [toF_map]
    split_ifs with hc
    · rcases hl : (as.zip hs).lookup c with _ | h
      · have := hψW c
        rw [abs_le] at this
        simp only [Option.getD_none]
        exact this.1
      · simp only [Option.getD_some]
        have hm := mem_of_lookup _ hl
        have := hzip _ hm
        simp only at this
        rw [this]
    · exact le_of_eq (hψ0 c hc).symm
  have hψlb : ∀ s ∈ S, lowerBound V F ψ s ≤ ψ s := fun s _ => lowerBound_le_of_adm hAψ s
  obtain ⟨hshape, hleR, hupR, hlbR⟩ :=
    relax_bf ψ hψlb hψ0 hL0 hle0 (kFuel V)
      (by show S.toFinset.card + 1 ≤ S.length + 1; have := List.toFinset_card_le S; omega)
  set f := toF (relax V F S (kFuel V) L0) with hfdef
  have hfk : classPotential V F as hs = f := classPotential_eq
  have hf0 : ∀ c, c ∉ boxSquares V → f c = 0 := fun c hc => toF_off hshape hc
  have hAf : Adm V F f := adm_of_fix hAψ hψ0 hf0 hleR hlbR
  have hholes : ∀ ah ∈ as.zip hs, f ah.1 = ah.2 := by
    intro ah hm
    rw [hzip ah hm]
    by_cases hc : ah.1 ∈ boxSquares V
    · apply le_antisymm (hleR _)
      have h1 := hupR ah.1
      simp only [L0, kInit] at h1
      rw [toF_map, ite_eq_left hc] at h1
      rcases hl : (as.zip hs).lookup ah.1 with _ | h
      · exfalso
        exact lookup_ne_none _ (by simpa using hm) hl
      · rw [hl] at h1
        simp only [Option.getD_some] at h1
        have := hzip _ (mem_of_lookup _ hl)
        simp only at this
        rw [this] at h1
        exact h1
    · rw [hf0 _ hc, hψ0 _ hc]
  have hcheck : isAdmissible V F as hs f = true := (check_iff hf0).2 ⟨hAf, hholes⟩
  unfold classSearch
  simp only [hfk, hcheck, ite_true]
  exact Option.some_ne_none _

end find

section one

variable {V W : Finset Pt} {d : Pt → ℕ} {F G : Finset Edge} {t : Pt} {h : ℤ}

/-- **B-3, soundness.** A factor returned by `classSearchOne` is a factor on `W`, differs from `F` only on
edges of `V`, and lies in class `h`. -/
theorem classSearchOne_sound (hVW : V ⊆ W) (hF : IsFactor W d F) (hT : classSearchOne V F t h = some G) :
    IsFactor W d G ∧ (∀ e ∈ symmDiff F G, e.p ∈ V ∧ e.q ∈ V) ∧ D F G t = 2 * h := by
  obtain ⟨hG, hFG, hD⟩ := classSearch_sound hVW hF hT
  exact ⟨hG, hFG, hD (t, h) (by simp)⟩

/-- **B-3, completeness.** If some factor on `W` agreeing with `F` off the edges of `V` lies in
class `h`, `classSearchOne` returns a factor. -/
theorem classSearchOne_complete (hF : IsFactor W d F) (hG : IsFactor W d G)
    (hFG : ∀ e ∈ symmDiff F G, e.p ∈ V ∧ e.q ∈ V) (hD : D F G t = 2 * h) :
    classSearchOne V F t h ≠ none := by
  apply classSearch_complete hF hG hFG
  intro ah hm
  simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at hm
  subst hm
  exact hD

-- The returned factor and any factor of class `h` have `D = 0` at the hole point.
--
lemma classSearchOne_D_zero (hVW : V ⊆ W) (hF : IsFactor W d F) {G' : Finset Edge}
    (hT : classSearchOne V F t h = some G') (hG : IsFactor W d G) (hD : D F G t = 2 * h) :
    D G' G t = 0 := by
  have hG' := (classSearchOne_sound hVW hF hT)
  rw [D_sub hF.1 hG'.1.1 hG.1, hD, hG'.2.2]
  ring

/-- **B-3 with B-1.** With one hole at `t` (every missing point of `V` joins `t` by king moves
through missing points, or escapes to the far left), the factor returned by `classSearchOne` and any factor of class `h` agreeing with `F` off `V` have
`D = 0` off the cells of `V`. -/
theorem classSearchOne_solidFor (hVW : V ⊆ W) (hF : IsFactor W d F) (htV : t ∉ V)
    (hesc : ∀ b, b ∉ V → Relation.ReflTransGen (MissAdj V) b t ∨
      ∃ b', Relation.ReflTransGen (MissAdj V) b b' ∧ ∀ p ∈ V, b'.1 < p.1)
    {G' : Finset Edge} (hT : classSearchOne V F t h = some G') (hG : IsFactor W d G)
    (hFG : ∀ e ∈ symmDiff F G, e.p ∈ V ∧ e.q ∈ V) (hD : D F G t = 2 * h) :
    SolidFor V G' G := by
  obtain ⟨hG', hFG', _⟩ := classSearchOne_sound hVW hF hT
  have hsd : ∀ e ∈ symmDiff G' G, e.p ∈ V ∧ e.q ∈ V := by
    intro e he
    have : symmDiff G' G = symmDiff (symmDiff F G') (symmDiff F G) := by
      rw [symmDiff_symmDiff_symmDiff_comm, symmDiff_self, bot_symmDiff]
    rw [this, Finset.mem_symmDiff] at he
    rcases he with ⟨he, _⟩ | ⟨he, _⟩
    · exact hFG' e he
    · exact hFG e he
  exact solidFor_of_holes hG' hG hsd (kholes_one htV hesc)
    (fun a ha => by
      simp only [List.mem_singleton] at ha
      subst ha
      exact classSearchOne_D_zero hVW hF hT hG hD)

/-- **Class bound.** Every factor agreeing with `F` off the edges of `V` has
`|D F G t| ≤ 2 |V|` and `|D F G t / 2| ≤ boxWidth V`; `D F G t` is even. -/
theorem hClass_bound (hF : IsFactor W d F) (hG : IsFactor W d G)
    (hFG : ∀ e ∈ symmDiff F G, e.p ∈ V ∧ e.q ∈ V) :
    |D F G t| ≤ 2 * V.card ∧ |D F G t / 2| ≤ boxWidth V ∧ D F G t = 2 * (D F G t / 2) :=
  ⟨D_abs_le_card hFG t, (half_propsW hF hG hFG).2 t,
    (Int.mul_ediv_cancel' (D_even F G t)).symm⟩

lemma mem_hRange {h : ℤ} (hh : |h| ≤ V.card) : h ∈ classRange V := by
  rw [abs_le] at hh
  refine List.mem_map.2 ⟨(h + V.card).toNat, List.mem_range.2 (by omega), ?_⟩
  omega

-- The class of every factor agreeing with `F` off `V` is in `classRange V`.
--
theorem class_mem_hRange (hFG : ∀ e ∈ symmDiff F G, e.p ∈ V ∧ e.q ∈ V) :
    D F G t / 2 ∈ classRange V ∧ D F G t = 2 * (D F G t / 2) := by
  have hb := D_abs_le_card hFG t
  have hev := (Int.mul_ediv_cancel' (D_even F G t)).symm
  refine ⟨mem_hRange ?_, hev⟩
  rw [abs_le] at hb ⊢
  omega

end one

end HP

end SolidGridHam
