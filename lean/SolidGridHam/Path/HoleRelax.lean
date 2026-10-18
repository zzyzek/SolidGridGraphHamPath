/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import SolidGridHam.Path.HoleAdm
public import SolidGridHam.Algorithm

@[expose] public section

/-!
# Hole classes: the relaxation (B-3, docs/HOLE_CLASSES.md §3.2, port of ulhc-hole `KHole2/3`)

`classPotential V F as hs`: the least admissible potential (`Adm V F`) with `φ a = h` for
`(a, h) ∈ as.zip hs`, found by monotone relaxation over the cells strictly inside the box of the
inner set `V` (`boxSquares V`), starting from `-boxWidth V` (`boxWidth V` the width of the box). `isAdmissible` tests the
result, and `jumpEdges V f` lists the edges of `V` where `f` jumps.

Everything here depends only on the inner set `V` and the reference factor `F`: factors on a box
set `W ⊇ V` agreeing with `F` off the edges of `V` have `D F · / 2` vanishing off `boxSquares V`
(`half_propsW`), so the box of `V` is enough.

* `relax_fix`: from below a solution `ψ`, relaxation stays below `ψ` and reaches a fixed point;
* `adm_of_fix`, `check_iff`: the fixed point is admissible, and `isAdmissible` says exactly that;
* `mem_kX`, `toF_kPot_off`: the jump set and the support of `classPotential`.
-/

namespace SolidGridHam

namespace HP

open Finset

/-! ## The box -/

lemma box_mem {V : Finset Pt} {p : Pt} (hp : p ∈ V) :
    bx0 V ≤ p.1 ∧ p.1 ≤ bx1 V ∧ by0 V ≤ p.2 ∧ p.2 ≤ by1 V := by
  have hn : V.Nonempty := ⟨p, hp⟩
  simp only [bx0, bx1, by0, by1, hn, dite_true]
  exact ⟨Finset.inf'_le _ hp, Finset.le_sup' _ hp, Finset.inf'_le _ hp, Finset.le_sup' _ hp⟩

lemma box_attain {V : Finset Pt} (hn : V.Nonempty) :
    (∃ p ∈ V, p.1 = bx0 V) ∧ (∃ p ∈ V, p.1 = bx1 V) ∧ (∃ p ∈ V, p.2 = by0 V) ∧
      ∃ p ∈ V, p.2 = by1 V := by
  simp only [bx0, bx1, by0, by1, hn, dite_true]
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨p, hp, h⟩ := Finset.exists_mem_eq_inf' hn Prod.fst; exact ⟨p, hp, h.symm⟩
  · obtain ⟨p, hp, h⟩ := Finset.exists_mem_eq_sup' hn Prod.fst; exact ⟨p, hp, h.symm⟩
  · obtain ⟨p, hp, h⟩ := Finset.exists_mem_eq_inf' hn Prod.snd; exact ⟨p, hp, h.symm⟩
  · obtain ⟨p, hp, h⟩ := Finset.exists_mem_eq_sup' hn Prod.snd; exact ⟨p, hp, h.symm⟩

lemma mem_kSq {V : Finset Pt} {c : Pt} :
    c ∈ boxSquares V ↔ bx0 V ≤ c.1 ∧ c.1 < bx1 V ∧ by0 V ≤ c.2 ∧ c.2 < by1 V := by
  obtain ⟨x, y⟩ := c
  unfold boxSquares
  constructor
  · intro h
    obtain ⟨i, hi, hj⟩ := List.mem_flatMap.1 h
    obtain ⟨j, hj, he⟩ := List.mem_map.1 hj
    rw [List.mem_range] at hi hj
    simp only [Prod.mk.injEq] at he
    simp only
    omega
  · rintro ⟨h1, h2, h3, h4⟩
    simp only at h1 h2 h3 h4
    refine List.mem_flatMap.2 ⟨(x - bx0 V).toNat, List.mem_range.2 (by omega), ?_⟩
    refine List.mem_map.2 ⟨(y - by0 V).toNat, List.mem_range.2 (by omega), ?_⟩
    simp only [Prod.mk.injEq]
    omega

/-! ## Potentials as lists -/

def toF (L : List (Pt × ℤ)) (c : Pt) : ℤ := (L.lookup c).getD 0

lemma lookup_map (S : List Pt) (g : Pt → ℤ) (c : Pt) :
    (S.map (fun s => (s, g s))).lookup c = if c ∈ S then some (g c) else none := by
  induction S with
  | nil => simp
  | cons s S ih =>
    simp only [List.map_cons, List.lookup_cons, List.mem_cons]
    by_cases h : c = s
    · subst h; simp
    · have : (c == s) = false := by simpa using h
      rw [this]; simp only [ih, h, false_or]

lemma toF_map (S : List Pt) (g : Pt → ℤ) (c : Pt) :
    toF (S.map (fun s => (s, g s))) c = if c ∈ S then g c else 0 := by
  unfold toF; rw [lookup_map]; split_ifs <;> rfl

def roundL (V : Finset Pt) (F : Finset Edge) (S : List Pt) (L : List (Pt × ℤ)) :
    List (Pt × ℤ) :=
  S.map fun s => (s, max (toF L s) (lowerBound V F (toF L) s))

def relax (V : Finset Pt) (F : Finset Edge) (S : List Pt) :
    ℕ → List (Pt × ℤ) → List (Pt × ℤ)
  | 0, L => L
  | n + 1, L =>
    let L' := roundL V F S L
    if L' = L then L else relax V F S n L'

-- Hole cells start at their values, other box cells at `-W`.
--
def kInit (V : Finset Pt) (as : List Pt) (hs : List ℤ) : List (Pt × ℤ) :=
  (boxSquares V).map fun s => (s, ((as.zip hs).lookup s).getD (- boxWidth V))

def kWide (V : Finset Pt) : Bool :=
  decide ((V.card : ℤ) ≤ bx1 V - bx0 V ∨ (V.card : ℤ) ≤ by1 V - by0 V)

/-! ## Relaxation -/

section relax

variable {V : Finset Pt} {F : Finset Edge} {S : List Pt}

lemma lowerBound_mono {f g : Pt → ℤ} (h : ∀ c, f c ≤ g c) (s : Pt) : lowerBound V F f s ≤ lowerBound V F g s := by
  unfold lowerBound
  have := h (bot s).lo; have := h (lft s).lo; have := h (top s).hi; have := h (rgt s).hi
  omega

def Shape (S : List Pt) (L : List (Pt × ℤ)) : Prop := L = S.map fun s => (s, toF L s)

lemma shape_map (g : Pt → ℤ) : Shape S (S.map fun s => (s, g s)) := by
  unfold Shape
  apply List.map_congr_left
  intro s hs
  rw [toF_map]; simp [hs]

lemma toF_roundL (L : List (Pt × ℤ)) (c : Pt) :
    toF (roundL V F S L) c = if c ∈ S then max (toF L c) (lowerBound V F (toF L) c) else 0 := by
  unfold roundL; rw [toF_map]

lemma shape_roundL (L : List (Pt × ℤ)) : Shape S (roundL V F S L) := by
  unfold roundL; exact shape_map _

lemma toF_off {L : List (Pt × ℤ)} (hL : Shape S L) {c : Pt} (hc : c ∉ S) : toF L c = 0 := by
  rw [hL, toF_map]; simp [hc]

-- `ψ` satisfies every lower bound on `S` and vanishes off `S`.
--
variable (ψ : Pt → ℤ) (hψ : ∀ s ∈ S, lowerBound V F ψ s ≤ ψ s) (hψ0 : ∀ c, c ∉ S → ψ c = 0)
include hψ hψ0

theorem relax_fix : ∀ (n : ℕ) (L : List (Pt × ℤ)), Shape S L → (∀ c, toF L c ≤ ψ c) →
    (∑ s ∈ S.toFinset, (ψ s - toF L s)) ≤ n →
    Shape S (relax V F S n L) ∧ (∀ c, toF (relax V F S n L) c ≤ ψ c) ∧
      (∀ c, toF L c ≤ toF (relax V F S n L) c) ∧
      ∀ s ∈ S, lowerBound V F (toF (relax V F S n L)) s ≤ toF (relax V F S n L) s := by
  intro n
  induction n with
  | zero =>
    intro L hL hle hsum
    refine ⟨hL, hle, fun c => le_rfl, fun s hs => ?_⟩
    have hnn : ∀ t ∈ S.toFinset, 0 ≤ ψ t - toF L t := fun t _ => by have := hle t; omega
    have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1
      (le_antisymm (by simpa using hsum) (Finset.sum_nonneg hnn)) s (List.mem_toFinset.2 hs)
    have := lowerBound_mono (V := V) (F := F) hle s
    have := hψ s hs
    simp only [relax]
    omega
  | succ n ih =>
    intro L hL hle hsum
    simp only [relax]
    split_ifs with heq
    · refine ⟨hL, hle, fun c => le_rfl, fun s hs => ?_⟩
      have := congrArg (fun L => toF L s) heq
      simp only [toF_roundL, hs, ite_true] at this
      omega
    · have hle' : ∀ c, toF (roundL V F S L) c ≤ ψ c := by
        intro c
        rw [toF_roundL]
        split_ifs with hc
        · have := lowerBound_mono (V := V) (F := F) hle c
          have := hψ c hc
          have := hle c
          omega
        · rw [hψ0 c hc]
      have hup : ∀ c, toF L c ≤ toF (roundL V F S L) c := by
        intro c
        rw [toF_roundL]
        split_ifs with hc
        · exact le_max_left _ _
        · rw [toF_off hL hc]
      have hne : ∃ s ∈ S, toF L s < toF (roundL V F S L) s := by
        by_contra hno
        push Not at hno
        apply heq
        rw [shape_roundL (S := S) (V := V) (F := F) L, hL]
        apply List.map_congr_left
        intro s hs
        have := hup s; have := hno s hs
        rw [← hL]
        congr 1
        omega
      obtain ⟨s0, hs0, hlt⟩ := hne
      have hsum' : (∑ s ∈ S.toFinset, (ψ s - toF (roundL V F S L) s)) ≤ n := by
        have : (∑ s ∈ S.toFinset, (ψ s - toF (roundL V F S L) s)) <
            ∑ s ∈ S.toFinset, (ψ s - toF L s) := by
          apply Finset.sum_lt_sum
          · intro t _; have := hup t; omega
          · exact ⟨s0, List.mem_toFinset.2 hs0, by omega⟩
        push_cast at hsum
        omega
      obtain ⟨a, b, c, d⟩ := ih _ (shape_roundL L) hle' hsum'
      exact ⟨a, b, fun x => (hup x).trans (c x), d⟩

end relax

/-! ## Few rounds suffice (Bellman–Ford)

If some `ψ` satisfies every lower bound, a cell that still rises in round `k + 1` has a neighbour
that rose in round `k`, and `ψ − f` does not decrease along such a chain. A chain longer than the
number of cells repeats a cell, where `ψ − f` would have to drop. So `|S| + 1` rounds reach the
fixed point (`relax_bf`).
-/

section bf

variable {V : Finset Pt} {F : Finset Edge} {S : List Pt}

lemma lowerBound_cases (f : Pt → ℤ) (s : Pt) :
    ∃ n a, lowerBound V F f s = f n + a ∧ ∀ g : Pt → ℤ, g n + a ≤ lowerBound V F g s := by
  unfold lowerBound
  rcases max_choice (max (f (bot s).lo + (ivl V F (bot s)).1) (f (lft s).lo + (ivl V F (lft s)).1))
    (max (f (top s).hi - (ivl V F (top s)).2) (f (rgt s).hi - (ivl V F (rgt s)).2)) with h | h <;>
    rw [h]
  · rcases max_choice (f (bot s).lo + (ivl V F (bot s)).1) (f (lft s).lo + (ivl V F (lft s)).1)
      with h' | h' <;> rw [h']
    · exact ⟨_, _, rfl, fun g => le_max_of_le_left (le_max_left _ _)⟩
    · exact ⟨_, _, rfl, fun g => le_max_of_le_left (le_max_right _ _)⟩
  · rcases max_choice (f (top s).hi - (ivl V F (top s)).2) (f (rgt s).hi - (ivl V F (rgt s)).2)
      with h' | h' <;> rw [h']
    · exact ⟨_, -(ivl V F (top s)).2, by ring, fun g => by
        have h1 := le_max_left (g (top s).hi - (ivl V F (top s)).2)
          (g (rgt s).hi - (ivl V F (rgt s)).2)
        have h2 := le_max_right (max (g (bot s).lo + (ivl V F (bot s)).1)
          (g (lft s).lo + (ivl V F (lft s)).1))
          (max (g (top s).hi - (ivl V F (top s)).2) (g (rgt s).hi - (ivl V F (rgt s)).2))
        linarith⟩
    · exact ⟨_, -(ivl V F (rgt s)).2, by ring, fun g => by
        have h1 := le_max_right (g (top s).hi - (ivl V F (top s)).2)
          (g (rgt s).hi - (ivl V F (rgt s)).2)
        have h2 := le_max_right (max (g (bot s).lo + (ivl V F (bot s)).1)
          (g (lft s).lo + (ivl V F (lft s)).1))
          (max (g (top s).hi - (ivl V F (top s)).2) (g (rgt s).hi - (ivl V F (rgt s)).2))
        linarith⟩

lemma relax_cases : ∀ (n : ℕ) (L : List (Pt × ℤ)),
    (∃ m, roundL V F S ((roundL V F S)^[m] L) = (roundL V F S)^[m] L ∧
      relax V F S n L = (roundL V F S)^[m] L) ∨ relax V F S n L = (roundL V F S)^[n] L := by
  intro n
  induction n with
  | zero => intro L; right; rfl
  | succ n ih =>
    intro L
    simp only [relax]
    split_ifs with h
    · exact Or.inl ⟨0, h, rfl⟩
    · rcases ih (roundL V F S L) with ⟨m, h1, h2⟩ | h2
      · left; refine ⟨m + 1, ?_, ?_⟩
        · rw [Function.iterate_succ_apply]; exact h1
        · rw [Function.iterate_succ_apply]; exact h2
      · right; rw [Function.iterate_succ_apply]; exact h2

variable (ψ : Pt → ℤ) (hψ : ∀ s ∈ S, lowerBound V F ψ s ≤ ψ s) (hψ0 : ∀ c, c ∉ S → ψ c = 0)
  {L0 : List (Pt × ℤ)} (hL0 : Shape S L0) (hle0 : ∀ c, toF L0 c ≤ ψ c)
include hψ hψ0 hL0 hle0

lemma iter_props : ∀ m, Shape S ((roundL V F S)^[m] L0) ∧
    (∀ c, toF ((roundL V F S)^[m] L0) c ≤ ψ c) ∧ ∀ c, toF L0 c ≤ toF ((roundL V F S)^[m] L0) c := by
  intro m
  induction m with
  | zero => exact ⟨hL0, hle0, fun c => le_rfl⟩
  | succ m ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    rw [Function.iterate_succ_apply']
    refine ⟨shape_roundL _, fun c => ?_, fun c => ?_⟩
    · rw [toF_roundL]
      split_ifs with hc
      · have := lowerBound_mono (V := V) (F := F) h2 c
        have := hψ c hc
        have := h2 c
        omega
      · rw [hψ0 c hc]
    · rw [toF_roundL]
      split_ifs with hc
      · exact (h3 c).trans (le_max_left _ _)
      · rw [← toF_off h1 hc]; exact h3 c

theorem relax_bf (n : ℕ) (hn : S.toFinset.card + 1 ≤ n) :
    Shape S (relax V F S n L0) ∧ (∀ c, toF (relax V F S n L0) c ≤ ψ c) ∧
      (∀ c, toF L0 c ≤ toF (relax V F S n L0) c) ∧
      ∀ s ∈ S, lowerBound V F (toF (relax V F S n L0)) s ≤ toF (relax V F S n L0) s := by
  set Fk : ℕ → Pt → ℤ := fun k => toF ((roundL V F S)^[k] L0) with hFk
  have hP := iter_props ψ hψ hψ0 hL0 hle0
  have hstep : ∀ k c, Fk (k + 1) c = if c ∈ S then max (Fk k c) (lowerBound V F (Fk k) c) else 0 := by
    intro k c
    simp only [hFk]
    rw [Function.iterate_succ_apply', toF_roundL]
  have hmono1 : ∀ k c, Fk k c ≤ Fk (k + 1) c := by
    intro k c
    rw [hstep]
    split_ifs with hc
    · exact le_max_left _ _
    · rw [← toF_off (hP k).1 hc]
  have hmono : ∀ a b c, a ≤ b → Fk a c ≤ Fk b c := by
    intro a b c hab
    induction hab with
    | refl => exact le_rfl
    | step _ ih => exact ih.trans (hmono1 _ c)
  -- a rise at round `k + 2` comes from a rise of a neighbour at round `k + 1`
  have hrise : ∀ k s, Fk (k + 1) s < Fk (k + 2) s → ∃ n, n ∈ S ∧ Fk k n < Fk (k + 1) n ∧
      ψ n - Fk (k + 1) n ≤ ψ s - Fk (k + 2) s := by
    intro k s hlt
    have hs : s ∈ S := by
      by_contra hs
      rw [hstep (k + 1), ite_eq_right hs, hstep k, ite_eq_right hs] at hlt
      exact lt_irrefl _ hlt
    rw [hstep (k + 1), ite_eq_left hs] at hlt ⊢
    have hlb : Fk (k + 1) s < lowerBound V F (Fk (k + 1)) s := by
      by_contra h; push Not at h; rw [max_eq_left h] at hlt; exact lt_irrefl _ hlt
    rw [max_eq_right hlb.le] at hlt ⊢
    obtain ⟨n, a, h1, h2⟩ := lowerBound_cases (V := V) (F := F) (Fk (k + 1)) s
    have hk1 : Fk k n + a ≤ Fk (k + 1) s := by
      have := h2 (Fk k)
      rw [hstep k, ite_eq_left hs] at *
      exact this.trans (le_max_right _ _)
    have hψs := (h2 ψ).trans (hψ s hs)
    have hnr : Fk k n < Fk (k + 1) n := by rw [h1] at hlt; linarith
    have hn : n ∈ S := by
      by_contra hn
      rw [hstep k, ite_eq_right hn, show Fk k n = 0 from ?_] at hnr
      · exact lt_irrefl _ hnr
      · rcases k with _ | k
        · exact toF_off hL0 hn
        · rw [hstep k, ite_eq_right hn]
    refine ⟨n, hn, hnr, ?_⟩
    rw [h1]; linarith
  -- chains of rises
  have hchain : ∀ k s, Fk k s < Fk (k + 1) s → ∃ c : ℕ → Pt, c k = s ∧
      (∀ j ≤ k, c j ∈ S ∧ Fk j (c j) < Fk (j + 1) (c j)) ∧
      ∀ j < k, ψ (c j) - Fk (j + 1) (c j) ≤ ψ (c (j + 1)) - Fk (j + 2) (c (j + 1)) := by
    intro k
    induction k with
    | zero =>
      intro s h
      have hs : s ∈ S := by
        by_contra hs
        rw [hstep 0, ite_eq_right hs, show Fk 0 s = 0 from toF_off hL0 hs] at h
        exact lt_irrefl _ h
      exact ⟨fun _ => s, rfl, fun j hj => by
        obtain rfl : j = 0 := by omega
        exact ⟨hs, h⟩, fun j hj => by omega⟩
    | succ k ih =>
      intro s h
      obtain ⟨n, hn, hnr, hd⟩ := hrise k s h
      obtain ⟨c, hck, hc1, hc2⟩ := ih n hnr
      refine ⟨Function.update c (k + 1) s, by simp, fun j hj => ?_, fun j hj => ?_⟩
      · rcases Nat.lt_or_ge j (k + 1) with hj' | hj'
        · rw [Function.update_of_ne (by omega)]; exact hc1 j (by omega)
        · obtain rfl : j = k + 1 := by omega
          rw [Function.update_self]
          have hs : s ∈ S := by
            by_contra hs
            rw [hstep (k + 1), ite_eq_right hs, hstep k, ite_eq_right hs] at h
            exact lt_irrefl _ h
          exact ⟨hs, h⟩
      · rcases Nat.lt_or_ge j k with hj' | hj'
        · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          exact hc2 j hj'
        · obtain rfl : j = k := by omega
          rw [Function.update_of_ne (by omega), Function.update_self, hck]
          exact hd
  -- no rise after `|S|` rounds
  have hnorise : ∀ k, S.toFinset.card ≤ k → ∀ s, ¬ Fk k s < Fk (k + 1) s := by
    intro k hk s h
    obtain ⟨c, _, hc1, hc2⟩ := hchain k s h
    obtain ⟨i, hi, j, hj, hij, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
      (s := Finset.range (k + 1)) (t := S.toFinset) (f := c) (by simp; omega)
      (fun a ha => List.mem_toFinset.2 (hc1 a (by simp at ha; omega)).1)
    simp only [Finset.mem_range] at hi hj
    have hD : ∀ a b, a ≤ b → b ≤ k → ψ (c a) - Fk (a + 1) (c a) ≤ ψ (c b) - Fk (b + 1) (c b) := by
      intro a b hab hbk
      induction hab with
      | refl => exact le_rfl
      | step hle ih =>
        exact (ih (by omega)).trans (hc2 _ (by omega))
    rcases Nat.lt_or_gt_of_ne hij with hlt | hlt
    · have h1 := hD i j hlt.le (by omega)
      have h2 := (hc1 j (by omega)).2
      have h3 := hmono (i + 1) j (c j) (by omega)
      rw [heq] at h1
      linarith
    · have h1 := hD j i hlt.le (by omega)
      have h2 := (hc1 i (by omega)).2
      have h3 := hmono (j + 1) i (c i) (by omega)
      rw [← heq] at h1
      linarith
  rcases relax_cases (V := V) (F := F) (S := S) n L0 with ⟨m, hfix, hR⟩ | hR
  · rw [hR]
    obtain ⟨a, b, c⟩ := hP m
    refine ⟨a, b, c, fun s hs => ?_⟩
    have := congrArg (fun L => toF L s) hfix
    simp only [toF_roundL, hs, ite_true] at this
    omega
  · rw [hR]
    obtain ⟨a, b, c⟩ := hP n
    refine ⟨a, b, c, fun s hs => ?_⟩
    have h1 := hnorise n (by omega) s
    have h2 := hstep n s
    simp only [hFk] at h1 h2
    rw [ite_eq_left hs] at h2
    push Not at h1
    have := le_max_right (toF ((roundL V F S)^[n] L0) s) (lowerBound V F (toF ((roundL V F S)^[n] L0)) s)
    omega

end bf

/-! ## Potentials as arrays

The relaxation stores the potential in an array indexed by the box position, so that every lookup
is one step. `relaxA` computes exactly what `relax` computes on association lists (`toFA_relaxA`).
-/

lemma inBox_iff {V : Finset Pt} {c : Pt} : inBox V c ↔ c ∈ boxSquares V := by
  rw [mem_kSq]; rfl

lemma idx_lt {V : Finset Pt} {c : Pt} (h : inBox V c) : idx V c < kWn V * kHn V := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  unfold idx kWn kHn
  have ha : (c.1 - bx0 V).toNat + 1 ≤ (bx1 V - bx0 V).toNat := by omega
  have hb : (c.2 - by0 V).toNat < (by1 V - by0 V).toNat := by omega
  calc (c.1 - bx0 V).toNat * (by1 V - by0 V).toNat + (c.2 - by0 V).toNat
      < ((c.1 - bx0 V).toNat + 1) * (by1 V - by0 V).toNat := by nlinarith
    _ ≤ (bx1 V - bx0 V).toNat * (by1 V - by0 V).toNat := Nat.mul_le_mul_right _ ha

lemma cellOf_idx {V : Finset Pt} {c : Pt} (h : inBox V c) : cellOf V (idx V c) = c := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hH : 0 < kHn V := by unfold kHn; omega
  have hb : (c.2 - by0 V).toNat < kHn V := by unfold kHn; omega
  unfold cellOf idx
  rw [Nat.mul_comm, Nat.mul_add_div hH, Nat.div_eq_of_lt hb, Nat.add_zero, Nat.mul_add_mod,
    Nat.mod_eq_of_lt hb]
  obtain ⟨x, y⟩ := c
  simp only at h1 h3 ⊢
  ext <;> simp <;> omega

lemma inBox_cellOf {V : Finset Pt} {k : ℕ} (hk : k < kWn V * kHn V) : inBox V (cellOf V k) := by
  have hH : 0 < kHn V := by
    rcases Nat.eq_zero_or_pos (kHn V) with h | h
    · rw [h, Nat.mul_zero] at hk; omega
    · exact h
  have h1 : k / kHn V < kWn V := (Nat.div_lt_iff_lt_mul hH).2 hk
  have h2 : k % kHn V < kHn V := Nat.mod_lt _ hH
  have hW : kWn V = (bx1 V - bx0 V).toNat := rfl
  have hH' : kHn V = (by1 V - by0 V).toNat := rfl
  unfold inBox cellOf
  generalize k / kHn V = a at h1 ⊢
  generalize k % kHn V = b at h2 ⊢
  simp only
  omega

lemma toFA_ofFn {V : Finset Pt} (g : Pt → ℤ) (c : Pt) :
    toFA V (Array.ofFn (n := kWn V * kHn V) (fun k => g (cellOf V k))) c =
      if c ∈ boxSquares V then g c else 0 := by
  unfold toFA
  by_cases h : inBox V c
  · rw [ite_eq_left h, ite_eq_left (inBox_iff.1 h)]
    have hl := idx_lt h
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
    simp only [hl, ↓reduceDIte, Option.getD_some]
    rw [cellOf_idx h]
  · rw [ite_eq_right h, ite_eq_right (fun h' => h (inBox_iff.2 h'))]

lemma toFA_roundA (V : Finset Pt) (F : Finset Edge) (A : Array ℤ) (c : Pt) :
    toFA V (roundA V F A) c =
      if c ∈ boxSquares V then max (toFA V A c) (lowerBound V F (toFA V A) c) else 0 :=
  toFA_ofFn (fun c => max (toFA V A c) (lowerBound V F (toFA V A) c)) c

lemma shape_eq_iff {S : List Pt} {L L' : List (Pt × ℤ)} (hL : Shape S L) (hL' : Shape S L') :
    L' = L ↔ ∀ c ∈ S, toF L' c = toF L c := by
  constructor
  · rintro rfl _ _; rfl
  · intro h
    rw [hL', hL]
    exact List.map_congr_left (fun c hc => by rw [h c hc])

-- **The array relaxation simulates the list relaxation.**
--
theorem toFA_relaxA {V : Finset Pt} {F : Finset Edge} :
    ∀ n (A : Array ℤ) (L : List (Pt × ℤ)), Shape (boxSquares V) L → (∀ c, toFA V A c = toF L c) →
      ∀ c, toFA V (relaxA V F n A) c = toF (relax V F (boxSquares V) n L) c := by
  intro n
  induction n with
  | zero => intro A L _ h c; exact h c
  | succ n ih =>
    intro A L hL h
    have hf : toFA V A = toF L := funext h
    have hR : ∀ c, toFA V (roundA V F A) c = toF (roundL V F (boxSquares V) L) c := by
      intro c; rw [toFA_roundA, toF_roundL, hf]
    have hstop : (boxSquares V).all (fun c => toFA V (roundA V F A) c == toFA V A c) = true ↔
        roundL V F (boxSquares V) L = L := by
      rw [shape_eq_iff hL (shape_roundL L), List.all_eq_true]
      simp only [beq_iff_eq, hR, h]
    simp only [relaxA, relax]
    by_cases hs : roundL V F (boxSquares V) L = L
    · rw [ite_eq_left (hstop.2 hs), ite_eq_left hs]; exact h
    · rw [ite_eq_right (fun h' => hs (hstop.1 h')), ite_eq_right hs]
      exact ih _ _ (shape_roundL L) hR

lemma classPotential_eq {V : Finset Pt} {F : Finset Edge} {as : List Pt} {hs : List ℤ} :
    classPotential V F as hs = toF (relax V F (boxSquares V) (kFuel V) (kInit V as hs)) := by
  funext c
  apply toFA_relaxA _ _ _ (shape_map _)
  intro c'
  unfold kInitA
  rw [toFA_ofFn (fun c => ((as.zip hs).lookup c).getD (- boxWidth V)), toF_map]

/-! ## Intervals -/

lemma adm_ivl {V : Finset Pt} {F : Finset Edge} {φ : Pt → ℤ} (hA : Adm V F φ) (e : Edge) :
    (ivl V F e).1 ≤ φ e.hi - φ e.lo ∧ φ e.hi - φ e.lo ≤ (ivl V F e).2 := by
  unfold ivl
  rcases hA e with h | ⟨hE, h⟩
  · split_ifs <;> simp [h]
  · simp only [hE, ite_true, h]
    unfold sv; split_ifs <;> simp

lemma ivl_adm {V : Finset Pt} {F : Finset Edge} {φ : Pt → ℤ} {e : Edge}
    (h1 : (ivl V F e).1 ≤ φ e.hi - φ e.lo) (h2 : φ e.hi - φ e.lo ≤ (ivl V F e).2) :
    φ e.hi - φ e.lo = 0 ∨ (IsEdge V e ∧ φ e.hi - φ e.lo = sv F e) := by
  unfold ivl at h1 h2
  split_ifs at h1 h2 with hE
  · by_cases j0 : φ e.hi - φ e.lo = 0
    · exact Or.inl j0
    · right
      refine ⟨hE, ?_⟩
      rcases (show sv F e = 1 ∨ sv F e = -1 by unfold sv; split_ifs <;> simp) with h | h <;>
        rw [h] at h1 h2 ⊢ <;> simp at h1 h2 <;> omega
  · left; simp at h1 h2; omega

-- The bound at the high cell of `e` includes `e`, and so does the bound at its low cell.
--
lemma lowerBound_hi (V : Finset Pt) (F : Finset Edge) (f : Pt → ℤ) (e : Edge) :
    f e.lo + (ivl V F e).1 ≤ lowerBound V F f e.hi := by
  obtain ⟨d, p⟩ := e
  unfold lowerBound
  cases d
  · have : bot p = ⟨.h, p⟩ := rfl
    simp only [Edge.hi_mk, this]
    omega
  · have : lft p = ⟨.v, p⟩ := rfl
    simp only [Edge.hi_mk, this]
    omega

lemma lowerBound_lo (V : Finset Pt) (F : Finset Edge) (f : Pt → ℤ) (e : Edge) :
    f e.hi - (ivl V F e).2 ≤ lowerBound V F f e.lo := by
  obtain ⟨⟨⟩, ⟨x, y⟩⟩ := e
  · have : top (x, y - 1) = ⟨.h, (x, y)⟩ := by simp [top]
    unfold lowerBound
    simp only [Edge.lo_h, Edge.hi_mk, this]
    omega
  · have : rgt (x - 1, y) = ⟨.v, (x, y)⟩ := by simp [rgt]
    unfold lowerBound
    simp only [Edge.lo_v, Edge.hi_mk, this]
    omega

lemma lowerBound_le_of_adm {V : Finset Pt} {F : Finset Edge} {ψ : Pt → ℤ} (hA : Adm V F ψ) (s : Pt) :
    lowerBound V F ψ s ≤ ψ s := by
  have b := (adm_ivl hA (bot s)).1
  have l := (adm_ivl hA (lft s)).1
  have t := (adm_ivl hA (top s)).2
  have r := (adm_ivl hA (rgt s)).2
  have hb : (bot s).hi = s := rfl
  have hl : (lft s).hi = s := rfl
  have ht : (top s).lo = s := by simp [top]
  have hr : (rgt s).lo = s := by simp [rgt]
  rw [hb] at b; rw [hl] at l; rw [ht] at t; rw [hr] at r
  unfold lowerBound
  omega

/-! ## The fixed point passes the check -/

section fix

variable {V : Finset Pt} {F : Finset Edge} {S : List Pt} {f ψ : Pt → ℤ}

theorem adm_of_fix (hA : Adm V F ψ) (hψ0 : ∀ c, c ∉ S → ψ c = 0) (hf0 : ∀ c, c ∉ S → f c = 0)
    (hle : ∀ c, f c ≤ ψ c) (hlb : ∀ s ∈ S, lowerBound V F f s ≤ f s) : Adm V F f := by
  intro e
  have hψ := adm_ivl hA e
  apply ivl_adm
  · by_cases hs : e.hi ∈ S
    · have := lowerBound_hi V F f e; have := hlb _ hs; omega
    · have := hle e.lo; rw [hf0 _ hs]; rw [hψ0 _ hs] at hψ; omega
  · by_cases hs : e.lo ∈ S
    · have := lowerBound_lo V F f e; have := hlb _ hs; omega
    · have := hle e.hi; rw [hf0 _ hs]; rw [hψ0 _ hs] at hψ; omega

end fix

lemma mem_sides_hi (e : Edge) : e ∈ sides e.hi := by
  obtain ⟨⟨⟩, p⟩ := e <;> simp [sides, bot, lft]

lemma mem_sides_lo (e : Edge) : e ∈ sides e.lo := by
  obtain ⟨⟨⟩, ⟨x, y⟩⟩ := e <;> simp [sides, top, rgt]

theorem check_iff {V : Finset Pt} {F : Finset Edge} {as : List Pt} {hs : List ℤ} {f : Pt → ℤ}
    (hf0 : ∀ c, c ∉ boxSquares V → f c = 0) :
    isAdmissible V F as hs f = true ↔ Adm V F f ∧ ∀ ah ∈ as.zip hs, f ah.1 = ah.2 := by
  unfold isAdmissible
  simp only [Bool.and_eq_true, List.all_eq_true, sideOK, decide_eq_true_eq, beq_iff_eq]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun e => ?_, h2⟩
    by_cases hh : e.hi ∈ boxSquares V
    · exact h1 _ hh e (mem_sides_hi e)
    · by_cases hl : e.lo ∈ boxSquares V
      · exact h1 _ hl e (mem_sides_lo e)
      · left; rw [hf0 _ hh, hf0 _ hl]; simp
  · rintro ⟨h1, h2⟩
    exact ⟨fun s _ e _ => h1 e, h2⟩

theorem mem_kX {V : Finset Pt} {f : Pt → ℤ} (hf0 : ∀ c, c ∉ boxSquares V → f c = 0) (e : Edge) :
    e ∈ jumpEdges V f ↔ IsEdge V e ∧ f e.hi ≠ f e.lo := by
  unfold jumpEdges
  simp only [List.mem_toFinset, List.mem_filter, List.mem_flatMap, decide_eq_true_eq]
  constructor
  · rintro ⟨_, h⟩; exact h
  · rintro ⟨hE, hne⟩
    refine ⟨?_, hE, hne⟩
    by_cases hh : e.hi ∈ boxSquares V
    · exact ⟨_, hh, mem_sides_hi e⟩
    · by_cases hl : e.lo ∈ boxSquares V
      · exact ⟨_, hl, mem_sides_lo e⟩
      · exact absurd (by rw [hf0 _ hh, hf0 _ hl]) hne

/-! ## Lists -/

lemma mem_zip_map {g : Pt → ℤ} : ∀ (l : List Pt) (ah : Pt × ℤ), ah ∈ l.zip (l.map g) → ah.2 = g ah.1
  | [], _, h => by simp at h
  | a :: l, ah, h => by
    simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at h
    rcases h with rfl | h
    · rfl
    · exact mem_zip_map l ah h

lemma mem_of_lookup {c : Pt} {h : ℤ} : ∀ l : List (Pt × ℤ), l.lookup c = some h → (c, h) ∈ l
  | [], hl => by simp at hl
  | (a, b) :: l, hl => by
    simp only [List.lookup_cons] at hl
    by_cases hc : c = a
    · subst hc; simp at hl; subst hl; simp
    · have : (c == a) = false := by simpa using hc
      rw [this] at hl
      exact List.mem_cons_of_mem _ (mem_of_lookup l hl)

lemma lookup_ne_none {c : Pt} {h : ℤ} : ∀ l : List (Pt × ℤ), (c, h) ∈ l → l.lookup c ≠ none
  | [], hm => by simp at hm
  | (a, b) :: l, hm => by
    simp only [List.lookup_cons]
    by_cases hc : c = a
    · subst hc; simp
    · have : (c == a) = false := by simpa using hc
      rw [this]
      simp only [List.mem_cons, Prod.mk.injEq, hc, false_and, false_or] at hm
      exact lookup_ne_none l hm

theorem toF_kPot_off {V : Finset Pt} {F : Finset Edge} {as : List Pt} {hs : List ℤ} :
    ∀ c, c ∉ boxSquares V → classPotential V F as hs c = 0 := by
  intro c hc
  rw [classPotential_eq]
  have : ∀ n L, Shape (boxSquares V) L → Shape (boxSquares V) (relax V F (boxSquares V) n L) := by
    intro n
    induction n with
    | zero => intro L h; exact h
    | succ n ih =>
      intro L h
      simp only [relax]
      split_ifs
      · exact h
      · exact ih _ (shape_roundL L)
  exact toF_off (this _ _ (shape_map _)) hc

-- **P6.** For factors on `W` agreeing off the edges of `V`, `D F G / 2` vanishes off the box
-- cells of `V` and lies in `[-boxWidth V, boxWidth V]`.
--
theorem half_propsW {V W : Finset Pt} {d : Pt → ℕ} {F G : Finset Edge} (hF : IsFactor W d F)
    (hG : IsFactor W d G) (hFG : ∀ e ∈ symmDiff F G, IsEdge V e) :
    (∀ c, c ∉ boxSquares V → D F G c / 2 = 0) ∧ ∀ c, |D F G c / 2| ≤ boxWidth V := by
  have hbox : ∀ p ∈ V, bx0 V ≤ p.1 ∧ p.1 ≤ bx1 V ∧ by0 V ≤ p.2 ∧ p.2 ≤ by1 V :=
    fun p hp => box_mem hp
  have off : ∀ c, c ∉ boxSquares V → D F G c / 2 = 0 := by
    intro c hc
    rw [mem_kSq] at hc
    have : D F G c = 0 := by
      by_cases h1 : c.1 < bx0 V
      · exact D_zero_left hFG hbox c h1
      · by_cases h2 : bx1 V ≤ c.1
        · exact D_zero_right hF hG hFG hbox c h2
        · exact D_zero_row hFG hbox (by omega)
    rw [this]; simp
  refine ⟨off, fun c => ?_⟩
  by_cases hc : c ∈ boxSquares V
  · have := D_half_abs hF hG hFG hbox c
    rw [mem_kSq] at hc
    unfold boxWidth
    have : max 0 (c.1 - bx0 V + 1) ≤ bx1 V - bx0 V := by omega
    omega
  · rw [off c hc]; simp [boxWidth]
    rcases Finset.eq_empty_or_nonempty V with hV | hV
    · simp [bx0, bx1, hV]
    · obtain ⟨p, hp⟩ := hV
      have := box_mem hp
      omega

end HP

end SolidGridHam
