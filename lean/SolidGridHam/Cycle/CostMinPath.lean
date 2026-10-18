/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import SolidGridHam.Cycle.MinPath

@[expose] public section

/-!
# Running time, part 3: the minimum-path search

Costs of `MP.minPathL` and `MP.minPath`, for given costs `ec x y` of an `edge` evaluation and
`sc x` of a `src` evaluation (`mid`, `tgt`, `w` cost one step each). A table lookup scans the
association list. With `n = |NL|`, `ec ≤ E` and `sc ≤ S` on `NL`:

`minPathLCost ≤ n² (n (E + n + 5) + 4) + n (S + n + 3) + n + 4`  (`minPathLCost_le`).
-/

namespace SolidGridHam.MP

variable {α : Type} [DecidableEq α]

def lookCost {β : Type} (tbl : List (α × β)) : ℕ := tbl.length + 1

-- One update at `x`: the target and middle tests, and for a middle node one `edge`
-- evaluation, one lookup, one extension and one comparison per candidate `y`.
--
def stepCost (NL : List α) (mid tgt : α → Bool) (ec : α → α → ℕ)
    (tbl : List (α × Option (ℕ × List α))) (x : α) : ℕ :=
  1 + (if tgt x then 2 else 1 + (if mid x then (NL.map fun y => ec x y + lookCost tbl + 4).sum + 1
    else 0))

def nextCost (NL : List α) (mid tgt : α → Bool) (ec : α → α → ℕ)
    (tbl : List (α × Option (ℕ × List α))) : ℕ :=
  (NL.map fun x => stepCost NL mid tgt ec tbl x + 1).sum

def layerCost (NL : List α) (mid tgt : α → Bool) (edge : α → α → Bool) (w : α → ℕ)
    (ec : α → α → ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => layerCost NL mid tgt edge w ec k + nextCost NL mid tgt ec (layer NL mid tgt edge w k)

def pickSrcCost (NL : List α) (sc : α → ℕ) (tbl : List (α × Option (ℕ × List α))) : ℕ :=
  (NL.map fun x => sc x + lookCost tbl + 2).sum + 2

def minPathLCost (NL : List α) (mid tgt : α → Bool) (edge : α → α → Bool) (w : α → ℕ)
    (ec : α → α → ℕ) (sc : α → ℕ) : ℕ :=
  layerCost NL mid tgt edge w ec NL.length + pickSrcCost NL sc (layer NL mid tgt edge w NL.length) +
    NL.length + 1

lemma length_layer (NL : List α) (mid tgt : α → Bool) (edge : α → α → Bool) (w : α → ℕ) :
    ∀ k, (layer NL mid tgt edge w k).length ≤ NL.length
  | 0 => by simp [layer]
  | k + 1 => by simp [layer, next]

lemma sum_map_le {γ : Type} (l : List γ) (f : γ → ℕ) (b : ℕ) (h : ∀ x ∈ l, f x ≤ b) :
    (l.map f).sum ≤ l.length * b := by
  have := List.sum_le_length_nsmul (l.map f) b (by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
    exact h x hx)
  simpa using this

section bound

variable (NL : List α) (mid tgt : α → Bool) (edge : α → α → Bool) (w : α → ℕ)
  (ec : α → α → ℕ) (sc : α → ℕ) {E S : ℕ}
  (hE : ∀ x ∈ NL, ∀ y ∈ NL, ec x y ≤ E) (hS : ∀ x ∈ NL, sc x ≤ S)

include hE in
omit [DecidableEq α] in
lemma stepCost_le (tbl : List (α × Option (ℕ × List α))) (ht : tbl.length ≤ NL.length)
    {x : α} (hx : x ∈ NL) :
    stepCost NL mid tgt ec tbl x ≤ NL.length * (E + NL.length + 5) + 3 := by
  have h := sum_map_le NL (fun y => ec x y + lookCost tbl + 4) (E + NL.length + 5)
    (fun y hy => by have := hE x hx y hy; unfold lookCost; omega)
  unfold stepCost
  split_ifs <;> omega

include hE in
omit [DecidableEq α] in
lemma nextCost_le (tbl : List (α × Option (ℕ × List α))) (ht : tbl.length ≤ NL.length) :
    nextCost NL mid tgt ec tbl ≤ NL.length * (NL.length * (E + NL.length + 5) + 4) :=
  sum_map_le NL _ _ (fun x hx => by
    have := stepCost_le NL mid tgt ec hE tbl ht hx; omega)

include hE in
lemma layerCost_le : ∀ k, layerCost NL mid tgt edge w ec k ≤
    1 + k * (NL.length * (NL.length * (E + NL.length + 5) + 4)) := by
  intro k
  induction k with
  | zero => simp [layerCost]
  | succ k ih =>
    simp only [layerCost]
    have := nextCost_le NL mid tgt ec hE _ (length_layer NL mid tgt edge w k)
    rw [Nat.succ_mul]
    omega

include hE hS in
lemma minPathLCost_le : minPathLCost NL mid tgt edge w ec sc ≤
    NL.length * (NL.length * (NL.length * (E + NL.length + 5) + 4)) +
      NL.length * (S + NL.length + 3) + NL.length + 4 := by
  have h1 := layerCost_le NL mid tgt edge w ec hE NL.length
  have h2 := sum_map_le NL (fun x => sc x + lookCost (layer NL mid tgt edge w NL.length) + 2)
    (S + NL.length + 3) (fun x hx => by
      have := hS x hx
      have := length_layer NL mid tgt edge w NL.length
      unfold lookCost; omega)
  unfold minPathLCost pickSrcCost
  omega

end bound

/-! ## Monotonicity in the test costs -/

section mono

variable (NL : List α) (mid tgt : α → Bool) (edge : α → α → Bool) (w : α → ℕ)
  {ec ec' : α → α → ℕ} {sc sc' : α → ℕ} (hE : ∀ x y, ec x y ≤ ec' x y) (hS : ∀ x, sc x ≤ sc' x)

lemma lsum_mono' {γ : Type} (l : List γ) (f g : γ → ℕ) (h : ∀ x, f x ≤ g x) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a tf ih => simp only [List.map_cons, List.sum_cons]; exact Nat.add_le_add (h a) ih

include hE in
omit [DecidableEq α] in
lemma stepCost_mono (tbl : List (α × Option (ℕ × List α))) (x : α) :
    stepCost NL mid tgt ec tbl x ≤ stepCost NL mid tgt ec' tbl x := by
  have := lsum_mono' NL (fun y => ec x y + lookCost tbl + 4) (fun y => ec' x y + lookCost tbl + 4)
    (fun y => by have := hE x y; omega)
  unfold stepCost
  split_ifs <;> omega

include hE in
lemma layerCost_mono : ∀ k, layerCost NL mid tgt edge w ec k ≤ layerCost NL mid tgt edge w ec' k
  | 0 => le_rfl
  | k + 1 => by
    simp only [layerCost, nextCost]
    have := layerCost_mono k
    have := lsum_mono' NL (fun x => stepCost NL mid tgt ec (layer NL mid tgt edge w k) x + 1)
      (fun x => stepCost NL mid tgt ec' (layer NL mid tgt edge w k) x + 1)
      (fun x => by have := stepCost_mono NL mid tgt hE (layer NL mid tgt edge w k) x; omega)
    omega

include hE hS in
lemma minPathLCost_mono : minPathLCost NL mid tgt edge w ec sc ≤ minPathLCost NL mid tgt edge w ec' sc' := by
  have h1 := layerCost_mono NL mid tgt edge w hE NL.length
  have h2 := lsum_mono' NL (fun x => sc x + lookCost (layer NL mid tgt edge w NL.length) + 2)
    (fun x => sc' x + lookCost (layer NL mid tgt edge w NL.length) + 2) (fun x => by have := hS x; omega)
  unfold minPathLCost pickSrcCost
  omega

end mono

-- The `Finset` front end: sort, then search.
--
def minPathCost {β : Type} [LinearOrder β] (N : Finset β) (mid tgt : β → Bool)
    (edge : β → β → Bool) (w : β → ℕ) (ec : β → β → ℕ) (sc : β → ℕ) : ℕ :=
  N.card ^ 2 + minPathLCost (N.sort (· ≤ ·)) mid tgt edge w ec sc

theorem minPathCost_le {β : Type} [LinearOrder β] (N : Finset β) (mid tgt : β → Bool)
    (edge : β → β → Bool) (w : β → ℕ) (ec : β → β → ℕ) (sc : β → ℕ) {E S : ℕ}
    (hE : ∀ x ∈ N, ∀ y ∈ N, ec x y ≤ E) (hS : ∀ x ∈ N, sc x ≤ S) :
    minPathCost N mid tgt edge w ec sc ≤
      N.card ^ 2 + N.card * (N.card * (N.card * (E + N.card + 5) + 4)) +
        N.card * (S + N.card + 3) + N.card + 4 := by
  have h := minPathLCost_le (N.sort (· ≤ ·)) mid tgt edge w ec sc
    (fun x hx y hy => hE x (by simpa using hx) y (by simpa using hy))
    (fun x hx => hS x (by simpa using hx))
  rw [Finset.length_sort] at h
  unfold minPathCost
  omega

theorem minPathCost_mono {β : Type} [LinearOrder β] (N : Finset β) (mid tgt : β → Bool)
    (edge : β → β → Bool) (w : β → ℕ) {ec ec' : β → β → ℕ} {sc sc' : β → ℕ}
    (hE : ∀ x y, ec x y ≤ ec' x y) (hS : ∀ x, sc x ≤ sc' x) :
    minPathCost N mid tgt edge w ec sc ≤ minPathCost N mid tgt edge w ec' sc' := by
  have := minPathLCost_mono (N.sort (· ≤ ·)) mid tgt edge w hE hS
  unfold minPathCost
  omega

end SolidGridHam.MP
