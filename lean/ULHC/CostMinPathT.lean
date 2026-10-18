/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.CostMinPath

/-!
# Minimum-path search cost with a charged target test

Costs of `MP.minPathL` and `MP.minPath`, for given costs `ec x y` of an `edge` evaluation,
`sc x` of a `src` evaluation and `tc x` of a `tgt` evaluation (`mid`, `w` cost one step each). A table lookup scans the
association list. With `n = |NL|`, `ec ≤ E` and `sc ≤ S` on `NL`:

With `tc ≤ T` as well: `minPathLCostT ≤ n² (n (E + n + 5) + 4 + T) + n (S + n + 3) + n + 4` (`minPathLCostT_le`).
-/

namespace ULHC.MP

variable {α : Type} [DecidableEq α]

-- One update at `x`: the target and middle tests, and for a middle node one `edge`
-- evaluation, one lookup, one extension and one comparison per candidate `y`.
--
def stepCostT (NL : List α) (mid tgt : α → Bool) (tc : α → ℕ) (ec : α → α → ℕ)
    (tbl : List (α × Option (ℕ × List α))) (x : α) : ℕ :=
  1 + tc x + (if tgt x then 2 else 1 + (if mid x then (NL.map fun y => ec x y + lookCost tbl + 4).sum + 1
    else 0))

def nextCostT (NL : List α) (mid tgt : α → Bool) (tc : α → ℕ) (ec : α → α → ℕ)
    (tbl : List (α × Option (ℕ × List α))) : ℕ :=
  (NL.map fun x => stepCostT NL mid tgt tc ec tbl x + 1).sum

def layerCostT (NL : List α) (mid tgt : α → Bool) (edge : α → α → Bool) (w : α → ℕ)
    (tc : α → ℕ) (ec : α → α → ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => layerCostT NL mid tgt edge w tc ec k + nextCostT NL mid tgt tc ec (layer NL mid tgt edge w k)

def minPathLCostT (NL : List α) (mid tgt : α → Bool) (edge : α → α → Bool) (w : α → ℕ)
    (tc : α → ℕ) (ec : α → α → ℕ) (sc : α → ℕ) : ℕ :=
  layerCostT NL mid tgt edge w tc ec NL.length + pickSrcCost NL sc (layer NL mid tgt edge w NL.length) +
    NL.length + 1

section bound

variable (NL : List α) (mid tgt : α → Bool) (edge : α → α → Bool) (w : α → ℕ)
  (tc : α → ℕ) (ec : α → α → ℕ) (sc : α → ℕ) {E S T : ℕ}
  (hE : ∀ x ∈ NL, ∀ y ∈ NL, ec x y ≤ E) (hS : ∀ x ∈ NL, sc x ≤ S) (hT : ∀ x ∈ NL, tc x ≤ T)

include hE hT in
omit [DecidableEq α] in
lemma stepCostT_le (tbl : List (α × Option (ℕ × List α))) (ht : tbl.length ≤ NL.length)
    {x : α} (hx : x ∈ NL) :
    stepCostT NL mid tgt tc ec tbl x ≤ NL.length * (E + NL.length + 5) + 3 + T := by
  have h := sum_map_le NL (fun y => ec x y + lookCost tbl + 4) (E + NL.length + 5)
    (fun y hy => by have := hE x hx y hy; unfold lookCost; omega)
  have := hT x hx
  unfold stepCostT
  split_ifs <;> omega

include hE hT in
omit [DecidableEq α] in
lemma nextCostT_le (tbl : List (α × Option (ℕ × List α))) (ht : tbl.length ≤ NL.length) :
    nextCostT NL mid tgt tc ec tbl ≤ NL.length * (NL.length * (E + NL.length + 5) + 4 + T) :=
  sum_map_le NL _ _ (fun x hx => by
    have := stepCostT_le NL mid tgt tc ec hE hT tbl ht hx; omega)

include hE hT in
lemma layerCostT_le : ∀ k, layerCostT NL mid tgt edge w tc ec k ≤
    1 + k * (NL.length * (NL.length * (E + NL.length + 5) + 4 + T)) := by
  intro k
  induction k with
  | zero => simp [layerCostT]
  | succ k ih =>
    simp only [layerCostT]
    have := nextCostT_le NL mid tgt tc ec hE hT _ (length_layer NL mid tgt edge w k)
    rw [Nat.succ_mul]
    omega

include hE hS hT in
lemma minPathLCostT_le : minPathLCostT NL mid tgt edge w tc ec sc ≤
    NL.length * (NL.length * (NL.length * (E + NL.length + 5) + 4 + T)) +
      NL.length * (S + NL.length + 3) + NL.length + 4 := by
  have h1 := layerCostT_le NL mid tgt edge w tc ec hE hT NL.length
  have h2 := sum_map_le NL (fun x => sc x + lookCost (layer NL mid tgt edge w NL.length) + 2)
    (S + NL.length + 3) (fun x hx => by
      have := hS x hx
      have := length_layer NL mid tgt edge w NL.length
      unfold lookCost; omega)
  unfold minPathLCostT pickSrcCost
  omega

end bound

/-! ## Monotonicity in the test costs -/

section mono

variable (NL : List α) (mid tgt : α → Bool) (edge : α → α → Bool) (w : α → ℕ) (tc : α → ℕ)
  {ec ec' : α → α → ℕ} {sc sc' : α → ℕ} (hE : ∀ x y, ec x y ≤ ec' x y) (hS : ∀ x, sc x ≤ sc' x)

include hE in
omit [DecidableEq α] in
lemma stepCostT_mono (tbl : List (α × Option (ℕ × List α))) (x : α) :
    stepCostT NL mid tgt tc ec tbl x ≤ stepCostT NL mid tgt tc ec' tbl x := by
  have := lsum_mono' NL (fun y => ec x y + lookCost tbl + 4) (fun y => ec' x y + lookCost tbl + 4)
    (fun y => by have := hE x y; omega)
  unfold stepCostT
  split_ifs <;> omega

include hE in
lemma layerCostT_mono : ∀ k, layerCostT NL mid tgt edge w tc ec k ≤ layerCostT NL mid tgt edge w tc ec' k
  | 0 => le_rfl
  | k + 1 => by
    simp only [layerCostT, nextCostT]
    have := layerCostT_mono k
    have := lsum_mono' NL (fun x => stepCostT NL mid tgt tc ec (layer NL mid tgt edge w k) x + 1)
      (fun x => stepCostT NL mid tgt tc ec' (layer NL mid tgt edge w k) x + 1)
      (fun x => by have := stepCostT_mono NL mid tgt tc hE (layer NL mid tgt edge w k) x; omega)
    omega

include hE hS in
lemma minPathLCostT_mono : minPathLCostT NL mid tgt edge w tc ec sc ≤ minPathLCostT NL mid tgt edge w tc ec' sc' := by
  have h1 := layerCostT_mono NL mid tgt edge w tc hE NL.length
  have h2 := lsum_mono' NL (fun x => sc x + lookCost (layer NL mid tgt edge w NL.length) + 2)
    (fun x => sc' x + lookCost (layer NL mid tgt edge w NL.length) + 2) (fun x => by have := hS x; omega)
  unfold minPathLCostT pickSrcCost
  omega

end mono

-- The `Finset` front end: sort, then search.
--
def minPathCostT {β : Type} [LinearOrder β] (N : Finset β) (mid tgt : β → Bool)
    (edge : β → β → Bool) (w : β → ℕ) (tc : β → ℕ) (ec : β → β → ℕ) (sc : β → ℕ) : ℕ :=
  N.card ^ 2 + minPathLCostT (N.sort (· ≤ ·)) mid tgt edge w tc ec sc

theorem minPathCostT_le {β : Type} [LinearOrder β] (N : Finset β) (mid tgt : β → Bool)
    (edge : β → β → Bool) (w : β → ℕ) (tc : β → ℕ) (ec : β → β → ℕ) (sc : β → ℕ) {E S T : ℕ}
    (hE : ∀ x ∈ N, ∀ y ∈ N, ec x y ≤ E) (hS : ∀ x ∈ N, sc x ≤ S) (hT : ∀ x ∈ N, tc x ≤ T) :
    minPathCostT N mid tgt edge w tc ec sc ≤
      N.card ^ 2 + N.card * (N.card * (N.card * (E + N.card + 5) + 4 + T)) +
        N.card * (S + N.card + 3) + N.card + 4 := by
  have h := minPathLCostT_le (N.sort (· ≤ ·)) mid tgt edge w tc ec sc
    (fun x hx y hy => hE x (by simpa using hx) y (by simpa using hy))
    (fun x hx => hS x (by simpa using hx)) (fun x hx => hT x (by simpa using hx))
  rw [Finset.length_sort] at h
  unfold minPathCostT
  omega

theorem minPathCostT_mono {β : Type} [LinearOrder β] (N : Finset β) (mid tgt : β → Bool)
    (edge : β → β → Bool) (w : β → ℕ) (tc : β → ℕ) {ec ec' : β → β → ℕ} {sc sc' : β → ℕ}
    (hE : ∀ x y, ec x y ≤ ec' x y) (hS : ∀ x, sc x ≤ sc' x) :
    minPathCostT N mid tgt edge w tc ec sc ≤ minPathCostT N mid tgt edge w tc ec' sc' := by
  have := minPathLCostT_mono (N.sort (· ≤ ·)) mid tgt edge w tc hE hS
  unfold minPathCostT
  omega

end ULHC.MP
