/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import Mathlib

@[expose] public section

/-!
# Minimum-weight path search (Bellman–Ford on tails)

## Setting

A node type `α` with decidable equality, a node universe given as a list `NL : List α`
(duplicates allowed), Boolean predicates `src mid tgt : α → Bool`, an edge relation
`edge : α → α → Bool` and node weights `w : α → ℕ`.

The core search `minPathL` takes the universe as a list, because `Finset.toList` is
noncomputable. The `Finset` front end `minPath N` (for a linearly ordered node type)
runs `minPathL` on `N.sort (· ≤ ·)`, whose length is `N.card`.

A *path* (`IsPath`) is a nonempty list `x₀ :: rest` with `src x₀`, consecutive elements
joined by `edge`, `mid` at every element except the last, and `tgt` at the last.
A single-node path `[x]` needs `src x` and `tgt x`. The weight `pw w p` of a list is the
sum of its node weights.

A *tail* from `x` (`IsTail x L`) is the walk `x :: L` with edge steps, `mid` at every
node but the last and `tgt` at the last. So `IsPath (x :: L) ↔ src x ∧ IsTail x L`.

## Algorithm

`B k x` is a minimum-weight tail from `x` with at most `k` nodes, all in `NL`, stored
together with its weight. It satisfies
* `B 0 x = none`;
* `B (k+1) x = none` when `x ∉ NL`;
* `B (k+1) x = some (w x, [x])` when `x ∈ NL` and `tgt x`
  (`[x]` is no heavier than any other tail from `x`, since weights are natural numbers);
* otherwise, when `mid x`, the lightest of `x :: B k y` over `y ∈ NL` with `edge x y`,
  and `none` when `¬ mid x`.

The layers are stored as association lists (`layer k`, one entry per element of `NL`),
so each layer is computed once from the previous one. `minPathL` takes the lightest
`B |NL| x` over `x ∈ NL` with `src x`. Ties are broken by the order of `NL`.

## Correctness

* `minPathL_some`, `minPath_some`: a returned list is a path with all nodes in the
  universe.
* `minPathL_min`, `minPath_min`: it is no heavier than any path with all nodes in the
  universe.
* `minPathL_none`, `minPath_none`: `none` is returned only when no path with all nodes
  in the universe exists.

The key lemma is `shortcut`: cutting out a cycle `x … x` of a tail keeps it a tail and
leaves a sublist, so every tail can be replaced by a repetition-free one (at most `|NL|`
nodes when its nodes lie in `NL`) of no larger weight. Weights are natural numbers, so
removing nodes never increases the weight, and the hypothesis `1 ≤ w x` is not needed.

## Cost

Write `n = |NL|` (`n = N.card` for the `Finset` front end). There are `n` layers after
the empty one, each with `n` entries. An entry with `tgt x` costs one `w` evaluation; an
entry with `¬ tgt x ∧ mid x` costs `n` `edge` evaluations and at most `n` `w`
evaluations (weights of candidate tails are cached in the table, so only `w x` is
added). The final selection costs `n` `src` evaluations and no `edge` or `w`
evaluations. In total, at most `n³` `edge` evaluations plus `n` `src` evaluations
and at most `n³` `w` evaluations. Counting the
association-list lookups (`O(n)` each), the running time is `O(n⁴)` elementary steps.
Proved as `MP.minPathLCost_le` (`CostMinPath.lean`).
-/

namespace SolidGridHam.MP

variable {α : Type}

/-! ## Paths and weights -/

-- `IsTail mid tgt edge x L`: the walk `x :: L` steps along `edge`, every node but the
-- last satisfies `mid`, and the last node satisfies `tgt`.
--
def IsTail (mid tgt : α → Bool) (edge : α → α → Bool) : α → List α → Prop
  | x, []     => tgt x = true
  | x, y :: L => mid x = true ∧ edge x y = true ∧ IsTail mid tgt edge y L

-- `IsPath src mid tgt edge p`: `p` is nonempty, starts at a `src` node, and the rest is
-- a tail from its first node.
--
def IsPath (src mid tgt : α → Bool) (edge : α → α → Bool) : List α → Prop
  | []     => False
  | x :: L => src x = true ∧ IsTail mid tgt edge x L

-- Sum of the node weights of a list.
--
def pw (w : α → ℕ) (L : List α) : ℕ := (L.map w).sum

section Basic

variable {src mid tgt : α → Bool} {edge : α → α → Bool} {w : α → ℕ}

theorem isTail_nil {x : α} : IsTail mid tgt edge x [] ↔ tgt x = true := Iff.rfl

theorem isTail_cons {x y : α} {L : List α} :
    IsTail mid tgt edge x (y :: L) ↔
      mid x = true ∧ edge x y = true ∧ IsTail mid tgt edge y L := Iff.rfl

theorem isPath_cons {x : α} {L : List α} :
    IsPath src mid tgt edge (x :: L) ↔ src x = true ∧ IsTail mid tgt edge x L := Iff.rfl

theorem isPath_singleton {x : α} :
    IsPath src mid tgt edge [x] ↔ src x = true ∧ tgt x = true := Iff.rfl

theorem isPath_cons_cons {x y : α} {L : List α} :
    IsPath src mid tgt edge (x :: y :: L) ↔
      src x = true ∧ mid x = true ∧ edge x y = true ∧ IsTail mid tgt edge y L := Iff.rfl

theorem pw_nil : pw w [] = 0 := rfl

theorem pw_cons (x : α) (L : List α) : pw w (x :: L) = w x + pw w L := by
  simp only [pw, List.map_cons, List.sum_cons]

-- Removing nodes never increases the weight (weights are natural numbers).
--
theorem pw_sublist {l₁ l₂ : List α} (h : l₁.Sublist l₂) : pw w l₁ ≤ pw w l₂ := by
  induction h with
  | slnil => exact le_refl _
  | cons a _ ih =>
    rw [pw_cons]
    omega
  | cons_cons a _ ih =>
    rw [pw_cons, pw_cons]
    omega

/-! ## Shortcutting repeated nodes -/

-- A suffix of a tail that starts at one of its nodes is again a tail.
--
theorem isTail_suffix {x y : α} {L A R : List α} (h : IsTail mid tgt edge y L)
    (he : y :: L = A ++ x :: R) : IsTail mid tgt edge x R := by
  induction A generalizing y L with
  | nil =>
    simp only [List.nil_append, List.cons.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact h
  | cons a A ih =>
    simp only [List.cons_append, List.cons.injEq] at he
    obtain ⟨rfl, hL⟩ := he
    cases L with
    | nil => simp at hL
    | cons z L => exact ih h.2.2 hL

-- Every tail from `x` can be shortened to a repetition-free tail from `x` whose node
-- list is a sublist of the original one: if `x` reappears in the shortened rest, cut
-- the cycle `x … x`.
--
theorem shortcut {x : α} {L : List α} (h : IsTail mid tgt edge x L) :
    ∃ L', IsTail mid tgt edge x L' ∧ (x :: L').Nodup ∧ (x :: L').Sublist (x :: L) := by
  induction L generalizing x with
  | nil => exact ⟨[], h, List.nodup_singleton x, List.Sublist.refl _⟩
  | cons y L ih =>
    obtain ⟨hm, he, ht⟩ := h
    obtain ⟨L₁, ht₁, hnd, hsub⟩ := ih ht
    by_cases hx : x ∈ y :: L₁
    · obtain ⟨A, R, hAR⟩ := List.append_of_mem hx
      have hs : (x :: R).Sublist (y :: L₁) := by
        rw [hAR]
        exact List.sublist_append_right A (x :: R)
      refine ⟨R, isTail_suffix ht₁ hAR, hnd.sublist hs, ?_⟩
      exact ((List.sublist_cons_self x R).trans (hs.trans hsub)).cons_cons x
    · exact ⟨y :: L₁, ⟨hm, he, ht₁⟩, List.nodup_cons.2 ⟨hx, hnd⟩, hsub.cons_cons x⟩

-- A repetition-free list with nodes in `NL` has at most `|NL|` elements.
--
theorem length_le_card [DecidableEq α] {NL : List α} {l : List α} (hnd : l.Nodup)
    (hN : ∀ z ∈ l, z ∈ NL) : l.length ≤ NL.length := by
  rw [← List.toFinset_card_of_nodup hnd]
  exact (Finset.card_le_card (fun z hz => List.mem_toFinset.2 (hN z (List.mem_toFinset.1 hz)))).trans
    (List.toFinset_card_le NL)

end Basic

/-! ## Deterministic argmin -/

-- Keep the lighter of two candidates (by the cached weight); ties keep the left one.
--
def pick {β : Type} : Option (ℕ × β) → Option (ℕ × β) → Option (ℕ × β)
  | none,   b      => b
  | some a, none   => some a
  | some a, some b => if b.1 < a.1 then some b else some a

-- The lightest candidate `f y` over `y` in a list.
--
def amin {γ β : Type} (f : γ → Option (ℕ × β)) : List γ → Option (ℕ × β)
  | []      => none
  | y :: ys => pick (f y) (amin f ys)

section Argmin

variable {γ β : Type}

theorem pick_eq_some {a b : Option (ℕ × β)} {r : ℕ × β} (h : pick a b = some r) :
    a = some r ∨ b = some r := by
  rcases a with _ | a
  · exact Or.inr h
  · rcases b with _ | b
    · exact Or.inl h
    · simp only [pick] at h
      by_cases hb : b.1 < a.1
      · rw [ite_eq_left hb] at h
        exact Or.inr h
      · rw [ite_eq_right hb] at h
        exact Or.inl h

theorem pick_le_left {a b : Option (ℕ × β)} {r : ℕ × β} (h : a = some r) :
    ∃ r', pick a b = some r' ∧ r'.1 ≤ r.1 := by
  subst h
  rcases b with _ | b
  · exact ⟨r, rfl, le_refl _⟩
  · by_cases hb : b.1 < r.1
    · exact ⟨b, by simp only [pick, ite_eq_left hb], le_of_lt hb⟩
    · exact ⟨r, by simp only [pick, ite_eq_right hb], le_refl _⟩

theorem pick_le_right {a b : Option (ℕ × β)} {r : ℕ × β} (h : b = some r) :
    ∃ r', pick a b = some r' ∧ r'.1 ≤ r.1 := by
  subst h
  rcases a with _ | a
  · exact ⟨r, rfl, le_refl _⟩
  · by_cases hb : r.1 < a.1
    · exact ⟨r, by simp only [pick, ite_eq_left hb], le_refl _⟩
    · exact ⟨a, by simp only [pick, ite_eq_right hb], not_lt.1 hb⟩

-- The argmin is one of the candidates.
--
theorem amin_mem {f : γ → Option (ℕ × β)} {l : List γ} {r : ℕ × β}
    (h : amin f l = some r) : ∃ y ∈ l, f y = some r := by
  induction l with
  | nil => cases h
  | cons y ys ih =>
    simp only [amin] at h
    rcases pick_eq_some h with h1 | h1
    · exact ⟨y, by simp, h1⟩
    · obtain ⟨z, hz, hz'⟩ := ih h1
      exact ⟨z, List.mem_cons_of_mem y hz, hz'⟩

-- The argmin exists and is no heavier than any candidate.
--
theorem amin_le {f : γ → Option (ℕ × β)} {l : List γ} {y : γ} {r : ℕ × β}
    (hy : y ∈ l) (h : f y = some r) : ∃ r', amin f l = some r' ∧ r'.1 ≤ r.1 := by
  induction l with
  | nil => cases hy
  | cons z zs ih =>
    simp only [amin]
    rcases List.mem_cons.1 hy with rfl | hy'
    · exact pick_le_left h
    · obtain ⟨r1, h1, h1'⟩ := ih hy'
      obtain ⟨r2, h2, h2'⟩ := pick_le_right (a := f z) h1
      exact ⟨r2, h2, h2'.trans h1'⟩

end Argmin

/-! ## Tables -/

variable [DecidableEq α]

-- Association-list lookup; a missing key gives `none`.
--
def look {β : Type} (x : α) : List (α × Option β) → Option β
  | []          => none
  | (a, v) :: tf => if a = x then v else look x tf

theorem look_map {β : Type} (x : α) (f : α → Option β) (l : List α) :
    look x (l.map (fun a => (a, f a))) = if x ∈ l then f x else none := by
  induction l with
  | nil => simp [look]
  | cons a tf ih =>
    simp only [List.map_cons, look]
    by_cases h : a = x
    · subst h
      simp
    · rw [ite_eq_right h, ih]
      by_cases hx : x ∈ tf
      · rw [ite_eq_left hx, ite_eq_left (List.mem_cons_of_mem a hx)]
      · rw [ite_eq_right hx, ite_eq_right (by simp [hx, Ne.symm h])]

/-! ## The algorithm -/

-- One Bellman–Ford update at `x`, given the previous layer `T`. Each candidate carries
-- its weight, so only `w x` is evaluated when extending.
--
def step (NL : List α) (mid tgt : α → Bool) (edge : α → α → Bool) (w : α → ℕ)
    (T : α → Option (ℕ × List α)) (x : α) : Option (ℕ × List α) :=
  if tgt x then some (w x, [x])
  else if mid x then
    amin (fun y => if edge x y then (T y).map (fun r => (w x + r.1, x :: r.2)) else none)
      NL
  else none

-- The next layer, as an association list over `NL`.
--
def next (NL : List α) (mid tgt : α → Bool) (edge : α → α → Bool) (w : α → ℕ)
    (tbl : List (α × Option (ℕ × List α))) : List (α × Option (ℕ × List α)) :=
  NL.map (fun x => (x, step NL mid tgt edge w (fun y => look y tbl) x))

-- Layer `k`; each layer is computed once from the previous one.
--
def layer (NL : List α) (mid tgt : α → Bool) (edge : α → α → Bool) (w : α → ℕ) :
    ℕ → List (α × Option (ℕ × List α))
  | 0     => []
  | k + 1 => next NL mid tgt edge w (layer NL mid tgt edge w k)

-- `B k x`: a lightest tail from `x` with at most `k` nodes, all in `NL`, and its weight.
--
def B (NL : List α) (mid tgt : α → Bool) (edge : α → α → Bool) (w : α → ℕ)
    (k : ℕ) (x : α) : Option (ℕ × List α) :=
  look x (layer NL mid tgt edge w k)

-- Lightest entry of the final table among `src` nodes, with its weight dropped.
--
def pickSrc (NL : List α) (src : α → Bool) (tbl : List (α × Option (ℕ × List α))) :
    Option (List α) :=
  (amin (fun x => if src x then look x tbl else none) NL).map Prod.snd

-- A minimum-weight path with all nodes in `NL`, or `none` if there is no such path.
--
def minPathL (NL : List α) (src mid tgt : α → Bool) (edge : α → α → Bool) (w : α → ℕ) :
    Option (List α) :=
  pickSrc NL src (layer NL mid tgt edge w NL.length)

/-! ## Correctness -/

section Correct

variable (NL : List α) (src mid tgt : α → Bool) (edge : α → α → Bool) (w : α → ℕ)

-- The candidate for start node `x` in the final selection.
--
def srcF (x : α) : Option (ℕ × List α) :=
  if src x then B NL mid tgt edge w NL.length x else none

theorem minPathL_eq :
    minPathL NL src mid tgt edge w = (amin (srcF NL src mid tgt edge w) NL).map Prod.snd :=
  rfl

theorem B_zero (x : α) : B NL mid tgt edge w 0 x = none := rfl

theorem B_succ (k : ℕ) (x : α) :
    B NL mid tgt edge w (k + 1) x =
      if x ∈ NL then step NL mid tgt edge w (B NL mid tgt edge w k) x else none := by
  unfold B
  rw [layer, next, look_map]

-- Soundness of the table: an entry is a tail from `x` with at most `k` nodes, all in
-- `NL`, and its cached weight is correct.
--
theorem B_sound : ∀ (k : ℕ) (x : α) (r : ℕ × List α), B NL mid tgt edge w k x = some r →
    r.1 = pw w r.2 ∧ ∃ L, r.2 = x :: L ∧ IsTail mid tgt edge x L ∧
      (∀ z ∈ r.2, z ∈ NL) ∧ L.length < k := by
  intro k
  induction k with
  | zero =>
    intro x r h
    rw [B_zero] at h
    cases h
  | succ k ih =>
    intro x r h
    rw [B_succ] at h
    by_cases hxN : x ∈ NL
    · rw [ite_eq_left hxN] at h
      unfold step at h
      by_cases ht : tgt x = true
      · rw [ite_eq_left ht] at h
        obtain rfl := Option.some.inj h
        refine ⟨?_, [], rfl, ht, ?_, by simp⟩
        · show w x = pw w [x]
          rw [pw_cons, pw_nil, Nat.add_zero]
        · intro z hz
          simp only [List.mem_singleton] at hz
          subst hz
          exact hxN
      · rw [ite_eq_right ht] at h
        by_cases hm : mid x = true
        · rw [ite_eq_left hm] at h
          obtain ⟨y, -, hy⟩ := amin_mem h
          by_cases he : edge x y = true
          · rw [ite_eq_left he, Option.map_eq_some_iff] at hy
            obtain ⟨r', hr', rfl⟩ := hy
            obtain ⟨h1, L, h2, h3, h4, h5⟩ := ih y r' hr'
            refine ⟨?_, r'.2, rfl, ?_, ?_, ?_⟩
            · show w x + r'.1 = pw w (x :: r'.2)
              rw [pw_cons, h1]
            · rw [h2]
              exact ⟨hm, he, h3⟩
            · intro z hz
              change z ∈ x :: r'.2 at hz
              rcases List.mem_cons.1 hz with rfl | hz
              · exact hxN
              · exact h4 z hz
            · rw [h2, List.length_cons]
              omega
          · rw [ite_eq_right he] at hy
            cases hy
        · rw [ite_eq_right hm] at h
          cases h
    · rw [ite_eq_right hxN] at h
      cases h

-- Optimality of the table: every tail from `x` with fewer than `k + 1` nodes, all in
-- `NL`, is no lighter than the entry `B k x`, which therefore exists.
--
theorem B_opt : ∀ (k : ℕ) (x : α) (L : List α), IsTail mid tgt edge x L →
    (∀ z ∈ x :: L, z ∈ NL) → L.length < k →
      ∃ r, B NL mid tgt edge w k x = some r ∧ r.1 ≤ pw w (x :: L) := by
  intro k
  induction k with
  | zero =>
    intro x L _ _ hl
    exact absurd hl (Nat.not_lt_zero _)
  | succ k ih =>
    intro x L ht hN hl
    have hxN : x ∈ NL := hN x (by simp)
    rw [B_succ, ite_eq_left hxN]
    unfold step
    by_cases htg : tgt x = true
    · rw [ite_eq_left htg]
      refine ⟨_, rfl, ?_⟩
      show w x ≤ pw w (x :: L)
      rw [pw_cons]
      omega
    · rw [ite_eq_right htg]
      cases L with
      | nil => exact absurd (isTail_nil.1 ht) htg
      | cons y L =>
        obtain ⟨hm, he, ht'⟩ := ht
        rw [ite_eq_left hm]
        have hyN : ∀ z ∈ y :: L, z ∈ NL := fun z hz => hN z (List.mem_cons_of_mem x hz)
        have hl' : L.length < k := by
          rw [List.length_cons] at hl
          omega
        obtain ⟨r, hr, hr'⟩ := ih y L ht' hyN hl'
        have hf : (if edge x y then
              (B NL mid tgt edge w k y).map (fun r => (w x + r.1, x :: r.2)) else none) =
            some (w x + r.1, x :: r.2) := by
          rw [ite_eq_left he, hr]
          rfl
        obtain ⟨r2, h2, h2'⟩ := amin_le
          (f := fun y => if edge x y then
            (B NL mid tgt edge w k y).map (fun r => (w x + r.1, x :: r.2)) else none)
          ((hyN y (by simp))) hf
        refine ⟨r2, h2, ?_⟩
        rw [pw_cons]
        exact h2'.trans (by show w x + r.1 ≤ w x + pw w (y :: L); omega)

-- What the final selection returns: a path with nodes in `NL` and its correct weight.
--
theorem amin_srcF_sound {r : ℕ × List α}
    (h : amin (srcF NL src mid tgt edge w) NL = some r) :
    r.1 = pw w r.2 ∧ IsPath src mid tgt edge r.2 ∧ ∀ z ∈ r.2, z ∈ NL := by
  obtain ⟨x, -, hx⟩ := amin_mem h
  unfold srcF at hx
  by_cases hs : src x = true
  · rw [ite_eq_left hs] at hx
    obtain ⟨h1, L, h2, h3, h4, -⟩ := B_sound NL mid tgt edge w NL.length x r hx
    refine ⟨h1, ?_, h4⟩
    rw [h2]
    exact ⟨hs, h3⟩
  · rw [ite_eq_right hs] at hx
    cases hx

-- Every path with nodes in `NL` makes the final selection succeed with a weight no
-- larger than its own.
--
theorem amin_srcF_le {q : List α} (hq : IsPath src mid tgt edge q)
    (hqN : ∀ x ∈ q, x ∈ NL) :
    ∃ r, amin (srcF NL src mid tgt edge w) NL = some r ∧ r.1 ≤ pw w q := by
  cases q with
  | nil => exact hq.elim
  | cons x L =>
    obtain ⟨hs, ht⟩ := hq
    obtain ⟨L', ht', hnd, hsub⟩ := shortcut ht
    have hN' : ∀ z ∈ x :: L', z ∈ NL := fun z hz => hqN z (hsub.subset hz)
    have hlen : L'.length < NL.length := by
      have := length_le_card hnd hN'
      rw [List.length_cons] at this
      omega
    obtain ⟨c, hB, hc⟩ := B_opt NL mid tgt edge w NL.length x L' ht' hN' hlen
    have hf : srcF NL src mid tgt edge w x = some c := by
      unfold srcF
      rw [ite_eq_left hs]
      exact hB
    obtain ⟨r, hr, hr'⟩ := amin_le ((hN' x (by simp))) hf
    exact ⟨r, hr, hr'.trans (hc.trans (pw_sublist hsub))⟩

/-! ## Main theorems -/

theorem minPathL_some {p : List α} (h : minPathL NL src mid tgt edge w = some p) :
    IsPath src mid tgt edge p ∧ ∀ x ∈ p, x ∈ NL := by
  rw [minPathL_eq, Option.map_eq_some_iff] at h
  obtain ⟨r, hr, rfl⟩ := h
  exact (amin_srcF_sound NL src mid tgt edge w hr).2

theorem minPathL_min {p : List α} (h : minPathL NL src mid tgt edge w = some p)
    (q : List α) (hq : IsPath src mid tgt edge q) (hqN : ∀ x ∈ q, x ∈ NL) :
    pw w p ≤ pw w q := by
  obtain ⟨r, hr, hr'⟩ := amin_srcF_le NL src mid tgt edge w hq hqN
  rw [minPathL_eq, hr, Option.map_some] at h
  obtain rfl := Option.some.inj h
  rw [← (amin_srcF_sound NL src mid tgt edge w hr).1]
  exact hr'

theorem minPathL_none (h : minPathL NL src mid tgt edge w = none)
    (q : List α) (hq : IsPath src mid tgt edge q) (hqN : ∀ x ∈ q, x ∈ NL) : False := by
  obtain ⟨r, hr, -⟩ := amin_srcF_le NL src mid tgt edge w hq hqN
  rw [minPathL_eq, hr, Option.map_some] at h
  cases h

end Correct

/-! ## Finset front end

`Finset.toList` is noncomputable (it picks an order by choice), so a computable search
over a `Finset` needs a canonical enumeration. With a linear order on the node type we
use `Finset.sort`, whose length is `N.card`.
-/

section FinsetFront

variable {β : Type} [LinearOrder β] (N : Finset β) (src mid tgt : β → Bool)
  (edge : β → β → Bool) (w : β → ℕ)

-- A minimum-weight path with all nodes in `N`, or `none` if there is no such path.
--
def minPath : Option (List β) :=
  minPathL (N.sort (· ≤ ·)) src mid tgt edge w

theorem minPath_some {p : List β} (h : minPath N src mid tgt edge w = some p) :
    IsPath src mid tgt edge p ∧ ∀ x ∈ p, x ∈ N := by
  obtain ⟨h1, h2⟩ := minPathL_some _ _ _ _ _ _ h
  exact ⟨h1, fun x hx => by simpa using h2 x hx⟩

theorem minPath_min {p : List β} (h : minPath N src mid tgt edge w = some p)
    (q : List β) (hq : IsPath src mid tgt edge q) (hqN : ∀ x ∈ q, x ∈ N) :
    pw w p ≤ pw w q :=
  minPathL_min _ _ _ _ _ _ h q hq (fun x hx => by simpa using hqN x hx)

theorem minPath_none (h : minPath N src mid tgt edge w = none)
    (q : List β) (hq : IsPath src mid tgt edge q) (hqN : ∀ x ∈ q, x ∈ N) : False :=
  minPathL_none _ _ _ _ _ _ h q hq (fun x hx => by simpa using hqN x hx)

end FinsetFront

/-! ## Example

Nodes `0 … 4`, edges `x → x+1` and `x → x+2`, start `0`, target `4`, all nodes allowed
in the middle, weight `10` at node `2` and `1` elsewhere. The lightest path is
`[0, 1, 3, 4]` (weight `4`).
-/

-- Example (run in a scratch file that imports `SolidGridHam`):
-- #eval minPath (Finset.range 5) (fun x => x == 0) (fun _ => true) (fun x => x == 4)
--   (fun x y => (y == x + 1) || (y == x + 2)) (fun x => if x == 2 then 10 else 1)

end SolidGridHam.MP
