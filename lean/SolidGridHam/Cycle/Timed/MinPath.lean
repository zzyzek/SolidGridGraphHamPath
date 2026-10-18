/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import SolidGridHam.Cycle.Timed.TimeM
public import SolidGridHam.Cycle.CostMinPath

@[expose] public section

/-!
# Counted minimum-path search

Counted versions of `look`, `amin`, `MP.step`, `next`, `layer`, `pickSrc`, `minPathL` and
`minPath`, for counted `edge` and `src` tests (`mid`, `tgt`, `w` are constant-time). Results
equal the originals run on the results of the tests; steps are bounded by the costs of
`CostMinPath.lean` with `ec x y` and `sc x` the steps of the tests.
-/

namespace SolidGridHam.T

variable {α : Type} [DecidableEq α]

/-! ## Counted definitions -/

def lookT {β : Type} (x : α) : List (α × Option β) → TimeM (Option β)
  | [] => do
    tick 1
    pure none
  | (a, v) :: tf => do
    tick 1
    if a = x then pure v else lookT x tf

def aminT {γ β : Type} (f : γ → TimeM (Option (ℕ × β))) : List γ → TimeM (Option (ℕ × β))
  | [] => do
    tick 1
    pure none
  | y :: ys => do
    let a ← f y
    let b ← aminT f ys
    tick 1
    pure (pick2 a b)

def stepT (NL : List α) (mid tgt : α → Bool) (edgeT : α → α → TimeM Bool) (w : α → ℕ)
    (tbl : List (α × Option (ℕ × List α))) (x : α) : TimeM (Option (ℕ × List α)) := do
  tick 1
  if tgt x then do
    tick 2
    pure (some (w x, [x]))
  else do
    tick 1
    if mid x then
      aminT (fun y => do
        let e ← edgeT x y
        let tf ← lookT y tbl
        tick 3
        pure (if e then extend x (w x) tf else none)) NL
    else pure none

def nextT (NL : List α) (mid tgt : α → Bool) (edgeT : α → α → TimeM Bool) (w : α → ℕ)
    (tbl : List (α × Option (ℕ × List α))) : TimeM (List (α × Option (ℕ × List α))) :=
  lmapT (fun x => do
    let r ← stepT NL mid tgt edgeT w tbl x
    pure (x, r)) NL

def layerT (NL : List α) (mid tgt : α → Bool) (edgeT : α → α → TimeM Bool) (w : α → ℕ) :
    ℕ → TimeM (List (α × Option (ℕ × List α)))
  | 0 => do
    tick 1
    pure []
  | k + 1 => do
    let tf ← layerT NL mid tgt edgeT w k
    nextT NL mid tgt edgeT w tf

def pickSrcT (NL : List α) (srcT : α → TimeM Bool) (tbl : List (α × Option (ℕ × List α))) :
    TimeM (Option (List α)) := do
  let r ← aminT (fun x => do
    let s ← srcT x
    let tf ← lookT x tbl
    tick 1
    pure (if s then tf else none)) NL
  tick 1
  pure (dropW r)

def minPathLT (NL : List α) (srcT : α → TimeM Bool) (mid tgt : α → Bool)
    (edgeT : α → α → TimeM Bool) (w : α → ℕ) : TimeM (Option (List α)) := do
  let n ← lengthT NL
  let tbl ← layerT NL mid tgt edgeT w n
  pickSrcT NL srcT tbl

def minPathT {β : Type} [LinearOrder β] (N : Finset β) (srcT : β → TimeM Bool) (mid tgt : β → Bool)
    (edgeT : β → β → TimeM Bool) (w : β → ℕ) : TimeM (Option (List β)) := do
  let l ← sortT N
  minPathLT l srcT mid tgt edgeT w

/-! ## Results -/

section results

variable (NL : List α) (mid tgt : α → Bool) (edgeT : α → α → TimeM Bool) (w : α → ℕ)

@[simp] lemma lookT_ret {β : Type} (x : α) : ∀ (l : List (α × Option β)),
    (lookT x l).ret = MP.look x l
  | [] => rfl
  | (a, v) :: tf => by
    simp only [lookT, MP.look, ret_bind]
    split_ifs
    · rfl
    · exact lookT_ret x tf

@[simp] lemma aminT_ret {γ β : Type} (f : γ → TimeM (Option (ℕ × β))) : ∀ l : List γ,
    (aminT f l).ret = MP.amin (fun y => (f y).ret) l
  | [] => rfl
  | y :: ys => by
    simp only [aminT, MP.amin, ret_bind, ret_pure, pick2, aminT_ret f ys]

@[simp] lemma stepT_ret (tbl : List (α × Option (ℕ × List α))) (x : α) :
    (stepT NL mid tgt edgeT w tbl x).ret =
      MP.step NL mid tgt (fun a b => (edgeT a b).ret) w (fun y => MP.look y tbl) x := by
  unfold stepT MP.step
  by_cases h1 : tgt x = true
  · simp [h1]
  · by_cases h2 : mid x = true
    · simp only [h1, h2, ret_bind, Bool.false_eq_true, ite_false, ite_true, aminT_ret,
        lookT_ret, ret_pure, extend]
    · simp [h1, h2]

@[simp] lemma nextT_ret (tbl : List (α × Option (ℕ × List α))) :
    (nextT NL mid tgt edgeT w tbl).ret =
      MP.next NL mid tgt (fun a b => (edgeT a b).ret) w tbl := by
  simp [nextT, MP.next, lmapT]

@[simp] lemma layerT_ret : ∀ k, (layerT NL mid tgt edgeT w k).ret =
    MP.layer NL mid tgt (fun a b => (edgeT a b).ret) w k
  | 0 => rfl
  | k + 1 => by
    simp only [layerT, MP.layer, ret_bind, nextT_ret, layerT_ret k]

@[simp] lemma pickSrcT_ret (srcT : α → TimeM Bool) (tbl : List (α × Option (ℕ × List α))) :
    (pickSrcT NL srcT tbl).ret = MP.pickSrc NL (fun x => (srcT x).ret) tbl := by
  simp only [pickSrcT, MP.pickSrc, ret_bind, ret_pure, aminT_ret, lookT_ret, dropW]

@[simp] lemma minPathLT_ret (srcT : α → TimeM Bool) :
    (minPathLT NL srcT mid tgt edgeT w).ret =
      MP.minPathL NL (fun x => (srcT x).ret) mid tgt (fun a b => (edgeT a b).ret) w := by
  simp [minPathLT, MP.minPathL, lengthT]

end results

@[simp] lemma minPathT_ret {β : Type} [LinearOrder β] (N : Finset β) (srcT : β → TimeM Bool)
    (mid tgt : β → Bool) (edgeT : β → β → TimeM Bool) (w : β → ℕ) :
    (minPathT N srcT mid tgt edgeT w).ret =
      MP.minPath N (fun x => (srcT x).ret) mid tgt (fun a b => (edgeT a b).ret) w := by
  simp [minPathT, MP.minPath, sortT]

/-! ## Steps -/

lemma lsum_mono {γ : Type} (l : List γ) (f g : γ → ℕ) (h : ∀ x ∈ l, f x ≤ g x) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a tf ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (h a (by simp)) (ih (fun x hx => h x (by simp [hx])))

lemma lookT_time_le {β : Type} (x : α) : ∀ (l : List (α × Option β)),
    (lookT x l).time ≤ l.length + 1
  | [] => by simp [lookT]
  | (a, v) :: tf => by
    have := lookT_time_le x tf
    simp only [lookT, time_bind, time_tick, List.length_cons]
    split_ifs <;> (simp; try omega)

lemma aminT_time {γ β : Type} (f : γ → TimeM (Option (ℕ × β))) : ∀ l : List γ,
    (aminT f l).time = (l.map fun y => (f y).time + 1).sum + 1
  | [] => by simp [aminT]
  | y :: ys => by
    simp only [aminT, time_bind, time_tick, time_pure, List.map_cons, List.sum_cons, aminT_time f ys]
    omega

section steps

variable (NL : List α) (mid tgt : α → Bool) (edgeT : α → α → TimeM Bool) (w : α → ℕ)

lemma stepT_time_le (tbl : List (α × Option (ℕ × List α))) (x : α) :
    (stepT NL mid tgt edgeT w tbl x).time ≤
      MP.stepCost NL mid tgt (fun a b => (edgeT a b).time) tbl x := by
  unfold stepT MP.stepCost
  by_cases h1 : tgt x = true
  · simp [h1]
  · by_cases h2 : mid x = true
    · simp only [h1, h2, time_bind, time_tick, time_pure, Bool.false_eq_true, ite_false, ite_true,
        aminT_time]
      have := lsum_mono NL (fun y => (do
          let e ← edgeT x y
          let tf ← lookT y tbl
          tick 3
          pure (if e then extend x (w x) tf else none) : TimeM (Option (ℕ × List α))).time + 1)
        (fun y => (edgeT x y).time + MP.lookCost tbl + 4) (fun y _ => by
          have := lookT_time_le y tbl
          simp only [time_bind, time_tick, time_pure, MP.lookCost]
          omega)
      simp only [time_bind, time_tick, time_pure] at this
      omega
    · simp [h1, h2]

lemma nextT_time_le (tbl : List (α × Option (ℕ × List α))) :
    (nextT NL mid tgt edgeT w tbl).time ≤ MP.nextCost NL mid tgt (fun a b => (edgeT a b).time) tbl := by
  simp only [nextT, lmapT, MP.nextCost, time_bind, time_pure]
  exact lsum_mono NL _ _ (fun x _ => by have := stepT_time_le NL mid tgt edgeT w tbl x; omega)

lemma layerT_time_le : ∀ k, (layerT NL mid tgt edgeT w k).time ≤
    MP.layerCost NL mid tgt (fun a b => (edgeT a b).ret) w (fun a b => (edgeT a b).time) k
  | 0 => by simp [layerT, MP.layerCost]
  | k + 1 => by
    have ih := layerT_time_le k
    have := nextT_time_le NL mid tgt edgeT w (layerT NL mid tgt edgeT w k).ret
    simp only [layerT_ret] at this
    simp only [layerT, MP.layerCost, time_bind, layerT_ret]
    omega

lemma pickSrcT_time_le (srcT : α → TimeM Bool) (tbl : List (α × Option (ℕ × List α))) :
    (pickSrcT NL srcT tbl).time ≤ MP.pickSrcCost NL (fun x => (srcT x).time) tbl := by
  simp only [pickSrcT, MP.pickSrcCost, time_bind, time_tick, time_pure, aminT_time]
  have := lsum_mono NL (fun x => (do
      let s ← srcT x
      let tf ← lookT x tbl
      tick 1
      pure (if s then tf else none) : TimeM (Option (ℕ × List α))).time + 1)
    (fun x => (srcT x).time + MP.lookCost tbl + 2) (fun x _ => by
      have := lookT_time_le x tbl
      simp only [time_bind, time_tick, time_pure, MP.lookCost]
      omega)
  simp only [time_bind, time_tick, time_pure] at this
  omega

lemma minPathLT_time_le (srcT : α → TimeM Bool) :
    (minPathLT NL srcT mid tgt edgeT w).time ≤
      MP.minPathLCost NL mid tgt (fun a b => (edgeT a b).ret) w (fun a b => (edgeT a b).time)
        (fun x => (srcT x).time) := by
  have h1 := layerT_time_le NL mid tgt edgeT w NL.length
  have h2 := pickSrcT_time_le NL srcT (layerT NL mid tgt edgeT w NL.length).ret
  simp only [layerT_ret] at h2
  simp only [minPathLT, MP.minPathLCost, time_bind, lengthT, layerT_ret]
  omega

end steps

lemma minPathT_time_le {β : Type} [LinearOrder β] (N : Finset β) (srcT : β → TimeM Bool)
    (mid tgt : β → Bool) (edgeT : β → β → TimeM Bool) (w : β → ℕ) :
    (minPathT N srcT mid tgt edgeT w).time ≤
      MP.minPathCost N mid tgt (fun a b => (edgeT a b).ret) w (fun a b => (edgeT a b).time)
        (fun x => (srcT x).time) := by
  have := minPathLT_time_le (N.sort (· ≤ ·)) mid tgt edgeT w srcT
  simp only [minPathT, MP.minPathCost, time_bind, sortT]
  omega

end SolidGridHam.T
