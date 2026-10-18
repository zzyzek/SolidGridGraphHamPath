/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.Timed.TimeM
import ULHC.CostConn

/-!
# Counted reachability

Counted versions of `fnbr`, `creach`, `ccls`, `connB`, `cncomp`, and of the cell and degree
tests. Each `fooT` has `fooT_ret : (fooT …).ret = foo …` and a step bound by the cost function
of `CostConn.lean`.
-/

namespace ULHC.T

open Finset

/-! ## Counted definitions -/

def isCellT (V : Finset Pt) (c : Pt) : TimeM Bool := do
  let a ← memT c V
  let b ← memT (c.1 + 1, c.2) V
  let d ← memT (c.1, c.2 + 1) V
  let e ← memT (c.1 + 1, c.2 + 1) V
  tick 3
  pure (a && b && d && e)

def degT (F : Finset Edge) (p : Pt) : TimeM ℕ := do
  let a ← memT (eR p) F
  let b ← memT (eL p) F
  let c ← memT (eU p) F
  let d ← memT (eD p) F
  tick 4
  pure ((if a then 1 else 0) + (if b then 1 else 0) + (if c then 1 else 0) + (if d then 1 else 0))

def fnbrT (F : Finset Edge) (u : Pt) : TimeM (Finset Pt) := do
  let l ← lfilterT (fun e => memT e F) (TF.inc4 u)
  let l' ← lmapT (fun e => pure (other e u)) l
  toFinsetT l'

def creachT (F : Finset Edge) (x : Pt) : ℕ → TimeM (Finset Pt)
  | 0 => do
    tick 1
    pure {x}
  | k + 1 => do
    let C ← creachT F x k
    let Bs ← biUnionT (fnbrT F) C
    unionT C Bs

def cclsT (V : Finset Pt) (F : Finset Edge) (x : Pt) : TimeM (Finset Pt) := do
  let n ← cardT V
  creachT F x n

def connBT (V : Finset Pt) (F : Finset Edge) (x y : Pt) : TimeM Bool := do
  let C ← cclsT V F x
  memT y C

def cncompT (V : Finset Pt) (F : Finset Edge) : TimeM ℕ := do
  let S ← imageSetsT (cclsT V F) V
  cardT S

/-! ## Results -/

@[simp] lemma isCellT_ret (V : Finset Pt) (c : Pt) : (isCellT V c).ret = decide (IsCell V c) := by
  simp [isCellT, memT, IsCell, Bool.and_assoc]

lemma isCellT_time (V : Finset Pt) (c : Pt) : (isCellT V c).time = 7 := by
  simp [isCellT, memT]

@[simp] lemma degT_ret (F : Finset Edge) (p : Pt) : (degT F p).ret = deg F p := by
  simp only [degT, memT, ret_bind, ret_pure, deg, ind, decide_eq_true_eq]

lemma degT_time (F : Finset Edge) (p : Pt) : (degT F p).time = 8 := by
  simp [degT, memT]

@[simp] lemma fnbrT_ret (F : Finset Edge) (u : Pt) : (fnbrT F u).ret = fnbr F u := rfl

lemma fnbrT_time_le (F : Finset Edge) (u : Pt) : (fnbrT F u).time ≤ 17 := by
  have h1 := lfilterT_time_le (fun e => memT e F) (TF.inc4 u) 1 (fun _ _ => le_rfl)
  have hl : (TF.inc4 u).length = 4 := rfl
  have hlen : (TF.inc4 u |>.filter (fun e => (memT e F).ret)).length ≤ 4 :=
    (List.length_filter_le _ _).trans hl.le
  have h2 := lmapT_time_le (fun e => (pure (other e u) : TimeM Pt))
    ((TF.inc4 u).filter (fun e => (memT e F).ret)) 0 (fun _ _ => le_rfl)
  simp only [fnbrT, time_bind, toFinsetT, lmapT, List.length_map]
  simp only [lfilterT] at h1 ⊢
  simp only [lmapT] at h2
  rw [hl] at h1
  omega

@[simp] lemma creachT_ret (F : Finset Edge) (x : Pt) :
    ∀ k, (creachT F x k).ret = creach F x k
  | 0 => rfl
  | k + 1 => by
    simp only [creachT, ret_bind, unionT, biUnionT, fnbrT_ret, creachT_ret F x k]
    rfl

lemma creachT_time_le (F : Finset Edge) (x : Pt) : ∀ k, (creachT F x k).time ≤ creachCost F x k
  | 0 => by simp [creachT, creachCost]
  | k + 1 => by
    have ih := creachT_time_le F x k
    simp only [creachT, time_bind, creachT_ret, biUnionT, unionT, fnbrT_ret, creachCost]
    have hs : ∑ u ∈ creach F x k, ((fnbrT F u).time + (fnbr F u).card + 1) ≤
        ∑ u ∈ creach F x k, (fnbrCost + (fnbr F u).card) :=
      Finset.sum_le_sum (fun u _ => by have := fnbrT_time_le F u; unfold fnbrCost; omega)
    have he : ((creach F x k).biUnion fun u => fnbr F u).card =
        ((creach F x k).biUnion (fnbr F)).card := rfl
    omega

@[simp] lemma cclsT_ret (V : Finset Pt) (F : Finset Edge) (x : Pt) :
    (cclsT V F x).ret = ccls V F x := by
  simp [cclsT, cardT, ccls]

lemma cclsT_time_le (V : Finset Pt) (F : Finset Edge) (x : Pt) :
    (cclsT V F x).time ≤ cclsCost V F x := by
  have := creachT_time_le F x V.card
  simp only [cclsT, time_bind, cardT, cclsCost]
  omega

@[simp] lemma connBT_ret (V : Finset Pt) (F : Finset Edge) (x y : Pt) :
    (connBT V F x y).ret = connB V F x y := by
  simp [connBT, memT, connB]

lemma connBT_time_le (V : Finset Pt) (F : Finset Edge) (x y : Pt) :
    (connBT V F x y).time ≤ connBCost V F x := by
  have := cclsT_time_le V F x
  simp only [connBT, time_bind, memT, connBCost]
  omega

@[simp] lemma cncompT_ret (V : Finset Pt) (F : Finset Edge) : (cncompT V F).ret = cncomp V F := by
  simp only [cncompT, ret_bind, imageSetsT, cardT, cclsT_ret, cncomp]

lemma cncompT_time_le (V : Finset Pt) (F : Finset Edge) : (cncompT V F).time ≤ cncompCost V F := by
  simp only [cncompT, time_bind, imageSetsT, cardT, cclsT_ret, cncompCost]
  have hs : ∑ x ∈ V, ((cclsT V F x).time + (ccls V F x).card) ≤
      ∑ x ∈ V, (cclsCost V F x + (ccls V F x).card + 1) :=
    Finset.sum_le_sum (fun x _ => by have := cclsT_time_le V F x; omega)
  have hc : (V.image (fun x => ccls V F x)).card ≤ V.card := card_image_le
  omega

end ULHC.T
