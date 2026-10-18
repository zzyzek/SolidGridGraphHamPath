/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.Timed.Conn
import ULHC.CostStrips

/-!
# Counted strips, links and candidate nodes

Counted versions of `LatOK`, `stripScan`, `stripLen`, `allStrips`, `flip`, `validB`,
`sideOffB`, `midB`, `endOffB`, `notEndB`, `cr2B`, `chainOKB`, `gsrc`, `gedge`, `cand`, `candN`,
with results equal to the originals and steps bounded by the costs of `CostStrips.lean`.
-/

namespace ULHC.T

open Finset

/-! ## Counted definitions -/

def latOKT (F : Finset Edge) (c : Pt) (s : Side) (j : ℕ) : TimeM Bool := do
  let a ← memT (lat1 (cellJ c s j) s) F
  let b ← memT (lat2 (cellJ c s j) s) F
  tick 3
  pure ((a == (j % 2 == 1)) && (b == (j % 2 == 1)))

def stripScanT (V : Finset Pt) (F : Finset Edge) (c : Pt) (s : Side) : ℕ → ℕ → TimeM (Option ℕ)
  | 0, _ => do
    tick 1
    pure none
  | k + 1, j => do
    let a ← isCellT V (cellJ c s j)
    let b ← latOKT F c s j
    let f ← memT (front (cellJ c s j) s) F
    tick 3
    if a && b then
      if f == (j % 2 == 0) then pure (some (j + 1)) else stripScanT V F c s k (j + 1)
    else pure none

def stripLenT (V : Finset Pt) (F : Finset Edge) (c : Pt) (s : Side) : TimeM (Option ℕ) := do
  let b ← memT (back c s) F
  let n ← cardT V
  tick 1
  if b then stripScanT V F c s n 0 else pure none

def allStripsT (V : Finset Pt) (F : Finset Edge) : TimeM (Finset StripSpec) := do
  let Cs ← filterT (isCellT V) V
  biUnionT (fun c => biUnionT (fun s => do
    let o ← stripLenT V F c s
    pure (optStrips c s o)) sidesF) Cs

def flipT (G : Finset Edge) (u : Pt) : TimeM (Finset Edge) := symmDiffT G (cellE u)

def validBT (V : Finset Pt) (F : Finset Edge) (σ : StripSpec) : TimeM Bool := do
  let A ← allStripsT V F
  let a ← memT σ A
  let b ← connBT V F (back1 σ.c σ.s) (front1 σ.c σ.s)
  tick 2
  pure (a && !b)

def sideOffBT (b c : StripSpec) : TimeM Bool := do
  let R ← rangeT c.n
  let R' ← rangeT (b.n - 1)
  lallT (fun j => lallT (fun i => allT (fun e => do
    let m ← memT e (cellE (cellJ b.c b.s i))
    pure (!m)) (cellE (cellJ c.c c.s j))) R') R

def midBT (b : StripSpec) (z : Pt) : TimeM Bool := do
  let R ← rangeT (b.n - 2)
  lanyT (fun j => do
    tick 4
    pure (eqN (j % 2) 1 && (eqP z (front1 (cellJ b.c b.s j) b.s) ||
      eqP z (front2 (cellJ b.c b.s j) b.s)))) R

def endOffBT (b c : StripSpec) : TimeM Bool := do
  let r ← allT (fun e => do
    let m ← memT e (cellE (endCell b))
    pure (!m)) (cellE (endCell c))
  tick 3
  pure (!(c.n % 2 == 0) || r)

def notEndBT (b c : StripSpec) : TimeM Bool := do
  let R ← rangeT c.n
  lallT (fun j => do
    tick 3
    pure (!eqP (cellJ c.c c.s j) (endCell b))) R

def cr2BT (V : Finset Pt) (G : Finset Edge) (b c : StripSpec) : TimeM Bool := do
  let Gu ← flipT G (endCell b)
  let A ← allStripsT V Gu
  let a ← memT c A
  let s1 ← sideOffBT b c
  let s2 ← notEndBT b c
  let s3 ← endOffBT b c
  let m1 ← midBT b (back1 c.c c.s)
  let m2 ← midBT b (front1 c.c c.s)
  let k1 ← connBT V G (back1 c.c c.s) (front1 c.c c.s)
  let Gu' ← flipT G (endCell b)
  let k2 ← connBT V Gu' (back1 c.c c.s) (front1 c.c c.s)
  tick 12
  pure (((2 ≤ b.n : Bool) && eqN (b.n % 2) 0) && a && s1 && s2 && s3 && !m1 && !m2 && k1 && !k2)

def chainOKBT (b c : StripSpec) : TimeM Bool := do
  let R ← rangeT c.n
  lallT (fun j => allT (fun x => do
    let m ← memT x (cellE (endCell b))
    tick 4
    pure (!m || (eqN j 0 && (eqE x (lat1 (endCell b) b.s) || eqE x (lat2 (endCell b) b.s)))))
    (cellE (cellJ c.c c.s j))) R

def gsrcT (V : Finset Pt) (G : Finset Edge) (x : Node) : TimeM Bool := do
  let v ← validBT V G x.σ
  tick 2
  pure ((x.pos == 1) && v)

def gedgeT (V : Finset Pt) (G : Finset Edge) (x y : Node) : TimeM Bool := do
  let a ← cr2BT V G x.σ y.σ
  let b ← chainOKBT x.σ y.σ
  tick 3
  pure ((y.pos == min (x.pos + 1) 3) && a && b)

def candT (V : Finset Pt) (G : Finset Edge) : TimeM (Finset StripSpec) := do
  let A ← allStripsT V G
  let Cs ← filterT (isCellT V) V
  let Bs ← biUnionT (fun u => do
    let Gu ← flipT G u
    allStripsT V Gu) Cs
  unionT A Bs

def candNT (V : Finset Pt) (G : Finset Edge) : TimeM (Finset Node) := do
  let C ← candT V G
  biUnionT (fun σ => imageT (fun p => pure (Node.mk σ p)) ({1, 2, 3} : Finset ℕ)) C

/-! ## Results -/

@[simp] lemma latOKT_ret (F : Finset Edge) (c : Pt) (s : Side) (j : ℕ) :
    (latOKT F c s j).ret = decide (LatOK F c s j) := by
  unfold latOKT LatOK
  by_cases h1 : lat1 (cellJ c s j) s ∈ F <;> by_cases h2 : lat2 (cellJ c s j) s ∈ F <;>
    by_cases h3 : j % 2 = 1 <;> simp [memT, h1, h2, h3]

@[simp] lemma stripScanT_ret (V : Finset Pt) (F : Finset Edge) (c : Pt) (s : Side) :
    ∀ k j, (stripScanT V F c s k j).ret = stripScan V F c s k j
  | 0, _ => rfl
  | k + 1, j => by
    have ih := stripScanT_ret V F c s k (j + 1)
    simp only [stripScanT, stripScan, ret_bind, isCellT_ret, latOKT_ret, memT]
    by_cases h1 : IsCell V (cellJ c s j) ∧ LatOK F c s j
    · rw [ite_eq_left h1]
      have hb : (decide (IsCell V (cellJ c s j)) && decide (LatOK F c s j)) = true := by
        simp [h1.1, h1.2]
      rw [ite_eq_left hb]
      by_cases h2 : front (cellJ c s j) s ∈ F <;> by_cases h3 : j % 2 = 0 <;>
        simp [h2, h3, ih]
    · rw [ite_eq_right h1]
      have hb : (decide (IsCell V (cellJ c s j)) && decide (LatOK F c s j)) = false := by
        simpa using h1
      rw [hb]
      rfl

@[simp] lemma stripLenT_ret (V : Finset Pt) (F : Finset Edge) (c : Pt) (s : Side) :
    (stripLenT V F c s).ret = stripLen V F c s := by
  unfold stripLenT stripLen
  by_cases h : back c s ∈ F <;> simp [memT, cardT, h]

@[simp] lemma allStripsT_ret (V : Finset Pt) (F : Finset Edge) :
    (allStripsT V F).ret = allStrips V F := by
  simp only [allStripsT, ret_bind, filterT, biUnionT, isCellT_ret, stripLenT_ret, ret_pure,
    allStrips, optStrips, decide_eq_true_eq]

@[simp] lemma flipT_ret (G : Finset Edge) (u : Pt) : (flipT G u).ret = flip G u := rfl

@[simp] lemma validBT_ret (V : Finset Pt) (F : Finset Edge) (σ : StripSpec) :
    (validBT V F σ).ret = validB V F σ := by
  simp [validBT, validB, memT]

@[simp] lemma sideOffBT_ret (b c : StripSpec) : (sideOffBT b c).ret = sideOffB b c := by
  simp [sideOffBT, sideOffB, lallT, allT, rangeT, memT]

@[simp] lemma midBT_ret (b : StripSpec) (z : Pt) : (midBT b z).ret = midB b z := by
  simp [midBT, midB, lanyT, rangeT, eqN, eqP]

@[simp] lemma endOffBT_ret (b c : StripSpec) : (endOffBT b c).ret = endOffB b c := by
  unfold endOffBT endOffB
  by_cases h : c.n % 2 = 0 <;> simp [allT, memT, h]

@[simp] lemma notEndBT_ret (b c : StripSpec) : (notEndBT b c).ret = notEndB b c := by
  simp [notEndBT, notEndB, lallT, rangeT, eqP]

@[simp] lemma cr2BT_ret (V : Finset Pt) (G : Finset Edge) (b c : StripSpec) :
    (cr2BT V G b c).ret = cr2B V G b c := by
  simp [cr2BT, cr2B, memT, eqN, Bool.and_assoc]

@[simp] lemma chainOKBT_ret (b c : StripSpec) : (chainOKBT b c).ret = chainOKB b c := by
  unfold chainOKBT chainOKB
  simp only [ret_bind, rangeT, lallT, allT, memT, ret_pure, eqN, eqE]
  congr 1
  funext j
  apply decide_eq_decide.2
  refine forall₂_congr (fun x _ => ?_)
  by_cases h : x ∈ cellE (endCell b) <;> simp [h]

@[simp] lemma gsrcT_ret (V : Finset Pt) (G : Finset Edge) (x : Node) :
    (gsrcT V G x).ret = gsrc V G x := by
  simp [gsrcT, gsrc]

@[simp] lemma gedgeT_ret (V : Finset Pt) (G : Finset Edge) (x y : Node) :
    (gedgeT V G x y).ret = gedge V G x y := by
  simp [gedgeT, gedge, Bool.and_assoc]

@[simp] lemma candT_ret (V : Finset Pt) (G : Finset Edge) : (candT V G).ret = cand V G := by
  simp [candT, cand, unionT, biUnionT, filterT]

@[simp] lemma candNT_ret (V : Finset Pt) (G : Finset Edge) : (candNT V G).ret = candN V G := by
  simp [candNT, candN, biUnionT, imageT]

/-! ## Steps -/

lemma latOKT_time (F : Finset Edge) (c : Pt) (s : Side) (j : ℕ) : (latOKT F c s j).time = 5 := by
  simp [latOKT, memT]

lemma stripScanT_time_le (V : Finset Pt) (F : Finset Edge) (c : Pt) (s : Side) :
    ∀ k j, (stripScanT V F c s k j).time ≤ stripScanCost V F c s k j
  | 0, _ => by simp [stripScanT, stripScanCost]
  | k + 1, j => by
    have ih := stripScanT_time_le V F c s k (j + 1)
    simp only [stripScanT, stripScanCost, time_bind, isCellT_time, latOKT_time,
      isCellT_ret, latOKT_ret, memT, time_tick]
    by_cases h1 : IsCell V (cellJ c s j) ∧ LatOK F c s j
    · rw [ite_eq_left h1]
      have hb : (decide (IsCell V (cellJ c s j)) && decide (LatOK F c s j)) = true := by
        simp [h1.1, h1.2]
      rw [ite_eq_left hb]
      by_cases h2 : front (cellJ c s j) s ∈ F <;> by_cases h3 : j % 2 = 0 <;> simp [h2, h3] <;> omega
    · rw [ite_eq_right h1]
      have hb : (decide (IsCell V (cellJ c s j)) && decide (LatOK F c s j)) = false := by
        simpa using h1
      rw [hb]
      simp

lemma stripLenT_time_le (V : Finset Pt) (F : Finset Edge) (c : Pt) (s : Side) :
    (stripLenT V F c s).time ≤ stripLenCost V F c s := by
  have := stripScanT_time_le V F c s V.card 0
  unfold stripLenT stripLenCost
  by_cases h : back c s ∈ F <;> simp [memT, cardT, h] <;> omega

lemma allStripsT_time_le (V : Finset Pt) (F : Finset Edge) :
    (allStripsT V F).time ≤ allStripsCost V F := by
  set inner : Pt → TimeM (Finset StripSpec) := fun c => biUnionT (fun s => do
      let o ← stripLenT V F c s
      pure (optStrips c s o)) sidesF with hinner
  have hin : ∀ c, (inner c).time ≤ ∑ s ∈ sidesF, (stripLenCost V F c s + 2) := by
    intro c
    simp only [hinner, biUnionT, time_bind, time_pure, ret_bind, ret_pure]
    exact Finset.sum_le_sum (fun s _ => by
      have := stripLenT_time_le V F c s
      have := card_optStrips_le c s (stripLenT V F c s).ret
      omega)
  have hcard : ∀ c, (inner c).ret.card ≤ 4 := by
    intro c
    simp only [hinner, biUnionT, ret_bind, ret_pure]
    refine card_biUnion_le.trans ?_
    have := fsum_le sidesF (fun s => (optStrips c s (stripLenT V F c s).ret).card) 1
      (fun s _ => card_optStrips_le _ _ _)
    have hs : sidesF.card = 4 := by decide
    omega
  have hf : (filterT (isCellT V) V).ret = V.filter (IsCell V) := by
    simp only [filterT, isCellT_ret, decide_eq_true_eq]
  have e1 : (allStripsT V F).time =
      (filterT (isCellT V) V).time + (biUnionT inner (filterT (isCellT V) V).ret).time := rfl
  have hfc := filterT_time_le (isCellT V) V 7 (fun x _ => (isCellT_time V x).le)
  have e2 : (biUnionT inner (V.filter (IsCell V))).time =
      ∑ c ∈ V.filter (IsCell V), ((inner c).time + (inner c).ret.card + 1) := rfl
  have h2 : ∑ c ∈ V.filter (IsCell V), ((inner c).time + (inner c).ret.card + 1) ≤
      ∑ c ∈ V.filter (IsCell V), (∑ s ∈ sidesF, (stripLenCost V F c s + 2) + 5) :=
    Finset.sum_le_sum (fun c _ => by have := hin c; have := hcard c; omega)
  have e3 : ∑ _c ∈ V, 8 = V.card * 8 := by simp
  rw [e1, hf, e2]
  unfold allStripsCost
  omega

lemma flipT_time_le (G : Finset Edge) (u : Pt) : (flipT G u).time ≤ flipCost := by
  have := card_cellE_le u
  simp only [flipT, symmDiffT, flipCost]
  omega

lemma validBT_time_le (V : Finset Pt) (F : Finset Edge) (σ : StripSpec) :
    (validBT V F σ).time ≤ validBCost V F σ := by
  have h1 := allStripsT_time_le V F
  have h2 := connBT_time_le V F (back1 σ.c σ.s) (front1 σ.c σ.s)
  simp only [validBT, time_bind, memT, time_tick, time_pure, validBCost]
  omega

lemma memNot_time_le (e : Edge) (S : Finset Edge) :
    (do let m ← memT e S; pure (!m) : TimeM Bool).time ≤ 1 := by
  simp [memT]

lemma sideOffBT_time_le (b c : StripSpec) : (sideOffBT b c).time ≤ sideOffBCost b c := by
  have hall : ∀ i j, (allT (fun e => do
      let m ← memT e (cellE (cellJ b.c b.s i))
      pure (!m)) (cellE (cellJ c.c c.s j))).time ≤ 8 := by
    intro i j
    have := allT_time_le (fun e => do
      let m ← memT e (cellE (cellJ b.c b.s i))
      pure (!m)) (cellE (cellJ c.c c.s j)) 1 (fun e _ => memNot_time_le e _)
    have := card_cellE_le (cellJ c.c c.s j)
    nlinarith
  have hrow : ∀ j, (lallT (fun i => allT (fun e => do
      let m ← memT e (cellE (cellJ b.c b.s i))
      pure (!m)) (cellE (cellJ c.c c.s j))) (List.range (b.n - 1))).time ≤ (b.n - 1) * 9 := by
    intro j
    have := lallT_time_le _ (List.range (b.n - 1)) 8 (fun i _ => hall i j)
    simpa using this
  have hout := lallT_time_le (fun j => lallT (fun i => allT (fun e => do
      let m ← memT e (cellE (cellJ b.c b.s i))
      pure (!m)) (cellE (cellJ c.c c.s j))) (List.range (b.n - 1))) (List.range c.n)
    ((b.n - 1) * 9) (fun j _ => hrow j)
  simp only [List.length_range] at hout
  simp only [sideOffBT, time_bind, rangeT, sideOffBCost]
  have h9 : (b.n - 1) * 9 + 1 + 1 ≤ 20 * b.n + 2 := by omega
  have hm : c.n * ((b.n - 1) * 9 + 1) + c.n ≤ c.n * (20 * b.n + 2) := by
    have := Nat.mul_le_mul_left c.n h9
    rw [Nat.mul_add c.n _ 1, Nat.mul_one] at this
    exact this
  omega

lemma midBT_time_le (b : StripSpec) (z : Pt) : (midBT b z).time ≤ midBCost b := by
  have := lanyT_time_le (fun j => (do
      tick 4
      pure (eqN (j % 2) 1 && (eqP z (front1 (cellJ b.c b.s j) b.s) ||
        eqP z (front2 (cellJ b.c b.s j) b.s))) : TimeM Bool)) (List.range (b.n - 2)) 4
    (fun j _ => by simp)
  simp only [List.length_range] at this
  simp only [midBT, time_bind, rangeT, midBCost]
  omega

lemma endOffBT_time_le (b c : StripSpec) : (endOffBT b c).time ≤ endOffBCost := by
  have h := allT_time_le (fun e => do
    let m ← memT e (cellE (endCell b))
    pure (!m)) (cellE (endCell c)) 1 (fun e _ => memNot_time_le e (cellE (endCell b)))
  have := card_cellE_le (endCell c)
  simp only [endOffBT, time_bind, time_tick, time_pure, endOffBCost]
  omega

lemma notEndBT_time_le (b c : StripSpec) : (notEndBT b c).time ≤ notEndBCost c := by
  have := lallT_time_le (fun j => (do
      tick 3
      pure (!eqP (cellJ c.c c.s j) (endCell b)) : TimeM Bool)) (List.range c.n) 3 (fun j _ => by simp)
  simp only [List.length_range] at this
  simp only [notEndBT, time_bind, rangeT, notEndBCost]
  omega

lemma cr2BT_time_le (V : Finset Pt) (G : Finset Edge) (b c : StripSpec) :
    (cr2BT V G b c).time ≤ cr2BCost V G b c := by
  have h1 := flipT_time_le G (endCell b)
  have h2 := allStripsT_time_le V (flip G (endCell b))
  have h3 := sideOffBT_time_le b c
  have h4 := notEndBT_time_le b c
  have h5 := endOffBT_time_le b c
  have h6 := midBT_time_le b (back1 c.c c.s)
  have h7 := midBT_time_le b (front1 c.c c.s)
  have h8 := connBT_time_le V G (back1 c.c c.s) (front1 c.c c.s)
  have h9 := connBT_time_le V (flip G (endCell b)) (back1 c.c c.s) (front1 c.c c.s)
  simp only [cr2BT, time_bind, flipT_ret, memT, time_tick, time_pure, cr2BCost]
  omega

lemma chainOKBT_time_le (b c : StripSpec) : (chainOKBT b c).time ≤ chainOKBCost c := by
  have hall : ∀ j, (allT (fun x => do
      let m ← memT x (cellE (endCell b))
      tick 4
      pure (!m || (eqN j 0 && (eqE x (lat1 (endCell b) b.s) || eqE x (lat2 (endCell b) b.s)))))
      (cellE (cellJ c.c c.s j))).time ≤ 24 := by
    intro j
    have := allT_time_le (fun x => do
      let m ← memT x (cellE (endCell b))
      tick 4
      pure (!m || (eqN j 0 && (eqE x (lat1 (endCell b) b.s) || eqE x (lat2 (endCell b) b.s)))))
      (cellE (cellJ c.c c.s j)) 5 (fun x _ => by simp [memT])
    have := card_cellE_le (cellJ c.c c.s j)
    nlinarith
  have := lallT_time_le _ (List.range c.n) 24 (fun j _ => hall j)
  simp only [List.length_range] at this
  simp only [chainOKBT, time_bind, rangeT, chainOKBCost]
  omega

lemma gsrcT_time_le (V : Finset Pt) (G : Finset Edge) (x : Node) :
    (gsrcT V G x).time ≤ gsrcCost V G x := by
  have := validBT_time_le V G x.σ
  simp only [gsrcT, time_bind, time_tick, time_pure, gsrcCost]
  omega

lemma gedgeT_time_le (V : Finset Pt) (G : Finset Edge) (x y : Node) :
    (gedgeT V G x y).time ≤ gedgeCost V G x y := by
  have := cr2BT_time_le V G x.σ y.σ
  have := chainOKBT_time_le x.σ y.σ
  simp only [gedgeT, time_bind, time_tick, time_pure, gedgeCost]
  omega

lemma candT_time_le (V : Finset Pt) (G : Finset Edge) : (candT V G).time ≤ candCost V G := by
  set inner : Pt → TimeM (Finset StripSpec) := fun u => do
    let Gu ← flipT G u
    allStripsT V Gu with hinner
  have hf : (filterT (isCellT V) V).ret = V.filter (IsCell V) := by
    simp only [filterT, isCellT_ret, decide_eq_true_eq]
  have e1 : (candT V G).time = (allStripsT V G).time + ((filterT (isCellT V) V).time +
      ((biUnionT inner (filterT (isCellT V) V).ret).time +
      (unionT (allStripsT V G).ret (biUnionT inner (filterT (isCellT V) V).ret).ret).time)) := rfl
  have h1 := allStripsT_time_le V G
  have hfc := filterT_time_le (isCellT V) V 7 (fun x _ => (isCellT_time V x).le)
  have hret : (biUnionT inner (V.filter (IsCell V))).ret =
      (V.filter (IsCell V)).biUnion (fun u => allStrips V (flip G u)) := by
    simp [hinner, biUnionT]
  have e2 : (biUnionT inner (V.filter (IsCell V))).time =
      ∑ u ∈ V.filter (IsCell V), ((inner u).time + (inner u).ret.card + 1) := rfl
  have h2 : ∑ u ∈ V.filter (IsCell V), ((inner u).time + (inner u).ret.card + 1) ≤
      ∑ u ∈ V.filter (IsCell V), (flipCost + allStripsCost V (flip G u) +
        (allStrips V (flip G u)).card + 1) :=
    Finset.sum_le_sum (fun u _ => by
      have := flipT_time_le G u
      have := allStripsT_time_le V (flip G u)
      have e : (inner u).time = (flipT G u).time + (allStripsT V (flip G u)).time := rfl
      have e' : (inner u).ret = allStrips V (flip G u) := by simp [hinner]
      rw [e, e']
      omega)
  have hA : (allStrips V G).card ≤ (cand V G).card := card_le_card subset_union_left
  have hB : ((V.filter (IsCell V)).biUnion fun u => allStrips V (flip G u)).card ≤
      (cand V G).card := card_le_card subset_union_right
  rw [e1, hf, e2]
  simp only [unionT, allStripsT_ret, hret]
  unfold candCost
  omega

lemma candNT_time_le (V : Finset Pt) (G : Finset Edge) : (candNT V G).time ≤ candNCost V G := by
  have h1 := candT_time_le V G
  have h2 : ∑ σ ∈ cand V G, ((imageT (fun p => (pure (Node.mk σ p) : TimeM Node))
      ({1, 2, 3} : Finset ℕ)).time + (imageT (fun p => (pure (Node.mk σ p) : TimeM Node))
      ({1, 2, 3} : Finset ℕ)).ret.card + 1) ≤ ∑ _σ ∈ cand V G, 10 :=
    Finset.sum_le_sum (fun σ _ => by
      simp only [imageT, time_pure, ret_pure]
      have : (({1, 2, 3} : Finset ℕ).image fun p => Node.mk σ p).card ≤ 3 :=
        card_image_le.trans (by decide)
      have : ∑ x ∈ ({1, 2, 3} : Finset ℕ), (0 + 1) = 3 := by decide
      omega)
  simp only [candNT, time_bind, candT_ret, biUnionT, candNCost] at h2 ⊢
  simp only [sum_const, smul_eq_mul] at h2
  omega

end ULHC.T
