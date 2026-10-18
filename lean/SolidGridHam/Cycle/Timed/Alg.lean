/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import SolidGridHam.Cycle.Timed.Strips
import SolidGridHam.Cycle.Timed.MinPath
import SolidGridHam.Cycle.Timed.TwoFactor
import SolidGridHam.Cycle.CostAlg

/-!
# The counted algorithm

`ulhcT V` is the algorithm `ulhc` written with counted operations only (`checks/timed_lint.py`).
* `ulhcT_ret : (ulhcT V).ret = ulhc V`;
* `ulhcT_time_le : (ulhcT V).time ≤ ulhcCost V ≤ 5·10⁸ (|V| + 1)¹²`.
-/

namespace SolidGridHam.T

open Finset

/-! ## Counted definitions -/

def cellListT (V : Finset Pt) : TimeM (List Pt) := do
  let Cs ← filterT (isCellT V) V
  let Ls ← imageT (fun x => pure (toLex x)) Cs
  let l ← sortT Ls
  lmapT (fun x => pure (ofLex x)) l

def t3BT (V : Finset Pt) (G : Finset Edge) (d : Pt) (tf : Side) : TimeM Bool := do
  let a ← memT (back d tf) G
  let b ← memT (front d tf) G
  let c ← memT (lat1 d tf) G
  let e ← memT (lat2 d tf) G
  let k ← connBT V G (back1 d tf) (front1 d tf)
  tick 4
  pure (a && b && !c && !e && !k)

def findT3T (V : Finset Pt) (G : Finset Edge) : TimeM (Option (Pt × Side)) := do
  let cl ← cellListT V
  let ps ← lflatMapT (fun d => lmapT (fun tf => pure (d, tf)) sidesL) cl
  lfindT (fun p => t3BT V G p.1 p.2) ps

def decodeT : List Node → TimeM (Option (StripSpec × List StripSpec))
  | [] => do
    tick 1
    pure none
  | x :: p => do
    let l ← lmapT (fun y => pure y.σ) p
    tick 1
    pure (some (x.σ, l))

def findPathT (V : Finset Pt) (G : Finset Edge) : TimeM (Option (StripSpec × List StripSpec)) := do
  let N ← candNT V G
  let r ← minPathT N (gsrcT V G) gmid gtgt (gedgeT V G) gw
  match r with
  | none => pure none
  | some q => decodeT q

def flipColT (F : Finset Edge) (c : Pt) (s : Side) : ℕ → TimeM (Finset Edge)
  | 0 => do
    tick 1
    pure F
  | n + 1 => do
    let F' ← flipT F (cellJ c s n)
    flipColT F' c s n

def roundT (V : Finset Pt) (G : Finset Edge) : TimeM (Option (Finset Edge)) := do
  let r ← findT3T V G
  match r with
  | some (d, _) => do
    let G' ← flipT G d
    pure (some G')
  | none => do
    let p ← findPathT V G
    match p with
    | some (a, _) => do
      let G' ← flipColT G a.c a.s a.n
      pure (some G')
    | none => pure none

def runT (V : Finset Pt) : ℕ → Finset Edge → TimeM Bool
  | 0, G => do
    let c ← cncompT V G
    tick 2
    pure (c == 1)
  | k + 1, G => do
    let c ← cncompT V G
    tick 2
    if c == 1 then pure true
    else do
      let r ← roundT V G
      match r with
      | some G' => runT V k G'
      | none => pure false

-- `fuel` from the size of `V`.
--
def fuelN (n : ℕ) : ℕ := (n + 1) * (2 * (3 * (4 * n + n * (4 * n)) * n) + 4) + 2

def ulhcT (V : Finset Pt) : TimeM Bool := do
  let F? ← twoFactorT V
  let n ← cardT V
  tick 9
  match F? with
  | some F => runT V (fuelN n) F
  | none => pure false

/-! ## Results -/

@[simp] lemma cellListT_ret (V : Finset Pt) : (cellListT V).ret = cellList V := by
  simp [cellListT, cellList, filterT, imageT, sortT, lmapT, Finset.map_eq_image]

@[simp] lemma t3BT_ret (V : Finset Pt) (G : Finset Edge) (d : Pt) (tf : Side) :
    (t3BT V G d tf).ret = t3B V G d tf := by
  simp [t3BT, t3B, memT, Bool.and_assoc]

@[simp] lemma findT3T_ret (V : Finset Pt) (G : Finset Edge) : (findT3T V G).ret = findT3 V G := by
  simp [findT3T, findT3, lflatMapT, lmapT, lfindT]

@[simp] lemma decodeT_ret : ∀ q : List Node, (decodeT q).ret = decode q
  | [] => rfl
  | x :: p => by simp [decodeT, decode, lmapT]

@[simp] lemma findPathT_ret (V : Finset Pt) (G : Finset Edge) :
    (findPathT V G).ret = findPath V G := by
  have hs : (fun x => (gsrcT V G x).ret) = gsrc V G := funext fun x => gsrcT_ret V G x
  have he : (fun a b => (gedgeT V G a b).ret) = gedge V G :=
    funext fun a => funext fun b => gedgeT_ret V G a b
  simp only [findPathT, findPath, ret_bind, candNT_ret, minPathT_ret, hs, he]
  rcases MP.minPath (candN V G) (gsrc V G) gmid gtgt (gedge V G) gw with _ | q
  · rfl
  · simp

@[simp] lemma flipColT_ret (F : Finset Edge) (c : Pt) (s : Side) :
    ∀ n, (flipColT F c s n).ret = flipCol F c s n := by
  intro n
  induction n generalizing F with
  | zero => rfl
  | succ n ih => simp only [flipColT, flipCol, ret_bind, flipT_ret, ih]

@[simp] lemma roundT_ret (V : Finset Pt) (G : Finset Edge) : (roundT V G).ret = step V G := by
  simp only [roundT, step, ret_bind, findT3T_ret]
  rcases findT3 V G with _ | ⟨d, tf⟩
  · simp only [ret_bind, findPathT_ret]
    rcases findPath V G with _ | ⟨a, L⟩
    · rfl
    · simp [applyS]
  · simp

@[simp] lemma runT_ret (V : Finset Pt) : ∀ k G, (runT V k G).ret = run V k G
  | 0, G => by simp [runT, run]
  | k + 1, G => by
    simp only [runT, run, ret_bind, cncompT_ret]
    by_cases h : cncomp V G == 1
    · simp [h]
    · simp only [h, Bool.false_eq_true, ite_false, ret_bind, roundT_ret]
      rcases step V G with _ | G'
      · rfl
      · exact runT_ret V k G'

lemma fuelN_eq (V : Finset Pt) : fuelN V.card = fuel V := rfl

@[simp] lemma ulhcT_ret (V : Finset Pt) : (ulhcT V).ret = ulhc V := by
  simp only [ulhcT, ulhc, ret_bind, twoFactorT_ret, cardT, fuelN_eq]
  rcases twoFactor V with _ | F
  · rfl
  · simp

/-! ## Steps -/

lemma cellListT_time_le (V : Finset Pt) : (cellListT V).time ≤ cellListCost V := by
  have h1 := filterT_time_le (isCellT V) V 7 (fun x _ => (isCellT_time V x).le)
  set Cs := (filterT (isCellT V) V).ret
  have hCs : Cs.card ≤ V.card := by simp only [Cs, filterT]; exact card_filter_le _ _
  have h2 : (imageT (fun x => (pure (toLex x) : TimeM (Lex (ℤ × ℤ)))) Cs).time ≤ Cs.card := by
    simp [imageT]
  have hLs : (imageT (fun x => (pure (toLex x) : TimeM (Lex (ℤ × ℤ)))) Cs).ret.card ≤ V.card := by
    simp only [imageT, ret_pure]; exact card_image_le.trans hCs
  have h3 := Nat.pow_le_pow_left hLs 2
  set Ls := (imageT (fun x => (pure (toLex x) : TimeM (Lex (ℤ × ℤ)))) Cs).ret
  have h4 := lmapT_time_le (fun x => (pure (ofLex x) : TimeM Pt)) (Ls.sort (· ≤ ·)) 0 (fun _ _ => le_rfl)
  rw [Finset.length_sort] at h4
  simp only [cellListT, time_bind, sortT, cellListCost]
  nlinarith

lemma t3BT_time_le (V : Finset Pt) (G : Finset Edge) (d : Pt) (tf : Side) :
    (t3BT V G d tf).time ≤ t3BCost V G d tf := by
  have := connBT_time_le V G (back1 d tf) (front1 d tf)
  simp only [t3BT, time_bind, memT, time_tick, time_pure, t3BCost]
  omega

lemma findT3T_time_le (V : Finset Pt) (G : Finset Edge) : (findT3T V G).time ≤ findT3Cost V G := by
  have h1 := cellListT_time_le V
  have h2 : (lflatMapT (fun d => lmapT (fun tf => (pure (d, tf) : TimeM (Pt × Side))) sidesL)
      (cellList V)).time ≤ 9 * (cellList V).length := by
    have := lsum_le (cellList V) (fun d => (lmapT (fun tf => (pure (d, tf) : TimeM (Pt × Side))) sidesL).time +
      (lmapT (fun tf => (pure (d, tf) : TimeM (Pt × Side))) sidesL).ret.length + 1) 9
      (fun d _ => by simp [lmapT, sidesL])
    simp only [lflatMapT]; omega
  have hps : (lflatMapT (fun d => lmapT (fun tf => (pure (d, tf) : TimeM (Pt × Side))) sidesL)
      (cellList V)).ret = (cellList V).flatMap fun d => sidesL.map fun tf => (d, tf) := by
    simp [lflatMapT, lmapT]
  have h3 : (lfindT (fun p => t3BT V G p.1 p.2)
      ((cellList V).flatMap fun d => sidesL.map fun tf => (d, tf))).time ≤
      (((cellList V).flatMap fun d => sidesL.map fun tf => (d, tf)).map
        fun p => t3BCost V G p.1 p.2 + 1).sum := by
    simp only [lfindT]
    exact lsum_mono _ _ _ (fun p _ => by have := t3BT_time_le V G p.1 p.2; omega)
  simp only [findT3T, time_bind, cellListT_ret, findT3Cost]
  rw [hps]
  omega

lemma findPathT_time_le (V : Finset Pt) (G : Finset Edge) : (findPathT V G).time ≤ findPathCost V G := by
  have h1 := candNT_time_le V G
  have he : (fun a b => (gedgeT V G a b).ret) = gedge V G :=
    funext fun a => funext fun b => gedgeT_ret V G a b
  have hs : (fun x => (gsrcT V G x).ret) = gsrc V G := funext fun x => gsrcT_ret V G x
  have h2 := minPathT_time_le (candN V G) (gsrcT V G) gmid gtgt (gedgeT V G) gw
  rw [he] at h2
  have h3 := MP.minPathCost_mono (candN V G) gmid gtgt (gedge V G) gw
    (ec := fun a b => (gedgeT V G a b).time) (ec' := gedgeCost V G)
    (sc := fun x => (gsrcT V G x).time) (sc' := gsrcCost V G)
    (fun a b => gedgeT_time_le V G a b) (fun x => gsrcT_time_le V G x)
  have hr := minPathT_ret (candN V G) (gsrcT V G) gmid gtgt (gedgeT V G) gw
  rw [he, hs] at hr
  simp only [findPathT, findPathCost, time_bind, candNT_ret, decodeCost]
  have hfp : findPath V G = (MP.minPath (candN V G) (gsrc V G) gmid gtgt (gedge V G) gw).bind decode := rfl
  rw [hfp, hr]
  rcases MP.minPath (candN V G) (gsrc V G) gmid gtgt (gedge V G) gw with _ | q
  · simp only [time_pure, Option.bind]; omega
  · rcases q with _ | ⟨x, p⟩
    · simp only [decodeT, time_bind, time_tick, time_pure, Option.bind, decode]; omega
    · have := lmapT_time_le (fun y => (pure y.σ : TimeM StripSpec)) p 0 (fun _ _ => le_rfl)
      simp only [decodeT, time_bind, time_tick, time_pure, Option.bind, decode, List.length_map]
      omega

lemma flipColT_time_le (F : Finset Edge) (c : Pt) (s : Side) :
    ∀ n, (flipColT F c s n).time ≤ flipCost * n + 1 := by
  intro n
  induction n generalizing F with
  | zero => simp [flipColT]
  | succ n ih =>
    have := flipT_time_le F (cellJ c s n)
    have := ih (flipT F (cellJ c s n)).ret
    simp only [flipColT, time_bind]
    rw [Nat.mul_succ]
    omega

lemma roundT_time_le (V : Finset Pt) (G : Finset Edge) : (roundT V G).time ≤ roundCost V G := by
  have h1 := findT3T_time_le V G
  simp only [roundT, roundCost, time_bind, findT3T_ret]
  rcases findT3 V G with _ | ⟨d, tf⟩
  · have h2 := findPathT_time_le V G
    simp only [time_bind, findPathT_ret]
    rcases findPath V G with _ | ⟨a, L⟩
    · simp only [time_pure]; omega
    · have := flipColT_time_le G a.c a.s a.n
      simp only [time_bind, time_pure, applySCost]
      omega
  · have := flipT_time_le G d
    simp only [time_bind, time_pure]
    omega

lemma runT_time_le (V : Finset Pt) : ∀ k G, (runT V k G).time ≤ runCost V k G
  | 0, G => by
    have := cncompT_time_le V G
    simp only [runT, runCost, time_bind, time_tick, time_pure]
    omega
  | k + 1, G => by
    have h1 := cncompT_time_le V G
    simp only [runT, runCost, time_bind, time_tick, cncompT_ret]
    by_cases h : cncomp V G == 1
    · simp only [h, ite_true, time_pure]; omega
    · simp only [h, Bool.false_eq_true, ite_false, time_bind, roundT_ret]
      have h2 := roundT_time_le V G
      rcases step V G with _ | G'
      · simp only [time_pure]; omega
      · have := runT_time_le V k G'
        dsimp only
        omega

theorem ulhcT_time_le (V : Finset Pt) : (ulhcT V).time ≤ ulhcCost V := by
  have h1 := twoFactorT_time_le V
  simp only [ulhcT, ulhcCost, time_bind, twoFactorT_ret, cardT, time_tick,
    fuelN_eq]
  rcases twoFactor V with _ | F
  · simp only [time_pure]; omega
  · have := runT_time_le V (fuel V) F
    dsimp only
    omega

end SolidGridHam.T
