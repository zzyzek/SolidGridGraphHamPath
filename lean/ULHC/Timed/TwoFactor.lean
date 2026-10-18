/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.Timed.Conn
import ULHC.CostTwoFactor

/-!
# Counted starting 2-factor

Counted versions of `nbr`, `layerAcc`, `pred`, `walk`, `augStep`, `augLoop` and `twoFactor`,
with results equal to the originals and steps bounded by the costs of `CostTwoFactor.lean`.
-/

namespace ULHC.T

open Finset TF

/-! ## Counted definitions -/

def fwdT (V : Finset Pt) (F : Finset Edge) (u : Pt) (e : Edge) : TimeM Bool := do
  let a ← memT e.p V
  let b ← memT e.q V
  let m ← memT e F
  tick 4
  pure (a && b && (if Black u then !m else m))

def nbrT (V : Finset Pt) (F : Finset Edge) (u : Pt) : TimeM (Finset Pt) := do
  let l ← lfilterT (fwdT V F u) (inc4 u)
  let l' ← lmapT (fun e => pure (other e u)) l
  toFinsetT l'

def layerAccT (V : Finset Pt) (F : Finset Edge) : ℕ → TimeM (List (Finset Pt))
  | 0 => do
    let L ← filterT (fun z => do
      let d ← degT F z
      tick 2
      pure ((Black z : Bool) && (d < 2 : Bool))) V
    pure [L]
  | k + 1 => do
    let A ← layerAccT V F k
    match A with
    | [] => do
      tick 1
      pure []
    | L :: Ls => do
      let Bs ← biUnionT (nbrT V F) L
      let L' ← unionT L Bs
      tick 1
      pure (L' :: L :: Ls)

def bwdT (V : Finset Pt) (F : Finset Edge) (L : Finset Pt) (v : Pt) (e : Edge) : TimeM Bool := do
  let a ← memT e.p V
  let b ← memT e.q V
  let o ← memT (other e v) L
  let m ← memT e F
  tick 4
  pure (a && b && o && (if Black v then m else !m))

def predT (V : Finset Pt) (F : Finset Edge) (L : Finset Pt) (v : Pt) : TimeM (Option Edge) :=
  lfindT (bwdT V F L v) (inc4 v)

def boundaryEndpointsWalk (V : Finset Pt) (F0 : Finset Edge) :
    List (Finset Pt) → Pt → Finset Edge → TimeM (Finset Edge)
  | [], _, F => do
    tick 1
    pure F
  | L :: Ls, v, F => do
    let b ← memT v L
    tick 1
    if b then boundaryEndpointsWalk V F0 Ls v F
    else do
      let p ← predT V F0 L v
      match p with
      | none => pure F
      | some e => do
        let F' ← if Black v then eraseT e F else insertT e F
        tick 1
        boundaryEndpointsWalk V F0 Ls (other e v) F'

def augStepT (V : Finset Pt) (F : Finset Edge) : TimeM (Option (Finset Edge)) := do
  let n ← cardT V
  let A ← layerAccT V F n
  match A with
  | [] => do
    tick 1
    pure none
  | L :: Ls => do
    let S ← filterT (fun w => do
      let d ← degT F w
      tick 2
      pure (!(Black w : Bool) && (d < 2 : Bool))) L
    let p ← pickT S
    match p with
    | none => pure none
    | some w => do
      let F' ← boundaryEndpointsWalk V F Ls w F
      pure (some F')

def augLoopT (V : Finset Pt) : ℕ → Finset Edge → TimeM (Finset Edge)
  | 0, F => do
    tick 1
    pure F
  | n + 1, F => do
    let r ← augStepT V F
    tick 1
    match r with
    | none => pure F
    | some F' => augLoopT V n F'

def twoFactorT (V : Finset Pt) : TimeM (Option (Finset Edge)) := do
  let n ← cardT V
  let F ← augLoopT V (n + 1) ∅
  let ok ← allT (fun z => do
    let d ← degT F z
    tick 1
    pure (eqN d 2)) V
  tick 1
  pure (if ok then some F else none)

/-! ## Results -/

@[simp] lemma fwdT_ret (V : Finset Pt) (F : Finset Edge) (u : Pt) (e : Edge) :
    (fwdT V F u e).ret = decide (Fwd V F u e) := by
  unfold fwdT Fwd IsEdge
  by_cases h : Black u <;> simp [memT, h, Bool.and_assoc]

@[simp] lemma nbrT_ret (V : Finset Pt) (F : Finset Edge) (u : Pt) : (nbrT V F u).ret = nbr V F u := by
  simp [nbrT, nbr, lfilterT, lmapT, toFinsetT]

@[simp] lemma layerAccT_ret (V : Finset Pt) (F : Finset Edge) :
    ∀ k, (layerAccT V F k).ret = layerAcc V F k
  | 0 => by
    simp only [layerAccT, layerAcc, ret_bind, ret_pure, filterT, degT_ret]
    congr 2
    ext z
    simp
  | k + 1 => by
    have ih := layerAccT_ret V F k
    simp only [layerAccT, layerAcc, ret_bind, ih]
    rw [layerAcc_eq]
    simp [unionT, biUnionT]

@[simp] lemma bwdT_ret (V : Finset Pt) (F : Finset Edge) (L : Finset Pt) (v : Pt) (e : Edge) :
    (bwdT V F L v e).ret = decide (Bwd V F L v e) := by
  unfold bwdT Bwd IsEdge
  by_cases h : Black v <;> simp [memT, h, Bool.and_assoc]

@[simp] lemma predT_ret (V : Finset Pt) (F : Finset Edge) (L : Finset Pt) (v : Pt) :
    (predT V F L v).ret = pred V F L v := by
  simp [predT, pred, lfindT]

@[simp] lemma boundaryEndpointsWalk_ret (V : Finset Pt) (F0 : Finset Edge) :
    ∀ (Ls : List (Finset Pt)) (v : Pt) (F : Finset Edge), (boundaryEndpointsWalk V F0 Ls v F).ret = walk V F0 Ls v F
  | [], _, _ => rfl
  | L :: Ls, v, F => by
    simp only [boundaryEndpointsWalk, walk, ret_bind, memT]
    by_cases hv : v ∈ L
    · simp [hv, boundaryEndpointsWalk_ret V F0 Ls v F]
    · simp only [hv, decide_false, Bool.false_eq_true, ite_false, ret_bind, predT_ret]
      rcases pred V F0 L v with _ | e
      · rfl
      · by_cases hb : Black v
        · simp [hb, eraseT, boundaryEndpointsWalk_ret V F0 Ls (other e v) (F.erase e)]
        · simp [hb, insertT, boundaryEndpointsWalk_ret V F0 Ls (other e v) (insert e F)]

@[simp] lemma augStepT_ret (V : Finset Pt) (F : Finset Edge) : (augStepT V F).ret = augStep V F := by
  simp only [augStepT, augStep, ret_bind, cardT, layerAccT_ret]
  rw [layerAcc_eq]
  simp only [ret_bind, filterT, pickT, degT_ret, ret_pure]
  have hf : (layer V F V.card).filter (fun w => (!decide (Black w) && decide (deg F w < 2)) = true) =
      (layer V F V.card).filter (fun w => ¬ Black w ∧ deg F w < 2) := by
    ext w; simp
  rw [hf]
  rcases TF.pick ((layer V F V.card).filter (fun w => ¬ Black w ∧ deg F w < 2)) with _ | w
  · rfl
  · simp

@[simp] lemma augLoopT_ret (V : Finset Pt) :
    ∀ n F, (augLoopT V n F).ret = augLoop V n F
  | 0, _ => rfl
  | n + 1, F => by
    simp only [augLoopT, augLoop, ret_bind, augStepT_ret]
    rcases augStep V F with _ | F'
    · rfl
    · exact augLoopT_ret V n F'

@[simp] lemma twoFactorT_ret (V : Finset Pt) : (twoFactorT V).ret = twoFactor V := by
  simp only [twoFactorT, twoFactor, ret_bind, cardT, allT, augLoopT_ret, degT_ret, eqN,
    ret_pure, decide_eq_true_eq]

/-! ## Steps -/

lemma fwdT_time (V : Finset Pt) (F : Finset Edge) (u : Pt) (e : Edge) : (fwdT V F u e).time = 7 := by
  simp [fwdT, memT]

lemma nbrT_time_le (V : Finset Pt) (F : Finset Edge) (u : Pt) : (nbrT V F u).time ≤ 41 := by
  have h1 := lfilterT_time_le (fwdT V F u) (inc4 u) 7 (fun e _ => (fwdT_time V F u e).le)
  have hl : (inc4 u).length = 4 := rfl
  have hlen : ((inc4 u).filter (fun e => (fwdT V F u e).ret)).length ≤ 4 :=
    (List.length_filter_le _ _).trans hl.le
  have h2 := lmapT_time_le (fun e => (pure (other e u) : TimeM Pt))
    ((inc4 u).filter (fun e => (fwdT V F u e).ret)) 0 (fun _ _ => le_rfl)
  simp only [nbrT, time_bind, toFinsetT, lmapT, List.length_map]
  simp only [lfilterT] at h1 ⊢
  simp only [lmapT] at h2
  rw [hl] at h1
  omega

lemma layerAccT_time_le (V : Finset Pt) (F : Finset Edge) :
    ∀ k, (layerAccT V F k).time ≤ layerAccCost V F k
  | 0 => by
    have := filterT_time_le (fun z => (do
      let d ← degT F z
      tick 2
      pure ((Black z : Bool) && (d < 2 : Bool)) : TimeM Bool)) V 10
      (fun z _ => by simp [degT_time])
    simp only [layerAccT, time_bind, time_pure, layerAccCost]
    omega
  | k + 1 => by
    have ih := layerAccT_time_le V F k
    simp only [layerAccT, layerAccCost, time_bind, layerAccT_ret]
    rw [layerAcc_eq]
    simp only [time_bind, time_tick, time_pure, biUnionT, unionT]
    have hs : ∑ u ∈ layer V F k, ((nbrT V F u).time + (nbrT V F u).ret.card + 1) ≤
        ∑ u ∈ layer V F k, (nbrCost + (nbr V F u).card) :=
      Finset.sum_le_sum (fun u _ => by
        have := nbrT_time_le V F u; rw [nbrT_ret]; unfold nbrCost; omega)
    have he : ((layer V F k).biUnion fun u => (nbrT V F u).ret).card =
        ((layer V F k).biUnion (nbr V F)).card := by simp
    omega

lemma bwdT_time (V : Finset Pt) (F : Finset Edge) (L : Finset Pt) (v : Pt) (e : Edge) :
    (bwdT V F L v e).time = 8 := by
  simp [bwdT, memT]

lemma predT_time_le (V : Finset Pt) (F : Finset Edge) (L : Finset Pt) (v : Pt) :
    (predT V F L v).time ≤ predCost := by
  have := lfindT_time_le (bwdT V F L v) (inc4 v) 8 (fun e _ => (bwdT_time V F L v e).le)
  have hl : (inc4 v).length = 4 := rfl
  unfold predT predCost
  omega

lemma boundaryEndpointsWalk_time_le (V : Finset Pt) (F0 : Finset Edge) :
    ∀ (Ls : List (Finset Pt)) (v : Pt) (F : Finset Edge), (boundaryEndpointsWalk V F0 Ls v F).time ≤ walkCost V F0 Ls v F
  | [], _, _ => by simp [boundaryEndpointsWalk, walkCost]
  | L :: Ls, v, F => by
    simp only [boundaryEndpointsWalk, walkCost, time_bind, memT, time_tick]
    by_cases hv : v ∈ L
    · simp only [hv, decide_true, ite_true]
      have := boundaryEndpointsWalk_time_le V F0 Ls v F; omega
    · simp only [hv, decide_false, Bool.false_eq_true, ite_false, time_bind, predT_ret]
      have hp := predT_time_le V F0 L v
      rcases pred V F0 L v with _ | e
      · simp only [time_pure]; omega
      · by_cases hb : Black v
        · simp only [hb, ite_true, time_bind, eraseT, time_tick]
          have := boundaryEndpointsWalk_time_le V F0 Ls (other e v) (F.erase e); omega
        · simp only [hb, ite_false, time_bind, insertT, time_tick]
          have := boundaryEndpointsWalk_time_le V F0 Ls (other e v) (insert e F); omega

lemma augStepT_time_le (V : Finset Pt) (F : Finset Edge) : (augStepT V F).time ≤ augStepCost V F := by
  have h0 := layerAccT_time_le V F V.card
  simp only [augStepT, augStepCost, time_bind, cardT, layerAccT_ret]
  rw [layerAcc_eq]
  simp only [time_bind, pickT]
  have hfe : (filterT (fun w => (do
      let d ← degT F w
      tick 2
      pure (!(Black w : Bool) && (d < 2 : Bool)) : TimeM Bool)) (layer V F V.card)).ret =
      (layer V F V.card).filter (fun w => ¬ Black w ∧ deg F w < 2) := by
    ext w; simp [filterT]
  have hft : (filterT (fun w => (do
      let d ← degT F w
      tick 2
      pure (!(Black w : Bool) && (d < 2 : Bool)) : TimeM Bool)) (layer V F V.card)).time =
      ∑ _w ∈ layer V F V.card, (degCost + 3) := by
    simp [filterT, degT_time, degCost]
  rw [hft, hfe]
  rcases TF.pick ((layer V F V.card).filter (fun w => ¬ Black w ∧ deg F w < 2)) with _ | w
  · simp only [time_pure]; unfold pickCost; omega
  · simp only [time_bind, time_pure]
    have := boundaryEndpointsWalk_time_le V F (layersBelow V F V.card) w F
    unfold pickCost; omega

lemma augLoopT_time_le (V : Finset Pt) :
    ∀ n F, (augLoopT V n F).time ≤ augLoopCost V n F
  | 0, _ => by simp [augLoopT, augLoopCost]
  | n + 1, F => by
    have h1 := augStepT_time_le V F
    simp only [augLoopT, augLoopCost, time_bind, time_tick, augStepT_ret]
    rcases augStep V F with _ | F'
    · simp only [time_pure]; omega
    · have := augLoopT_time_le V n F'
      dsimp only
      omega

lemma twoFactorT_time_le (V : Finset Pt) : (twoFactorT V).time ≤ twoFactorCost V := by
  have h1 := augLoopT_time_le V (V.card + 1) ∅
  have h2 := allT_time_le (fun z => (do
    let d ← degT (augLoop V (V.card + 1) ∅) z
    tick 1
    pure (eqN d 2) : TimeM Bool)) V 9 (fun z _ => by simp [degT_time])
  simp only [twoFactorT, twoFactorCost, time_bind, cardT, time_tick, time_pure,
    augLoopT_ret]
  unfold degCost
  omega

end ULHC.T
