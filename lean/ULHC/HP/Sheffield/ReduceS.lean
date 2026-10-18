/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.HP.Sheffield.PhaseS
import ULHC.HP.Sheffield.TwoPhCost

/-!
# The undo with connections computed once per state, and the fast two-phantom loop

`reduceOutC` decides the undo plan through `connB` on the states `H_1, H_2, …` reached by flipping
the bridge ends, once per candidate cell and once per bridge index. `reducePieces` builds the
connection sets of these states once (`bridgeStatesConn`), computes each candidate's plan once
(`undoPlanSteps`), and returns exactly what `reduceOutC` returns (`reducePieces_eq`).

`twoPhantomLoop` is the two-phantom loop with `runPhase` and `reducePieces`; it returns what `runSC2` returns
on every two-phantom state (`twoPhantomLoop_eq`).
-/

namespace ULHC

namespace HP

open Finset Classical

def bridgeStatesConn (W : Finset Pt) : Finset Edge → List Bridge → List (Finset (Pt × Pt))
  | _, [] => []
  | H, b :: BS => connectedPairs W (flip H b.E) :: bridgeStatesConn W (flip H b.E) BS

def undoPlanSteps : List (Finset (Pt × Pt)) → List Bridge → Pt × Pt → List (Bool × (Pt × Pt))
  | S :: Ss, b :: BS, uv =>
    if isConnected S uv.1 uv.2 then (true, uv) :: undoPlanSteps Ss BS (rowStartPair b)
    else (false, uv) :: undoPlanSteps Ss BS uv
  | _, _, _ => []

def undoPlan (Ss : List (Finset (Pt × Pt))) (BS : List Bridge) (uv : Pt × Pt) : List Join :=
  List.zipWith (fun b e => if e.1 then lowJ b else undoJ b) BS (undoPlanSteps Ss BS uv)

def isGoodMergingCell (W : Finset Pt) (H : Finset Edge) (BS : List Bridge) (Ss : List (Finset (Pt × Pt)))
    (X : Pt) : Bool :=
  decide (Alt H X) && cutB W H X && !pairSqB BS X &&
    (let P := undoPlanSteps Ss BS (mergePair H X)
     (List.finRange BS.length).all fun i =>
      (P.getD i (false, mergePair H X)).1 || decide (X ≠ nb (BS.get i).E (BS.get i).a))

def reducePieces (V W : Finset Pt) (H : Finset Edge) (BS : List Bridge) : POut → Finset Edge
  | .merge c =>
    let Ss := bridgeStatesConn W H BS
    let X := ((cellList V).find? (isGoodMergingCell W H BS Ss)).getD c
    applyAll (flipCol H X (altFrame H X) 1) (undoPlan Ss BS (mergePair H X))
  | .odd b => applyAll (flipCol H b.q b.a b.r) (undoPlan (bridgeStatesConn W H BS) BS (rowStartPair b))
  | .twist b => applyAll (flipCol H b.q b.a b.r) (undoPlan (bridgeStatesConn W H BS) BS (rowStartPair b))
  | _ => H

section eq

variable {W : Finset Pt}

lemma undoPlanSteps_eq : ∀ (BS : List Bridge) (H : Finset Edge) (uv : Pt × Pt),
    Inside W H → uv.1 ∈ W → BrW W BS → undoPlanSteps (bridgeStatesConn W H BS) BS uv = planAB W H BS uv
  | [], _, _, _, _, _ => by simp [bridgeStatesConn, undoPlanSteps, planAB]
  | b :: BS, H, uv, hH, h1, hb => by
    have hbE := hb b List.mem_cons_self
    have hH' : Inside W (flip H b.E) := inside_flip hH hbE.1
    have hBS : BrW W BS := fun b' hb' => hb b' (List.mem_cons_of_mem _ hb')
    have hsp := corners_mem hbE.2 b.a
    simp only [bridgeStatesConn, undoPlanSteps, planAB]
    rw [isConnected_eq hH' h1]
    split_ifs
    · rw [undoPlanSteps_eq BS _ _ hH' hsp.1 hBS]
    · rw [undoPlanSteps_eq BS _ _ hH' h1 hBS]

lemma undoPlan_eq {BS : List Bridge} {H : Finset Edge} {uv : Pt × Pt} (hH : Inside W H)
    (h1 : uv.1 ∈ W) (hb : BrW W BS) : undoPlan (bridgeStatesConn W H BS) BS uv = planB W H BS uv := by
  unfold undoPlan planB; rw [undoPlanSteps_eq BS H uv hH h1 hb]

lemma isGoodMergingCell_eq {BS : List Bridge} {H : Finset Edge} (hH : Inside W H) (hb : BrW W BS) {X : Pt}
    (hX : IsCell W X) : isGoodMergingCell W H BS (bridgeStatesConn W H BS) X = goodB W H BS X := by
  have hcc := corners_mem hX (altFrame H X)
  unfold isGoodMergingCell goodB lowAtB
  rw [undoPlanSteps_eq BS H _ hH hcc.1 hb]

-- **`reducePieces` is `reduceOutC`** for states inside `W` whose bridges and output cells are cells
-- of `W`.
--
theorem reducePieces_eq {V : Finset Pt} (hVW : V ⊆ W) {H : Finset Edge} {BS : List Bridge}
    {out : POut} (hH : Inside W H) (hb : BrW W BS)
    (hc : ∀ c, out = .merge c → IsCell V c)
    (hg : ∀ g, (out = .odd g ∨ out = .twist g) → IsCell V g.q) :
    reducePieces V W H BS out = reduceOutC V W H BS out := by
  cases out with
  | stuck => rfl
  | fuel => rfl
  | odd g =>
    have hq := corners_mem (isCell_mono (hg g (Or.inl rfl)) hVW) g.a
    simp only [reducePieces, reduceOutC]
    rw [undoPlan_eq hH hq.1 hb]
  | twist g =>
    have hq := corners_mem (isCell_mono (hg g (Or.inr rfl)) hVW) g.a
    simp only [reducePieces, reduceOutC]
    rw [undoPlan_eq hH hq.1 hb]
  | merge c =>
    simp only [reducePieces, reduceOutC]
    have hfind : (cellList V).find? (isGoodMergingCell W H BS (bridgeStatesConn W H BS)) =
        (cellList V).find? (goodB W H BS) :=
      find?_congr (fun X hX => isGoodMergingCell_eq hH hb (isCell_mono (mem_cellList.1 hX).2 hVW))
    rw [hfind]
    have hX : IsCell V (((cellList V).find? (goodB W H BS)).getD c) := by
      rcases h : (cellList V).find? (goodB W H BS) with _ | X
      · exact hc c rfl
      · exact (mem_cellList.1 (List.mem_of_find?_eq_some h)).2
    have hcc := corners_mem (isCell_mono hX hVW)
      (altFrame H (((cellList V).find? (goodB W H BS)).getD c))
    rw [undoPlan_eq hH hcc.1 hb]

end eq

/-! ## The fast two-phantom loop -/

def twoPhantomLoop (V : Finset Pt) (p q : Pt) : ℕ → Finset Edge → Bool
  | 0, G => cncomp (insert q (insert p V)) G == 1
  | n + 1, G =>
    if cncomp (insert q (insert p V)) G == 1 then true
    else
      match runPhase V (insert q (insert p V)) ((insert q (insert p V)).card + 1) G [] with
      | (_, _, .stuck) => false
      | (_, _, .fuel) => false
      | (H, BS, out) => twoPhantomLoop V p q n (reducePieces V (insert q (insert p V)) H BS out)

section loopF

variable {V : Finset Pt} {s t p q : Pt} {e0 e1 : Edge}
  (hsV : s ∈ V) (htV : t ∈ V) (hpV : p ∉ V) (hqV : q ∉ V)
  (he0 : Ends e0 t p) (he1 : Ends e1 s q) (hfr : FarN t p s q)
include hsV htV hpV hqV he0 he1 hfr

-- **The fast loop is the loop.**
--
theorem twoPhantomLoop_eq : ∀ n G, NotchF2 V p q e0 e1 G → twoPhantomLoop V p q n G = runSC2 V p q n G := by
  intro n
  induction n with
  | zero => intro G _; rfl
  | succ n ih =>
    intro G hG
    simp only [twoPhantomLoop, runSC2]
    by_cases h1 : (cncomp (insert q (insert p V)) G == 1) = true
    · rw [ite_eq_left h1, ite_eq_left h1]
    rw [ite_eq_right h1, ite_eq_right h1]
    have hPhI : PhI V (insert q (insert p V)) G [] := ⟨Inside.of_factor hG.fac, by simp⟩
    rw [runPhase_eq vw2 _ G [] hPhI]
    have hpok := two_pok hsV htV hpV hqV he0 he1 hG ((insert q (insert p V)).card + 1)
    rcases hph : phase V (insert q (insert p V)) ((insert q (insert p V)).card + 1) G [] with
      ⟨H, BS, out⟩
    rw [hph] at hpok
    cases out with
    | stuck => rfl
    | fuel => rfl
    | merge c =>
      obtain ⟨hHW, hb⟩ := brW2 hsV htV hpV hqV he0 he1 hG hpok.1
      simp only
      rw [reducePieces_eq vw2 hHW hb (fun c' h => by cases h; exact hpok.2.1)
        (fun g h => by rcases h with h | h <;> cases h)]
      exact ih _ (s4C2 hsV htV hpV hqV he0 he1 hfr hG hpok (by simp) (by simp)).1
    | odd g =>
      obtain ⟨hHW, hb⟩ := brW2 hsV htV hpV hqV he0 he1 hG hpok.1
      simp only
      rw [reducePieces_eq vw2 hHW hb (fun c' h => by cases h)
        (fun g' h => by rcases h with h | h <;> cases h; exact hpok.2.2.1.1)]
      exact ih _ (s4C2 hsV htV hpV hqV he0 he1 hfr hG hpok (by simp) (by simp)).1
    | twist g =>
      obtain ⟨hHW, hb⟩ := brW2 hsV htV hpV hqV he0 he1 hG hpok.1
      simp only
      rw [reducePieces_eq vw2 hHW hb (fun c' h => by cases h)
        (fun g' h => by rcases h with h | h <;> cases h; exact hpok.2.2.1.1)]
      exact ih _ (s4C2 hsV htV hpV hqV he0 he1 hfr hG hpok (by simp) (by simp)).1

end loopF

end HP

end ULHC
