/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import SolidGridHam.Cycle.CostStrips
public import SolidGridHam.Cycle.CostMinPath
public import SolidGridHam.Cycle.CostTwoFactor
public import SolidGridHam.Cycle.Timed.TimeM

@[expose] public section

/-!
# Running time, part 5: rounds, runs and the whole algorithm

* `findT3Cost ≤ 200 N³`, `findPathCost ≤ 6·10⁶ N⁸`, `stepCost ≤ 7·10⁶ N⁸` on a factor.
* `runCost_le`: `k` rounds from a factor cost at most `(k + 1) · 8·10⁶ N⁸`.
* **`ulhcCost_le : ulhcCost V ≤ 5·10⁸ (|V| + 1)¹²`.**

`findT3` charges every (cell, frame) pair (its `find?` may stop earlier), the cells taken from
the sorted cell list (`|V|²` for sorting).
-/

namespace SolidGridHam

open Finset

def cellListCost (V : Finset Pt) : ℕ := 10 * V.card + V.card ^ 2

def t3BCost (V : Finset Pt) (G : Finset Edge) (d : Pt) (tf : Side) : ℕ :=
  10 + connBCost V G (back1 d tf)

def findT3Cost (V : Finset Pt) (G : Finset Edge) : ℕ :=
  cellListCost V + 9 * (cellList V).length +
    (((cellList V).flatMap fun d => sidesL.map fun tf => (d, tf)).map
      fun p => t3BCost V G p.1 p.2 + 1).sum

-- `decode`: one step per strip of the returned path.
--
def decodeCost (V : Finset Pt) (G : Finset Edge) : ℕ :=
  match findPath V G with
  | some (_, L) => L.length + 2
  | none => 1

def findPathCost (V : Finset Pt) (G : Finset Edge) : ℕ :=
  candNCost V G +
    MP.minPathCost (candN V G) gmid gtgt (gedge V G) gw (gedgeCost V G) (gsrcCost V G) +
    decodeCost V G

-- Flipping a strip of `n` cells.
--
def applySCost (a : StripSpec) : ℕ := flipCost * a.n + 1

def roundCost (V : Finset Pt) (G : Finset Edge) : ℕ :=
  findT3Cost V G +
    match findT3 V G with
    | some _ => flipCost
    | none =>
      findPathCost V G +
        match findPath V G with
        | some (a, _) => applySCost a
        | none => 0

def runCost (V : Finset Pt) : ℕ → Finset Edge → ℕ
  | 0, G => cncompCost V G + 2
  | k + 1, G =>
    cncompCost V G + 2 +
      if cncomp V G == 1 then 0
      else roundCost V G +
        match step V G with
        | some G' => runCost V k G'
        | none => 0

-- `fuel V`: the size of `V` and a few products.
--
def ulhcCost (V : Finset Pt) : ℕ :=
  twoFactorCost V + V.card + 10 +
    match twoFactor V with
    | some F => runCost V (fuel V) F
    | none => 0

/-! ## Bounds -/

section bounds

variable {V : Finset Pt} {G : Finset Edge}

lemma length_cellList (V : Finset Pt) : (cellList V).length ≤ V.card := by
  unfold cellList
  rw [List.length_map, Finset.length_sort, Finset.card_map]
  exact card_filter_le _ _

lemma findT3Cost_le (hGV : Inside V G) : findT3Cost V G ≤ 200 * (V.card + 1) ^ 3 := by
  have hl := length_cellList V
  have hps : ((cellList V).flatMap fun d => sidesL.map fun tf => (d, tf)).length =
      4 * (cellList V).length := by
    rw [List.length_flatMap]
    simp only [List.length_map]
    have : ∀ l : List Pt, (l.map fun _ => sidesL.length).sum = 4 * l.length := by
      intro l; simp [sidesL]; ring
    exact this _
  have h1 := T.lsum_le ((cellList V).flatMap fun d => sidesL.map fun tf => (d, tf))
    (fun p => t3BCost V G p.1 p.2 + 1) (11 + 30 * (V.card + 1) ^ 2) (fun p _ => by
      have := connBCost_le hGV (back1 p.1 p.2); unfold t3BCost; omega)
  rw [hps] at h1
  unfold findT3Cost cellListCost
  nlinarith

-- Every strip of a path has a cell, so a path has at most its weight in strips.
--
lemma chain_len {V : Finset Pt} {G : Finset Edge} :
    ∀ (L : List StripSpec) (σ : StripSpec), CRChain V G σ L → L.length ≤ (L.map StripSpec.n).sum
  | [], _, _ => by simp
  | τ :: L, _, h => by
    have h1 : 1 ≤ τ.n := h.2.1.2.2.1
    have := chain_len L τ h.2.2
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    omega

lemma decodeCost_le (hGV : Inside V G) : decodeCost V G ≤ Dm V + 2 := by
  unfold decodeCost
  rcases hp : findPath V G with _ | ⟨σ, L⟩
  · simp
  · simp only
    have hP := (findPath_some hGV hp).1
    have h1 := chain_len L σ hP.1.2
    have h2 := dval_le (V := V) hGV
    rw [dval_eq hp] at h2
    unfold wt at h2
    omega

-- The bound of `MP.minPathCost_le` at `n ≤ 24 N²`, `E = 300 N²`, `S = 160 N²`.
--
lemma poly8 (N n : ℕ) (hN : 1 ≤ N) (hn : n ≤ 24 * N ^ 2) :
    n ^ 2 + n * (n * (n * (300 * N ^ 2 + n + 5) + 4)) + n * (160 * N ^ 2 + n + 3) + n + 4 ≤
      5000000 * N ^ 8 := by
  calc n ^ 2 + n * (n * (n * (300 * N ^ 2 + n + 5) + 4)) + n * (160 * N ^ 2 + n + 3) + n + 4
      ≤ (24 * N ^ 2) ^ 2 + (24 * N ^ 2) * ((24 * N ^ 2) * ((24 * N ^ 2) *
          (300 * N ^ 2 + 24 * N ^ 2 + 5) + 4)) + (24 * N ^ 2) * (160 * N ^ 2 + 24 * N ^ 2 + 3) +
          24 * N ^ 2 + 4 := by
        gcongr
    _ ≤ 5000000 * N ^ 8 := by
        set M := N ^ 2 with hM
        have h1 : 1 ≤ M := Nat.one_le_pow _ _ hN
        have h8 : N ^ 8 = M ^ 4 := by rw [hM, ← pow_mul]
        rw [h8]
        have a1 : M ≤ M ^ 2 := by nlinarith
        have a2 : M ^ 2 ≤ M ^ 3 := by nlinarith
        have a3 : M ^ 3 ≤ M ^ 4 := by nlinarith
        nlinarith

lemma findPathCost_le (hGV : Inside V G) : findPathCost V G ≤ 6000000 * (V.card + 1) ^ 8 := by
  have hN : 1 ≤ V.card + 1 := by omega
  have hn : (candN V G).card ≤ 24 * (V.card + 1) ^ 2 := by
    have := card_candN_le (V := V) G; unfold Bd at this; nlinarith
  have hmp := MP.minPathCost_le (candN V G) gmid gtgt (gedge V G) gw (gedgeCost V G)
    (gsrcCost V G) (E := 300 * (V.card + 1) ^ 2) (S := 160 * (V.card + 1) ^ 2)
    (fun x hx y hy => gedgeCost_le hGV hx hy) (fun x _ => gsrcCost_le hGV x)
  have hp := poly8 (V.card + 1) _ hN hn
  have h1 := candNCost_le (V := V) G
  have h2 := decodeCost_le hGV
  have h3 : Dm V ≤ 24 * (V.card + 1) ^ 3 := by unfold Dm Bd; nlinarith
  have h4 : (V.card + 1) ^ 3 ≤ (V.card + 1) ^ 8 := Nat.pow_le_pow_right hN (by omega)
  unfold findPathCost
  omega

lemma roundCost_le (hG : Deg2 V G) : roundCost V G ≤ 7000000 * (V.card + 1) ^ 8 := by
  have hN : 1 ≤ V.card + 1 := by omega
  have h1 := findT3Cost_le hG.1
  have h2 := findPathCost_le hG.1
  have h4 : (V.card + 1) ^ 3 ≤ (V.card + 1) ^ 8 := Nat.pow_le_pow_right hN (by omega)
  have h5 : V.card + 1 ≤ (V.card + 1) ^ 8 := Nat.le_self_pow (by omega) _
  have ha : ∀ a L, findPath V G = some (a, L) → applySCost a ≤ 8 * V.card + 1 := by
    intro a L hp
    have hv := (findPath_some hG.1 hp).1.1.1
    have := len_le_card hv.2.2.1
    unfold applySCost flipCost; omega
  unfold roundCost
  split
  · unfold flipCost; omega
  · split
    · rename_i a L hp
      have := ha a L hp
      show findT3Cost V G + (findPathCost V G + applySCost a) ≤ _
      omega
    · show findT3Cost V G + (findPathCost V G + 0) ≤ _
      omega

theorem runCost_le : ∀ (k : ℕ) (G : Finset Edge), Deg2 V G →
    runCost V k G ≤ (k + 1) * (8000000 * (V.card + 1) ^ 8) := by
  have hN : 1 ≤ V.card + 1 := by omega
  have h4 : (V.card + 1) ^ 3 ≤ (V.card + 1) ^ 8 := Nat.pow_le_pow_right hN (by omega)
  have h5 : 1 ≤ (V.card + 1) ^ 8 := Nat.one_le_pow _ _ hN
  intro k
  induction k with
  | zero =>
    intro G hG
    have := cncompCost_le hG.1
    simp only [runCost]
    omega
  | succ k ih =>
    intro G hG
    have hc := cncompCost_le hG.1
    have hr := roundCost_le hG
    simp only [runCost]
    split
    · nlinarith
    · rcases hs : step V G with _ | G'
      · simp only; nlinarith
      · simp only
        have := ih G' (step_deg2 hG hs)
        nlinarith

/-- **Running time.** The algorithm makes at most `5·10⁸ (|V| + 1)¹²` elementary steps. -/
theorem ulhcCost_le (V : Finset Pt) : ulhcCost V ≤ 500000000 * (V.card + 1) ^ 12 := by
  have hN : 1 ≤ V.card + 1 := by omega
  have h0 := twoFactorCost_le V
  have h3 : (V.card + 1) ^ 3 ≤ (V.card + 1) ^ 12 := Nat.pow_le_pow_right hN (by omega)
  have hf : fuel V + 1 ≤ 55 * (V.card + 1) ^ 4 := by
    unfold fuel Dm Bd
    have a1 : 1 ≤ (V.card + 1) ^ 4 := Nat.one_le_pow _ _ hN
    nlinarith
  have h12 : (V.card + 1) ^ 4 * (V.card + 1) ^ 8 = (V.card + 1) ^ 12 := by rw [← pow_add]
  unfold ulhcCost
  split
  · rename_i F hF
    have := runCost_le (fuel V) F (twoFactor_some hF)
    have : V.card + 10 ≤ 11 * (V.card + 1) ^ 12 := by
      have := Nat.le_self_pow (n := 12) (by omega) (V.card + 1); omega
    nlinarith
  · have : V.card + 10 ≤ 11 * (V.card + 1) ^ 12 := by
      have := Nat.le_self_pow (n := 12) (by omega) (V.card + 1); omega
    omega

end bounds

end SolidGridHam
