/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.CostAlg
import ULHC.CostMinPathT
import ULHC.HP.CompletePF

/-!
# Running time of the path-factor algorithm, part 1: the tests

Costs of the pieces of one round of `stepPF`, in the style of ULHC's `CostAlg` (each test
charged by its evaluation), with `N = |V| + 1`:

* `findT3R`: `≤ 240 N³` (ULHC's `findT3` plus the two corner tests per pair);
* `Mc` (component count and the two Type III searches): `≤ 490 N³`;
* the end test `ptgt` (at position 1 it applies the strip and computes `Mc` twice): `≤ 1000 N³`;
* the edge and source tests: `≤ 310 N²`, `≤ 165 N²`.
-/

namespace ULHC

namespace HP

open Finset Classical

-- A strip flip of cells in `V` keeps the edges inside `V`.
--
lemma inside_flipCol {V : Finset Pt} {c : Pt} {s : Side} :
    ∀ n (F : Finset Edge), Inside V F → (∀ j < n, IsCell V (cellJ c s j)) →
      Inside V (flipCol F c s n) := by
  intro n
  induction n with
  | zero => intro F hF _; exact hF
  | succ n ih =>
    intro F hF hc
    rw [flipCol_succ]
    exact ih _ (inside_flip hF (hc n (by omega))) (fun j hj => hc j (by omega))

def findT3RCost (V : Finset Pt) (G : Finset Edge) : ℕ := findT3Cost V G + 40 * V.card

def McCost (V : Finset Pt) (G : Finset Edge) : ℕ :=
  cncompCost V G + findT3RCost V G + findT3Cost V G + 10

def twistBCost (V : Finset Pt) (G : Finset Edge) (u : Pt) : ℕ :=
  20 + flipCost + cncompCost V (flip G u) + cncompCost V G

def ptgtCost (V : Finset Pt) (G : Finset Edge) (x : PNode) : ℕ :=
  if x.pos == 1 then applySCost x.σ + McCost V (applyS G x.σ) + McCost V G + 5
  else twistBCost V G (endCell x.σ) + 10

def pedgeCost (V : Finset Pt) (G : Finset Edge) (x y : PNode) : ℕ :=
  10 + cr2BCost V G x.σ y.σ + chainOKBCost y.σ

def psrcCost (V : Finset Pt) (G : Finset Edge) (x : PNode) : ℕ := 5 + validBCost V G x.σ

section bounds

variable {V : Finset Pt} {G : Finset Edge} {s t : Pt}

lemma findT3RCost_le (hGV : Inside V G) : findT3RCost V G ≤ 240 * (V.card + 1) ^ 3 := by
  have h := findT3Cost_le hGV
  have : V.card ≤ (V.card + 1) ^ 3 := by
    have := Nat.le_self_pow (n := 3) (by omega) (V.card + 1); omega
  unfold findT3RCost; omega

lemma McCost_le (hGV : Inside V G) : McCost V G ≤ 490 * (V.card + 1) ^ 3 := by
  have h1 := cncompCost_le hGV
  have h2 := findT3RCost_le hGV
  have h3 := findT3Cost_le hGV
  have : 1 ≤ (V.card + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  unfold McCost; omega

lemma twistBCost_le (hGV : Inside V G) {u : Pt} (hu : IsCell V u) :
    twistBCost V G u ≤ 100 * (V.card + 1) ^ 3 := by
  have h1 := cncompCost_le hGV
  have h2 := cncompCost_le (inside_flip hGV hu)
  have : 1 ≤ (V.card + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  unfold twistBCost flipCost; omega

lemma pnode_len {x : PNode} (hx : x ∈ pnodes V G s t) :
    1 ≤ x.σ.n ∧ x.σ.n ≤ V.card ∧ ∀ j < x.σ.n, IsCell V (cellJ x.σ.c x.σ.s j) := by
  obtain ⟨h1, hc⟩ := cells_of_cand (mem_pnodes_cand hx).1
  exact ⟨h1, len_le_card hc, hc⟩

lemma ptgtCost_le (hGV : Inside V G) {x : PNode} (hx : x ∈ pnodes V G s t) :
    ptgtCost V G x ≤ 1000 * (V.card + 1) ^ 3 := by
  obtain ⟨h1, hn, hc⟩ := pnode_len hx
  have hN : V.card + 1 ≤ (V.card + 1) ^ 3 := Nat.le_self_pow (by omega) _
  unfold ptgtCost
  split
  · have hA : Inside V (applyS G x.σ) := inside_flipCol x.σ.n G hGV hc
    have := McCost_le hA
    have := McCost_le hGV
    unfold applySCost flipCost
    omega
  · have := twistBCost_le hGV (endCell_isCell h1 hc)
    have : 1 ≤ (V.card + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
    omega

lemma pedgeCost_le (hGV : Inside V G) {x y : PNode} (hx : x ∈ pnodes V G s t)
    (hy : y ∈ pnodes V G s t) : pedgeCost V G x y ≤ 310 * (V.card + 1) ^ 2 := by
  obtain ⟨hx1, hxn, hxc⟩ := pnode_len hx
  obtain ⟨_, hyn, _⟩ := pnode_len hy
  have := cr2BCost_le hGV hx1 hxn hxc hyn
  unfold pedgeCost chainOKBCost
  nlinarith

lemma psrcCost_le (hGV : Inside V G) (x : PNode) : psrcCost V G x ≤ 165 * (V.card + 1) ^ 2 := by
  have h1 := allStripsCost_le V G
  have h2 := connBCost_le hGV (back1 x.σ.c x.σ.s)
  have hN1 : 1 ≤ (V.card + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  unfold psrcCost validBCost
  nlinarith

end bounds

/-! ## The search, one round, and a run -/

def candRCost (V : Finset Pt) (G : Finset Edge) : ℕ :=
  candCost V G + ∑ σ ∈ cand V G, (20 * σ.n + 2)

def pnodesCost (V : Finset Pt) (G : Finset Edge) (s t : Pt) : ℕ :=
  candRCost V G + 3 * (candR V G s t).card ^ 2 + 3 * (candR V G s t).card + 10

-- Reading the strips off the found path: one step per node.
--
def decodePFCost (V : Finset Pt) (G : Finset Edge) (s t : Pt) : ℕ :=
  match findChainPF V G s t with
  | some L => L.length + 2
  | none => 1

def findChainPFCost (V : Finset Pt) (G : Finset Edge) (s t : Pt) : ℕ :=
  pnodesCost V G s t +
    MP.minPathCostT (pnodes V G s t) pmid (ptgt V G s t) (pedge V G) pw (ptgtCost V G)
      (pedgeCost V G) (psrcCost V G) + decodePFCost V G s t

-- Applying the first strip of the found chain (with its membership check).
--
def applyFirstCost (V : Finset Pt) (G : Finset Edge) (s t : Pt) : ℕ :=
  match findChainPF V G s t with
  | some (σ :: _) => allStripsCost V G + applySCost σ + 2
  | _ => 2

def chainBranchCost (V : Finset Pt) (G : Finset Edge) (s t : Pt) : ℕ :=
  findChainPFCost V G s t + applyFirstCost V G s t

def stepPFCost (V : Finset Pt) (G : Finset Edge) (s t : Pt) : ℕ :=
  findT3RCost V G +
    match findT3R V G s t with
    | some _ => flipCost
    | none =>
      cncompCost V G + 2 +
        if cncomp V G == 2 then
          findT3Cost V G +
            match findT3 V G with
            | some _ => flipCost
            | none => chainBranchCost V G s t
        else chainBranchCost V G s t

def runPFCost (V : Finset Pt) (s t : Pt) : ℕ → Finset Edge → ℕ
  | 0, G => cncompCost V G + 2
  | k + 1, G =>
    cncompCost V G + 2 +
      if cncomp V G == 1 then 0
      else stepPFCost V G s t +
        match stepPF V G s t with
        | some G' => runPFCost V s t k G'
        | none => 0

section bounds2

variable {V : Finset Pt} {G : Finset Edge} {s t : Pt}

lemma CandB_le (V : Finset Pt) : CandB V ≤ 4 * (V.card + 1) ^ 2 := by
  unfold CandB; nlinarith

lemma card_cand_le' (G : Finset Edge) : (cand V G).card ≤ 4 * (V.card + 1) ^ 2 := by
  have := card_cand_le (V := V) G; have := CandB_le V; unfold CandB at *; omega

lemma Wb_le (V : Finset Pt) : Wb V ≤ 24 * (V.card + 1) ^ 5 := by
  have hC := CandB_le V
  have hN : V.card ≤ V.card + 1 := by omega
  have h2 : CandB V * CandB V ≤ 16 * (V.card + 1) ^ 4 := by
    have := Nat.mul_le_mul hC hC; nlinarith
  have h1 : 2 * CandB V ≤ 8 * (V.card + 1) ^ 4 := by
    have : (V.card + 1) ^ 2 ≤ (V.card + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  unfold Wb
  calc (2 * CandB V + CandB V * CandB V) * V.card ≤ (24 * (V.card + 1) ^ 4) * (V.card + 1) :=
        Nat.mul_le_mul (by omega) hN
    _ = 24 * (V.card + 1) ^ 5 := by ring

lemma candRCost_le (G : Finset Edge) : candRCost V G ≤ 400 * (V.card + 1) ^ 3 := by
  have h1 : candCost V G ≤ 300 * (V.card + 1) ^ 3 := by
    have := candNCost_le (V := V) G; unfold candNCost at this; omega
  have h2 : ∑ σ ∈ cand V G, (20 * σ.n + 2) ≤ (cand V G).card * (20 * V.card + 2) := by
    have := Finset.sum_le_card_nsmul (cand V G) (fun σ => 20 * σ.n + 2) (20 * V.card + 2)
      (fun σ hσ => by
        have := len_le_card (cells_of_cand hσ).2; omega)
    simpa using this
  have h3 := card_cand_le' (V := V) G
  have h4 : (cand V G).card * (20 * V.card + 2) ≤ 4 * (V.card + 1) ^ 2 * (20 * (V.card + 1)) :=
    Nat.mul_le_mul h3 (by omega)
  unfold candRCost
  nlinarith

lemma card_candR_le (G : Finset Edge) : (candR V G s t).card ≤ 4 * (V.card + 1) ^ 2 :=
  (Finset.card_filter_le _ _).trans (card_cand_le' G)

lemma pnodesCost_le (G : Finset Edge) : pnodesCost V G s t ≤ 500 * (V.card + 1) ^ 4 := by
  have h1 := candRCost_le (V := V) G
  have h2 := card_candR_le (V := V) (s := s) (t := t) G
  have hN : 1 ≤ V.card + 1 := by omega
  have h3 : (candR V G s t).card ^ 2 ≤ 16 * (V.card + 1) ^ 4 := by
    have := Nat.pow_le_pow_left h2 2; nlinarith
  have a1 : (V.card + 1) ^ 2 ≤ (V.card + 1) ^ 4 := Nat.pow_le_pow_right hN (by omega)
  have a2 : (V.card + 1) ^ 3 ≤ (V.card + 1) ^ 4 := Nat.pow_le_pow_right hN (by omega)
  have a3 : 1 ≤ (V.card + 1) ^ 4 := Nat.one_le_pow _ _ hN
  unfold pnodesCost
  omega

lemma card_pnodes_le' (G : Finset Edge) : (pnodes V G s t).card ≤ 24 * (V.card + 1) ^ 4 := by
  have h := card_pnodes_le (V := V) (s := s) (t := t) G
  have hC := CandB_le V
  have h2 : CandB V * CandB V ≤ 16 * (V.card + 1) ^ 4 := by
    have := Nat.mul_le_mul hC hC; nlinarith
  have : (V.card + 1) ^ 2 ≤ (V.card + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  omega

-- A chain found by the search has at most `Wb V` strips (each strip has a cell).
--
lemma decodePFCost_le : decodePFCost V G s t ≤ 24 * (V.card + 1) ^ 5 + 2 := by
  have hW := Wb_le V
  unfold decodePFCost
  rcases hf : findChainPF V G s t with _ | L
  · simp only; omega
  · simp only
    unfold findChainPF at hf
    rcases hm : MP.minPath (pnodes V G s t) (psrc V G) pmid (ptgt V G s t) (pedge V G) pw with _ | p
    · rw [hm] at hf; simp at hf
    rw [hm] at hf
    simp only [Option.map_some, Option.some.injEq] at hf
    subst hf
    obtain ⟨_, hpN⟩ := MP.minPath_some _ _ _ _ _ _ hm
    have hw : wmin V G s t = MP.pw pw p := by unfold wmin; rw [hm]
    have hb := wmin_le_Wb (V := V) (s := s) (t := t) G
    have hlen : p.length ≤ MP.pw pw p := by
      unfold MP.pw
      have : ∀ q : List PNode, (∀ x ∈ q, x ∈ pnodes V G s t) → q.length ≤ (q.map pw).sum := by
        intro q hq
        induction q with
        | nil => simp
        | cons x q ih =>
          simp only [List.length_cons, List.map_cons, List.sum_cons]
          have h1 : 1 ≤ pw x := (pnode_len (hq x (by simp))).1
          have := ih (fun z hz => hq z (by simp [hz]))
          omega
      exact this p hpN
    rw [List.length_map]
    omega

lemma minPathCostT_pf_le (hGV : Inside V G) :
    MP.minPathCostT (pnodes V G s t) pmid (ptgt V G s t) (pedge V G) pw (ptgtCost V G)
      (pedgeCost V G) (psrcCost V G) ≤ 6000000 * (V.card + 1) ^ 16 := by
  set N := V.card + 1 with hNdef
  have hN : 1 ≤ N := by omega
  set M := N ^ 4 with hM
  have hM1 : 1 ≤ M := Nat.one_le_pow _ _ hN
  have hN2 : N ^ 2 ≤ M := Nat.pow_le_pow_right hN (by omega)
  have hN3 : N ^ 3 ≤ M := Nat.pow_le_pow_right hN (by omega)
  have h16 : N ^ 16 = M ^ 4 := by rw [hM, ← pow_mul]
  have hn := card_pnodes_le' (V := V) (s := s) (t := t) G
  rw [← hNdef] at hn
  have hmp := MP.minPathCostT_le (pnodes V G s t) pmid (ptgt V G s t) (pedge V G) pw (ptgtCost V G)
    (pedgeCost V G) (psrcCost V G) (E := 310 * M) (S := 165 * M) (T := 1000 * M)
    (fun x hx y hy => (pedgeCost_le hGV hx hy).trans (by rw [← hNdef]; omega))
    (fun x _ => (psrcCost_le hGV x).trans (by rw [← hNdef]; omega))
    (fun x hx => (ptgtCost_le hGV hx).trans (by rw [← hNdef]; omega))
  rw [h16]
  set n := (pnodes V G s t).card
  have hnM : n ≤ 24 * M := hn
  have b1 : 310 * M + n + 5 ≤ 339 * M := by omega
  have b2 : n * (310 * M + n + 5) ≤ 24 * M * (339 * M) := Nat.mul_le_mul hnM b1
  have b3 : n * (310 * M + n + 5) + 4 + 1000 * M ≤ 9140 * (M * M) := by nlinarith
  have b4 : n * (n * (310 * M + n + 5) + 4 + 1000 * M) ≤ 24 * M * (9140 * (M * M)) :=
    Nat.mul_le_mul hnM b3
  have b5 : n * (n * (n * (310 * M + n + 5) + 4 + 1000 * M)) ≤ 24 * M * (24 * M * (9140 * (M * M))) :=
    Nat.mul_le_mul hnM b4
  have b6 : n ^ 2 ≤ 576 * (M * M) := by nlinarith
  have b7 : n * (165 * M + n + 3) ≤ 24 * M * (192 * M) := Nat.mul_le_mul hnM (by omega)
  have e4 : M ^ 4 = M * (M * (M * M)) := by ring
  rw [e4]
  have m1 : M ≤ M * M := Nat.le_mul_of_pos_left _ hM1
  have m2 : M * M ≤ M * (M * M) := Nat.le_mul_of_pos_left _ hM1
  have m3 : M * (M * M) ≤ M * (M * (M * M)) := Nat.le_mul_of_pos_left _ hM1
  nlinarith

lemma findChainPFCost_le (hGV : Inside V G) :
    findChainPFCost V G s t ≤ 6001000 * (V.card + 1) ^ 16 := by
  have hN : 1 ≤ V.card + 1 := by omega
  have h1 := pnodesCost_le (V := V) (s := s) (t := t) G
  have h2 := minPathCostT_pf_le (s := s) (t := t) hGV
  have h3 := decodePFCost_le (V := V) (G := G) (s := s) (t := t)
  have a4 : (V.card + 1) ^ 4 ≤ (V.card + 1) ^ 16 := Nat.pow_le_pow_right hN (by omega)
  have a5 : (V.card + 1) ^ 5 ≤ (V.card + 1) ^ 16 := Nat.pow_le_pow_right hN (by omega)
  have a0 : 1 ≤ (V.card + 1) ^ 16 := Nat.one_le_pow _ _ hN
  unfold findChainPFCost
  omega

lemma applyFirstCost_le (_hGV : Inside V G) : applyFirstCost V G s t ≤ 200 * (V.card + 1) ^ 2 := by
  have h1 := allStripsCost_le V G
  have hN1 : 1 ≤ (V.card + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  unfold applyFirstCost
  split
  · rename_i σ L hf
    unfold findChainPF at hf
    rcases hm : MP.minPath (pnodes V G s t) (psrc V G) pmid (ptgt V G s t) (pedge V G) pw with _ | p
    · rw [hm] at hf; simp at hf
    rw [hm] at hf
    obtain ⟨_, hpN⟩ := MP.minPath_some _ _ _ _ _ _ hm
    rcases p with _ | ⟨x, q⟩
    · simp at hf
    simp only [Option.map_some, List.map_cons, Option.some.injEq, List.cons.injEq] at hf
    obtain ⟨rfl, _⟩ := hf
    have := (pnode_len (hpN x (by simp))).2.1
    have : V.card + 1 ≤ (V.card + 1) ^ 2 := Nat.le_self_pow (by omega) _
    unfold applySCost flipCost; omega
  · omega

lemma stepPFCost_le (hGV : Inside V G) : stepPFCost V G s t ≤ 6002000 * (V.card + 1) ^ 16 := by
  have hN : 1 ≤ V.card + 1 := by omega
  have h1 := findT3RCost_le hGV
  have h2 := cncompCost_le hGV
  have h3 := findT3Cost_le hGV
  have h4 := findChainPFCost_le (s := s) (t := t) hGV
  have h5 := applyFirstCost_le (s := s) (t := t) hGV
  have a2 : (V.card + 1) ^ 2 ≤ (V.card + 1) ^ 16 := Nat.pow_le_pow_right hN (by omega)
  have a3 : (V.card + 1) ^ 3 ≤ (V.card + 1) ^ 16 := Nat.pow_le_pow_right hN (by omega)
  have a0 : 1 ≤ (V.card + 1) ^ 16 := Nat.one_le_pow _ _ hN
  have hc : chainBranchCost V G s t ≤ 6001200 * (V.card + 1) ^ 16 := by
    unfold chainBranchCost; omega
  have key : stepPFCost V G s t ≤ findT3RCost V G +
      (cncompCost V G + 2 + (findT3Cost V G + flipCost + chainBranchCost V G s t)) := by
    unfold stepPFCost
    rcases findT3R V G s t with _ | p
    · simp only
      split
      · rcases findT3 V G with _ | q
        · simp only; omega
        · simp only; omega
      · omega
    · simp only; unfold flipCost; omega
  unfold flipCost at key
  omega

theorem runPFCost_le {d : Pt → ℕ} (hd : ∀ z, z ≠ s → z ≠ t → d z = 2) (hds : d s = 1)
    (hsV : s ∈ V) : ∀ (k : ℕ) (G : Finset Edge), IsFactor V d G →
    runPFCost V s t k G ≤ (k + 1) * (6003000 * (V.card + 1) ^ 16) := by
  have hN : 1 ≤ V.card + 1 := by omega
  have a3 : (V.card + 1) ^ 3 ≤ (V.card + 1) ^ 16 := Nat.pow_le_pow_right hN (by omega)
  have a0 : 1 ≤ (V.card + 1) ^ 16 := Nat.one_le_pow _ _ hN
  intro k
  induction k with
  | zero =>
    intro G hG
    have := cncompCost_le (Inside.of_factor hG)
    simp only [runPFCost]
    omega
  | succ k ih =>
    intro G hG
    have hc := cncompCost_le (Inside.of_factor hG)
    have hr := stepPFCost_le (s := s) (t := t) (Inside.of_factor hG)
    have e : (k + 1 + 1) * (6003000 * (V.card + 1) ^ 16) =
        (k + 1) * (6003000 * (V.card + 1) ^ 16) + 6003000 * (V.card + 1) ^ 16 := Nat.succ_mul _ _
    have hk0 : 0 ≤ (k + 1) * (6003000 * (V.card + 1) ^ 16) := Nat.zero_le _
    have hX : 6003000 * (V.card + 1) ^ 16 ≤ (k + 1) * (6003000 * (V.card + 1) ^ 16) :=
      Nat.le_mul_of_pos_left _ (by omega)
    rw [e]
    simp only [runPFCost]
    split
    · omega
    · rcases hs : stepPF V G s t with _ | G'
      · simp only; omega
      · simp only
        have := ih G' (stepPF_factor hG hd hds hsV hs)
        omega

-- **Running time of a run of `fuelPF V` rounds**: at most `4·10⁸ (|V| + 1)²²` elementary steps.
--
theorem runPFCost_fuel_le {d : Pt → ℕ} (hd : ∀ z, z ≠ s → z ≠ t → d z = 2) (hds : d s = 1)
    (hsV : s ∈ V) (G : Finset Edge) (hG : IsFactor V d G) :
    runPFCost V s t (fuelPF V) G ≤ 400000000 * (V.card + 1) ^ 22 := by
  have hN : 1 ≤ V.card + 1 := by omega
  have h := runPFCost_le hd hds hsV (fuelPF V) G hG
  have hW := Wb_le V
  have hf : fuelPF V + 1 ≤ 60 * (V.card + 1) ^ 6 := by
    unfold fuelPF
    have e : (V.card + 1) * (V.card + 1) ^ 5 = (V.card + 1) ^ 6 := by ring
    have : (2 * V.card + 2) * (Wb V + 1) ≤ (2 * (V.card + 1)) * (24 * (V.card + 1) ^ 5 + 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    have a5 : 1 ≤ (V.card + 1) ^ 5 := Nat.one_le_pow _ _ hN
    have a6 : (V.card + 1) ≤ (V.card + 1) ^ 6 := Nat.le_self_pow (by omega) _
    nlinarith
  have e22 : (V.card + 1) ^ 6 * (V.card + 1) ^ 16 = (V.card + 1) ^ 22 := by rw [← pow_add]
  calc runPFCost V s t (fuelPF V) G ≤ (fuelPF V + 1) * (6003000 * (V.card + 1) ^ 16) := h
    _ ≤ (60 * (V.card + 1) ^ 6) * (6003000 * (V.card + 1) ^ 16) := Nat.mul_le_mul_right _ hf
    _ = 360180000 * ((V.card + 1) ^ 6 * (V.card + 1) ^ 16) := by ring
    _ ≤ 400000000 * (V.card + 1) ^ 22 := by rw [e22]; omega

end bounds2

end HP

end ULHC
