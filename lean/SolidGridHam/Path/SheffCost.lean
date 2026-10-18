/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import SolidGridHam.Path.SheffComp
import SolidGridHam.Cycle.CostAlg
import SolidGridHam.Cycle.CostMinPath
import SolidGridHam.Path.Prelim.ZeroPF
import SolidGridHam.Path.Prelim.CompCleanTg
import SolidGridHam.Cycle.Phase2
import SolidGridHam.Path.Prelim.TheoremAPF
import SolidGridHam.Cycle.Comp
import SolidGridHam.Cycle.Enum
import SolidGridHam.Path.Prelim.StripCountPF
import SolidGridHam.Path.FindFactorCost

/-!
# Running time of the decided Sheffield loop, part 1: the phase

Costs in the style of `CostPF` (each test charged by its evaluation, with the primitives of
`CostConn`: `connBCost`, `cncompCost`; `flipCost` per cell flip; one step per membership test).
Loops are charged for every step (an upper bound when they exit early). With `N = |W| + 1`:

* `cutBCost ≤ 100 N²`, `findMergeCost ≤ 125 N³`;
* `scanCost ≤ 120 N³`, `findMoveCost ≤ 1020 N⁴`;
* `phaseCost` with fuel `n` from `BS = []`: `≤ (n + 1) · 1300 N⁴`.

The bounds use the phase invariant `PhI`: the state is inside `W`, every bridge has `r ≤ |V| + 1`
(the scan's fuel) and its end square is a cell of `V`.
-/

namespace SolidGridHam

namespace HP

open Finset Classical

lemma lsum_le {α : Type*} (l : List α) (f : α → ℕ) (B : ℕ) (h : ∀ x ∈ l, f x ≤ B) :
    (l.map f).sum ≤ l.length * B := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have h1 := h a List.mem_cons_self
    have h2 := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    rw [Nat.succ_mul]; omega

/-! ## Bridge lengths -/

lemma scanAux_row_lt {V W : Finset Pt} {H : Finset Edge} {q : Pt} {a : Side} {o : Bool} :
    ∀ fuel j r, scanAux V W H q a o fuel j = some (.row r) → r < j + fuel := by
  intro fuel
  induction fuel with
  | zero => intro j r h; simp [scanAux] at h
  | succ fuel ih =>
    intro j r h
    simp only [scanAux] at h
    split_ifs at h with h1 h2
    · simp only [Option.some.injEq, RunEnd.row.injEq] at h; omega
    · simp at h
    · have := ih (j + 1) r h; omega

lemma findMove_r {V W : Finset Pt} {H : Finset Edge} {BS : List Bridge} {b : Bridge}
    (h : findMove V W H BS = some b) : b.r ≤ V.card + 1 := by
  obtain ⟨x, _, hb⟩ := List.exists_of_findSome?_eq_some h
  unfold moveOf at hb
  split_ifs at hb
  rcases hs : scan V W H x.1 x.2 with _ | e
  · rw [hs] at hb; simp at hb
  · rcases e with r | k
    · rw [hs] at hb
      simp only [Option.some.injEq] at hb
      subst hb
      have := scanAux_row_lt (V.card + 1) 1 r hs
      simp only; omega
    · rw [hs] at hb; simp at hb

/-! ## The phase invariant -/

def PhI (V W : Finset Pt) (H : Finset Edge) (BS : List Bridge) : Prop :=
  Inside W H ∧ ∀ b ∈ BS, b.r ≤ V.card + 1 ∧ IsCell V b.E

lemma phI_step {V W : Finset Pt} (hVW : V ⊆ W) {H : Finset Edge} {BS : List Bridge}
    (hI : PhI V W H BS) {b : Bridge} (hb : findMove V W H BS = some b) :
    PhI V W (flip H b.E) (b :: BS) := by
  have mf := findMove_some hVW hI.1 hb
  have hE : IsCell V b.E := mf.2.2.2.2.2.1 _ (by have := mf.2.2.2.2.1; omega)
  refine ⟨inside_flip hI.1 (isCell_mono hE hVW), fun b' hb' => ?_⟩
  rcases List.mem_cons.1 hb' with rfl | hb'
  · exact ⟨findMove_r hb, hE⟩
  · exact hI.2 b' hb'

-- The phase output: invariant, list length, and the bridge of a row outcome.
--
lemma phase_inv {V W : Finset Pt} (hVW : V ⊆ W) :
    ∀ n (H : Finset Edge) (BS : List Bridge), PhI V W H BS →
      PhI V W (phase V W n H BS).1 (phase V W n H BS).2.1 ∧
        (phase V W n H BS).2.1.length ≤ BS.length + n ∧
        (∀ g, ((phase V W n H BS).2.2 = .odd g ∨ (phase V W n H BS).2.2 = .twist g) →
          g.r ≤ V.card + 1 ∧ ∀ j < g.r, IsCell V (g.cell j)) := by
  intro n
  induction n with
  | zero => intro H BS hI; simp [phase, hI]
  | succ n ih =>
    intro H BS hI
    simp only [phase]
    rcases hm : findMerge V W H BS with _ | c
    · simp only
      rcases hmv : findMove V W H BS with _ | b
      · simp [hI]
      · simp only
        have mf := findMove_some hVW hI.1 hmv
        have hrb := findMove_r hmv
        split_ifs with h1 h2
        · refine ⟨hI, by simp, fun g hg => ?_⟩
          simp only [POut.odd.injEq, or_false] at hg
          subst hg; exact ⟨hrb, mf.2.2.2.2.2.1⟩
        · obtain ⟨a1, a2, a3⟩ := ih _ _ (phI_step hVW hI hmv)
          exact ⟨a1, by simp at a2; omega, a3⟩
        · refine ⟨hI, by simp, fun g hg => ?_⟩
          simp only [POut.twist.injEq, false_or] at hg
          subst hg; exact ⟨hrb, mf.2.2.2.2.2.1⟩
    · simp [hI]

/-! ## Costs of the phase tests -/

def isCellCost : ℕ := 4
def altCost : ℕ := 4
def outArcCost : ℕ := 2

def cutBCost (W : Finset Pt) (H : Finset Edge) (c : Pt) : ℕ := 3 * connBCost W H c + 3

def pairSqBCost (BS : List Bridge) : ℕ := 2 * BS.length + 1

def findMergeCost (V W : Finset Pt) (H : Finset Edge) (BS : List Bridge) : ℕ :=
  cellListCost V + ((cellList V).map fun c => altCost + cutBCost W H c + pairSqBCost BS + 1).sum + 1

def critBCost (W : Finset Pt) (H : Finset Edge) (q : Pt) (a : Side) : ℕ :=
  connBCost W H (back1 q a) + connBCost W H (front1 q a) + connBCost W H (back1 q a) + 5

def bridgeSqBCost (BS : List Bridge) : ℕ := (BS.map fun b => b.r + 1).sum + 1

def scanCost (V W : Finset Pt) (H : Finset Edge) (q : Pt) (a : Side) : ℕ :=
  ((List.range (V.card + 1)).map fun j =>
    2 * outArcCost + isCellCost + cutBCost W H (cellJ q a (j + 1)) + 1).sum + outArcCost + 1

def moveOfCost (V W : Finset Pt) (H : Finset Edge) (BS : List Bridge) (x : Pt × Side) : ℕ :=
  critBCost W H x.1 x.2 + bridgeSqBCost BS + scanCost V W H x.1 x.2 + 2

def findMoveCost (V W : Finset Pt) (H : Finset Edge) (BS : List Bridge) : ℕ :=
  (((cellList V).flatMap fun q => sidesL.map fun a => (q, a)).map fun x =>
    moveOfCost V W H BS x + 1).sum + cellListCost V + 5 * (cellList V).length + 1

def flipSplitsCost (W : Finset Pt) (H : Finset Edge) (b : Bridge) : ℕ :=
  flipCost + connBCost W (flip H b.E) (back1 b.E b.a) + 1

def phaseCost (V W : Finset Pt) : ℕ → Finset Edge → List Bridge → ℕ
  | 0, _, _ => 1
  | n + 1, H, BS =>
    findMergeCost V W H BS + 1 +
      match findMerge V W H BS with
      | some _ => 0
      | none =>
        findMoveCost V W H BS + 1 +
          match findMove V W H BS with
          | none => 0
          | some b =>
            if b.r % 2 = 1 then 1
            else flipSplitsCost W H b + 1 +
              (if flipSplits W H b then flipCost + phaseCost V W n (flip H b.E) (b :: BS) else 0)

/-! ## Bounds -/

section bounds

variable {V W : Finset Pt} {H : Finset Edge} {BS : List Bridge}

lemma cutBCost_le (hHW : Inside W H) (c : Pt) : cutBCost W H c ≤ 100 * (W.card + 1) ^ 2 := by
  unfold cutBCost
  have := connBCost_le hHW c
  have : 1 ≤ (W.card + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  omega

lemma cellListCost_le' (hVW : V ⊆ W) : cellListCost V ≤ 11 * (W.card + 1) ^ 2 := by
  unfold cellListCost
  have hV := Finset.card_le_card hVW
  have : V.card ^ 2 ≤ (W.card + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have : W.card + 1 ≤ (W.card + 1) ^ 2 := Nat.le_self_pow (by omega) _
  omega

lemma findMergeCost_le (hVW : V ⊆ W) (hHW : Inside W H) (hBS : BS.length ≤ W.card + 1) :
    findMergeCost V W H BS ≤ 125 * (W.card + 1) ^ 3 := by
  have hcl := cellListCost_le' hVW
  have : (W.card + 1) ^ 2 ≤ (W.card + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  unfold findMergeCost
  have hl := length_cellList V
  have hV := Finset.card_le_card hVW
  have hf : W.card + 1 ≤ (W.card + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have hs := lsum_le (cellList V) (fun c => altCost + cutBCost W H c + pairSqBCost BS + 1)
    (110 * (W.card + 1) ^ 2) (fun c _ => by
      have := cutBCost_le hHW c
      unfold altCost pairSqBCost
      omega)
  have e : (W.card + 1) * (W.card + 1) ^ 2 = (W.card + 1) ^ 3 := by ring
  have h1 : (cellList V).length * (110 * (W.card + 1) ^ 2) ≤ W.card * (110 * (W.card + 1) ^ 2) :=
    Nat.mul_le_mul_right _ (by omega)
  nlinarith

lemma critBCost_le (hHW : Inside W H) (q : Pt) (a : Side) :
    critBCost W H q a ≤ 100 * (W.card + 1) ^ 2 := by
  unfold critBCost
  have := connBCost_le hHW (back1 q a)
  have := connBCost_le hHW (front1 q a)
  have : 1 ≤ (W.card + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  omega

lemma bridgeSqBCost_le (hVW : V ⊆ W) (hBS : BS.length ≤ W.card + 1)
    (hr : ∀ b ∈ BS, b.r ≤ V.card + 1) : bridgeSqBCost BS ≤ 3 * (W.card + 1) ^ 2 := by
  unfold bridgeSqBCost
  have hV := Finset.card_le_card hVW
  have hs := lsum_le BS (fun b => b.r + 1) (W.card + 2) (fun b hb => by have := hr b hb; omega)
  have h1 : BS.length * (W.card + 2) ≤ (W.card + 1) * (W.card + 2) := Nat.mul_le_mul_right _ hBS
  nlinarith

lemma scanCost_le (hVW : V ⊆ W) (hHW : Inside W H) (q : Pt) (a : Side) :
    scanCost V W H q a ≤ 120 * (W.card + 1) ^ 3 := by
  unfold scanCost
  have hV := Finset.card_le_card hVW
  have hs := lsum_le (List.range (V.card + 1))
    (fun j => 2 * outArcCost + isCellCost + cutBCost W H (cellJ q a (j + 1)) + 1)
    (109 * (W.card + 1) ^ 2) (fun j _ => by
      have := cutBCost_le hHW (cellJ q a (j + 1))
      unfold outArcCost isCellCost
      have : 1 ≤ (W.card + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
      omega)
  rw [List.length_range] at hs
  have h1 : (V.card + 1) * (109 * (W.card + 1) ^ 2) ≤ (W.card + 1) * (109 * (W.card + 1) ^ 2) :=
    Nat.mul_le_mul_right _ (by omega)
  have e : (W.card + 1) * (W.card + 1) ^ 2 = (W.card + 1) ^ 3 := by ring
  have : 1 ≤ (W.card + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  have ho : outArcCost = 2 := rfl
  nlinarith

lemma moveOfCost_le (hVW : V ⊆ W) (hHW : Inside W H) (hBS : BS.length ≤ W.card + 1)
    (hr : ∀ b ∈ BS, b.r ≤ V.card + 1) (x : Pt × Side) :
    moveOfCost V W H BS x ≤ 230 * (W.card + 1) ^ 3 := by
  unfold moveOfCost
  have := critBCost_le hHW x.1 x.2
  have := bridgeSqBCost_le hVW hBS hr
  have := scanCost_le hVW hHW x.1 x.2
  have : (W.card + 1) ^ 2 ≤ (W.card + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have : 1 ≤ (W.card + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  omega

lemma findMoveCost_le (hVW : V ⊆ W) (hHW : Inside W H) (hBS : BS.length ≤ W.card + 1)
    (hr : ∀ b ∈ BS, b.r ≤ V.card + 1) : findMoveCost V W H BS ≤ 1020 * (W.card + 1) ^ 4 := by
  have hcl := cellListCost_le' hVW
  have : (W.card + 1) ^ 2 ≤ (W.card + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  unfold findMoveCost
  have hl := length_cellList V
  have hV := Finset.card_le_card hVW
  have hps : ((cellList V).flatMap fun d => sidesL.map fun tf => (d, tf)).length =
      4 * (cellList V).length := by
    simp [List.length_flatMap, sidesL]; ring
  have hs := lsum_le ((cellList V).flatMap fun q => sidesL.map fun a => (q, a))
    (fun x => moveOfCost V W H BS x + 1) (231 * (W.card + 1) ^ 3) (fun x _ => by
      have := moveOfCost_le hVW hHW hBS hr x
      have : 1 ≤ (W.card + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
      omega)
  rw [hps] at hs
  have h1 : 4 * (cellList V).length * (231 * (W.card + 1) ^ 3) ≤
      4 * (W.card + 1) * (231 * (W.card + 1) ^ 3) := Nat.mul_le_mul_right _ (by omega)
  have e : (W.card + 1) * (W.card + 1) ^ 3 = (W.card + 1) ^ 4 := by ring
  have : W.card + 1 ≤ (W.card + 1) ^ 4 := Nat.le_self_pow (by omega) _
  nlinarith

lemma flipSplitsCost_le (hVW : V ⊆ W) (hHW : Inside W H) {b : Bridge} (hE : IsCell V b.E) :
    flipSplitsCost W H b ≤ 40 * (W.card + 1) ^ 2 := by
  unfold flipSplitsCost
  have := connBCost_le (inside_flip hHW (isCell_mono hE hVW)) (back1 b.E b.a)
  have : 1 ≤ (W.card + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  unfold flipCost; omega

-- **The phase.** With `n` steps of fuel left and `|BS| + n ≤ |W| + 1`.
--
theorem phaseCost_le (hVW : V ⊆ W) :
    ∀ n (H : Finset Edge) (BS : List Bridge), PhI V W H BS → BS.length + n ≤ W.card + 1 →
      phaseCost V W n H BS ≤ (n + 1) * (1300 * (W.card + 1) ^ 4) := by
  intro n
  induction n with
  | zero =>
    intro H BS _ _
    simp only [phaseCost]
    have : 1 ≤ (W.card + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
    omega
  | succ n ih =>
    intro H BS hI hlen
    have hfc : flipCost = 8 := rfl
    have hBS : BS.length ≤ W.card + 1 := by omega
    have hr : ∀ b ∈ BS, b.r ≤ V.card + 1 := fun b hb => (hI.2 b hb).1
    have c1 := findMergeCost_le hVW hI.1 hBS
    have c2 := findMoveCost_le hVW hI.1 hBS hr
    have a3 : (W.card + 1) ^ 3 ≤ (W.card + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
    have a2 : (W.card + 1) ^ 2 ≤ (W.card + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
    have a0 : 1 ≤ (W.card + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
    have e : (n + 1 + 1) * (1300 * (W.card + 1) ^ 4) =
        (n + 1) * (1300 * (W.card + 1) ^ 4) + 1300 * (W.card + 1) ^ 4 := Nat.succ_mul _ _
    have hpos : 0 ≤ (n + 1) * (1300 * (W.card + 1) ^ 4) := Nat.zero_le _
    have hX : 1300 * (W.card + 1) ^ 4 ≤ (n + 1) * (1300 * (W.card + 1) ^ 4) :=
      Nat.le_mul_of_pos_left _ (by omega)
    rw [e]
    simp only [phaseCost]
    rcases hm : findMerge V W H BS with _ | c
    · simp only
      rcases hmv : findMove V W H BS with _ | b
      · simp only; omega
      · simp only
        have mf := findMove_some hVW hI.1 hmv
        have hE : IsCell V b.E := mf.2.2.2.2.2.1 _ (by have := mf.2.2.2.2.1; omega)
        have c3 := flipSplitsCost_le hVW hI.1 hE
        split_ifs with h1 h2
        · omega
        · have := ih _ _ (phI_step hVW hI hmv) (by simp; omega)
          omega
        · omega
    · simp only; omega

end bounds

/-! ## Part 2: the reduction and the loop -/

def planABCost (W : Finset Pt) : Finset Edge → List Bridge → Pt × Pt → ℕ
  | _, [], _ => 1
  | H, b :: BS, uv =>
    flipCost + connBCost W (flip H b.E) uv.1 + 2 +
      planABCost W (flip H b.E) BS (if connB W (flip H b.E) uv.1 uv.2 then rowStartPair b else uv)

def lowAtBCost (W : Finset Pt) (H : Finset Edge) (BS : List Bridge) (uv : Pt × Pt) : ℕ :=
  planABCost W H BS uv + BS.length + 1

def goodBCost (W : Finset Pt) (H : Finset Edge) (BS : List Bridge) (X : Pt) : ℕ :=
  altCost + cutBCost W H X + pairSqBCost BS +
    ((List.finRange BS.length).map fun _ =>
      lowAtBCost W H BS (mergePair H X) + BS.length + 8).sum + BS.length + 5

def applyAllCost (ops : List Join) : ℕ := (ops.map fun o => flipCost * o.n + 1).sum + 1

def planBCost (W : Finset Pt) (H : Finset Edge) (BS : List Bridge) (uv : Pt × Pt) : ℕ :=
  planABCost W H BS uv + 2 * BS.length + 1

def reduceOutCCost (V W : Finset Pt) (H : Finset Edge) (BS : List Bridge) : POut → ℕ
  | .merge c =>
    cellListCost V + ((cellList V).map fun x => goodBCost W H BS x + 1).sum + 1 +
      (flipCost + 4 + planBCost W H BS (mergePair H (((cellList V).find? (goodB W H BS)).getD c)) +
        applyAllCost (planB W H BS (mergePair H (((cellList V).find? (goodB W H BS)).getD c))))
  | .odd b => flipCost * b.r + planBCost W H BS (rowStartPair b) +
      applyAllCost (planB W H BS (rowStartPair b)) + 2
  | .twist b => flipCost * b.r + planBCost W H BS (rowStartPair b) +
      applyAllCost (planB W H BS (rowStartPair b)) + 2
  | _ => 1

def runSCCost (V : Finset Pt) (p : Pt) : ℕ → Finset Edge → ℕ
  | 0, G => cncompCost (insert p V) G + 2
  | n + 1, G =>
    cncompCost (insert p V) G + 2 +
      if cncomp (insert p V) G == 1 then 0
      else
        (insert p V).card + 3 + phaseCost V (insert p V) ((insert p V).card + 1) G [] +
          match phase V (insert p V) ((insert p V).card + 1) G [] with
          | (_, _, .stuck) => 0
          | (_, _, .fuel) => 0
          | (H, BS, out) => reduceOutCCost V (insert p V) H BS out +
              runSCCost V p n (reduceOutC V (insert p V) H BS out)

def hpSheffCCost (V : Finset Pt) (s t p : Pt) (e0 : Edge) : ℕ :=
  DFC.findFactorCost V (dST s t) + 1 +
    match findFactor V (dST s t) with
    | none => 0
    | some R => runSCCost V p (V.card + 2) (insert e0 R)

section bounds2

variable {V W : Finset Pt} {H : Finset Edge} {BS : List Bridge}

lemma planABCost_le {W : Finset Pt} : ∀ (BS : List Bridge) (H : Finset Edge) (uv : Pt × Pt),
    Inside W H → (∀ b ∈ BS, IsCell W b.E) →
      planABCost W H BS uv ≤ (BS.length + 1) * (40 * (W.card + 1) ^ 2)
  | [], _, _, _, _ => by
    simp only [planABCost, List.length_nil, zero_add, one_mul]
    have : 1 ≤ (W.card + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega
  | b :: BS, H, uv, hH, hb => by
    have hH' := inside_flip hH (hb b List.mem_cons_self)
    have ih := planABCost_le BS (flip H b.E)
      (if connB W (flip H b.E) uv.1 uv.2 then rowStartPair b else uv) hH'
      (fun b' hb' => hb b' (List.mem_cons_of_mem _ hb'))
    have := connBCost_le hH' uv.1
    simp only [planABCost, List.length_cons]
    rw [show BS.length + 1 + 1 = (BS.length + 1) + 1 from rfl, Nat.succ_mul]
    have : 1 ≤ (W.card + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    unfold flipCost; omega

lemma planAB_length {W : Finset Pt} : ∀ (BS : List Bridge) (H : Finset Edge) (uv : Pt × Pt),
    (planAB W H BS uv).length = BS.length
  | [], _, _ => rfl
  | b :: BS, H, uv => by
    simp only [planAB]
    split_ifs <;> simp [planAB_length BS]

lemma mem_planB {W : Finset Pt} {H : Finset Edge} {BS : List Bridge} {uv : Pt × Pt} {o : Join}
    (ho : o ∈ planB W H BS uv) : ∃ b ∈ BS, o = lowJ b ∨ o = undoJ b := by
  unfold planB at ho
  generalize planAB W H BS uv = L at ho
  induction BS generalizing L with
  | nil => simp at ho
  | cons b BS ih =>
    cases L with
    | nil => simp at ho
    | cons e L =>
      simp only [List.zipWith_cons_cons, List.mem_cons] at ho
      rcases ho with h | h
      · refine ⟨b, List.mem_cons_self, ?_⟩
        split_ifs at h
        · exact Or.inl h
        · exact Or.inr h
      · obtain ⟨b', hb', h'⟩ := ih L h
        exact ⟨b', List.mem_cons_of_mem _ hb', h'⟩

lemma applyAllCost_planB_le (hVW : V ⊆ W) (hBS : BS.length ≤ W.card + 1)
    (hr : ∀ b ∈ BS, b.r ≤ V.card + 1) (uv : Pt × Pt) :
    applyAllCost (planB W H BS uv) ≤ 10 * (W.card + 1) ^ 2 := by
  unfold applyAllCost
  have hV := Finset.card_le_card hVW
  have hlen : (planB W H BS uv).length ≤ W.card + 1 := by
    unfold planB; rw [List.length_zipWith, planAB_length]; omega
  have hs := lsum_le (planB W H BS uv) (fun o => flipCost * o.n + 1) (8 * (W.card + 1) + 1)
    (fun o ho => by
      obtain ⟨b, hb, h⟩ := mem_planB ho
      have := hr b hb
      unfold flipCost
      rcases h with rfl | rfl
      · simp only [lowJ]; omega
      · simp only [undoJ]; omega)
  have h1 : (planB W H BS uv).length * (8 * (W.card + 1) + 1) ≤
      (W.card + 1) * (8 * (W.card + 1) + 1) := Nat.mul_le_mul_right _ hlen
  nlinarith

lemma planBCost_le (hHW : Inside W H) (hBS : BS.length ≤ W.card + 1)
    (hE : ∀ b ∈ BS, IsCell W b.E) (uv : Pt × Pt) :
    planBCost W H BS uv ≤ 100 * (W.card + 1) ^ 3 := by
  unfold planBCost
  have := planABCost_le BS H uv hHW hE
  have h1 : (BS.length + 1) * (40 * (W.card + 1) ^ 2) ≤ (W.card + 2) * (40 * (W.card + 1) ^ 2) :=
    Nat.mul_le_mul_right _ (by omega)
  have e : (W.card + 1) * (W.card + 1) ^ 2 = (W.card + 1) ^ 3 := by ring
  have : 1 ≤ (W.card + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  nlinarith

lemma goodBCost_le (hHW : Inside W H) (hBS : BS.length ≤ W.card + 1)
    (hE : ∀ b ∈ BS, IsCell W b.E) (X : Pt) : goodBCost W H BS X ≤ 400 * (W.card + 1) ^ 4 := by
  unfold goodBCost lowAtBCost
  have hc := cutBCost_le hHW X
  have hp := planABCost_le BS H (mergePair H X) hHW hE
  have hs := lsum_le (List.finRange BS.length)
    (fun _ => planABCost W H BS (mergePair H X) + BS.length + 1 + BS.length + 8)
    ((W.card + 2) * (40 * (W.card + 1) ^ 2) + 2 * W.card + 12) (fun _ _ => by
      have : (BS.length + 1) * (40 * (W.card + 1) ^ 2) ≤ (W.card + 2) * (40 * (W.card + 1) ^ 2) :=
        Nat.mul_le_mul_right _ (by omega)
      omega)
  rw [List.length_finRange] at hs
  have h1 : BS.length * ((W.card + 2) * (40 * (W.card + 1) ^ 2) + 2 * W.card + 12) ≤
      (W.card + 1) * ((W.card + 2) * (40 * (W.card + 1) ^ 2) + 2 * W.card + 12) :=
    Nat.mul_le_mul_right _ hBS
  have e4 : (W.card + 1) * ((W.card + 1) * (W.card + 1) ^ 2) = (W.card + 1) ^ 4 := by ring
  have e3 : (W.card + 1) * (W.card + 1) ^ 2 = (W.card + 1) ^ 3 := by ring
  have a2 : 1 ≤ (W.card + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have a3 : (W.card + 1) ^ 2 ≤ (W.card + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have a4 : (W.card + 1) ^ 3 ≤ (W.card + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  unfold altCost pairSqBCost
  nlinarith

lemma reduceOutCCost_le (hVW : V ⊆ W) (hI : PhI V W H BS) (hBS : BS.length ≤ W.card + 1)
    {out : POut} (hg : ∀ g, (out = .odd g ∨ out = .twist g) → g.r ≤ V.card + 1) :
    reduceOutCCost V W H BS out ≤ 600 * (W.card + 1) ^ 5 := by
  have hV := Finset.card_le_card hVW
  have hr : ∀ b ∈ BS, b.r ≤ V.card + 1 := fun b hb => (hI.2 b hb).1
  have hE : ∀ b ∈ BS, IsCell W b.E := fun b hb => isCell_mono (hI.2 b hb).2 hVW
  have a2 : 1 ≤ (W.card + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have a3 : (W.card + 1) ^ 2 ≤ (W.card + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have a4 : (W.card + 1) ^ 3 ≤ (W.card + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have a5 : (W.card + 1) ^ 4 ≤ (W.card + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
  have a1 : W.card + 1 ≤ (W.card + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have hcl := cellListCost_le' hVW
  cases out with
  | merge c =>
    simp only [reduceOutCCost]
    have hl := length_cellList V
    have hs := lsum_le (cellList V) (fun x => goodBCost W H BS x + 1) (401 * (W.card + 1) ^ 4)
      (fun x _ => by have := goodBCost_le hI.1 hBS hE x; omega)
    have h1 : (cellList V).length * (401 * (W.card + 1) ^ 4) ≤ W.card * (401 * (W.card + 1) ^ 4) :=
      Nat.mul_le_mul_right _ (by omega)
    have e5 : (W.card + 1) * (W.card + 1) ^ 4 = (W.card + 1) ^ 5 := by ring
    have := planBCost_le hI.1 hBS hE (mergePair H (((cellList V).find? (goodB W H BS)).getD c))
    have := applyAllCost_planB_le (H := H) hVW hBS hr
      (mergePair H (((cellList V).find? (goodB W H BS)).getD c))
    unfold flipCost
    nlinarith
  | odd g =>
    simp only [reduceOutCCost]
    have := hg g (Or.inl rfl)
    have := planBCost_le hI.1 hBS hE (rowStartPair g)
    have := applyAllCost_planB_le (H := H) hVW hBS hr (rowStartPair g)
    unfold flipCost
    nlinarith
  | twist g =>
    simp only [reduceOutCCost]
    have := hg g (Or.inr rfl)
    have := planBCost_le hI.1 hBS hE (rowStartPair g)
    have := applyAllCost_planB_le (H := H) hVW hBS hr (rowStartPair g)
    unfold flipCost
    nlinarith
  | stuck => simp only [reduceOutCCost]; nlinarith
  | fuel => simp only [reduceOutCCost]; nlinarith

end bounds2

end HP

end SolidGridHam
