/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import SolidGridHam.Cycle.Algorithm
public import SolidGridHam.Cycle.Counts
public import SolidGridHam.Cycle.NearCA

@[expose] public section

/-!
# Completeness of the algorithm, conditional on path existence

`PathComplete V`: every Type III-free 2-factor with at least two components has a
`CRPathCA` path. Under this hypothesis, `ulhc V = true` for every solid `V` with a
Hamiltonian cycle (`ulhc_complete`).

## Potential

* `dval V G`: the weight of the path `findPath V G` returns (`0` for none). It is at most
  `Dm V = Bd V * |V|` (`dval_le`): a minimum path is no heavier than a repetition-free
  one, which has at most `|candN V G| ≤ Bd V` nodes (`card_candN_le`), each of weight at
  most `|V|`.
* `Mz V G = ncomp V G * (2 Dm + 4) + e`, with `e = 2 dval + 2` when `G` has no Type III
  cell and `e = 1` otherwise, so `1 ≤ e ≤ 2 Dm + 2`.
* `step_decrease`: every round from a 2-factor with at least two components succeeds and
  lowers `Mz`. A Type III flip, an odd first strip, or an even first strip that splits
  off two components lowers `ncomp`. An even first strip that keeps `ncomp` either
  creates a Type III cell (`e` drops to `1`) or, by `round_ca`, leaves a path of weight
  `dval - a.n` (`e` drops).

## Cost

The number of rounds is at most `fuel V = (|V| + 1)(2 Dm V + 4) + 2`, where
`Dm V = 3 (4|V| + 4|V|²) |V|`, so `fuel V = O(|V|⁴)`. Each round costs polynomially many
basic operations: `findT3` makes `O(|V|)` Type III tests (`4` frames per cell), each with
one `connB` reachability test; `findPath` makes at most `n³ + n` link-graph edge and
source tests with `n = |candN V G| ≤ Bd V = O(|V|²)`, and the flip
itself touches at most `|V|` cells. Proved, in the cost model of `CostConn.lean`: `ulhcCost_le` (`CostAlg.lean`).
-/

namespace SolidGridHam

open Finset

def PathComplete (V : Finset Pt) : Prop :=
  ∀ G, Deg2 V G → NoTypeIII V G → 2 ≤ ncomp V G → ∃ σ L, CRPathCA V G σ L

/-! ## Bounds -/

section bounds

variable {V : Finset Pt}

lemma card_cand_le (G : Finset Edge) :
    (cand V G).card ≤ 4 * V.card + V.card * (4 * V.card) := by
  unfold cand
  refine (Finset.card_union_le _ _).trans (Nat.add_le_add (card_allStrips (V := V) (F := G)) ?_)
  refine Finset.card_biUnion_le.trans ?_
  refine (Finset.sum_le_sum (fun u _ => card_allStrips (V := V) (F := flip G u))).trans ?_
  rw [Finset.sum_const, smul_eq_mul]
  exact Nat.mul_le_mul_right _ (Finset.card_filter_le _ _)

lemma card_candN_le (G : Finset Edge) : (candN V G).card ≤ Bd V := by
  unfold candN Bd
  refine Finset.card_biUnion_le.trans ?_
  have h3 : ∀ σ ∈ cand V G,
      (({1, 2, 3} : Finset ℕ).image fun p => Node.mk σ p).card ≤ 3 := fun σ _ =>
    Finset.card_image_le.trans (by simp)
  refine (Finset.sum_le_sum h3).trans ?_
  rw [Finset.sum_const, smul_eq_mul]
  have := card_cand_le (V := V) G
  omega

-- Every link-graph node has weight at most `|V|`.
--
lemma gw_le {G : Finset Edge} {x : Node} (hx : x ∈ candN V G) : gw x ≤ V.card := by
  obtain ⟨_, hc⟩ := cells_of_cand (mem_candN.1 hx).1
  exact strip_len_le hc

lemma pw_le_len {l : List Node} {M : ℕ} (h : ∀ x ∈ l, gw x ≤ M) :
    MP.pw gw l ≤ l.length * M := by
  induction l with
  | nil => simp [MP.pw_nil]
  | cons x l ih =>
    rw [MP.pw_cons, List.length_cons, Nat.succ_mul]
    have h1 := h x (by simp)
    have h2 := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    omega

end bounds

/-! ## The potential -/

def dval (V : Finset Pt) (G : Finset Edge) : ℕ :=
  match findPath V G with
  | some (σ, L) => wt σ L
  | none => 0

open Classical in
noncomputable def Mz (V : Finset Pt) (G : Finset Edge) : ℕ :=
  ncomp V G * (2 * Dm V + 4) + (if NoTypeIII V G then 2 * dval V G + 2 else 1)

section potential

variable {V : Finset Pt}

lemma dval_eq {G : Finset Edge} {σ : StripSpec} {L : List StripSpec}
    (h : findPath V G = some (σ, L)) : dval V G = wt σ L := by
  unfold dval
  rw [h]

-- A minimum path is no heavier than a repetition-free path, which has at most
-- `|candN V G|` nodes of weight at most `|V|` each.
--
theorem dval_le {G : Finset Edge} (hGV : Inside V G) : dval V G ≤ Dm V := by
  rcases hp : findPath V G with _ | ⟨σ, L⟩
  · unfold dval
    rw [hp]
    exact Nat.zero_le _
  rw [dval_eq hp]
  obtain ⟨hP, hmin⟩ := findPath_some hGV hp
  obtain ⟨hpath, hN, _⟩ := crpath_to_path hGV hP
  generalize posList 1 (σ :: L) = q at hpath hN
  cases q with
  | nil => exact hpath.elim
  | cons x rest =>
    obtain ⟨hsrc, htail⟩ := MP.isPath_cons.1 hpath
    obtain ⟨L1, ht1, hnd, hsub⟩ := MP.shortcut htail
    have hpath1 : MP.IsPath (gsrc V G) gmid gtgt (gedge V G) (x :: L1) :=
      MP.isPath_cons.2 ⟨hsrc, ht1⟩
    have hN1 : ∀ z ∈ x :: L1, z ∈ candN V G := fun z hz => hN z (hsub.subset hz)
    obtain ⟨σ', L', _, hP', hw'⟩ := path_to_crpath hGV hpath1 hN1
    have hlen : (x :: L1).length ≤ (candN V G).card := by
      rw [← List.toFinset_card_of_nodup hnd]
      exact Finset.card_le_card (fun z hz => hN1 z (List.mem_toFinset.1 hz))
    have hpw := pw_le_len (fun z hz => gw_le (hN1 z hz))
    have hc := card_candN_le (V := V) G
    have hm := hmin σ' L' hP'
    have hmul : (x :: L1).length * V.card ≤ Bd V * V.card :=
      Nat.mul_le_mul_right _ (hlen.trans hc)
    unfold Dm
    omega

lemma extra_le {G : Finset Edge} (hGV : Inside V G) :
    Mz V G ≤ ncomp V G * (2 * Dm V + 4) + (2 * Dm V + 2) := by
  have hd := dval_le hGV
  unfold Mz
  split_ifs <;> omega

lemma Mz_ge (G : Finset Edge) : ncomp V G * (2 * Dm V + 4) + 1 ≤ Mz V G := by
  unfold Mz
  split_ifs <;> omega

-- Losing a component lowers the potential.
--
lemma Mz_lt_of_ncomp {G G' : Finset Edge} (hG' : Inside V G')
    (h : ncomp V G' + 1 ≤ ncomp V G) : Mz V G' < Mz V G := by
  have h1 := extra_le hG'
  have h2 := Mz_ge (V := V) G
  have h3 : (ncomp V G' + 1) * (2 * Dm V + 4) ≤ ncomp V G * (2 * Dm V + 4) :=
    Nat.mul_le_mul_right _ h
  rw [Nat.succ_mul] at h3
  omega

lemma Mz_of_noT3 {G : Finset Edge} (hT : NoTypeIII V G) :
    Mz V G = ncomp V G * (2 * Dm V + 4) + (2 * dval V G + 2) := by
  unfold Mz
  rw [ite_eq_left hT]

lemma Mz_of_T3 {G : Finset Edge} (hT : ¬ NoTypeIII V G) :
    Mz V G = ncomp V G * (2 * Dm V + 4) + 1 := by
  unfold Mz
  rw [ite_eq_right hT]

end potential

/-! ## One round lowers the potential -/

-- Flipping a Type III cell, read in the frame `latA t` where its dark sides are lateral,
-- joins two components.
--
lemma t3_count {V : Finset Pt} {G : Finset Edge} (hG : Deg2 V G) {d : Pt} {tf : Side}
    (ht : findT3 V G = some (d, tf)) : ncomp V (flip G d) + 1 = ncomp V G := by
  obtain ⟨hd, hb, hf, hl1, hl2, hnc⟩ := findT3_some hG.1 ht
  obtain ⟨ff, fb, fl⟩ := frame_latA d tf
  have l1 : lat1 d (latA tf) ∈ G := by
    rcases fl with ⟨e1, _⟩ | ⟨e1, _⟩
    · rw [e1]; exact hb
    · rw [e1]; exact hf
  have l2 : lat2 d (latA tf) ∈ G := by
    rcases fl with ⟨_, e2⟩ | ⟨_, e2⟩
    · rw [e2]; exact hf
    · rw [e2]; exact hb
  have bs : back d (latA tf) ∉ G := by rw [fb]; exact hl2
  have fs : front d (latA tf) ∉ G := by rw [ff]; exact hl1
  have ht' : tf = latA (latA tf) ∨ tf = latB (latA tf) := by
    cases tf <;> simp [latA, latB]
  exact (flip_alt_count hG hd l1 l2 bs fs).2 (cross_to_back ht' l1 l2 hnc)

section round

variable {V : Finset Pt} (hs : Solid V) (x0 : Pt) (hconn : ∀ z ∈ V, Conn (GE V) x0 z)
  (hPC : PathComplete V)
include hs x0 hconn hPC

theorem step_decrease {G : Finset Edge} (hG : Deg2 V G) (h2 : 2 ≤ ncomp V G) :
    ∃ G', step V G = some G' ∧ Mz V G' < Mz V G := by
  rcases ht : findT3 V G with _ | ⟨d, tf⟩
  · have hT := findT3_none hG.1 ht
    rcases hp : findPath V G with _ | ⟨a, L⟩
    · obtain ⟨σ, L, hP⟩ := hPC G hG hT h2
      exact absurd hP (findPath_none hG.1 hp σ L)
    have hstep : step V G = some (applyS G a) := by
      unfold step
      rw [ht, hp]
    refine ⟨_, hstep, ?_⟩
    have hG' := step_deg2 hG hstep
    obtain ⟨hP, hmin⟩ := findPath_some hG.1 hp
    have hMz := Mz_of_noT3 hT
    rw [dval_eq hp] at hMz
    cases L with
    | nil =>
      -- An odd first strip joins two components.
      --
      have hv : ValidSeq V G [a] := ⟨hP.1.1, hP.1.2⟩
      have hc := seq_count [a] G hG hv
      change ncomp V (applyS G a) + 1 = ncomp V G at hc
      exact Mz_lt_of_ncomp hG'.1 (le_of_eq hc)
    | cons b L' =>
      obtain ⟨⟨h1, hpat, hcell, hsep⟩, hch⟩ := hP.1
      have hae : a.n % 2 = 0 := hch.1
      obtain ⟨k, hk⟩ : ∃ k, a.n = k + 2 := ⟨a.n - 2, by omega⟩
      have hfc : applyS G a = flipCol G a.c a.s (k + 2) := by
        unfold applyS
        rw [hk]
      have hpat' : StripPat G a.c a.s (k + 2) := by rw [← hk]; exact hpat
      rcases strip_even_gen k (by omega) G hG (fun j hj => hcell j (by omega)) hpat' hsep with
        heq | hdrop
      · rw [← hfc] at heq
        by_cases hT' : NoTypeIII V (applyS G a)
        · -- The rest of the path is a path of the new 2-factor.
          --
          obtain ⟨hP', hw⟩ := round_ca hs x0 hconn hG hT ⟨h1, hpat, hcell, hsep⟩ hae
            (by omega) hT' hmin hP rfl
          rcases hp' : findPath V (applyS G a) with _ | ⟨σ', L''⟩
          · exact absurd hP' (findPath_none hG'.1 hp' b L')
          have hle := (findPath_some hG'.1 hp').2 b L' hP'
          rw [Mz_of_noT3 hT', dval_eq hp', heq, hMz]
          omega
        · rw [Mz_of_T3 hT', heq, hMz]
          omega
      · rw [← hfc] at hdrop
        exact Mz_lt_of_ncomp hG'.1 (by omega)
  · have hstep : step V G = some (flip G d) := by
      unfold step
      rw [ht]
    refine ⟨_, hstep, ?_⟩
    exact Mz_lt_of_ncomp (step_deg2 hG hstep).1 (le_of_eq (t3_count hG ht))

-- Enough fuel: `run` succeeds when the fuel exceeds the potential.
--
theorem run_complete (hne : V.Nonempty) : ∀ (k : ℕ) (G : Finset Edge), Deg2 V G →
    Mz V G < k → run V k G = true := by
  intro k
  induction k with
  | zero => intro G _ h; omega
  | succ k ih =>
    intro G hG hk
    simp only [run]
    by_cases h1 : cncomp V G = 1
    · simp [h1]
    · rw [ite_eq_right (by simpa using h1)]
      have hpos : 1 ≤ ncomp V G :=
        Finset.card_pos.2 (hne.image _)
      have h2 : 2 ≤ ncomp V G := by
        rw [cncomp_eq hG.1] at h1
        omega
      obtain ⟨G', hs', hlt⟩ := step_decrease hs x0 hconn hPC hG h2
      rw [hs']
      exact ih G' (step_deg2 hG hs') (by omega)

end round

/-! ## Completeness -/

theorem ulhc_complete {V : Finset Pt} (hs : Solid V) {H : Finset Edge} (hH : Deg2 V H)
    (hHam : ncomp V H = 1) (hPC : PathComplete V) : ulhc V = true := by
  have hne : V.Nonempty := by
    have hc : 0 < (V.image (cls V H)).card := by
      unfold ncomp at hHam
      omega
    exact Finset.image_nonempty.1 (Finset.card_pos.1 hc)
  obtain ⟨x0, hx0⟩ := hne
  have hconn : ∀ z ∈ V, Conn (GE V) x0 z := fun z hz =>
    (conn_of_ncomp_one hHam hx0 hz).mono (fun e he => mem_GE.2 (hH.1 e he))
  unfold ulhc
  rcases hf : twoFactor V with _ | F
  · exact absurd ⟨H, hH⟩ (twoFactor_none hf)
  have hF := twoFactor_some hf
  apply run_complete hs x0 hconn hPC ⟨x0, hx0⟩ _ F hF
  have h1 := extra_le hF.1
  have h2 : ncomp V F ≤ V.card := Finset.card_image_le
  have h3 : ncomp V F * (2 * Dm V + 4) ≤ V.card * (2 * Dm V + 4) := Nat.mul_le_mul_right _ h2
  unfold fuel
  rw [Nat.succ_mul]
  omega

end SolidGridHam
