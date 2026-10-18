/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.HP.Guess
import ULHC.HP.CostPF
import ULHC.DFactor

/-!
# The start phase, computably (part 1: fences)

The guided fence chain of `Guess.lean` uses the ancestor and descendant regions of an endpoint
cell and the region flip `rflip`, both stated with propositions. Here:

* `regionC next b n`: breadth-first closure of `{b}` under `next`, `n + 1` rounds;
* `ancNext`, `desNext`: the one-step relations of `AncP` and `DesP`;
* when the computed region lies in `cells V` it is exactly `(cells V).filter (AncP F b)` (resp.
  `DesP`), and otherwise some ancestor (descendant) is not a cell;
* `bndC`, `rflipC`: computable copies of `bnd`, `rflip`.
-/

namespace ULHC

namespace HP

open Finset

/-! ## Breadth-first closure -/

def growF (next : Pt → Finset Pt) (S : Finset Pt) : Finset Pt := S ∪ S.biUnion next

def iterG (next : Pt → Finset Pt) (b : Pt) : ℕ → Finset Pt
  | 0 => {b}
  | k + 1 => growF next (iterG next b k)

section closure

variable (next : Pt → Finset Pt) (b : Pt)

lemma iterG_mono_succ (k : ℕ) : iterG next b k ⊆ iterG next b (k + 1) := by
  intro x hx; simp only [iterG, growF, mem_union]; exact Or.inl hx

lemma iterG_mono {k j : ℕ} (h : k ≤ j) : iterG next b k ⊆ iterG next b j := by
  induction h with
  | refl => exact Subset.refl _
  | step _ ih => exact ih.trans (iterG_mono_succ next b _)

-- Points of the closure are reachable.
--
lemma iterG_reach : ∀ k, ∀ y ∈ iterG next b k, Relation.ReflTransGen (fun x y => y ∈ next x) b y := by
  intro k
  induction k with
  | zero => intro y hy; rw [iterG, mem_singleton] at hy; subst hy; exact Relation.ReflTransGen.refl
  | succ k ih =>
    intro y hy
    simp only [iterG, growF, mem_union, mem_biUnion] at hy
    rcases hy with hy | ⟨x, hx, hxy⟩
    · exact ih y hy
    · exact (ih x hx).tail hxy

-- A closed stage holds every reachable point.
--
lemma reach_iterG {k : ℕ} (hst : growF next (iterG next b k) = iterG next b k) :
    ∀ y, Relation.ReflTransGen (fun x y => y ∈ next x) b y → y ∈ iterG next b k := by
  intro y hy
  induction hy with
  | refl => exact iterG_mono next b (Nat.zero_le k) (by simp [iterG])
  | tail _ hxy ih =>
    rw [← hst]; simp only [growF, mem_union, mem_biUnion]; exact Or.inr ⟨_, ih, hxy⟩

-- Inside a set of `n` points the closure is closed after `n` rounds.
--
lemma iterG_closed {U : Finset Pt} (hU : iterG next b (U.card + 1) ⊆ U) :
    growF next (iterG next b U.card) = iterG next b U.card := by
  by_contra hne
  have hgrow : ∀ m, m ≤ U.card + 1 → m ≤ (iterG next b m).card := by
    intro m
    induction m with
    | zero => intro _; exact Nat.zero_le _
    | succ m ih =>
      intro hm
      have hne' : iterG next b m ≠ iterG next b (m + 1) := by
        intro heq
        apply hne
        have hst : growF next (iterG next b m) = iterG next b m := heq.symm
        have : ∀ j, m ≤ j → iterG next b j = iterG next b m := by
          intro j hj
          induction hj with
          | refl => rfl
          | step _ ihj => show growF next _ = _; rw [ihj, hst]
        rw [show growF next (iterG next b U.card) = iterG next b (U.card + 1) from rfl,
          this (U.card + 1) (by omega), this U.card (by omega)]
      have hss : iterG next b m ⊂ iterG next b (m + 1) :=
        ssubset_of_subset_of_ne (iterG_mono_succ next b m) hne'
      have := card_lt_card hss
      have := ih (by omega)
      omega
  have h1 := hgrow (U.card + 1) le_rfl
  have h2 := card_le_card hU
  omega

end closure

/-! ## Ancestor and descendant steps -/

-- Predecessors of `y` under `ArcTo`: `x` with `ArcTo F x y`.
--
def ancNext (F : Finset Edge) (y : Pt) : Finset Pt :=
  (sidesL.filter (fun s => outArc F y s = false)).toFinset.image (nb y)

-- Successors of `x` under `ArcTo`: `y` with `ArcTo F x y`... read as `ArcTo F x y` in
-- `DesP`'s chain from `b` (`nb y s = x`, `outArc F y s = false`).
--
def desNext (F : Finset Edge) (x : Pt) : Finset Pt :=
  (sidesL.filter (fun s => outArc F (nb x s) s.opp = false)).toFinset.image (nb x)

lemma mem_sidesL' (s : Side) : s ∈ sidesL := by cases s <;> simp [sidesL]

lemma mem_ancNext {F : Finset Edge} {x y : Pt} : x ∈ ancNext F y ↔ ArcTo F x y := by
  unfold ancNext ArcTo
  simp only [mem_image, List.mem_toFinset, List.mem_filter, mem_sidesL', true_and,
    decide_eq_true_eq]
  constructor
  · rintro ⟨s, hs, rfl⟩; exact ⟨s, rfl, hs⟩
  · rintro ⟨s, rfl, hs⟩; exact ⟨s, hs, rfl⟩

lemma mem_desNext {F : Finset Edge} {x y : Pt} : y ∈ desNext F x ↔ ArcTo F x y := by
  unfold desNext ArcTo
  simp only [mem_image, List.mem_toFinset, List.mem_filter, mem_sidesL', true_and,
    decide_eq_true_eq]
  constructor
  · rintro ⟨s, hs, rfl⟩; exact ⟨s.opp, nb_nb_opp x s, hs⟩
  · rintro ⟨s, rfl, hs⟩
    refine ⟨s.opp, ?_, ?_⟩
    · rw [opp_opp, nb_nb_opp]; exact hs
    · rw [nb_nb_opp]

lemma ancP_iff {F : Finset Edge} {b c : Pt} :
    AncP F b c ↔ Relation.ReflTransGen (fun x y => y ∈ ancNext F x) b c := by
  unfold AncP
  have e : (fun x y => y ∈ ancNext F x) = Function.swap (ArcTo F) := by
    funext x y; simp [Function.swap, mem_ancNext]
  rw [e]
  exact ⟨fun h => h.swap, fun h => by have := h.swap; simpa [Function.swap] using this⟩

lemma desP_iff {F : Finset Edge} {b c : Pt} :
    DesP F b c ↔ Relation.ReflTransGen (fun x y => y ∈ desNext F x) b c := by
  unfold DesP
  have e : (fun x y => y ∈ desNext F x) = ArcTo F := by
    funext x y; simp [mem_desNext]
  rw [e]

/-! ## Regions -/

def regionC (next : Pt → Finset Pt) (V : Finset Pt) (b : Pt) : Finset Pt :=
  iterG next b ((cells V).card + 1)

-- When the computed region lies in `cells V`, it is the whole reachable set (all cells).
--
open Classical in
theorem regionC_spec {next : Pt → Finset Pt} {V : Finset Pt} {b : Pt}
    (h : regionC next V b ⊆ cells V) :
    (∀ c, Relation.ReflTransGen (fun x y => y ∈ next x) b c → IsCell V c) ∧
      regionC next V b = (cells V).filter (Relation.ReflTransGen (fun x y => y ∈ next x) b) := by
  classical
  have hcl := iterG_closed next b h
  have hcl' : growF next (iterG next b ((cells V).card + 1)) = iterG next b ((cells V).card + 1) := by
    have e1 : iterG next b ((cells V).card + 1) = iterG next b (cells V).card := hcl
    rw [e1]; exact hcl
  have hall : ∀ c, Relation.ReflTransGen (fun x y => y ∈ next x) b c → c ∈ regionC next V b :=
    fun c hc => reach_iterG next b hcl' c hc
  refine ⟨fun c hc => mem_cells.1 (h (hall c hc)), ?_⟩
  ext c
  simp only [mem_filter]
  exact ⟨fun hc => ⟨h hc, iterG_reach next b _ c hc⟩, fun ⟨_, hc⟩ => hall c hc⟩

-- When it does not, some reachable point is not a cell.
--
theorem regionC_not {next : Pt → Finset Pt} {V : Finset Pt} {b : Pt}
    (h : ¬ regionC next V b ⊆ cells V) :
    ¬ ∀ c, Relation.ReflTransGen (fun x y => y ∈ next x) b c → IsCell V c := by
  intro hall
  apply h
  intro c hc
  exact mem_cells.2 (hall c (iterG_reach next b _ c hc))

/-! ## Region flip, computably -/

def bndC (R : Finset Pt) : Finset Edge :=
  (R.biUnion cellE).filter (fun e => (decide (e.lo ∈ R) != decide (e.hi ∈ R)) = true)

def rflipC (F : Finset Edge) (R : Finset Pt) : Finset Edge := symmDiff F (bndC R)

lemma rflipC_eq (F : Finset Edge) (R : Finset Pt) : rflipC F R = rflip F R := by
  classical
  unfold rflipC rflip
  congr 1

/-! ## The guided step and chain, computably -/

-- The cells with `s` (resp. `t`) as a corner, in `absSumAt`'s order.
--
def epCells (s t : Pt) : List Pt :=
  [s, (s.1 - 1, s.2), (s.1, s.2 - 1), (s.1 - 1, s.2 - 1),
   t, (t.1 - 1, t.2), (t.1, t.2 - 1), (t.1 - 1, t.2 - 1)]

lemma isCorner_iff_mem (z w : Pt) :
    IsCorner z w ↔ w = z ∨ w = (z.1 - 1, z.2) ∨ w = (z.1, z.2 - 1) ∨ w = (z.1 - 1, z.2 - 1) := by
  obtain ⟨a, b⟩ := z; obtain ⟨x, y⟩ := w
  unfold IsCorner
  simp only [Prod.mk.injEq]
  omega

lemma mem_epCells {s t w : Pt} : w ∈ epCells s t ↔ IsCorner s w ∨ IsCorner t w := by
  rw [isCorner_iff_mem, isCorner_iff_mem]
  simp only [epCells, List.mem_cons, List.not_mem_nil, or_false]
  tauto

-- One fence at `b` toward the target `τ b`.
--
def stepAt (V : Finset Pt) (R : Finset Edge) (τ : Pt → ℤ) (F : Finset Edge) (b : Pt) :
    Option (Finset Edge) :=
  if D F R b < τ b then
    (if regionC (ancNext F) V b ⊆ cells V then some (rflipC F (regionC (ancNext F) V b)) else none)
  else
    (if regionC (desNext F) V b ⊆ cells V then some (rflipC F (regionC (desNext F) V b)) else none)

def allMatch (s t : Pt) (R : Finset Edge) (τ : Pt → ℤ) (F : Finset Edge) : Bool :=
  (epCells s t).all (fun b => D F R b == τ b)

def guidedStepC (V : Finset Pt) (s t : Pt) (R : Finset Edge) (τ : Pt → ℤ) (F : Finset Edge) :
    Option (Finset Edge) :=
  match (epCells s t).find? (fun b => D F R b != τ b) with
  | none => none
  | some b => stepAt V R τ F b

def guidedChainC (V : Finset Pt) (s t : Pt) (R : Finset Edge) (τ : Pt → ℤ) :
    ℕ → Finset Edge → Option (Finset Edge)
  | 0, F => if allMatch s t R τ F then some F else none
  | k + 1, F =>
    if allMatch s t R τ F then some F
    else match guidedStepC V s t R τ F with
      | some F' => guidedChainC V s t R τ k F'
      | none => none

section guided

variable {V : Finset Pt} {d : Pt → ℕ} {s t : Pt} {R : Finset Edge} {τ : Pt → ℤ}

open Classical in
lemma ancRegion_eq {F : Finset Edge} {b : Pt} (h : regionC (ancNext F) V b ⊆ cells V) :
    (∀ c, AncP F b c → IsCell V c) ∧ regionC (ancNext F) V b = (cells V).filter (AncP F b) := by
  obtain ⟨h1, h2⟩ := regionC_spec h
  refine ⟨fun c hc => h1 c (ancP_iff.1 hc), ?_⟩
  rw [h2]
  exact Finset.filter_congr (fun c _ => ancP_iff.symm)

open Classical in
lemma desRegion_eq {F : Finset Edge} {b : Pt} (h : regionC (desNext F) V b ⊆ cells V) :
    (∀ c, DesP F b c → IsCell V c) ∧ regionC (desNext F) V b = (cells V).filter (DesP F b) := by
  obtain ⟨h1, h2⟩ := regionC_spec h
  refine ⟨fun c hc => h1 c (desP_iff.1 hc), ?_⟩
  rw [h2]
  exact Finset.filter_congr (fun c _ => desP_iff.symm)

-- A computed fence is a guided step.
--
lemma stepAt_guided {F F' : Finset Edge} {b : Pt} (hb : b ∈ epCells s t) (hne : D F R b ≠ τ b)
    (h : stepAt V R τ F b = some F') : GuidedStep V s t R τ F F' := by
  classical
  obtain ⟨z, hz, hzb⟩ : ∃ z, (z = s ∨ z = t) ∧ IsCorner z b := by
    rcases mem_epCells.1 hb with h | h
    · exact ⟨s, Or.inl rfl, h⟩
    · exact ⟨t, Or.inr rfl, h⟩
  unfold stepAt at h
  split_ifs at h with hlt hsub hsub'
  · simp only [Option.some.injEq] at h
    obtain ⟨hall, heq⟩ := ancRegion_eq hsub
    refine ⟨z, b, hz, hzb, hne, Or.inl ⟨hlt, hall, ?_⟩⟩
    rw [← h, rflipC_eq, heq]
  · simp only [Option.some.injEq] at h
    obtain ⟨hall, heq⟩ := desRegion_eq hsub'
    refine ⟨z, b, hz, hzb, hne, Or.inr ⟨by omega, hall, ?_⟩⟩
    rw [← h, rflipC_eq, heq]

lemma guidedStepC_guided {F F' : Finset Edge} (h : guidedStepC V s t R τ F = some F') :
    GuidedStep V s t R τ F F' := by
  unfold guidedStepC at h
  split at h
  · simp at h
  · rename_i b hb
    have hmem := List.mem_of_find?_eq_some hb
    have hp := List.find?_some hb
    simp only [bne_iff_ne, ne_eq] at hp
    exact stepAt_guided hmem hp h

-- Guided steps keep the factor.
--
lemma guided_factor {F F' : Finset Edge} (hF : IsFactor V d F) (h : GuidedStep V s t R τ F F') :
    IsFactor V d F' := by
  obtain ⟨_, b, _, _, _, h⟩ := h
  rcases h with ⟨_, hall, rfl⟩ | ⟨_, hall, rfl⟩
  · exact (smallest_fence hF hall).1
  · exact (desc_fence hF hall).1

lemma guidedChainC_factor : ∀ k (F F1 : Finset Edge), IsFactor V d F →
    guidedChainC V s t R τ k F = some F1 → IsFactor V d F1 := by
  intro k
  induction k with
  | zero =>
    intro F F1 hF h
    simp only [guidedChainC] at h
    split_ifs at h; simp only [Option.some.injEq] at h; exact h ▸ hF
  | succ k ih =>
    intro F F1 hF h
    simp only [guidedChainC] at h
    split_ifs at h
    · simp only [Option.some.injEq] at h; exact h ▸ hF
    · rcases hs : guidedStepC V s t R τ F with _ | F'
      · rw [hs] at h; simp at h
      · rw [hs] at h
        exact ih F' F1 (guided_factor hF (guidedStepC_guided hs)) h

-- **Completeness of the guided chain.** For targets equal to `H`'s values on the endpoint cells,
-- the chain ends at a factor with zeros at the endpoint cells.
--
theorem guidedChainC_complete {H : Finset Edge} (hs : Solid V) (hH : IsFactor V d H)
    (_hR : IsFactor V d R) (hτ : ∀ w ∈ epCells s t, τ w = D H R w) :
    ∀ n (F : Finset Edge), IsFactor V d F → absSumAt F H s + absSumAt F H t ≤ 2 * n →
      ∃ F1, guidedChainC V s t R τ n F = some F1 ∧ IsFactor V d F1 ∧
        ∀ w, IsCorner s w ∨ IsCorner t w → D F1 H w = 0 := by
  have hD : ∀ G x, D G H x = D G R x - D H R x := fun G x => by have := D_add G H R x; omega
  have hdone : ∀ F, allMatch s t R τ F = true → ∀ w, IsCorner s w ∨ IsCorner t w → D F H w = 0 := by
    intro F hm w hw
    have hw' := mem_epCells.2 hw
    have := List.all_eq_true.1 hm w hw'
    simp only [beq_iff_eq] at this
    rw [hD, this, hτ w hw']; ring
  intro n
  induction n with
  | zero =>
    intro F hF hle
    have hm : allMatch s t R τ F = true := by
      unfold allMatch
      refine List.all_eq_true.2 (fun w hw => ?_)
      simp only [beq_iff_eq]
      have h0s : absSumAt F H s = 0 := by omega
      have h0t : absSumAt F H t = 0 := by omega
      simp only [absSumAt, Nat.add_eq_zero_iff, Int.natAbs_eq_zero] at h0s h0t
      have hz : D F H w = 0 := by
        rcases mem_epCells.1 hw with h | h
        · rw [isCorner_iff_mem] at h
          rcases h with rfl | rfl | rfl | rfl
          · exact h0s.1.1.1
          · exact h0s.1.1.2
          · exact h0s.1.2
          · exact h0s.2
        · rw [isCorner_iff_mem] at h
          rcases h with rfl | rfl | rfl | rfl
          · exact h0t.1.1.1
          · exact h0t.1.1.2
          · exact h0t.1.2
          · exact h0t.2
      rw [hτ w hw]; rw [hD] at hz; omega
    exact ⟨F, by simp only [guidedChainC, hm, ite_true], hF, hdone F hm⟩
  | succ n ih =>
    intro F hF hle
    by_cases hm : allMatch s t R τ F = true
    · exact ⟨F, by simp only [guidedChainC, hm, ite_true], hF, hdone F hm⟩
    -- Some endpoint cell is off target: the first one is fenced.
    have hfind : ∃ b, (epCells s t).find? (fun b => D F R b != τ b) = some b := by
      rcases hf : (epCells s t).find? (fun b => D F R b != τ b) with _ | b
      · exfalso; apply hm
        unfold allMatch
        refine List.all_eq_true.2 (fun w hw => ?_)
        have := List.find?_eq_none.1 hf w hw
        simpa using this
      · exact ⟨b, rfl⟩
    obtain ⟨b, hb⟩ := hfind
    have hbm := List.mem_of_find?_eq_some hb
    have hbne : D F R b ≠ τ b := by have := List.find?_some hb; simpa using this
    have hbH : D F R b ≠ D H R b := by rw [← hτ b hbm]; exact hbne
    have hDb : D F H b = D F R b - D H R b := hD F b
    -- The fence region consists of cells (as in `guided_step_exists`).
    have hstep : ∃ F', stepAt V R τ F b = some F' := by
      unfold stepAt
      rw [hτ b hbm]
      split_ifs with hlt hsub hsub'
      · exact ⟨_, rfl⟩
      · exfalso
        apply regionC_not hsub
        intro c hc
        have hc' := ancP_iff.2 hc
        by_contra hnc
        have h1 := D_eq_zero_of_not_cell hF hH hs hnc
        have h2 := D_le_anc hF hH hc'
        omega
      · exact ⟨_, rfl⟩
      · exfalso
        apply regionC_not hsub'
        intro c hc
        have hc' := desP_iff.2 hc
        by_contra hnc
        have h1 := D_eq_zero_of_not_cell hF hH hs hnc
        have h2 := D_ge_desc hF hH hc'
        omega
    obtain ⟨F', hF'⟩ := hstep
    have hgs : guidedStepC V s t R τ F = some F' := by unfold guidedStepC; rw [hb]; exact hF'
    have hG : GuidedStep V s t R (D H R) F F' := by
      have := stepAt_guided hbm hbne hF'
      obtain ⟨z, b', hz, hzb, hne, hcase⟩ := this
      have hb'm : b' ∈ epCells s t := by
        rcases hz with rfl | rfl
        · exact mem_epCells.2 (Or.inl hzb)
        · exact mem_epCells.2 (Or.inr hzb)
      rw [hτ b' hb'm] at hne hcase
      exact ⟨z, b', hz, hzb, hne, hcase⟩
    obtain ⟨hF'f, _, hdec⟩ := guided_step_spec hF hH hG
    obtain ⟨F1, h1, h2, h3⟩ := ih F' hF'f (by omega)
    refine ⟨F1, ?_, h2, h3⟩
    simp only [guidedChainC, hm, Bool.false_eq_true, ite_false, hgs]
    exact h1

end guided

/-! ## Guesses and the whole algorithm -/

-- The degrees of an s–t path-factor.
--
def dST (s t : Pt) (z : Pt) : ℕ := if z = s ∨ z = t then 1 else 2

lemma dST_le (s t z : Pt) : dST s t z ≤ 2 := by unfold dST; split_ifs <;> omega

-- A guess: `H`'s edge at `s`, `H`'s `D · R` at the cell `s`, and the same at `t`.
--
structure Guess where
  es : Edge
  vs : ℤ
  et : Edge
  vt : ℤ

-- The window rule: from one value and the edge at `z`, the values on the four cells at `z`
-- (`D` changes across each edge at `z` by its weight, `D_jump`).
--
def winVal (R : Finset Edge) (z : Pt) (e : Edge) (v : ℤ) (x : Pt) : Option ℤ :=
  if x = z then some v
  else if x = (z.1, z.2 - 1) then some (v - wD {e} R (eR z))
  else if x = (z.1 - 1, z.2) then some (v - wD {e} R (eU z))
  else if x = (z.1 - 1, z.2 - 1) then some (v - wD {e} R (eR z) - wD {e} R (eD z))
  else none

def tauOf (R : Finset Edge) (s t : Pt) (g : Guess) (x : Pt) : ℤ :=
  match winVal R s g.es g.vs x with
  | some v => v
  | none => (winVal R t g.et g.vt x).getD 0

def edgesAt (z : Pt) : List Edge := [eR z, eL z, eU z, eD z]

def vals (B : ℕ) : List ℤ := (List.range (2 * B + 1)).map (fun i : ℕ => (i : ℤ) - (B : ℤ))

def guessList (V : Finset Pt) (s t : Pt) : List Guess :=
  (edgesAt s).flatMap fun es => (vals (4 * V.card)).flatMap fun vs =>
    (edgesAt t).flatMap fun et => (vals (4 * V.card)).map fun vt => ⟨es, vs, et, vt⟩

-- **The algorithm.** A starting path-factor `R`, then for every guess: the guided fence chain
-- from `R`, then the restricted search (`runPF`, `fuelPF V` rounds).
--
def hpPF (V : Finset Pt) (s t : Pt) : Bool :=
  match findFactor V (dST s t) with
  | none => false
  | some R => (guessList V s t).any fun g =>
      match guidedChainC V s t R (tauOf R s t g) (16 * V.card + 1) R with
      | some F1 => runPF V s t (fuelPF V) F1
      | none => false

section top

variable {V : Finset Pt} {s t : Pt}

-- **Soundness.** A `true` answer gives an s–t path-factor with one component (a Hamiltonian
-- s–t path).
--
theorem hpPF_sound (_hst : s ≠ t) (hsV : s ∈ V) (h : hpPF V s t = true) :
    ∃ H, IsFactor V (dST s t) H ∧ ncomp V H = 1 := by
  have hd : ∀ z, z ≠ s → z ≠ t → dST s t z = 2 := fun z h1 h2 => by unfold dST; simp [h1, h2]
  have hds : dST s t s = 1 := by unfold dST; simp
  unfold hpPF at h
  rcases hR : findFactor V (dST s t) with _ | R
  · rw [hR] at h; simp at h
  rw [hR] at h
  have hRf := findFactor_some (dST_le s t) hR
  obtain ⟨g, _, hg⟩ := List.any_eq_true.1 h
  rcases hc : guidedChainC V s t R (tauOf R s t g) (16 * V.card + 1) R with _ | F1
  · rw [hc] at hg; simp at hg
  rw [hc] at hg
  exact runPF_sound hd hds hsV _ F1 (guidedChainC_factor _ R F1 hRf hc) hg

/-! ### Completeness -/

lemma card_le_factor {d : Pt → ℕ} (hd2 : ∀ z, d z ≤ 2) {F : Finset Edge} (hF : IsFactor V d F) :
    F.card ≤ V.card := by
  refine DF.card_le_of_good hd2 ⟨Inside.of_factor hF, fun z => ?_⟩
  by_cases hz : z ∈ V
  · rw [hF.2 z hz]
  · rw [deg_zero_of_inside (Inside.of_factor hF) hz]; omega

-- `|D| ≤ 4 |V|` for two factors with degrees at most 2.
--
lemma D_natAbs_le {d : Pt → ℕ} (hd2 : ∀ z, d z ≤ 2) {F H : Finset Edge} (hF : IsFactor V d F)
    (hH : IsFactor V d H) (x : Pt) : (D F H x).natAbs ≤ 4 * V.card := by
  have h1 := card_le_factor hd2 hF
  have h2 := card_le_factor hd2 hH
  have hsd : (symmDiff F H).card ≤ F.card + H.card := by
    have hsub : symmDiff F H ⊆ F ∪ H := by
      intro e he; rw [Finset.mem_symmDiff] at he; rw [Finset.mem_union]; tauto
    exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hw : ∀ e, |wD F H e| ≤ 2 := by
    intro e; unfold wD wb; split_ifs <;> simp
  unfold D pot
  set S := (symmDiff F H).filter (RowSel x)
  have k1 : |∑ e ∈ S, wD F H e| ≤ ∑ e ∈ S, |wD F H e| := Finset.abs_sum_le_sum_abs _ _
  have k2 : ∑ e ∈ S, |wD F H e| ≤ ∑ e ∈ S, (2 : ℤ) := Finset.sum_le_sum (fun e _ => hw e)
  rw [Finset.sum_const, nsmul_eq_mul] at k2
  have h4 : S.card ≤ (symmDiff F H).card := Finset.card_le_card (Finset.filter_subset _ _)
  have k3 : ((∑ e ∈ S, wD F H e).natAbs : ℤ) ≤ (S.card : ℤ) * 2 := by
    rw [Int.natCast_natAbs]; linarith
  have k4 : (∑ e ∈ S, wD F H e).natAbs ≤ S.card * 2 := by exact_mod_cast k3
  omega

lemma wD_congr {H H' R : Finset Edge} {e : Edge} (h : e ∈ H ↔ e ∈ H') : wD H R e = wD H' R e := by
  unfold wD up inE1
  simp only [h]

-- The window rule is right for `H`: if `H`'s edges at `z` are exactly `e`, the computed values
-- are `H`'s on the four cells at `z`.
--
lemma winVal_correct {d : Pt → ℕ} {H R : Finset Edge} (hH : IsFactor V d H) (hR : IsFactor V d R)
    {z : Pt} {e : Edge} (he : ∀ f ∈ edgesAt z, f ∈ H ↔ f = e) :
    ∀ y, ∀ w, winVal R z e (D H R z) y = some w → w = D H R y := by
  intro y w h
  have j1 := D_jump hH hR (eR z)
  have j2 := D_jump hH hR (eU z)
  have j3 := D_jump hH hR (eD z)
  have c1 : wD H R (eR z) = wD {e} R (eR z) := wD_congr (by
    rw [he _ (by simp [edgesAt]), Finset.mem_singleton])
  have c2 : wD H R (eU z) = wD {e} R (eU z) := wD_congr (by
    rw [he _ (by simp [edgesAt]), Finset.mem_singleton])
  have c3 : wD H R (eD z) = wD {e} R (eD z) := wD_congr (by
    rw [he _ (by simp [edgesAt]), Finset.mem_singleton])
  simp only [eR, eU, eD, Edge.hi, Edge.lo] at j1 j2 j3 c1 c2 c3
  unfold winVal at h
  split_ifs at h with h1 h2 h3 h4 <;> simp only [Option.some.injEq] at h <;> subst h
  · rw [h1]
  · rw [h2]; simp only [eR]; omega
  · rw [h3]; simp only [eU]; omega
  · rw [h4]; simp only [eR, eD]; omega

lemma mem_vals {B : ℕ} {v : ℤ} (h : v.natAbs ≤ B) : v ∈ vals B := by
  have h1 : 0 ≤ v + B := by rcases Int.natAbs_eq v with h' | h' <;> omega
  have h2 : ((v + B).toNat : ℤ) < 2 * B + 1 := by
    rw [Int.toNat_of_nonneg h1]; rcases Int.natAbs_eq v with h' | h' <;> omega
  rw [vals, List.mem_map]
  exact ⟨(v + B).toNat, List.mem_range.2 (by exact_mod_cast h2),
    by rw [Int.toNat_of_nonneg h1]; ring⟩

lemma pne1 (z : Pt) : (z.1 - 1, z.2) ≠ z := fun h => by have := congrArg Prod.fst h; simp at this
lemma pne2 (z : Pt) : (z.1, z.2 - 1) ≠ z := fun h => by have := congrArg Prod.snd h; simp at this
lemma pne3 (z : Pt) : (z.1 - 1, z.2 - 1) ≠ z := fun h => by have := congrArg Prod.fst h; simp at this
lemma pne4 (z : Pt) : (z.1 - 1, z.2) ≠ (z.1, z.2 - 1) := fun h => by
  have := congrArg Prod.fst h; simp at this
lemma pne5 (z : Pt) : (z.1 - 1, z.2 - 1) ≠ (z.1, z.2 - 1) := fun h => by
  have := congrArg Prod.fst h; simp at this
lemma pne6 (z : Pt) : (z.1 - 1, z.2 - 1) ≠ (z.1 - 1, z.2) := fun h => by
  have := congrArg Prod.snd h; simp at this

lemma edges_ne (z : Pt) : eR z ≠ eL z ∧ eR z ≠ eU z ∧ eR z ≠ eD z ∧ eL z ≠ eU z ∧ eL z ≠ eD z ∧
    eU z ≠ eD z := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;> simp only [eR, eL, eU, eD, Edge.mk.injEq] at h
  · exact pne1 z h.2.symm
  · exact absurd h.1 (by decide)
  · exact absurd h.1 (by decide)
  · exact absurd h.1 (by decide)
  · exact absurd h.1 (by decide)
  · exact pne2 z h.2.symm

-- A degree-1 point has exactly one edge.
--
lemma unique_edge {F : Finset Edge} {z : Pt} (h : deg F z = 1) :
    ∃ e ∈ edgesAt z, ∀ f ∈ edgesAt z, f ∈ F ↔ f = e := by
  obtain ⟨n1, n2, n3, n4, n5, n6⟩ := edges_ne z
  unfold deg ind at h
  have key : ∀ e ∈ edgesAt z, e ∈ F → (∀ f ∈ edgesAt z, f ≠ e → f ∉ F) →
      ∃ e ∈ edgesAt z, ∀ f ∈ edgesAt z, f ∈ F ↔ f = e := fun e he hF hoth =>
    ⟨e, he, fun f hf => ⟨fun hfF => by by_contra hne; exact hoth f hf hne hfF, fun h' => h' ▸ hF⟩⟩
  have hoth : ∀ e, (∀ g, g = eR z ∨ g = eL z ∨ g = eU z ∨ g = eD z → g ≠ e → g ∉ F) →
      ∀ f ∈ edgesAt z, f ≠ e → f ∉ F := by
    intro e h f hf
    simp only [edgesAt, List.mem_cons, List.not_mem_nil, or_false] at hf
    exact h f hf
  have m : ∀ g, g = eR z ∨ g = eL z ∨ g = eU z ∨ g = eD z → g ∈ edgesAt z := by
    intro g hg; simp only [edgesAt, List.mem_cons, List.not_mem_nil, or_false]; exact hg
  split_ifs at h <;> (try omega)
  all_goals first
    | exact key _ (m _ (Or.inl rfl)) (by assumption) (hoth _ (by
        rintro g (rfl | rfl | rfl | rfl) hg <;> first | exact absurd rfl hg | assumption))
    | exact key _ (m _ (Or.inr (Or.inl rfl))) (by assumption) (hoth _ (by
        rintro g (rfl | rfl | rfl | rfl) hg <;> first | exact absurd rfl hg | assumption))
    | exact key _ (m _ (Or.inr (Or.inr (Or.inl rfl)))) (by assumption) (hoth _ (by
        rintro g (rfl | rfl | rfl | rfl) hg <;> first | exact absurd rfl hg | assumption))
    | exact key _ (m _ (Or.inr (Or.inr (Or.inr rfl)))) (by assumption) (hoth _ (by
        rintro g (rfl | rfl | rfl | rfl) hg <;> first | exact absurd rfl hg | assumption))

lemma winVal_none {R : Finset Edge} {z : Pt} {e : Edge} {v : ℤ} {x : Pt}
    (hx : ¬ IsCorner z x) : winVal R z e v x = none := by
  rw [isCorner_iff_mem] at hx
  unfold winVal
  push Not at hx
  simp [hx.1, hx.2.1, hx.2.2.1, hx.2.2.2]

lemma winVal_some {R : Finset Edge} {z : Pt} {e : Edge} {v : ℤ} {x : Pt}
    (hx : IsCorner z x) : ∃ w, winVal R z e v x = some w := by
  rw [isCorner_iff_mem] at hx
  unfold winVal
  rcases hx with rfl | rfl | rfl | rfl <;>
    simp [pne1, pne2, pne3]

-- **Completeness.** If `V` has a Hamiltonian s–t path, the algorithm answers `true` (modulo the
-- named gaps behind `runPF_complete_fuel`).
--
theorem hpPF_complete (hs : Solid V) (_hst : s ≠ t) (hsV : s ∈ V) (htV : t ∈ V)
    (hg : GapsPF V (dST s t) s t)
    {H : Finset Edge} (hH : IsFactor V (dST s t) H) (hHam : ncomp V H = 1) : hpPF V s t = true := by
  have hd : ∀ z, z ≠ s → z ≠ t → dST s t z = 2 := fun z h1 h2 => by unfold dST; simp [h1, h2]
  have hds : dST s t s = 1 := by unfold dST; simp
  have hdt : dST s t t = 1 := by unfold dST; simp
  unfold hpPF
  rcases hR : findFactor V (dST s t) with _ | R
  · exact absurd ⟨H, hH⟩ (findFactor_none (dST_le s t) hR)
  simp only
  have hRf := findFactor_some (dST_le s t) hR
  obtain ⟨es, hes, hesu⟩ := unique_edge (show deg H s = 1 by rw [hH.2 s hsV, hds])
  obtain ⟨et, het, hetu⟩ := unique_edge (show deg H t = 1 by rw [hH.2 t htV, hdt])
  set g : Guess := ⟨es, D H R s, et, D H R t⟩
  have hgm : g ∈ guessList V s t := by
    unfold guessList
    simp only [List.mem_flatMap, List.mem_map]
    exact ⟨es, hes, D H R s, mem_vals (D_natAbs_le (dST_le s t) hH hRf s), et, het, D H R t,
      mem_vals (D_natAbs_le (dST_le s t) hH hRf t), rfl⟩
  have hτ : ∀ w ∈ epCells s t, tauOf R s t g w = D H R w := by
    intro w hw
    unfold tauOf
    by_cases hws : IsCorner s w
    · obtain ⟨v, hv⟩ := winVal_some (R := R) (e := es) (v := D H R s) hws
      rw [hv]
      exact winVal_correct hH hRf hesu w v hv
    · rw [winVal_none hws]
      have hwt : IsCorner t w := (mem_epCells.1 hw).resolve_left hws
      obtain ⟨v, hv⟩ := winVal_some (R := R) (e := et) (v := D H R t) hwt
      show (winVal R t et (D H R t) w).getD 0 = _
      rw [hv, Option.getD_some]
      exact winVal_correct hH hRf hetu w v hv
  have hab : absSumAt R H s + absSumAt R H t ≤ 2 * (16 * V.card + 1) := by
    have b := fun x => D_natAbs_le (dST_le s t) hRf hH x
    unfold absSumAt
    have := b s; have := b (s.1 - 1, s.2); have := b (s.1, s.2 - 1); have := b (s.1 - 1, s.2 - 1)
    have := b t; have := b (t.1 - 1, t.2); have := b (t.1, t.2 - 1); have := b (t.1 - 1, t.2 - 1)
    omega
  obtain ⟨F1, hc, hF1, hz⟩ := guidedChainC_complete hs hH hRf hτ (16 * V.card + 1) R hRf hab
  refine List.any_eq_true.2 ⟨g, hgm, ?_⟩
  rw [hc]
  exact runPF_complete_fuel hs hH hHam hd hds hdt hsV htV hg F1 hF1 (Or.inl hz)

-- **Correctness of the s–t path algorithm**, given the open lemmas `GapsPF` of this route:
-- `hpPF V s t` answers `true` exactly when `V` has a Hamiltonian s–t path.
--
theorem hpPF_correct (hs : Solid V) (hst : s ≠ t) (hsV : s ∈ V) (htV : t ∈ V)
    (hg : GapsPF V (dST s t) s t) :
    hpPF V s t = true ↔ ∃ H, IsFactor V (dST s t) H ∧ ncomp V H = 1 :=
  ⟨hpPF_sound hst hsV, fun ⟨_, hH, hHam⟩ => hpPF_complete hs hst hsV htV hg hH hHam⟩

-- **Correctness with no open lemma when no cell has `s` or `t` as a corner** (both endpoints
-- dangle off the body of the graph).
--
theorem hpPF_correct_dang (hs : Solid V) (hst : s ≠ t) (hsV : s ∈ V) (htV : t ∈ V)
    (hD : Dang V s t) :
    hpPF V s t = true ↔ ∃ H, IsFactor V (dST s t) H ∧ ncomp V H = 1 :=
  ⟨hpPF_sound hst hsV, fun ⟨_, hH, hHam⟩ => hpPF_complete hs hst hsV htV (gapsPF_dang hD) hH hHam⟩

end top

end HP

end ULHC
