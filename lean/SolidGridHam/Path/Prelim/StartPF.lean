/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import SolidGridHam.Cycle.Phase2
import SolidGridHam.Path.Prelim.TheoremAPF
import SolidGridHam.Cycle.CostAlg
import SolidGridHam.Cycle.CostMinPath
import SolidGridHam.Path.Prelim.ZeroPF
import SolidGridHam.Path.Prelim.CompCleanTg
import SolidGridHam.Cycle.Comp
import SolidGridHam.Cycle.Enum
import SolidGridHam.Path.Prelim.StripCountPF
import SolidGridHam.Path.FindFactor

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

namespace SolidGridHam

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

def desNext (F : Finset Edge) (x : Pt) : Finset Pt :=
  (sidesL.filter (fun s => outArc F (nb x s) s.opp = false)).toFinset.image (nb x)

lemma mem_sidesL' (s : Side) : s ∈ sidesL := by cases s <;> simp [sidesL]

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

def allMatch (s t : Pt) (R : Finset Edge) (τ : Pt → ℤ) (F : Finset Edge) : Bool :=
  (epCells s t).all (fun b => D F R b == τ b)

/-! ## Guesses and the whole algorithm -/

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

section top

variable {V : Finset Pt} {s t : Pt}

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

end top

end HP

end SolidGridHam
