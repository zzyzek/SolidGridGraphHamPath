/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import SolidGridHam.Cycle.StripCount
public import SolidGridHam.Algorithm

@[expose] public section

/-!
# A verified 2-factor algorithm for grid graphs

`twoFactor V` returns `some F` with `Deg2 V F`, or `none` when no such `F` exists.

Method: bipartite b-matching with `b = 2`. A point is *black* when its coordinate sum is
even; every grid edge joins a black and a white point. The state is an edge set `F` of
grid edges with all degrees at most 2 (`Good`). One augmentation:
* builds the alternating layers `layer V F k`: layer 0 holds the deficient black points
  (degree < 2), and a step goes from a black point along a grid edge not in `F`, or from
  a white point along an edge of `F`;
* picks a deficient white point in the last layer, and walks back down the layers,
  inserting the non-`F` edges and erasing the `F` edges it crosses. The layer index drops
  at every step, so the walk never revisits a point and adds exactly one edge in total.

When no deficient white point is reachable, a counting argument on the reachable set
shows that no 2-factor exists unless every degree is already 2.

Running time, as explicit iteration bounds (proved below):
* at most `|V| + 1` augmentation rounds (`|F|` grows by one per round, `|F| ≤ |V|`);
* each round builds `|V| + 1` layers once (`layerAcc`; `layer V F |V|` is already closed,
  `layer_closed`), each layer from the previous one by scanning 4 edges per point;
* each walk takes at most `|V|` steps (one per layer, `walk` consumes the layer list).
Each layer step and walk step is polynomial work on `Finset`s, so the whole algorithm is
polynomial in `|V|`.
-/

namespace SolidGridHam

open Finset

-- Helpers live in `SolidGridHam.TF` to avoid clashes with names elsewhere in the development.
--
namespace TF

/-! ## Colours, incident edges, steps -/

-- Black points have an even coordinate sum.
--
def Black (z : Pt) : Prop := (z.1 + z.2) % 2 = 0

instance (z : Pt) : Decidable (Black z) := by unfold Black; infer_instance

-- A forward alternating step from `u` along `e`: a grid edge, not in `F` when `u` is
-- black, in `F` when `u` is white.
--
def Fwd (V : Finset Pt) (F : Finset Edge) (u : Pt) (e : Edge) : Prop :=
  IsEdge V e ∧ (Black u → e ∉ F) ∧ (¬ Black u → e ∈ F)

instance (V : Finset Pt) (F : Finset Edge) (u : Pt) (e : Edge) : Decidable (Fwd V F u e) := by
  unfold Fwd; infer_instance

-- The points one forward step from `u`.
--
def nbr (V : Finset Pt) (F : Finset Edge) (u : Pt) : Finset Pt :=
  (((inc4 u).filter (fun e => decide (Fwd V F u e))).map (fun e => other e u)).toFinset

-- The alternating layers: layer `k` holds the points reachable in at most `k` steps from
-- a deficient black point.
--
def layer (V : Finset Pt) (F : Finset Edge) : ℕ → Finset Pt
  | 0 => V.filter (fun z => Black z ∧ deg F z < 2)
  | k + 1 =>
    let L := layer V F k
    L ∪ L.biUnion (nbr V F)

-- A backward step from `v` along `e` into `L`: the reverse of a forward step from
-- `other e v ∈ L`.
--
def Bwd (V : Finset Pt) (F : Finset Edge) (L : Finset Pt) (v : Pt) (e : Edge) : Prop :=
  IsEdge V e ∧ other e v ∈ L ∧ (Black v → e ∈ F) ∧ (¬ Black v → e ∉ F)

instance (V : Finset Pt) (F : Finset Edge) (L : Finset Pt) (v : Pt) (e : Edge) :
    Decidable (Bwd V F L v e) := by
  unfold Bwd; infer_instance

-- The first backward step from `v` into `L`, if any.
--
def pred (V : Finset Pt) (F : Finset Edge) (L : Finset Pt) (v : Pt) : Option Edge :=
  (inc4 v).find? (fun e => decide (Bwd V F L v e))

-- The layers below index `k`, top first: `[layer (k-1), ..., layer 0]` (specification).
--
def layersBelow (V : Finset Pt) (F : Finset Edge) : ℕ → List (Finset Pt)
  | 0 => []
  | k + 1 => layer V F k :: layersBelow V F k

-- The same layers computed bottom up, each from the previous one only once:
-- `layerAcc V F k = [layer k, layer (k-1), ..., layer 0]` (`layerAcc_eq`).
--
def layerAcc (V : Finset Pt) (F : Finset Edge) : ℕ → List (Finset Pt)
  | 0 => [V.filter (fun z => Black z ∧ deg F z < 2)]
  | k + 1 =>
    match layerAcc V F k with
    | [] => []
    | L :: Ls => (L ∪ L.biUnion (nbr V F)) :: L :: Ls

-- Walk back from `v` down the layers `Ls` (top first), flipping the crossed edges of `F`.
-- `F0` is the edge set the layers were built from. One list entry is consumed per step.
--
def walk (V : Finset Pt) (F0 : Finset Edge) :
    List (Finset Pt) → Pt → Finset Edge → Finset Edge
  | [], _, F => F
  | L :: Ls, v, F =>
    if v ∈ L then walk V F0 Ls v F
    else
      match pred V F0 L v with
      | none => F
      | some e => walk V F0 Ls (other e v) (if Black v then F.erase e else insert e F)

-- A computable choice of an element of a finite set of points (the lexicographic least).
--
def pick (S : Finset Pt) : Option Pt :=
  match (S.image toLex).min with
  | ⊤ => none
  | (x : Lex (ℤ × ℤ)) => some (ofLex x)

-- One augmentation: `none` when no deficient white point is reachable.
--
def augStep (V : Finset Pt) (F : Finset Edge) : Option (Finset Edge) :=
  match layerAcc V F V.card with
  | [] => none
  | L :: Ls =>
    match pick (L.filter (fun w => ¬ Black w ∧ deg F w < 2)) with
    | none => none
    | some w => some (walk V F Ls w F)

-- Augment at most `n` times.
--
def augLoop (V : Finset Pt) : ℕ → Finset Edge → Finset Edge
  | 0, F => F
  | n + 1, F =>
    match augStep V F with
    | none => F
    | some F' => augLoop V n F'

/-! ## Basic lemmas -/

lemma mem_inc4 {e : Edge} {z : Pt} : e ∈ inc4 z ↔ e.p = z ∨ e.q = z := by
  obtain ⟨d, p1, p2⟩ := e
  obtain ⟨z1, z2⟩ := z
  cases d <;> simp [inc4, eR, eL, eU, eD, Edge.q] <;> constructor <;> intro h <;> omega

lemma black_q (e : Edge) : Black e.q ↔ ¬ Black e.p := by
  obtain ⟨d, p1, p2⟩ := e
  cases d <;> simp [Black, Edge.q] <;> omega

-- The ends of `e` are `v` and `other e v`, of opposite colours.
--
lemma ends_iff {e : Edge} {v : Pt} (hv : e.p = v ∨ e.q = v) (z : Pt) :
    (e.p = z ∨ e.q = z) ↔ (z = v ∨ z = other e v) := by
  unfold other
  by_cases h : e.p = v
  · rw [ite_eq_left h]; subst h; constructor <;> rintro (h | h) <;> simp [h]
  · rw [ite_eq_right h]
    have hq : e.q = v := hv.resolve_left h
    subst hq; constructor <;> rintro (h | h) <;> simp [h]

lemma other_other {e : Edge} {v : Pt} (hv : e.p = v ∨ e.q = v) : other e (other e v) = v := by
  have hne := e.p_ne_q
  unfold other
  by_cases h : e.p = v
  · subst h; simp [hne]
  · have hq : e.q = v := hv.resolve_left h
    subst hq; simp [h]

lemma other_black {e : Edge} {v : Pt} (hv : e.p = v ∨ e.q = v) :
    Black (other e v) ↔ ¬ Black v := by
  unfold other
  by_cases h : e.p = v
  · rw [ite_eq_left h, ← h, black_q]
  · rw [ite_eq_right h, ← hv.resolve_left h, black_q]; tauto

lemma inside_end {V : Finset Pt} {e : Edge} (he : IsEdge V e) {z : Pt} (hz : e.p = z ∨ e.q = z) :
    z ∈ V := by
  rcases hz with h | h <;> rw [← h]
  exacts [he.1, he.2]

lemma mem_nbr {V : Finset Pt} {F : Finset Edge} {u v : Pt} :
    v ∈ nbr V F u ↔ ∃ e, (e.p = u ∨ e.q = u) ∧ Fwd V F u e ∧ other e u = v := by
  simp [nbr, mem_inc4, and_assoc]

lemma layer_succ (V : Finset Pt) (F : Finset Edge) (k : ℕ) :
    layer V F (k + 1) = layer V F k ∪ (layer V F k).biUnion (nbr V F) := rfl

lemma layer_sub_succ {V : Finset Pt} {F : Finset Edge} {k : ℕ} :
    layer V F k ⊆ layer V F (k + 1) := by
  rw [layer_succ]; exact subset_union_left

lemma layer_mono {V : Finset Pt} {F : Finset Edge} {k j : ℕ} (h : k ≤ j) :
    layer V F k ⊆ layer V F j := by
  induction h with
  | refl => exact Subset.refl _
  | step _ ih => exact ih.trans layer_sub_succ

lemma nbr_sub {V : Finset Pt} {F : Finset Edge} (u : Pt) : nbr V F u ⊆ V := by
  intro v hv
  obtain ⟨e, -, hf, rfl⟩ := mem_nbr.1 hv
  exact inside_end hf.1 other_inc

lemma layer_sub {V : Finset Pt} {F : Finset Edge} (k : ℕ) : layer V F k ⊆ V := by
  induction k with
  | zero => exact filter_subset _ _
  | succ k ih =>
    rw [layer_succ]
    exact union_subset ih (biUnion_subset.2 fun u _ => nbr_sub u)

lemma layerAcc_eq (V : Finset Pt) (F : Finset Edge) (k : ℕ) :
    layerAcc V F k = layer V F k :: layersBelow V F k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [layerAcc, ih]; rfl

lemma mem_layer_succ {V : Finset Pt} {F : Finset Edge} {k : ℕ} {v : Pt} :
    v ∈ layer V F (k + 1) ↔ v ∈ layer V F k ∨ ∃ u ∈ layer V F k, v ∈ nbr V F u := by
  rw [layer_succ, mem_union, mem_biUnion]

/-! ## The layers stop growing by index `|V|` -/

lemma layer_stable {V : Finset Pt} {F : Finset Edge} {k : ℕ}
    (h : layer V F (k + 1) = layer V F k) : ∀ j, k ≤ j → layer V F j = layer V F k := by
  intro j hj
  induction hj with
  | refl => rfl
  | step _ ih => rw [layer_succ, ih, ← layer_succ, h]

lemma layer_exists_fix (V : Finset Pt) (F : Finset Edge) :
    ∃ k ≤ V.card, layer V F (k + 1) = layer V F k := by
  by_contra hn
  push Not at hn
  have hgrow : ∀ n, n ≤ V.card + 1 → n ≤ (layer V F n).card := by
    intro n
    induction n with
    | zero => intro _; exact Nat.zero_le _
    | succ n ih =>
      intro hn1
      have hss : layer V F n ⊂ layer V F (n + 1) :=
        ssubset_of_subset_of_ne layer_sub_succ (hn n (by omega)).symm
      have := card_lt_card hss
      have := ih (by omega)
      omega
  have h1 := hgrow (V.card + 1) le_rfl
  have h2 := card_le_card (layer_sub (V := V) (F := F) (V.card + 1))
  omega

-- The BFS bound: `|V|` rounds already give the closed reachable set.
--
theorem layer_fix (V : Finset Pt) (F : Finset Edge) (m : ℕ) :
    layer V F (V.card + m) = layer V F V.card := by
  obtain ⟨k, hk, h⟩ := layer_exists_fix V F
  rw [layer_stable h _ (by omega), layer_stable h _ hk]

theorem layer_closed {V : Finset Pt} {F : Finset Edge} {u v : Pt}
    (hu : u ∈ layer V F V.card) (hv : v ∈ nbr V F u) : v ∈ layer V F V.card := by
  rw [← layer_fix V F 1]
  exact mem_layer_succ.2 (Or.inr ⟨u, hu, hv⟩)

/-! ## Degrees -/

lemma deg_empty (z : Pt) : deg ∅ z = 0 := by
  simp [deg, ind]

lemma deg_eq_card (F : Finset Edge) (z : Pt) :
    deg F z = (F.filter (fun e => e.p = z ∨ e.q = z)).card := by
  classical
  induction F using Finset.induction_on with
  | empty => simp [deg_empty]
  | insert e F he ih =>
    rw [deg_insert he, ih, filter_insert]
    split_ifs with h
    · rw [card_insert_of_notMem (fun h' => he (mem_filter.1 h').1)]
    · rfl

lemma deg_erase_end {F : Finset Edge} {e : Edge} (he : e ∈ F) {z : Pt} (hz : e.p = z ∨ e.q = z) :
    deg (F.erase e) z + 1 = deg F z := by
  have := deg_erase he z; rwa [ite_eq_left hz] at this

lemma deg_erase_off {F : Finset Edge} {e : Edge} (he : e ∈ F) {z : Pt} (hz : ¬ (e.p = z ∨ e.q = z)) :
    deg (F.erase e) z = deg F z := by
  have := deg_erase he z; rwa [ite_eq_right hz, add_zero] at this

lemma deg_insert_end {F : Finset Edge} {e : Edge} (he : e ∉ F) {z : Pt} (hz : e.p = z ∨ e.q = z) :
    deg (insert e F) z = deg F z + 1 := by
  rw [deg_insert he, ite_eq_left hz]

lemma deg_insert_off {F : Finset Edge} {e : Edge} (he : e ∉ F) {z : Pt} (hz : ¬ (e.p = z ∨ e.q = z)) :
    deg (insert e F) z = deg F z := by
  rw [deg_insert he, ite_eq_right hz, add_zero]

-- Degree sum over a set `S` containing no edge: each edge touching `S` is counted once.
--
lemma sum_deg {S : Finset Pt} (hS : ∀ e : Edge, ¬ (e.p ∈ S ∧ e.q ∈ S)) (F : Finset Edge) :
    ∑ z ∈ S, deg F z = (F.filter (fun e => e.p ∈ S ∨ e.q ∈ S)).card := by
  classical
  simp_rw [deg_eq_card]
  rw [← card_biUnion]
  · congr 1
    ext e
    simp only [mem_biUnion, mem_filter]
    constructor
    · rintro ⟨z, hz, he, h | h⟩
      · exact ⟨he, Or.inl (h ▸ hz)⟩
      · exact ⟨he, Or.inr (h ▸ hz)⟩
    · rintro ⟨he, h | h⟩
      · exact ⟨_, h, he, Or.inl rfl⟩
      · exact ⟨_, h, he, Or.inr rfl⟩
  · intro x hx y hy hxy
    simp only [Function.onFun]
    rw [disjoint_left]
    intro e h1 h2
    simp only [mem_filter] at h1 h2
    apply hS e
    rcases h1.2 with h1 | h1 <;> rcases h2.2 with h2 | h2
    · exact absurd (h1.symm.trans h2) hxy
    · exact ⟨h1 ▸ hx, h2 ▸ hy⟩
    · exact ⟨h2 ▸ hy, h1 ▸ hx⟩
    · exact absurd (h1.symm.trans h2) hxy

lemma no_edge_black {S : Finset Pt} (hS : ∀ z ∈ S, Black z) (e : Edge) :
    ¬ (e.p ∈ S ∧ e.q ∈ S) := fun h => (black_q e).1 (hS _ h.2) (hS _ h.1)

lemma no_edge_white {S : Finset Pt} (hS : ∀ z ∈ S, ¬ Black z) (e : Edge) :
    ¬ (e.p ∈ S ∧ e.q ∈ S) := fun h => hS _ h.2 ((black_q e).2 (hS _ h.1))

/-! ## The walk -/

-- The invariant of the algorithm: grid edges only, all degrees at most 2.
--
def Good (V : Finset Pt) (F : Finset Edge) : Prop := Inside V F ∧ ∀ z, deg F z ≤ 2

lemma good_empty (V : Finset Pt) : Good V ∅ :=
  ⟨fun e he => absurd he (Finset.notMem_empty e), fun z => by rw [deg_empty]; omega⟩

-- The walk invariant at layer index `k`, current point `v`, current edge set `F`:
-- `v` still needs one more edge (white) or one fewer edge (black); every other point
-- of layer `k` keeps its old degree; every changed edge has an end outside layer `k`.
--
def WInv (V : Finset Pt) (F0 : Finset Edge) (k : ℕ) (v : Pt) (F : Finset Edge) : Prop :=
  v ∈ layer V F0 k ∧ Inside V F ∧ (∀ z, z ≠ v → deg F z ≤ 2) ∧
  (¬ Black v → deg F v < 2 ∧ F.card = F0.card) ∧
  (Black v → deg F v = deg F0 v + 1 ∧ F.card = F0.card + 1) ∧
  (∀ z ∈ layer V F0 k, z ≠ v → deg F z = deg F0 z) ∧
  (∀ e, (e ∈ F ↔ e ∈ F0) ∨ e.p ∉ layer V F0 k ∨ e.q ∉ layer V F0 k)

lemma pred_some {V : Finset Pt} {F : Finset Edge} {L : Finset Pt} {v : Pt} {e : Edge}
    (h : pred V F L v = some e) : (e.p = v ∨ e.q = v) ∧ Bwd V F L v e := by
  unfold pred at h
  have h2 := List.find?_some h
  exact ⟨mem_inc4.1 (List.mem_of_find?_eq_some h), by simpa using h2⟩

-- A point that enters at layer `k + 1` has a backward step into layer `k`.
--
lemma pred_ne_none {V : Finset Pt} {F : Finset Edge} {k : ℕ} {v : Pt}
    (hv : v ∈ layer V F (k + 1)) (hvk : v ∉ layer V F k) : pred V F (layer V F k) v ≠ none := by
  rcases mem_layer_succ.1 hv with h | ⟨u, hu, huv⟩
  · exact absurd h hvk
  obtain ⟨e, heu, ⟨hE, hb, hw⟩, rfl⟩ := mem_nbr.1 huv
  have hev : e.p = other e u ∨ e.q = other e u := other_inc
  intro hn
  unfold pred at hn
  have := List.find?_eq_none.1 hn e (mem_inc4.2 hev)
  apply this
  rw [decide_eq_true_iff]
  have hc := other_black heu
  refine ⟨hE, by rw [other_other heu]; exact hu, fun h => ?_, fun h => ?_⟩
  · by_contra h'; exact (hc.1 h) (by_contra fun h'' => h' (hw h''))
  · exact hb (by by_contra h''; exact h (hc.2 h''))

theorem walk_spec {V : Finset Pt} {F0 : Finset Edge} (hF0 : Good V F0) (k : ℕ) :
    ∀ v F, WInv V F0 k v F →
      Good V (walk V F0 (layersBelow V F0 k) v F) ∧
        (walk V F0 (layersBelow V F0 k) v F).card = F0.card + 1 := by
  induction k with
  | zero =>
    rintro v F ⟨hv, hin, hle, -, hb, -, -⟩
    show Good V F ∧ F.card = F0.card + 1
    simp only [layer, mem_filter] at hv
    obtain ⟨-, hvb, hvd⟩ := hv
    obtain ⟨hd, hc⟩ := hb hvb
    refine ⟨⟨hin, fun z => ?_⟩, hc⟩
    by_cases hz : z = v
    · subst hz; omega
    · exact hle z hz
  | succ k ih =>
    rintro v F ⟨hv, hin, hle, hw, hb, hdeg, hfl⟩
    have hsub : layer V F0 k ⊆ layer V F0 (k + 1) := layer_sub_succ
    have hfl' : ∀ e, (e ∈ F ↔ e ∈ F0) ∨ e.p ∉ layer V F0 k ∨ e.q ∉ layer V F0 k := by
      intro e
      rcases hfl e with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl fun h' => h (hsub h'))
      · exact Or.inr (Or.inr fun h' => h (hsub h'))
    by_cases hvk : v ∈ layer V F0 k
    · rw [layersBelow, walk, ite_eq_left hvk]
      exact ih v F ⟨hvk, hin, hle, hw, hb, fun z hz => hdeg z (hsub hz), hfl'⟩
    rw [layersBelow, walk, ite_eq_right hvk]
    rcases hp : pred V F0 (layer V F0 k) v with _ | e
    · exact absurd hp (pred_ne_none hv hvk)
    simp only
    obtain ⟨hev, hE, hu, hbk, hwk⟩ := pred_some hp
    have hends := ends_iff hev
    have huv : other e v ≠ v := other_ne hev
    have hcol := other_black hev
    have hu' : other e v ∈ layer V F0 (k + 1) := hsub hu
    have heF : e ∈ F ↔ e ∈ F0 := by
      rcases hfl e with h | h | h
      · exact h
      · exfalso; apply h
        rcases (hends e.p).1 (Or.inl rfl) with h' | h' <;> rw [h']
        exacts [hv, hu']
      · exfalso; apply h
        rcases (hends e.q).1 (Or.inr rfl) with h' | h' <;> rw [h']
        exacts [hv, hu']
    -- Points other than `v` and `other e v` keep their degree.
    --
    have hoff : ∀ z, z ≠ v → z ≠ other e v → ¬ (e.p = z ∨ e.q = z) := by
      intro z h1 h2 h
      rcases (hends z).1 h with h | h
      exacts [h1 h, h2 h]
    have hfl2 : ∀ G : Finset Edge, (∀ f, f ≠ e → (f ∈ G ↔ f ∈ F)) →
        ∀ f, (f ∈ G ↔ f ∈ F0) ∨ f.p ∉ layer V F0 k ∨ f.q ∉ layer V F0 k := by
      intro G hG f
      by_cases hfe : f = e
      · subst hfe
        rcases hev with h | h
        · exact Or.inr (Or.inl (h ▸ hvk))
        · exact Or.inr (Or.inr (h ▸ hvk))
      · rcases hfl' f with h | h
        · exact Or.inl ((hG f hfe).trans h)
        · exact Or.inr h
    by_cases hvb : Black v
    · -- Black `v`: erase the `F0`-edge `e`, moving to the white point `other e v`.
      --
      rw [ite_eq_left hvb]
      have heF' : e ∈ F := heF.2 (hbk hvb)
      obtain ⟨hdv, hc⟩ := hb hvb
      have hub : ¬ Black (other e v) := fun h => hcol.1 h hvb
      apply ih
      refine ⟨hu, hin.mono (erase_subset _ _), ?_, ?_, ?_, ?_, ?_⟩
      · intro z hz
        by_cases hzv : z = v
        · subst hzv
          have := deg_erase_end heF' hev
          have := hF0.2 z
          omega
        · rw [deg_erase_off heF' (hoff z hzv hz)]; exact hle z hzv
      · intro _
        have h1 := deg_erase_end heF' ((hends _).2 (Or.inr rfl))
        have h2 := hdeg _ hu' huv
        have h3 := hF0.2 (other e v)
        have h4 := card_erase_of_mem heF'
        omega
      · intro h; exact absurd h hub
      · intro z hz hzu
        have hzv : z ≠ v := fun h => hvk (h ▸ hz)
        rw [deg_erase_off heF' (hoff z hzv hzu)]
        exact hdeg z (hsub hz) hzv
      · apply hfl2
        intro f hf
        rw [mem_erase]
        exact ⟨fun h => h.2, fun h => ⟨hf, h⟩⟩
    · -- White `v`: insert the non-`F0` edge `e`, moving to the black point `other e v`.
      --
      rw [ite_eq_right hvb]
      have heF' : e ∉ F := fun h => hwk hvb (heF.1 h)
      obtain ⟨hdv, hc⟩ := hw hvb
      have hub : Black (other e v) := hcol.2 hvb
      apply ih
      refine ⟨hu, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro f hf
        rcases mem_insert.1 hf with h | h
        · subst h; exact hE
        · exact hin f h
      · intro z hz
        by_cases hzv : z = v
        · subst hzv
          rw [deg_insert_end heF' hev]
          omega
        · rw [deg_insert_off heF' (hoff z hzv hz)]; exact hle z hzv
      · intro h; exact absurd hub h
      · intro _
        rw [deg_insert_end heF' ((hends _).2 (Or.inr rfl)), hdeg _ hu' huv,
          card_insert_of_notMem heF', hc]
        exact ⟨rfl, rfl⟩
      · intro z hz hzu
        have hzv : z ≠ v := fun h => hvk (h ▸ hz)
        rw [deg_insert_off heF' (hoff z hzv hzu)]
        exact hdeg z (hsub hz) hzv
      · apply hfl2
        intro f hf
        rw [mem_insert]
        exact ⟨fun h => h.resolve_left hf, fun h => Or.inr h⟩

/-! ## One augmentation -/

lemma pick_some {S : Finset Pt} {p : Pt} (h : pick S = some p) : p ∈ S := by
  unfold pick at h
  split at h
  · exact absurd h (by simp)
  · rename_i x hx
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨a, ha, rfl⟩ := mem_image.1 (mem_of_min hx)
    simpa using ha

lemma pick_none {S : Finset Pt} (h : pick S = none) : S = ∅ := by
  unfold pick at h
  split at h
  · rename_i hx
    exact image_eq_empty.1 (Finset.min_eq_top.1 hx)
  · exact absurd h (by simp)

theorem augStep_some {V : Finset Pt} {F F' : Finset Edge} (hF : Good V F)
    (h : augStep V F = some F') : Good V F' ∧ F'.card = F.card + 1 := by
  unfold augStep at h
  rw [layerAcc_eq] at h
  simp only at h
  split at h
  · exact absurd h (by simp)
  · rename_i w hw
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨hwL, hwb, hwd⟩ := mem_filter.1 (pick_some hw)
    exact walk_spec hF _ w F
      ⟨hwL, hF.1, fun z _ => hF.2 z, fun _ => ⟨hwd, rfl⟩, fun h => absurd h hwb,
        fun _ _ _ => rfl, fun _ => Or.inl Iff.rfl⟩

-- When stuck, no reachable white point is deficient.
--
lemma augStep_none {V : Finset Pt} {F : Finset Edge} (h : augStep V F = none)
    {w : Pt} (hw : w ∈ layer V F V.card) (hwb : ¬ Black w) : ¬ deg F w < 2 := by
  unfold augStep at h
  rw [layerAcc_eq] at h
  simp only at h
  split at h
  · rename_i hp
    have := pick_none hp
    intro hd
    have hm : w ∈ (layer V F V.card).filter (fun w => ¬ Black w ∧ deg F w < 2) :=
      mem_filter.2 ⟨hw, hwb, hd⟩
    rw [this] at hm
    exact absurd hm (Finset.notMem_empty w)
  · exact absurd h (by simp)

/-! ## Counting: a stuck state is full whenever a 2-factor exists -/

-- Within a set where every degree is at most 2, a degree sum of at least `2 |S|`
-- forces every degree to be 2.
--
lemma all_two {S : Finset Pt} {f : Pt → ℕ} (hle : ∀ z ∈ S, f z ≤ 2)
    (hsum : 2 * S.card ≤ ∑ z ∈ S, f z) : ∀ z ∈ S, f z = 2 := by
  have hle' : ∑ z ∈ S, f z ≤ ∑ z ∈ S, 2 := sum_le_sum hle
  have heq : ∑ z ∈ S, f z = ∑ z ∈ S, (fun _ => 2) z := by
    simp only [sum_const, smul_eq_mul] at hle' ⊢
    omega
  exact (sum_eq_sum_iff_of_le hle).1 heq

-- Every edge of an `Inside` set has exactly one black end inside `V`, so the black (and
-- the white) degree sums both equal `|F|`.
--
lemma sum_deg_black {V : Finset Pt} {F : Finset Edge} (hF : Inside V F) :
    ∑ z ∈ V.filter Black, deg F z = F.card := by
  rw [sum_deg (no_edge_black fun z hz => (mem_filter.1 hz).2), filter_true_of_mem]
  intro e he
  by_cases h : Black e.p
  · exact Or.inl (mem_filter.2 ⟨(hF e he).1, h⟩)
  · exact Or.inr (mem_filter.2 ⟨(hF e he).2, (black_q e).2 h⟩)

lemma sum_deg_white {V : Finset Pt} {F : Finset Edge} (hF : Inside V F) :
    ∑ z ∈ V.filter (fun z => ¬ Black z), deg F z = F.card := by
  rw [sum_deg (no_edge_white fun z hz => (mem_filter.1 hz).2), filter_true_of_mem]
  intro e he
  by_cases h : Black e.p
  · exact Or.inr (mem_filter.2 ⟨(hF e he).2, fun h' => (black_q e).1 h' h⟩)
  · exact Or.inl (mem_filter.2 ⟨(hF e he).1, h⟩)

-- The counting argument. `R` is the reachable set, `SB`/`SW` its black/white parts.
-- Every white point of `R` is full and its `F`-edges go to `SB`; every grid edge from
-- `SB` to a white point outside `SW` is in `F`. Comparing with a 2-factor `G` gives
-- `2 |SB| ≤ Σ_{SB} deg F`, so `SB` (which holds every deficient black point) is full.
-- Then the colour balance of degree sums makes every white point full too.
--
theorem stuck_full {V : Finset Pt} {F G : Finset Edge} (hF : Good V F)
    (hst : augStep V F = none) (hG : Deg2 V G) : ∀ z ∈ V, deg F z = 2 := by
  classical
  set R := layer V F V.card with hR
  set SB := R.filter Black
  set SW := R.filter (fun z => ¬ Black z)
  have hRV : R ⊆ V := layer_sub _
  have hSBb : ∀ z ∈ SB, Black z := fun z hz => (mem_filter.1 hz).2
  have hSWw : ∀ z ∈ SW, ¬ Black z := fun z hz => (mem_filter.1 hz).2
  have hSWfull : ∀ z ∈ SW, deg F z = 2 := by
    intro z hz
    obtain ⟨hzR, hzb⟩ := mem_filter.1 hz
    have := augStep_none hst hzR hzb
    have := hF.2 z
    omega
  have hSWG : ∀ z ∈ SW, deg G z = 2 := fun z hz => hG.2 z (hRV (mem_filter.1 hz).1)
  have hSBG : ∀ z ∈ SB, deg G z = 2 := fun z hz => hG.2 z (hRV (mem_filter.1 hz).1)
  -- Touching a set: one end in it.
  --
  let T : Finset Pt → Edge → Prop := fun S e => e.p ∈ S ∨ e.q ∈ S
  have hsumB : ∀ H : Finset Edge, ∑ z ∈ SB, deg H z = (H.filter (T SB)).card :=
    fun H => sum_deg (no_edge_black hSBb) H
  have hsumW : ∀ H : Finset Edge, ∑ z ∈ SW, deg H z = (H.filter (T SW)).card :=
    fun H => sum_deg (no_edge_white hSWw) H
  -- An edge touching `SB` (resp. `SW`) at its end `b`.
  --
  have hend : ∀ (S : Finset Pt) e, T S e → ∃ b ∈ S, e.p = b ∨ e.q = b := by
    rintro S e (h | h)
    · exact ⟨_, h, Or.inl rfl⟩
    · exact ⟨_, h, Or.inr rfl⟩
  have htouch : ∀ (S : Finset Pt) e z, z ∈ S → (e.p = z ∨ e.q = z) → T S e := by
    rintro S e z hz (h | h)
    · exact Or.inl (h ▸ hz)
    · exact Or.inr (h ▸ hz)
  -- Claim 2: an `F`-edge touching `SW` also touches `SB`.
  --
  have hc2 : ∀ e ∈ F, T SW e → T SB e := by
    intro e he hT
    obtain ⟨w, hw, hwe⟩ := hend SW e hT
    obtain ⟨hwR, hwb⟩ := mem_filter.1 hw
    have hfw : Fwd V F w e := ⟨hF.1 e he, fun h => absurd h hwb, fun _ => he⟩
    have hbR : other e w ∈ R := layer_closed hwR (mem_nbr.2 ⟨e, hwe, hfw, rfl⟩)
    have hbb : Black (other e w) := (other_black hwe).2 hwb
    exact htouch SB e _ (mem_filter.2 ⟨hbR, hbb⟩) ((ends_iff hwe _).2 (Or.inr rfl))
  -- Claim 1: a `G`-edge touching `SB` touches `SW` or is an `F`-edge.
  --
  have hc1 : ∀ e ∈ G, T SB e → T SW e ∨ e ∈ F := by
    intro e he hT
    by_cases heF : e ∈ F
    · exact Or.inr heF
    left
    obtain ⟨b, hb, hbe⟩ := hend SB e hT
    obtain ⟨hbR, hbb⟩ := mem_filter.1 hb
    have hfb : Fwd V F b e := ⟨hG.1 e he, fun _ => heF, fun h => absurd hbb h⟩
    have hwR : other e b ∈ R := layer_closed hbR (mem_nbr.2 ⟨e, hbe, hfb, rfl⟩)
    have hww : ¬ Black (other e b) := fun h => (other_black hbe).1 h hbb
    exact htouch SW e _ (mem_filter.2 ⟨hwR, hww⟩) ((ends_iff hbe _).2 (Or.inr rfl))
  -- The edges of `F` touching `SB` but not `SW`.
  --
  set Y := (F.filter (T SB)).filter (fun e => ¬ T SW e)
  have hAF : (F.filter (T SB)).card = 2 * SW.card + Y.card := by
    rw [← card_filter_add_card_filter_not (s := F.filter (T SB)) (T SW)]
    have : (F.filter (T SB)).filter (T SW) = F.filter (T SW) := by
      ext e
      simp only [mem_filter]
      exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hc2 e h.1 h.2⟩, h.2⟩⟩
    rw [this, ← hsumW, sum_congr rfl hSWfull, sum_const, smul_eq_mul, mul_comm]
  have hAG : 2 * SB.card ≤ 2 * SW.card + Y.card := by
    have h1 : (G.filter (T SB)).card = 2 * SB.card := by
      rw [← hsumB, sum_congr rfl hSBG, sum_const, smul_eq_mul, mul_comm]
    have h2 : (G.filter (T SW)).card = 2 * SW.card := by
      rw [← hsumW, sum_congr rfl hSWG, sum_const, smul_eq_mul, mul_comm]
    have hsub : G.filter (T SB) ⊆ G.filter (T SW) ∪ Y := by
      intro e he
      obtain ⟨heG, hT⟩ := mem_filter.1 he
      rw [mem_union]
      rcases hc1 e heG hT with h | h
      · exact Or.inl (mem_filter.2 ⟨heG, h⟩)
      · by_cases hW : T SW e
        · exact Or.inl (mem_filter.2 ⟨heG, hW⟩)
        · exact Or.inr (mem_filter.2 ⟨mem_filter.2 ⟨h, hT⟩, hW⟩)
    have := (card_le_card hsub).trans (card_union_le _ _)
    omega
  have hSBfull : ∀ z ∈ SB, deg F z = 2 :=
    all_two (fun z _ => hF.2 z) (by rw [hsumB, hAF]; exact hAG)
  -- Every black point is full: a deficient one would lie in layer 0, inside `SB`.
  --
  have hBfull : ∀ z ∈ V.filter Black, deg F z = 2 := by
    intro z hz
    obtain ⟨hzV, hzb⟩ := mem_filter.1 hz
    by_contra hne
    have hd : deg F z < 2 := by have := hF.2 z; omega
    have h0 : z ∈ layer V F 0 := mem_filter.2 ⟨hzV, hzb, hd⟩
    have hzR : z ∈ R := layer_mono (Nat.zero_le _) h0
    exact hne (hSBfull z (mem_filter.2 ⟨hzR, hzb⟩))
  -- Colour balance: `|F| = 2 |VB|` and `2 |VB| = |G| = 2 |VW|`.
  --
  have hFB := sum_deg_black hF.1
  have hFW := sum_deg_white hF.1
  have hGB := sum_deg_black hG.1
  have hGW := sum_deg_white hG.1
  rw [sum_congr rfl hBfull, sum_const, smul_eq_mul] at hFB
  rw [sum_congr rfl (fun z hz => hG.2 z (mem_filter.1 hz).1), sum_const, smul_eq_mul] at hGB hGW
  have hWfull : ∀ z ∈ V.filter (fun z => ¬ Black z), deg F z = 2 :=
    all_two (fun z _ => hF.2 z) (by rw [hFW]; omega)
  intro z hz
  by_cases hzb : Black z
  · exact hBfull z (mem_filter.2 ⟨hz, hzb⟩)
  · exact hWfull z (mem_filter.2 ⟨hz, hzb⟩)

/-! ## The augmentation loop and the main theorems -/

-- A good edge set has at most `|V|` edges (`|F| ≤ 2 |VB|` and `|F| ≤ 2 |VW|`).
--
lemma card_le_of_good {V : Finset Pt} {F : Finset Edge} (hF : Good V F) : F.card ≤ V.card := by
  have hB : ∑ z ∈ V.filter Black, deg F z ≤ ∑ z ∈ V.filter Black, 2 :=
    sum_le_sum fun z _ => hF.2 z
  have hW : ∑ z ∈ V.filter (fun z => ¬ Black z), deg F z ≤
      ∑ z ∈ V.filter (fun z => ¬ Black z), 2 :=
    sum_le_sum fun z _ => hF.2 z
  rw [sum_deg_black hF.1, sum_const, smul_eq_mul] at hB
  rw [sum_deg_white hF.1, sum_const, smul_eq_mul] at hW
  have := card_filter_add_card_filter_not (s := V) Black
  omega

-- Fuel bound: with `|F| + n > |V|` the loop ends in a stuck good state. Each round adds
-- one edge and a good set has at most `|V|` edges, so at most `|V|` rounds augment.
--
theorem augLoop_spec {V : Finset Pt} :
    ∀ n F, Good V F → V.card < F.card + n →
      Good V (augLoop V n F) ∧ augStep V (augLoop V n F) = none := by
  intro n
  induction n with
  | zero =>
    intro F hF hn
    have := card_le_of_good hF
    omega
  | succ n ih =>
    intro F hF hn
    rcases h : augStep V F with _ | F'
    · simp only [augLoop, h, and_true]
      exact hF
    · simp only [augLoop, h]
      obtain ⟨hF', hc⟩ := augStep_some hF h
      exact ih F' hF' (by omega)

-- Extra fuel changes nothing once the loop is stuck, so `augLoop V (|V| + 1) ∅` is the
-- result of the unbounded loop.
--
theorem augLoop_add {V : Finset Pt} :
    ∀ n m F, augStep V (augLoop V n F) = none → augLoop V (n + m) F = augLoop V n F := by
  intro n
  induction n with
  | zero =>
    intro m F h
    cases m with
    | zero => rfl
    | succ m =>
      simp only [augLoop] at h
      simp only [augLoop, h]
  | succ n ih =>
    intro m F h
    rw [Nat.add_right_comm]
    rcases hs : augStep V F with _ | F'
    · simp only [augLoop, hs]
    · simp only [augLoop, hs] at h ⊢
      exact ih m F' h

lemma augLoop_final (V : Finset Pt) :
    Good V (augLoop V (V.card + 1) ∅) ∧ augStep V (augLoop V (V.card + 1) ∅) = none :=
  augLoop_spec _ _ (good_empty V) (by simp)

end TF

open TF

-- The algorithm: augment from the empty set (`|V| + 1` rounds suffice), then check.
--
def twoFactor (V : Finset Pt) : Option (Finset Edge) :=
  let F := augLoop V (V.card + 1) ∅
  if ∀ z ∈ V, deg F z = 2 then some F else none

theorem twoFactor_some {V : Finset Pt} {F : Finset Edge} (h : twoFactor V = some F) :
    Deg2 V F := by
  dsimp only [twoFactor] at h
  split_ifs at h with hall
  simp only [Option.some.injEq] at h
  subst h
  exact ⟨(augLoop_final V).1.1, hall⟩

theorem twoFactor_none {V : Finset Pt} (h : twoFactor V = none) : ¬ ∃ F, Deg2 V F := by
  dsimp only [twoFactor] at h
  split_ifs at h with hall
  rintro ⟨G, hG⟩
  exact hall (stuck_full (augLoop_final V).1 (augLoop_final V).2 hG)

-- Both directions together.
--
theorem twoFactor_isSome_iff (V : Finset Pt) : (twoFactor V).isSome ↔ ∃ F, Deg2 V F := by
  constructor
  · intro h
    obtain ⟨F, hF⟩ := Option.isSome_iff_exists.1 h
    exact ⟨F, twoFactor_some hF⟩
  · intro h
    by_contra hn
    exact twoFactor_none (Option.not_isSome_iff_eq_none.1 hn) h

end SolidGridHam
