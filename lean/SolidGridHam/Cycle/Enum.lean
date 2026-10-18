/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import SolidGridHam.Cycle.CrPath
public import SolidGridHam.Cycle.Comp
public import SolidGridHam.Cycle.Phase2
public import SolidGridHam.Algorithm

@[expose] public section

/-!
# Deciding strips and links

Computable versions of the strip and link predicates, each with its exact specification.

* `stripLen V F c s`: the unique `n` such that the strip from `c` in direction `s` has its
  pattern in `F` with all cells in `V` (`stripLen_eq_some`). A scan from `c` stops at the
  first cell whose front side ends the pattern; at most `|V|` cells are scanned.
* `allStrips V F`: all such strips (`mem_allStrips`), at most `4 |V|` of them.
* `connB`, `validB`, `cr2B`: decide `Conn`, `ValidStrip` and `CR2` (`connB_iff`,
  `validB_iff`, `cr2B_iff`).
-/

namespace SolidGridHam

open Finset

instance : DecidableEq StripSpec := fun a b =>
  decidable_of_iff (a.c = b.c ∧ a.s = b.s ∧ a.n = b.n) (by
    cases a; cases b; simp)

section enum

variable (V : Finset Pt) (F : Finset Edge) (c : Pt) (s : Side)

-- The lateral sides of the `j`-th cell match the strip pattern.
--
def LatOK (j : ℕ) : Prop :=
  (lat1 (cellJ c s j) s ∈ F ↔ j % 2 = 1) ∧ (lat2 (cellJ c s j) s ∈ F ↔ j % 2 = 1)

instance (j : ℕ) : Decidable (LatOK F c s j) := by unfold LatOK; infer_instance

-- Scan from cell `j` with fuel `k`: the first cell whose front side ends the pattern.
--
def stripScan : ℕ → ℕ → Option ℕ
  | 0, _ => none
  | k + 1, j =>
    if IsCell V (cellJ c s j) ∧ LatOK F c s j then
      if (front (cellJ c s j) s ∈ F ↔ j % 2 = 0) then some (j + 1) else stripScan k (j + 1)
    else none

def stripLen : Option ℕ := if back c s ∈ F then stripScan V F c s V.card 0 else none

variable {V F c s}

lemma stripScan_some {k j m : ℕ} (h : stripScan V F c s k j = some m) :
    j < m ∧ ∀ i, j ≤ i → i < m → IsCell V (cellJ c s i) ∧ LatOK F c s i ∧
      (front (cellJ c s i) s ∈ F ↔ (i % 2 = 1 ↔ i + 1 < m)) := by
  induction k generalizing j with
  | zero => simp [stripScan] at h
  | succ k ih =>
    simp only [stripScan] at h
    split_ifs at h with h1 h2
    · cases h
      refine ⟨by omega, fun i hi hi' => ?_⟩
      obtain rfl : i = j := by omega
      refine ⟨h1.1, h1.2, ?_⟩
      rw [h2]; omega
    · obtain ⟨hjm, hrest⟩ := ih h
      refine ⟨by omega, fun i hi hi' => ?_⟩
      rcases Nat.eq_or_lt_of_le hi with rfl | hlt
      · refine ⟨h1.1, h1.2, ?_⟩
        have hr : (j % 2 = 1 ↔ j + 1 < m) ↔ j % 2 = 1 :=
          ⟨fun h => h.2 (by omega), fun h => ⟨fun _ => by omega, fun _ => h⟩⟩
        rw [hr]
        by_cases hf : front (cellJ c s j) s ∈ F
        · simp only [hf, true_iff] at h2 ⊢; omega
        · simp only [hf, false_iff] at h2 ⊢; omega
      · exact hrest i (by omega) hi'

lemma stripScan_of {n : ℕ}
    (hn : ∀ i < n, IsCell V (cellJ c s i) ∧ LatOK F c s i ∧
      (front (cellJ c s i) s ∈ F ↔ (i % 2 = 1 ↔ i + 1 < n))) :
    ∀ k j, j < n → n ≤ j + k → stripScan V F c s k j = some n := by
  intro k
  induction k with
  | zero => intro j hj hk; omega
  | succ k ih =>
    intro j hj hk
    obtain ⟨hc, hl, hf⟩ := hn j hj
    simp only [stripScan, ite_eq_left (And.intro hc hl)]
    by_cases hj1 : j + 1 = n
    · rw [ite_eq_left (by rw [hf]; omega)]; rw [hj1]
    · rw [ite_eq_right (by rw [hf]; omega)]
      exact ih (j + 1) (by omega) (by omega)

-- A strip with all cells in `V` has at most `|V|` cells.
--
lemma strip_len_le {n : ℕ} (h : ∀ j < n, IsCell V (cellJ c s j)) : n ≤ V.card := by
  have hmaps : ∀ k ∈ Finset.range n, cellJ c s k ∈ V := fun k hk =>
    (h k (Finset.mem_range.1 hk)).1
  have hinj : Set.InjOn (cellJ c s) (Finset.range n) := fun i _ j _ hij => cellJ_inj c s hij
  have := Finset.card_le_card_of_injOn _ hmaps hinj
  simpa using this

theorem stripLen_eq_some {n : ℕ} :
    stripLen V F c s = some n ↔
      1 ≤ n ∧ StripPat F c s n ∧ ∀ j < n, IsCell V (cellJ c s j) := by
  constructor
  · intro h
    unfold stripLen at h
    split_ifs at h with hb
    obtain ⟨h0, hr⟩ := stripScan_some h
    refine ⟨h0, ⟨hb, fun j hj => (hr j (Nat.zero_le _) hj).2.1,
      fun j hj => (hr j (Nat.zero_le _) hj).2.2⟩, fun j hj => (hr j (Nat.zero_le _) hj).1⟩
  · rintro ⟨h1, ⟨hb, hl, hf⟩, hc⟩
    unfold stripLen
    rw [ite_eq_left hb]
    exact stripScan_of (fun i hi => ⟨hc i hi, hl i hi, hf i hi⟩) _ 0 (by omega)
      (by have := strip_len_le hc; omega)

variable (V F)

def sidesF : Finset Side := {.b, .t, .l, .r}

lemma mem_sidesF (s : Side) : s ∈ sidesF := by cases s <;> simp [sidesF]

-- All strips of `F` with cells in `V`.
--
def allStrips : Finset StripSpec :=
  (V.filter (IsCell V)).biUnion fun c => sidesF.biUnion fun s =>
    ((stripLen V F c s).map (fun n => StripSpec.mk c s n)).toFinset

variable {V F}

theorem mem_allStrips {σ : StripSpec} :
    σ ∈ allStrips V F ↔
      1 ≤ σ.n ∧ StripPat F σ.c σ.s σ.n ∧ ∀ j < σ.n, IsCell V (cellJ σ.c σ.s j) := by
  obtain ⟨c, s, n⟩ := σ
  simp only [allStrips, Finset.mem_biUnion, Finset.mem_filter, Option.mem_toFinset,
    Option.mem_def, Option.map_eq_some_iff]
  constructor
  · rintro ⟨c', _, s', _, n', hn', he⟩
    cases he
    exact stripLen_eq_some.1 hn'
  · intro h
    have hc0 : IsCell V c := by have := h.2.2 0 (by omega); rwa [cellJ_zero] at this
    exact ⟨c, ⟨hc0.1, hc0⟩, s, mem_sidesF s, n, stripLen_eq_some.2 h, rfl⟩

lemma card_allStrips : (allStrips V F).card ≤ 4 * V.card := by
  unfold allStrips
  refine (Finset.card_biUnion_le).trans ?_
  have h1 : ∀ c ∈ V.filter (IsCell V), (sidesF.biUnion fun s =>
      ((stripLen V F c s).map (fun n => StripSpec.mk c s n)).toFinset).card ≤ 4 := by
    intro c _
    refine (Finset.card_biUnion_le).trans ?_
    have : ∀ s ∈ sidesF, (((stripLen V F c s).map (fun n => StripSpec.mk c s n)).toFinset).card
        ≤ 1 := fun s _ => by
      cases (stripLen V F c s).map (fun n => StripSpec.mk c s n) <;> simp
    refine (Finset.sum_le_sum this).trans ?_
    simp [sidesF]
  refine (Finset.sum_le_sum h1).trans ?_
  rw [Finset.sum_const, smul_eq_mul]
  have := Finset.card_filter_le V (IsCell V)
  omega

end enum

section decide

variable {V : Finset Pt} {F G : Finset Edge}

lemma connB_iff (hFV : Inside V F) {x y : Pt} (hx : x ∈ V) (hy : y ∈ V) :
    connB V F x y = true ↔ Conn F x y := by
  simp only [connB, decide_eq_true_eq, ccls_eq hFV hx, cls, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨hy, h⟩⟩

lemma corners_mem {c : Pt} (hc : IsCell V c) (s : Side) :
    back1 c s ∈ V ∧ front1 c s ∈ V := by
  obtain ⟨h1, h2, h3, h4⟩ := hc
  cases s <;> exact ⟨by simpa [back1] using ‹_›, by simpa [front1] using ‹_›⟩

def validB (V : Finset Pt) (F : Finset Edge) (σ : StripSpec) : Bool :=
  decide (σ ∈ allStrips V F) && !connB V F (back1 σ.c σ.s) (front1 σ.c σ.s)

theorem validB_iff (hFV : Inside V F) {σ : StripSpec} :
    validB V F σ = true ↔ ValidStrip V F σ := by
  unfold validB ValidStrip
  rw [Bool.and_eq_true, decide_eq_true_eq, mem_allStrips, Bool.not_eq_true']
  constructor
  · rintro ⟨⟨h1, hp, hc⟩, hn⟩
    have hc0 : IsCell V σ.c := by have := hc 0 (by omega); rwa [cellJ_zero] at this
    obtain ⟨hb, hf⟩ := corners_mem hc0 σ.s
    refine ⟨h1, hp, hc, fun h => ?_⟩
    rw [← connB_iff hFV hb hf] at h
    rw [h] at hn; cases hn
  · rintro ⟨h1, hp, hc, hn⟩
    have hc0 : IsCell V σ.c := by have := hc 0 (by omega); rwa [cellJ_zero] at this
    obtain ⟨hb, hf⟩ := corners_mem hc0 σ.s
    refine ⟨⟨h1, hp, hc⟩, ?_⟩
    cases h : connB V F (back1 σ.c σ.s) (front1 σ.c σ.s)
    · rfl
    · exact absurd ((connB_iff hFV hb hf).1 h) hn

-- `SideOff b c`, decided cell pair by cell pair.
--
def sideOffB (b c : StripSpec) : Bool :=
  (List.range c.n).all fun j => (List.range (b.n - 1)).all fun i =>
    decide (∀ e ∈ cellE (cellJ c.c c.s j), e ∉ cellE (cellJ b.c b.s i))

lemma sideOffB_iff {b c : StripSpec} : sideOffB b c = true ↔ SideOff b c := by
  simp only [sideOffB, SideOff, List.all_eq_true, List.mem_range, decide_eq_true_eq]
  constructor
  · intro h j hj i hi e he; exact h j hj i (by omega) e he
  · intro h j hj i hi e he; exact h j hj i (by omega) e he

def midB (b : StripSpec) (z : Pt) : Bool :=
  (List.range (b.n - 2)).any fun j =>
    decide (j % 2 = 1 ∧ (z = front1 (cellJ b.c b.s j) b.s ∨ z = front2 (cellJ b.c b.s j) b.s))

lemma midB_iff {b : StripSpec} {z : Pt} : midB b z = true ↔ IsMid b.c b.s (b.n - 2) z := by
  simp only [midB, IsMid, List.any_eq_true, List.mem_range, decide_eq_true_eq]
  constructor
  · rintro ⟨j, hj, h1, h2⟩; exact ⟨j, h1, hj, h2⟩
  · rintro ⟨j, h1, hj, h2⟩; exact ⟨j, hj, h1, h2⟩

-- The end-cell condition for even targets.
--
def endOffB (b c : StripSpec) : Bool :=
  decide (c.n % 2 = 0 → ∀ e ∈ cellE (endCell c), e ∉ cellE (endCell b))

def notEndB (b c : StripSpec) : Bool :=
  (List.range c.n).all fun j => decide (cellJ c.c c.s j ≠ endCell b)

def cr2B (V : Finset Pt) (G : Finset Edge) (b c : StripSpec) : Bool :=
  decide (2 ≤ b.n ∧ b.n % 2 = 0) && decide (c ∈ allStrips V (flip G (endCell b))) &&
    sideOffB b c && notEndB b c && endOffB b c && !midB b (back1 c.c c.s) &&
    !midB b (front1 c.c c.s) && connB V G (back1 c.c c.s) (front1 c.c c.s) &&
    !connB V (flip G (endCell b)) (back1 c.c c.s) (front1 c.c c.s)

lemma bool_not_iff {p : Bool} {P : Prop} (h : p = true ↔ P) : (!p) = true ↔ ¬ P := by
  rw [Bool.not_eq_true', ← h]; cases p <;> simp

theorem cr2B_iff (hGV : Inside V G) {b c : StripSpec} (hu : IsCell V (endCell b)) :
    cr2B V G b c = true ↔ CR2 V G b c := by
  have hFu : Inside V (flip G (endCell b)) := inside_flip hGV hu
  unfold cr2B CR2
  simp only [Bool.and_eq_true, decide_eq_true_eq, mem_allStrips, sideOffB_iff,
    bool_not_iff midB_iff]
  have hne : notEndB b c = true ↔ ∀ j < c.n, cellJ c.c c.s j ≠ endCell b := by
    simp [notEndB, List.all_eq_true, List.mem_range]
  have hend : endOffB b c = true ↔
      (c.n % 2 = 0 → ∀ e ∈ cellE (endCell c), e ∉ cellE (endCell b)) := by
    simp only [endOffB, decide_eq_true_eq]
  rw [hne, hend]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨⟨⟨⟨h2, he⟩, h1, hp, hc⟩, hso⟩, hne'⟩, hen⟩, hm1⟩, hm2⟩, hcg⟩, hcu⟩
    have hc0 : IsCell V c.c := by have := hc 0 (by omega); rwa [cellJ_zero] at this
    obtain ⟨hb, hf⟩ := corners_mem hc0 c.s
    refine ⟨h2, he, h1, hp, hc, hso, hne', hen, hm1, hm2, (connB_iff hGV hb hf).1 hcg, ?_⟩
    exact (bool_not_iff (connB_iff hFu hb hf)).1 hcu
  · rintro ⟨h2, he, h1, hp, hc, hso, hne', hen, hm1, hm2, hcg, hcu⟩
    have hc0 : IsCell V c.c := by have := hc 0 (by omega); rwa [cellJ_zero] at this
    obtain ⟨hb, hf⟩ := corners_mem hc0 c.s
    exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨h2, he⟩, h1, hp, hc⟩, hso⟩, hne'⟩, hen⟩, hm1⟩, hm2⟩,
      (connB_iff hGV hb hf).2 hcg⟩, (bool_not_iff (connB_iff hFu hb hf)).2 hcu⟩

end decide

end SolidGridHam
