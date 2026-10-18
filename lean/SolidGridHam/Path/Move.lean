/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import SolidGridHam.Path.Column
public import SolidGridHam.Path.FinalLocal
public import SolidGridHam.Cycle.L57
public import SolidGridHam.Path.Prelim.TheoremAPF

@[expose] public section

/-!
# The generalized move: edges and pieces after the move

`H₁ = lowerCol H c s k` flips `c_1 … c_k`. An edge changes iff an odd number of these cells has it
as a side (`mem_lowerCol`). So the lateral sides of `c_1 … c_k` and the two end fronts (`front c_0`,
`front c_k`) change; the inner fronts change twice and stay; nothing else changes.

For a column (`StripPat H c s (k + 1)`, `k` even) this makes `c_0` and `c_1` alternating: the new
fixed pair (docs/STUCK_MINIMAL.md §20).
-/

namespace SolidGridHam

namespace HP

open Finset Classical

section move

variable {c : Pt} {s : Side}

-- How many of `c_1 … c_k` have `e` as a side.
--
noncomputable def tog (c : Pt) (s : Side) (e : Edge) (k : ℕ) : ℕ :=
  ((Finset.Icc 1 k).filter (fun j => e ∈ cellE (cellJ c s j))).card

lemma tog_succ (e : Edge) (k : ℕ) :
    tog c s e (k + 1) = tog c s e k + (if e ∈ cellE (cellJ c s (k + 1)) then 1 else 0) := by
  unfold tog
  rw [show Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) by
    ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega]
  rw [Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · rfl

-- **Membership after the move.**
--
lemma mem_lowerCol : ∀ (k : ℕ) (F : Finset Edge) (e : Edge),
    e ∈ lowerCol F c s k ↔ (e ∈ F ↔ tog c s e k % 2 = 0)
  | 0, F, e => by simp [lowerCol, tog]
  | k + 1, F, e => by
    rw [lowerCol_succ, mem_lowerCol k, mem_flip_iff, tog_succ]
    by_cases h : e ∈ cellE (cellJ c s (k + 1))
    · rw [ite_eq_left h]
      have hp : (tog c s e k + 1) % 2 = 0 ↔ ¬ (tog c s e k % 2 = 0) := by omega
      rw [hp]; tauto
    · rw [ite_eq_right h, add_zero]; tauto

lemma tog_eq_of (e : Edge) (k : ℕ) (J : Finset ℕ)
    (h : ∀ j, 1 ≤ j → j ≤ k → (e ∈ cellE (cellJ c s j) ↔ j ∈ J)) (hJ : ∀ j ∈ J, 1 ≤ j ∧ j ≤ k) :
    tog c s e k = J.card := by
  unfold tog
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨h1, h2⟩, he⟩; exact (h j h1 h2).1 he
  · intro hj; obtain ⟨h1, h2⟩ := hJ j hj; exact ⟨⟨h1, h2⟩, (h j h1 h2).2 hj⟩

lemma mem_lowerCol_off {F : Finset Edge} {e : Edge} {k : ℕ}
    (h : ∀ j, 1 ≤ j → j ≤ k → e ∉ cellE (cellJ c s j)) : e ∈ lowerCol F c s k ↔ e ∈ F := by
  rw [mem_lowerCol, tog_eq_of e k ∅ (fun j h1 h2 => ⟨fun he => absurd he (h j h1 h2),
    fun hj => absurd hj (Finset.notMem_empty _)⟩) (fun j hj => absurd hj (Finset.notMem_empty _))]
  simp

lemma mem_lowerCol_once {F : Finset Edge} {e : Edge} {k m : ℕ} (hm1 : 1 ≤ m) (hmk : m ≤ k)
    (h : ∀ j, 1 ≤ j → j ≤ k → (e ∈ cellE (cellJ c s j) ↔ j = m)) :
    e ∈ lowerCol F c s k ↔ e ∉ F := by
  rw [mem_lowerCol, tog_eq_of e k {m} (fun j h1 h2 => by rw [h j h1 h2, Finset.mem_singleton])
    (fun j hj => by rw [Finset.mem_singleton] at hj; subst hj; exact ⟨hm1, hmk⟩)]
  simp

lemma mem_lowerCol_twice {F : Finset Edge} {e : Edge} {k m : ℕ} (hm1 : 1 ≤ m) (hmk : m + 1 ≤ k)
    (h : ∀ j, 1 ≤ j → j ≤ k → (e ∈ cellE (cellJ c s j) ↔ j = m ∨ j = m + 1)) :
    e ∈ lowerCol F c s k ↔ e ∈ F := by
  rw [mem_lowerCol, tog_eq_of e k {m, m + 1} (fun j h1 h2 => by
      rw [h j h1 h2]; simp)
    (fun j hj => by simp only [Finset.mem_insert, Finset.mem_singleton] at hj; omega)]
  rw [Finset.card_insert_of_notMem (by simp)]
  simp

/-! ## The column after the move -/

lemma cellJ_inj {i j : ℕ} (h : cellJ c s i = cellJ c s j) : i = j := by
  obtain ⟨x, y⟩ := c
  cases s <;> simp [cellJ] at h <;> omega

lemma lat1_mem_cellE_iff (i j : ℕ) : lat1 (cellJ c s i) s ∈ cellE (cellJ c s j) ↔ j = i := by
  constructor
  · intro h; by_contra hne; exact lat1_not_mem c s (j := i) (m := j) (Ne.symm hne) h
  · intro h; rw [h]; exact lat1_mem_self c s i

lemma lat2_mem_cellE_iff (i j : ℕ) : lat2 (cellJ c s i) s ∈ cellE (cellJ c s j) ↔ j = i := by
  constructor
  · intro h; by_contra hne; exact lat2_not_mem c s (j := i) (m := j) (Ne.symm hne) h
  · intro h; rw [h]; exact lat2_mem_self c s i

lemma front_mem_cellE_iff (i j : ℕ) :
    front (cellJ c s i) s ∈ cellE (cellJ c s j) ↔ j = i ∨ j = i + 1 := by
  constructor
  · intro h; by_contra hne; push Not at hne
    exact front_not_mem c s (j := i) (m := j) (Ne.symm hne.1) hne.2 h
  · rintro (h | h) <;> rw [h]
    · exact front_mem_self c s i
    · exact front_mem_next c s i

section col

set_option linter.unusedSectionVars false

variable {F : Finset Edge} {k : ℕ} (hk : k % 2 = 0) (hk2 : 2 ≤ k) (hp : StripPat F c s (k + 1))
include hk hk2 hp

-- Lateral sides of `c_1 … c_k` are toggled: dark exactly at even index.
--
lemma lat1_after {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ k) :
    lat1 (cellJ c s j) s ∈ lowerCol F c s k ↔ j % 2 = 0 := by
  rw [mem_lowerCol_once h1 h2 (fun i _ _ => lat1_mem_cellE_iff j i)]
  have := (hp.2.1 j (by omega)).1
  rw [this]; omega

lemma lat2_after {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ k) :
    lat2 (cellJ c s j) s ∈ lowerCol F c s k ↔ j % 2 = 0 := by
  rw [mem_lowerCol_once h1 h2 (fun i _ _ => lat2_mem_cellE_iff j i)]
  have := (hp.2.1 j (by omega)).2
  rw [this]; omega

lemma front0_after : front c s ∈ lowerCol F c s k := by
  have e := mem_lowerCol_once (F := F) (e := front (cellJ c s 0) s) (k := k) (m := 1) le_rfl
    (by omega) (fun i h1 _ => by rw [front_mem_cellE_iff]; omega)
  rw [cellJ_zero] at e
  rw [e]
  have := hp.2.2 0 (by omega)
  rw [cellJ_zero] at this
  rw [this]; omega

lemma frontk_after : front (cellJ c s k) s ∉ lowerCol F c s k := by
  have e := mem_lowerCol_once (F := F) (e := front (cellJ c s k) s) (k := k) (m := k) (by omega)
    le_rfl (fun i _ h2 => by rw [front_mem_cellE_iff]; omega)
  rw [e]
  have := hp.2.2 k (by omega)
  rw [this]; omega

lemma front_inner_after {j : ℕ} (h1 : 1 ≤ j) (h2 : j + 1 ≤ k) :
    front (cellJ c s j) s ∈ lowerCol F c s k ↔ j % 2 = 1 := by
  rw [mem_lowerCol_twice h1 h2 (fun i _ _ => front_mem_cellE_iff j i)]
  have := hp.2.2 j (by omega)
  rw [this]; omega

lemma back0_after : back c s ∈ lowerCol F c s k := by
  rw [mem_lowerCol_off (fun j h1 _ => back_not_mem c s (m := j) (by omega))]
  exact hp.1

lemma lat0_after : lat1 c s ∉ lowerCol F c s k ∧ lat2 c s ∉ lowerCol F c s k := by
  have h1 := (hp.2.1 0 (by omega)).1
  have h2 := (hp.2.1 0 (by omega)).2
  rw [cellJ_zero] at h1 h2
  rw [mem_lowerCol_off (fun j h1 _ => by
      have := lat1_mem_cellE_iff (c := c) (s := s) 0 j; rw [cellJ_zero] at this
      rw [this]; omega),
    mem_lowerCol_off (fun j h1 _ => by
      have := lat2_mem_cellE_iff (c := c) (s := s) 0 j; rw [cellJ_zero] at this
      rw [this]; omega)]
  constructor <;> simp [h1, h2]

-- **The new fixed pair is alternating.**
--
lemma alt0_after : Alt (lowerCol F c s k) c :=
  alt_of_bf (back0_after hk hk2 hp) (front0_after hk hk2 hp) (lat0_after hk hk2 hp).1
    (lat0_after hk hk2 hp).2

lemma alt1_after : Alt (lowerCol F c s k) (cellJ c s 1) := by
  apply alt_of_bf
  · rw [back_cellJ_succ, cellJ_zero]; exact front0_after hk hk2 hp
  · exact (front_inner_after hk hk2 hp le_rfl (by omega)).2 rfl
  · intro h; have := (lat1_after hk hk2 hp le_rfl (by omega)).1 h; omega
  · intro h; have := (lat2_after hk hk2 hp le_rfl (by omega)).1 h; omega

end col

/-! ## Pair facts -/

lemma side_cases (s s' : Side) : s' = s ∨ s' = s.opp ∨ s' = latA s ∨ s' = latB s := by
  cases s <;> cases s' <;> simp [Side.opp, latA, latB]

lemma outArc_toggle {F F' : Finset Edge} {q : Pt} {s' : Side}
    (h : sideEdge q s' ∈ F' ↔ sideEdge q s' ∉ F) : outArc F' q s' = !outArc F q s' := by
  rw [outArc_eq, outArc_eq]
  by_cases h1 : sideEdge q s' ∈ F
  · have h2 : sideEdge q s' ∉ F' := fun h' => h.1 h' h1
    simp only [h1, h2, decide_true, decide_false]
    cases par q <;> cases s'.horiz <;> rfl
  · have h2 : sideEdge q s' ∈ F' := h.2 h1
    simp only [h1, h2, decide_true, decide_false]
    cases par q <;> cases s'.horiz <;> rfl

lemma corner_cases (q : Pt) (s' : Side) {u : Pt} (h : IsCorner u q) :
    u = back1 q s' ∨ u = back2 q s' ∨ u = front1 q s' ∨ u = front2 q s' := by
  obtain ⟨x, y⟩ := q
  rcases h with rfl | rfl | rfl | rfl <;> cases s' <;> simp [back1, back2, front1, front2]

-- At a square with dark back and front, two corners on different pieces are the two pieces of
-- the dark sides.
--
lemma peq_of_bf {F : Finset Edge} {q : Pt} {s' : Side} (hb : back q s' ∈ F)
    (hf : front q s' ∈ F) {u v : Pt} (hu : IsCorner u q) (hv : IsCorner v q)
    (huv : ¬ Conn F u v) : PEq F u v (back1 q s') (front1 q s') := by
  have kb := (ends_back q s').conn hb
  have kf := (ends_front q s').conn hf
  have side : ∀ w, IsCorner w q → Conn F w (back1 q s') ∨ Conn F w (front1 q s') := by
    intro w hw
    rcases corner_cases q s' hw with rfl | rfl | rfl | rfl
    · exact Or.inl (Conn.refl _ _)
    · exact Or.inl kb.symm
    · exact Or.inr (Conn.refl _ _)
    · exact Or.inr kf.symm
  rcases side u hu with h1 | h1 <;> rcases side v hv with h2 | h2
  · exact absurd (h1.trans h2.symm) huv
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩
  · exact absurd (h1.trans h2.symm) huv

/-! ## The new pair -/

-- The new fixed pair: top `c_0`, bottom `c_1` (for a climbing column).
--
def newPair (c : Pt) (s : Side) : FixedPr :=
  ⟨cellJ c s 1, s.opp, back1 c s, front1 c s, back1 (cellJ c s 1) s, front1 (cellJ c s 1) s⟩

lemma newPair_top : (newPair c s).top = c := by
  unfold FixedPr.top newPair
  obtain ⟨x, y⟩ := c
  cases s <;> simp [cellJ, nb, Side.opp]

lemma newPair_ok {F : Finset Edge} {k : ℕ} (hk : k % 2 = 0) (hk2 : 2 ≤ k)
    (hp : StripPat F c s (k + 1)) (hup : outArc F c s = true) :
    PairOK (lowerCol F c s k) (newPair c s) := by
  set H₁ := lowerCol F c s k
  have hb0 := back0_after hk hk2 hp
  have hf0 := front0_after hk hk2 hp
  have hl0 := lat0_after hk hk2 hp
  have hf1 := (front_inner_after hk hk2 hp le_rfl (by omega)).2 rfl
  have hn1 : nb c s = cellJ c s 1 := by rw [← nb_cellJ, cellJ_zero]
  have hb1 : back (cellJ c s 1) s ∈ H₁ := by rw [back_cellJ_succ, cellJ_zero]; exact hf0
  have arcA := lat_arc_first hp (by omega)
  rw [hup] at arcA
  -- Lateral sides of `c`: unchanged; of `c_1`: toggled.
  --
  have l0A : outArc H₁ c (latA s) = false := by
    rw [outArc_congr (F' := F) (by
      rw [← lat1_eq]
      exact ⟨fun h => absurd h hl0.1, fun h => absurd h (by
        have := (hp.2.1 0 (by omega)).1; rw [cellJ_zero] at this; simp [this])⟩)]
    exact arcA.1
  have l0B : outArc H₁ c (latB s) = false := by
    rw [outArc_congr (F' := F) (by
      rw [← lat2_eq]
      exact ⟨fun h => absurd h hl0.2, fun h => absurd h (by
        have := (hp.2.1 0 (by omega)).2; rw [cellJ_zero] at this; simp [this])⟩)]
    exact arcA.2
  have l1A : outArc H₁ (cellJ c s 1) (latA s) = true := by
    rw [outArc_toggle (F := F) (by
      rw [← lat1_eq]
      have e := lat1_after hk hk2 hp (j := 1) le_rfl (by omega)
      have f := (hp.2.1 1 (by omega)).1
      constructor
      · intro h; have := e.1 h; omega
      · intro h; exact absurd (f.2 rfl) h), lat_arcA hp (by omega), arcA.1]
    rfl
  have l1B : outArc H₁ (cellJ c s 1) (latB s) = true := by
    rw [outArc_toggle (F := F) (by
      rw [← lat2_eq]
      have e := lat2_after hk hk2 hp (j := 1) le_rfl (by omega)
      have f := (hp.2.1 1 (by omega)).2
      constructor
      · intro h; have := e.1 h; omega
      · intro h; exact absurd (f.2 rfl) h), lat_arcB hp (by omega), arcA.2]
    rfl
  have f0arc : outArc H₁ c s = false := by
    rw [outArc_toggle (F := F) (by
      have := hp.2.2 0 (by omega); rw [cellJ_zero] at this
      exact ⟨fun _ h => by have := this.1 h; omega, fun _ => hf0⟩), hup]
    rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro s' hs'
    rw [newPair_top] at hs' ⊢
    rcases side_cases s s' with rfl | rfl | rfl | rfl
    · exact absurd hf0 hs'
    · exact absurd hb0 hs'
    · exact l0A
    · exact l0B
  · intro s' hs'
    show outArc H₁ (cellJ c s 1) s' = true
    rcases side_cases s s' with rfl | rfl | rfl | rfl
    · exact absurd hf1 hs'
    · exact absurd hb1 hs'
    · exact l1A
    · exact l1B
  · show outArc H₁ (cellJ c s 1) s.opp = true
    rw [← hn1, outArc_nb_opp, f0arc]; rfl
  · intro u v hu hv huv
    rw [newPair_top] at hu hv
    exact peq_of_bf hb0 hf0 hu hv huv
  · intro u v hu hv huv
    exact peq_of_bf hb1 hf1 hu hv huv

-- The new fixed pair for a descending column: bottom `c_0`, top `c_1`.
--
def newPairF (c : Pt) (s : Side) : FixedPr :=
  ⟨c, s, back1 (cellJ c s 1) s, front1 (cellJ c s 1) s, back1 c s, front1 c s⟩

lemma newPairF_top : (newPairF c s).top = cellJ c s 1 := by
  unfold FixedPr.top newPairF; rw [← nb_cellJ, cellJ_zero]

lemma newPairF_ok {F : Finset Edge} {k : ℕ} (hk : k % 2 = 0) (hk2 : 2 ≤ k)
    (hp : StripPat F c s (k + 1)) (hdn : outArc F c s = false) :
    PairOK (lowerCol F c s k) (newPairF c s) := by
  set H₁ := lowerCol F c s k
  have hb0 := back0_after hk hk2 hp
  have hf0 := front0_after hk hk2 hp
  have hl0 := lat0_after hk hk2 hp
  have hf1 := (front_inner_after hk hk2 hp le_rfl (by omega)).2 rfl
  have hb1 : back (cellJ c s 1) s ∈ H₁ := by rw [back_cellJ_succ, cellJ_zero]; exact hf0
  have arcA := lat_arc_first hp (by omega)
  rw [hdn] at arcA
  have l0A : outArc H₁ c (latA s) = true := by
    rw [outArc_congr (F' := F) (by
      rw [← lat1_eq]
      exact ⟨fun h => absurd h hl0.1, fun h => absurd h (by
        have := (hp.2.1 0 (by omega)).1; rw [cellJ_zero] at this; simp [this])⟩)]
    exact arcA.1
  have l0B : outArc H₁ c (latB s) = true := by
    rw [outArc_congr (F' := F) (by
      rw [← lat2_eq]
      exact ⟨fun h => absurd h hl0.2, fun h => absurd h (by
        have := (hp.2.1 0 (by omega)).2; rw [cellJ_zero] at this; simp [this])⟩)]
    exact arcA.2
  have l1A : outArc H₁ (cellJ c s 1) (latA s) = false := by
    rw [outArc_toggle (F := F) (by
      rw [← lat1_eq]
      have e := lat1_after hk hk2 hp (j := 1) le_rfl (by omega)
      have f := (hp.2.1 1 (by omega)).1
      constructor
      · intro h; have := e.1 h; omega
      · intro h; exact absurd (f.2 rfl) h), lat_arcA hp (by omega), arcA.1]
    rfl
  have l1B : outArc H₁ (cellJ c s 1) (latB s) = false := by
    rw [outArc_toggle (F := F) (by
      rw [← lat2_eq]
      have e := lat2_after hk hk2 hp (j := 1) le_rfl (by omega)
      have f := (hp.2.1 1 (by omega)).2
      constructor
      · intro h; have := e.1 h; omega
      · intro h; exact absurd (f.2 rfl) h), lat_arcB hp (by omega), arcA.2]
    rfl
  have f0arc : outArc H₁ c s = true := by
    rw [outArc_toggle (F := F) (by
      have := hp.2.2 0 (by omega); rw [cellJ_zero] at this
      exact ⟨fun _ h => by have := this.1 h; omega, fun _ => hf0⟩), hdn]
    rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro s' hs'
    rw [newPairF_top] at hs' ⊢
    rcases side_cases s s' with rfl | rfl | rfl | rfl
    · exact absurd hf1 hs'
    · exact absurd hb1 hs'
    · exact l1A
    · exact l1B
  · intro s' hs'
    show outArc H₁ c s' = true
    rcases side_cases s s' with rfl | rfl | rfl | rfl
    · exact absurd hf0 hs'
    · exact absurd hb0 hs'
    · exact l0A
    · exact l0B
  · exact f0arc
  · intro u v hu hv huv
    rw [newPairF_top] at hu hv
    exact peq_of_bf hb1 hf1 hu hv huv
  · intro u v hu hv huv
    exact peq_of_bf hb0 hf0 hu hv huv

/-! ## Forced edges beside the column

At a column vertex `front1 c_j` (`j + 1 < n`) the three column edges (`lat1 c_j`, `front c_j`,
`lat1 c_(j+1)`) contain exactly one dark edge when `j` is even and two when `j` is odd; degree 2
forces the fourth edge, `outer1 c_j`, which leaves the column sideways. -/

lemma outer1_forced {F : Finset Edge} {n j : ℕ} (hp : StripPat F c s n) (hj : j + 1 < n)
    (hd : deg F (front1 (cellJ c s j) s) = 2) :
    outer1 (cellJ c s j) s ∈ F ↔ j % 2 = 0 := by
  rw [deg_front1, nb_cellJ] at hd
  have a1 := (hp.2.1 j (by omega)).1
  have b1 := (hp.2.1 (j + 1) hj).1
  have af := hp.2.2 j (by omega)
  have af' : front (cellJ c s j) s ∈ F ↔ j % 2 = 1 := by rw [af]; omega
  by_cases h : j % 2 = 1
  · rw [ind_of_mem (a1.2 h), ind_of_mem (af'.2 h),
      ind_of_not_mem (fun h' => by have := b1.1 h'; omega)] at hd
    constructor
    · intro ho; rw [ind_of_mem ho] at hd; omega
    · intro h'; omega
  · rw [ind_of_not_mem (fun h' => h (a1.1 h')), ind_of_not_mem (fun h' => h (af'.1 h')),
      ind_of_mem (b1.2 (by omega))] at hd
    constructor
    · intro _; omega
    · intro _; by_contra ho; rw [ind_of_not_mem ho] at hd; omega

lemma outer2_forced {F : Finset Edge} {n j : ℕ} (hp : StripPat F c s n) (hj : j + 1 < n)
    (hd : deg F (front2 (cellJ c s j) s) = 2) :
    outer2 (cellJ c s j) s ∈ F ↔ j % 2 = 0 := by
  rw [deg_front2, nb_cellJ] at hd
  have a1 := (hp.2.1 j (by omega)).2
  have b1 := (hp.2.1 (j + 1) hj).2
  have af := hp.2.2 j (by omega)
  have af' : front (cellJ c s j) s ∈ F ↔ j % 2 = 1 := by rw [af]; omega
  by_cases h : j % 2 = 1
  · rw [ind_of_mem (a1.2 h), ind_of_mem (af'.2 h),
      ind_of_not_mem (fun h' => by have := b1.1 h'; omega)] at hd
    constructor
    · intro ho; rw [ind_of_mem ho] at hd; omega
    · intro h'; omega
  · rw [ind_of_not_mem (fun h' => h (a1.1 h')), ind_of_not_mem (fun h' => h (af'.1 h')),
      ind_of_mem (b1.2 (by omega))] at hd
    constructor
    · intro _; omega
    · intro _; by_contra ho; rw [ind_of_not_mem ho] at hd; omega

-- An alternating square has opposite sides of equal membership.
--
lemma alt_opp_iff {F : Finset Edge} {q : Pt} (h : Alt F q) (s' : Side) :
    sideEdge q s' ∈ F ↔ sideEdge q s'.opp ∈ F := by
  unfold Alt at h
  cases s' <;> simp only [sideEdge, Side.opp] <;> tauto

-- **Side squares beside the column interior are not alternating**: their two sides along the
-- column direction are the outer edges at consecutive column vertices, of opposite membership.
--
lemma sideA_not_alt {F : Finset Edge} {n j : ℕ} (hp : StripPat F c s n) (h1 : 1 ≤ j)
    (hj : j + 1 < n) (hd0 : deg F (front1 (cellJ c s (j - 1)) s) = 2)
    (hd1 : deg F (front1 (cellJ c s j) s) = 2) : ¬ Alt F (nb (cellJ c s j) (latA s)) := by
  intro halt
  have e0 := outer1_forced hp (j := j - 1) (by omega) hd0
  have e1 := outer1_forced hp hj hd1
  have hb : outer1 (cellJ c s (j - 1)) s = sideEdge (nb (cellJ c s j) (latA s)) s.opp := by
    rw [outer1_side_nb_next, nb_cellJ, show j - 1 + 1 = j by omega]
  have hf : outer1 (cellJ c s j) s = sideEdge (nb (cellJ c s j) (latA s)) s := outer1_side_nb _ _
  have := alt_opp_iff halt s
  rw [← hb, ← hf, e0, e1] at this
  omega

lemma sideB_not_alt {F : Finset Edge} {n j : ℕ} (hp : StripPat F c s n) (h1 : 1 ≤ j)
    (hj : j + 1 < n) (hd0 : deg F (front2 (cellJ c s (j - 1)) s) = 2)
    (hd1 : deg F (front2 (cellJ c s j) s) = 2) : ¬ Alt F (nb (cellJ c s j) (latB s)) := by
  intro halt
  have e0 := outer2_forced hp (j := j - 1) (by omega) hd0
  have e1 := outer2_forced hp hj hd1
  have hb : outer2 (cellJ c s (j - 1)) s = sideEdge (nb (cellJ c s j) (latB s)) s.opp := by
    rw [outer2_side_nb_next, nb_cellJ, show j - 1 + 1 = j by omega]
  have hf : outer2 (cellJ c s j) s = sideEdge (nb (cellJ c s j) (latB s)) s := outer2_side_nb _ _
  have := alt_opp_iff halt s
  rw [← hb, ← hf, e0, e1] at this
  omega

/-! ## Factor and pieces after the move, on `W ⊇ V` -/

-- The column's cells are cells of `V`, `V ⊆ W`, and every corner of a column cell has degree 2.
-- Then the move keeps `H` a factor of `W`, keeps the number of pieces, and keeps every connection
-- between points that are not even-height interior column vertices.
--
theorem lowerCol_factor {V W : Finset Pt} {d : Pt → ℕ} (hVW : V ⊆ W) :
    ∀ k : ℕ, k % 2 = 0 → ∀ F : Finset Edge, IsFactor W d F →
    (∀ j ≤ k, IsCell V (cellJ c s j)) →
    (∀ j ≤ k, ∀ z, IsCorner z (cellJ c s j) → d z = 2) →
    StripPat F c s (k + 1) →
    IsFactor W d (lowerCol F c s k) ∧ ncomp W (lowerCol F c s k) = ncomp W F ∧
      ∀ x y, ¬ IsMid c s k x → ¬ IsMid c s k y → (Conn (lowerCol F c s k) x y ↔ Conn F x y) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro hk F hF hcell hd hpat
  rcases (show k = 0 ∨ 2 ≤ k by omega) with rfl | hk2
  · exact ⟨hF, rfl, fun x y _ _ => Iff.rfl⟩
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  have hm : m % 2 = 0 := by omega
  rw [lowerCol_succ, lowerCol_succ]
  set u := cellJ c s (m + 1)
  have hnb : nb u s = cellJ c s (m + 2) := nb_cellJ c s (m + 1)
  obtain ⟨hb, hl, hf⟩ := hpat
  have uL1 : lat1 u s ∈ F := (hl (m + 1) (by omega)).1.2 (by omega)
  have uL2 : lat2 u s ∈ F := (hl (m + 1) (by omega)).2.2 (by omega)
  have uF : front u s ∈ F := (hf (m + 1) (by omega)).2 (by omega)
  have uB : back u s ∉ F := by
    rw [back_cellJ_succ]
    intro h; have := (hf m (by omega)).1 h; omega
  have wL1 : lat1 (nb u s) s ∉ F := by
    rw [hnb]; intro h; have := (hl (m + 2) (by omega)).1.1 h; omega
  have wL2 : lat2 (nb u s) s ∉ F := by
    rw [hnb]; intro h; have := (hl (m + 2) (by omega)).2.1 h; omega
  have wF : front (nb u s) s ∈ F := by
    rw [hnb]; exact (hf (m + 2) (by omega)).2 (by omega)
  have hdouble : flip (flip F (cellJ c s (m + 2))) (cellJ c s (m + 1)) = (mkPair u s).res F := by
    rw [← hnb]; exact pair_flip_eq u s uL1 uL2 wF uB wL1 wL2
  have hcu : IsCell V u := hcell (m + 1) (by omega)
  have hcw : IsCell V (nb u s) := by rw [hnb]; exact hcell (m + 2) (by omega)
  obtain ⟨ub1, ub2, uf1, uf2⟩ := isCell_corners hcu s
  obtain ⟨_, _, wf1, wf2⟩ := isCell_corners hcw s
  have df1 : deg F (front1 u s) = 2 := by
    rw [hF.2 _ (hVW uf1)]; exact hd (m + 1) (by omega) _ (isCorner_front1 u s)
  have df2 : deg F (front2 u s) = 2 := by
    rw [hF.2 _ (hVW uf2)]; exact hd (m + 1) (by omega) _ (isCorner_front2 u s)
  obtain ⟨hcount, hrel⟩ := (mkPair u s).flip (V := W) (hVW ub2) (hVW uf1) (hVW uf2) (hVW wf1)
    uL1 uL2 uF wF df1 df2
  rw [hdouble]
  have hF2' : IsFactor W d ((mkPair u s).res F) := by
    rw [← hdouble]
    have hcwW : IsCell W (nb u s) := isCell_mono hcw hVW
    have hcuW : IsCell W u := isCell_mono hcu hVW
    have d1 : IsFactor W d (flip F (cellJ c s (m + 2))) := by
      rw [← hnb]
      exact factor_flip hF (mkBF (nb u s) s) hcwW (mkBF_cellE _ s)
        (by show back (nb u s) s ∈ F; rw [back_nb]; exact uF) wF wL1 wL2
    have m1 : lat1 u s ∈ flip F (cellJ c s (m + 2)) := by
      rw [mem_flip_iff]; have := lat1_not_mem c s (j := m + 1) (m := m + 2) (by omega); tauto
    have m2 : lat2 u s ∈ flip F (cellJ c s (m + 2)) := by
      rw [mem_flip_iff]; have := lat2_not_mem c s (j := m + 1) (m := m + 2) (by omega); tauto
    have m3 : back u s ∉ flip F (cellJ c s (m + 2)) := by
      rw [mem_flip_iff, back_cellJ_succ]
      have := front_not_mem c s (j := m) (m := m + 2) (by omega) (by omega)
      rw [back_cellJ_succ] at uB; tauto
    have m4 : front u s ∉ flip F (cellJ c s (m + 2)) := by
      rw [mem_flip_iff]; have := front_mem_next c s (m + 1); tauto
    exact factor_flip d1 (mkLat u s) hcuW (mkLat_cellE u s) m1 m2 m3 m4
  have hpat2 : StripPat ((mkPair u s).res F) c s (m + 1) := by
    rw [← hdouble]; exact pat_flip_pair hm ⟨hb, hl, hf⟩
  obtain ⟨ihf, ihc, ihr⟩ := ih m (by omega) hm _ hF2' (fun j hj => hcell j (by omega))
    (fun j hj => hd j (by omega)) hpat2
  refine ⟨ihf, ihc.trans hcount, fun x y hx hy => ?_⟩
  have mono : ∀ z, ¬ IsMid c s (m + 2) z → ¬ IsMid c s m z := fun z hz ⟨j, hj1, hj2, hj3⟩ =>
    hz ⟨j, hj1, by omega, hj3⟩
  have off : ∀ z, ¬ IsMid c s (m + 2) z → z ≠ front1 u s ∧ z ≠ front2 u s := fun z hz =>
    ⟨fun h => hz ⟨m + 1, by omega, by omega, Or.inl h⟩,
      fun h => hz ⟨m + 1, by omega, by omega, Or.inr h⟩⟩
  rw [ihr x y (mono x hx) (mono y hy)]
  exact hrel x y (off x hx).1 (off x hx).2 (off y hy).1 (off y hy).2

end move

end HP

end SolidGridHam
