/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import SolidGridHam.Path.SlitHeight

/-!
# Hole classes: factors as admissible potentials (B-3, docs/HOLE_CLASSES.md §3.1, §3.2)

Port of ulhc-hole's `HoleClass`/`KHole1` with the single vertex set split in two: factors live on
a box set `W` (degree function `d`), and potentials may jump only across edges of the inner set
`V ⊆ W`. Edges outside `V` are therefore frozen equal to the reference factor `F`.

* `adm_factorW` (P1): an admissible `φ` gives the factor `F ⊕ X`, `X` the edges of `V` where `φ`
  jumps, with `wD F (F ⊕ X) = 2 · (jump of φ)`.
* `D_of_admW` (P4): then `D F (F ⊕ X) = 2 φ` when `φ` vanishes far left.
* `adm_of_factorW` (P3): a factor `G` agreeing with `F` off `V` gives the admissible `D F G / 2`.
* `D_sub`: `D G H = D F H − D F G`, so classes subtract.
* `solidFor_of_holes` (B-1 for several holes): `D` vanishes off the cells once it vanishes at
  one point of each hole.
* `D_abs_le_card`: `|D F G c| ≤ 2 |V|` (the class bound); `D_half_abs`, `D_zero_*`: `D F G / 2`
  vanishes off the box of `V` and is bounded by its width.
* `width_lt_card'`, `height_lt_card'`: one connected component spans a narrow box.
-/

namespace SolidGridHam

namespace HP

open Finset

/-! ## Signs and `D` as a difference of row sums -/

def sv (F : Finset Edge) (e : Edge) : ℤ := if up F e then 1 else -1

noncomputable def Sc (V : Finset Pt) (F : Finset Edge) (c : Pt) : ℤ :=
  ∑ e ∈ (GE V).filter (RowSel c), sv F e

lemma wD_eq_sv (F H : Finset Edge) (e : Edge) : wD F H e = sv F e - sv H e := by
  unfold wD wb sv up inE1
  by_cases h1 : e ∈ F <;> by_cases h2 : e ∈ H <;> cases hd : e.d <;> cases hp : par e.lo <;>
    simp [h1, h2]

theorem D_eq_Sc {V : Finset Pt} {F H : Finset Edge} (hF : ∀ e ∈ F, e ∈ GE V)
    (hH : ∀ e ∈ H, e ∈ GE V) (c : Pt) : D F H c = Sc V F c - Sc V H c := by
  have hsub : symmDiff F H ⊆ GE V := by
    intro e he
    rw [Finset.mem_symmDiff] at he
    rcases he with ⟨he, _⟩ | ⟨he, _⟩
    · exact hF e he
    · exact hH e he
  unfold D
  rw [pot_mono_supp hsub (wD_supp F H) c]
  unfold pot Sc
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun e _ => wD_eq_sv F H e)

-- Classes subtract: for edge sets inside one `W`, `D G H = D F H − D F G`.
--
lemma D_sub {W : Finset Pt} {F G H : Finset Edge} (hF : Inside W F) (hG : Inside W G)
    (hH : Inside W H) (c : Pt) : D G H c = D F H c - D F G c := by
  have gF : ∀ e ∈ F, e ∈ GE W := fun e he => mem_GE.2 (hF e he)
  have gG : ∀ e ∈ G, e ∈ GE W := fun e he => mem_GE.2 (hG e he)
  have gH : ∀ e ∈ H, e ∈ GE W := fun e he => mem_GE.2 (hH e he)
  rw [D_eq_Sc gG gH, D_eq_Sc gF gH, D_eq_Sc gF gG]
  ring

/-! ## Degrees from balance -/

-- The converse of `wD_balanced_at`: balance of `wD F G` at `p` forces equal degrees.
--
lemma deg_eq_of_balanced (F G : Finset Edge) (p : Pt)
    (hb : wD F G (eD p) + wD F G (eR p) = wD F G (eL p) + wD F G (eU p)) :
    deg F p = deg G p := by
  obtain ⟨x, y⟩ := p
  have p1 := par_sub_sub (x, y)
  have p2 := par_sub_snd (x, y)
  have p3 := par_sub_fst (x, y)
  simp only at p1 p2 p3
  unfold deg ind
  unfold wD at hb
  simp only [up, inE1, eD, eR, eL, eU, Edge.lo, p1, p2, p3] at hb ⊢
  generalize par (x, y) = b at hb
  cases b <;>
  by_cases a1 : (⟨.v, (x, y - 1)⟩ : Edge) ∈ F <;>
  by_cases a2 : (⟨.h, (x, y)⟩ : Edge) ∈ F <;>
  by_cases a3 : (⟨.h, (x - 1, y)⟩ : Edge) ∈ F <;>
  by_cases a4 : (⟨.v, (x, y)⟩ : Edge) ∈ F <;>
  by_cases b1 : (⟨.v, (x, y - 1)⟩ : Edge) ∈ G <;>
  by_cases b2 : (⟨.h, (x, y)⟩ : Edge) ∈ G <;>
  by_cases b3 : (⟨.h, (x - 1, y)⟩ : Edge) ∈ G <;>
  by_cases b4 : (⟨.v, (x, y)⟩ : Edge) ∈ G <;>
  simp [a1, a2, a3, a4, b1, b2, b3, b4, wb] at hb ⊢

/-! ## Admissible potentials -/

-- `φ` stays the same across `e`, or `e` is an edge of the inner set `V` and `φ` jumps by
-- `sv F e` from the low cell to the high cell.
--
def Adm (V : Finset Pt) (F : Finset Edge) (φ : Pt → ℤ) : Prop :=
  ∀ e : Edge, φ e.hi - φ e.lo = 0 ∨ (IsEdge V e ∧ φ e.hi - φ e.lo = sv F e)

lemma mem_symmDiff_xor (F X : Finset Edge) (e : Edge) :
    (decide (e ∈ F) ^^ decide (e ∈ symmDiff F X)) = decide (e ∈ X) := by
  by_cases h1 : e ∈ F <;> by_cases h2 : e ∈ X <;> simp [Finset.mem_symmDiff, h1, h2]

-- The jumps of any function around a point telescope.
--
lemma jump_balanced (φ : Pt → ℤ) : Balanced (fun e => 2 * (φ e.hi - φ e.lo)) := by
  intro p
  obtain ⟨x, y⟩ := p
  simp only [eD, eR, eL, eU, Edge.hi_mk, Edge.lo_h, Edge.lo_v]
  ring

section adm

variable {V W : Finset Pt} {d : Pt → ℕ} {F G : Finset Edge}

-- **P1.** An admissible `φ` gives a factor on `W` with the same degrees.
--
theorem adm_factorW {X : Finset Edge} {φ : Pt → ℤ} (hVW : V ⊆ W) (hF : IsFactor W d F)
    (hA : Adm V F φ) (hX : ∀ e, e ∈ X ↔ IsEdge V e ∧ φ e.hi ≠ φ e.lo) :
    IsFactor W d (symmDiff F X) ∧ ∀ e, wD F (symmDiff F X) e = 2 * (φ e.hi - φ e.lo) := by
  have hw : ∀ e, wD F (symmDiff F X) e = 2 * (φ e.hi - φ e.lo) := by
    intro e
    unfold wD
    rw [mem_symmDiff_xor]
    by_cases he : e ∈ X
    · have h2 := (hX e).1 he
      rcases hA e with h | ⟨_, h⟩
      · exact absurd (by omega) h2.2
      · simp only [he, decide_true, wb, ite_true, h, sv]
        cases up F e <;> simp
    · have h0 : φ e.hi - φ e.lo = 0 := by
        rcases hA e with h | ⟨hE, h⟩
        · exact h
        · by_contra hne
          exact he ((hX e).2 ⟨hE, by omega⟩)
      simp [he, wb, h0]
  refine ⟨⟨?_, ?_⟩, hw⟩
  · intro e he
    rw [Finset.mem_symmDiff] at he
    rcases he with ⟨he, _⟩ | ⟨he, _⟩
    · exact hF.1 e he
    · have h := ((hX e).1 he).1
      exact ⟨hVW h.1, hVW h.2⟩
  · intro z hz
    have hb := jump_balanced φ z
    simp only at hb
    rw [← hw, ← hw, ← hw, ← hw] at hb
    rw [← deg_eq_of_balanced F _ z hb]
    exact hF.2 z hz

-- **P4.** With the same jumps as `D F G` and vanishing far left, `φ` is `D F G / 2`.
--
theorem D_of_admW {φ : Pt → ℤ} (hF : IsFactor W d F) (hG : IsFactor W d G)
    (hFG : ∀ e ∈ symmDiff F G, IsEdge V e) (hw : ∀ e, wD F G e = 2 * (φ e.hi - φ e.lo))
    {B : ℤ} (hB : ∀ p ∈ V, B < p.1) (h0 : ∀ c : Pt, c.1 ≤ B → φ c = 0) (c : Pt) :
    D F G c = 2 * φ c := by
  have hE : ∀ e ∈ symmDiff F G, B < e.p.1 := fun e he => hB _ (hFG e he).1
  have base : ∀ c : Pt, c.1 ≤ B → D F G c = 2 * φ c := by
    intro c hc
    rw [h0 c hc]
    unfold D
    rw [pot_eq_zero_of_left hE c hc]
    ring
  obtain ⟨x, y⟩ := c
  rcases le_total x B with hx | hx
  · exact base (x, y) hx
  · induction x, hx using Int.leInduction with
    | base => exact base (B, y) le_rfl
    | succ n _ ih =>
      have j := D_jump hF hG (⟨.v, (n + 1, y)⟩ : Edge)
      rw [hw] at j
      simp only [Edge.hi_mk, Edge.lo_v, add_sub_cancel_right] at j
      linarith

-- **P3.** A factor `G` on `W` agreeing with `F` off the edges of `V` gives an admissible
-- function.
--
theorem adm_of_factorW (hF : IsFactor W d F) (hG : IsFactor W d G)
    (hFG : ∀ e ∈ symmDiff F G, IsEdge V e) :
    Adm V F (fun c => D F G c / 2) ∧ ∀ c, D F G c = 2 * (D F G c / 2) := by
  have hev : ∀ c, D F G c = 2 * (D F G c / 2) := fun c =>
    (Int.mul_ediv_cancel' (D_even F G c)).symm
  refine ⟨fun e => ?_, hev⟩
  have j := D_jump hF hG e
  have a1 := hev e.hi
  have a2 := hev e.lo
  unfold wD at j
  by_cases hx : (decide (e ∈ F) ^^ decide (e ∈ G)) = true
  · right
    have hE : IsEdge V e := by
      apply hFG
      rw [Finset.mem_symmDiff]
      by_cases h1 : e ∈ F
      · have h2 : e ∉ G := by simpa [h1] using hx
        exact Or.inl ⟨h1, h2⟩
      · have h2 : e ∈ G := by simpa [h1] using hx
        exact Or.inr ⟨h2, h1⟩
    refine ⟨hE, ?_⟩
    rw [hx] at j
    have j2 : D F G e.hi - D F G e.lo = 2 * sv F e := by
      rw [j]; unfold sv wb; cases up F e <;> simp
    show D F G e.hi / 2 - D F G e.lo / 2 = sv F e
    unfold sv at j2 ⊢
    split_ifs at j2 ⊢ <;> omega
  · left
    simp only [Bool.not_eq_true] at hx
    rw [hx] at j
    simp only [wb, Bool.false_eq_true, ite_false] at j
    show D F G e.hi / 2 - D F G e.lo / 2 = 0
    omega

end adm

/-! ## Holes -/

-- Every missing point of `V` joins some point of `as`, or escapes to the left of `V`, by king
-- moves through missing points.
--
def KHoles (V : Finset Pt) (as : List Pt) : Prop :=
  (∀ a ∈ as, a ∉ V) ∧ ∀ b, b ∉ V → (∃ a ∈ as, Relation.ReflTransGen (MissAdj V) b a) ∨
    ∃ b', Relation.ReflTransGen (MissAdj V) b b' ∧ ∀ p ∈ V, b'.1 < p.1

-- One hole: every missing point of `V` joins `t` (a king cluster of missing points containing
-- `t`) or escapes to the far left.
--
lemma kholes_one {V : Finset Pt} {t : Pt} (htV : t ∉ V)
    (hesc : ∀ b, b ∉ V → Relation.ReflTransGen (MissAdj V) b t ∨
      ∃ b', Relation.ReflTransGen (MissAdj V) b b' ∧ ∀ p ∈ V, b'.1 < p.1) :
    KHoles V [t] := by
  refine ⟨by simpa using htV, fun b hb => ?_⟩
  rcases hesc b hb with h | h
  · exact Or.inl ⟨t, by simp, h⟩
  · exact Or.inr h

-- **B-1, several holes.** Two factors on `W` agreeing off the edges of `V`, with `D = 0` at one
-- point of each hole, have `D = 0` on every non-cell of `V`.
--
theorem solidFor_of_holes {V W : Finset Pt} {d : Pt → ℕ} {F H : Finset Edge} {as : List Pt}
    (hF : IsFactor W d F) (hH : IsFactor W d H)
    (hFH : ∀ e ∈ symmDiff F H, e.p ∈ V ∧ e.q ∈ V) (hk : KHoles V as)
    (h0 : ∀ a ∈ as, D F H a = 0) : SolidFor V F H := by
  intro c hc
  obtain ⟨x, y⟩ := c
  have corner : ∃ m, m ∉ V ∧ Around m (x, y) := by
    unfold IsCell at hc
    by_cases g1 : (x, y) ∈ V
    · by_cases g2 : (x + 1, y) ∈ V
      · by_cases g3 : (x, y + 1) ∈ V
        · refine ⟨(x + 1, y + 1), fun g4 => hc ⟨g1, g2, g3, g4⟩, ?_⟩
          simp [Around]
        · exact ⟨(x, y + 1), g3, by simp [Around]⟩
      · exact ⟨(x + 1, y), g2, by simp [Around]⟩
    · exact ⟨(x, y), g1, by simp [Around]⟩
  obtain ⟨m, hm, hmc⟩ := corner
  rw [D_aroundW hF hH hFH hm hmc]
  rcases hk.2 m hm with ⟨a, ha, hma⟩ | ⟨b, hmb, hb⟩
  · rw [D_chainW hF hH hFH hma, h0 a ha]
  · rw [D_chainW hF hH hFH hmb]
    exact pot_eq_zero_of_left (B := b.1) (fun e he => hb _ (hFH e he).1) b le_rfl

/-! ## The class bound -/

-- `D F G c` sums `±2` over the vertical edges of `F ⊕ G` left of `c` in its row; these are
-- edges of `V`, one per point of `V`.
--
theorem D_abs_le_card {V : Finset Pt} {F G : Finset Edge}
    (hFG : ∀ e ∈ symmDiff F G, IsEdge V e) (c : Pt) : |D F G c| ≤ 2 * V.card := by
  unfold D pot
  have hw : ∀ e, |wD F G e| ≤ 2 := by
    intro e; unfold wD wb; split_ifs <;> simp
  have hcard : ((symmDiff F G).filter (RowSel c)).card ≤ V.card := by
    apply Finset.card_le_card_of_injOn (fun e => e.p)
    · intro e he
      exact (hFG e (Finset.mem_filter.1 he).1).1
    · intro e1 he1 e2 he2 hp
      obtain ⟨d1, p1⟩ := e1
      obtain ⟨d2, p2⟩ := e2
      have r1 := (Finset.mem_filter.1 he1).2.1
      have r2 := (Finset.mem_filter.1 he2).2.1
      simp only at hp r1 r2
      subst hp r1 r2
      rfl
  calc |∑ e ∈ (symmDiff F G).filter (RowSel c), wD F G e|
      ≤ ∑ e ∈ (symmDiff F G).filter (RowSel c), |wD F G e| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ e ∈ (symmDiff F G).filter (RowSel c), (2 : ℤ) := Finset.sum_le_sum (fun e _ => hw e)
    _ = 2 * ((symmDiff F G).filter (RowSel c)).card := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ 2 * V.card := by exact_mod_cast Nat.mul_le_mul_left 2 hcard

/-! ## `D` vanishes off the box of `V` -/

section box

variable {V W : Finset Pt} {d : Pt → ℕ} {F G : Finset Edge}
  (hF : IsFactor W d F) (hG : IsFactor W d G) (hFG : ∀ e ∈ symmDiff F G, IsEdge V e)
  {x0 x1 y0 y1 : ℤ} (hbox : ∀ p ∈ V, x0 ≤ p.1 ∧ p.1 ≤ x1 ∧ y0 ≤ p.2 ∧ p.2 ≤ y1)
include hF hG hFG hbox

omit hF hG in
lemma D_zero_left (c : Pt) (hc : c.1 < x0) : D F G c = 0 := by
  unfold D
  apply pot_eq_zero_of_left (B := x0 - 1) _ c (by omega)
  intro e he
  have := (hbox _ (hFG e he).1).1
  omega

omit hF hG in
lemma D_zero_row {c : Pt} (hc : c.2 < y0 ∨ y1 ≤ c.2) : D F G c = 0 := by
  unfold D pot
  rw [Finset.filter_false_of_mem, Finset.sum_empty]
  intro e he hs
  obtain ⟨h1, h2, _⟩ := hs
  have i := hFG e he
  obtain ⟨d, p⟩ := e
  simp only at h1 h2
  subst h1
  have a := hbox _ i.1
  have b := hbox _ i.2
  simp only [Edge.q_v] at a b
  omega

lemma D_zero_right (c : Pt) (hc : x1 ≤ c.1) : D F G c = 0 := by
  obtain ⟨x, y⟩ := c
  rcases lt_or_ge y y0 with hy | hy
  · exact D_zero_row hFG hbox (Or.inl hy)
  · have : ∀ n : ℤ, y0 - 1 ≤ n → D F G (x, n) = 0 := by
      intro n hn
      induction n, hn using Int.leInduction with
      | base => exact D_zero_row hFG hbox (Or.inl (by simp))
      | succ n _ ih =>
        have j := D_jump hF hG (⟨.h, (x, n + 1)⟩ : Edge)
        have z : wD F G (⟨.h, (x, n + 1)⟩ : Edge) = 0 := by
          apply wD_supp
          intro he
          have := (hbox _ (hFG _ he).2).2.1
          simp at this
          simp only at hc
          omega
        rw [z] at j
        simp only [Edge.hi_mk, Edge.lo_h, add_sub_cancel_right] at j
        linarith
    exact this y (by omega)

-- Half of `D` changes by at most 1 per step, starting from 0 left of `x0`.
--
lemma D_half_abs (c : Pt) : |D F G c / 2| ≤ max 0 (c.1 - x0 + 1) := by
  obtain ⟨A, _⟩ := adm_of_factorW hF hG hFG
  obtain ⟨x, y⟩ := c
  rcases lt_or_ge x x0 with hx | hx
  · rw [D_zero_left hFG hbox _ hx]; simp
  · induction x, hx using Int.leInduction with
    | base =>
      have h1 := A ⟨.v, (x0, y)⟩
      have h2 := D_zero_left hFG hbox (x0 - 1, y) (by simp)
      simp only [Edge.hi_mk, Edge.lo_v, h2] at h1
      have h3 : (0 : ℤ) / 2 = 0 := by simp
      rw [h3] at h1
      rw [abs_le]
      unfold sv at h1
      constructor <;> split_ifs at h1 <;> rcases h1 with h | ⟨_, h⟩ <;> simp at * <;> omega
    | succ n hn ih =>
      have h1 := A ⟨.v, (n + 1, y)⟩
      simp only [Edge.hi_mk, Edge.lo_v, add_sub_cancel_right] at h1
      rw [abs_le] at ih ⊢
      unfold sv at h1
      constructor <;> split_ifs at h1 <;> rcases h1 with h | ⟨_, h⟩ <;> simp at * <;> omega

end box

/-! ## One component spans a narrow box -/

lemma conn_fst_between {V : Finset Pt} {H : Finset Edge} (hH : Inside V H) {p q : Pt}
    (h : Conn H p q) (hp : p ∈ V) :
    ∀ t : ℤ, min p.1 q.1 ≤ t → t ≤ max p.1 q.1 → ∃ r ∈ V, r.1 = t := by
  induction h with
  | refl =>
    intro t h1 h2
    exact ⟨p, hp, by simp at h1 h2; omega⟩
  | @tail b c _ hbc ih =>
    intro t h1 h2
    obtain ⟨e, he, hb⟩ := hbc
    have hi := hH e he
    have hc : c ∈ V := by rcases hb with ⟨_, h⟩ | ⟨h, _⟩ <;> [rw [← h]; rw [← h]] <;>
      [exact hi.2; exact hi.1]
    have hstep : b.1 - 1 ≤ c.1 ∧ c.1 ≤ b.1 + 1 := by
      obtain ⟨d, e0⟩ := e
      cases d <;> rcases hb with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> subst h3 h4 <;> simp <;> omega
    by_cases ht : min p.1 b.1 ≤ t ∧ t ≤ max p.1 b.1
    · exact ih t ht.1 ht.2
    · exact ⟨c, hc, by
        simp only [min_le_iff, le_max_iff, not_and_or, not_or, not_le] at ht h1 h2
        omega⟩

lemma conn_snd_between {V : Finset Pt} {H : Finset Edge} (hH : Inside V H) {p q : Pt}
    (h : Conn H p q) (hp : p ∈ V) :
    ∀ t : ℤ, min p.2 q.2 ≤ t → t ≤ max p.2 q.2 → ∃ r ∈ V, r.2 = t := by
  induction h with
  | refl =>
    intro t h1 h2
    exact ⟨p, hp, by simp at h1 h2; omega⟩
  | @tail b c _ hbc ih =>
    intro t h1 h2
    obtain ⟨e, he, hb⟩ := hbc
    have hi := hH e he
    have hc : c ∈ V := by rcases hb with ⟨_, h⟩ | ⟨h, _⟩ <;> [rw [← h]; rw [← h]] <;>
      [exact hi.2; exact hi.1]
    have hstep : b.2 - 1 ≤ c.2 ∧ c.2 ≤ b.2 + 1 := by
      obtain ⟨d, e0⟩ := e
      cases d <;> rcases hb with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> subst h3 h4 <;> simp <;> omega
    by_cases ht : min p.2 b.2 ≤ t ∧ t ≤ max p.2 b.2
    · exact ih t ht.1 ht.2
    · exact ⟨c, hc, by
        simp only [min_le_iff, le_max_iff, not_and_or, not_or, not_le] at ht h1 h2
        omega⟩

open Classical in
lemma conn_of_ncomp {V : Finset Pt} {H : Finset Edge} (hHam : ncomp V H = 1) {p q : Pt}
    (hp : p ∈ V) (hq : q ∈ V) : Conn H p q := by
  have h1 : cls V H p = cls V H q := by
    have hle : (V.image (cls V H)).card ≤ 1 := hHam.le
    rw [Finset.card_le_one] at hle
    exact hle _ (Finset.mem_image_of_mem _ hp) _ (Finset.mem_image_of_mem _ hq)
  have : q ∈ cls V H q := by
    unfold cls; rw [Finset.mem_filter]; exact ⟨hq, Conn.refl _ _⟩
  rw [← h1] at this
  unfold cls at this
  exact (Finset.mem_filter.1 this).2

open Classical in
theorem width_lt_card' {V : Finset Pt} {H : Finset Edge} (hH : Inside V H)
    (hHam : ncomp V H = 1) {p q : Pt} (hp : p ∈ V) (hq : q ∈ V) : q.1 - p.1 < V.card := by
  have hc := conn_of_ncomp hHam hp hq
  by_contra hlt
  push Not at hlt
  have hsub : Finset.Icc p.1 q.1 ⊆ V.image Prod.fst := by
    intro t ht
    rw [Finset.mem_Icc] at ht
    obtain ⟨r, hr, hrt⟩ := conn_fst_between hH hc hp t (by omega) (by omega)
    exact Finset.mem_image.2 ⟨r, hr, hrt⟩
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_image_le (s := V) (f := Prod.fst)
  rw [Int.card_Icc] at h1
  omega

open Classical in
theorem height_lt_card' {V : Finset Pt} {H : Finset Edge} (hH : Inside V H)
    (hHam : ncomp V H = 1) {p q : Pt} (hp : p ∈ V) (hq : q ∈ V) : q.2 - p.2 < V.card := by
  have hc := conn_of_ncomp hHam hp hq
  by_contra hlt
  push Not at hlt
  have hsub : Finset.Icc p.2 q.2 ⊆ V.image Prod.snd := by
    intro t ht
    rw [Finset.mem_Icc] at ht
    obtain ⟨r, hr, hrt⟩ := conn_snd_between hH hc hp t (by omega) (by omega)
    exact Finset.mem_image.2 ⟨r, hr, hrt⟩
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_image_le (s := V) (f := Prod.snd)
  rw [Int.card_Icc] at h1
  omega

end HP

end SolidGridHam
