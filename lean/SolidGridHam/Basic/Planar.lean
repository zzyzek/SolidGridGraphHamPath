/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import SolidGridHam.Basic.Conn

@[expose] public section

/-!
# The planar lemma for a cell

Cell `c = (x, y)` has corners `a = (x, y)`, `b = (x+1, y)`, `d = (x, y+1)`, `k = (x+1, y+1)`.
Let `G` be any edge set containing none of the four sides of `c`. Then `G` cannot join
`b` to `d` and `k` to `a` while keeping `a` and `b` apart.

Proof: close a `b → d` chain with the steps `d → a → b`. Its flow, rotated by 90°, is a
balanced weight, so it has a potential (a winding number). A `k → a` chain avoids the
closed chain until it reaches `a`. Along the way the potential at the current vertex
stays equal to its value at `k`, which is the value at the cell `c`. But both cells next
to `a`'s remaining `G`-edges have value one less.

This is used for the split rule: flipping an alternating cell whose two dark edges are on
one cycle splits that cycle.
-/

namespace SolidGridHam

open Finset

/-! ## Flow lemmas -/

lemma stepFlow_ne_zero {u v : Pt} {e : Edge} (h : stepFlow u v e ≠ 0) :
    (e.p = u ∧ e.q = v) ∨ (e.p = v ∧ e.q = u) := by
  unfold stepFlow at h
  by_contra hc
  push Not at hc
  rw [ite_eq_right (fun h' => hc.1 h'.1 h'.2), ite_eq_right (fun h' => hc.2 h'.1 h'.2)] at h
  simp at h

lemma flowL_ne_zero {u : Pt} {l : List Pt} {e : Edge} (h : flowL u l e ≠ 0) :
    e.p ∈ u :: l ∧ e.q ∈ u :: l := by
  induction l generalizing u with
  | nil => simp [flowL] at h
  | cons v l ih =>
    simp only [flowL] at h
    by_cases h1 : stepFlow u v e = 0
    · rw [h1, zero_add] at h
      obtain ⟨h2, h3⟩ := ih h
      exact ⟨List.mem_cons_of_mem _ h2, List.mem_cons_of_mem _ h3⟩
    · rcases stepFlow_ne_zero h1 with ⟨h2, h3⟩ | ⟨h2, h3⟩ <;> simp [h2, h3]

lemma flowL_append (u : Pt) (l₁ l₂ : List Pt) (e : Edge) :
    flowL u (l₁ ++ l₂) e = flowL u l₁ e + flowL ((u :: l₁).getLast (by simp)) l₂ e := by
  induction l₁ generalizing u with
  | nil => simp [flowL]
  | cons v l ih =>
    simp only [List.cons_append, flowL, ih v, List.getLast_cons_cons]
    ring

/-! ## Rotated flows as crossing weights -/

-- Crossing weight from a flow: horizontal edges keep their flow, vertical ones negate.
--
def rot (f : Edge → ℤ) (e : Edge) : ℤ :=
  match e.d with
  | .h => f e
  | .v => - f e

lemma rot_balanced {f : Edge → ℤ} (h : ∀ x, outflow f x = 0) : Balanced (rot f) := by
  intro x
  have := h x
  unfold outflow at this
  simp only [eD, eR, eL, eU] at this
  simp only [rot, eD, eR, eL, eU]
  linarith

-- Edges with their low end in a list.
--
def edgesAt (L : List Pt) : Finset Edge :=
  L.toFinset.biUnion (fun z => {eR z, eU z})

lemma rot_supp_of {f : Edge → ℤ} {L : List Pt} (h : ∀ e, f e ≠ 0 → e.p ∈ L) :
    Supp (edgesAt L) (rot f) := by
  intro e he
  have : f e = 0 := by
    by_contra hne
    apply he
    obtain ⟨d, p⟩ := e
    have hp := h _ hne
    simp only [edgesAt, Finset.mem_biUnion, List.mem_toFinset]
    refine ⟨p, hp, ?_⟩
    cases d <;> simp [eR, eU]
  unfold rot; cases e.d <;> simp [this]

/-! ## The potential is constant around points off the chain -/

section around

variable {E : Finset Edge} {w : Edge → ℤ} (hS : Supp E w) (hb : Balanced w)
include hS hb

-- If all four edges at `z` have weight 0, the four cells at `z` share the potential.
--
lemma pot_around {z : Pt} (h0 : w (eR z) = 0 ∧ w (eU z) = 0 ∧ w (eL z) = 0 ∧ w (eD z) = 0)
    {c : Pt} (hc : Around z c) : pot E w c = pot E w z := by
  obtain ⟨x, y⟩ := z
  have jR := pot_jump hS hb (eR (x, y))
  have jU := pot_jump hS hb (eU (x, y))
  have jL := pot_jump hS hb (eL (x, y))
  rw [h0.1] at jR
  rw [h0.2.1] at jU
  rw [h0.2.2.1] at jL
  simp only [eR, eU, eL, Edge.hi_mk, Edge.lo_h, Edge.lo_v] at jR jU jL
  obtain ⟨c1, c2⟩ := c
  obtain ⟨h1 | h1, h2 | h2⟩ := hc <;> simp only at h1 h2 <;> subst h1 h2 <;> linarith

end around

/-! ## Chains -/

lemma chain_reach {r : Pt → Pt → Prop} {u : Pt} {l : List Pt} (h : List.IsChain r (u :: l))
    {z : Pt} (hz : z ∈ u :: l) : Relation.ReflTransGen r u z := by
  induction l generalizing u with
  | nil =>
    simp at hz; subst hz; exact Relation.ReflTransGen.refl
  | cons v l ih =>
    rw [List.isChain_cons_cons] at h
    rcases List.mem_cons.1 hz with hz | hz
    · subst hz; exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.head h.1 (ih h.2 hz)

lemma unit_shared {u v : Pt} (h : Unit u v) :
    Around u (max u.1 v.1 - 1, max u.2 v.2 - 1) ∧ Around v (max u.1 v.1 - 1, max u.2 v.2 - 1) := by
  rcases unit_cases h with h' | h' | h' | h' <;> subst h' <;>
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> simp only [max_def] <;> split_ifs <;> omega

lemma adj_right_mem {G : Finset Edge} {x y : ℤ} (h : Adj G (x + 1, y) (x, y)) :
    bot (x, y) ∈ G := by
  obtain ⟨⟨d, p1, p2⟩, he, h⟩ := h
  cases d <;> rcases h with ⟨q1, q2⟩ | ⟨q1, q2⟩ <;>
    simp only [Edge.q, Prod.mk.injEq] at q1 q2 <;> try omega
  all_goals (obtain ⟨rfl, rfl⟩ : p1 = x ∧ p2 = y := by omega); exact he

lemma adj_up_mem {G : Finset Edge} {x y : ℤ} (h : Adj G (x, y + 1) (x, y)) :
    lft (x, y) ∈ G := by
  obtain ⟨⟨d, p1, p2⟩, he, h⟩ := h
  cases d <;> rcases h with ⟨q1, q2⟩ | ⟨q1, q2⟩ <;>
    simp only [Edge.q, Prod.mk.injEq] at q1 q2 <;> try omega
  all_goals (obtain ⟨rfl, rfl⟩ : p1 = x ∧ p2 = y := by omega); exact he

/-! ## The lemma -/

theorem planar_cell (G : Finset Edge) (x y : ℤ)
    (hb : bot (x, y) ∉ G) (hl : lft (x, y) ∉ G)
    (h1 : Conn G (x + 1, y) (x, y + 1)) (h2 : Conn G (x + 1, y + 1) (x, y))
    (h3 : ¬ Conn G (x, y) (x + 1, y)) : False := by
  -- Corners.
  set a : Pt := (x, y) with ha
  set b : Pt := (x + 1, y) with hbdef
  set d : Pt := (x, y + 1) with hd
  set k : Pt := (x + 1, y + 1) with hk
  obtain ⟨pl, hpc, hpl⟩ := List.exists_isChain_cons_of_relationReflTransGen h1
  obtain ⟨ql, hqc, hql⟩ := List.exists_isChain_cons_of_relationReflTransGen h2
  -- The closed chain b → … → d → a → b and its flow.
  let f : Edge → ℤ := fun e => flowL b pl e + stepFlow d a e + stepFlow a b e
  let Lst : List Pt := a :: d :: b :: pl
  have hunit_p : List.IsChain Unit (b :: pl) := hpc.imp (fun _ _ h => h.unit)
  have hout : ∀ z, outflow f z = 0 := by
    intro z
    have e1 : f = fun e => (fun e => flowL b pl e + stepFlow d a e) e + stepFlow a b e := rfl
    rw [e1, outflow_add, outflow_add, outflow_flowL b pl hunit_p,
      outflow_step d a z (by simp [Unit, d, a]), outflow_step a b z (by simp [Unit, a, b]), hpl]
    ring
  have hfmem : ∀ e, f e ≠ 0 → e.p ∈ Lst ∧ e.q ∈ Lst := by
    intro e he
    by_cases f1 : flowL b pl e = 0
    · by_cases f2 : stepFlow d a e = 0
      · have f3 : stepFlow a b e ≠ 0 := by simp only [f] at he; rw [f1, f2] at he; simpa using he
        rcases stepFlow_ne_zero f3 with ⟨q1, q2⟩ | ⟨q1, q2⟩ <;> simp [Lst, q1, q2]
      · rcases stepFlow_ne_zero f2 with ⟨q1, q2⟩ | ⟨q1, q2⟩ <;> simp [Lst, q1, q2]
    · obtain ⟨q1, q2⟩ := flowL_ne_zero f1
      exact ⟨List.mem_cons_of_mem _ (List.mem_cons_of_mem _ q1),
        List.mem_cons_of_mem _ (List.mem_cons_of_mem _ q2)⟩
  have hS : Supp (edgesAt Lst) (rot f) := rot_supp_of (fun e he => (hfmem e he).1)
  have hB : Balanced (rot f) := rot_balanced hout
  let P : Pt → ℤ := pot (edgesAt Lst) (rot f)
  -- Off the closed chain, the four edges at a point carry no flow.
  have hzero : ∀ z, z ∉ Lst →
      rot f (eR z) = 0 ∧ rot f (eU z) = 0 ∧ rot f (eL z) = 0 ∧ rot f (eD z) = 0 := by
    intro z hz
    have g : ∀ e : Edge, (e.p = z ∨ e.q = z) → rot f e = 0 := by
      intro e hez
      have : f e = 0 := by
        by_contra hne
        obtain ⟨q1, q2⟩ := hfmem e hne
        rcases hez with hez | hez
        · rw [hez] at q1; exact hz q1
        · rw [hez] at q2; exact hz q2
      unfold rot; cases e.d <;> simp [this]
    refine ⟨g _ (Or.inl rfl), g _ (Or.inl rfl), g _ (Or.inr ?_), g _ (Or.inr ?_)⟩ <;>
      simp [eL, eD, Edge.q]
  -- Classes: the closed chain minus `a` lies in `b`'s class; the chain from `k` in `a`'s.
  have hLb : ∀ z ∈ Lst, z ≠ a → Conn G b z := by
    intro z hz hza
    simp only [Lst, List.mem_cons] at hz
    rcases hz with hz | hz | hz | hz
    · exact absurd hz hza
    · rw [hz]; exact h1
    · rw [hz]; exact Conn.refl _ _
    · exact chain_reach hpc (List.mem_cons_of_mem _ hz)
  have hqa : ∀ z ∈ k :: ql, Conn G z a := by
    intro z hz
    have hkz : Conn G k z := chain_reach hqc hz
    exact Conn.trans hkz.symm h2
  have hmeet : ∀ z ∈ k :: ql, z ∈ Lst → z = a := by
    intro z hzq hzL
    by_contra hza
    exact h3 (Conn.trans (hqa z hzq).symm (hLb z hzL hza).symm)
  have hkL : k ∉ Lst := by
    intro hkL
    have := hmeet k (List.mem_cons_self) hkL
    simp [k, a] at this
  have haL : a ∈ Lst := List.mem_cons_self
  -- Walk the chain from `k` until it first meets the closed chain.
  have exit : ∀ (u : Pt) (l : List Pt), List.IsChain (Adj G) (u :: l) → u ∉ Lst →
      (u :: l).getLast (by simp) ∈ Lst →
      ∃ z z', Adj G z z' ∧ z ∉ Lst ∧ z' ∈ Lst ∧ z' ∈ u :: l ∧ P z = P u := by
    intro u l
    induction l generalizing u with
    | nil => intro _ hu hlast; simp at hlast; exact absurd hlast hu
    | cons v l ih =>
      intro hc hu hlast
      rw [List.isChain_cons_cons] at hc
      by_cases hv : v ∈ Lst
      · exact ⟨u, v, hc.1, hu, hv, by simp, rfl⟩
      · rw [List.getLast_cons_cons] at hlast
        obtain ⟨z, z', hzz, hz, hz', hmem, hP⟩ := ih v hc.2 hv hlast
        refine ⟨z, z', hzz, hz, hz', List.mem_cons_of_mem _ hmem, ?_⟩
        rw [hP]
        obtain ⟨s1, s2⟩ := unit_shared hc.1.unit
        have := pot_around hS hB (hzero u hu) s1
        have := pot_around hS hB (hzero v hv) s2
        simp only [P]
        linarith
  obtain ⟨z, z', hzz, hz, hz', hmem, hP⟩ := exit k ql hqc hkL (by rw [hql]; exact haL)
  have hz'a : z' = a := hmeet z' hmem hz'
  subst hz'a
  -- Values next to `a`.
  have aNotPl : a ∉ b :: pl := by
    intro h
    exact h3 (Conn.symm (chain_reach hpc h))
  have fl : f (lft (x, y)) = -1 := by
    have : flowL b pl (lft (x, y)) = 0 := by
      by_contra hne
      exact aNotPl (flowL_ne_zero hne).1
    show flowL b pl (lft (x, y)) + stepFlow d a (lft (x, y)) + stepFlow a b (lft (x, y)) = -1
    rw [this]; simp [stepFlow, lft, Edge.q, a, b, d]
  have fb : f (bot (x, y)) = 1 := by
    have : flowL b pl (bot (x, y)) = 0 := by
      by_contra hne
      exact aNotPl (flowL_ne_zero hne).1
    show flowL b pl (bot (x, y)) + stepFlow d a (bot (x, y)) + stepFlow a b (bot (x, y)) = 1
    rw [this]; simp [stepFlow, bot, Edge.q, a, b, d]
  have jl := pot_jump hS hB (lft (x, y))
  have jb := pot_jump hS hB (bot (x, y))
  simp only [lft, bot, Edge.hi_mk, Edge.lo_v, Edge.lo_h] at jl jb
  simp only [rot] at jl jb
  rw [show (⟨.v, (x, y)⟩ : Edge) = lft (x, y) from rfl, fl] at jl
  rw [show (⟨.h, (x, y)⟩ : Edge) = bot (x, y) from rfl, fb] at jb
  have hPk : P k = P (x, y) := (pot_around hS hB (hzero k hkL) (by simp [Around, k])).symm
  -- `z` is the left or lower neighbour of `a`.
  have hzv : z = (x - 1, y) ∨ z = (x, y - 1) := by
    obtain ⟨z1, z2⟩ := z
    rcases unit_cases hzz.unit with h | h | h | h <;>
      simp only [a, Prod.mk.injEq] at h
    · left; simp only [Prod.mk.injEq]; omega
    · exfalso; apply hb
      have e1 : z1 = x + 1 := by omega
      have e2 : z2 = y := by omega
      subst e1 e2; exact adj_right_mem hzz
    · right; simp only [Prod.mk.injEq]; omega
    · exfalso; apply hl
      have e1 : z1 = x := by omega
      have e2 : z2 = y + 1 := by omega
      subst e1 e2; exact adj_up_mem hzz
  rcases hzv with hzv | hzv <;> subst hzv <;> simp only [P] at hP hPk <;> linarith

end SolidGridHam
