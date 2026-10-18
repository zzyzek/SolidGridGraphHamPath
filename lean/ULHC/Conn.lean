/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.D

/-!
# Connectivity of an edge set, and flows of vertex chains

`Conn F a b`: `a` and `b` are joined by edges of `F`. Reachability is extracted as a chain
of lattice points (`List.Chain`), each step along an edge of `F`.

A chain also gives an integer *flow* on edges (net number of traversals in the edge's
`p → q` direction). Rotating flows by 90° turns them into crossing weights, and a closed
chain gives balanced weights. Its potential is a winding number. This is the only
topology used for the split rule in `Flip.lean`.
-/

namespace ULHC

def Adj (F : Finset Edge) (a b : Pt) : Prop :=
  ∃ e ∈ F, (e.p = a ∧ e.q = b) ∨ (e.p = b ∧ e.q = a)

def Conn (F : Finset Edge) : Pt → Pt → Prop := Relation.ReflTransGen (Adj F)

lemma Adj.symm {F : Finset Edge} {a b : Pt} (h : Adj F a b) : Adj F b a := by
  obtain ⟨e, he, h⟩ := h; exact ⟨e, he, h.symm⟩

lemma Conn.refl (F : Finset Edge) (a : Pt) : Conn F a a := Relation.ReflTransGen.refl

lemma Conn.trans {F : Finset Edge} {a b c : Pt} (h1 : Conn F a b) (h2 : Conn F b c) :
    Conn F a c := Relation.ReflTransGen.trans h1 h2

lemma Conn.symm {F : Finset Edge} {a b : Pt} (h : Conn F a b) : Conn F b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head hbc.symm ih

lemma Conn.of_adj {F : Finset Edge} {a b : Pt} (h : Adj F a b) : Conn F a b :=
  Relation.ReflTransGen.single h

lemma Adj.mono {F F' : Finset Edge} (hs : F ⊆ F') {a b : Pt} (h : Adj F a b) : Adj F' a b := by
  obtain ⟨e, he, h⟩ := h; exact ⟨e, hs he, h⟩

lemma Conn.mono {F F' : Finset Edge} (hs : F ⊆ F') {a b : Pt} (h : Conn F a b) :
    Conn F' a b := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail (hbc.mono hs)

lemma Conn.of_edge {F : Finset Edge} {e : Edge} (he : e ∈ F) : Conn F e.p e.q :=
  Conn.of_adj ⟨e, he, Or.inl ⟨rfl, rfl⟩⟩

/-! ## Unit steps -/

-- Two lattice points at distance one.
--
def Unit (a b : Pt) : Prop := |a.1 - b.1| + |a.2 - b.2| = 1

lemma Adj.unit {F : Finset Edge} {a b : Pt} (h : Adj F a b) : Unit a b := by
  obtain ⟨⟨d, p⟩, _, h⟩ := h
  unfold Unit
  cases d <;> rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h1 h2 <;> simp [Edge.q]

/-! ## Flows of chains -/

-- Flow of one step `u → v` on edge `e`.
--
def stepFlow (u v : Pt) (e : Edge) : ℤ :=
  (if e.p = u ∧ e.q = v then 1 else 0) - (if e.p = v ∧ e.q = u then 1 else 0)

-- Flow of the chain `u, l₀, l₁, …`.
--
def flowL : Pt → List Pt → Edge → ℤ
  | _, [], _ => 0
  | u, v :: l, e => stepFlow u v e + flowL v l e

-- Net outflow at `x`, read off the four edges at `x`.
--
def outflow (f : Edge → ℤ) (x : Pt) : ℤ := f (eR x) + f (eU x) - f (eL x) - f (eD x)

lemma unit_cases {u v : Pt} (h : Unit u v) :
    v = (u.1 + 1, u.2) ∨ v = (u.1 - 1, u.2) ∨ v = (u.1, u.2 + 1) ∨ v = (u.1, u.2 - 1) := by
  obtain ⟨u1, u2⟩ := u
  obtain ⟨v1, v2⟩ := v
  unfold Unit at h
  simp only [Prod.mk.injEq] at h ⊢
  rcases abs_cases (u1 - v1) with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
    rcases abs_cases (u2 - v2) with ⟨h2, _⟩ | ⟨h2, _⟩ <;> omega

-- An indicator of one edge, as a flow.
--
def oneE (a : Edge) (e : Edge) : ℤ := if e = a then 1 else 0

lemma stepFlow_right (u : Pt) : stepFlow u (u.1 + 1, u.2) = oneE ⟨.h, u⟩ := by
  obtain ⟨u1, u2⟩ := u
  funext e; obtain ⟨d, p1, p2⟩ := e
  cases d <;> simp [stepFlow, oneE, Edge.q] <;> omega

lemma stepFlow_left (u : Pt) :
    stepFlow u (u.1 - 1, u.2) = fun e => - oneE ⟨.h, (u.1 - 1, u.2)⟩ e := by
  obtain ⟨u1, u2⟩ := u
  funext e; obtain ⟨d, p1, p2⟩ := e
  cases d <;> simp [stepFlow, oneE, Edge.q] <;> omega

lemma stepFlow_up (u : Pt) : stepFlow u (u.1, u.2 + 1) = oneE ⟨.v, u⟩ := by
  obtain ⟨u1, u2⟩ := u
  funext e; obtain ⟨d, p1, p2⟩ := e
  cases d <;> simp [stepFlow, oneE, Edge.q] <;> omega

lemma stepFlow_down (u : Pt) :
    stepFlow u (u.1, u.2 - 1) = fun e => - oneE ⟨.v, (u.1, u.2 - 1)⟩ e := by
  obtain ⟨u1, u2⟩ := u
  funext e; obtain ⟨d, p1, p2⟩ := e
  cases d <;> simp [stepFlow, oneE, Edge.q] <;> omega

lemma outflow_oneE_h (a : Pt) (x : Pt) :
    outflow (oneE ⟨.h, a⟩) x = (if x = a then 1 else 0) - (if x = (a.1 + 1, a.2) then 1 else 0) := by
  obtain ⟨a1, a2⟩ := a
  obtain ⟨x1, x2⟩ := x
  simp only [outflow, oneE, eR, eU, eL, eD, Edge.mk.injEq, Prod.mk.injEq, reduceCtorEq,
    false_and, ite_false, sub_zero, add_zero]
  by_cases h1 : x1 = a1 <;> by_cases h2 : x2 = a2 <;> by_cases h3 : x1 = a1 + 1 <;>
    (simp [h1, h2, h3]; try omega)

lemma outflow_oneE_v (a : Pt) (x : Pt) :
    outflow (oneE ⟨.v, a⟩) x = (if x = a then 1 else 0) - (if x = (a.1, a.2 + 1) then 1 else 0) := by
  obtain ⟨a1, a2⟩ := a
  obtain ⟨x1, x2⟩ := x
  simp only [outflow, oneE, eR, eU, eL, eD, Edge.mk.injEq, Prod.mk.injEq, reduceCtorEq,
    false_and, ite_false, sub_zero, zero_add]
  by_cases h1 : x1 = a1 <;> by_cases h2 : x2 = a2 <;> by_cases h3 : x2 = a2 + 1 <;>
    (simp [h1, h2, h3]; try omega)

lemma outflow_neg (f : Edge → ℤ) (x : Pt) : outflow (fun e => - f e) x = - outflow f x := by
  unfold outflow; ring

lemma outflow_step (u v x : Pt) (h : Unit u v) :
    outflow (stepFlow u v) x = (if x = u then 1 else 0) - (if x = v then 1 else 0) := by
  obtain ⟨u1, u2⟩ := u
  rcases unit_cases h with h' | h' | h' | h' <;> subst h'
  · rw [stepFlow_right, outflow_oneE_h]
  · rw [stepFlow_left, outflow_neg, outflow_oneE_h]
    simp only [sub_add_cancel]; ring
  · rw [stepFlow_up, outflow_oneE_v]
  · rw [stepFlow_down, outflow_neg, outflow_oneE_v]
    simp only [sub_add_cancel]; ring

lemma outflow_add (f g : Edge → ℤ) (x : Pt) :
    outflow (fun e => f e + g e) x = outflow f x + outflow g x := by
  unfold outflow; ring

-- Conservation along a chain of unit steps: outflow `+1` at the start, `−1` at the end.
--
lemma outflow_flowL (u : Pt) (l : List Pt) (hc : List.IsChain Unit (u :: l)) (x : Pt) :
    outflow (flowL u l) x =
      (if x = u then 1 else 0) - (if x = (u :: l).getLast (by simp) then 1 else 0) := by
  induction l generalizing u with
  | nil =>
    simp only [flowL, outflow, List.getLast_singleton]
    by_cases h : x = u <;> simp [h]
  | cons v l ih =>
    rw [List.isChain_cons_cons] at hc
    have e1 : flowL u (v :: l) = fun e => stepFlow u v e + flowL v l e := rfl
    rw [e1, outflow_add, outflow_step u v x hc.1, ih v hc.2]
    rw [List.getLast_cons_cons]
    ring

end ULHC
