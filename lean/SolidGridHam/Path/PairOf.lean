/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import SolidGridHam.Path.Freeze

/-!
# The fixed pair of a bridge

In a frozen bridge region both `A = cellJ (r−2)` and `E = cellJ (r−1)` are alternating with dark
back and front (frame `a`), so each is a sink or a source, and across their shared side they are
opposite. The sink is the pair's top, the source its bottom (`pairOf`). Its corner pieces are read
from one corner on each dark side (`peq_of_bf`). This gives every pair field of `Cert`
(`pair_facts`).
-/

namespace SolidGridHam

namespace HP

open Finset Classical

-- The fixed pair of bridge `b` in state `H`.
--
def Bridge.pairOf (H : Finset Edge) (b : Bridge) : FixedPr :=
  if outArc H (b.cell (b.r - 2)) b.a = false then
    ⟨b.E, b.a.opp, back1 (b.cell (b.r - 2)) b.a, front1 (b.cell (b.r - 2)) b.a,
      back1 b.E b.a, front1 b.E b.a⟩
  else
    ⟨b.cell (b.r - 2), b.a, back1 b.E b.a, front1 b.E b.a,
      back1 (b.cell (b.r - 2)) b.a, front1 (b.cell (b.r - 2)) b.a⟩

section pairs

variable {H : Finset Edge}

lemma peq_of_bf' {q : Pt} {s' : Side} (hb : back q s' ∈ H) (hf : front q s' ∈ H) :
    ∀ u v, IsCorner u q → IsCorner v q → ¬ Conn H u v → PEq H u v (back1 q s') (front1 q s') :=
  fun _ _ hu hv huv => peq_of_bf hb hf hu hv huv

-- **The pair facts of a frozen bridge.**
--
theorem pair_facts {b : Bridge} (hR : RegionOK H b) (htwo : 2 ≤ b.r) (hev : b.r % 2 = 0) :
    PairOK H (b.pairOf H) ∧ (Alt H (b.pairOf H).top ∧ Alt H (b.pairOf H).bot) ∧
      sideEdge (b.pairOf H).bot (b.pairOf H).s ∈ H ∧
      (IsCorner (b.pairOf H).tx (b.pairOf H).top ∧ IsCorner (b.pairOf H).ty (b.pairOf H).top ∧
        IsCorner (b.pairOf H).bx (b.pairOf H).bot ∧ IsCorner (b.pairOf H).by' (b.pairOf H).bot) ∧
      ((b.pairOf H).top = b.cell (b.r - 2) ∨ (b.pairOf H).top = b.E) ∧
      ((b.pairOf H).bot = b.cell (b.r - 2) ∨ (b.pairOf H).bot = b.E) := by
  obtain ⟨q, a, r⟩ := b
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 2 := ⟨r - 2, by simp only at htwo; omega⟩
  obtain ⟨bk, lat, lat0, latE, fr, frA, frE, outer, cut0, cut0', cutE⟩ := hR
  simp only [Bridge.pairOf, Bridge.cell, Bridge.E, show m + 2 - 1 = m + 1 by omega,
    show m + 2 - 2 = m by omega] at *
  have meven : m % 2 = 0 := by omega
  -- `A` and `E`: dark back and front, light laterals.
  --
  have latA' : lat1 (cellJ q a m) a ∉ H ∧ lat2 (cellJ q a m) a ∉ H := by
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · subst h0; rw [cellJ_zero]; exact lat0
    · obtain ⟨a1, a2⟩ := lat m hpos (by omega)
      exact ⟨fun h => by have := a1.1 h; omega, fun h => by have := a2.1 h; omega⟩
  have bA : back (cellJ q a m) a ∈ H := by
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · subst h0; rw [cellJ_zero]; exact bk
    · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      rw [back_cellJ_succ]; exact (fr m' (by omega)).2 (by omega)
  have bE : back (cellJ q a (m + 1)) a ∈ H := by rw [back_cellJ_succ]; exact frA
  have altA := alt_of_bf bA frA latA'.1 latA'.2
  have altE := alt_of_bf bE frE latE.1 latE.2
  have hnb : nb (cellJ q a m) a = cellJ q a (m + 1) := nb_cellJ q a m
  have hnb' : nb (cellJ q a (m + 1)) a.opp = cellJ q a m := nb_cellJ_opp _ _ _
  have arcE : outArc H (cellJ q a (m + 1)) a.opp = !outArc H (cellJ q a m) a := by
    rw [← hnb, outArc_nb_opp]
  have pA := peq_of_bf' bA frA
  have pE := peq_of_bf' bE frE
  by_cases ho : outArc H (cellJ q a m) a = false
  · rw [ite_eq_left ho]; simp only [PairOK, FixedPr.top, hnb']
    have sA := sink_of_alt altA ho
    have sE := source_of_alt altE (s := a.opp) (by rw [arcE, ho]; rfl)
    refine ⟨⟨fun s _ => sA s, fun s _ => sE s, sE _, pA, pE⟩, ⟨altA, altE⟩, ?_,
      ⟨isCorner_back1 _ _, isCorner_front1 _ _, isCorner_back1 _ _, isCorner_front1 _ _⟩,
      by simp, by simp⟩
    unfold back at bE; exact bE
  · rw [ite_eq_right ho]; simp only [PairOK, FixedPr.top, hnb]
    have ho' : outArc H (cellJ q a m) a = true := by simpa using ho
    have sA := source_of_alt altA ho'
    have sE := sink_of_alt altE (s := a.opp) (by rw [arcE, ho']; rfl)
    refine ⟨⟨fun s _ => sE s, fun s _ => sA s, sA _, pE, pA⟩, ⟨altE, altA⟩, ?_,
      ⟨isCorner_back1 _ _, isCorner_front1 _ _, isCorner_back1 _ _, isCorner_front1 _ _⟩,
      by simp, by simp⟩
    exact frA

end pairs

end HP

end SolidGridHam
