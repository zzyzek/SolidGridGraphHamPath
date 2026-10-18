/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import SolidGridHam.Path.LoopF
public import SolidGridHam.Algorithm

@[expose] public section

/-!
# Two phantoms: the deletion walk (docs/ENDPOINTS_GENERAL.md, route A2)

`twoPhantomTest` (the fast `hpSheffC2`) needs both endpoints to have a missing neighbour, to be Far (king
distance at least 2), and to carry phantoms that are not opposed.
Otherwise delete `t` and branch over its neighbours `w ≠ s` (`del_iff`): `w` gets the deleted point
as its phantom. The walk stops once `t` is Far from `s` (king distance ≥ 2) with a usable phantom
(not opposed to `s`'s); measure `wmu` ≤ 11.
-/

namespace SolidGridHam

namespace HP

open Finset Classical

section del

variable {V : Finset Pt} {s t : Pt}

-- **Deleting an endpoint.** With at least three points, `V` has a Hamiltonian `s`–`t` path iff
-- `V.erase t` has one from `s` to a neighbour `w ≠ s` of `t`.
--
theorem del_iff (hst : s ≠ t) (htV : t ∈ V) (h3 : 3 ≤ V.card) :
    (∃ H, IsFactor V (dST s t) H ∧ ncomp V H = 1) ↔
      ∃ x ∈ nbrsL t, x.1 ∈ V ∧ x.1 ≠ s ∧
        ∃ H, IsFactor (V.erase t) (dST s x.1) H ∧ ncomp (V.erase t) H = 1 := by
  constructor
  · rintro ⟨H, hH, hHam⟩
    have hdt : deg H t = 1 := by rw [hH.2 t htV]; unfold dST; simp
    rw [DF.deg_eq_card] at hdt
    obtain ⟨e, he⟩ := Finset.card_eq_one.1 hdt
    have hem : e ∈ H.filter (fun e => e.p = t ∨ e.q = t) := by
      rw [he]; exact Finset.mem_singleton_self e
    obtain ⟨heH, het⟩ := Finset.mem_filter.1 hem
    obtain ⟨w, hew⟩ : ∃ w, (e.p = t ∧ e.q = w) ∨ (e.p = w ∧ e.q = t) := by
      rcases het with h | h
      · exact ⟨e.q, Or.inl ⟨h, rfl⟩⟩
      · exact ⟨e.p, Or.inr ⟨rfl, h⟩⟩
    have hwV : w ∈ V := by
      have := Inside.of_factor hH e heH
      rcases hew with ⟨_, h⟩ | ⟨h, _⟩
      · rw [← h]; exact this.2
      · rw [← h]; exact this.1
    have hsw : s ≠ w := by
      intro hsw
      subst hsw
      obtain ⟨z, hz, hzs, hzt⟩ := three_of_card h3 s t
      have endS : e.p = s ∨ e.q = s := by
        rcases hew with ⟨_, h⟩ | ⟨h, _⟩
        · exact Or.inr h
        · exact Or.inl h
      have d0 : ∀ x, (x = s ∨ x = t) → deg (H.erase e) x = 0 := by
        intro x hx
        rcases hx with rfl | rfl
        · have h1 := DF.deg_erase_end heH endS
          rw [hH.2 x hwV] at h1; unfold dST at h1; simp at h1; omega
        · have h1 := DF.deg_erase_end heH het
          rw [hH.2 x htV] at h1; unfold dST at h1; simp at h1; omega
      have reach : ∀ y, Conn H s y → y = s ∨ y = t := by
        intro y hy
        induction hy with
        | refl => exact Or.inl rfl
        | @tail a b _ hab ih =>
          obtain ⟨f, hf, hfe⟩ := hab
          by_cases hff : f = e
          · subst hff
            rcases hfe with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hew with ⟨h3, h4⟩ | ⟨h3, h4⟩
            · exact Or.inl (h2.symm.trans h4)
            · exact Or.inr (h2.symm.trans h4)
            · exact Or.inr (h1.symm.trans h3)
            · exact Or.inl (h1.symm.trans h3)
          · have hf' : f ∈ H.erase e := Finset.mem_erase.2 ⟨hff, hf⟩
            have ha : f.p = a ∨ f.q = a := by
              rcases hfe with ⟨h1, _⟩ | ⟨_, h2⟩
              · exact Or.inl h1
              · exact Or.inr h2
            have := one_le_deg hf' ha
            rw [d0 a ih] at this; omega
      rcases reach z (conn_of_ncomp_one hHam hwV hz) with h | h
      · exact hzs h
      · exact hzt h
    obtain ⟨hH', hHam'⟩ := delete_down htV hwV hew hst hsw hH hHam heH
    exact ⟨(w, e), mem_nbrsL hew, hwV, Ne.symm hsw, _, hH', hHam'⟩
  · rintro ⟨x, hx, hxV, hxs, H', hH', hHam'⟩
    obtain ⟨hH, hHam, _⟩ := delete_up htV hxV (nbrsL_ends hx) hst (Ne.symm hxs) hH' hHam'
    exact ⟨_, hH, hHam⟩

-- **Two points.** With `V = {s, t}`, a Hamiltonian `s`–`t` path exists iff they are neighbours.
--
theorem hp_two (hst : s ≠ t) (hsV : s ∈ V) (htV : t ∈ V) (h2 : V.card ≤ 2) :
    (∃ H, IsFactor V (dST s t) H ∧ ncomp V H = 1) ↔ ∃ x ∈ nbrsL t, x.1 = s := by
  have hVst : V = {s, t} := by
    symm; apply Finset.eq_of_subset_of_card_le
    · intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl <;> assumption
    · rw [Finset.card_pair hst]; exact h2
  constructor
  · rintro ⟨H, hH, _⟩
    have hdt : deg H t = 1 := by rw [hH.2 t htV]; unfold dST; simp
    rw [DF.deg_eq_card] at hdt
    obtain ⟨e, he⟩ := Finset.card_eq_one.1 hdt
    have hem : e ∈ H.filter (fun e => e.p = t ∨ e.q = t) := by
      rw [he]; exact Finset.mem_singleton_self e
    obtain ⟨heH, het⟩ := Finset.mem_filter.1 hem
    obtain ⟨w, hew⟩ : ∃ w, (e.p = t ∧ e.q = w) ∨ (e.p = w ∧ e.q = t) := by
      rcases het with h | h
      · exact ⟨e.q, Or.inl ⟨h, rfl⟩⟩
      · exact ⟨e.p, Or.inr ⟨rfl, h⟩⟩
    have hwV : w ∈ V := by
      have := Inside.of_factor hH e heH
      rcases hew with ⟨_, h⟩ | ⟨h, _⟩
      · rw [← h]; exact this.2
      · rw [← h]; exact this.1
    have hwt : w ≠ t := (edge_ne hew).symm
    have hws : w = s := by
      rw [hVst] at hwV; simp only [Finset.mem_insert, Finset.mem_singleton] at hwV
      exact hwV.resolve_right hwt
    exact ⟨(w, e), mem_nbrsL hew, hws⟩
  · rintro ⟨x, hx, hxs⟩
    have hew := nbrsL_ends hx
    rw [hxs] at hew
    have hes : x.2.p = s ∨ x.2.q = s := by
      rcases hew with ⟨_, h⟩ | ⟨h, _⟩
      · exact Or.inr h
      · exact Or.inl h
    have het : x.2.p = t ∨ x.2.q = t := by
      rcases hew with ⟨h, _⟩ | ⟨_, h⟩
      · exact Or.inl h
      · exact Or.inr h
    refine ⟨{x.2}, ⟨fun e he => ?_, fun z hz => ?_⟩, ?_⟩
    · rw [Finset.mem_singleton] at he; subst he
      rcases hew with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · unfold IsEdge; rw [h1, h2]; exact ⟨htV, hsV⟩
      · unfold IsEdge; rw [h1, h2]; exact ⟨hsV, htV⟩
    · rw [hVst] at hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      have hnot : x.2 ∉ (∅ : Finset Edge) := by simp
      rcases hz with rfl | rfl
      · rw [show ({x.2} : Finset Edge) = insert x.2 ∅ from rfl, DF.deg_insert_end hnot hes,
          DF.deg_empty]; unfold dST; simp
      · rw [show ({x.2} : Finset Edge) = insert x.2 ∅ from rfl, DF.deg_insert_end hnot het,
          DF.deg_empty]; unfold dST; simp
    · apply ncomp_one_of_conn htV
      intro a ha b hb
      have hst' : Conn ({x.2} : Finset Edge) s t := by
        apply Relation.ReflTransGen.single
        refine ⟨x.2, Finset.mem_singleton_self _, ?_⟩
        rcases hew with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inr ⟨h1, h2⟩
        · exact Or.inl ⟨h1, h2⟩
      rw [hVst] at ha hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact Conn.refl _ _
      · exact hst'
      · exact hst'.symm
      · exact Conn.refl _ _

end del

lemma isFar_iff {t s : Pt} : isFar t s = true ↔ Far t s := by
  unfold isFar Far Close1
  simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true', Bool.and_eq_false_iff,
    decide_eq_false_iff_not, not_and_or]

lemma opp_close {a ma b mb : Pt} (h : Opp a ma b mb) : Close a b := by
  unfold Opp at h; unfold Close
  simp only [abs_le] at h ⊢
  rcases h with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ <;> omega

-- The phantom of the first out-vertex is at king distance 3 from the second.
--
lemma opp_far_a {a ma b mb : Pt} (h : Opp a ma b mb) : ¬ Close ma b := by
  unfold Opp at h; unfold Close
  simp only [abs_le, not_and_or, not_le]
  rcases h with ⟨h1, _, rfl, _⟩ | ⟨h1, _, rfl, _⟩ | ⟨h1, _, rfl, _⟩ | ⟨h1, _, rfl, _⟩ <;>
    simp only <;> omega

-- The phantom of the second out-vertex is at king distance 3 from the first.
--
lemma opp_far_b {a ma b mb : Pt} (h : Opp a ma b mb) : ¬ Close a mb :=
  fun hc => opp_far_a (opp_symm h) (close_comm hc)

lemma ends_close1 {e : Edge} {u v : Pt} (h : Ends e u v) : |u.1 - v.1| ≤ 1 ∧ |u.2 - v.2| ≤ 1 := by
  obtain ⟨d, ⟨x, y⟩⟩ := e
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> cases d <;> simp only [Edge.q] at h1 h2 <;>
    rw [← h1, ← h2] <;> simp

-- Two points with a common lattice neighbour are within king distance 2.
--
lemma close_of_common {e f : Edge} {t s x : Pt} (h1 : Ends e t x) (h2 : Ends f s x) : Close t s := by
  have c1 := ends_close1 h1
  have c2 := ends_close1 h2
  unfold Close
  simp only [abs_le] at c1 c2 ⊢
  omega

-- Points of `V` other than `s` within king distance 2 of `s`.
--
noncomputable def ballc (V : Finset Pt) (s : Pt) : ℕ := (V.filter (fun x => x ≠ s ∧ Close x s)).card

lemma ballc_le (V : Finset Pt) (s : Pt) : ballc V s ≤ 24 := by
  set B := ((Finset.Icc (s.1 - 2) (s.1 + 2)) ×ˢ (Finset.Icc (s.2 - 2) (s.2 + 2))).erase s with hB
  have hsub : V.filter (fun x => x ≠ s ∧ Close x s) ⊆ B := by
    intro x hx
    simp only [Finset.mem_filter] at hx
    obtain ⟨_, hxs, h1, h2⟩ := hx
    rw [abs_le] at h1 h2
    rw [hB, Finset.mem_erase, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
    exact ⟨hxs, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
  have hcard : B.card = 24 := by
    rw [hB, Finset.card_erase_of_mem (by simp), Finset.card_product, Int.card_Icc, Int.card_Icc]
    simp only [show s.1 + 2 + 1 - (s.1 - 2) = 5 by ring, show s.2 + 2 + 1 - (s.2 - 2) = 5 by ring]
    rfl
  unfold ballc
  rw [← hcard]; exact Finset.card_le_card hsub

-- Points of `V` other than `s` within king distance 1 of `s` (the ring).
--
noncomputable def ringc (V : Finset Pt) (s : Pt) : ℕ := (V.filter (fun x => x ≠ s ∧ Close1 x s)).card

lemma ringc_le (V : Finset Pt) (s : Pt) : ringc V s ≤ 8 := by
  set B := ((Finset.Icc (s.1 - 1) (s.1 + 1)) ×ˢ (Finset.Icc (s.2 - 1) (s.2 + 1))).erase s with hB
  have hsub : V.filter (fun x => x ≠ s ∧ Close1 x s) ⊆ B := by
    intro x hx
    simp only [Finset.mem_filter] at hx
    obtain ⟨_, hxs, h1, h2⟩ := hx
    rw [abs_le] at h1 h2
    rw [hB, Finset.mem_erase, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
    exact ⟨hxs, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
  have hcard : B.card = 8 := by
    rw [hB, Finset.card_erase_of_mem (by simp), Finset.card_product, Int.card_Icc, Int.card_Icc]
    simp only [show s.1 + 1 + 1 - (s.1 - 1) = 3 by ring, show s.2 + 1 + 1 - (s.2 - 1) = 3 by ring]
    rfl
  unfold ringc
  rw [← hcard]; exact Finset.card_le_card hsub

lemma ringc_erase_le (V : Finset Pt) (s t : Pt) : ringc (V.erase t) s ≤ ringc V s := by
  unfold ringc
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.erase_subset _ _))

lemma ringc_erase_lt {V : Finset Pt} {s t : Pt} (htV : t ∈ V) (hts : t ≠ s) (hc : Close1 t s) :
    ringc (V.erase t) s < ringc V s := by
  unfold ringc
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset (Finset.filter_subset_filter _ (Finset.erase_subset _ _))]
  exact ⟨t, Finset.mem_filter.2 ⟨htV, hts, hc⟩, by simp⟩

-- The walk measure.
--
noncomputable def wmu (V : Finset Pt) (s q t : Pt) : ℕ :=
  ringc V s + (if (∃ x ∈ nbrsL t, x.1 ∉ V) then 0 else 2) +
    (if (∃ x ∈ nbrsL t, isUsablePhantom V s q t x = true) then 0 else 1)

-- The walk's invariant.
--
structure WI (V : Finset Pt) (s q : Pt) (e1 : Edge) (t : Pt) : Prop where
  solid : Solid V
  sV : s ∈ V
  tV : t ∈ V
  st : s ≠ t
  qV : q ∉ V
  e1 : Ends e1 s q
  miss : ∃ m, m ∉ V ∧ |m.1 - t.1| ≤ 1 ∧ |m.2 - t.2| ≤ 1

section walk

variable {s q : Pt} {e1 : Edge}

lemma wi_step {V : Finset Pt} {t : Pt} (hI : WI V s q e1 t) {x : Pt × Edge} (hx : x ∈ nbrsL t)
    (hxV : x.1 ∈ V) (hxs : x.1 ≠ s) : WI (V.erase t) s q e1 x.1 := by
  obtain ⟨m, hm, hm1, hm2⟩ := hI.miss
  have hends := nbrsL_ends hx
  have htx : t ≠ x.1 := edge_ne hends
  have hc := ends_close1 (show Ends x.2 t x.1 from hends)
  refine ⟨solid_erase hI.tV hI.solid hm hm1 hm2, Finset.mem_erase.2 ⟨hI.st, hI.sV⟩,
    Finset.mem_erase.2 ⟨htx.symm, hxV⟩, Ne.symm hxs,
    fun h => hI.qV (Finset.mem_of_mem_erase h), hI.e1, t, by simp, ?_, ?_⟩
  · exact hc.1
  · exact hc.2

lemma wmu_step {V : Finset Pt} {t : Pt} (hI : WI V s q e1 t) {x : Pt × Edge} (hx : x ∈ nbrsL t)
    (hcase : ¬ Far t s ∨ ¬ (∃ y ∈ nbrsL t, isUsablePhantom V s q t y = true)) :
    wmu (V.erase t) s q x.1 < wmu V s q t := by
  have hends := nbrsL_ends hx
  have hts : t ≠ s := hI.st.symm
  have hx2 : Ends x.2 x.1 t := by rcases hends with h | h; exacts [Or.inr h, Or.inl h]
  have hmem : (t, x.2) ∈ nbrsL x.1 := mem_nbrsL (by rcases hends with h | h; exacts [Or.inr h, Or.inl h])
  have hlat : ∃ y ∈ nbrsL x.1, y.1 ∉ V.erase t := ⟨(t, x.2), hmem, by simp⟩
  have hring := ringc_erase_le V s t
  -- if `t` is within king distance 2 of `s`, the deleted `t` is a usable phantom of `x.1`
  have hgood : Close t s → ∃ y ∈ nbrsL x.1, isUsablePhantom (V.erase t) s q x.1 y = true := by
    intro hc
    refine ⟨(t, x.2), hmem, ?_⟩
    simp only [isUsablePhantom, phantomsOpposed, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
      decide_eq_false_iff_not]
    exact ⟨⟨by simp, fun h => hI.qV (h ▸ hI.tV)⟩, fun hop => opp_far_a hop hc⟩
  unfold wmu
  rw [ite_eq_left hlat]
  by_cases hc : Close t s
  · rw [ite_eq_left (hgood hc)]
    rcases hcase with hf | hg
    · have hc1 : Close1 t s := by unfold Far at hf; push Not at hf; exact hf.2
      have := ringc_erase_lt hI.tV hts hc1
      omega
    · rw [ite_eq_right hg]; split_ifs <;> omega
  · -- far from `s`: no usable phantom means no missing lattice neighbour at all
    have hf : Far t s := Or.inr (fun h1 => hc (by unfold Close1 at h1; unfold Close; omega))
    have hg : ¬ (∃ y ∈ nbrsL t, isUsablePhantom V s q t y = true) := hcase.resolve_left (not_not.2 hf)
    have hno : ¬ (∃ y ∈ nbrsL t, y.1 ∉ V) := by
      rintro ⟨y, hy, hyV⟩
      apply hg
      refine ⟨y, hy, ?_⟩
      simp only [isUsablePhantom, phantomsOpposed, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
        decide_eq_false_iff_not]
      refine ⟨⟨hyV, fun h => hc ?_⟩, fun hop => hc (opp_close hop)⟩
      have hye := nbrsL_ends hy
      rw [h] at hye
      exact close_of_common hye hI.e1
    rw [ite_eq_right hno, ite_eq_right hg]
    split_ifs <;> omega

-- **The walk is correct** when its fuel exceeds the measure.
--
theorem boundaryEndpointsWalk_correct :
    ∀ n V t, WI V s q e1 t → wmu V s q t < n →
      (boundaryEndpointsWalk s q e1 n V t = true ↔ ∃ H, IsFactor V (dST s t) H ∧ ncomp V H = 1) := by
  intro n
  induction n with
  | zero => intro V t _ h; omega
  | succ n ih =>
    intro V t hI hmu
    -- the deletion branch
    have hdel : (¬ Far t s ∨ ¬ (∃ y ∈ nbrsL t, isUsablePhantom V s q t y = true)) → 3 ≤ V.card →
        ((nbrsL t).any (fun x => decide (x.1 ∈ V) && decide (x.1 ≠ s) &&
          boundaryEndpointsWalk s q e1 n (V.erase t) x.1) = true ↔
          ∃ H, IsFactor V (dST s t) H ∧ ncomp V H = 1) := by
      intro hcase h3
      rw [del_iff hI.st hI.tV h3, List.any_eq_true]
      constructor
      · rintro ⟨x, hx, hb⟩
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
        obtain ⟨⟨hxV, hxs⟩, hw⟩ := hb
        have hmu' := wmu_step hI hx hcase
        exact ⟨x, hx, hxV, hxs, (ih _ _ (wi_step hI hx hxV hxs) (by omega)).1 hw⟩
      · rintro ⟨x, hx, hxV, hxs, hH⟩
        have hmu' := wmu_step hI hx hcase
        refine ⟨x, hx, ?_⟩
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨⟨hxV, hxs⟩, (ih _ _ (wi_step hI hx hxV hxs) (by omega)).2 hH⟩
    simp only [boundaryEndpointsWalk]
    by_cases h2 : V.card ≤ 2
    · rw [ite_eq_left h2, hp_two hI.st hI.sV hI.tV h2, List.any_eq_true]
      simp only [decide_eq_true_eq]
    · rw [ite_eq_right h2]
      have h3 : 3 ≤ V.card := by omega
      rcases hf : (nbrsL t).find? (isUsablePhantom V s q t) with _ | x
      · simp only
        have hnone : ¬ (∃ y ∈ nbrsL t, isUsablePhantom V s q t y = true) := by
          rintro ⟨y, hy, hgy⟩
          have := List.find?_eq_none.1 hf y hy
          rw [hgy] at this; exact this rfl
        exact hdel (Or.inr hnone) h3
      · simp only
        have hm := List.mem_of_find?_eq_some hf
        have hp := List.find?_some hf
        simp only [isUsablePhantom, phantomsOpposed, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
          decide_eq_false_iff_not] at hp
        obtain ⟨⟨hpV, hpq⟩, hno⟩ := hp
        split_ifs with hfar
        · have hfr := isFar_iff.1 hfar
          have he0 : Ends x.2 t x.1 := nbrsL_ends hm
          rw [twoPhantomTest_eq hI.st hI.sV hI.tV hpV hI.qV hpq he0 hI.e1 ⟨hfr, hno⟩]
          exact hpSheffC2_correct hI.st hI.sV hI.tV hpV hI.qV hpq he0 hI.e1 ⟨hfr, hno⟩ hI.solid
        · exact hdel (Or.inl (fun h => hfar (isFar_iff.2 h))) h3

end walk

lemma wmu_le (V : Finset Pt) (s q t : Pt) : wmu V s q t ≤ 11 := by
  have := ringc_le V s
  unfold wmu; split_ifs <;> omega

section boundaryEndpoints

variable {V : Finset Pt} {s t : Pt}

theorem boundaryEndpoints_correct (hs : Solid V) (hst : s ≠ t) (hsV : s ∈ V) (htV : t ∈ V)
    (hms : ∃ m, m ∉ V ∧ |m.1 - s.1| ≤ 1 ∧ |m.2 - s.2| ≤ 1)
    (hmt : ∃ m, m ∉ V ∧ |m.1 - t.1| ≤ 1 ∧ |m.2 - t.2| ≤ 1) :
    boundaryEndpoints V s t = true ↔ ∃ H, IsFactor V (dST s t) H ∧ ncomp V H = 1 := by
  unfold boundaryEndpoints
  by_cases h2 : V.card ≤ 2
  · rw [ite_eq_left h2, hp_two hst hsV htV h2, List.any_eq_true]
    simp only [decide_eq_true_eq]
  rw [ite_eq_right h2]
  have h3 : 3 ≤ V.card := by omega
  rcases hf : (nbrsL s).find? (fun x => decide (x.1 ∉ V)) with _ | x
  · simp only [hf]
    -- delete `s` first
    obtain ⟨m, hm, hm1, hm2⟩ := hms
    rw [hp_swap, del_iff (Ne.symm hst) hsV h3, List.any_eq_true]
    have hsol := solid_erase hsV hs hm hm1 hm2
    constructor
    · rintro ⟨x, hx, hb⟩
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
      obtain ⟨⟨hxV, hxt⟩, hw⟩ := hb
      have hends := nbrsL_ends hx
      have hI : WI (V.erase s) x.1 s x.2 t :=
        ⟨hsol, Finset.mem_erase.2 ⟨(edge_ne hends).symm, hxV⟩, Finset.mem_erase.2 ⟨Ne.symm hst, htV⟩,
          hxt, by simp, by rcases hends with h | h; exacts [Or.inr h, Or.inl h],
          let ⟨m', hm', h1, h2⟩ := hmt; ⟨m', fun h => hm' (Finset.mem_of_mem_erase h), h1, h2⟩⟩
      refine ⟨x, hx, hxV, hxt, ?_⟩
      rw [← hp_swap]
      exact (boundaryEndpointsWalk_correct 12 _ _ hI (by have := wmu_le (V.erase s) x.1 s t; omega)).1 hw
    · rintro ⟨x, hx, hxV, hxt, hH⟩
      have hends := nbrsL_ends hx
      have hI : WI (V.erase s) x.1 s x.2 t :=
        ⟨hsol, Finset.mem_erase.2 ⟨(edge_ne hends).symm, hxV⟩, Finset.mem_erase.2 ⟨Ne.symm hst, htV⟩,
          hxt, by simp, by rcases hends with h | h; exacts [Or.inr h, Or.inl h],
          let ⟨m', hm', h1, h2⟩ := hmt; ⟨m', fun h => hm' (Finset.mem_of_mem_erase h), h1, h2⟩⟩
      refine ⟨x, hx, ?_⟩
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      rw [← hp_swap] at hH
      exact ⟨⟨hxV, hxt⟩, (boundaryEndpointsWalk_correct 12 _ _ hI
        (by have := wmu_le (V.erase s) x.1 s t; omega)).2 hH⟩
  · simp only [hf]
    have hm := List.mem_of_find?_eq_some hf
    have hp := List.find?_some hf
    simp only [decide_eq_true_eq] at hp
    have hI : WI V s x.1 x.2 t := ⟨hs, hsV, htV, hst, hp, nbrsL_ends hm, hmt⟩
    exact boundaryEndpointsWalk_correct 12 _ _ hI (by have := wmu_le V s x.1 t; omega)

end boundaryEndpoints

end HP

end SolidGridHam
