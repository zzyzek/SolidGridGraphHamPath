/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import SolidGridHam.Path.S4MergeII

/-!
# Theorem R: a good merging cell exists (docs/S4_RESIDUAL.md §1–§3)

A merging cell `X` is *bad* through bridge `i` when `X` is the square beyond `E_i` (across its
front) and `i` is undone in `X`'s plan. Lemma 1: a merging cell across a lateral of `E_k` has node
`k`. Lemma 2: the side squares `Y` of a bad `E_i` are merging when they are cells, have node `i`,
and at most one is not a cell (the out vertex `t0` lies at a corner of `E_i` on that side); if `Y`
is bad through `k`, then `E_k` is beside `X` across the same lateral direction (crossed) and `X`
has node `k`. Theorem R then finds a good cell among `X`, its two side squares, and the far side
square of a crossed `E_k`.
-/

namespace SolidGridHam

namespace HP

open Finset Classical

-- The start pair of a merging cell (the pair `reduceOut` uses).
--
def mergePair (H : Finset Edge) (X : Pt) : Pt × Pt := (back1 X (altFrame H X), front1 X (altFrame H X))

lemma planA_fst_swap : ∀ (BS : List Bridge) (H : Finset Edge) (u v : Pt),
    (planA H BS (u, v)).map Prod.fst = (planA H BS (v, u)).map Prod.fst
  | [], _, _, _ => rfl
  | b :: BS, H, u, v => by
    simp only [planA]
    by_cases h : Conn (flip H b.E) u v
    · have h' : Conn (flip H b.E) v u := h.symm
      simp [h, h']
    · have h' : ¬ Conn (flip H b.E) v u := fun c => h c.symm
      simp [h, h', planA_fst_swap BS]

-- The plan's decisions do not depend on the order of the pair.
--
lemma lowAt_swap (H : Finset Edge) (BS : List Bridge) (u v : Pt) (k : ℕ) :
    lowAt H BS (u, v) k = lowAt H BS (v, u) k := by
  unfold lowAt
  have h := congrArg (fun l => l[k]?) (planA_fst_swap BS H u v)
  simp only [List.getElem?_map] at h
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  cases h1 : (planA H BS (u, v))[k]? <;> cases h2 : (planA H BS (v, u))[k]? <;>
    simp_all

lemma side_roles (c : Pt) (s a : Side) :
    sideEdge c s = lat1 c a ∨ sideEdge c s = lat2 c a ∨ sideEdge c s = back c a ∨
      sideEdge c s = front c a := by
  cases s <;> cases a <;> simp [lat1, lat2, back, front, sideEdge, Side.opp]

-- A merging cell's frame is the axis of any dark side.
--
lemma frame_of_dark {V : Finset Pt} {H : Finset Edge} {X : Pt} {aX : Side} (hc : MCell V H X aX)
    {s : Side} (hs : sideEdge X s ∈ H) : aX = s ∨ aX = s.opp := by
  rcases side_cases aX s with h | h | h | h
  · exact Or.inl h.symm
  · exact Or.inr (by rw [h, opp_opp])
  · exfalso; rw [h, ← lat1_eq] at hs; exact hc.l1 hs
  · exfalso; rw [h, ← lat2_eq] at hs; exact hc.l2 hs

lemma low_frame {H : Finset Edge} {BS : List Bridge} {X : Pt} {aX s : Side}
    (h : aX = s ∨ aX = s.opp) (k : ℕ) :
    lowAt H BS (back1 X aX, front1 X aX) k = lowAt H BS (back1 X s, front1 X s) k := by
  rcases h with rfl | rfl
  · rfl
  · rw [back1_sopp, front1_sopp, lowAt_swap]

lemma apart_frame {H : Finset Edge} {X : Pt} {aX s : Side} (h : aX = s ∨ aX = s.opp)
    (hn : ¬ Conn H (back1 X aX) (front1 X aX)) : ¬ Conn H (back1 X s) (front1 X s) := by
  rcases h with rfl | rfl
  · exact hn
  · rw [back1_sopp, front1_sopp] at hn; exact fun c => hn c.symm

lemma nb_latAB_ne (c : Pt) (a : Side) : nb c (latA a) ≠ nb c (latB a) := by
  obtain ⟨x, y⟩ := c; cases a <;> simp [nb, latA, latB] <;> omega

lemma nb_nb_ne (c : Pt) (s : Side) : nb (nb c s) s ≠ c := by
  obtain ⟨x, y⟩ := c; cases s <;> simp [nb] <;> omega

lemma t_both (E : Pt) (a : Side) {z : Pt} (h1 : z = front1 E a ∨ z = back1 E a)
    (h2 : z = front2 E a ∨ z = back2 E a) : False := by
  obtain ⟨x, y⟩ := E
  rcases h1 with rfl | rfl <;> rcases h2 with h | h <;> cases a <;>
    simp [front1, front2, back1, back2, Prod.ext_iff] at h

lemma t_farA (E : Pt) (a : Side) {z : Pt}
    (h1 : z = front1 (nb (nb E a) (latA a)) a.opp ∨ z = back1 (nb (nb E a) (latA a)) a.opp)
    (h2 : z = front2 E a ∨ z = back2 E a) : False := by
  obtain ⟨x, y⟩ := E
  rcases h1 with rfl | rfl <;> rcases h2 with h | h <;> cases a <;>
    simp [nb, latA, Side.opp, front1, front2, back1, back2, Prod.ext_iff] at h <;> omega

lemma t_farB (E : Pt) (a : Side) {z : Pt}
    (h1 : z = front2 (nb (nb E a) (latB a)) a.opp ∨ z = back2 (nb (nb E a) (latB a)) a.opp)
    (h2 : z = front1 E a ∨ z = back1 E a) : False := by
  obtain ⟨x, y⟩ := E
  rcases h1 with rfl | rfl <;> rcases h2 with h | h <;> cases a <;>
    simp [nb, latB, Side.opp, front1, front2, back1, back2, Prod.ext_iff] at h <;> omega

lemma farA_back (x : Pt) (s : Side) : back1 (nb x (latA s)) s = nb (back1 x s) (latA s) := by
  obtain ⟨a, b⟩ := x; cases s <;> simp [back1, nb, latA]

lemma farA_front (x : Pt) (s : Side) : front1 (nb x (latA s)) s = nb (front1 x s) (latA s) := by
  obtain ⟨a, b⟩ := x; cases s <;> simp [front1, nb, latA]

lemma isFar_back (x : Pt) (s : Side) : back2 (nb x (latB s)) s = nb (back2 x s) (latB s) := by
  obtain ⟨a, b⟩ := x; cases s <;> simp [back2, nb, latB]

lemma isFar_front (x : Pt) (s : Side) : front2 (nb x (latB s)) s = nb (front2 x s) (latB s) := by
  obtain ⟨a, b⟩ := x; cases s <;> simp [front2, nb, latB]

-- An out-vertex on the `latA` lateral of the cell two steps over, its phantom pointing further
-- along `latA`, and one on the `latB` lateral of `E`, its phantom pointing along `latB`: the
-- phantoms are opposed, which `NoOpp` excludes (the only place needing more than `Far`).
--
lemma t_farA2 {V : Finset Pt} {H : Finset Edge} {t0 u0 : Pt} (hopp : NoOpp V H t0 u0)
    (E : Pt) (a : Side)
    (h1 : ∃ w m, (w = t0 ∨ w = u0) ∧
      (w = front1 (nb (nb E a) (latA a)) a.opp ∨ w = back1 (nb (nb E a) (latA a)) a.opp) ∧
      (∃ e ∈ H, Ends e w m) ∧ m ∉ V ∧ m = nb w (latA a.opp))
    (h2 : ∃ w m, (w = t0 ∨ w = u0) ∧ (w = front2 E a ∨ w = back2 E a) ∧
      (∃ e ∈ H, Ends e w m) ∧ m ∉ V ∧ m = nb w (latB a)) : False := by
  obtain ⟨w, m, hw, hw1, ⟨e, he, hee⟩, hm, rfl⟩ := h1
  obtain ⟨w', m', hw', hw2, ⟨f, hf, hff⟩, hm', rfl⟩ := h2
  by_cases hww : w = w'
  · subst hww; exact t_farA E a hw1 hw2
  · apply hopp e he f hf _ _ _ _ hw hw' hww hee hm hff hm'
    obtain ⟨x, y⟩ := E
    rcases hw1 with rfl | rfl <;> rcases hw2 with rfl | rfl <;> cases a <;>
      simp only [Opp, nb, latA, latB, Side.opp, front1, front2, back1, back2, Prod.mk.injEq,
        abs_le, and_true, true_and] <;> omega

lemma t_farB2 {V : Finset Pt} {H : Finset Edge} {t0 u0 : Pt} (hopp : NoOpp V H t0 u0)
    (E : Pt) (a : Side)
    (h1 : ∃ w m, (w = t0 ∨ w = u0) ∧
      (w = front2 (nb (nb E a) (latB a)) a.opp ∨ w = back2 (nb (nb E a) (latB a)) a.opp) ∧
      (∃ e ∈ H, Ends e w m) ∧ m ∉ V ∧ m = nb w (latB a.opp))
    (h2 : ∃ w m, (w = t0 ∨ w = u0) ∧ (w = front1 E a ∨ w = back1 E a) ∧
      (∃ e ∈ H, Ends e w m) ∧ m ∉ V ∧ m = nb w (latA a)) : False := by
  obtain ⟨w, m, hw, hw1, ⟨e, he, hee⟩, hm, rfl⟩ := h1
  obtain ⟨w', m', hw', hw2, ⟨f, hf, hff⟩, hm', rfl⟩ := h2
  by_cases hww : w = w'
  · subst hww; exact t_farB E a hw1 hw2
  · apply hopp e he f hf _ _ _ _ hw hw' hww hee hm hff hm'
    obtain ⟨x, y⟩ := E
    rcases hw1 with rfl | rfl <;> rcases hw2 with rfl | rfl <;> cases a <;>
      simp only [Opp, nb, latA, latB, Side.opp, front1, front2, back1, back2, Prod.mk.injEq,
        abs_le, and_true, true_and] <;> omega

-- Edges with an end outside `V` are never flipped.
--
lemma reach_out_mem {V : Finset Pt} {H0 H : Finset Edge} {BS : List Bridge}
    (hr : Reach V H0 H BS) {e : Edge} (he : e ∈ H) (hx : e.p ∉ V ∨ e.q ∉ V) : e ∈ H0 := by
  induction hr with
  | base => exact he
  | @step H' BS' b _ hrs _ _ ih =>
    apply ih
    have hc : IsCell V b.E := hrs.cells (b.r - 1) (by have := hrs.two; omega)
    rcases hx with hx | hx
    · exact (mem_flip_off (not_cellE_of_p hx hc (Or.inl rfl))).1 he
    · exact (mem_flip_off (not_cellE_of_p hx hc (Or.inr rfl))).1 he

lemma noOpp_reach {V : Finset Pt} {H0 H : Finset Edge} {BS : List Bridge} {t0 u0 : Pt}
    (hr : Reach V H0 H BS) (h0 : NoOpp V H0 t0 u0) : NoOpp V H t0 u0 := by
  intro e he f hf a ma b mb ha hb hab hee hma hff hmb
  have ox : ∀ {g : Edge} {x y : Pt}, Ends g x y → y ∉ V → g.p ∉ V ∨ g.q ∉ V := by
    intro g x y hg hy
    rcases hg with ⟨_, h⟩ | ⟨h, _⟩
    · exact Or.inr (h ▸ hy)
    · exact Or.inl (h ▸ hy)
  exact h0 e (reach_out_mem hr he (ox hee hma)) f (reach_out_mem hr hf (ox hff hmb)) a ma b mb
    ha hb hab hee hma hff hmb

section theoremR

variable {V W : Finset Pt} {d : Pt → ℕ} {t0 u0 : Pt} {H0 : Finset Edge}
  (hVW : V ⊆ W) (hdc : ∀ q, IsCell V q → ∀ z, IsCorner z q → d z = 2)
  (h0 : IsFactor W d H0) (hout0 : ∀ e ∈ H0, (e.p ∉ V → e.q = t0 ∨ e.q = u0) ∧ (e.q ∉ V → e.p = t0 ∨ e.p = u0))
include hVW hdc h0 hout0

-- A bridge of the final state, frozen.
--
lemma frozen0 {BS : List Bridge} {H : Finset Edge} (hr : Reach V H0 H BS) {i : ℕ}
    (hi : i < BS.length) :
    RegionOK H (BS[i]'hi) ∧ 2 ≤ (BS[i]'hi).r ∧ (BS[i]'hi).r % 2 = 0 ∧
      ∀ j < (BS[i]'hi).r, IsCell V ((BS[i]'hi).cell j) := by
  have hinv := pinv_reach (t0 := t0) (u0 := u0) hVW hdc h0 hout0 hr
  exact hinv.reg _ (List.getElem_mem hi)

lemma low_of_node {BS : List Bridge} {H : Finset Edge} (hr : Reach V H0 H BS) {uv : Pt × Pt}
    (hn : ¬ Conn H uv.1 uv.2) {j' k : ℕ} (hj' : j' ≤ k) (hk : k < BS.length)
    (h : nodeI H0 BS (pendAt H BS uv j').1 (pendAt H BS uv j').2 = k) :
    lowAt H BS uv k = true := by
  by_contra hl
  exact (node_pend hVW hdc h0 hout0 hr hn (k - j') j' k rfl hj' hk).1 (by simpa using hl) h

-- **Lemma 1.** A merging cell across a lateral of `E_k` has node `k`.
--
theorem node_beside {BS : List Bridge} {H : Finset Edge} (hr : Reach V H0 H BS) {Y : Pt}
    {aY : Side} (hc : MCell V H Y aY) {k : ℕ} (hk : k < BS.length) {s' : Side}
    (hs' : s' = latA (BS[k]'hk).a ∨ s' = latB (BS[k]'hk).a) (hY : Y = nb (BS[k]'hk).E s') :
    nodeI H0 BS (back1 Y aY) (front1 Y aY) = k := by
  have hH := seqH_of_reach hr
  have hF : seqH H0 (BS.drop 0) = H := by rw [List.drop_zero, ← hH]
  obtain ⟨hR, htwo, _, _⟩ := frozen0 hVW hdc h0 hout0 hr hk
  set b := BS[k]'hk with hb
  have bE : back b.E b.a ∈ H := by
    have := hR.frA
    unfold Bridge.E Bridge.cell at *
    rw [show b.r - 1 = b.r - 2 + 1 by omega, back_cellJ_succ]; exact this
  have hlight : sideEdge b.E s' ∉ H := by
    rcases hs' with h | h <;> rw [h]
    · rw [← lat1_eq]; exact hR.latE.1
    · rw [← lat2_eq]; exact hR.latE.2
  have heY : sideEdge b.E s' = sideEdge Y s'.opp := by rw [hY, sideEdge_nb_opp]
  have hl : sideEdge b.E s' = lat1 Y aY ∨ sideEdge b.E s' = lat2 Y aY := by
    rcases side_roles Y s'.opp aY with h | h | h | h <;> rw [← heY] at h
    · exact Or.inl h
    · exact Or.inr h
    · rw [h] at hlight; exact absurd hc.bk hlight
    · rw [h] at hlight; exact absurd hc.fr hlight
  have kb := (ends_back (c := Y) (s := aY)).conn hc.bk
  have kf := (ends_front (c := Y) (s := aY)).conn hc.fr
  have hR' := isEqv_conn H
  have hmE : Matched (Conn H) (back1 Y aY) (front1 Y aY) (back1 b.E b.a) (front1 b.E b.a) := by
    rcases hs' with h | h
    · have he : Ends (sideEdge b.E s') (back1 b.E b.a) (front1 b.E b.a) := by
        rw [h, ← lat1_eq]; exact ends_lat1 _ _
      exact lat_matched kb kf hl he
    · have he : Ends (sideEdge b.E s') (back2 b.E b.a) (front2 b.E b.a) := by
        rw [h, ← lat2_eq]; exact ends_lat2 _ _
      have m1 := lat_matched kb kf hl he
      have m2 : Matched (Conn H) (back2 b.E b.a) (front2 b.E b.a) (back1 b.E b.a)
          (front1 b.E b.a) :=
        Or.inl ⟨((ends_back (c := b.E) (s := b.a)).conn bE).symm,
          ((ends_front (c := b.E) (s := b.a)).conn hR.frE).symm⟩
      exact Matched.trans hR' m1 m2
  rw [← hF] at hmE
  exact sameNodeI' hVW hdc h0 hout0 hr hk (Nat.zero_le _) hmE

-- The facts at a merging cell beyond `E_i`, in `E_i`'s frame.
--
lemma beyond_facts {BS : List Bridge} {H : Finset Edge} (hr : Reach V H0 H BS) {X : Pt}
    (hcX : MCell V H X (altFrame H X)) (haX : Alt H X) {i : ℕ} (hi : i < BS.length)
    (hX : X = nb (BS[i]'hi).E (BS[i]'hi).a) :
    (altFrame H X = (BS[i]'hi).a ∨ altFrame H X = (BS[i]'hi).a.opp) ∧
      back X (BS[i]'hi).a ∈ H ∧ front X (BS[i]'hi).a ∈ H ∧
      lat1 X (BS[i]'hi).a ∉ H ∧ lat2 X (BS[i]'hi).a ∉ H := by
  obtain ⟨hR, _, _, _⟩ := frozen0 hVW hdc h0 hout0 hr hi
  have hbk : sideEdge X (BS[i]'hi).a.opp ∈ H := by
    rw [hX, sideEdge_nb_opp]; exact hR.frE
  have hfa := frame_of_dark hcX hbk
  have hfr : sideEdge X (BS[i]'hi).a ∈ H := by
    have := (alt_opp_iff haX (BS[i]'hi).a.opp).1 hbk; rwa [opp_opp] at this
  obtain ⟨l1, l2⟩ := alt_lats haX hbk
  rw [latA_opp] at l1; rw [latB_opp] at l2
  refine ⟨?_, hbk, hfr, by rw [lat1_eq]; exact l1, by rw [lat2_eq]; exact l2⟩
  rcases hfa with h | h
  · exact Or.inr h
  · exact Or.inl (by rw [h, opp_opp])

-- **Lemma 2.2.** The side squares of `E_i`, for a bad `X` beyond it, are merging and not pair
-- squares.
--
theorem l22 {BS : List Bridge} {H : Finset Edge} (hr : Reach V H0 H BS) {X : Pt}
    (hcX : MCell V H X (altFrame H X)) (haX : Alt H X) {i : ℕ} (hi : i < BS.length)
    (hlow : lowAt H BS (mergePair H X) i = false) (hX : X = nb (BS[i]'hi).E (BS[i]'hi).a)
    {ℓ : Side} (hℓ : ℓ = latA (BS[i]'hi).a ∨ ℓ = latB (BS[i]'hi).a) :
    Alt H (nb (BS[i]'hi).E ℓ) ∧ CutSq H (nb (BS[i]'hi).E ℓ) ∧
      ¬ ∃ b' ∈ BS, nb (BS[i]'hi).E ℓ = b'.cell (b'.r - 2) ∨ nb (BS[i]'hi).E ℓ = b'.E := by
  have hH := seqH_of_reach hr
  have hF : seqH H0 (BS.drop 0) = H := by rw [List.drop_zero, ← hH]
  obtain ⟨hfa, hbk, hfr, l1, l2⟩ := beyond_facts hVW hdc h0 hout0 hr hcX haX hi hX
  have hlow' : lowAt H BS (back1 X (BS[i]'hi).a, front1 X (BS[i]'hi).a) i = false := by
    rw [← low_frame hfa]; exact hlow
  have hn' := apart_frame hfa hcX.apart
  have kb := (ends_back (c := X) (s := (BS[i]'hi).a)).conn hbk
  have kf := (ends_front (c := X) (s := (BS[i]'hi).a)).conn hfr
  have hp0 := pend_zero hVW hdc h0 hout0 hr (uv := (back1 X (BS[i]'hi).a, front1 X (BS[i]'hi).a))
    hn' (by omega)
  subst hX
  rw [← hF] at l1 l2 kb kf
  rcases hℓ with rfl | rfl
  · have := sideA_merging hVW hdc h0 hout0 hr hn' hi hlow' (Nat.zero_le _) l1 (Or.inl ⟨0, le_rfl, hp0, kb, kf⟩)
    rw [hF, List.drop_zero] at this; exact this
  · have := sideB_merging hVW hdc h0 hout0 hr hn' hi hlow' (Nat.zero_le _) l2 (Or.inl ⟨0, le_rfl, hp0, kb, kf⟩)
    rw [hF, List.drop_zero] at this; exact this

-- **Lemma 2.1 (sides).** Each side square of `E_i` (with `X` beyond it, laterals light) is a
-- cell, or the out vertex `t0` is a corner of `E_i` on that side.
--
theorem side_or_t {BS : List Bridge} {H : Finset Edge} (hr : Reach V H0 H BS) {i : ℕ}
    (hi : i < BS.length)
    (hXl1 : lat1 (nb (BS[i]'hi).E (BS[i]'hi).a) (BS[i]'hi).a ∉ H)
    (hXl2 : lat2 (nb (BS[i]'hi).E (BS[i]'hi).a) (BS[i]'hi).a ∉ H) :
    (IsCell V (nb (BS[i]'hi).E (latA (BS[i]'hi).a)) ∨ ∃ w m, (w = t0 ∨ w = u0) ∧
        (w = front1 (BS[i]'hi).E (BS[i]'hi).a ∨ w = back1 (BS[i]'hi).E (BS[i]'hi).a) ∧
        (∃ e ∈ H, Ends e w m) ∧ m ∉ V ∧ m = nb w (latA (BS[i]'hi).a)) ∧
      (IsCell V (nb (BS[i]'hi).E (latB (BS[i]'hi).a)) ∨ ∃ w m, (w = t0 ∨ w = u0) ∧
        (w = front2 (BS[i]'hi).E (BS[i]'hi).a ∨ w = back2 (BS[i]'hi).E (BS[i]'hi).a) ∧
        (∃ e ∈ H, Ends e w m) ∧ m ∉ V ∧ m = nb w (latB (BS[i]'hi).a)) := by
  have hinvF := pinv_reach (t0 := t0) (u0 := u0) hVW hdc h0 hout0 hr
  have hdegcF := degc_of hVW hdc hinvF.fac
  obtain ⟨hR, htwo, _, cellsb⟩ := frozen0 hVW hdc h0 hout0 hr hi
  set b := BS[i]'hi with hb
  have hEcell : IsCell V b.E := cellsb _ (by omega)
  have oA : outer1 b.E b.a ∈ H := by
    have dF1 := hdegcF _ hEcell (front1 b.E b.a) (isCorner_front1 _ _)
    rw [deg_front1, ind_of_not_mem hR.latE.1, ind_of_mem hR.frE, ind_of_not_mem hXl1] at dF1
    by_contra h; rw [ind_of_not_mem h] at dF1; omega
  have oB : outer2 b.E b.a ∈ H := by
    have dF2 := hdegcF _ hEcell (front2 b.E b.a) (isCorner_front2 _ _)
    rw [deg_front2, ind_of_not_mem hR.latE.2, ind_of_mem hR.frE, ind_of_not_mem hXl2] at dF2
    by_contra h; rw [ind_of_not_mem h] at dF2; omega
  have hE : b.E = cellJ b.q b.a (b.r - 1) := rfl
  have bkA : back (nb b.E (latA b.a)) b.a ∈ H := by
    unfold back
    rw [hE, side_backA b.q b.a (by omega), show b.r - 1 - 1 = b.r - 2 by omega]
    have := (hR.outer (b.r - 2) (by omega)).1.2 (by omega)
    unfold Bridge.cell at this; exact this
  have bkB : back (nb b.E (latB b.a)) b.a ∈ H := by
    unfold back
    rw [hE, side_backB b.q b.a (by omega), show b.r - 1 - 1 = b.r - 2 by omega]
    have := (hR.outer (b.r - 2) (by omega)).2.2 (by omega)
    unfold Bridge.cell at this; exact this
  have EV := isCell_corners hEcell b.a
  have hout := hinvF.out
  constructor
  · by_cases hcell : IsCell V (nb b.E (latA b.a))
    · exact Or.inl hcell
    right
    by_cases hx : back1 (nb b.E (latA b.a)) b.a ∈ V
    · have hy : front1 (nb b.E (latA b.a)) b.a ∉ V := fun hy => hcell (isCell_of_corners (a := b.a)
        hx (by rw [sideA_back2]; exact EV.1) hy (by rw [sideA_front2]; exact EV.2.2.1))
      have e := ends_front (c := nb b.E (latA b.a)) (s := b.a)
      rw [side_front, sideA_front2] at e
      exact ⟨_, _, out_end hout e oA hy, Or.inl rfl, ⟨_, oA, ends_swap e⟩, hy, farA_front _ _⟩
    · have e := ends_back (c := nb b.E (latA b.a)) (s := b.a)
      rw [sideA_back2] at e
      exact ⟨_, _, out_end hout e bkA hx, Or.inr rfl, ⟨_, bkA, ends_swap e⟩, hx, farA_back _ _⟩
  · by_cases hcell : IsCell V (nb b.E (latB b.a))
    · exact Or.inl hcell
    right
    by_cases hx : back2 (nb b.E (latB b.a)) b.a ∈ V
    · have hy : front2 (nb b.E (latB b.a)) b.a ∉ V := fun hy => hcell (isCell_of_corners (a := b.a)
        (by rw [sideB_back1]; exact EV.2.1) hx (by rw [sideB_front1]; exact EV.2.2.2) hy)
      have e := ends_swap (ends_front (c := nb b.E (latB b.a)) (s := b.a))
      rw [sideB_front, sideB_front1] at e
      exact ⟨_, _, out_end hout e oB hy, Or.inl rfl, ⟨_, oB, ends_swap e⟩, hy, isFar_front _ _⟩
    · have e := ends_swap (ends_back (c := nb b.E (latB b.a)) (s := b.a))
      rw [sideB_back1] at e
      exact ⟨_, _, out_end hout e bkB hx, Or.inr rfl, ⟨_, bkB, ends_swap e⟩, hx, isFar_back _ _⟩

-- **Lemma 2.3.** If the side square `Y = nb E_i ℓ` of a bad `E_i` is bad through `k`, then
-- `E_k` is beside `X` across `ℓ` (running against `E_i`) and `X` has node `k`.
--
theorem l23 {BS : List Bridge} {H : Finset Edge} (hr : Reach V H0 H BS) {X : Pt}
    (hcX : MCell V H X (altFrame H X)) (haX : Alt H X) {i : ℕ} (hi : i < BS.length)
    (hlowX : lowAt H BS (mergePair H X) i = false) (hX : X = nb (BS[i]'hi).E (BS[i]'hi).a)
    {ℓ : Side} (hℓ : ℓ = latA (BS[i]'hi).a ∨ ℓ = latB (BS[i]'hi).a)
    (hYc : IsCell V (nb (BS[i]'hi).E ℓ)) {k : ℕ} (hk : k < BS.length)
    (hlowk : lowAt H BS (mergePair H (nb (BS[i]'hi).E ℓ)) k = false)
    (hYk : nb (BS[i]'hi).E ℓ = nb (BS[k]'hk).E (BS[k]'hk).a) :
    (BS[k]'hk).a = (BS[i]'hi).a.opp ∧ (BS[k]'hk).E = nb X ℓ ∧
      nodeI H0 BS (mergePair H X).1 (mergePair H X).2 = k := by
  obtain ⟨altY, cutY, _⟩ := l22 hVW hdc h0 hout0 hr hcX haX hi hlowX hX hℓ
  have hcY := mcell_of hYc altY cutY
  obtain ⟨hR, htwo, hev, _⟩ := frozen0 hVW hdc h0 hout0 hr hi
  obtain ⟨hRk, _, _, _⟩ := frozen0 hVW hdc h0 hout0 hr hk
  -- `Y` has node `i`, so `i` is lowered in `Y`'s plan
  have hnodeY : nodeI H0 BS (mergePair H (nb (BS[i]'hi).E ℓ)).1 (mergePair H (nb (BS[i]'hi).E ℓ)).2 = i :=
    node_beside hVW hdc h0 hout0 hr hcY hi hℓ rfl
  have hp0Y := pend_zero hVW hdc h0 hout0 hr (uv := mergePair H (nb (BS[i]'hi).E ℓ)) hcY.apart
    (by omega)
  have hlowYi : lowAt H BS (mergePair H (nb (BS[i]'hi).E ℓ)) i = true :=
    low_of_node hVW hdc h0 hout0 hr (uv := mergePair H (nb (BS[i]'hi).E ℓ)) hcY.apart
      (Nat.zero_le i) hi (by rw [hp0Y]; exact hnodeY)
  -- `E_k` lies across a dark side of `Y`
  have hEk : (BS[k]'hk).E = nb (nb (BS[i]'hi).E ℓ) (BS[k]'hk).a.opp := by rw [hYk, nb_nb_opp]
  have hdark : sideEdge (nb (BS[i]'hi).E ℓ) (BS[k]'hk).a.opp ∈ H := by
    rw [hYk, sideEdge_nb_opp]; exact hRk.frE
  -- the sides of `Y` across `ℓ` are light
  have hl1 : sideEdge (nb (BS[i]'hi).E ℓ) ℓ.opp ∉ H := by
    rw [sideEdge_nb_opp]
    rcases hℓ with h | h <;> rw [h]
    · rw [← lat1_eq]; exact hR.latE.1
    · rw [← lat2_eq]; exact hR.latE.2
  have hl2 : sideEdge (nb (BS[i]'hi).E ℓ) ℓ ∉ H := fun h => hl1 ((alt_opp_iff altY ℓ).1 h)
  have hax : (BS[k]'hk).a.opp = (BS[i]'hi).a ∨ (BS[k]'hk).a.opp = (BS[i]'hi).a.opp := by
    rcases side_cases (BS[i]'hi).a (BS[k]'hk).a.opp with h | h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exfalso
      rcases hℓ with hl | hl
      · rw [h, ← hl] at hdark; exact hl2 hdark
      · rw [h, latA_eq_opp, ← hl] at hdark; exact hl1 hdark
    · exfalso
      rcases hℓ with hl | hl
      · rw [h, latB_eq_opp, ← hl] at hdark; exact hl1 hdark
      · rw [h, ← hl] at hdark; exact hl2 hdark
  rcases hax with hax | hax
  · -- crossed: the conclusion
    have hka : (BS[k]'hk).a = (BS[i]'hi).a.opp := by rw [← hax, opp_opp]
    have hEkX : (BS[k]'hk).E = nb X ℓ := by
      rw [hEk, hax, side_comm _ _ hℓ, ← hX]
    refine ⟨hka, hEkX, ?_⟩
    have hs' : ℓ.opp = latA (BS[k]'hk).a ∨ ℓ.opp = latB (BS[k]'hk).a := by
      rw [hka, latA_opp, latB_opp]
      rcases hℓ with rfl | rfl
      · exact Or.inr (latA_opp' _)
      · exact Or.inl (latB_opp' _)
    exact node_beside hVW hdc h0 hout0 hr hcX hk hs' (by rw [hEkX, nb_nb_opp])
  · -- parallel: impossible
    exfalso
    have hka : (BS[k]'hk).a = (BS[i]'hi).a := by
      have := congrArg Side.opp hax; rwa [opp_opp, opp_opp] at this
    have hA : nb (BS[i]'hi).E (BS[i]'hi).a.opp = (BS[i]'hi).cell ((BS[i]'hi).r - 2) := by
      unfold Bridge.E Bridge.cell
      rw [show (BS[i]'hi).r - 1 = (BS[i]'hi).r - 2 + 1 by omega, nb_cellJ_opp]
    have hEside : (BS[k]'hk).E = nb ((BS[i]'hi).cell ((BS[i]'hi).r - 2)) ℓ := by
      rw [hEk, hax, side_comm _ _ (latAB_opp hℓ), hA]
    have hsep := (pinv_reach (t0 := t0) (u0 := u0) hVW hdc h0 hout0 hr).sep
    rcases lt_trichotomy k i with hki | rfl | hik
    · have hz : NotZ (BS[k]'hk) (BS[i]'hi) := List.pairwise_iff_getElem.1 hsep k i hk hi hki
      have := hz.2.2 ((BS[i]'hi).r - 2) (by omega)
      rcases hℓ with h | h <;> rw [h] at hEside
      · exact this.1 hEside
      · exact this.2 hEside
    · exact side_ne_col (BS[k]'hk).q (BS[k]'hk).a hℓ ((BS[k]'hk).r - 2) ((BS[k]'hk).r - 1)
        hEside.symm
    · -- `k` older than `i`: before bridge `i`, `E_k` is frozen
      obtain ⟨_, _, hRk', htwok', _⟩ := frozen_at hVW hdc h0 hout0 hr (m := i + 1) (by omega) hk
      obtain ⟨c1', c2'⟩ := cutE_both hRk' htwok'
      have hrow := rowAt_at hVW hdc h0 hout0 hr hi
      have hAk : (BS[i]'hi).cell ((BS[i]'hi).r - 2) = nb (BS[k]'hk).E ℓ.opp := by
        rw [hEside, nb_nb_opp]
      have hlo : ℓ.opp = latA (BS[k]'hk).a ∨ ℓ.opp = latB (BS[k]'hk).a := by
        rw [hka]
        rcases hℓ with rfl | rfl
        · exact Or.inr (latA_opp' _)
        · exact Or.inl (latB_opp' _)
      -- the square of `i` beside `E_k` is cut before bridge `i`
      have hcutA : CutSq (seqH H0 (BS.drop (i + 1))) ((BS[i]'hi).cell ((BS[i]'hi).r - 2)) := by
        rw [hAk]
        rcases hlo with h | h <;> rw [h]
        · refine cutSq_of_corners (isCorner_back2 _ (BS[k]'hk).a)
            (isCorner_front2 _ (BS[k]'hk).a) ?_
          rw [sideA_back2, sideA_front2]; exact c1'
        · refine cutSq_of_corners (isCorner_back1 _ (BS[k]'hk).a)
            (isCorner_front1 _ (BS[k]'hk).a) ?_
          rw [sideB_back1, sideB_front1]; exact c2'
      by_cases r4 : 4 ≤ (BS[i]'hi).r
      · exact hrow.uncut ((BS[i]'hi).r - 2) (by omega) (by omega) hcutA
      · -- `r = 2`: the start pair of `i` has node `k`
        have hr2 : (BS[i]'hi).r = 2 := by omega
        have hq : (BS[i]'hi).cell ((BS[i]'hi).r - 2) = (BS[i]'hi).q := by
          unfold Bridge.cell; rw [hr2, Nat.sub_self, cellJ_zero]
        rw [hq] at hAk
        set G := seqH H0 (BS.drop (i + 1)) with hG
        have bEk : back (BS[k]'hk).E (BS[k]'hk).a ∈ G := by
          have := hRk'.frA
          unfold Bridge.E Bridge.cell at *
          rw [show (BS[k]'hk).r - 1 = (BS[k]'hk).r - 2 + 1 by omega, back_cellJ_succ]; exact this
        have heq : sideEdge (BS[i]'hi).q ℓ = sideEdge (BS[k]'hk).E ℓ.opp := by
          rw [hAk]; have := sideEdge_nb_opp (BS[k]'hk).E ℓ.opp; rw [opp_opp] at this; exact this
        have hlq : sideEdge (BS[i]'hi).q ℓ = lat1 (BS[i]'hi).q (BS[i]'hi).a ∨
            sideEdge (BS[i]'hi).q ℓ = lat2 (BS[i]'hi).q (BS[i]'hi).a := by
          rcases hℓ with h | h <;> rw [h]
          · exact Or.inl (lat1_eq _ _).symm
          · exact Or.inr (lat2_eq _ _).symm
        have hm : Matched (Conn G) (back1 (BS[i]'hi).q (BS[i]'hi).a) (front1 (BS[i]'hi).q (BS[i]'hi).a)
            (back1 (BS[k]'hk).E (BS[k]'hk).a) (front1 (BS[k]'hk).E (BS[k]'hk).a) := by
          rcases hlo with h | h
          · have he : Ends (sideEdge (BS[i]'hi).q ℓ) (back1 (BS[k]'hk).E (BS[k]'hk).a)
                (front1 (BS[k]'hk).E (BS[k]'hk).a) := by
              rw [heq, h, ← lat1_eq]; exact ends_lat1 _ _
            exact lat_matched hrow.crit.1 hrow.crit.2.1 hlq he
          · have he : Ends (sideEdge (BS[i]'hi).q ℓ) (back2 (BS[k]'hk).E (BS[k]'hk).a)
                (front2 (BS[k]'hk).E (BS[k]'hk).a) := by
              rw [heq, h, ← lat2_eq]; exact ends_lat2 _ _
            have m1 := lat_matched hrow.crit.1 hrow.crit.2.1 hlq he
            have m2 : Matched (Conn G) (back2 (BS[k]'hk).E (BS[k]'hk).a)
                (front2 (BS[k]'hk).E (BS[k]'hk).a) (back1 (BS[k]'hk).E (BS[k]'hk).a)
                (front1 (BS[k]'hk).E (BS[k]'hk).a) :=
              Or.inl ⟨((ends_back (c := (BS[k]'hk).E) (s := (BS[k]'hk).a)).conn bEk).symm,
                ((ends_front (c := (BS[k]'hk).E) (s := (BS[k]'hk).a)).conn hRk'.frE).symm⟩
            exact Matched.trans (isEqv_conn G) m1 m2
        have hnq := sameNodeI' hVW hdc h0 hout0 hr hk (m := i + 1) (by omega) hm
        obtain ⟨_, _, _, f4⟩ := pend_facts hVW hdc h0 hout0 hr
          (uv := mergePair H (nb (BS[i]'hi).E ℓ)) hcY.apart hi
        have hp1 := f4 (by omega)
        rw [ite_eq_left hlowYi] at hp1
        have hne := (node_pend hVW hdc h0 hout0 hr (uv := mergePair H (nb (BS[i]'hi).E ℓ)) hcY.apart
          (k - (i + 1)) (i + 1) k rfl (by omega) hk).1 hlowk
        rw [hp1] at hne
        exact hne hnq

-- **Theorem R, one side.** A bad `X` beyond `E_i` whose side square `Y` across `ℓ` is a cell,
-- when every merging cell is bad and the far side square of a crossed `E_k` is a cell: impossible.
--
theorem r_core {BS : List Bridge} {H : Finset Edge} (hr : Reach V H0 H BS) {X : Pt}
    (hcX : MCell V H X (altFrame H X)) (haX : Alt H X) {i : ℕ} (hi : i < BS.length)
    (hlowX : lowAt H BS (mergePair H X) i = false) (hX : X = nb (BS[i]'hi).E (BS[i]'hi).a)
    {ℓ : Side} (hℓ : ℓ = latA (BS[i]'hi).a ∨ ℓ = latB (BS[i]'hi).a)
    (hYc : IsCell V (nb (BS[i]'hi).E ℓ))
    (hno : ∀ Z, IsCell V Z → Alt H Z → CutSq H Z → (¬ ∃ b ∈ BS, Z = b.cell (b.r - 2) ∨ Z = b.E) →
      ∃ k, ∃ hk : k < BS.length, lowAt H BS (mergePair H Z) k = false ∧
        Z = nb (BS[k]'hk).E (BS[k]'hk).a)
    (hzc : ∀ k (hk : k < BS.length), (BS[k]'hk).a = (BS[i]'hi).a.opp → (BS[k]'hk).E = nb X ℓ →
      ((IsCell V (nb (BS[k]'hk).E (latA (BS[k]'hk).a)) ∨ ∃ w m, (w = t0 ∨ w = u0) ∧
          (w = front1 (BS[k]'hk).E (BS[k]'hk).a ∨ w = back1 (BS[k]'hk).E (BS[k]'hk).a) ∧
          (∃ e ∈ H, Ends e w m) ∧ m ∉ V ∧ m = nb w (latA (BS[k]'hk).a)) ∧
        (IsCell V (nb (BS[k]'hk).E (latB (BS[k]'hk).a)) ∨ ∃ w m, (w = t0 ∨ w = u0) ∧
          (w = front2 (BS[k]'hk).E (BS[k]'hk).a ∨ w = back2 (BS[k]'hk).E (BS[k]'hk).a) ∧
          (∃ e ∈ H, Ends e w m) ∧ m ∉ V ∧ m = nb w (latB (BS[k]'hk).a))) →
      IsCell V (nb (BS[k]'hk).E ℓ)) : False := by
  obtain ⟨altY, cutY, npY⟩ := l22 hVW hdc h0 hout0 hr hcX haX hi hlowX hX hℓ
  have hcY := mcell_of hYc altY cutY
  obtain ⟨k, hk, hlowk, hYk⟩ := hno _ hYc altY cutY npY
  obtain ⟨hka, hEk, _⟩ := l23 hVW hdc h0 hout0 hr hcX haX hi hlowX hX hℓ hYc hk hlowk hYk
  -- Lemma 2 at `(Y, k)`
  obtain ⟨_, _, _, yl1, yl2⟩ := beyond_facts hVW hdc h0 hout0 hr hcY altY hk hYk
  have hso := side_or_t hVW hdc h0 hout0 hr hk (by rw [← hYk]; exact yl1) (by rw [← hYk]; exact yl2)
  have hZc := hzc k hk hka hEk hso
  have hℓk : ℓ = latA (BS[k]'hk).a ∨ ℓ = latB (BS[k]'hk).a := by
    rw [hka, latA_opp, latB_opp]; exact hℓ
  obtain ⟨altZ, cutZ, npZ⟩ := l22 hVW hdc h0 hout0 hr hcY altY hk hlowk hYk hℓk
  obtain ⟨k', hk', hlowk', hZk'⟩ := hno _ hZc altZ cutZ npZ
  obtain ⟨_, hEk', hnodeY⟩ := l23 hVW hdc h0 hout0 hr hcY altY hk hlowk hYk hℓk hZc hk' hlowk'
    hZk'
  have hnodeY' : nodeI H0 BS (mergePair H (nb (BS[i]'hi).E ℓ)).1
      (mergePair H (nb (BS[i]'hi).E ℓ)).2 = i := node_beside hVW hdc h0 hout0 hr hcY hi hℓ rfl
  have hki : k' = i := by rw [← hnodeY]; exact hnodeY'
  subst hki
  exact nb_nb_ne _ _ hEk'.symm

-- **Theorem R.** Given a merging cell, some merging cell is good (no bridge makes it bad).
--
theorem theoremR (hfr : Far t0 u0) (hopp0 : NoOpp V H0 t0 u0) {BS : List Bridge} {H : Finset Edge}
    (hr : Reach V H0 H BS)
    {c : Pt}
    (hc : IsCell V c) (ha : Alt H c) (hcut : CutSq H c)
    (hnp : ¬ ∃ b ∈ BS, c = b.cell (b.r - 2) ∨ c = b.E) :
    ∃ X, IsCell V X ∧ Alt H X ∧ CutSq H X ∧ (¬ ∃ b ∈ BS, X = b.cell (b.r - 2) ∨ X = b.E) ∧
      ∀ i (hi : i < BS.length), lowAt H BS (mergePair H X) i = false →
        X ≠ nb (BS[i]'hi).E (BS[i]'hi).a := by
  by_contra hno'
  have hno : ∀ Z, IsCell V Z → Alt H Z → CutSq H Z →
      (¬ ∃ b ∈ BS, Z = b.cell (b.r - 2) ∨ Z = b.E) →
      ∃ k, ∃ hk : k < BS.length, lowAt H BS (mergePair H Z) k = false ∧
        Z = nb (BS[k]'hk).E (BS[k]'hk).a := by
    intro Z h1 h2 h3 h4
    by_contra hz
    push Not at hz
    exact hno' ⟨Z, h1, h2, h3, h4, fun i hi hl => hz i hi hl⟩
  obtain ⟨i, hi, hlow, hX⟩ := hno c hc ha hcut hnp
  have hopp := noOpp_reach hr hopp0
  have hcX := mcell_of hc ha hcut
  obtain ⟨_, _, _, l1, l2⟩ := beyond_facts hVW hdc h0 hout0 hr hcX ha hi hX
  obtain ⟨sA, sB⟩ := side_or_t hVW hdc h0 hout0 hr hi (by rw [← hX]; exact l1)
    (by rw [← hX]; exact l2)
  rcases sA with cA | tA <;> rcases sB with cB | tB
  · -- both side squares are cells: two crossed bridges give `X` two nodes
    obtain ⟨altA, cutA, npA⟩ := l22 hVW hdc h0 hout0 hr hcX ha hi hlow hX (Or.inl rfl)
    obtain ⟨kA, hkA, lowA, hA⟩ := hno _ cA altA cutA npA
    obtain ⟨_, hEA, nA⟩ := l23 hVW hdc h0 hout0 hr hcX ha hi hlow hX (Or.inl rfl) cA hkA lowA hA
    obtain ⟨altB, cutB, npB⟩ := l22 hVW hdc h0 hout0 hr hcX ha hi hlow hX (Or.inr rfl)
    obtain ⟨kB, hkB, lowB, hB⟩ := hno _ cB altB cutB npB
    obtain ⟨_, hEB, nB⟩ := l23 hVW hdc h0 hout0 hr hcX ha hi hlow hX (Or.inr rfl) cB hkB lowB hB
    have hk : kA = kB := nA.symm.trans nB
    subst hk
    exact nb_latAB_ne c _ (hEA.symm.trans hEB)
  · exact r_core hVW hdc h0 hout0 hr hcX ha hi hlow hX (Or.inl rfl) cA hno
      (fun k hk hka hEk hso => by
        rcases hso.1 with h | h
        · rw [hka, latA_opp] at h; exact h
        · exfalso
          rw [hEk, hka, hX] at h
          exact t_farA2 hopp _ _ h tB)
  · exact r_core hVW hdc h0 hout0 hr hcX ha hi hlow hX (Or.inr rfl) cB hno
      (fun k hk hka hEk hso => by
        rcases hso.2 with h | h
        · rw [hka, latB_opp] at h; exact h
        · exfalso
          rw [hEk, hka, hX] at h
          exact t_farB2 hopp _ _ h tA)
  · obtain ⟨w, _, hw, hwA, _⟩ := tA
    obtain ⟨w', _, hw', hwB, _⟩ := tB
    exact two_sides hfr ⟨w, hw, hwA⟩ ⟨w', hw', hwB⟩

end theoremR

end HP

end SolidGridHam
