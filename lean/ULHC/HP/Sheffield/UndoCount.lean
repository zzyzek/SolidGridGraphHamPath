/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.HP.Sheffield.Undo
import ULHC.HP.CompCleanTg

/-!
# S4: the count of the undo plan (docs/S4_UNDO.md, Theorem I.8)

`plan H BS (u, v)`: from the newest bridge down, with a pending pair `(u, v)`:
* if `u`, `v` are joined before bridge `b` (in `flip H b.E`), lower `b`'s odd row and make
  `b`'s start pair pending;
* otherwise re-flip `b.E`.

`undo_count`: if the operations are intact and compatible (`OpsOK`) and the state `G` after the
half bridge has one piece fewer than `H`, with `Conn G = merge (Conn H) u v` on the relevant
points, then the plan ends with one piece fewer than `H0`.
-/

namespace ULHC

namespace HP

open Finset Classical

noncomputable def plan (H : Finset Edge) : List Bridge → Pt × Pt → List Join
  | [], _ => []
  | b :: BS, uv =>
    if Conn (flip H b.E) uv.1 uv.2 then
      ⟨b.q, b.a, b.r - 1⟩ :: plan (flip H b.E) BS (back1 b.q b.a, front1 b.q b.a)
    else ⟨b.E, b.a, 1⟩ :: plan (flip H b.E) BS uv

def applyAll (G : Finset Edge) : List Join → Finset Edge
  | [] => G
  | o :: os => applyAll (o.apply G) os

-- The operations are intact in `G`, odd strips of cells, their pairs are relevant points and no
-- relevant point is an interior point of any of them; an earlier one toggles no side of a later
-- one's cells.
--
structure OpsOK (W : Finset Pt) (G : Finset Edge) (ops : List Join) (P : Pt → Prop)
    (s0 t0 : Pt) : Prop where
  each : ∀ o ∈ ops, StripPat G o.c o.a o.n ∧ o.n % 2 = 1 ∧
    (∀ j < o.n, IsCell W (cellJ o.c o.a j)) ∧
    (∀ j < o.n, ¬ IsCorner s0 (cellJ o.c o.a j) ∧ ¬ IsCorner t0 (cellJ o.c o.a j)) ∧
    P (back1 o.c o.a) ∧ P (front1 o.c o.a) ∧ (∀ x, P x → ¬ IsMid o.c o.a (o.n - 1) x)
  compat : ops.Pairwise fun o o' => ∀ j < o'.n, ∀ e ∈ cellE (cellJ o'.c o'.a j), ¬ o.tog e

section undoCount

variable {V W : Finset Pt} {d : Pt → ℕ} {t0 u0 s0 p0 : Pt}

lemma stripPat_congr {G G' : Finset Edge} {c : Pt} {s : Side} {n : ℕ} (hn : 1 ≤ n)
    (h : ∀ j < n, ∀ e ∈ cellE (cellJ c s j), (e ∈ G' ↔ e ∈ G)) (hp : StripPat G c s n) :
    StripPat G' c s n := by
  have mem : ∀ j < n, back (cellJ c s j) s ∈ cellE (cellJ c s j) ∧
      front (cellJ c s j) s ∈ cellE (cellJ c s j) ∧ lat1 (cellJ c s j) s ∈ cellE (cellJ c s j) ∧
      lat2 (cellJ c s j) s ∈ cellE (cellJ c s j) := fun j _ => by
    rw [mkBF_cellE _ s]; simp [mkBF]
  obtain ⟨hb, hl, hf⟩ := hp
  refine ⟨?_, fun j hj => ?_, fun j hj => ?_⟩
  · have := h 0 hn _ (mem 0 hn).1; rw [cellJ_zero] at this; rw [this]; exact hb
  · rw [h j (by omega) _ (mem j (by omega)).2.2.1, h j (by omega) _ (mem j (by omega)).2.2.2]
    exact hl j hj
  · rw [h j (by omega) _ (mem j (by omega)).2.1]; exact hf j hj

lemma OpsOK.tail {G : Finset Edge} {o : Join} {os : List Join} {P : Pt → Prop}
    (h : OpsOK W G (o :: os) P s0 p0) : OpsOK W (o.apply G) os P s0 p0 := by
  obtain ⟨each, compat⟩ := h
  rw [List.pairwise_cons] at compat
  refine ⟨fun o' ho' => ?_, compat.2⟩
  obtain ⟨pat, odd, rest⟩ := each o' (List.mem_cons_of_mem _ ho')
  refine ⟨stripPat_congr (by omega) (fun j hj e he => joinKeep (compat.1 o' ho' j hj e he)) pat,
    odd, rest⟩

-- `merge (Conn H) u v` is `Conn Hp` when `u`, `v` are joined in `Hp` but not in `H`.
--
lemma merge_eq_prev {H Hp : Finset Edge} {β φ u v : Pt}
    (rel : ∀ x y, Conn Hp x y ↔ merge (Conn H) β φ x y) (hn : ¬ Conn H u v) (hb : Conn Hp u v)
    (x y : Pt) : merge (Conn H) u v x y ↔ Conn Hp x y := by
  have hR := isEqv_conn H
  rw [rel]
  rcases (rel u v).1 hb with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact absurd h hn
  · exact merge_congr hR h1 h2.symm x y
  · rw [merge_congr hR h1 h2.symm x y]
    constructor
    · rintro (h | ⟨h3, h4⟩ | ⟨h3, h4⟩)
      · exact Or.inl h
      · exact Or.inr (Or.inr ⟨h3, h4⟩)
      · exact Or.inr (Or.inl ⟨h3, h4⟩)
    · rintro (h | ⟨h3, h4⟩ | ⟨h3, h4⟩)
      · exact Or.inl h
      · exact Or.inr (Or.inr ⟨h3, h4⟩)
      · exact Or.inr (Or.inl ⟨h3, h4⟩)

-- **The count of the undo plan.**
--
theorem undo_count (hVW : V ⊆ W) (hdc : ∀ q, IsCell V q → ∀ z, IsCorner z q → d z = 2)
    {H0 : Finset Edge} (h0 : IsFactor W d H0)
    (hout0 : ∀ e ∈ H0, (e.p ∉ V → e.q = t0 ∨ e.q = u0) ∧ (e.q ∉ V → e.p = t0 ∨ e.p = u0))
    (hd2 : ∀ z ∈ W, z ≠ s0 → z ≠ p0 → d z = 2) (hds : d s0 = 1) (hs0 : s0 ∈ W) :
    ∀ BS H, Reach V H0 H BS → ∀ (G : Finset Edge) (uv : Pt × Pt) (P : Pt → Prop),
      IsFactor W d G → ncomp W G + 1 = ncomp W H →
      (∀ x y, P x → P y → (Conn G x y ↔ merge (Conn H) uv.1 uv.2 x y)) →
      P uv.1 → P uv.2 → ¬ Conn H uv.1 uv.2 → OpsOK W G (plan H BS uv) P s0 p0 →
      ncomp W (applyAll G (plan H BS uv)) + 1 = ncomp W H0 := by
  intro BS
  induction BS with
  | nil =>
    intro H hr G uv P _ hc _ _ _ _ _
    cases hr
    simpa [plan, applyAll] using hc
  | cons b BS ih =>
    intro H hr G uv P hG hc hrel hu hv hn hops
    cases hr with
    | step hr' hrs hm hnb =>
    rename_i Hp
    have hinvp := pinv_reach (t0 := t0) (u0 := u0) hVW hdc h0 hout0 hr'
    have hdegc := degc_of hVW hdc hinvp.fac
    have rel := step_rel hrs hdegc
    have nsplit := hrs.split
    have hcount := step_count hVW hrs hdegc
    have sub : ∀ x y, Conn (flip Hp b.E) x y → Conn Hp x y := fun x y h => (rel x y).2 (Or.inl h)
    have hD : Deg2Off W G s0 p0 := ⟨fun e he => by
        have := hG.1 e he
        exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem this.1),
          Finset.mem_insert_of_mem (Finset.mem_insert_of_mem this.2)⟩,
      fun z hz h1 h2 => by rw [hG.2 z hz, hd2 z hz h1 h2]⟩
    have hdeg : deg G s0 = 1 := by rw [hG.2 s0 hs0, hds]
    have hst : Conn G s0 p0 := conn_st hD hs0 hdeg
    have fac_of : ∀ o : Join, StripPat G o.c o.a o.n → (∀ j < o.n, IsCell W (cellJ o.c o.a j)) →
        IsFactor W d (o.apply G) := fun o pat cells => by
      obtain ⟨hin, hd⟩ := degs_flipCol o.n G (Inside.of_factor hG) pat cells
      exact ⟨fun e he => hin e he, fun z hz => by unfold Join.apply; rw [hd z, hG.2 z hz]⟩
    simp only [plan, flip_flip] at hops ⊢
    by_cases hb : Conn Hp uv.1 uv.2
    · -- lower the bridge's odd row
      rw [ite_eq_left hb] at hops ⊢
      simp only [applyAll]
      set o : Join := ⟨b.q, b.a, b.r - 1⟩ with ho
      obtain ⟨pat, odd, cells, corners, Px, Py, nomid⟩ := hops.each o List.mem_cons_self
      have hcr := hrs.crit
      have hnp : ¬ Conn G (back1 b.q b.a) (front1 b.q b.a) := by
        rw [hrel _ _ Px Py]
        rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact hcr.2.2.1 (sub _ _ h)
        · exact hcr.2.2.1 ((sub _ _ h1).trans (hb.trans (sub _ _ h2)))
        · exact hcr.2.2.1 ((sub _ _ h1).trans (hb.symm.trans (sub _ _ h2)))
      have hn1 : o.n - 1 + 1 = o.n := by omega
      obtain ⟨cnt, crel⟩ := strip_odd_pf (V := W) (c := o.c) (s := o.a) (o.n - 1) (by omega) G hD
        hst (fun j hj => cells j (by omega)) (fun j hj => corners j (by omega))
        (by rw [hn1]; exact pat) hnp
      rw [hn1] at cnt crel
      apply ih Hp hr' (o.apply G) (back1 b.q b.a, front1 b.q b.a) P (fac_of o pat cells)
        (by unfold Join.apply; omega) _ Px Py hcr.2.2.1 hops.tail
      intro x y hx hy
      unfold Join.apply
      rw [crel x y (nomid x hx) (nomid y hy)]
      have e1 := merge_on (R := Conn G) (S := merge (Conn (flip Hp b.E)) uv.1 uv.2) hrel Px Py hx hy
      unfold merge at e1
      rw [e1]
      have e2 := merge_eq_prev rel hn hb
      unfold merge at e2 ⊢
      simp only [e2]
      exact Iff.rfl
    · -- re-flip `E`
      rw [ite_eq_right hb] at hops ⊢
      simp only [applyAll]
      set o : Join := ⟨b.E, b.a, 1⟩ with ho
      obtain ⟨pat, odd, cells, corners, Px, Py, nomid⟩ := hops.each o List.mem_cons_self
      have hHp : ∀ x y, Conn (flip Hp b.E) x y → Conn Hp x y := sub
      have hbf : Conn Hp (back1 b.E b.a) (front1 b.E b.a) := (rel _ _).2 (merge_self (isEqv_conn _) _ _)
      have hnp : ¬ Conn G (back1 o.c o.a) (front1 o.c o.a) := by
        rw [hrel _ _ Px Py]
        rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact nsplit h
        · exact hb (((hHp _ _ h1).symm.trans hbf).trans (hHp _ _ h2).symm)
        · exact hb ((hHp _ _ h2).trans (hbf.symm.trans (hHp _ _ h1)))
      obtain ⟨cnt, crel⟩ := strip_odd_pf (V := W) (c := o.c) (s := o.a) 0 (by omega) G hD
        hst (fun j hj => cells j (by omega)) (fun j hj => corners j (by omega)) pat hnp
      have hon : o.n = 0 + 1 := rfl
      apply ih Hp hr' (o.apply G) uv P (fac_of o pat cells)
        (by unfold Join.apply; rw [hon]; omega) _ hu hv hb
        hops.tail
      intro x y hx hy
      unfold Join.apply
      rw [hon, crel x y (nomid x hx) (nomid y hy)]
      have e1 := merge_on (R := Conn G) (S := merge (Conn (flip Hp b.E)) uv.1 uv.2) hrel Px Py hx hy
      unfold merge at e1
      rw [e1]
      have hR := isEqv_conn (flip Hp b.E)
      have e3 := merge_comm2 hR uv.1 uv.2 (back1 b.E b.a) (front1 b.E b.a) x y
      unfold merge at e3
      rw [e3]
      have e4 : ∀ x y, merge (Conn (flip Hp b.E)) (back1 b.E b.a) (front1 b.E b.a) x y ↔
          Conn Hp x y := fun x y => (rel x y).symm
      unfold merge at e4 ⊢
      simp only [e4]

end undoCount

end HP

end ULHC
