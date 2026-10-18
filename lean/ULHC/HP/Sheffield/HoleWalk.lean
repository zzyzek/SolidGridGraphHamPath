/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.HP.Sheffield.HoleExposed

/-!
# An inner endpoint, the other on the boundary: the walk on the `s` side

`t` is inner, `s` has a missing king neighbour. Delete `t` and branch over the path's last edge
`w–t`; then delete `s` and branch over its successor. From there walk on the `s` side with `w`
fixed: the endpoint `s` has the point deleted last as its phantom `q`, and the hole `t` is the
phantom of `w`. When `w` and `s` are at king distance at least 3, enumerate the classes (`classSearchOne`)
and run the two-phantom loop; otherwise delete `s` again. Every point deleted by the walk lies
within king distance 2 of `w`, so the walk has at most 25 steps.

The deleted points form a path ending at `q`; adding its edges `P` to a factor gives degree 2 at
every inner point of `V` other than `t` (the first deleted point is not inner), so the factors have
no closed climb (`acyc_ext`).
-/

namespace ULHC

namespace HP

open Finset Classical

/-! ## Small facts -/

lemma inner_king {V : Finset Pt} {s m : Pt} (hs : Inner V s) (h1 : |m.1 - s.1| ≤ 1)
    (h2 : |m.2 - s.2| ≤ 1) : m ∈ V := by
  obtain ⟨a, b⟩ := m
  obtain ⟨x, y⟩ := s
  obtain ⟨c1, c2, c3, c4⟩ := hs
  simp only [IsCell, sub_add_cancel] at c1 c2 c3 c4
  simp only [abs_le] at h1 h2
  have ha : a = x - 1 ∨ a = x ∨ a = x + 1 := by omega
  have hb : b = y - 1 ∨ b = y ∨ b = y + 1 := by omega
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;> tauto

lemma deg_union_disj {G P : Finset Edge} (h : Disjoint G P) (v : Pt) :
    deg (G ∪ P) v = deg G v + deg P v := by
  rw [DF.deg_eq_card, DF.deg_eq_card, DF.deg_eq_card, Finset.filter_union,
    Finset.card_union_of_disjoint (Finset.disjoint_filter_filter h)]

lemma deg_zero_off {P : Finset Edge} {v : Pt} (h : ∀ e ∈ P, ¬ (e.p = v ∨ e.q = v)) :
    deg P v = 0 := by
  rw [DF.deg_eq_card, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  exact h

lemma missAdj_mono {U U' : Finset Pt} (hU : U' ⊆ U) {x y : Pt}
    (h : Relation.ReflTransGen (MissAdj U) x y) : Relation.ReflTransGen (MissAdj U') x y := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hab ih =>
    obtain ⟨h1, h2, h3, h4⟩ := hab
    exact ih.tail ⟨fun h => h1 (hU h), fun h => h2 (hU h), h3, h4⟩

lemma ends_flip {e : Edge} {u v : Pt} (h : Ends e u v) : Ends e v u := by
  rcases h with h | h
  exacts [Or.inr h, Or.inl h]

lemma pat_of_symm {U : Finset Pt} {p : Pt} {e0 : Edge} {F G : Finset Edge} (hpU : p ∉ U)
    (hF : PAt p e0 F) (hFG : ∀ e ∈ symmDiff F G, e.p ∈ U ∧ e.q ∈ U) : PAt p e0 G := by
  intro e he
  rw [← hF e he]
  have off : e ∉ symmDiff F G := fun h => by
    have := hFG e h
    rcases he with h' | h'
    · exact hpU (h' ▸ this.1)
    · exact hpU (h' ▸ this.2)
  rw [Finset.mem_symmDiff] at off
  push Not at off
  exact ⟨off.2, off.1⟩

-- A factor agreeing with a two-phantom state off the inner edges is a two-phantom state.
--
lemma notch2_of_symm {U : Finset Pt} {p q : Pt} {e0 e1 : Edge} {F G : Finset Edge} (hpU : p ∉ U)
    (hqU : q ∉ U) (hF : NotchF2 U p q e0 e1 F) (hG : IsFactor (insert q (insert p U)) (dST p q) G)
    (hFG : ∀ e ∈ symmDiff F G, e.p ∈ U ∧ e.q ∈ U) : NotchF2 U p q e0 e1 G :=
  ⟨hG, pat_of_symm hpU hF.patp hFG, pat_of_symm hqU hF.patq hFG⟩

/-! ## The walk's invariant -/

-- `Vo` is the original set, `t` its inner endpoint, `r` its other endpoint, `w–t` (`e0`) the
-- path's last edge; the current set is `U`, with endpoint `s` and phantom `q` (edge `e1`). `P` is
-- the deleted path from `r` to `q`.
--
structure WS (Vo : Finset Pt) (t r w : Pt) (e0 : Edge) (U : Finset Pt) (s q : Pt) (e1 : Edge) :
    Prop where
  solid : Solid Vo
  inner : Inner Vo t
  sub : U ⊆ Vo
  tU : t ∉ U
  rU : r ∉ U
  rt : r ≠ t
  sU : s ∈ U
  wU : w ∈ U
  sw : s ≠ w
  qU : q ∉ U
  qt : q ≠ t
  he0 : Ends e0 w t
  he1 : Ends e1 s q
  ext : ∃ P : Finset Edge, (∀ e ∈ P, e.p ∉ U ∧ e.q ∉ U) ∧ deg P t = 0 ∧
    ∀ v, v ≠ t → Inner Vo v → v ∉ U → deg P v + (if v = q then 1 else 0) = if v = r then 1 else 2
  esc : ∀ b, b ∉ U → Relation.ReflTransGen (MissAdj U) b t ∨
    Relation.ReflTransGen (MissAdj U) b r ∨
    ∃ b', Relation.ReflTransGen (MissAdj U) b b' ∧ ∀ p ∈ U, b'.1 < p.1

section ws

variable {Vo : Finset Pt} {t r w : Pt} {e0 : Edge} {U : Finset Pt} {s q : Pt} {e1 : Edge}

-- Degrees of a factor of the walk's two-phantom setting, with the deleted path added.
--
lemma ws_deg (hI : WS Vo t r w e0 U s q e1) {P : Finset Edge} (hPU : ∀ e ∈ P, e.p ∉ U ∧ e.q ∉ U)
    (hPt : deg P t = 0)
    (hPd : ∀ v, v ≠ t → Inner Vo v → v ∉ U → deg P v + (if v = q then 1 else 0) =
      if v = r then 1 else 2)
    {G : Finset Edge} (hG : IsFactor (insert q (insert t U)) (dST t q) G) :
    deg (G ∪ P) t = 1 ∧ ∀ v, v ≠ t → Inner Vo v → deg (G ∪ P) v = if v = r then 1 else 2 := by
  have hin := Inside.of_factor hG
  have hdis : Disjoint G P := by
    rw [Finset.disjoint_left]
    intro e heG heP
    have h1 := hin e heG
    have h2 := hPU e heP
    have hne : e.p ≠ e.q := edge_ne (Or.inl ⟨rfl, rfl⟩)
    simp only [Finset.mem_insert] at h1
    have ht : e.p = t ∨ e.q = t := by
      rcases h1 with ⟨h1 | h1 | h1, h3 | h3 | h3⟩
      · exact absurd (h1.trans h3.symm) hne
      · exact Or.inr h3
      · exact absurd h3 h2.2
      · exact Or.inl h1
      · exact Or.inl h1
      · exact absurd h3 h2.2
      · exact absurd h1 h2.1
      · exact absurd h1 h2.1
      · exact absurd h1 h2.1
    have := one_le_deg heP ht
    omega
  have hGt : deg G t = 1 := by
    rw [hG.2 t (by simp)]; exact dST_s t q
  refine ⟨by rw [deg_union_disj hdis, hGt, hPt], fun v hvt hv => ?_⟩
  rw [deg_union_disj hdis]
  by_cases hvU : v ∈ U
  · have hvq : v ≠ q := fun h => hI.qU (h ▸ hvU)
    have hvr : v ≠ r := fun h => hI.rU (h ▸ hvU)
    rw [hG.2 v (by simp [hvU]), dST_off hvt hvq, ite_eq_right hvr,
      deg_zero_off (fun e he h => by
        rcases h with h | h
        · exact (hPU e he).1 (h ▸ hvU)
        · exact (hPU e he).2 (h ▸ hvU))]
  · have h := hPd v hvt hv hvU
    by_cases hvq : v = q
    · subst hvq
      rw [hG.2 v (by simp), dST_t t v]
      rw [ite_eq_left rfl] at h
      omega
    · rw [ite_eq_right hvq] at h
      rw [deg_zero_of_inside hin (by simp [hvq, hvt, hvU])]
      omega

-- **No closed climb, one vortex** (the other endpoint `r` has a missing king neighbour).
--
theorem ws_acyc (hI : WS Vo t r w e0 U s q e1)
    (hrm : ∃ m, m ∉ Vo ∧ |m.1 - r.1| ≤ 1 ∧ |m.2 - r.2| ≤ 1) :
    ∀ G, IsFactor (insert q (insert t U)) (dST t q) G → ClimbAcyc U G := by
  obtain ⟨P, hPU, hPt, hPd⟩ := hI.ext
  refine acyc_ext hI.solid hI.inner hI.sub P hPU (fun G hG => ?_)
  obtain ⟨h1, h2⟩ := ws_deg hI hPU hPt hPd hG
  refine ⟨h1, fun v hvt hv => ?_⟩
  have hvr : v ≠ r := by
    rintro rfl
    obtain ⟨m, hm, hm1, hm2⟩ := hrm
    exact hm (inner_king hv hm1 hm2)
  rw [h2 v hvt hv, ite_eq_right hvr]

-- With `r` next to a missing point of the solid `Vo`, every missing point of `U` joins `t` or
-- escapes to the far left.
--
lemma ws_esc1 (hI : WS Vo t r w e0 U s q e1)
    (hrm : ∃ m, m ∉ Vo ∧ |m.1 - r.1| ≤ 1 ∧ |m.2 - r.2| ≤ 1) :
    ∀ b, b ∉ U → Relation.ReflTransGen (MissAdj U) b t ∨
      ∃ b', Relation.ReflTransGen (MissAdj U) b b' ∧ ∀ p ∈ U, b'.1 < p.1 := by
  obtain ⟨m, hm, hm1, hm2⟩ := hrm
  intro b hb
  rcases hI.esc b hb with h | h | h
  · exact Or.inl h
  · obtain ⟨b', h', hl⟩ := hI.solid m hm
    have hadj : MissAdj U r m := ⟨hI.rU, fun h => hm (hI.sub h), by rw [abs_sub_comm]; exact hm1,
      by rw [abs_sub_comm]; exact hm2⟩
    exact Or.inr ⟨b', h.trans (Relation.ReflTransGen.head hadj (missAdj_mono hI.sub h')),
      fun p hp => hl p (hI.sub hp)⟩
  · exact Or.inr h

-- **One walk step**: delete `s`, continue from its successor `x ≠ w`.
--
theorem ws_step (hI : WS Vo t r w e0 U s q e1) {x : Pt × Edge} (hx : x ∈ nbrsL s) (hxU : x.1 ∈ U)
    (hxw : x.1 ≠ w) : WS Vo t r w e0 (U.erase s) x.1 s x.2 := by
  have hends := nbrsL_ends hx
  have hsx : s ≠ x.1 := edge_ne hends
  have hst : s ≠ t := fun h => hI.tU (h ▸ hI.sU)
  have hsr : s ≠ r := fun h => hI.rU (h ▸ hI.sU)
  have hsq : s ≠ q := fun h => hI.qU (h ▸ hI.sU)
  have hqU' : q ∉ U.erase s := fun h => hI.qU (Finset.mem_of_mem_erase h)
  have he1 := hI.he1
  have hc := ends_close1 he1
  have tch : ∀ v, (e1.p = v ∨ e1.q = v) ↔ (v = s ∨ v = q) := by
    intro v
    rcases he1 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> constructor <;>
      rintro (h | h) <;> first | exact Or.inl h.symm | exact Or.inr h.symm
  obtain ⟨P, hPU, hPt, hPd⟩ := hI.ext
  have he1P : e1 ∉ P := by
    intro h
    have := hPU e1 h
    rcases (tch s).2 (Or.inl rfl) with h' | h'
    · exact this.1 (h' ▸ hI.sU)
    · exact this.2 (h' ▸ hI.sU)
  refine ⟨hI.solid, hI.inner, (Finset.erase_subset _ _).trans hI.sub,
    fun h => hI.tU (Finset.mem_of_mem_erase h), fun h => hI.rU (Finset.mem_of_mem_erase h), hI.rt,
    Finset.mem_erase.2 ⟨hsx.symm, hxU⟩,
    Finset.mem_erase.2 ⟨Ne.symm hI.sw, hI.wU⟩, hxw, by simp, hst, hI.he0,
    ends_flip hends, ⟨insert e1 P, ?_, ?_, ?_⟩, ?_⟩
  · intro e he
    rcases Finset.mem_insert.1 he with rfl | he
    · constructor
      · intro h
        rcases (tch e.p).1 (Or.inl rfl) with h' | h'
        · exact (by simp : s ∉ U.erase s) (h' ▸ h)
        · exact hqU' (h' ▸ h)
      · intro h
        rcases (tch e.q).1 (Or.inr rfl) with h' | h'
        · exact (by simp : s ∉ U.erase s) (h' ▸ h)
        · exact hqU' (h' ▸ h)
    · exact ⟨fun h => (hPU e he).1 (Finset.mem_of_mem_erase h),
        fun h => (hPU e he).2 (Finset.mem_of_mem_erase h)⟩
  · rw [DF.deg_insert_off he1P (fun h => by
      rcases (tch t).1 h with h' | h'
      · exact hst h'.symm
      · exact hI.qt h'.symm), hPt]
  · intro v hvt hv hvU
    by_cases hvs : v = s
    · subst hvs
      rw [DF.deg_insert_end he1P ((tch v).2 (Or.inl rfl)), ite_eq_left rfl, ite_eq_right hsr,
        deg_zero_off (fun e he h => by
          rcases h with h | h
          · exact (hPU e he).1 (h ▸ hI.sU)
          · exact (hPU e he).2 (h ▸ hI.sU))]
    · rw [ite_eq_right hvs]
      have hvU' : v ∉ U := fun h => hvU (Finset.mem_erase.2 ⟨hvs, h⟩)
      have h := hPd v hvt hv hvU'
      by_cases hvq : v = q
      · subst hvq
        rw [DF.deg_insert_end he1P ((tch v).2 (Or.inr rfl))]
        rw [ite_eq_left rfl] at h
        omega
      · rw [DF.deg_insert_off he1P (fun h => by
          rcases (tch v).1 h with h' | h'
          · exact hvs h'
          · exact hvq h')]
        rw [ite_eq_right hvq] at h
        omega
  · have hsub : U.erase s ⊆ U := Finset.erase_subset _ _
    have lift : ∀ b, b ∉ U → Relation.ReflTransGen (MissAdj (U.erase s)) b t ∨
        Relation.ReflTransGen (MissAdj (U.erase s)) b r ∨
        ∃ b', Relation.ReflTransGen (MissAdj (U.erase s)) b b' ∧ ∀ p ∈ U.erase s, b'.1 < p.1 := by
      intro b hb
      rcases hI.esc b hb with h | h | ⟨b', h, hl⟩
      · exact Or.inl (missAdj_mono hsub h)
      · exact Or.inr (Or.inl (missAdj_mono hsub h))
      · exact Or.inr (Or.inr ⟨b', missAdj_mono hsub h, fun p hp => hl p (Finset.mem_of_mem_erase hp)⟩)
    intro b hb
    by_cases hbs : b = s
    · subst hbs
      have hadj : MissAdj (U.erase b) b q := ⟨by simp, hqU', hc.1, hc.2⟩
      rcases lift q hI.qU with h | h | ⟨b', h, hl⟩
      · exact Or.inl (Relation.ReflTransGen.head hadj h)
      · exact Or.inr (Or.inl (Relation.ReflTransGen.head hadj h))
      · exact Or.inr (Or.inr ⟨b', Relation.ReflTransGen.head hadj h, hl⟩)
    · exact lift b (fun h => hb (Finset.mem_erase.2 ⟨hbs, h⟩))

-- **The walk's start**: `t` deleted with last edge `w–t`, then `s` deleted with successor `x`.
--
theorem ws_init {V : Finset Pt} {s t : Pt} (hs : Solid V) (ht : Inner V t) (hst : s ≠ t)
    {y : Pt × Edge} (hy : y ∈ nbrsL t) (hyV : y.1 ∈ V) (hys : y.1 ≠ s) {x : Pt × Edge}
    (hx : x ∈ nbrsL s) (hxV : x.1 ∈ V.erase t) (hxy : x.1 ≠ y.1) :
    WS V t s y.1 y.2 ((V.erase t).erase s) x.1 s x.2 := by
  have hyends := nbrsL_ends hy
  have hxends := nbrsL_ends hx
  have hty : t ≠ y.1 := edge_ne hyends
  have hsx : s ≠ x.1 := edge_ne hxends
  refine ⟨hs, ht, (Finset.erase_subset _ _).trans (Finset.erase_subset _ _), by simp, by simp,
    hst, Finset.mem_erase.2 ⟨hsx.symm, hxV⟩,
    Finset.mem_erase.2 ⟨hys, Finset.mem_erase.2 ⟨hty.symm, hyV⟩⟩, hxy, by simp, hst,
    ends_flip hyends, ends_flip hxends, ⟨∅, by simp, DF.deg_empty t, ?_⟩, ?_⟩
  · intro v hvt hv hvU
    have hvV : v ∈ V := hv.2.2.2.1
    have hvs : v = s := by
      by_contra h
      exact hvU (Finset.mem_erase.2 ⟨h, Finset.mem_erase.2 ⟨hvt, hvV⟩⟩)
    subst hvs
    rw [DF.deg_empty, ite_eq_left rfl, ite_eq_left rfl]
  · have hsub : (V.erase t).erase s ⊆ V :=
      (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
    intro b hb
    by_cases hbt : b = t
    · exact Or.inl (hbt ▸ Relation.ReflTransGen.refl)
    by_cases hbs : b = s
    · exact Or.inr (Or.inl (hbs ▸ Relation.ReflTransGen.refl))
    · have hbV : b ∉ V := fun h => hb (Finset.mem_erase.2 ⟨hbs, Finset.mem_erase.2 ⟨hbt, h⟩⟩)
      obtain ⟨b', h, hl⟩ := hs b hbV
      exact Or.inr (Or.inr ⟨b', missAdj_mono hsub h, fun p hp => hl p (hsub hp)⟩)

end ws

/-! ## The walk, for any final test -/

-- `fin U s q e1` decides the problem on `U` from `s` to `w` when `w` and `s` are far apart.
--
def holeCaseWalk (fin : Finset Pt → Pt → Pt → Edge → Bool) (w pw : Pt) :
    ℕ → Finset Pt → Pt → Pt → Edge → Bool
  | 0, _, _, _, _ => false
  | n + 1, U, s, q, e1 =>
    if U.card ≤ 2 then (nbrsL w).any (fun x => decide (x.1 = s))
    else if isFar w s && !phantomsOpposed w pw s q then fin U s q e1
    else (nbrsL s).any (fun x => decide (x.1 ∈ U) && decide (x.1 ≠ w) &&
      holeCaseWalk fin w pw n (U.erase s) x.1 s x.2)

-- The walk measure: points of `U` in the ring around `w`, plus one while `s`'s phantom is not
-- within king distance 2 of `w` (only possible at the start).
--
noncomputable def wmuG (U : Finset Pt) (w q : Pt) : ℕ :=
  ringc U w + if Close w q then 0 else 1

lemma wmuG_le (U : Finset Pt) (w q : Pt) : wmuG U w q ≤ 9 := by
  have := ringc_le U w
  unfold wmuG; split_ifs <;> omega

section walk

variable {Vo : Finset Pt} {t r w : Pt} {e0 : Edge} {fin : Finset Pt → Pt → Pt → Edge → Bool}

-- **The walk is correct** when its fuel exceeds the measure.
--
theorem holeCaseWalk_correct
    (hfin : ∀ U s q e1, WS Vo t r w e0 U s q e1 → FarN w t s q →
      (fin U s q e1 = true ↔ ∃ H, IsFactor U (dST s w) H ∧ ncomp U H = 1)) :
    ∀ n U s q e1, WS Vo t r w e0 U s q e1 → wmuG U w q < n →
      (holeCaseWalk fin w t n U s q e1 = true ↔ ∃ H, IsFactor U (dST s w) H ∧ ncomp U H = 1) := by
  intro n
  induction n with
  | zero => intro U s q e1 _ h; omega
  | succ n ih =>
    intro U s q e1 hI hmu
    simp only [holeCaseWalk]
    by_cases h2 : U.card ≤ 2
    · rw [ite_eq_left h2, hp_two hI.sw hI.sU hI.wU h2, List.any_eq_true]
      simp only [decide_eq_true_eq]
    rw [ite_eq_right h2]
    have h3 : 3 ≤ U.card := by omega
    by_cases hfar : (isFar w s && !phantomsOpposed w t s q) = true
    · rw [ite_eq_left hfar]
      simp only [Bool.and_eq_true, Bool.not_eq_true', phantomsOpposed, decide_eq_false_iff_not] at hfar
      exact hfin U s q e1 hI ⟨isFar_iff.1 hfar.1, hfar.2⟩
    rw [ite_eq_right hfar]
    have hmu' : wmuG (U.erase s) w s < n := by
      have hring := ringc_erase_le U w s
      unfold wmuG at hmu ⊢
      by_cases hf : Far w s
      · have hop : Opp w t s q := by
          by_contra hno
          exact hfar (by simp [isFar_iff.2 hf, phantomsOpposed, hno])
        rw [ite_eq_left (opp_close hop)]
        rw [ite_eq_right (opp_far_b hop)] at hmu
        omega
      · have hc1 : Close1 s w := by
          unfold Far at hf; push Not at hf; exact close1_comm hf.2
        have := ringc_erase_lt hI.sU hI.sw hc1
        have hc : Close w s := by unfold Close1 at hc1; unfold Close; rw [abs_sub_comm, abs_sub_comm w.2]; omega
        rw [ite_eq_left hc]
        split_ifs at hmu <;> omega
    rw [hp_swap, del_iff (Ne.symm hI.sw) hI.sU h3, List.any_eq_true]
    constructor
    · rintro ⟨x, hx, hb⟩
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
      obtain ⟨⟨hxU, hxw⟩, hb⟩ := hb
      refine ⟨x, hx, hxU, hxw, ?_⟩
      rw [← hp_swap]
      exact (ih _ _ _ _ (ws_step hI hx hxU hxw) hmu').1 hb
    · rintro ⟨x, hx, hxU, hxw, hH⟩
      refine ⟨x, hx, ?_⟩
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      rw [← hp_swap] at hH
      exact ⟨⟨hxU, hxw⟩, (ih _ _ _ _ (ws_step hI hx hxU hxw) hmu').2 hH⟩

end walk

-- Delete `t` (branch over `w`), delete `s` (branch over its successor), then walk.
--
def holeCase (fin : Pt → Edge → Finset Pt → Pt → Pt → Edge → Bool) (V : Finset Pt) (s t : Pt) :
    Bool :=
  if V.card ≤ 2 then (nbrsL t).any (fun x => decide (x.1 = s))
  else (nbrsL t).any fun y => decide (y.1 ∈ V) && decide (y.1 ≠ s) &&
    if (V.erase t).card ≤ 2 then (nbrsL y.1).any (fun x => decide (x.1 = s))
    else (nbrsL s).any fun x => decide (x.1 ∈ V.erase t) && decide (x.1 ≠ y.1) &&
      holeCaseWalk (fin y.1 y.2) y.1 t 10 ((V.erase t).erase s) x.1 s x.2

section holeCase

variable {V : Finset Pt} {s t : Pt} {fin : Pt → Edge → Finset Pt → Pt → Pt → Edge → Bool}

-- **One branch** (the path's last edge `w–t`).
--
theorem holeCase_branch (hs : Solid V) (ht : Inner V t) (hst : s ≠ t) (hsV : s ∈ V)
    (hfin : ∀ w e0 U s' q e1, WS V t s w e0 U s' q e1 → FarN w t s' q →
      (fin w e0 U s' q e1 = true ↔ ∃ H, IsFactor U (dST s' w) H ∧ ncomp U H = 1))
    {y : Pt × Edge} (hy : y ∈ nbrsL t) (hyV : y.1 ∈ V) (hys : y.1 ≠ s) :
    (if (V.erase t).card ≤ 2 then (nbrsL y.1).any (fun x => decide (x.1 = s))
      else (nbrsL s).any fun x => decide (x.1 ∈ V.erase t) && decide (x.1 ≠ y.1) &&
        holeCaseWalk (fin y.1 y.2) y.1 t 10 ((V.erase t).erase s) x.1 s x.2) = true ↔
      ∃ H, IsFactor (V.erase t) (dST s y.1) H ∧ ncomp (V.erase t) H = 1 := by
  have hty : t ≠ y.1 := edge_ne (nbrsL_ends hy)
  have hsV' : s ∈ V.erase t := Finset.mem_erase.2 ⟨hst, hsV⟩
  have hyV' : y.1 ∈ V.erase t := Finset.mem_erase.2 ⟨hty.symm, hyV⟩
  by_cases h2 : (V.erase t).card ≤ 2
  · rw [ite_eq_left h2, hp_two (Ne.symm hys) hsV' hyV' h2, List.any_eq_true]
    simp only [decide_eq_true_eq]
  rw [ite_eq_right h2, hp_swap, del_iff hys hsV' (by omega), List.any_eq_true]
  have hmu : wmuG ((V.erase t).erase s) y.1 s < 10 := by
    have := wmuG_le ((V.erase t).erase s) y.1 s; omega
  have hW := holeCaseWalk_correct (fin := fin y.1 y.2) (fun U s' q e1 hI hfr => hfin _ _ U s' q e1 hI hfr)
  constructor
  · rintro ⟨x, hx, hb⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
    obtain ⟨⟨hxV, hxy⟩, hb⟩ := hb
    refine ⟨x, hx, hxV, hxy, ?_⟩
    rw [← hp_swap]
    exact (hW 10 _ _ _ _ (ws_init hs ht hst hy hyV hys hx hxV hxy) hmu).1 hb
  · rintro ⟨x, hx, hxV, hxy, hH⟩
    refine ⟨x, hx, ?_⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    rw [← hp_swap] at hH
    exact ⟨⟨hxV, hxy⟩, (hW 10 _ _ _ _ (ws_init hs ht hst hy hyV hys hx hxV hxy) hmu).2 hH⟩

theorem holeCase_correct (hs : Solid V) (ht : Inner V t) (hst : s ≠ t) (hsV : s ∈ V)
    (hfin : ∀ w e0 U s' q e1, WS V t s w e0 U s' q e1 → FarN w t s' q →
      (fin w e0 U s' q e1 = true ↔ ∃ H, IsFactor U (dST s' w) H ∧ ncomp U H = 1)) :
    holeCase fin V s t = true ↔ ∃ H, IsFactor V (dST s t) H ∧ ncomp V H = 1 := by
  have htV : t ∈ V := ht.2.2.2.1
  unfold holeCase
  by_cases h2 : V.card ≤ 2
  · rw [ite_eq_left h2, hp_two hst hsV htV h2, List.any_eq_true]
    simp only [decide_eq_true_eq]
  rw [ite_eq_right h2, del_iff hst htV (by omega), List.any_eq_true]
  constructor
  · rintro ⟨y, hy, hb⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
    obtain ⟨⟨hyV, hys⟩, hb⟩ := hb
    exact ⟨y, hy, hyV, hys, (holeCase_branch hs ht hst hsV hfin hy hyV hys).1 hb⟩
  · rintro ⟨y, hy, hyV, hys, hH⟩
    refine ⟨y, hy, ?_⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨hyV, hys⟩, (holeCase_branch hs ht hst hsV hfin hy hyV hys).2 hH⟩

end holeCase

/-! ## One hole: the two-phantom hole run -/

-- Per class (`classRange`) the factor `classSearchOne` returns, then the two-phantom loop.
--
def oneHoleFinalTest (U : Finset Pt) (s w t q : Pt) (e0 e1 : Edge) : Bool :=
  isNarrow U &&
    match findFactor U (dST s w) with
    | none => false
    | some R => (classRange U).any fun h =>
        match classSearchOne U (insert e1 (insert e0 R)) t h with
        | some G => twoPhantomLoop U t q (U.card + 2) G
        | none => false

section oneHoleFinalTest

variable {Vo : Finset Pt} {t r w : Pt} {e0 : Edge} {U : Finset Pt} {s q : Pt} {e1 : Edge}

theorem oneHoleFinalTest_correct (hI : WS Vo t r w e0 U s q e1)
    (hrm : ∃ m, m ∉ Vo ∧ |m.1 - r.1| ≤ 1 ∧ |m.2 - r.2| ≤ 1) (hfr : FarN w t s q) :
    oneHoleFinalTest U s w t q e0 e1 = true ↔ ∃ H, IsFactor U (dST s w) H ∧ ncomp U H = 1 := by
  have hVW : U ⊆ insert q (insert t U) :=
    (Finset.subset_insert _ _).trans (Finset.subset_insert _ _)
  unfold oneHoleFinalTest
  rw [Bool.and_eq_true]
  constructor
  · rintro ⟨_, hb⟩
    rcases hR : findFactor U (dST s w) with _ | R
    · rw [hR] at hb; simp at hb
    rw [hR] at hb
    simp only [List.any_eq_true] at hb
    obtain ⟨h, _, hb⟩ := hb
    rcases hT : classSearchOne U (insert e1 (insert e0 R)) t h with _ | G
    · rw [hT] at hb; simp at hb
    rw [hT] at hb
    simp only at hb
    have hF := two_up hI.sw hI.sU hI.wU hI.tU hI.qU hI.qt.symm hI.he0 hI.he1
      (findFactor_some (dST_le s w) hR)
    obtain ⟨hGf, hFG, _⟩ := classSearchOne_sound hVW hF.fac hT
    have hG := notch2_of_symm hI.tU hI.qU hF hGf hFG
    rw [twoPhantomLoop_eq hI.sU hI.wU hI.tU hI.qU hI.he0 hI.he1 hfr _ _ hG] at hb
    obtain ⟨G', hG', h1⟩ := runSC2_sound hI.sU hI.wU hI.tU hI.qU hI.he0 hI.he1 hfr _ _ hG hb
    exact two_down hI.sw hI.sU hI.wU hI.tU hI.qU hI.qt.symm hI.he0 hI.he1 hG' h1
  · rintro ⟨Hs, hHs, hHam⟩
    refine ⟨by
      simp only [isNarrow, Bool.and_eq_true, decide_eq_true_eq]
      exact narrow_of_ncomp (Inside.of_factor hHs) hHam, ?_⟩
    rcases hR : findFactor U (dST s w) with _ | R
    · exact absurd ⟨Hs, hHs⟩ (findFactor_none (dST_le s w) hR)
    simp only [List.any_eq_true]
    have hF := two_up hI.sw hI.sU hI.wU hI.tU hI.qU hI.qt.symm hI.he0 hI.he1
      (findFactor_some (dST_le s w) hR)
    have hHN := two_up hI.sw hI.sU hI.wU hI.tU hI.qU hI.qt.symm hI.he0 hI.he1 hHs
    have hFH := two_symm hF hHN
    obtain ⟨hmem, hev⟩ := class_mem_hRange (t := t) hFH
    refine ⟨_, hmem, ?_⟩
    have hne := classSearchOne_complete hF.fac hHN.fac hFH hev
    rcases hT : classSearchOne U (insert e1 (insert e0 R)) t
      (D (insert e1 (insert e0 R)) (insert e1 (insert e0 Hs)) t / 2) with _ | G
    · exact absurd hT hne
    simp only
    obtain ⟨hGf, hFG, _⟩ := classSearchOne_sound hVW hF.fac hT
    have hG := notch2_of_symm hI.tU hI.qU hF hGf hFG
    have hsol := classSearchOne_solidFor hVW hF.fac hI.tU (ws_esc1 hI hrm) hT hHN.fac hFH hev
    have hle := ncomp_le_card (X := U) (F := G)
    rw [twoPhantomLoop_eq hI.sU hI.wU hI.tU hI.qU hI.he0 hI.he1 hfr _ _ hG]
    exact runSC2_complete_hole (ws_acyc hI hrm) hI.tU hI.qU hI.qt.symm hI.sw hI.sU hI.wU hI.he0
      hI.he1 hfr hHs hHam _ G hG hsol (by omega)

end oneHoleFinalTest

/-! ## An inner endpoint, the other with a missing king neighbour -/

def oneHoleCase (V : Finset Pt) (s t : Pt) : Bool :=
  holeCase (fun w e0 U s' q e1 => oneHoleFinalTest U s' w t q e0 e1) V s t

section oneHoleCase

variable {V : Finset Pt} {s t : Pt}

-- **An inner endpoint, the other with a missing king neighbour.** For solid `V`, `t` inner and
-- `s ≠ t` in `V` with a missing king neighbour, `oneHoleCase` decides the Hamiltonian `s`–`t` path
-- problem.
--
theorem oneHoleCase_correct (hs : Solid V) (ht : Inner V t) (hst : s ≠ t) (hsV : s ∈ V)
    (hms : ∃ m, m ∉ V ∧ |m.1 - s.1| ≤ 1 ∧ |m.2 - s.2| ≤ 1) :
    oneHoleCase V s t = true ↔ ∃ H, IsFactor V (dST s t) H ∧ ncomp V H = 1 :=
  holeCase_correct hs ht hst hsV (fun _ _ _ _ _ _ hI hfr => oneHoleFinalTest_correct hI hms hfr)

end oneHoleCase

end HP

end ULHC
