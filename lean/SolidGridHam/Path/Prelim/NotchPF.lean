/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import SolidGridHam.Path.Prelim.Dangle
import SolidGridHam.Cycle.Comp
import SolidGridHam.Cycle.Enum
import SolidGridHam.Path.Prelim.StripCountPF
import SolidGridHam.Cycle.Phase2
import SolidGridHam.Path.Prelim.TheoremAPF

/-!
# A notch endpoint: the path's end moved to a missing neighbour

`t ∈ V` has a missing neighbour `p ∉ V` (the edge `e0` from `t` to `p`); `p` may have other
neighbours in `V` (a notch), so squares with corner `p` can have their other three corners in
`V`. They are not cells of `V`. Factors live on `W = insert p V`, with `e0` the only edge at
`p` (`PAt`). Hamiltonian `s`–`t` paths of `V` are the Hamiltonian `s`–`p` paths of `W` through
`e0`.

The algorithm keeps `e0` (no cell of `V` has `e0` as a side) and runs `runPF V s p`.

This file: the bridges between `V` and `W` (cells, component counts, `μ`, `D = 0` off the cells
of `V`), and the walk's start on `W` (`lemmaB_t2` applied to `W` and `p`).
-/

namespace SolidGridHam

namespace HP

open Finset Classical

/-! ## Factors through `e0` -/

-- `e0` is the only edge of `G` at `p`.
--
def PAt (p : Pt) (e0 : Edge) (G : Finset Edge) : Prop :=
  ∀ e : Edge, (e.p = p ∨ e.q = p) → (e ∈ G ↔ e = e0)

section bridge

variable {V : Finset Pt} {p : Pt} {e0 : Edge}

lemma cellE_inside {c : Pt} (hc : IsCell V c) {e : Edge} (he : e ∈ cellE c) : e.p ∈ V ∧ e.q ∈ V := by
  obtain ⟨x, y⟩ := c
  obtain ⟨h1, h2, h3, h4⟩ := hc
  simp only [cellE, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl <;> simp [bot, top, lft, rgt, Edge.q] <;>
    exact ⟨by assumption, by assumption⟩

-- No side of a cell of `V` has the missing point `p` as an end.
--
lemma not_cellE_of_p (hpV : p ∉ V) {c : Pt} (hc : IsCell V c) {e : Edge} (he : e.p = p ∨ e.q = p) :
    e ∉ cellE c := fun hm => by
  obtain ⟨h1, h2⟩ := cellE_inside hc hm
  rcases he with h | h
  · exact hpV (h ▸ h1)
  · exact hpV (h ▸ h2)

lemma PAt.flip {G : Finset Edge} (hpV : p ∉ V) (h : PAt p e0 G) {c : Pt} (hc : IsCell V c) :
    PAt p e0 (SolidGridHam.flip G c) := fun e he => by
  rw [mem_flip_off (not_cellE_of_p hpV hc he)]; exact h e he

lemma PAt.flipCol {c : Pt} {sd : Side} (hpV : p ∉ V) :
    ∀ n (G : Finset Edge), PAt p e0 G → (∀ j < n, IsCell V (cellJ c sd j)) →
      PAt p e0 (SolidGridHam.flipCol G c sd n) := by
  intro n
  induction n with
  | zero => intro G h _; exact h
  | succ n ih =>
    intro G h hc
    exact ih _ (h.flip hpV (hc n (by omega))) (fun j hj => hc j (by omega))

-- Two factors on `insert p V` through `e0` differ only on edges inside `V`.
--
lemma symmDiff_inside_of_PAt {G H : Finset Edge} (hG : Inside (insert p V) G)
    (hH : Inside (insert p V) H) (pG : PAt p e0 G) (pH : PAt p e0 H) :
    ∀ e ∈ symmDiff G H, e.p ∈ V ∧ e.q ∈ V := by
  intro e he
  have hW : e.p ∈ insert p V ∧ e.q ∈ insert p V := by
    rw [Finset.mem_symmDiff] at he
    rcases he with ⟨h, _⟩ | ⟨h, _⟩
    · exact hG e h
    · exact hH e h
  have hnp : e.p ≠ p ∧ e.q ≠ p := by
    constructor <;> intro h <;> rw [Finset.mem_symmDiff] at he
    · have k1 := pG e (Or.inl h); have k2 := pH e (Or.inl h); tauto
    · have k1 := pG e (Or.inr h); have k2 := pH e (Or.inr h); tauto
  exact ⟨(Finset.mem_insert.1 hW.1).resolve_left hnp.1, (Finset.mem_insert.1 hW.2).resolve_left hnp.2⟩

-- A cell of `insert p V` without corner `p` is a cell of `V`.
--
lemma cell_of_insP {c : Pt} (hc : IsCell (insert p V) c) (hp : ¬ IsCorner p c) : IsCell V c := by
  obtain ⟨c1, c2, c3, c4⟩ := hc
  unfold IsCorner at hp
  push Not at hp
  obtain ⟨n1, n2, n3, n4⟩ := hp
  exact ⟨(Finset.mem_insert.1 c1).resolve_left (Ne.symm n1),
    (Finset.mem_insert.1 c2).resolve_left (Ne.symm n2),
    (Finset.mem_insert.1 c3).resolve_left (Ne.symm n3),
    (Finset.mem_insert.1 c4).resolve_left (Ne.symm n4)⟩

lemma corner_of_not_cell {c : Pt} (hc : IsCell (insert p V) c) (hn : ¬ IsCell V c) : IsCorner p c := by
  by_contra h; exact hn (cell_of_insP hc h)

-- **Component counts agree** when `p` hangs on `t ∈ V` by an edge of `G`.
--
theorem ncomp_insP {G : Finset Edge} {t : Pt} (hGW : Inside (insert p V) G) (htV : t ∈ V)
    (hpt : Conn G p t) : ncomp (insert p V) G = ncomp V G := by
  unfold ncomp
  set W := insert p V
  have hVW : V ⊆ W := Finset.subset_insert _ _
  have h1 : W.image (cls W G) = V.image (cls W G) := by
    ext S
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rcases Finset.mem_insert.1 hx with rfl | hx
      · refine ⟨t, htV, ?_⟩
        ext z; simp only [cls, Finset.mem_filter]
        exact ⟨fun ⟨hz, h⟩ => ⟨hz, hpt.trans h⟩, fun ⟨hz, h⟩ => ⟨hz, hpt.symm.trans h⟩⟩
      · exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hVW hx, rfl⟩
  have h2 : V.image (cls V G) = (V.image (cls W G)).image (fun S => S.filter (· ∈ V)) := by
    rw [Finset.image_image]
    apply Finset.image_congr
    intro x _
    ext z
    simp only [cls, Function.comp, Finset.mem_filter]
    constructor
    · rintro ⟨hz, hc⟩; exact ⟨⟨hVW hz, hc⟩, hz⟩
    · rintro ⟨⟨_, hc⟩, hz⟩; exact ⟨hz, hc⟩
  rw [h1, h2]
  symm
  apply Finset.card_image_of_injOn
  intro A hA B hB hAB
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hA)
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hB)
  have hxy : x ∈ (cls W G y).filter (· ∈ V) := by
    have h := hAB; simp only at h; rw [← h]; simp only [cls, Finset.mem_filter]
    exact ⟨⟨hVW hx, Conn.refl G x⟩, hx⟩
  simp only [cls, Finset.mem_filter] at hxy
  have hc : Conn G y x := hxy.1.2
  ext z
  simp only [cls, Finset.mem_filter]
  exact ⟨fun ⟨hz, h⟩ => ⟨hz, hc.trans h⟩, fun ⟨hz, h⟩ => ⟨hz, hc.symm.trans h⟩⟩

-- **`μ` agrees** when `D` vanishes on the squares at `p`.
--
theorem mu_insP {F H : Finset Edge} (hz : ∀ c, ¬ IsCell V c → D F H c = 0) :
    mu (insert p V) F H = mu V F H := by
  unfold mu
  symm
  apply Finset.sum_subset
  · intro c hc
    exact mem_cells.2 (isCell_mono (mem_cells.1 hc) (Finset.subset_insert _ _))
  · intro c _ hn
    rw [hz c (fun h => hn (mem_cells.2 h))]; rfl

end bridge

/-! ## The notch setting -/

section notch

variable {V : Finset Pt} {s t p : Pt} {e0 : Edge}

lemma e0_mem {G : Finset Edge} (he0 : Ends e0 t p) (pG : PAt p e0 G) : e0 ∈ G :=
  (pG e0 (by rcases he0 with ⟨_, h⟩ | ⟨h, _⟩ <;> simp [h])).2 rfl

-- The facts a factor on `insert p V` through `e0` carries over to `V`.
--
structure NotchF (V : Finset Pt) (s p : Pt) (e0 : Edge) (G : Finset Edge) : Prop where
  fac : IsFactor (insert p V) (dST s p) G
  pat : PAt p e0 G

lemma NotchF.conn {G : Finset Edge} (he0 : Ends e0 t p) (hG : NotchF V s p e0 G) : Conn G p t :=
  (he0.conn (e0_mem he0 hG.pat)).symm

lemma NotchF.ncomp {G : Finset Edge} (htV : t ∈ V) (he0 : Ends e0 t p) (hG : NotchF V s p e0 G) :
    ncomp (insert p V) G = ncomp V G :=
  ncomp_insP (Inside.of_factor hG.fac) htV (hG.conn he0)

lemma NotchF.dzero {G H : Finset Edge} (hs : Solid V) (hG : NotchF V s p e0 G)
    (hH : NotchF V s p e0 H) : ∀ c, ¬ IsCell V c → D G H c = 0 := fun _ hc =>
  D_eq_zero_of_not_cellW hG.fac hH.fac
    (symmDiff_inside_of_PAt (Inside.of_factor hG.fac) (Inside.of_factor hH.fac) hG.pat hH.pat) hs hc

lemma NotchF.solidFor {G H : Finset Edge} (hs : Solid V) (hG : NotchF V s p e0 G)
    (hH : NotchF V s p e0 H) : SolidFor (insert p V) G H :=
  SolidFor.of_solidW hG.fac hH.fac
    (symmDiff_inside_of_PAt (Inside.of_factor hG.fac) (Inside.of_factor hH.fac) hG.pat hH.pat) hs
    (Finset.subset_insert _ _)

lemma NotchF.mu {G H : Finset Edge} (hs : Solid V) (hG : NotchF V s p e0 G)
    (hH : NotchF V s p e0 H) : mu (insert p V) G H = mu V G H :=
  mu_insP (hG.dzero hs hH)

-- With `s` a corner of no cell of `V`, `D` vanishes on the cells at both endpoints.
--
lemma NotchF.zero {G H : Finset Edge} (hs : Solid V) (hpV : p ∉ V)
    (hsD : ∀ c, IsCell V c → ¬ IsCorner s c) (hG : NotchF V s p e0 G) (hH : NotchF V s p e0 H) :
    ZeroAt G H s p := by
  intro w hw
  apply hG.dzero hs hH
  intro hc
  rcases hw with h | h
  · exact hsD w hc h
  · rcases h with h | h | h | h
    · exact hpV (h ▸ hc.1)
    · exact hpV (h ▸ hc.2.1)
    · exact hpV (h ▸ hc.2.2.1)
    · exact hpV (h ▸ hc.2.2.2)

lemma NotchF.strip {G : Finset Edge} (hpV : p ∉ V) (hG : NotchF V s p e0 G) {σ : StripSpec}
    (hpat : StripPat G σ.c σ.s σ.n) (hc : ∀ j < σ.n, IsCell V (cellJ σ.c σ.s j)) :
    NotchF V s p e0 (applyS G σ) :=
  ⟨factor_flipCol σ.n G hG.fac hpat (fun j hj => isCell_mono (hc j hj) (Finset.subset_insert _ _)),
    PAt.flipCol hpV σ.n G hG.pat hc⟩

lemma NotchF.flip {G : Finset Edge} (hpV : p ∉ V) (hG : NotchF V s p e0 G) {c : Pt}
    (hc : IsCell V c) (hF : IsFactor (insert p V) (dST s p) (SolidGridHam.flip G c)) :
    NotchF V s p e0 (SolidGridHam.flip G c) :=
  ⟨hF, hG.pat.flip hpV hc⟩

lemma dST_off {s p z : Pt} (h1 : z ≠ s) (h2 : z ≠ p) : dST s p z = 2 := by unfold dST; simp [h1, h2]
lemma dST_s (s p : Pt) : dST s p s = 1 := by unfold dST; simp
lemma dST_t (s p : Pt) : dST s p p = 1 := by unfold dST; simp

lemma NotchF.deg2Off {G : Finset Edge} (hG : NotchF V s p e0 G) : Deg2Off V G s p :=
  ⟨inside_mono_right (Inside.of_factor hG.fac) (Finset.subset_insert _ _),
    fun z hz h1 h2 => by rw [hG.fac.2 z (Finset.mem_insert_of_mem hz)]; exact dST_off h1 h2⟩

lemma NotchF.degS {G : Finset Edge} (hsV : s ∈ V) (hG : NotchF V s p e0 G) : deg G s = 1 := by
  rw [hG.fac.2 s (Finset.mem_insert_of_mem hsV)]; exact dST_s s p

lemma NotchF.le2 {G : Finset Edge} (hG : NotchF V s p e0 G) : ∀ z, deg G z ≤ 2 := fun z => by
  by_cases hz : z ∈ insert p V
  · rw [hG.fac.2 z hz]; exact dST_le s p z
  · rw [deg_zero_of_inside (Inside.of_factor hG.fac) hz]; omega

-- The two cells beside a cell, on its two lateral sides, have no common corner.
--
lemma corner_latAB {z e : Pt} {sd : Side} (hA : IsCorner z (nb e (latA sd)))
    (hB : IsCorner z (nb e (latB sd))) : False := by
  obtain ⟨x, y⟩ := e
  cases sd <;> simp only [latA, latB, nb, IsCorner] at hA hB <;>
    rcases hA with h | h | h | h <;> rcases hB with h' | h' | h' | h' <;>
    rw [h] at h' <;> simp only [Prod.mk.injEq] at h' <;> omega

/-! ## The algorithm's decisions on factors through `e0` -/

lemma card_insP : (insert p V).card ≤ V.card + 1 := Finset.card_insert_le p V

/-! ## Completeness of `runPF V s p` at a notch -/

/-! ## Soundness of `runPF V s p` at a notch -/

/-! ## The top theorem -/

-- An s–t path-factor of `V` plus `e0` is a factor through `e0`.
--
lemma notch_up (hst : s ≠ t) (htV : t ∈ V) (hpV : p ∉ V) (he0 : Ends e0 t p) {R : Finset Edge}
    (hR : IsFactor V (dST s t) R) : NotchF V s p e0 (insert e0 R) := by
  have hin : Inside V R := fun e he => hR.1 e he
  have hnot : e0 ∉ R := fun h => by
    have := hin e0 h
    rcases he0 with ⟨_, h2⟩ | ⟨h1, _⟩
    · exact hpV (h2 ▸ this.2)
    · exact hpV (h1 ▸ this.1)
  have hep : e0.p = p ∨ e0.q = p := by rcases he0 with ⟨_, h⟩ | ⟨h, _⟩ <;> simp [h]
  have het : e0.p = t ∨ e0.q = t := by rcases he0 with ⟨h, _⟩ | ⟨_, h⟩ <;> simp [h]
  have htp : t ≠ p := fun h => hpV (h ▸ htV)
  refine ⟨⟨fun e he => ?_, fun z hz => ?_⟩, fun e hp => ?_⟩
  · rcases Finset.mem_insert.1 he with rfl | he
    · rcases he0 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨by rw [h1]; exact Finset.mem_insert_of_mem htV,
          by rw [h2]; exact Finset.mem_insert_self _ _⟩
      · exact ⟨by rw [h1]; exact Finset.mem_insert_self _ _,
          by rw [h2]; exact Finset.mem_insert_of_mem htV⟩
    · obtain ⟨a, b⟩ := hR.1 e he
      exact ⟨Finset.mem_insert_of_mem a, Finset.mem_insert_of_mem b⟩
  · rcases Finset.mem_insert.1 hz with rfl | hz
    · rw [DF.deg_insert_end hnot hep, deg_zero_of_inside hin hpV]; unfold dST; simp
    · by_cases hzt : z = t
      · subst hzt
        rw [DF.deg_insert_end hnot het, hR.2 z hz]
        unfold dST; simp [Ne.symm hst, htp]
      · have hzp : z ≠ p := fun h => hpV (h ▸ hz)
        have hoff : ¬ (e0.p = z ∨ e0.q = z) := by
          rcases he0 with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · rw [h1, h2]; rintro (h | h)
            · exact hzt h.symm
            · exact hzp h.symm
          · rw [h1, h2]; rintro (h | h)
            · exact hzp h.symm
            · exact hzt h.symm
        rw [DF.deg_insert_off hnot hoff, hR.2 z hz]
        unfold dST; simp [hzt, hzp]
  · constructor
    · intro he
      rcases Finset.mem_insert.1 he with h | he
      · exact h
      · have := hin e he
        rcases hp with h | h
        · exact absurd (h ▸ this.1) hpV
        · exact absurd (h ▸ this.2) hpV
    · rintro rfl; exact Finset.mem_insert_self _ _

-- A factor through `e0` with one component on `V`, minus `e0`, is a Hamiltonian s–t path of `V`.
--
lemma notch_down (hst : s ≠ t) (htV : t ∈ V) (hpV : p ∉ V) (he0 : Ends e0 t p)
    {G : Finset Edge} (hG : NotchF V s p e0 G) (h1 : ncomp V G = 1) :
    IsFactor V (dST s t) (G.erase e0) ∧ ncomp V (G.erase e0) = 1 := by
  have htp : t ≠ p := fun h => hpV (h ▸ htV)
  have het : e0.p = t ∨ e0.q = t := by rcases he0 with ⟨h, _⟩ | ⟨_, h⟩ <;> simp [h]
  have touch : ∀ e ∈ G, (e.p = p ∨ e.q = p) → e = e0 := fun e he hp => (hG.pat e hp).1 he
  have he0G := e0_mem he0 hG.pat
  have hH := hG.fac
  set H := G.erase e0 with hHdef
  have offp : ∀ e ∈ H, ¬ (e.p = p ∨ e.q = p) := by
    intro e he hp
    obtain ⟨hne, heH⟩ := Finset.mem_erase.1 he
    exact hne (touch e heH hp)
  refine ⟨⟨fun e he => ?_, fun z hz => ?_⟩, ?_⟩
  · obtain ⟨a, b⟩ := hH.1 e (Finset.mem_erase.1 he).2
    have hn := offp e he
    push Not at hn
    exact ⟨(Finset.mem_insert.1 a).resolve_left hn.1, (Finset.mem_insert.1 b).resolve_left hn.2⟩
  · have hzp : z ≠ p := fun h => hpV (h ▸ hz)
    by_cases hzt : z = t
    · subst hzt
      have := DF.deg_erase_end he0G het
      rw [hH.2 z (Finset.mem_insert_of_mem hz)] at this
      unfold dST at this ⊢
      simp [Ne.symm hst, htp] at this ⊢
      omega
    · have hoff : ¬ (e0.p = z ∨ e0.q = z) := by
        rcases he0 with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h1, h2]; rintro (h | h)
          · exact hzt h.symm
          · exact hzp h.symm
        · rw [h1, h2]; rintro (h | h)
          · exact hzp h.symm
          · exact hzt h.symm
      rw [DF.deg_erase_off he0G hoff, hH.2 z (Finset.mem_insert_of_mem hz)]
      unfold dST; simp [hzt, hzp]
  · -- A walk of `G` from a vertex of `V` reaches every vertex of `V` it reaches without `p`.
    --
    have walk : ∀ x ∈ V, ∀ y, Conn G x y → (y ≠ p → Conn H x y) ∧ (y = p → Conn H x t) := by
      intro x hx y hxy
      induction hxy with
      | refl => exact ⟨fun _ => Conn.refl _ _, fun h => absurd (h ▸ hx) hpV⟩
      | @tail y z _ hyz ih =>
        obtain ⟨e, he, hends⟩ := hyz
        by_cases hee : e = e0
        · subst hee
          rcases he0 with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · rcases hends with ⟨a, b⟩ | ⟨a, b⟩
            · rw [h1] at a; rw [h2] at b; subst a; subst b
              exact ⟨fun h => absurd rfl h, fun _ => ih.1 htp⟩
            · rw [h1] at a; rw [h2] at b; subst a; subst b
              exact ⟨fun _ => ih.2 rfl, fun h => absurd h htp⟩
          · rcases hends with ⟨a, b⟩ | ⟨a, b⟩
            · rw [h1] at a; rw [h2] at b; subst a; subst b
              exact ⟨fun _ => ih.2 rfl, fun h => absurd h htp⟩
            · rw [h1] at a; rw [h2] at b; subst a; subst b
              exact ⟨fun h => absurd rfl h, fun _ => ih.1 htp⟩
        · have heH : e ∈ H := Finset.mem_erase.2 ⟨hee, he⟩
          have hn := offp e heH
          push Not at hn
          have hyp : y ≠ p := by rcases hends with ⟨a, _⟩ | ⟨_, b⟩; exacts [a ▸ hn.1, b ▸ hn.2]
          have hzp : z ≠ p := by rcases hends with ⟨_, b⟩ | ⟨a, _⟩; exacts [b ▸ hn.2, a ▸ hn.1]
          exact ⟨fun _ => (ih.1 hyp).trans (Relation.ReflTransGen.single ⟨e, heH, hends⟩),
            fun h => absurd h hzp⟩
    refine ncomp_one_of_conn htV (fun x hx y hy => ?_)
    have hy' : y ≠ p := fun h => hpV (h ▸ hy)
    exact (walk x hx y (conn_of_ncomp_one h1 hx hy)).1 hy'

end notch

end HP

end SolidGridHam
