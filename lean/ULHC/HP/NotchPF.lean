/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.HP.Dangle
import ULHC.HP.CompW
import ULHC.HP.WalkStartS

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

namespace ULHC

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
    PAt p e0 (ULHC.flip G c) := fun e he => by
  rw [mem_flip_off (not_cellE_of_p hpV hc he)]; exact h e he

lemma PAt.flipCol {c : Pt} {sd : Side} (hpV : p ∉ V) :
    ∀ n (G : Finset Edge), PAt p e0 G → (∀ j < n, IsCell V (cellJ c sd j)) →
      PAt p e0 (ULHC.flipCol G c sd n) := by
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
    (hc : IsCell V c) (hF : IsFactor (insert p V) (dST s p) (ULHC.flip G c)) :
    NotchF V s p e0 (ULHC.flip G c) :=
  ⟨hF, hG.pat.flip hpV hc⟩

lemma dST_off {s p z : Pt} (h1 : z ≠ s) (h2 : z ≠ p) : dST s p z = 2 := by unfold dST; simp [h1, h2]
lemma dST_s (s p : Pt) : dST s p s = 1 := by unfold dST; simp
lemma dST_t (s p : Pt) : dST s p p = 1 := by unfold dST; simp

-- **The walk's start on `insert p V`.** In a state without a restricted Type III cell and with
-- two components or more, `lemmaB_t2` on `insert p V` with endpoint `p` gives a walk strip of
-- `V`, or two components and a Type III square with corner `p` (not a cell of `V`).
--
theorem notch_lemmaB {G H : Finset Edge} (hs : Solid V) (hsV : s ∈ V) (htV : t ∈ V)
    (hpV : p ∉ V) (he0 : Ends e0 t p) (hsD : ∀ c, IsCell V c → ¬ IsCorner s c)
    (hG : NotchF V s p e0 G) (hH : NotchF V s p e0 H) (hHam : ncomp V H = 1)
    (hT : NoTypeIIIR V G s p) (h2 : 2 ≤ ncomp V G) :
    (∃ σ, WalkStrip V G H s p σ) ∨
    (ncomp V G = 2 ∧ ∃ c, IsCell (insert p V) c ∧ IsCorner p c ∧ ¬ NotTypeIII V G c) := by
  have hfar : ∀ c, IsCell (insert p V) c → ¬ IsCorner s c → ¬ IsCorner p c →
      NotTypeIII (insert p V) G c := fun c hc h1 h2 => hT c (cell_of_insP hc h2) h1 h2
  rcases lemmaB_t2 (hG.solidFor hs hH) hG.fac hH.fac (by rw [hH.ncomp htV he0]; exact hHam)
      (fun z h1 h2 => dST_off h1 h2) (dST_s s p) (Finset.mem_insert_of_mem hsV)
      (hG.zero hs hpV hsD hH) (dST_t s p) (Finset.mem_insert_self _ _) hfar
      (by rw [hG.ncomp htV he0]; exact h2) with
    ⟨σ, hv, hn2, hmu, hcor, hle1, hle2, hodd, _⟩ | ⟨h2c, c, hc, hc3⟩
  · left
    have hcV : ∀ j < σ.n, IsCell V (cellJ σ.c σ.s j) :=
      fun j hj => cell_of_insP (hv.2.2.1 j hj) (hcor j hj).2
    have hA := hG.strip hpV hv.2.1 hcV
    rw [hG.ncomp htV he0, hA.ncomp htV he0] at hle1 hle2 hodd
    rw [hG.mu hs hH, hA.mu hs hH] at hmu
    exact ⟨σ, ⟨hv.1, hv.2.1, hcV, hv.2.2.2⟩, hn2, hmu, hcor, hle1, hle2, hodd⟩
  · right
    rw [hG.ncomp htV he0] at h2c
    have hcp : IsCorner p c := by
      by_contra hn
      have hcV := cell_of_insP hc hn
      exact hc3 (hT c hcV (hsD c hcV) hn)
    exact ⟨h2c, c, hc, hcp, hc3⟩

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

-- One of the two cells beside a cell is restricted whenever it is a cell of `insert p V`: the
-- square at `p` can be on one side only.
--
lemma notch_hLR (hsV : s ∈ V) (hsD : ∀ c, IsCell V c → ¬ IsCorner s c) (e : Pt) (sd : Side) :
    (IsCell (insert s (insert p V)) (nb e (latA sd)) →
      ¬ IsCorner s (nb e (latA sd)) ∧ ¬ IsCorner p (nb e (latA sd))) ∨
    (IsCell (insert s (insert p V)) (nb e (latB sd)) →
      ¬ IsCorner s (nb e (latB sd)) ∧ ¬ IsCorner p (nb e (latB sd))) := by
  rw [Finset.insert_eq_of_mem (Finset.mem_insert_of_mem hsV)]
  have key : ∀ x, ¬ IsCorner p x → (IsCell (insert p V) x → ¬ IsCorner s x ∧ ¬ IsCorner p x) :=
    fun x hx hc => ⟨hsD x (cell_of_insP hc hx), hx⟩
  by_cases hA : IsCorner p (nb e (latA sd))
  · exact Or.inr (key _ (fun hB => corner_latAB hA hB))
  · exact Or.inl (key _ hA)

-- **`t3_link` at a notch**: an even count-neutral restricted strip after which a restricted Type
-- III cell exists links to a one-cell strip (from `t3_link_pf`).
--
theorem t3_link_notch {G : Finset Edge} (hsV : s ∈ V) (hsD : ∀ c, IsCell V c → ¬ IsCorner s c)
    (hD : Deg2Off V G s p) (hdsG : deg G s = 1) (hleG : ∀ z, deg G z ≤ 2)
    (hT : NoTypeIIIR V G s p) {σ : StripSpec} (hv : ValidStrip V G σ) (hn2 : 2 ≤ σ.n)
    (hR : Restr s p σ) (hev : σ.n % 2 = 0) (hneut : ncomp V (applyS G σ) = ncomp V G)
    (hE2 : E2Of V G σ) {c1 : Pt} {tf : Side} (hc1 : IsCell V c1)
    (hc1R : ¬ IsCorner s c1 ∧ ¬ IsCorner p c1) (hb : back c1 tf ∈ applyS G σ)
    (hf : front c1 tf ∈ applyS G σ) (hl1 : lat1 c1 tf ∉ applyS G σ)
    (hl2 : lat2 c1 tf ∉ applyS G σ) (hn : ¬ Conn (applyS G σ) (back1 c1 tf) (front1 c1 tf)) :
    ∃ τ, RPathTg V G s p σ [τ] := by
  have hv0 := hv
  obtain ⟨c0, sd, n⟩ := σ
  obtain ⟨_, hpat, hcellS, hsep⟩ := hv
  change n % 2 = 0 at hev
  change 2 ≤ n at hn2
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  have hk : k % 2 = 0 := by omega
  have hcell : ∀ j ≤ k + 1, IsCell V (cellJ c0 sd j) := fun j hj => hcellS j (by simp only; omega)
  have hcor : ∀ j ≤ k + 1, ¬ IsCorner s (cellJ c0 sd j) ∧ ¬ IsCorner p (cellJ c0 sd j) :=
    fun j hj => hR j (by simp only; omega)
  obtain ⟨τ, hτ1, hl, hok, hτR⟩ := t3_link_pf hD hsV hdsG hleG hT hk hcell hcor hpat hsep hneut
    hE2 hc1 hc1R hb hf hl1 hl2 hn (fun _ => notch_hLR hsV hsD _ _)
  refine ⟨τ, hv0, ⟨by show (k + 2) % 2 = 0; omega, hl, Or.inl (by rw [hτ1])⟩, ⟨hok, trivial⟩, ?_⟩
  intro x hx
  rcases List.mem_cons.1 hx with rfl | hx
  · exact hR
  · rw [List.mem_singleton.1 hx]; exact hτR

-- **The walk always starts at a notch** when `s` is a corner of no square of `insert p V`:
-- `good_start2`'s Type III case needs a Type III square with `s` as a corner (`lemmaB_t2s`).
--
theorem notch_lemmaB' {G H : Finset Edge} (hs : Solid V) (hsV : s ∈ V) (htV : t ∈ V)
    (hpV : p ∉ V) (he0 : Ends e0 t p) (hsD : ∀ c, IsCell V c → ¬ IsCorner s c)
    (hsW : ∀ c, IsCell (insert p V) c → ¬ IsCorner s c)
    (hG : NotchF V s p e0 G) (hH : NotchF V s p e0 H) (hHam : ncomp V H = 1)
    (hT : NoTypeIIIR V G s p) (h2 : 2 ≤ ncomp V G) :
    ∃ σ, WalkStrip V G H s p σ := by
  have hfar : ∀ c, IsCell (insert p V) c → ¬ IsCorner s c → ¬ IsCorner p c →
      NotTypeIII (insert p V) G c := fun c hc h1 h2 => hT c (cell_of_insP hc h2) h1 h2
  rcases lemmaB_t2s (hG.solidFor hs hH) hG.fac hH.fac (by rw [hH.ncomp htV he0]; exact hHam)
      (fun z h1 h2 => dST_off h1 h2) (dST_s s p) (Finset.mem_insert_of_mem hsV)
      (hG.zero hs hpV hsD hH) (dST_t s p) (Finset.mem_insert_self _ _) hfar
      (by rw [hG.ncomp htV he0]; exact h2) with
    ⟨σ, hv, hn2, hmu, hcor, hle1, hle2, hodd, _⟩ | ⟨c, hc, _, hcs⟩
  · have hcV : ∀ j < σ.n, IsCell V (cellJ σ.c σ.s j) :=
      fun j hj => cell_of_insP (hv.2.2.1 j hj) (hcor j hj).2
    have hA := hG.strip hpV hv.2.1 hcV
    rw [hG.ncomp htV he0, hA.ncomp htV he0] at hle1 hle2 hodd
    rw [hG.mu hs hH, hA.mu hs hH] at hmu
    exact ⟨σ, ⟨hv.1, hv.2.1, hcV, hv.2.2.2⟩, hn2, hmu, hcor, hle1, hle2, hodd⟩
  · exact absurd hcs (hsW c hc)

-- **The near lemma at a notch** (`p ∉ V`): the four sites of the near lemma's proof where the
-- square with corner `p` beside a strip matters, each under the hypothesis that the state before
-- the strip has no restricted Tg chain (`NearGaps`), and one round (`Gap_round`), as named gaps.
--
-- (Both open; not proved. `hpNotch_correct` takes them as hypotheses.)

-- **Restricted Tg chains exist at a notch** in every state through `e0` without a restricted
-- Type III cell and with two components or more, from the walk start (`notch_lemmaB'`) and the near lemma.
-- With `s` a corner of no cell and `p` outside `V`, no cell of `V` has an endpoint as a corner,
-- so the dangling arguments (`gapsCE_dang`) replace H1, H2a and N.
--
theorem rpath_exists_notch [NearOK V p] {H : Finset Edge} (hs : Solid V) (hsV : s ∈ V) (htV : t ∈ V)
    (hpV : p ∉ V) (he0 : Ends e0 t p) (hsD : ∀ c, IsCell V c → ¬ IsCorner s c)
    (hsW : ∀ c, IsCell (insert p V) c → ¬ IsCorner s c)
    (hH : NotchF V s p e0 H) (hHam : ncomp V H = 1) :
    ∀ (m : ℕ) (G : Finset Edge), mu V G H = m → NotchF V s p e0 G → CleanR V G s p →
      2 ≤ ncomp V G → (∃ σ L, RPathTg V G s p σ L) ∨ T3Walk V G H s p := by
  have hDg : Dang V s p := fun c hc => ⟨hsD c hc, fun h => hpV (corner_mem hc h)⟩
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro G hm hG hcl h2
  have hD := hG.deg2Off
  have hdsG := hG.degS hsV
  have hleG := hG.le2
  obtain ⟨σ, hw0⟩ := notch_lemmaB' hs hsV htV hpV he0 hsD hsW hG hH hHam hcl.1 h2
  have hwσ := hw0
  obtain ⟨hv, hn2, hmu, hR, hc1, hc2, _⟩ := hw0
  have hRall : ∀ x ∈ [σ], Restr s p x := by
    intro x hx; rw [List.mem_singleton.1 hx]; exact hR
  rcases Nat.mod_two_eq_zero_or_one σ.n with hev | hodd
  swap
  · exact Or.inl ⟨σ, [], hv, Or.inl hodd, trivial, hRall⟩
  by_cases hdrop : ncomp V (applyS G σ) + 1 = ncomp V G
  · exact Or.inl ⟨σ, [], hv, Or.inr ⟨hev, drop_twists hD hsV hdsG hcl.1 hv hR hev hdrop⟩, trivial,
      hRall⟩
  have hneut : ncomp V (applyS G σ) = ncomp V G := by omega
  by_cases hR' : NoTypeIIIR V (applyS G σ) s p
  swap
  · exact Or.inr ⟨σ, hwσ, hev, hneut, hR'⟩
  have hcl' : CleanR V (applyS G σ) s p :=
    ⟨hR', fun ⟨_, c, hc, hn⟩ => hn (noT3_of_dang hDg hR' c hc)⟩
  have hnoG := noT3_of_dang hDg hcl.1
  have hnoA := noT3_of_dang hDg hR'
  have hE : EFree V G σ :=
    ⟨fun tf _ hc => hnoG _ hc, fun tf _ hc => hnoA _ hc, fun tf _ hc => hnoA _ hc⟩
  obtain ⟨c0, sd, n⟩ := σ
  obtain ⟨h1, hpat, hcellS, hsep⟩ := hv
  change n % 2 = 0 at hev
  change 2 ≤ n at hn2
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  have hk : k % 2 = 0 := by omega
  have hcell : ∀ j ≤ k + 1, IsCell V (cellJ c0 sd j) := fun j hj => hcellS j (by simp only; omega)
  have hcor : ∀ j ≤ k + 1, ¬ IsCorner s (cellJ c0 sd j) ∧ ¬ IsCorner p (cellJ c0 sd j) :=
    fun j hj => hR j (by simp only; omega)
  have hA : NotchF V s p e0 (flipCol G c0 sd (k + 2)) :=
    hG.strip (σ := ⟨c0, sd, k + 2⟩) hpV hpat hcellS
  have hmu' : mu V (flipCol G c0 sd (k + 2)) H < m := by
    have h' : mu V (flipCol G c0 sd (k + 2)) H + 2 * (k + 2) = mu V G H := hmu
    rw [← hm]; omega
  have hex := ih _ hmu' _ rfl hA hcl'
    (by have h3 : ncomp V (flipCol G c0 sd (k + 2)) = ncomp V G := hneut; omega)
  by_cases hP0 : ∃ q L, RPathTg V (flipCol G c0 sd (k + 2)) s p q L
  swap
  · -- No chain after `σ`: its Type-III walk strip gives one through `t3_link` (no cell has an
    -- endpoint as a corner).
    exfalso
    apply hP0
    obtain ⟨τ, ⟨hvτ, hn2τ, _, hRτ0, _, _, _⟩, hevτ, hneutτ, hRτ⟩ := hex.resolve_left hP0
    unfold NoTypeIIIR at hRτ
    push Not at hRτ
    obtain ⟨c, hc, hcs, hct, hn⟩ := hRτ
    unfold NotTypeIII at hn
    push Not at hn
    obtain ⟨tf, hb, hf, hl1, hl2, hnc⟩ := hn
    obtain ⟨τ', h⟩ := t3_link_notch hsV hsD hA.deg2Off (hA.degS hsV) hA.le2 hcl'.1 hvτ hn2τ hRτ0
      hevτ hneutτ (fun tf _ hc => hnoA _ hc) hc ⟨hcs, hct⟩ hb hf hl1 hl2 hnc
    exact ⟨τ, [τ'], h⟩
  have hP : ∃ w, ∃ q L, RPathTg V (flipCol G c0 sd (k + 2)) s p q L ∧ wt q L = w := by
    obtain ⟨q, L, h⟩ := hP0; exact ⟨_, q, L, h, rfl⟩
  obtain ⟨q, L, hQ, hw⟩ := Nat.find_spec hP
  refine Or.inl ?_
  exact comp_clean_tg hD hsV hdsG hleG hcl.1 hk hcell hcor hpat hsep hneut hcl'.1 hE.1 hE.2.1 hE.2.2
    hQ (fun σ' L' h' => by rw [hw]; exact Nat.find_min' hP ⟨σ', L', h', rfl⟩)

/-! ## The algorithm's decisions on factors through `e0` -/

lemma card_insP : (insert p V).card ≤ V.card + 1 := Finset.card_insert_le p V

lemma t3B_iffN {G : Finset Edge} (hGW : Inside (insert p V) G) {c : Pt} (hc : IsCell V c)
    {tf : Side} : t3B V G c tf = true ↔ back c tf ∈ G ∧ front c tf ∈ G ∧ lat1 c tf ∉ G ∧
      lat2 c tf ∉ G ∧ ¬ Conn G (back1 c tf) (front1 c tf) := by
  obtain ⟨hb, _, hf, _⟩ := corners4 hc tf
  unfold t3B
  simp only [Bool.and_eq_true, decide_eq_true_eq,
    bool_not_iff (connB_iffW hGW card_insP (Finset.subset_insert _ _) hb hf)]
  tauto

lemma findT3R_someN {G : Finset Edge} (hGW : Inside (insert p V) G) {c : Pt} {tf : Side}
    (h : findT3R V G s p = some (c, tf)) : IsCell V c ∧ back c tf ∈ G ∧ front c tf ∈ G ∧
      lat1 c tf ∉ G ∧ lat2 c tf ∉ G ∧ ¬ Conn G (back1 c tf) (front1 c tf) := by
  unfold findT3R at h
  have hm := List.mem_of_find?_eq_some h
  have hp := List.find?_some h
  simp only [List.mem_flatMap, List.mem_map] at hm
  obtain ⟨c', hc', t', _, he⟩ := hm
  cases he
  have hc := (mem_cellList.1 hc').2
  simp only [Bool.and_eq_true] at hp
  exact ⟨hc, (t3B_iffN hGW hc).1 hp.2⟩

lemma findT3_someN {G : Finset Edge} (hGW : Inside (insert p V) G) {c : Pt} {tf : Side}
    (h : findT3 V G = some (c, tf)) : IsCell V c ∧ back c tf ∈ G ∧ front c tf ∈ G ∧
      lat1 c tf ∉ G ∧ lat2 c tf ∉ G ∧ ¬ Conn G (back1 c tf) (front1 c tf) := by
  unfold findT3 at h
  have hm := List.mem_of_find?_eq_some h
  have hp := List.find?_some h
  simp only [List.mem_flatMap, List.mem_map] at hm
  obtain ⟨c', hc', t', _, he⟩ := hm
  cases he
  have hc := (mem_cellList.1 hc').2
  exact ⟨hc, (t3B_iffN hGW hc).1 hp⟩

lemma findT3_noneN {G : Finset Edge} (hGW : Inside (insert p V) G) (h : findT3 V G = none) :
    NoTypeIII V G := by
  intro c hc tf hb hf hl1 hl2
  by_contra hn
  unfold findT3 at h
  have := List.find?_eq_none.1 h (c, tf) (by
    simp only [List.mem_flatMap, List.mem_map]
    exact ⟨c, mem_cellList.2 ⟨hc.1, hc⟩, tf, mem_sidesL tf, rfl⟩)
  exact this ((t3B_iffN hGW hc).2 ⟨hb, hf, hl1, hl2, hn⟩)

lemma findT3R_noneN {G : Finset Edge} (hGW : Inside (insert p V) G) (h : findT3R V G s p = none) :
    NoTypeIIIR V G s p := by
  intro c hc hcs hct tf hb hf hl1 hl2
  by_contra hn
  unfold findT3R at h
  have := List.find?_eq_none.1 h (c, tf) (by
    simp only [List.mem_flatMap, List.mem_map]
    exact ⟨c, mem_cellList.2 ⟨hc.1, hc⟩, tf, mem_sidesL tf, rfl⟩)
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at this
  exact this ⟨⟨Bool.eq_false_iff.2 (fun h' => hcs (cornerB_eq_true_iff.1 h')),
    Bool.eq_false_iff.2 (fun h' => hct (cornerB_eq_true_iff.1 h'))⟩,
    (t3B_iffN hGW hc).2 ⟨hb, hf, hl1, hl2, hn⟩⟩

lemma M_eq_McN {G : Finset Edge} (hGW : Inside (insert p V) G) : M V G s p = Mc V G s p := by
  unfold M Mc
  rw [cncomp_eqW hGW card_insP (Finset.subset_insert _ _)]
  congr 1
  by_cases h1 : (findT3R V G s p).isSome = true <;> by_cases h2 : ncomp V G = 2 <;>
    by_cases h3 : (findT3 V G).isSome = true <;> simp [h1, h2, h3]

lemma cleanR_iffN {X : Finset Edge} (hXW : Inside (insert p V) X) :
    CleanR V X s p ↔ ¬ ((findT3R V X s p).isSome = true ∨
      (ncomp V X = 2 ∧ (findT3 V X).isSome = true)) := by
  constructor
  · rintro ⟨hR, h2⟩ (h | ⟨h2', h⟩)
    · rcases hf : findT3R V X s p with _ | ⟨c, tf⟩
      · rw [hf] at h; simp at h
      · obtain ⟨hc, hb, hff, hl1, hl2, hn⟩ := findT3R_someN hXW hf
        obtain ⟨hcs, hct⟩ := findT3R_avoid hf
        exact hn (hR c hc hcs hct tf hb hff hl1 hl2)
    · rcases hf : findT3 V X with _ | ⟨c, tf⟩
      · rw [hf] at h; simp at h
      · obtain ⟨hc, hb, hff, hl1, hl2, hn⟩ := findT3_someN hXW hf
        exact h2 ⟨h2', c, hc, fun hT => hn (hT tf hb hff hl1 hl2)⟩
  · intro h
    refine ⟨fun c hc hcs hct => ?_, fun ⟨h2', c, hc, hn⟩ => ?_⟩
    · by_contra hn
      apply h; left
      rcases hf : findT3R V X s p with _ | q
      · exact absurd (fun tf => findT3R_noneN hXW hf c hc hcs hct tf) hn
      · rfl
    · apply h; right
      refine ⟨h2', ?_⟩
      rcases hf : findT3 V X with _ | q
      · exact absurd (fun tf => findT3_noneN hXW hf c hc tf) hn
      · rfl

lemma M_cleanN {X : Finset Edge} (hXW : Inside (insert p V) X) (h : CleanR V X s p) :
    M V X s p = 2 * ncomp V X + 1 := by
  unfold M; rw [ite_eq_right ((cleanR_iffN hXW).1 h)]

lemma M_not_cleanN {X : Finset Edge} (hXW : Inside (insert p V) X) (h : ¬ CleanR V X s p) :
    M V X s p = 2 * ncomp V X := by
  unfold M; rw [ite_eq_left (by by_contra h'; exact h ((cleanR_iffN hXW).2 h'))]; rfl

/-! ## Completeness of `runPF V s p` at a notch -/

-- A path in the restricted link graph exists (from `rpath_exists_notch`).
--
theorem chain_exists_notch [NearOK V p] {G H : Finset Edge} (hs : Solid V) (hsV : s ∈ V) (htV : t ∈ V)
    (hpV : p ∉ V) (he0 : Ends e0 t p) (hsD : ∀ c, IsCell V c → ¬ IsCorner s c)
    (hsW : ∀ c, IsCell (insert p V) c → ¬ IsCorner s c)
    (hG : NotchF V s p e0 G) (hH : NotchF V s p e0 H) (hHam : ncomp V H = 1)
    (hr : findT3R V G s p = none) (h2c : ¬ (ncomp V G = 2 ∧ (findT3 V G).isSome))
    (h2 : 2 ≤ ncomp V G) :
    ∃ q : List PNode, MP.IsPath (psrc V G) pmid (ptgt V G s p) (pedge V G) q ∧
      ∀ x ∈ q, x ∈ pnodes V G s p := by
  have hGW := Inside.of_factor hG.fac
  have hcl : CleanR V G s p := by
    refine ⟨findT3R_noneN hGW hr, fun ⟨h2', c, hc, hn⟩ => h2c ⟨h2', ?_⟩⟩
    rcases hf : findT3 V G with _ | q
    · exact absurd (fun tf => findT3_noneN hGW hf c hc tf) hn
    · rfl
  rcases rpath_exists_notch hs hsV htV hpV he0 hsD hsW hH hHam _ G rfl hG hcl h2 with ⟨σ, L, h⟩ | hT
  · obtain ⟨q, hq, hN, _⟩ := rpath_to_ppath hG.deg2Off hsV (hG.degS hsV) h
    exact ⟨q, hq, hN⟩
  -- A Type-III walk strip lowers `M` by itself: a one-strip chain.
  --
  obtain ⟨τ, ⟨hv, _, _, hR, _, _, _⟩, _, hneut, hR'⟩ := hT
  have hin : Inside (insert p V) (applyS G τ) := Inside.of_factor (hG.strip hpV hv.2.1 hv.2.2.1).fac
  refine single_ppath hG.deg2Off hsV hv hR ?_
  rw [← M_eq_McN hin, ← M_eq_McN hGW, M_not_cleanN hin (fun h => hR' h.1), M_cleanN hGW hcl, hneut]
  omega

-- One round from a state through `e0` with at least two components makes a move, stays through
-- `e0`, and lowers `M`, or keeps it and lowers the weight of the minimum chain.
--
theorem step_progress_notch [NearOK V p] [RoundOK V p] {G H : Finset Edge} (hs : Solid V) (hsV : s ∈ V) (htV : t ∈ V)
    (hpV : p ∉ V) (he0 : Ends e0 t p) (hsD : ∀ c, IsCell V c → ¬ IsCorner s c)
    (hsW : ∀ c, IsCell (insert p V) c → ¬ IsCorner s c)
    (hG : NotchF V s p e0 G) (hH : NotchF V s p e0 H) (hHam : ncomp V H = 1)
    (h2 : 2 ≤ ncomp V G) :
    ∃ G', stepPF V G s p = some G' ∧ NotchF V s p e0 G' ∧
      (M V G' s p < M V G s p ∨ (M V G' s p = M V G s p ∧ wmin V G' s p < wmin V G s p)) := by
  have hDg : Dang V s p := fun c hc => ⟨hsD c hc, fun h => hpV (corner_mem hc h)⟩
  have hGV := Inside.of_factor hG.fac
  have hcn : cncomp V G = ncomp V G := cncomp_eqW hGV card_insP (Finset.subset_insert _ _)
  have hD := hG.deg2Off
  have hdsG := hG.degS hsV
  have hleG := hG.le2
  -- The chain branch, used when no Type III cell is to be flipped.
  have chain : findT3R V G s p = none → ¬ (ncomp V G = 2 ∧ (findT3 V G).isSome) →
      ∃ G', (match findChainPF V G s p with
              | some L => applyChainChecked V G (L.take 1)
              | none => none) = some G' ∧ NotchF V s p e0 G' ∧
        (M V G' s p < M V G s p ∨ (M V G' s p = M V G s p ∧ wmin V G' s p < wmin V G s p)) := by
    intro hr h2c
    have hcl : CleanR V G s p := by
      refine ⟨findT3R_noneN hGV hr, fun ⟨h2', c, hc, hn⟩ => h2c ⟨h2', ?_⟩⟩
      rcases hf : findT3 V G with _ | q
      · exact absurd (fun tf => findT3_noneN hGV hf c hc tf) hn
      · rfl
    have hMG := M_cleanN hGV hcl
    obtain ⟨q0, hq0, hN0⟩ := chain_exists_notch hs hsV htV hpV he0 hsD hsW hG hH hHam hr h2c h2
    rcases hm : MP.minPath (pnodes V G s p) (psrc V G) pmid (ptgt V G s p) (pedge V G) pw with _ | q
    · exact absurd (MP.minPath_none _ _ _ _ _ _ hm q0 hq0 hN0) id
    obtain ⟨hq, hqN⟩ := MP.minPath_some _ _ _ _ _ _ hm
    have hfc : findChainPF V G s p = some (q.map PNode.σ) := by unfold findChainPF; rw [hm]; rfl
    have hwG : wmin V G s p = MP.pw pw q := by unfold wmin; rw [hm]
    rw [hfc]
    rcases q with _ | ⟨x, rest⟩
    · exact absurd hq id
    obtain ⟨hsrc, htail⟩ := MP.isPath_cons.1 hq
    have hsrc' := hsrc
    simp only [psrc, Bool.and_eq_true, beq_iff_eq] at hsrc'
    obtain ⟨⟨hpos, _⟩, hval⟩ := hsrc'
    have hv := (validB_iffW hGV card_insP (Finset.subset_insert _ _)).1 hval
    have hσ : x.σ ∈ allStrips V G := mem_allStrips.2 ⟨hv.1, hv.2.1, hv.2.2.1⟩
    have hF' : NotchF V s p e0 (applyS G x.σ) := hG.strip hpV hv.2.1 hv.2.2.1
    have hF'V := Inside.of_factor hF'.fac
    refine ⟨applyS G x.σ, by simp [applyChainChecked, hσ], hF', ?_⟩
    rcases rest with _ | ⟨y, rest'⟩
    · -- One strip: the end test at position 1 is "the measure drops".
      left
      have htg := MP.isTail_nil.1 htail
      simp only [ptgt, hpos, beq_self_eq_true, ite_true, decide_eq_true_eq] at htg
      rw [M_eq_McN hF'V, M_eq_McN hGV]; exact htg
    · obtain ⟨hRP, hpw⟩ := ppath_to_rpath hGV card_insP (Finset.subset_insert _ _) hq hqN
      have hmin : ∀ σ L', RPathTg V G s p σ L' →
          wt x.σ (y.σ :: rest'.map PNode.σ) ≤ wt σ L' := fun σ L' h => by
        obtain ⟨q', hq', hq'N, hq'w⟩ := rpath_to_ppath hD hsV hdsG h
        have := MP.minPath_min _ _ _ _ _ _ hm q' hq' hq'N
        omega
      have hneut := first_neutral hD hsV hdsG hcl.1 hRP
      by_cases hcl' : CleanR V (applyS G x.σ) s p
      · right
        have hnoG := noT3_of_dang hDg hcl.1
        have hnoA := noT3_of_dang hDg hcl'.1
        refine ⟨by rw [M_cleanN hF'V hcl', hMG, hneut], ?_⟩
        have hR0 : Restr s p x.σ := hRP.2.2.2 x.σ (List.mem_cons_self ..)
        generalize hxs : x.σ = a at hRP hmin hneut hcl' hnoA hR0 hv hpw hF'V hF' ⊢
        obtain ⟨c0, sd, n⟩ := a
        obtain ⟨h1, hpat, hcellS, hsep⟩ := hv
        have hev : n % 2 = 0 := hRP.2.1.1
        change 1 ≤ n at h1
        obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
        have hk : k % 2 = 0 := by omega
        have hcell : ∀ j ≤ k + 1, IsCell V (cellJ c0 sd j) :=
          fun j hj => hcellS j (by simp only; omega)
        have hcor : ∀ j ≤ k + 1, ¬ IsCorner s (cellJ c0 sd j) ∧ ¬ IsCorner p (cellJ c0 sd j) :=
          fun j hj => hR0 j (by simp only; omega)
        obtain ⟨hR', hwt⟩ := round_tg hD hsV hdsG hleG hcl.1 hk hcell hcor hpat hsep hcl'.1 hneut
          (fun tf _ hc => hnoG _ hc) (fun tf _ hc => hnoA _ hc) (fun tf _ hc => hnoG _ hc) hRP hmin
        obtain ⟨q', hq', hq'N, hq'w⟩ := rpath_to_ppath hF'.deg2Off hsV (hF'.degS hsV) hR'
        have hle' := wmin_le hq' hq'N
        change wmin V (flipCol G c0 sd (k + 2)) s p < wmin V G s p
        rw [hwG, hpw]
        change wmin V (flipCol G c0 sd (k + 2)) s p ≤ MP.pw pw q' at hle'
        omega
      · left
        rw [M_not_cleanN hF'V hcl', hMG, hneut]; omega
  have hsW : s ∈ insert p V := Finset.mem_insert_of_mem hsV
  unfold stepPF
  rcases hr : findT3R V G s p with _ | ⟨c, tf⟩
  · simp only
    by_cases hc2 : cncomp V G = 2
    · rw [ite_eq_left (by simpa using hc2)]
      rcases ht : findT3 V G with _ | ⟨c, tf⟩
      · simp only
        exact chain hr (by rw [ht]; simp)
      · simp only [Option.some.injEq, exists_eq_left']
        obtain ⟨hc, hb, hf, hl1, hl2, hn⟩ := findT3_someN hGV ht
        obtain ⟨hF', hcnt, _⟩ := typeIII_flip (H := H) hG.fac (fun z h1 h2 => dST_off h1 h2)
          (dST_s s p) hsW (isCell_mono hc (Finset.subset_insert _ _))
          (fun hT => hn (hT tf hb hf hl1 hl2))
        have hN' := hG.flip hpV hc hF'
        rw [hG.ncomp htV he0, hN'.ncomp htV he0] at hcnt
        have h2' : ncomp V G = 2 := by rw [← hcn]; exact hc2
        refine ⟨hN', Or.inl ?_⟩
        unfold M
        have : (findT3R V G s p).isSome = true ∨ (ncomp V G = 2 ∧ (findT3 V G).isSome = true) :=
          Or.inr ⟨h2', by rw [ht]; rfl⟩
        rw [ite_eq_left this]
        split_ifs <;> omega
    · rw [ite_eq_right (by simpa using hc2)]
      exact chain hr (fun h => hc2 (by rw [hcn]; exact h.1))
  · simp only [Option.some.injEq, exists_eq_left']
    obtain ⟨hc, hb, hf, hl1, hl2, hn⟩ := findT3R_someN hGV hr
    obtain ⟨hF', hcnt, _⟩ := typeIII_flip (H := H) hG.fac (fun z h1 h2 => dST_off h1 h2)
      (dST_s s p) hsW (isCell_mono hc (Finset.subset_insert _ _))
      (fun hT => hn (hT tf hb hf hl1 hl2))
    have hN' := hG.flip hpV hc hF'
    rw [hG.ncomp htV he0, hN'.ncomp htV he0] at hcnt
    refine ⟨hN', Or.inl ?_⟩
    unfold M
    have : (findT3R V G s p).isSome = true ∨ (ncomp V G = 2 ∧ (findT3 V G).isSome = true) :=
      Or.inl (by rw [hr]; rfl)
    rw [ite_eq_left this]
    split_ifs <;> omega

-- **Completeness from a state through `e0`**, with an explicit number of rounds.
--
theorem runPF_complete_notch [NearOK V p] [RoundOK V p] {H : Finset Edge} (hs : Solid V) (hsV : s ∈ V) (htV : t ∈ V)
    (hpV : p ∉ V) (he0 : Ends e0 t p) (hsD : ∀ c, IsCell V c → ¬ IsCorner s c)
    (hsW : ∀ c, IsCell (insert p V) c → ¬ IsCorner s c)
    (hH : NotchF V s p e0 H) (hHam : ncomp V H = 1) :
    ∀ k (G : Finset Edge), NotchF V s p e0 G →
      M V G s p * (Wb V + 1) + wmin V G s p ≤ k → runPF V s p (k + 1) G = true := by
  intro k
  induction k with
  | zero =>
    intro G _ hM
    have := ncomp_pos (F := G) hsV
    have hM1 : 1 ≤ M V G s p := by unfold M; split_ifs <;> omega
    have : Wb V + 1 ≤ M V G s p * (Wb V + 1) := Nat.le_mul_of_pos_left _ hM1
    omega
  | succ k ih =>
    intro G hG hM
    simp only [runPF]
    by_cases h1 : cncomp V G = 1
    · simp [h1]
    · have h1' : ncomp V G ≠ 1 := by
        rw [← cncomp_eqW (Inside.of_factor hG.fac) card_insP (Finset.subset_insert _ _)]; exact h1
      have hn : 2 ≤ ncomp V G := by have := ncomp_pos (F := G) hsV; omega
      obtain ⟨G', hst, hG', hlt⟩ := step_progress_notch hs hsV htV hpV he0 hsD hsW hG hH hHam hn
      rw [ite_eq_right_iff.2 (fun h => absurd (by simpa using h) h1), hst]
      refine ih G' hG' ?_
      have hw' := wmin_le_Wb (V := V) (s := s) (t := p) G'
      rcases hlt with hlt | ⟨heq, hlt⟩
      · have : M V G' s p * (Wb V + 1) + (Wb V + 1) ≤ M V G s p * (Wb V + 1) := by
          rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hlt
        omega
      · rw [heq]; omega

theorem runPF_complete_fuel_notch [NearOK V p] [RoundOK V p] {H : Finset Edge} (hs : Solid V) (hsV : s ∈ V) (htV : t ∈ V)
    (hpV : p ∉ V) (he0 : Ends e0 t p) (hsD : ∀ c, IsCell V c → ¬ IsCorner s c)
    (hsW : ∀ c, IsCell (insert p V) c → ¬ IsCorner s c)
    (hH : NotchF V s p e0 H) (hHam : ncomp V H = 1) (G : Finset Edge) (hG : NotchF V s p e0 G) :
    runPF V s p (fuelPF V) G = true := by
  have hle : M V G s p * (Wb V + 1) + wmin V G s p + 1 ≤ fuelPF V := by
    have h1 := M_le (V := V) (s := s) (t := p) G
    have h2 := wmin_le_Wb (V := V) (s := s) (t := p) G
    unfold fuelPF
    have : M V G s p * (Wb V + 1) ≤ (2 * V.card + 1) * (Wb V + 1) := Nat.mul_le_mul_right _ h1
    nlinarith
  obtain ⟨j, hj⟩ : ∃ j, fuelPF V = (M V G s p * (Wb V + 1) + wmin V G s p + j) + 1 :=
    ⟨fuelPF V - (M V G s p * (Wb V + 1) + wmin V G s p + 1), by omega⟩
  rw [hj]
  exact runPF_complete_notch hs hsV htV hpV he0 hsD hsW hH hHam _ G hG (by omega)

/-! ## Soundness of `runPF V s p` at a notch -/

lemma applyChainChecked_notch (hpV : p ∉ V) : ∀ (L : List StripSpec) (G G' : Finset Edge),
    NotchF V s p e0 G → applyChainChecked V G L = some G' → NotchF V s p e0 G'
  | [], G, G', hG, h => by simp only [applyChainChecked, Option.some.injEq] at h; exact h ▸ hG
  | σ :: L, G, G', hG, h => by
    simp only [applyChainChecked] at h
    split_ifs at h with hσ
    obtain ⟨_, hpat, hcell⟩ := mem_allStrips.1 hσ
    exact applyChainChecked_notch hpV L _ G' (hG.strip hpV hpat hcell) h

theorem stepPF_notch {G G' : Finset Edge} (hsV : s ∈ V) (hpV : p ∉ V) (hG : NotchF V s p e0 G)
    (h : stepPF V G s p = some G') : NotchF V s p e0 G' := by
  have hGV := Inside.of_factor hG.fac
  have hsW : s ∈ insert p V := Finset.mem_insert_of_mem hsV
  have flipN : ∀ {c : Pt} {tf : Side}, (IsCell V c ∧ back c tf ∈ G ∧ front c tf ∈ G ∧
      lat1 c tf ∉ G ∧ lat2 c tf ∉ G ∧ ¬ Conn G (back1 c tf) (front1 c tf)) →
      NotchF V s p e0 (ULHC.flip G c) := fun {c} {_} hd =>
    hG.flip hpV hd.1 (flip_t3_factor hG.fac (fun z h1 h2 => dST_off h1 h2) (dST_s s p) hsW
      ⟨isCell_mono hd.1 (Finset.subset_insert _ _), hd.2⟩)
  unfold stepPF at h
  rcases hr : findT3R V G s p with _ | ⟨c, tf⟩
  · rw [hr] at h
    simp only at h
    split_ifs at h
    · rcases ht : findT3 V G with _ | ⟨c, tf⟩
      · rw [ht] at h
        simp only at h
        rcases hp : findChainPF V G s p with _ | L
        · rw [hp] at h; simp at h
        · rw [hp] at h; exact applyChainChecked_notch hpV (L.take 1) G G' hG h
      · rw [ht] at h
        simp only [Option.some.injEq] at h
        subst h
        exact flipN (findT3_someN hGV ht)
    · rcases hp : findChainPF V G s p with _ | L
      · rw [hp] at h; simp at h
      · rw [hp] at h; exact applyChainChecked_notch hpV (L.take 1) G G' hG h
  · rw [hr] at h
    simp only [Option.some.injEq] at h
    subst h
    exact flipN (findT3R_someN hGV hr)

theorem runPF_sound_notch (hsV : s ∈ V) (hpV : p ∉ V) :
    ∀ (k : ℕ) (G : Finset Edge), NotchF V s p e0 G → runPF V s p k G = true →
      ∃ G', NotchF V s p e0 G' ∧ ncomp V G' = 1 := by
  intro k
  induction k with
  | zero =>
    intro G hG h
    simp only [runPF, beq_iff_eq] at h
    exact ⟨G, hG, by
      rw [← cncomp_eqW (Inside.of_factor hG.fac) card_insP (Finset.subset_insert _ _)]; exact h⟩
  | succ k ih =>
    intro G hG h
    simp only [runPF] at h
    by_cases h1 : cncomp V G = 1
    · exact ⟨G, hG, by
        rw [← cncomp_eqW (Inside.of_factor hG.fac) card_insP (Finset.subset_insert _ _)]; exact h1⟩
    · rw [ite_eq_right (by simpa using h1)] at h
      rcases hs : stepPF V G s p with _ | G'
      · rw [hs] at h; simp at h
      · rw [hs] at h
        exact ih G' (stepPF_notch hsV hpV hG hs) h

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

-- **The algorithm at a notch.** A starting s–t path-factor `R` of `V`, plus the edge `e0` from `t`
-- to its missing neighbour `p`, then the restricted search with endpoints `s` and `p`.
--
def hpNotch (V : Finset Pt) (s t p : Pt) (e0 : Edge) : Bool :=
  match findFactor V (dST s t) with
  | none => false
  | some R => runPF V s p (fuelPF V) (insert e0 R)

-- **Correctness at a notch** (modulo the near lemma's open sites): with
-- `s` a corner of no cell and `p ∉ V` a neighbour of `t`, `hpNotch` answers `true` exactly when
-- `V` has a Hamiltonian s–t path. `p` may have other neighbours in `V`.
--
theorem hpNotch_correct (hs : Solid V) (hst : s ≠ t) (hsV : s ∈ V) (htV : t ∈ V) (hpV : p ∉ V)
    (he0 : Ends e0 t p) (hsD : ∀ c, IsCell V c → ¬ IsCorner s c)
    (hsW : ∀ c, IsCell (insert p V) c → ¬ IsCorner s c) (hng : NearGaps) (hgr : Gap_round) :
    hpNotch V s t p e0 = true ↔ ∃ H, IsFactor V (dST s t) H ∧ ncomp V H = 1 := by
  constructor
  · intro h
    unfold hpNotch at h
    rcases hR : findFactor V (dST s t) with _ | R
    · rw [hR] at h; simp at h
    rw [hR] at h
    obtain ⟨G, hG, h1⟩ := runPF_sound_notch hsV hpV _ _
      (notch_up hst htV hpV he0 (findFactor_some (dST_le s t) hR)) h
    exact ⟨_, notch_down hst htV hpV he0 hG h1⟩
  · rintro ⟨H, hH, hHam⟩
    unfold hpNotch
    rcases hR : findFactor V (dST s t) with _ | R
    · exact absurd ⟨H, hH⟩ (findFactor_none (dST_le s t) hR)
    have hHN := notch_up hst htV hpV he0 hH
    have hHam' : ncomp V (insert e0 H) = 1 := ncomp_one_of_conn htV (fun x hx y hy =>
      (conn_of_ncomp_one hHam hx hy).mono (Finset.subset_insert _ _))
    have : NearOK V p := ⟨Or.inr (Or.inr hng)⟩
    have : RoundOK V p := ⟨Or.inr (Or.inr hgr)⟩
    exact runPF_complete_fuel_notch hs hsV htV hpV he0 hsD hsW hHN hHam' _
      (notch_up hst htV hpV he0 (findFactor_some (dST_le s t) hR))

-- **The notch theorem when `p` is a corner of no square of `V ∪ {p}`** (`PDang`; this includes
-- the pendant case, and `V ∪ {p}` need not be solid). No open lemma is used: every remaining
-- case of the near lemma puts `p` at a corner of such a square.
--
theorem hpNotch_correct_pdang (hs : Solid V) (hst : s ≠ t) (hsV : s ∈ V) (htV : t ∈ V) (hpV : p ∉ V)
    (he0 : Ends e0 t p) (hsD : ∀ c, IsCell V c → ¬ IsCorner s c)
    (hsW : ∀ c, IsCell (insert p V) c → ¬ IsCorner s c) (hpD : PDang V p) :
    hpNotch V s t p e0 = true ↔ ∃ H, IsFactor V (dST s t) H ∧ ncomp V H = 1 := by
  constructor
  · intro h
    unfold hpNotch at h
    rcases hR : findFactor V (dST s t) with _ | R
    · rw [hR] at h; simp at h
    rw [hR] at h
    obtain ⟨G, hG, h1⟩ := runPF_sound_notch hsV hpV _ _
      (notch_up hst htV hpV he0 (findFactor_some (dST_le s t) hR)) h
    exact ⟨_, notch_down hst htV hpV he0 hG h1⟩
  · rintro ⟨H, hH, hHam⟩
    unfold hpNotch
    rcases hR : findFactor V (dST s t) with _ | R
    · exact absurd ⟨H, hH⟩ (findFactor_none (dST_le s t) hR)
    have hHN := notch_up hst htV hpV he0 hH
    have hHam' : ncomp V (insert e0 H) = 1 := ncomp_one_of_conn htV (fun x hx y hy =>
      (conn_of_ncomp_one hHam hx hy).mono (Finset.subset_insert _ _))
    have : NearOK V p := NearOK.of_pdang hpD
    have : RoundOK V p := RoundOK.of_pdang hpD
    exact runPF_complete_fuel_notch hs hsV htV hpV he0 hsD hsW hHN hHam' _
      (notch_up hst htV hpV he0 (findFactor_some (dST_le s t) hR))

end notch

end HP

end ULHC
