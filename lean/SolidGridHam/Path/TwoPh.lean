/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import SolidGridHam.Path.SheffEndpoints

/-!
# Two phantoms (docs/ENDPOINTS_GENERAL.md, route A1): the states

Both endpoints get a missing neighbour as phantom: `p` at `t` (edge `e0`) and `q` at `s` (edge
`e1`). States are factors on `W₂ = V ∪ {p, q}` with degree 1 at `p` and `q`, 2 elsewhere, and the
phantom edges the only edges at `p` and `q` (`NotchF2`). Only cells of `V` are flipped. The
out-vertices are `t` and `s`.

A two-phantom state is a one-phantom state of `V ∪ {p}` with phantom `q` at `s` that also keeps
`e0`, so the passages to and from Hamiltonian `s`–`t` paths are `notch_up`/`notch_down` twice.
-/

namespace SolidGridHam

namespace HP

open Finset Classical

-- `ncomp_insP` without the insideness hypothesis (which its proof does not use).
--
theorem ncomp_ins {V : Finset Pt} {p : Pt} {G : Finset Edge} {t : Pt} (htV : t ∈ V)
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

-- A two-phantom state.
--
structure NotchF2 (V : Finset Pt) (p q : Pt) (e0 e1 : Edge) (G : Finset Edge) : Prop where
  fac : IsFactor (insert q (insert p V)) (dST p q) G
  patp : PAt p e0 G
  patq : PAt q e1 G

section two

variable {V : Finset Pt} {s t p q : Pt} {e0 e1 : Edge}

lemma PAt.insert_off {G : Finset Edge} {e : Edge} (h : PAt p e0 G) (he : ¬ (e.p = p ∨ e.q = p)) :
    PAt p e0 (insert e G) := fun f hf => by
  rw [Finset.mem_insert]
  constructor
  · rintro (rfl | h')
    · exact absurd hf he
    · exact (h f hf).1 h'
  · intro h'; exact Or.inr ((h f hf).2 h')

lemma PAt.erase_off {G : Finset Edge} {e : Edge} (h : PAt p e0 G) (he : ¬ (e.p = p ∨ e.q = p)) :
    PAt p e0 (G.erase e) := fun f hf => by
  rw [Finset.mem_erase]
  constructor
  · rintro ⟨_, h'⟩; exact (h f hf).1 h'
  · intro h'
    refine ⟨fun hfe => he (hfe ▸ hf), (h f hf).2 h'⟩

-- The phantom edge at `s` has no end at `p`.
--
lemma e1_off_p (hsV : s ∈ V) (hpV : p ∉ V) (hpq : p ≠ q) (he1 : Ends e1 s q) :
    ¬ (e1.p = p ∨ e1.q = p) := by
  rintro (h | h) <;> rcases he1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact hpV (h ▸ h1 ▸ hsV)
  · exact hpq (h ▸ h1)
  · exact hpq (h ▸ h2)
  · exact hpV (h ▸ h2 ▸ hsV)

-- **Up.** A Hamiltonian `s`–`t` path plus both phantom edges is a two-phantom state.
--
lemma two_up (hst : s ≠ t) (hsV : s ∈ V) (htV : t ∈ V) (hpV : p ∉ V) (hqV : q ∉ V) (hpq : p ≠ q)
    (he0 : Ends e0 t p) (he1 : Ends e1 s q) {R : Finset Edge} (hR : IsFactor V (dST s t) R) :
    NotchF2 V p q e0 e1 (insert e1 (insert e0 R)) := by
  have h1 := notch_up hst htV hpV he0 hR
  have hqV' : q ∉ insert p V := by
    rw [Finset.mem_insert]; rintro (h | h)
    · exact hpq h.symm
    · exact hqV h
  have hps : p ≠ s := fun h => hpV (h ▸ hsV)
  have hfac : IsFactor (insert p V) (dST p s) (insert e0 R) := by rw [dST_comm]; exact h1.fac
  have h2 := notch_up hps (Finset.mem_insert_of_mem hsV) hqV' he1 hfac
  exact ⟨h2.fac, h1.pat.insert_off (e1_off_p hsV hpV hpq he1), h2.pat⟩

lemma NotchF2.one (hG : NotchF2 V p q e0 e1 G) : NotchF (insert p V) p q e1 G := ⟨hG.fac, hG.patq⟩

lemma NotchF2.ncomp (hsV : s ∈ V) (htV : t ∈ V) (he0 : Ends e0 t p) (he1 : Ends e1 s q)
    {G : Finset Edge} (hG : NotchF2 V p q e0 e1 G) :
    ncomp (insert q (insert p V)) G = ncomp V G := by
  rw [NotchF.ncomp (Finset.mem_insert_of_mem hsV) he1 hG.one]
  exact ncomp_ins htV (he0.conn (e0_mem he0 hG.patp)).symm

-- **Down.** A two-phantom state with one piece, minus both phantom edges, is a Hamiltonian
-- `s`–`t` path.
--
lemma two_down (hst : s ≠ t) (hsV : s ∈ V) (htV : t ∈ V) (hpV : p ∉ V) (hqV : q ∉ V)
    (hpq : p ≠ q) (he0 : Ends e0 t p) (he1 : Ends e1 s q) {G : Finset Edge}
    (hG : NotchF2 V p q e0 e1 G) (h1 : ncomp V G = 1) :
    ∃ H, IsFactor V (dST s t) H ∧ ncomp V H = 1 := by
  have hqV' : q ∉ insert p V := by
    rw [Finset.mem_insert]; rintro (h | h)
    · exact hpq h.symm
    · exact hqV h
  have hps : p ≠ s := fun h => hpV (h ▸ hsV)
  have h1' : ncomp (insert p V) G = 1 := by
    rw [ncomp_ins htV (he0.conn (e0_mem he0 hG.patp)).symm]; exact h1
  obtain ⟨hf, hc⟩ := notch_down hps (Finset.mem_insert_of_mem hsV) hqV' he1 hG.one h1'
  have hN : NotchF V s p e0 (G.erase e1) :=
    ⟨by rw [dST_comm]; exact hf, hG.patp.erase_off (e1_off_p hsV hpV hpq he1)⟩
  rw [hN.ncomp htV he0] at hc
  exact ⟨_, notch_down hst htV hpV he0 hN hc⟩

-- Degree 2 at the corners of cells of `V`.
--
lemma two_dc (hpV : p ∉ V) (hqV : q ∉ V) : ∀ c, IsCell V c → ∀ z, IsCorner z c → dST p q z = 2 := by
  intro c hc z hz
  have hzV : z ∈ V := by
    obtain ⟨x, y⟩ := c
    rcases hz with rfl | rfl | rfl | rfl
    · exact hc.1
    · exact hc.2.1
    · exact hc.2.2.1
    · exact hc.2.2.2
  exact dST_off (fun h => hpV (h ▸ hzV)) (fun h => hqV (h ▸ hzV))

-- The only edges leaving `V` end at `t` or `s`.
--
lemma two_out (htV : t ∈ V) (hsV : s ∈ V) (he0 : Ends e0 t p) (he1 : Ends e1 s q) {G : Finset Edge}
    (hG : NotchF2 V p q e0 e1 G) :
    ∀ e ∈ G, (e.p ∉ V → e.q = t ∨ e.q = s) ∧ (e.q ∉ V → e.p = t ∨ e.p = s) := by
  intro e he
  have hev := Inside.of_factor hG.fac e he
  have side : ∀ {x y : Pt}, x ∈ insert q (insert p V) → x ∉ V → (x = p ∨ x = q) := by
    intro x y hx hxV
    rcases Finset.mem_insert.1 hx with h | h
    · exact Or.inr h
    · rcases Finset.mem_insert.1 h with h | h
      · exact Or.inl h
      · exact absurd h hxV
  constructor
  · intro hx
    rcases side (y := e.q) hev.1 hx with h | h
    · have := (hG.patp e (Or.inl h)).1 he
      subst this
      rcases he0 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact absurd (h1 ▸ htV) hx
      · exact Or.inl h2
    · have := (hG.patq e (Or.inl h)).1 he
      subst this
      rcases he1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact absurd (h1 ▸ hsV) hx
      · exact Or.inr h2
  · intro hx
    rcases side (y := e.p) hev.2 hx with h | h
    · have := (hG.patp e (Or.inr h)).1 he
      subst this
      rcases he0 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl h1
      · exact absurd (h2 ▸ htV) hx
    · have := (hG.patq e (Or.inr h)).1 he
      subst this
      rcases he1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inr h1
      · exact absurd (h2 ▸ hsV) hx

-- `G ⊕ H` stays inside `V` (both keep the phantom edges).
--
lemma two_symm {G H : Finset Edge} (hG : NotchF2 V p q e0 e1 G) (hH : NotchF2 V p q e0 e1 H) :
    ∀ e ∈ symmDiff G H, e.p ∈ V ∧ e.q ∈ V := by
  intro e he
  have hW : e.p ∈ insert q (insert p V) ∧ e.q ∈ insert q (insert p V) := by
    rw [Finset.mem_symmDiff] at he
    rcases he with ⟨h, _⟩ | ⟨h, _⟩
    · exact Inside.of_factor hG.fac e h
    · exact Inside.of_factor hH.fac e h
  have offp : ¬ (e.p = p ∨ e.q = p) := by
    intro hp
    rw [Finset.mem_symmDiff] at he
    rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h2 ((hH.patp e hp).2 ((hG.patp e hp).1 h1))
    · exact h2 ((hG.patp e hp).2 ((hH.patp e hp).1 h1))
  have offq : ¬ (e.p = q ∨ e.q = q) := by
    intro hp
    rw [Finset.mem_symmDiff] at he
    rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h2 ((hH.patq e hp).2 ((hG.patq e hp).1 h1))
    · exact h2 ((hG.patq e hp).2 ((hH.patq e hp).1 h1))
  push Not at offp offq
  constructor
  · rcases Finset.mem_insert.1 hW.1 with h | h
    · exact absurd h offq.1
    · exact (Finset.mem_insert.1 h).resolve_left offp.1
  · rcases Finset.mem_insert.1 hW.2 with h | h
    · exact absurd h offq.2
    · exact (Finset.mem_insert.1 h).resolve_left offp.2

lemma two_reach (hpV : p ∉ V) (hqV : q ∉ V) {H0 H : Finset Edge} {BS : List Bridge}
    (hr : Reach V H0 H BS) (hN : NotchF2 V p q e0 e1 H0)
    (hfac : IsFactor (insert q (insert p V)) (dST p q) H) : NotchF2 V p q e0 e1 H :=
  ⟨hfac, reach_pat hpV hr hN.patp, reach_pat hqV hr hN.patq⟩

-- **The two-phantom condition.** The endpoints `t`, `s` (phantoms `p`, `q`) are Far, and their
-- phantoms are not opposed.
--
def FarN (t p s q : Pt) : Prop := Far t s ∧ ¬ Opp t p s q

lemma ends_out_eq {e : Edge} {a x m : Pt} (h1 : Ends e a m) (h2 : Ends e x m) (ham : a ≠ m) :
    a = x := by
  rcases h1 with ⟨h1, h1'⟩ | ⟨h1, h1'⟩ <;> rcases h2 with ⟨h2, h2'⟩ | ⟨h2, h2'⟩
  · exact h1.symm.trans h2
  · exact absurd (h1.symm.trans h2) ham
  · exact absurd (h1'.symm.trans h2') ham
  · exact h1'.symm.trans h2'

-- In a two-phantom state the only edges leaving `V` are `t–p` and `s–q`, so `NoOpp` reduces to
-- the phantoms of `t` and `s`.
--
lemma two_noOpp (hsV : s ∈ V) (htV : t ∈ V) (hpV : p ∉ V) (hqV : q ∉ V) (he0 : Ends e0 t p)
    (he1 : Ends e1 s q) {G : Finset Edge} (hG : NotchF2 V p q e0 e1 G) (hno : ¬ Opp t p s q) :
    NoOpp V G t s := by
  have key : ∀ g ∈ G, ∀ c m, (c = t ∨ c = s) → Ends g c m → m ∉ V →
      (c = t ∧ m = p) ∨ (c = s ∧ m = q) := by
    intro g hg c m hc hgc hm
    have hcV : c ∈ V := by rcases hc with rfl | rfl <;> assumption
    have hin := (Inside.of_factor hG.fac) g hg
    have hmW : m ∈ insert q (insert p V) := by
      rcases hgc with ⟨_, h⟩ | ⟨h, _⟩
      · rw [← h]; exact hin.2
      · rw [← h]; exact hin.1
    simp only [Finset.mem_insert] at hmW
    have hcm : c ≠ m := fun h => hm (h ▸ hcV)
    rcases hmW with rfl | rfl | h
    · have hge : g = e1 := (hG.patq g (by rcases hgc with ⟨_, h⟩ | ⟨h, _⟩; exacts [Or.inr h, Or.inl h])).1 hg
      subst hge
      exact Or.inr ⟨ends_out_eq hgc he1 hcm, rfl⟩
    · have hge : g = e0 := (hG.patp g (by rcases hgc with ⟨_, h⟩ | ⟨h, _⟩; exacts [Or.inr h, Or.inl h])).1 hg
      subst hge
      exact Or.inl ⟨ends_out_eq hgc he0 hcm, rfl⟩
    · exact absurd h hm
  intro e he f hf a ma b mb ha hb hab hee hma hff hmb hop
  rcases key e he a ma ha hee hma with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rcases key f hf b mb hb hff hmb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hab rfl
  · exact hno hop
  · exact hno (opp_symm hop)
  · exact hab rfl

end two

end HP

end SolidGridHam
