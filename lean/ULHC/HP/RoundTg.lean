/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.HP.CompCleanTg

/-!
# One round, rule Tg (ULHC `round_ca`)

After the first strip `a` of a minimum restricted Tg chain, the rest is a restricted Tg chain of
`F ⊕ a`, lighter by `a`'s length; for `a` count-neutral, `F ⊕ a` with no restricted Type III
cell, and E1–E3 at `a`. This is what an algorithm that applies one strip per round (as ULHC
does) needs for its progress measure.
-/

namespace ULHC

namespace HP

open Finset Classical

-- **NEW MATH (phantom near lemma, one round).** `round_tg` for a phantom endpoint (`t0 ∉ V`).
--
def Gap_round : Prop :=
  ∀ {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ} {s0 t0 : Pt}
    {b : StripSpec} {L : List StripSpec},
    Deg2Off V F s0 t0 → s0 ∈ V → deg F s0 = 1 → (∀ z, deg F z ≤ 2) → NoTypeIIIR V F s0 t0 →
    k % 2 = 0 → (∀ j ≤ k + 1, IsCell V (cellJ c s j)) →
    (∀ j ≤ k + 1, ¬ IsCorner s0 (cellJ c s j) ∧ ¬ IsCorner t0 (cellJ c s j)) →
    StripPat F c s (k + 2) → ¬ Conn F (back1 c s) (front1 c s) →
    NoTypeIIIR V (flipCol F c s (k + 2)) s0 t0 → ncomp V (flipCol F c s (k + 2)) = ncomp V F →
    (∀ tf, (tf = latA s ∨ tf = latB s) → IsCell V (nb c tf) → NotTypeIII V F (nb c tf)) →
    (∀ tf, (tf = latA s ∨ tf = latB s) → IsCell V (nb (cellJ c s (k + 1)) tf) →
      NotTypeIII V (flipCol F c s (k + 2)) (nb (cellJ c s (k + 1)) tf)) →
    (∀ tf, (tf = latA s ∨ tf = latB s) → IsCell V (nb (nb c tf) s.opp) →
      NotTypeIII V F (nb (nb c tf) s.opp)) →
    RPathTg V F s0 t0 ⟨c, s, k + 2⟩ (b :: L) →
    (∀ σ L', RPathTg V F s0 t0 σ L' → wt ⟨c, s, k + 2⟩ (b :: L) ≤ wt σ L') →
    ¬ PDang V t0 → t0 ∉ V →
    RPathTg V (flipCol F c s (k + 2)) s0 t0 b L ∧ wt b L + (k + 2) = wt ⟨c, s, k + 2⟩ (b :: L)

class RoundOK (V : Finset Pt) (t0 : Pt) : Prop where
  ok : t0 ∈ V ∨ PDang V t0 ∨ Gap_round

lemma RoundOK.of_mem {V : Finset Pt} {t0 : Pt} (h : t0 ∈ V) : RoundOK V t0 := ⟨Or.inl h⟩

lemma RoundOK.of_pdang {V : Finset Pt} {t0 : Pt} (h : PDang V t0) : RoundOK V t0 :=
  ⟨Or.inr (Or.inl h)⟩

section round

variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ} {s0 t0 : Pt}
  (hF : Deg2Off V F s0 t0) (hs0 : s0 ∈ V) (hds : deg F s0 = 1) (hle : ∀ z, deg F z ≤ 2)
  (hTR : NoTypeIIIR V F s0 t0) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j))
  (hcor : ∀ j ≤ k + 1, ¬ IsCorner s0 (cellJ c s j) ∧ ¬ IsCorner t0 (cellJ c s j))
  (hpat : StripPat F c s (k + 2))
  (hsep : ¬ Conn F (back1 c s) (front1 c s)) (hT' : NoTypeIIIR V (flipCol F c s (k + 2)) s0 t0)
  (hneut : ncomp V (flipCol F c s (k + 2)) = ncomp V F)
  (hTs : ∀ tf, (tf = latA s ∨ tf = latB s) → IsCell V (nb c tf) → NotTypeIII V F (nb c tf))
  (hTend : ∀ tf, (tf = latA s ∨ tf = latB s) → IsCell V (nb (cellJ c s (k + 1)) tf) →
    NotTypeIII V (flipCol F c s (k + 2)) (nb (cellJ c s (k + 1)) tf))
  (hTd : ∀ tf, (tf = latA s ∨ tf = latB s) → IsCell V (nb (nb c tf) s.opp) →
    NotTypeIII V F (nb (nb c tf) s.opp))
include hF hs0 hds hle hTR hk hcell hcor hpat hsep hT' hneut hTs hTend hTd

-- **One round** (ULHC `near_far_CA` + `progress_step_CA`).
--
theorem round_tg [hr : RoundOK V t0] {b : StripSpec} {L : List StripSpec}
    (hP : RPathTg V F s0 t0 ⟨c, s, k + 2⟩ (b :: L))
    (hmin : ∀ σ L', RPathTg V F s0 t0 σ L' → wt ⟨c, s, k + 2⟩ (b :: L) ≤ wt σ L') :
    RPathTg V (flipCol F c s (k + 2)) s0 t0 b L ∧ wt b L + (k + 2) = wt ⟨c, s, k + 2⟩ (b :: L) := by
  by_cases ht0 : t0 ∈ V ∨ PDang V t0
  swap
  · have h1 : t0 ∉ V := fun h => ht0 (Or.inl h)
    have h2 : ¬ PDang V t0 := fun h => ht0 (Or.inr h)
    exact ((hr.ok.resolve_left h1).resolve_left h2) hF hs0 hds hle hTR hk hcell hcor hpat hsep hT'
      hneut hTs hTend hTd hP hmin h2 h1
  have : NearOK V t0 := ⟨by rcases ht0 with h | h; exacts [Or.inl h, Or.inr (Or.inl h)]⟩
  obtain ⟨_, hch, hcat, hR⟩ := hP
  have hRb : ∀ x ∈ b :: L, Restr s0 t0 x := fun x hx => hR x (List.mem_cons_of_mem _ hx)
  have hWeq : wt ⟨c, s, k + 2⟩ (b :: L) = k + 2 + wt b L := wt_cons _ _ _
  have hvia : ViaFreeTg V F s0 t0 ⟨c, s, k + 2⟩ (wt ⟨c, s, k + 2⟩ (b :: L)) :=
    fun w R hP' _ _ hlt => by have := hmin _ _ hP'; omega
  have hab := hch.2.1
  have hfar : FarChainCA F ⟨c, s, k + 2⟩ b L := by
    cases L with
    | nil => trivial
    | cons τ L' =>
      have hbe : b.n % 2 = 0 := hch.2.2.1
      have hbfar : ∀ j < k + 2, ∀ y ∈ cellE (endCell b), y ∉ cellE (cellJ c s j) := by
        intro j hj y hy hy'
        by_cases hja : j + 1 < k + 2
        · exact hab.2.2.2.2.2.1 (b.n - 1) (by have := hab.2.2.1; omega) j hja y hy hy'
        · obtain rfl : j = k + 1 := by omega
          exact hab.2.2.2.2.2.2.2.1 hbe y hy hy'
      exact farchain_pf hle hk hcell hcor hpat hsep hvia (τ :: L') b hch.2.2 hcat.2
        (endOK_of_link hab) hRb hbfar
        (notouch_pf hF hs0 hds hle hTR hk hcell hcor hpat hsep hT' hneut hTs hTend hTd hmin hvia
          (fun h hn => by rcases ht0 with h' | h'; exacts [absurd h' h, absurd h' hn]) (τ :: L') b hch.2.2 hcat.2 (endOK_of_link hab) hRb (by omega) (by omega))
        (by omega)
  exact progress_step_pf hF hs0 hds hTR hk hcell hcor hpat hsep hneut hT' hch hcat hRb hfar

end round

end HP

end ULHC
