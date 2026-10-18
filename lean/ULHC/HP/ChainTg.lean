/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.HP.CompCleanPF

/-!
# Chains with twist endings (rule Tg)

ULHC's chains (`CRChain`) end with an odd strip. Path-factors also need even endings: an even
strip whose end cell, flipped in `G`, twists the path (leaves the count unchanged) merges two
components (T6). Rule Tg (notes 5g, 2026-10-12): a chain ends with an odd strip, or with an even
strip whose end cell twists when flipped in `G` itself. The test looks at `G` and the end cell
only, so it does not depend on the earlier strips: suffixes and ULHC's path surgery keep it, and
a link that fails after a neutral strip because the previous end cell now twists becomes an early
end.
-/

namespace ULHC

namespace HP

open Finset Classical

-- An alternating cell whose flip leaves the count unchanged (it twists the s-t path).
--
def TwistsIn (V : Finset Pt) (G : Finset Edge) (u : Pt) : Prop :=
  Alt G u ∧ ncomp V (flip G u) = ncomp V G

-- The good end of a chain under rule Tg.
--
def TgEnd (V : Finset Pt) (G : Finset Edge) (σ : StripSpec) : Prop :=
  σ.n % 2 = 1 ∨ (σ.n % 2 = 0 ∧ TwistsIn V G (endCell σ))

-- **Chains with Tg endings**: middles even and linked (ULHC `CR2`), the last strip a Tg end.
--
def CRChainTg (V : Finset Pt) (G : Finset Edge) : StripSpec → List StripSpec → Prop
  | σ, [] => TgEnd V G σ
  | σ, τ :: L => σ.n % 2 = 0 ∧ CR2 V G σ τ ∧ CRChainTg V G τ L

-- **Restricted Tg paths**: a valid first strip, a Tg chain, ULHC's chain side condition, every
-- strip avoiding the endpoint cells.
--
def RPathTg (V : Finset Pt) (G : Finset Edge) (s0 t0 : Pt) (σ : StripSpec) (L : List StripSpec) :
    Prop :=
  ValidStrip V G σ ∧ CRChainTg V G σ L ∧ CATail (σ :: L) ∧ ∀ x ∈ σ :: L, Restr s0 t0 x

-- ULHC's chains are Tg chains.
--
lemma crChainTg_of_crChain {V : Finset Pt} {G : Finset Edge} :
    ∀ (L : List StripSpec) (σ : StripSpec), CRChain V G σ L → CRChainTg V G σ L := by
  intro L
  induction L with
  | nil => intro σ h; exact Or.inl h
  | cons τ L ih =>
    intro σ h
    exact ⟨h.1, h.2.1, ih τ h.2.2⟩

-- The end cell of a strip is the end cell of its suffix from any index before its length.
--
lemma tgEnd_suf {V : Finset Pt} {G : Finset Edge} {z : StripSpec} {i : ℕ} (he : i % 2 = 0)
    (hi : i < z.n) (h : TgEnd V G z) : TgEnd V G (suf z i) := by
  have hn : (suf z i).n = z.n - i := rfl
  have hend : endCell (suf z i) = endCell z := suf_end hi
  rcases h with h | ⟨h1, h2⟩
  · left; rw [hn]; omega
  · right; rw [hn, hend]; exact ⟨by omega, h2⟩

end HP

end ULHC
