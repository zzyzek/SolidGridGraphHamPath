/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.HP.LemmaB

/-!
# Stuck states (notes: P17's core, P20)

`StuckPF V F s t`: no Type III cell, and every valid strip of length at least 2 whose cells
have neither endpoint as a corner raises the component count. (A state with no UL move at
all satisfies this.)

`stuck_charged`: at such a state with at least two components, every Hamiltonian path `H`
has `D F H ≠ 0` on some cell with `s` or `t` as a corner (contrapositive of `lemmaB`).

`two_C_lines` (P20): two configuration-C lines cannot share the endpoint `t`: the vertex next
to `t` on the side away from `t`'s edge would keep at most one edge.
-/

namespace ULHC

open Finset Classical

namespace HP

def StuckPF (V : Finset Pt) (F : Finset Edge) (s t : Pt) : Prop :=
  NoTypeIII V F ∧ ∀ σ : StripSpec, ValidStrip V F σ → 2 ≤ σ.n →
    (∀ j < σ.n, ¬ IsCorner s (cellJ σ.c σ.s j) ∧ ¬ IsCorner t (cellJ σ.c σ.s j)) →
      ncomp V F < ncomp V (applyS F σ)

-- **P17's core.** At a stuck state, every Hamiltonian path is "charged" at an endpoint.
--
theorem stuck_charged {V : Finset Pt} {d : Pt → ℕ} {F H : Finset Edge} (hs : Solid V)
    (hF : IsFactor V d F) (hH : IsFactor V d H) (hHam : ncomp V H = 1) {s t : Pt}
    (hd : ∀ z, z ≠ s → z ≠ t → d z = 2) (hds : d s = 1) (hsV : s ∈ V)
    (hst : StuckPF V F s t) (h2 : 2 ≤ ncomp V F) :
    ∃ w, (IsCorner s w ∨ IsCorner t w) ∧ D F H w ≠ 0 := by
  by_contra hall
  push Not at hall
  obtain ⟨σ, hv, hn, _, hcor, hle, _, _, _⟩ :=
    lemmaB hs hF hH hHam hd hds hsV (fun w hw => hall w hw) hst.1 h2
  have := hst.2 σ hv hn hcor
  omega

-- **P20.** Let `t`'s only edge point E (`eR t`). The vertex `w` W of `t` loses `w–t`; if the two
-- configuration-C lines (into the cells NW and SW of `t`, in our pictures) both hold, they
-- also remove `w`'s vertical edges. Then `w` has at most one edge.
--
theorem two_C_lines {F : Finset Edge} {t : Pt} (htW : eL t ∉ F)
    (hup : eU (t.1 - 1, t.2) ∉ F) (hdown : eD (t.1 - 1, t.2) ∉ F) :
    deg F (t.1 - 1, t.2) ≤ 1 := by
  have hR : eR (t.1 - 1, t.2) = eL t := by
    obtain ⟨x, y⟩ := t; simp [eR, eL]
  unfold deg
  rw [hR]
  have h1 : ind F (eL t) = 0 := by simp [ind, htW]
  have h2 : ind F (eU (t.1 - 1, t.2)) = 0 := by simp [ind, hup]
  have h3 : ind F (eD (t.1 - 1, t.2)) = 0 := by simp [ind, hdown]
  have h4 := ind_le_one F (eL (t.1 - 1, t.2))
  omega

end HP

end ULHC
