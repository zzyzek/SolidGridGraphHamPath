/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import SolidGridHam.Path.Agree

/-!
# Sheffield 4.8 ("stuck ⇒ minimal"): comparison facts along rows

For factors `H`, `H'` with the same degrees, `D H H'` is `τ_H − τ_H'` (`D.lean`), and
`outArc H c s` says the face across side `s` of `c` is higher than `c` for `H`. Stepping along
`H`'s arc changes `D H H'` by `0` or `+2` (`D_step`), so:

* `D_mono_arc`: `D H H'` never decreases along an arc of `H`;
* `D_mono_row`: nor along a row of squares climbing in `H` (Sheffield's maximal rows);
* `row_stays_inside`: a row climbing from a face where `H'` is lower (`D > 0`) never reaches a
  face where the heights are fixed (`D = 0`, e.g. the outside of a solid graph): Sheffield's
  "since τ_H and τ_H' agree on holes and the unbounded face";
* `pair_one_side`: the two members of a fixed pair cannot have `H'` lower at the top and higher
  at the bottom, so no fixed pair is claimed from both sides (Sheffield's "if f₁ is maximal in
  F₊, f₂ cannot be minimal in F₋").
-/

namespace SolidGridHam

namespace HP

open Finset

section taut

variable {V : Finset Pt} {d : Pt → ℕ} {H H' : Finset Edge}
  (hH : IsFactor V d H) (hH' : IsFactor V d H')
include hH hH'

-- `D H H'` does not decrease along an arc of `H`.
--
lemma D_mono_arc {c : Pt} {s : Side} (ha : outArc H c s = true) :
    D H H' c ≤ D H H' (nb c s) := by
  have h := D_step hH hH' c s
  simp only [ha, ↓reduceIte] at h
  split_ifs at h <;> omega

-- Nor along a row of squares each higher than the one before it.
--
lemma D_mono_row {c : Pt} {s : Side} :
    ∀ n, (∀ j < n, outArc H (cellJ c s j) s = true) →
      D H H' (cellJ c s 0) ≤ D H H' (cellJ c s n)
  | 0, _ => le_rfl
  | n + 1, ha => by
    have ih := D_mono_row n (fun j hj => ha j (by omega))
    have h := D_mono_arc hH hH' (ha n (by omega))
    rw [nb_cellJ] at h
    exact ih.trans h

-- A climbing row that starts where `H'` is lower never reaches a face with `D = 0`.
--
-- `D` does not increase along a row of arcs pointing back.
--
lemma D_anti_row {c : Pt} {s : Side} :
    ∀ n, (∀ j < n, outArc H (cellJ c s j) s = false) →
      D H H' (cellJ c s n) ≤ D H H' (cellJ c s 0)
  | 0, _ => le_rfl
  | n + 1, ha => by
    have ih := D_anti_row n (fun j hj => ha j (by omega))
    have h := D_step hH hH' (cellJ c s n) s
    rw [ha n (by omega), nb_cellJ] at h
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    split_ifs at h <;> omega

lemma row_stays_inside {c : Pt} {s : Side} {n : ℕ} (hpos : 0 < D H H' (cellJ c s 0))
    (ha : ∀ j < n, outArc H (cellJ c s j) s = true) : D H H' (cellJ c s n) ≠ 0 := by
  have := D_mono_row hH hH' n ha
  omega

-- In a solid graph the climbing row stays on cells of `V`.
--
lemma row_cells {c : Pt} {s : Side} {n : ℕ} (hsol : SolidFor V H H')
    (hpos : 0 < D H H' (cellJ c s 0)) (ha : ∀ j < n, outArc H (cellJ c s j) s = true) :
    IsCell V (cellJ c s n) := by
  by_contra hc
  exact row_stays_inside hH hH' hpos ha (hsol _ hc)

-- A fixed pair (bottom `a`, top `nb a s` higher) is not lower in `H'` at the top and higher in
-- `H'` at the bottom.
--
lemma pair_one_side {a : Pt} {s : Side} (ha : outArc H a s = true)
    (htop : 0 < D H H' (nb a s)) (hbot : D H H' a < 0) : False := by
  have h := D_step hH hH' a s
  simp only [ha, ↓reduceIte] at h
  obtain ⟨k, hk⟩ := D_even H H' (nb a s)
  obtain ⟨l, hl⟩ := D_even H H' a
  split_ifs at h <;> omega

end taut

end HP

end SolidGridHam
