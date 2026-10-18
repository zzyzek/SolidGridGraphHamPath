/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.HP.StripEvenPF

/-!
# Lemma B for path-factors (notes, section 6)

For path-factors `F`, `H` with endpoints `s`, `t` (`H` Hamiltonian), `F` with at least two
components and no Type III cell: if `D F H` vanishes on every cell with `s` or `t` as a
corner, the walk toward `H` gives a valid strip that lowers `μ` by twice its length, has
neither endpoint as a corner of any cell, and lowers the component count by 0 or 1 (by
exactly 1 when its length is odd).
-/

namespace ULHC

open Finset Classical

namespace HP

theorem lemmaB {V : Finset Pt} {d : Pt → ℕ} {F H : Finset Edge} (hs : Solid V)
    (hF : IsFactor V d F) (hH : IsFactor V d H) (hHam : ncomp V H = 1) {s t : Pt}
    (hd : ∀ z, z ≠ s → z ≠ t → d z = 2) (hds : d s = 1) (hsV : s ∈ V)
    (hz : ∀ w, IsCorner s w ∨ IsCorner t w → D F H w = 0)
    (hT : NoTypeIII V F) (h2 : 2 ≤ ncomp V F) :
    ∃ σ : StripSpec, ValidStrip V F σ ∧ 2 ≤ σ.n ∧ mu V (applyS F σ) H + 2 * σ.n = mu V F H ∧
      (∀ j < σ.n, ¬ IsCorner s (cellJ σ.c σ.s j) ∧ ¬ IsCorner t (cellJ σ.c σ.s j)) ∧
      ncomp V (applyS F σ) ≤ ncomp V F ∧ ncomp V F ≤ ncomp V (applyS F σ) + 1 ∧
      (σ.n % 2 = 1 → ncomp V (applyS F σ) + 1 = ncomp V F) ∧
      ∃ o, ParOK σ.c σ.s o ∧ ∀ j < σ.n, Good o (D F H (cellJ σ.c σ.s j)) := by
  obtain ⟨σ, hv, hn, hmu, hcor, o, hpo, hgo⟩ := endpoint_criterion hs hF hH hHam hd hz hT h2
  have hD : Deg2Off V F s t :=
    ⟨InsideST.of_inside (Inside.of_factor hF), fun z hz hzs hzt => by rw [hF.2 z hz]; exact hd z hzs hzt⟩
  have hdsF : deg F s = 1 := by rw [hF.2 s hsV]; exact hds
  have hst := conn_st hD hsV hdsF
  suffices hcnt : ncomp V (applyS F σ) ≤ ncomp V F ∧ ncomp V F ≤ ncomp V (applyS F σ) + 1 ∧
      (σ.n % 2 = 1 → ncomp V (applyS F σ) + 1 = ncomp V F) from
    ⟨σ, hv, hn, hmu, hcor, hcnt.1, hcnt.2.1, hcnt.2.2, o, hpo, hgo⟩
  obtain ⟨_, hpat, hcell, hsep⟩ := hv
  unfold applyS
  rcases Nat.mod_two_eq_zero_or_one σ.n with hev | hodd
  · obtain ⟨k, hk⟩ : ∃ k, σ.n = k + 2 := ⟨σ.n - 2, by omega⟩
    have hk2 : k % 2 = 0 := by omega
    rw [hk] at hpat hcell hcor ⊢
    have hsame : Conn F (back1 (cellJ σ.c σ.s (k + 1)) σ.s) (back2 (cellJ σ.c σ.s (k + 1)) σ.s) := by
      have hce := hcell (k + 1) (by omega)
      obtain ⟨_, hl, hf⟩ := hpat
      have ha : Alt F (cellJ σ.c σ.s (k + 1)) := by
        have l1 := (hl (k + 1) (by omega)).1.2 (by omega)
        have l2 := (hl (k + 1) (by omega)).2.2 (by omega)
        have fF : front (cellJ σ.c σ.s (k + 1)) σ.s ∉ F := by
          intro h; have := (hf (k + 1) (by omega)).1 h; omega
        have bF : back (cellJ σ.c σ.s (k + 1)) σ.s ∉ F := by
          rw [back_cellJ_succ]; intro h; have := (hf k (by omega)).1 h; omega
        rw [lat1_eq] at l1
        rw [lat2_eq] at l2
        simp only [back, front] at fF bF
        generalize cellJ σ.c σ.s (k + 1) = r at *
        obtain ⟨x, y⟩ := r
        cases hs' : σ.s <;> rw [hs'] at l1 l2 fF bF <;>
          simp only [latA, latB, sideEdge, Side.opp] at l1 l2 fF bF <;> unfold Alt <;> tauto
      obtain ⟨k1, k2, k3⟩ := alt_corners_conn hT hce ha
      generalize cellJ σ.c σ.s (k + 1) = r at *
      obtain ⟨x, y⟩ := r
      cases σ.s <;> simp only [back1, back2] at * <;>
        first
        | exact k1
        | exact k2.symm.trans k3
        | exact k1.symm.trans k3
        | exact k2
    obtain ⟨b1, b2⟩ := strip_even_count_pf k hk2 F hD hsV hdsF (fun j hj => hcell j (by omega))
      (fun j hj => hcor j (by omega)) hpat hsep hsame
    exact ⟨b1, b2, fun h => by omega⟩
  · obtain ⟨k, hk⟩ : ∃ k, σ.n = k + 1 := ⟨σ.n - 1, by omega⟩
    have hk2 : k % 2 = 0 := by omega
    rw [hk] at hpat hcell hcor ⊢
    have := strip_odd_count_pf k hk2 F hD hst (fun j hj => hcell j (by omega))
      (fun j hj => hcor j (by omega)) hpat hsep
    exact ⟨by omega, by omega, fun _ => this⟩

end HP

end ULHC
