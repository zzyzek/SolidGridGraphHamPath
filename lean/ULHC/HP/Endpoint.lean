/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.HP.LocalWalk
import ULHC.TheoremA

/-!
# One strip toward H for path-factors, and the endpoint-cell criterion (notes P18)

`one_strip_loc` is `one_strip` (TheoremA.lean) for two factors `F`, `H` with a common degree
function, with degree 2 needed only at corners of cells where `D` has the walk's sign. Its
strip's cells all have that sign.

`endpoint_criterion`: for path-factors (degree 2 except at `s`, `t`), if `D F H` vanishes on
every cell with `s` or `t` as a corner, then the hypothesis holds, and the strip lowers `μ`
and has neither `s` nor `t` as a corner of any of its cells.
-/

namespace ULHC

open Finset Classical

namespace HP

-- `z` is one of the four corners of cell `w`.
--
def IsCorner (z w : Pt) : Prop :=
  z = w ∨ z = (w.1 + 1, w.2) ∨ z = (w.1, w.2 + 1) ∨ z = (w.1 + 1, w.2 + 1)

lemma good_ne_zero {o : Bool} {x : ℤ} (h : Good o x) : x ≠ 0 := by
  unfold Good at h; split_ifs at h <;> omega

-- If `D` vanishes on the cells with an endpoint as a corner, every cell where `D` has a walk's
-- sign has degree 2 at its corners.
--
lemma deg2Cell_of_zero {V : Finset Pt} {d : Pt → ℕ} {F H : Finset Edge}
    (hF : IsFactor V d F) (_hH : IsFactor V d H) (hs : SolidFor V F H) {s t : Pt}
    (hd : ∀ z, z ≠ s → z ≠ t → d z = 2)
    (hz : ∀ w, IsCorner s w ∨ IsCorner t w → D F H w = 0)
    (o : Bool) (w : Pt) (hg : Good o (D F H w)) : Deg2Cell F w := by
  have hD := good_ne_zero hg
  obtain ⟨c1, c2, c3, c4⟩ := Good.isCell_f hs hg
  have key : ∀ z, IsCorner z w → z ∈ V → deg F z = 2 := by
    intro z hzw hzV
    rw [hF.2 z hzV]
    apply hd
    · rintro rfl; exact hD (hz w (Or.inl hzw))
    · rintro rfl; exact hD (hz w (Or.inr hzw))
  exact ⟨key _ (Or.inl rfl) c1, key _ (Or.inr (Or.inl rfl)) c2,
    key _ (Or.inr (Or.inr (Or.inl rfl))) c3, key _ (Or.inr (Or.inr (Or.inr rfl))) c4⟩

-- One strip from the walk toward `H` (common degree function, local degree hypothesis).
--
lemma one_strip_loc {V : Finset Pt} {d : Pt → ℕ} {F H : Finset Edge} (hs : Solid V)
    (hF : IsFactor V d F) (hH : IsFactor V d H) (hHam : ncomp V H = 1)
    (hT : NoTypeIII V F) (h2 : 2 ≤ ncomp V F)
    (hloc : ∀ o w, Good o (D F H w) → Deg2Cell F w) :
    ∃ σ : StripSpec, ValidStrip V F σ ∧ 2 ≤ σ.n ∧ mu V (applyS F σ) H + 2 * σ.n = mu V F H ∧
      ∃ o, ParOK σ.c σ.s o ∧ ∀ j < σ.n, Good o (D F H (cellJ σ.c σ.s j)) := by
  obtain ⟨x, hx, y, hy, hxy⟩ := exists_not_conn h2
  set P := cls V F x
  have hB : Border V F P := ⟨Finset.filter_subset _ _, fun u hu w hw => closed_cls (Inside.of_factor hF) x u hu w hw⟩
  have hxP : x ∈ P := mem_cls_self hx
  have hyP : y ∉ P := by simp only [P, cls, Finset.mem_filter, not_and]; exact fun _ => hxy
  obtain ⟨e, heH, hcut⟩ := exists_cut_edge (conn_of_ncomp_one hHam hx hy) hxP hyP
  have heF : e ∉ F := fun h => hB.not_cut h hcut
  obtain ⟨sh, sl, h1, h2', h3, h4, h5, h6⟩ := edge_cells F e
  have hjump := D_jump hF hH e
  have hw : wD F H e = if up F e then 2 else -2 := by
    unfold wD wb; simp [heF, heH]
  rw [hw] at hjump
  -- Choose the orientation from the sign of `D` at the arc's tail.
  have key : ∃ o v s0, Cut P (sideEdge v s0) ∧ outArc F v s0 = !o ∧
      (if o then D F H v = D F H (nb v s0) + 2 else D F H v = D F H (nb v s0) - 2) ∧
      Good o (D F H v) := by
    -- `a` is the tail of the arc across `e`, `b` its head; `D b = D a + 2`.
    obtain ⟨a, b, sa, sb, ha1, ha2, ha3, hb1, hb2, hb3, hD⟩ :
        ∃ a b sa sb, sideEdge a sa = e ∧ nb a sa = b ∧ outArc F a sa = true ∧
          sideEdge b sb = e ∧ nb b sb = a ∧ outArc F b sb = false ∧
          D F H b = D F H a + 2 := by
      cases hu : up F e
      · refine ⟨e.hi, e.lo, sh, sl, h1, h2', by rw [h3, hu]; rfl, h4, h5, by rw [h6, hu], ?_⟩
        rw [hu] at hjump; simp at hjump; omega
      · refine ⟨e.lo, e.hi, sl, sh, h4, h5, by rw [h6, hu], h1, h2', by rw [h3, hu]; rfl, ?_⟩
        rw [hu] at hjump; simp at hjump; omega
    by_cases hpos : 0 ≤ D F H a
    · refine ⟨true, b, sb, by rw [hb1]; exact hcut, by rw [hb3]; rfl, ?_, ?_⟩
      · simp only [ite_true]; rw [hb2]; exact hD
      · unfold Good; simp; omega
    · obtain ⟨m, hm⟩ := D_even F H a
      refine ⟨false, a, sa, by rw [ha1]; exact hcut, by rw [ha3]; rfl, ?_, ?_⟩
      · simp only [Bool.false_eq_true, ite_false]; rw [ha2]; omega
      · unfold Good; simp; omega
  obtain ⟨o, v, s0, hc0, hi0, hj0, hg0⟩ := key
  obtain ⟨w, _, hgw, hst⟩ := phase1_loc hF hH (SolidFor.of_solid hF hH hs) hB hT o (hloc o) v s0 hc0 hi0 hj0 hg0
  obtain ⟨s, n, hn, hpat, hcell, hgood, hp, hsep⟩ := phase2_loc hF hH (SolidFor.of_solid hF hH hs) hB (hloc o) hgw hst
  refine ⟨⟨w, s, n⟩, ⟨show 1 ≤ n by omega, hpat, hcell, hsep⟩, hn, strip_mu hp n hpat hcell hgood, ?_⟩
  exact ⟨o, hp, hgood⟩

-- **Endpoint-cell criterion (notes P18).** For path-factors with endpoints `s`, `t`: if `D F H`
-- vanishes on every cell with `s` or `t` as a corner, the walk toward `H` gives a valid strip
-- of length at least 2 that lowers `μ` by twice its length, and none of its cells has `s` or
-- `t` as a corner.
--
theorem endpoint_criterion {V : Finset Pt} {d : Pt → ℕ} {F H : Finset Edge} (hs : Solid V)
    (hF : IsFactor V d F) (hH : IsFactor V d H) (hHam : ncomp V H = 1) {s t : Pt}
    (hd : ∀ z, z ≠ s → z ≠ t → d z = 2)
    (hz : ∀ w, IsCorner s w ∨ IsCorner t w → D F H w = 0)
    (hT : NoTypeIII V F) (h2 : 2 ≤ ncomp V F) :
    ∃ σ : StripSpec, ValidStrip V F σ ∧ 2 ≤ σ.n ∧ mu V (applyS F σ) H + 2 * σ.n = mu V F H ∧
      (∀ j < σ.n, ¬ IsCorner s (cellJ σ.c σ.s j) ∧ ¬ IsCorner t (cellJ σ.c σ.s j)) ∧
      ∃ o, ParOK σ.c σ.s o ∧ ∀ j < σ.n, Good o (D F H (cellJ σ.c σ.s j)) := by
  obtain ⟨σ, hv, hn, hmu, o, hp, hg⟩ :=
    one_strip_loc hs hF hH hHam hT h2 (deg2Cell_of_zero hF hH (SolidFor.of_solid hF hH hs) hd hz)
  refine ⟨σ, hv, hn, hmu, fun j hj => ?_, o, hp, hg⟩
  have h0 := good_ne_zero (hg j hj)
  exact ⟨fun h => h0 (hz _ (Or.inl h)), fun h => h0 (hz _ (Or.inr h))⟩

end HP

end ULHC
