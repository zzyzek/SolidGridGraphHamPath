/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import SolidGridHam.Cycle.Phase2
import SolidGridHam.Cycle.TheoremA

/-!
# One strip toward H for path-factors, and the endpoint-cell criterion (notes P18)

`one_strip_loc` is `one_strip` (TheoremA.lean) for two factors `F`, `H` with a common degree
function, with degree 2 needed only at corners of cells where `D` has the walk's sign. Its
strip's cells all have that sign.

`endpoint_criterion`: for path-factors (degree 2 except at `s`, `t`), if `D F H` vanishes on
every cell with `s` or `t` as a corner, then the hypothesis holds, and the strip lowers `μ`
and has neither `s` nor `t` as a corner of any of its cells.
-/

namespace SolidGridHam

open Finset Classical

namespace HP

-- `z` is one of the four corners of cell `w`.
--
def IsCorner (z w : Pt) : Prop :=
  z = w ∨ z = (w.1 + 1, w.2) ∨ z = (w.1, w.2 + 1) ∨ z = (w.1 + 1, w.2 + 1)

lemma good_ne_zero {o : Bool} {x : ℤ} (h : Good o x) : x ≠ 0 := by
  unfold Good at h; split_ifs at h <;> omega

end HP

end SolidGridHam
