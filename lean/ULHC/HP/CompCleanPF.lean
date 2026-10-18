/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.HP.RelPF
import ULHC.PathComplete
import ULHC.HP.AlgPF

/-!
# Restricted strips (path-factors)

`Restr`: no cell of a strip has an endpoint as a corner; `NoTypeIIIR`: no Type III cell away
from the endpoint cells. (The completeness step itself is `comp_clean_tg`, `CompCleanTg.lean`;
the earlier skeleton with an end-rule parameter was replaced by rule Tg.)
-/

namespace ULHC

namespace HP

open Finset Classical

-- No cell of the strip has `s0` or `t0` as a corner.
--
def Restr (s0 t0 : Pt) (σ : StripSpec) : Prop :=
  ∀ j < σ.n, ¬ IsCorner s0 (cellJ σ.c σ.s j) ∧ ¬ IsCorner t0 (cellJ σ.c σ.s j)

-- No Type III cell away from the endpoint cells.
--
def NoTypeIIIR (V : Finset Pt) (F : Finset Edge) (s0 t0 : Pt) : Prop :=
  ∀ c, IsCell V c → ¬ IsCorner s0 c → ¬ IsCorner t0 c → NotTypeIII V F c


end HP

end ULHC
