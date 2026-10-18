/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import Lake
open Lake DSL

package «solidgridham» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «SolidGridHam» where

-- The Palomar registry statement (`Challenge`, imports only Mathlib) and its solution.
--
lean_lib «Challenge» where

lean_lib «Solution» where
