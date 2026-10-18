/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import Lake
open Lake DSL

package «ulhc» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «ULHC» where

lean_exe protorun where
  root := `ULHC.HP.ProtoMain
