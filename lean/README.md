# Lean package `ulhc`

The Lean 4 library `ULHC`. See the [top-level README](../README.md) for what is proved, how to
build, and how to check it, and [`../docs/MAP.md`](../docs/MAP.md) for the statement map.

* `ULHC.lean`: imports every module.
* `ULHC/Main.lean`: the main theorem `ULHC.ulhc_main`.
* `CheckAxioms.lean`: `#print axioms` for the main results (`lake env lean CheckAxioms.lean`).
* `build.sh`: `lake build`, optionally with memory and thread limits (`ULHC_MEM`,
  `LEAN_NUM_THREADS`).

Finite case checks (for example `walk_local`, `inter_local`) use kernel `decide`; there is no
`native_decide`.
