/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.HP.AlgProto

/-!
# Native runner for the prototype

Reads one case per line from standard input:
`tag nV x1 y1 … sx sy tx ty nE d1 x1 y1 …` (edge direction `d` = 0 horizontal, 1 vertical,
from point `(x, y)`), and prints `tag code rounds restValid noDrop rounds_total` per case.
-/

open ULHC ULHC.HP

def parseCase (ws : List String) : Option (String × Finset Pt × Pt × Pt × Finset Edge) := do
  let tag :: rest := ws | none
  let ns ← rest.mapM String.toInt?
  let nV :: r1 := ns | none
  let pts := (List.range nV.toNat).map fun i => ((r1.getD (2 * i) 0, r1.getD (2 * i + 1) 0) : Pt)
  let r2 := r1.drop (2 * nV.toNat)
  let sx :: sy :: tx :: ty :: nE :: r3 := r2 | none
  let es := (List.range nE.toNat).map fun i =>
    let d := r3.getD (3 * i) 0
    let p : Pt := (r3.getD (3 * i + 1) 0, r3.getD (3 * i + 2) 0)
    (if d == 0 then ⟨.h, p⟩ else ⟨.v, p⟩ : Edge)
  pure (tag, pts.toFinset, (sx, sy), (tx, ty), es.toFinset)

partial def loop (h : IO.FS.Stream) (out : IO.FS.Stream) : IO Unit := do
  let line ← h.getLine
  if line.isEmpty then return
  let ws := ((line.replace "\n" " ").replace "\r" " ").splitOn " " |>.filter (· ≠ "")
  match parseCase ws with
  | some (tag, V, s, t, F) =>
    if tag.startsWith "W" then
      -- One state: is there a restricted Type III cell, and the minimum chain's weight and length.
      let t3 := (findT3R V F s t).isSome
      let r := match findPathR V F s t with
        | some (a, L) => s!"{wtL a L} {L.length + 1}"
        | none => "none"
      out.putStrLn s!"{tag} {t3} {r}"
      out.flush
      loop h out
    else
    let fuel := 4 * V.card ^ 2
    let (c, r, v, w) := runRC V s t fuel (0, 0, 0) none F
    out.putStrLn s!"{tag} {c} {r} {v} {w}"
    out.flush
  | none => out.putStrLn s!"PARSE_ERROR {ws.take 1}"; out.flush
  loop h out

def main : IO Unit := do
  loop (← IO.getStdin) (← IO.getStdout)
