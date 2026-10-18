# SPDX-License-Identifier: CC0-1.0
# Hill-climb for factors with long clean V2 executions (each strip proper, on the chain created
# by the previous one, disjoint from earlier strips; every factor Type III-free with the same
# count). Prints instances with at least MIN clean steps.
#
import sys, random, json
from collections import deque
args = sys.argv[1:]
exec(open('/home/z/claude/ulhc-lean/checks/chain_avoid.py').read().split("st = {}")[0])
def clean_walk(V, cells, F, rng, tries=6):
  n0 = ncomp(V, F); best = []
  for _ in range(tries):
    seq = []; Fi = F; anchor = None
    for step in range(10):
      pr = [r for r in proper(V, cells, Fi) if len(r) % 2 == 0]
      if anchor is not None:
        ch = chain(V, cells, Fi, anchor); pr = [r for r in pr if r[0] in ch]
      used = set(c for q in seq for c in q)
      pr = [r for r in pr if not (set(r) & used)]
      rng.shuffle(pr); moved = False
      for r in pr[:6]:
        F2 = apply(Fi, [list(r)]); cl2 = classes(V, F2)
        if ncomp(V, F2) == n0 and not any(type3(F2, cl2, c) for c in cells):
          seq.append(r); Fi = F2; anchor = r[-1]; moved = True; break
      if not moved: break
    if len(seq) > len(best): best = seq
  return best
rng = random.Random(int(args[0])); MIN = int(args[2])
for r in range(int(args[1])):
  W = rng.choice([10, 12, 14]); Hh = rng.choice([10, 12, 14])
  V = set(E3['grow_shape'](W, Hh, rng))
  Fs = E3['two_factor'](V, rng)
  if Fs is None: continue
  F = {tuple(sorted(e)) for e in Fs}
  G = ph.induced(V); cells = ph.unit_cells(G)
  F = settle(V, cells, F)
  if ncomp(V, F) < 2: continue
  sc = len(clean_walk(V, cells, F, rng))
  for it in range(40):
    moves = [[c] for c in cells if is_alt(F, c)]
    if not moves: break
    F2 = settle(V, cells, apply(F, [rng.choice(moves)]))
    if ncomp(V, F2) < 2: continue
    seq = clean_walk(V, cells, F2, rng)
    if len(seq) >= sc or rng.random() < 0.05:
      F, sc = F2, len(seq)
      if sc >= MIN:
        print('CLEAN', sc, json.dumps([sorted(V), sorted(F), [list(map(list, q)) for q in seq]]), flush=True)
  if r % 20 == 0: print('round', r, 'score', sc, flush=True)
