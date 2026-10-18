# SPDX-License-Identifier: CC0-1.0
# Adversarial hunt for counterexamples to conjecture (C): mutate stuck factors and look for a
# TL path that fails while its execution is still clean (no Type III, count unchanged).
#
import sys, random, json
args = sys.argv[1:]
exec(open('/home/z/claude/ulhc-lean/checks/clean_var.py').read().split("st = {}")[0].replace("VARIANT = args[3]", "VARIANT = args[3]"))
def clean_fail(V, cells, F, maxlen, slack):
  n0 = ncomp(V, F)
  best = tl_search(V, cells, F)
  if best is None: return None, 0
  wmin = sum(len(r) for r in best)
  cands = candidates(V, cells, F); pr = set(proper(V, cells, F))
  memo = {}; paths = []
  def go(path, w):
    x = path[-1]
    if len(x[0]) % 2 == 1: paths.append(list(path)); return
    if len(path) >= maxlen: return
    if x not in memo: memo[x] = tl_succ_all(V, cells, F, cands, x)
    for z in memo[x]:
      if w + len(z[0]) <= wmin + slack:
        path.append(z); go(path, w + len(z[0])); path.pop()
  for x in cands:
    if x[1] is None and x[0] in pr: go([x], len(x[0]))
  nmulti = 0
  for p_ in paths:
    runs = [r for r, _ in p_]
    if len(runs) < 2: continue
    nmulti += 1
    Fi = F
    for i, r in enumerate(runs):
      if r not in set(proper(V, cells, Fi)): return (runs, i), nmulti
      Fi = apply(Fi, [list(r)])
      if ncomp(V, Fi) != n0: break
      cl = classes(V, Fi)
      if any(type3(Fi, cl, c) for c in cells): break
  return None, nmulti
rng = random.Random(int(args[0]))
tot = 0
for r in range(int(args[1])):
  W = rng.choice([8, 10, 12, 14]); Hh = rng.choice([8, 10, 12, 14])
  V = set(E3['grow_shape'](W, Hh, rng))
  Fs = E3['two_factor'](V, rng)
  if Fs is None: continue
  F = {tuple(sorted(e)) for e in Fs}
  G = ph.induced(V); cells = ph.unit_cells(G)
  F = settle(V, cells, F)
  for it in range(30):
    moves = [[c] for c in cells if is_alt(F, c)]
    if not moves: break
    F2 = settle(V, cells, apply(F, [rng.choice(moves)]))
    if ncomp(V, F2) < 2: continue
    F = F2
    res, nm = clean_fail(V, cells, F, 5, 6)
    tot += nm
    if res is not None:
      print('C_COUNTEREXAMPLE', json.dumps([sorted(V), sorted(F), [list(map(list, q)) for q in res[0]], res[1]]), flush=True)
  if r % 20 == 0: print('round', r, 'multi-strip paths checked', tot, flush=True)
print('done', tot)
