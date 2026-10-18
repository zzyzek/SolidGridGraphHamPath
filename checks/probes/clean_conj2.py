# SPDX-License-Identifier: CC0-1.0
# Conjecture test: a TL path whose execution keeps the count and creates no Type III cell
# before a step is proper at that step (patterns hold, start separated).
# Random stuck instances; all TL paths up to length 4 and weight min + slack.
#
import sys, random, json
args = sys.argv[1:]
exec(open('/home/z/claude/ulhc-lean/checks/tl_algo.py').read())
src = open('/home/z/claude/ulhc-lean/checks/depth2_climb.py').read()
exec("def settle" + src.split("def settle")[1].split("best = None")[0])
E3 = {}
exec(open('/home/z/claude/ulhc-lean/checks/l57_check.py').read().split('def run(')[0], E3)
_e = open('/home/z/claude/ulhc-lean/checks/even_t3.py').read()
exec('import random\nimport networkx as nx\ndef grow_shape' + _e.split('def grow_shape')[1].rsplit('def run(', 1)[0], E3)
_t = open('/home/z/claude/ulhc-lean/checks/tl_enum.py').read()
exec('def tl_succ_all' + _t.split('def tl_succ_all')[1].split('def touches')[0])

st = {}
def bump(k): st[k] = st.get(k, 0) + 1
rng = random.Random(int(args[0]))
slack = int(args[2]); MAXLEN = int(args[3])
for t in range(int(args[1])):
  if t % 500 == 0: print('progress', t, st, flush=True)
  W = rng.choice([8, 10, 12]); Hh = rng.choice([8, 10, 12])
  V = set(E3['grow_shape'](W, Hh, rng))
  Fs = E3['two_factor'](V, rng)
  if Fs is None: continue
  F = {tuple(sorted(e)) for e in Fs}
  G = ph.induced(V); cells = ph.unit_cells(G)
  for _ in range(rng.randint(0, 40)):
    alts = [c for c in cells if is_alt(F, c)]
    if not alts: break
    F = apply(F, [[rng.choice(alts)]])
  F = settle(V, cells, F)
  n0 = ncomp(V, F)
  if n0 < 2: continue
  best = tl_search(V, cells, F)
  if best is None: continue
  wmin = sum(len(r) for r in best)
  cands = candidates(V, cells, F)
  pr = set(proper(V, cells, F))
  memo = {}; paths = []
  def go(path, w):
    x = path[-1]
    if len(x[0]) % 2 == 1: paths.append(list(path)); return
    if len(path) >= MAXLEN: return
    if x not in memo: memo[x] = tl_succ_all(V, cells, F, cands, x)
    for z in memo[x]:
      if w + len(z[0]) <= wmin + slack:
        path.append(z); go(path, w + len(z[0])); path.pop()
  for x in cands:
    if x[1] is None and x[0] in pr: go([x], len(x[0]))
  for p_ in paths:
    runs = [r for r, _ in p_]
    if len(runs) < 2: continue
    Fi = F; clean = True
    for i, r in enumerate(runs):
      prop = r in set(proper(V, cells, Fi))
      if not prop:
        if clean:
          bump('CLEAN_FAIL'); print('CLEAN_FAIL', json.dumps([sorted(V), sorted(F), [list(map(list, q)) for q in runs], i]), flush=True)
        else: bump('fail_after_unclean')
        break
      Fi = apply(Fi, [list(r)])
      if ncomp(V, Fi) != n0: clean = False
      cl = classes(V, Fi)
      if any(type3(Fi, cl, c) for c in cells): clean = False
    else:
      bump('valid')
print('final', st)
