# SPDX-License-Identifier: CC0-1.0
# Stress test on stuck 2-factors from the broad sampler: run the thesis-style search
# (find_seq) and the pairwise-exact search (px_search); simulate each strip by strip and
# check that the count drops. Hamiltonicity by ILP when a search returns nothing.
#
# Usage: python3 checks/stress.py SEED TRIALS W,H,..
#
import random, sys
args = sys.argv[1:]
exec(open('/home/z/claude/ulhc-lean/checks/px_algo.py').read())
src = open('/home/z/claude/ulhc-lean/checks/depth2_climb.py').read()
exec("def settle" + src.split("def settle")[1].split("best = None")[0])
E3 = {}
exec(open('/home/z/claude/ulhc-lean/checks/l57_check.py').read().split('def run(')[0], E3)
_e = open('/home/z/claude/ulhc-lean/checks/even_t3.py').read()
exec('import random\nimport networkx as nx\ndef grow_shape' + _e.split('def grow_shape')[1].rsplit('def run(', 1)[0], E3)

seed, trials = int(args[0]), int(args[1])
sizes = [int(x) for x in args[2].split(',')]
rng = random.Random(seed)
st = dict(loc1_fail=0, loc2_fail=0, stuck=0, ham=0, nonham=0, th_ok=0, th_fail=0, px_ok=0, px_fail=0, th_len={}, px_len={})
def simok(V, cells, F, runs):
  F2 = simulate(V, cells, F, [tuple(r) for r in runs])
  return F2 is not None and is_factor(V, F2) and ncomp(V, F2) < ncomp(V, F)
for t in range(trials):
  if t % 2000 == 0: print('progress', t, st, flush=True)
  W = rng.choice(sizes); Hh = rng.choice(sizes)
  V = E3['grow_shape'](W, Hh, rng)
  Fs = E3['two_factor'](V, rng)
  if Fs is None: continue
  V = set(V); F = {tuple(sorted(e)) for e in Fs}
  G = ph.induced(V); cells = ph.unit_cells(G)
  for _ in range(rng.randint(0, 50)):
    alts = [c for c in cells if is_alt(F, c)]
    if not alts: break
    F = apply(F, [[rng.choice(alts)]])
  F = settle(V, cells, F)
  if ncomp(V, F) < 2: continue
  st['stuck'] += 1
  th = find_seq(V, cells, F)
  px = px_search(V, cells, F)
  if th is None or px is None:
    h = ham_cycle(V) is not None
  else:
    h = True
  st['ham' if h else 'nonham'] += 1
  if h:
    for dd in (1, 2):
      q = px_search(V, cells, F, local=dd)
      if q is None or not simok(V, cells, F, q):
        st['loc%d_fail' % dd] += 1
        print('LOC%d_FAIL' % dd, sorted(V), sorted(F), px, flush=True)
  for name, seq, runs in (('th', th, [s['run'] for s in th] if th else None), ('px', px, px)):
    if seq is None:
      if h:
        st[name + '_fail'] += 1; print(name.upper() + '_NONE_HAM', sorted(V), sorted(F), flush=True)
      continue
    ok = simok(V, cells, F, runs)
    if ok:
      st[name + '_ok'] += 1
      k = len(runs); st[name + '_len'][k] = st[name + '_len'].get(k, 0) + 1
      if k >= 3: print(name.upper() + '_LONG', k, sorted(V), sorted(F), [list(r) for r in runs], flush=True)
    else:
      st[name + '_fail'] += 1; print(name.upper() + '_SIMFAIL', sorted(V), sorted(F), [list(r) for r in runs], flush=True)
print('final', st, flush=True)
