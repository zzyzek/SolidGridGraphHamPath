# SPDX-License-Identifier: CC0-1.0
# Collect stuck 2-factors that need sequences of 3 or more strips (no 2-strip escape),
# using the broad sampler of checks/even_t3.py (random solid shapes, min-cost-flow
# 2-factors) plus random alternating-cell walks. Each hit is checked against the Ch. 8
# algorithm (checks/ul_algo.py): it must find a sequence that merges two cycles.
#
# Usage: python3 checks/long_gen.py SEED TRIALS W,H,..  > out
#
import random, sys
sys.path.insert(0, '/home/z/claude/ulhc-lean/checks')
from ham_ilp import ham_cycle
args = sys.argv[1:]
sys.argv = sys.argv[:1] + ['0', '0', '4']
exec(open('/home/z/claude/ulhc-lean/checks/ul_algo.py').read().split("ap = argparse")[0])
src = open('/home/z/claude/ulhc-lean/checks/depth2_climb.py').read()
exec("def settle" + src.split("def settle")[1].split("best = None")[0])
E3 = {}
exec(open('/home/z/claude/ulhc-lean/checks/l57_check.py').read().split('def run(')[0], E3)
_e = open('/home/z/claude/ulhc-lean/checks/even_t3.py').read()
exec('import random\nimport networkx as nx\ndef grow_shape' + _e.split('def grow_shape')[1].rsplit('def run(', 1)[0], E3)

seed, trials = int(args[0]), int(args[1])
sizes = [int(x) for x in args[2].split(',')]
rng = random.Random(seed)
st = dict(stuck=0, hits=0, algo_ok=0, algo_fail=0, nonham_skip=0)
for t in range(trials):
  W = rng.choice(sizes); Hh = rng.choice(sizes)
  Vs = E3['grow_shape'](W, Hh, rng)
  Fs = E3['two_factor'](Vs, rng)
  if Fs is None: continue
  V = set(Vs); F = {tuple(sorted(e)) for e in Fs}
  G = ph.induced(V); cells = ph.unit_cells(G)
  for _ in range(rng.randint(0, 50)):
    alts = [c for c in cells if is_alt(F, c)]
    if not alts: break
    F = apply(F, [[rng.choice(alts)]])
  if t % 2000 == 0: print('progress', t, st, flush=True)
  F = settle(V, cells, F)
  sc = escapes(V, cells, F)
  if sc is None: continue
  st['stuck'] += 1
  if sc > 0: continue
  st['hits'] += 1
  seq = find_seq(V, cells, F)
  if seq is None:
    h = ham_cycle(V) is not None
    if not h: st['nonham_skip'] += 1; continue
    st['algo_fail'] += 1
    print('ALGO_NONE', h, sorted(V), sorted(F), flush=True); continue
  F2 = apply(F, [s['run'] for s in seq])
  if is_factor(V, F2) and ncomp(V, F2) == ncomp(V, F) - 1:
    st['algo_ok'] += 1
    print('LONG', len(seq), sorted(V), sorted(F), [(s['kind'], s['run']) for s in seq], flush=True)
  else:
    st['algo_fail'] += 1
    print('ALGO_BAD', sorted(V), sorted(F), [(s['kind'], s['run']) for s in seq], flush=True)

print('final', st)
