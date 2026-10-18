# SPDX-License-Identifier: CC0-1.0
# Completeness and soundness of the execute-and-stop algorithm with a given link variant:
# on stuck Hamiltonian instances, does a path exist, and does executing it (stopping at a
# Type III cell or a count drop) merge two cycles?
#
import sys, random, json
args = sys.argv[1:]
exec(open('/home/z/claude/ulhc-lean/checks/clean_var.py').read().split("\nst = {}")[0])
sys.path.insert(0, '/home/z/claude/ulhc-lean/checks')
from ham_ilp import ham_cycle
from parse import split_top
def exec_stop(V, cells, F, runs):
  n0 = ncomp(V, F); Fi = F
  for r in runs:
    cl = classes(V, Fi)
    t3 = [c for c in cells if type3(Fi, cl, c)]
    if t3: Fi = apply(Fi, [[t3[0]]]); return is_factor(V, Fi) and ncomp(V, Fi) < n0
    if r not in set(proper(V, cells, Fi)): return False
    Fi = apply(Fi, [list(r)])
    if ncomp(V, Fi) < n0: return is_factor(V, Fi)
  return False
st = {}
def bump(k): st[k] = st.get(k, 0) + 1
def check(V, F, tag):
  G = ph.induced(V); cells = ph.unit_cells(G)
  p = var_search(V, cells, F)
  if p is None:
    if ham_cycle(V) is not None:
      bump(tag + '_NONE_HAM'); print('NONE_HAM', tag, json.dumps([sorted(V), sorted(F)]), flush=True)
    else: bump(tag + '_none_nonham')
    return
  if exec_stop(V, cells, F, p): bump(tag + '_ok'); bump(tag + '_len%d' % len(p))
  else: bump(tag + '_EXEC_FAIL'); print('EXEC_FAIL', tag, json.dumps([sorted(V), sorted(F), [list(map(list, r)) for r in p]]), flush=True)
for fn in ['/home/z/claude/runs/2026-10-09/long_climb.txt', '/home/z/claude/runs/2026-10-09/long_climb_run1.txt']:
  for line in open(fn):
    if line.startswith('LONG'):
      q = split_top(line); check(set(map(tuple, q[4])), {tuple(map(tuple, e)) for e in q[5]}, 'long')
print('long done', st, flush=True)
rng = random.Random(int(args[0]))
for t in range(int(args[1])):
  if t % 2000 == 0: print('progress', t, st, flush=True)
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
  if ncomp(V, F) < 2: continue
  check(V, F, 'rand')
print('final', st)
