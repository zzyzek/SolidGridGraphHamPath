# SPDX-License-Identifier: CC0-1.0
# Enumerate pairwise-exact paths (a1 proper in F, a(i+1) proper in F xor a_i) up to a weight
# bound and simulate them. For invalid ones record the first failing step and the cause:
# 'pattern' (not a strip of the current factor) or 'sep' (strip, start not separated).
# Also record whether the failure involves a non-consecutive earlier strip touching it.
#
import sys, random
args = sys.argv[1:]
exec(open('/home/z/claude/ulhc-lean/checks/px_algo.py').read())
sys.path.insert(0, '/home/z/claude/ulhc-lean/checks')
from parse import split_top

def strip_pattern_ok(V, cells, F, r):
  if len(r) == 1:
    return is_alt(F, r[0])
  c = r[0]; s = next(d for d in SIDES if nb(c, d) == r[1])
  run = strip_from(cells, F, c, s)
  return run is not None and tuple(run) == tuple(r)

def touches(r1, r2):
  A = set(r1)
  for c in r2:
    if c in A: return True
    for d in SIDES:
      if nb(c, d) in A: return True
  return False

def enum(V, cells, F, wmax, lmax):
  out = []
  src = proper(V, cells, F)
  memo = {}
  def succ(r):
    if r not in memo: memo[r] = proper(V, cells, apply(F, [list(r)]))
    return memo[r]
  def go(path, w):
    last = path[-1]
    if len(last) % 2 == 1:
      out.append(list(path)); return
    if len(path) >= lmax: return
    for r2 in succ(last):
      if w + len(r2) <= wmax:
        path.append(r2); go(path, w + len(r2)); path.pop()
  for r in src:
    if len(r) <= wmax: go([r], len(r))
  return out

st = {}
def bump(k): st[k] = st.get(k, 0) + 1
lines = [l for l in open(args[0]) if l.startswith('LONG')]
for line in lines[:int(args[1])]:
  parts = split_top(line)
  Vl, Fl = parts[4], parts[5]
  V = set(map(tuple, Vl)); F = {tuple(map(tuple, e)) for e in Fl}
  G = ph.induced(V); cells = ph.unit_cells(G)
  best = px_search(V, cells, F)
  wmin = sum(len(r) for r in best)
  for p in enum(V, cells, F, wmin + int(args[2]), 6):
    Fi = F; bad = None
    for i, r in enumerate(p):
      if not strip_pattern_ok(V, cells, Fi, r): bad = (i, 'pattern'); break
      if r not in proper(V, cells, Fi): bad = (i, 'sep'); break
      Fi = apply(Fi, [list(r)])
    w = sum(len(r) for r in p)
    if bad is None:
      bump('valid_w%+d' % (w - wmin))
    else:
      i, why = bad
      far = any(touches(p[j], p[i]) for j in range(i - 1))
      bump('bad_%s_far%s_w%+d' % (why, far, w - wmin))
      if why == 'sep' and not far: print('SEP_NOT_TOUCHING', p, i, flush=True)
print(sorted(st.items()))
