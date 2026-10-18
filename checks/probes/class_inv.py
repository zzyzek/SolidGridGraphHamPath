# SPDX-License-Identifier: CC0-1.0
# Class invariant test on clean V2 executions with disjoint strips:
# H1: partition(F_i) = partition(F xor a_i) joined with the merges of the start corners of
#     a_1 and of a_i (back1/front1 of the start cell, read in F).
#
import sys, random
from collections import deque
args = sys.argv[1:]
exec(open('/home/z/claude/ulhc-lean/checks/chain_avoid.py').read().split("st = {}")[0])
def join(V, cl, pairs):
  uf = UF(V)
  for v in V: uf.u(v, cl[v])
  for a, b in pairs: uf.u(a, b)
  return {v: uf.f(v) for v in V}
def same_partition(V, c1, c2):
  m = {}
  for v in V:
    k = (c1[v], c2[v])
    m.setdefault(c1[v], set()).add(c2[v])
  if any(len(s) > 1 for s in m.values()): return False
  m2 = {}
  for v in V: m2.setdefault(c2[v], set()).add(c1[v])
  return all(len(s) == 1 for s in m2.values())
st = {}
def bump(k): st[k] = st.get(k, 0) + 1
rng = random.Random(int(args[0]))
for t in range(int(args[1])):
  if t % 5000 == 0: print('progress', t, st, flush=True)
  W = rng.choice([8, 10, 12]); Hh = rng.choice([8, 10, 12])
  V = set(E3['grow_shape'](W, Hh, rng))
  Fs = E3['two_factor'](V, rng)
  if Fs is None: continue
  F = {tuple(sorted(e)) for e in Fs}
  G = ph.induced(V); cells = ph.unit_cells(G)
  F = settle(V, cells, F)
  n0 = ncomp(V, F)
  if n0 < 2: continue
  seq = []; Fi = F; anchor = None
  for step in range(6):
    pr = [r for r in proper(V, cells, Fi) if len(r) % 2 == 0]
    if anchor is not None:
      ch = chain(V, cells, Fi, anchor); pr = [r for r in pr if r[0] in ch]
    used = set(c for q in seq for c in q)
    pr = [r for r in pr if not (set(r) & used)]
    if not pr: break
    r = rng.choice(pr)
    F2 = apply(Fi, [list(r)])
    cl2 = classes(V, F2)
    if ncomp(V, F2) != n0 or any(type3(F2, cl2, c) for c in cells): break
    seq.append(r); Fi = F2; anchor = r[-1]
    if len(seq) >= 2:
      def startpair(q):
        c = q[0]; s = next(d for d in SIDES if nb(c, d) == q[1])
        b = side(c, OPP[s]); f = side(c, s)
        return [(b[0], f[0]), (b[0], f[1])]
      Fa = apply(F, [list(r)])
      Q = join(V, classes(V, Fa), [startpair(seq[0])[0]] + [startpair(seq[0])[1]] + startpair(r))
      bump('H1_ok' if same_partition(V, classes(V, Fi), Q) else 'H1_fail')
print('final', st)
