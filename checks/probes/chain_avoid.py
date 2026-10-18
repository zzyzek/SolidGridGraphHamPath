# SPDX-License-Identifier: CC0-1.0
# Random V2 sequences (no Type III; each strip a random proper strip starting on the chain
# created by the previous one). After each step, does the created chain contain the start
# or end cell of an earlier strip? (Thesis Lemmas 7.2 and 8.1.)
#
import sys, random
from collections import deque
args = sys.argv[1:]
exec(open('/home/z/claude/ulhc-lean/checks/tl_algo.py').read())
src = open('/home/z/claude/ulhc-lean/checks/depth2_climb.py').read()
exec("def settle" + src.split("def settle")[1].split("best = None")[0])
E3 = {}
exec(open('/home/z/claude/ulhc-lean/checks/l57_check.py').read().split('def run(')[0], E3)
_e = open('/home/z/claude/ulhc-lean/checks/even_t3.py').read()
exec('import random\nimport networkx as nx\ndef grow_shape' + _e.split('def grow_shape')[1].rsplit('def run(', 1)[0], E3)

def chain(V, cells, F, u):
  cl = classes(V, F)
  seen = {u}; dq = deque([u])
  while dq:
    c = dq.popleft()
    for d in SIDES:
      e = side(c, d)
      if e in F or cl[e[0]] == cl[e[1]]: continue
      n = nb(c, d)
      if n in cells and n not in seen: seen.add(n); dq.append(n)
  return seen

st = {}
def bump(k): st[k] = st.get(k, 0) + 1
rng = random.Random(int(args[0]))
for t in range(int(args[1])):
  W = rng.choice([8, 10, 12]); Hh = rng.choice([8, 10, 12])
  V = set(E3['grow_shape'](W, Hh, rng))
  Fs = E3['two_factor'](V, rng)
  if Fs is None: continue
  F = {tuple(sorted(e)) for e in Fs}
  G = ph.induced(V); cells = ph.unit_cells(G)
  F = settle(V, cells, F)
  if ncomp(V, F) < 2: continue
  n0 = ncomp(V, F)
  seq = []; Fi = F; anchor = None
  for step in range(8):
    cl = classes(V, Fi)
    if any(type3(Fi, cl, c) for c in cells): break
    pr = [r for r in proper(V, cells, Fi) if len(r) % 2 == 0]
    if anchor is not None:
      ch = chain(V, cells, Fi, anchor)
      pr = [r for r in pr if r[0] in ch]
    used = set(c for q in seq for c in q)
    pr = [r for r in pr if not (set(r) & used)]
    if not pr: break
    r = rng.choice(pr)
    Fi2 = apply(Fi, [list(r)])
    if ncomp(V, Fi2) != n0: bump('count_changed'); break
    seq.append(r); Fi = Fi2; anchor = r[-1]
    ch = chain(V, cells, Fi, anchor)
    for j, rj in enumerate(seq[:-1]):
      if rj[0] in ch: bump('chain_has_earlier_start'); print('START', sorted(V), sorted(F), seq, j, flush=True)
      if rj[-1] in ch:
        bump('chain_has_earlier_end'); print('END', sorted(V), sorted(F), seq, j, flush=True)
    bump('steps')
  if t % 2000 == 0: print('progress', t, st, flush=True)
print(st)
