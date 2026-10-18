# SPDX-License-Identifier: CC0-1.0
# Markov test for the 'created' rule: along valid clean executions of enumerated paths,
# compare the inter sides of the dynamic chain of u_i in F_i with the static 'created'
# sides: sides on a cycle of Q + rung(u_i) but on none of Q, where Q is the light dual of F
# minus the sides of y_i and the lengthwise sides of u_i. Only sides away from earlier strips.
#
import sys, random, json
from collections import deque
args = sys.argv[1:]
exec(open('/home/z/claude/ulhc-lean/checks/clean_var.py').read().split("\nst = {}")[0])
sys.path.insert(0, '/home/z/claude/ulhc-lean/checks')
from parse import split_top
def dyn_chain_sides(V, cells, Fi, u):
  cl = classes(V, Fi)
  seen = {u}; dq = deque([u]); out = set()
  while dq:
    c = dq.popleft()
    for d in SIDES:
      e = side(c, d)
      if e in Fi or cl[e[0]] == cl[e[1]]: continue
      out.add(e)
      n = nb(c, d)
      if n in cells and n not in seen: seen.add(n); dq.append(n)
  return out
def static_created(cells, F, run):
  u = run[-1]; s = strip_dir(run); y = run[0]
  extra = {side(u, LATA[s]), side(u, LATB[s])}
  banned = {side(y, d) for d in SIDES} | {side(u, s), side(u, OPP[s])}
  Dg = light_graph(cells, F, extra, banned); D0 = light_graph(cells, F, set(), banned)
  out = set()
  for c in cells:
    for d in SIDES:
      e = side(c, d)
      if (e in F and e not in extra) or e in banned: continue
      if in_cycle(Dg, c, d) and not in_cycle(D0, c, d): out.add(e)
  return out
st = {}
def bump(k): st[k] = st.get(k, 0) + 1
def study(V, F):
  G = ph.induced(V); cells = ph.unit_cells(G)
  n0 = ncomp(V, F)
  cands = candidates(V, cells, F); pr = set(proper(V, cells, F))
  memo = {}
  def go(path, Fi):
    x = path[-1]
    if len(x[0]) % 2 == 1 or len(path) >= 4: return
    near = set()
    for q, _ in path[:-1]:
      for c in q:
        for dx in (-1, 0, 1):
          for dy in (-1, 0, 1): near.add((c[0] + dx, c[1] + dy))
    if len(path) >= 1:
      dyn = {e for e in dyn_chain_sides(V, cells, Fi, x[0][-1]) if e[0] not in near and e[1] not in near}
      sta = {e for e in static_created(cells, F, x[0]) if e[0] not in near and e[1] not in near}
      bump('cmp%d' % len(path)); bump('L%d_' % len(path) + 'same' if dyn == sta else ('dyn_sub' if dyn < sta else ('sta_sub' if sta < dyn else 'differ')))
    if x not in memo: memo[x] = tl_succ_all(V, cells, F, cands, x)
    for z in memo[x]:
      if len(z[0]) % 2 == 1: continue
      if z[0] not in set(proper(V, cells, Fi)): continue
      F2 = apply(Fi, [list(z[0])]); cl = classes(V, F2)
      if ncomp(V, F2) != n0 or any(type3(F2, cl, c) for c in cells): continue
      path.append(z); go(path, F2); path.pop()
  for x in cands:
    if x[1] is None and x[0] in pr and len(x[0]) % 2 == 0:
      F1 = apply(F, [list(x[0])]); cl = classes(V, F1)
      if ncomp(V, F1) != n0: continue
      go([x], F1)
for fn in ['/home/z/claude/runs/2026-10-09/long_climb.txt', '/home/z/claude/runs/2026-10-09/long_climb_run1.txt']:
  for line in open(fn):
    if line.startswith('LONG'):
      q = split_top(line); study(set(map(tuple, q[4])), {tuple(map(tuple, e)) for e in q[5]})
print('long', st, flush=True)
rng = random.Random(int(args[0]))
for t in range(int(args[1])):
  W = rng.choice([10, 12, 14]); Hh = rng.choice([10, 12, 14])
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
  study(V, F)
  if t % 1000 == 0: print('progress', t, st, flush=True)
print('final', st)
