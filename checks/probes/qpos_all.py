# SPDX-License-Identifier: CC0-1.0
# Completeness step for class CA (chain links anywhere, ChainOK at every link).
# G clean, s proper even, F = G xor s clean with >= 2 components, a = rev s.
# Q = minimum CA path of F. Classify: Q starts with a; else is s -> q a CA link of G, is s :: Q
# a CA path of G (every link of Q also a CA link of G), do later strips of Q touch a, and how
# q.n compares with a.n. Reports cases where s :: Q fails, and any G without a CA path.
#
# usage: comp_ca.py seed trials
#
import sys, random, json, heapq
myargs = sys.argv[1:]
sys.argv = [sys.argv[0], myargs[0], myargs[1], '0']
exec(open('/home/z/claude/ulhc-lean/checks/iter_exact.py').read().split("\nst = {}\ndef bump")[0])
from parse import split_top
st = {}
def bump(k): st[k] = st.get(k, 0) + 1
def cells_of_x(x): return [cellj(x[0], x[1], j) for j in range(x[2])]
def chain_ok(b, x):
  u = endc(b); us = set(csides(u)); L = {wside(u, WLA[b[1]]), wside(u, WLB[b[1]])}
  for j, q in enumerate(cells_of_x(x)):
    for e in csides(q):
      if e in us and (j != 0 or e not in L): return False
  return True
def ca_links(V, cells, G, clG, b, cache):
  return [z for z, ch in links(V, cells, G, clG, b, cache) if chain_ok(b, z)]
def min_path_ca(V, cells, G):
  clG = classes(V, G); cache = {}
  dist = {}; prev = {}; pq = []
  for x in strips_of(G, cells):
    l = lat1(x)
    if clG[l[0]] == clG[l[1]]: continue
    dist[x] = x[2]; prev[x] = None; heapq.heappush(pq, (x[2], x))
  memo = {}
  while pq:
    dd, x = heapq.heappop(pq)
    if dd > dist[x]: continue
    if x[2] % 2 == 1:
      seq = [x]
      while prev[seq[-1]] is not None: seq.append(prev[seq[-1]])
      return dd, seq[::-1]
    if x not in memo: memo[x] = ca_links(V, cells, G, clG, x, cache)
    for z in memo[x]:
      nd = dd + z[2]
      if nd < dist.get(z, 1 << 30):
        dist[z] = nd; prev[z] = x; heapq.heappush(pq, (nd, z))
  return None, None
def touches(x, Acells):
  A = set(e for q in Acells for e in csides(q))
  return any(e in A for q in cells_of_x(x) for e in csides(q))
SEEDS = []
for fn in ['/home/z/claude/runs/2026-10-09/long_climb.txt', '/home/z/claude/runs/2026-10-09/long_climb_run1.txt']:
  for line in open(fn):
    if line.startswith('LONG'):
      q = split_top(line); SEEDS.append((set(map(tuple, q[4])), {tuple(map(tuple, e)) for e in q[5]}))
OPPS = {'t': 'b', 'b': 't', 'l': 'r', 'r': 'l'}

def qkey(q, s, Sc):
  d = OPPS[s[1]]; e = Sc[-1]
  rel = {d: 'along', OPPS[d]: 'back', WLA[d]: 'latA', WLB[d]: 'latB'}[q[1]]
  st_ = WSTEP[d]; la = WSTEP[WLA[d]]
  out = []
  A = {}
  for i in range(s[2]): A[cellj(e, d, i)] = i
  for j, c in enumerate(cells_of_x(q)):
    dx, dy = c[0] - e[0], c[1] - e[1]
    i = dx * st_[0] + dy * st_[1]; l = dx * la[0] + dy * la[1]
    if abs(l) <= 1 and -1 <= i <= s[2] and (l == 0 or 0 <= i < s[2]):
      ii = 'S' if i == 0 else ('E' if i == s[2]-1 else ('Y' if i == s[2] else ('P' if i == -1 else 'M')))
      out.append('%s%s%d@%d' % (ii, {0:'',1:'+',-1:'-'}[l], 0, j) if False else '%s%s@%s' % (ii, {0:'o',1:'A',-1:'B'}[l], 'last' if j == q[2]-1 and j > 0 else ('0' if j == 0 else 'k')))
  return rel + ('_odd' if q[2] % 2 else '_even') + ':' + ','.join(out)
rng = random.Random(int(myargs[0]))
for t in range(int(myargs[1])):
  if t % 100 == 0: print('progress', t, st, flush=True)
  V, G = rng.choice(SEEDS); V = set(V); G = set(G)
  cells = set(ph.unit_cells(ph.induced(V)))
  for _ in range(rng.randint(0, 15)):
    alts = [c for c in cells if is_alt(G, c)]
    if not alts: break
    G = apply(G, [[rng.choice(alts)]])
  G = settle(V, cells, G)
  if ncomp(V, G) < 2: continue
  clG = classes(V, G)
  if any(type3(G, clG, c) for c in cells): continue
  ss = [x for x in strips_of(G, cells) if x[2] % 2 == 0 and clG[lat1(x)[0]] != clG[lat1(x)[1]]]
  rng.shuffle(ss)
  for s in ss[:3]:
    Sc = cells_of_x(s)
    F = apply(G, [Sc]); clF = classes(V, F)
    if any(type3(F, clF, c) for c in cells): continue
    if ncomp(V, F) < 2: continue
    bump('situations')
    ra = (Sc[-1], OPPS[s[1]], s[2])
    for q in strips_of(F, cells):
      l = lat1(q)
      if clF[l[0]] == clF[l[1]]: continue
      if tuple(q) == ra: continue
      if not touches(q, Sc): continue
      bump(qkey(q, s, Sc))
print('final', st)
