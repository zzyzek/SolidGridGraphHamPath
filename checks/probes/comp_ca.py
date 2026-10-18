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
    dF, Q = min_path_ca(V, cells, F)
    if Q is None: bump('F_NO_PATH'); continue
    ra = (Sc[-1], OPPS[s[1]], s[2])
    if tuple(Q[0]) == ra: bump('q_is_rev'); continue
    q = Q[0]
    bump('q_touches' if touches(q, Sc) else 'q_far')
    # q's start in a's frame: a starts at e = Sc[-1], direction d = OPPS[s[1]]
    d = OPPS[s[1]]; e = Sc[-1]
    dx, dy = q[0][0] - e[0], q[0][1] - e[1]
    st_ = WSTEP[d]; la = WSTEP[WLA[d]]
    i = dx * st_[0] + dy * st_[1]; l = dx * la[0] + dy * la[1]
    rel = {d: 'along', OPPS[d]: 'back', WLA[d]: 'latA', WLB[d]: 'latB'}[q[1]]
    ii = 'i%d' % i if i <= 0 else ('end' if i == s[2] - 1 else ('beyond' if i >= s[2] else 'mid'))
    bump('qpos_%s_l%d_%s_n%s' % (ii, l, rel, 'odd' if q[2] % 2 else 'even'))
    bump('qn_ge_an+1' if q[2] >= s[2] + 1 else 'qn_le_an')
    cacheG = {}
    ok1 = tuple(q) in [tuple(z) for z in ca_links(V, cells, G, clG, tuple(s), cacheG)]
    okr = all(tuple(Q[i + 1]) in [tuple(z) for z in ca_links(V, cells, G, clG, tuple(Q[i]), cacheG)]
              for i in range(len(Q) - 1))
    later = any(touches(x, Sc) for x in Q[1:])
    bump('later_touch' if later else 'later_far')
    bump('sQ_' + ('link' if ok1 else 'nolink') + '_' + ('rest_ok' if okr else 'rest_bad'))
    if not (ok1 and okr):
      print('SQFAIL', json.dumps([sorted(V), sorted(G), Sc, Q, ok1, okr]), flush=True)
    dG, P = min_path_ca(V, cells, G)
    if P is None:
      bump('G_NO_PATH'); print('GNOPATH', json.dumps([sorted(V), sorted(G), Sc]), flush=True)
print('final', st)
