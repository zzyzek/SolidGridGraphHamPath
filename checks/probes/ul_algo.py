# SPDX-License-Identifier: CC0-1.0
# Probe: the thesis Ch. 8 algorithm (static strip sequences via the auxiliary graph H),
# as read from the thesis, against a brute-force Hamiltonicity oracle.
#
# Usage: python3 checks/ul_algo.py SEED TRIALS NCELLS[,NCELLS..] [--w area|dist] [--avoid]
#
import random, sys, heapq, argparse
from collections import deque
sys.path.insert(0, '/home/z/claude/pathfactor/code')
import pfharness as ph

SIDES = 'btlr'
OPP = {'b': 't', 't': 'b', 'l': 'r', 'r': 'l'}
LATA = {'t': 'l', 'b': 'l', 'r': 'b', 'l': 'b'}
LATB = {'t': 'r', 'b': 'r', 'r': 't', 'l': 't'}
STEP = {'b': (0, -1), 't': (0, 1), 'l': (-1, 0), 'r': (1, 0)}

def side(c, d):
  x, y = c
  if d == 'b': return ph.ekey((x, y), (x + 1, y))
  if d == 't': return ph.ekey((x, y + 1), (x + 1, y + 1))
  if d == 'l': return ph.ekey((x, y), (x, y + 1))
  return ph.ekey((x + 1, y), (x + 1, y + 1))

def nb(c, d):
  return (c[0] + STEP[d][0], c[1] + STEP[d][1])

def cell_edges(c):
  return [side(c, d) for d in SIDES]

class UF:
  def __init__(s, V): s.p = {v: v for v in V}
  def f(s, v):
    while s.p[v] != v:
      s.p[v] = s.p[s.p[v]]; v = s.p[v]
    return v
  def u(s, a, b): s.p[s.f(a)] = s.f(b)

def classes(V, F):
  uf = UF(V)
  for (a, b) in F: uf.u(a, b)
  return {v: uf.f(v) for v in V}

def dark(F, c):
  return {d for d in SIDES if side(c, d) in F}

def is_alt(F, c):
  D = dark(F, c)
  return D == {'b', 't'} or D == {'l', 'r'}

def corners(c, d):
  # Ends of side d of cell c.
  #
  return side(c, d)

def type3(F, cl, c):
  D = dark(F, c)
  if not (D == {'b', 't'} or D == {'l', 'r'}): return False
  a, b = list(D)
  return cl[side(c, a)[0]] != cl[side(c, b)[0]]

def strip_from(cells, F, c, s, toggle=frozenset()):
  # Walk from c in direction s until the first alternating cell; check the strip
  # pattern (with edges in `toggle` flipped). Returns the cell list or None.
  #
  Fe = lambda e: (e in F) != (e in toggle)
  if not Fe(side(c, OPP[s])): return None
  run = [c]
  j = 0
  while True:
    cj = run[-1]
    lat = (Fe(side(cj, LATA[s])), Fe(side(cj, LATB[s])))
    fr = Fe(side(cj, s))
    if j >= 1 and lat[0] == lat[1] and lat[0] != fr and \
       Fe(side(cj, OPP[s])) == fr:
      # alternating; check the end pattern
      if j % 2 == 1 and lat == (True, True) and not fr: return run
      if j % 2 == 0 and lat == (False, False) and fr: return run
      return None
    # interior pattern
    if lat != ((j % 2 == 1), (j % 2 == 1)): return None
    if fr != (j % 2 == 1): return None
    n = nb(cj, s)
    if n not in cells: return None
    run.append(n); j += 1

def apply(F, runs):
  F = set(F)
  for run in runs:
    for c in run:
      for e in cell_edges(c):
        F ^= {e}
  return F

def is_factor(V, F):
  deg = {v: 0 for v in V}
  for (a, b) in F:
    if a not in V or b not in V: return False
    deg[a] += 1; deg[b] += 1
  return all(d == 2 for d in deg.values())

def ncomp(V, F):
  return len(set(classes(V, F).values()))

def dual_sp(cells, F, a, b, avoid=None):
  # BFS shortest path in the dual (cells + 'OUT'), across light edges.
  #
  def nbrs(c):
    if c == 'OUT':
      for x in cells:
        for d in SIDES:
          if nb(x, d) not in cells and side(x, d) not in F: yield x; break
      return
    for d in SIDES:
      if side(c, d) in F: continue
      n = nb(c, d)
      yield n if n in cells else 'OUT'
  prev = {a: None}; q = deque([a])
  while q:
    x = q.popleft()
    if x == b: break
    for y in nbrs(x):
      if y == avoid or y in prev: continue
      prev[y] = x; q.append(y)
  if b not in prev: return None
  p = [b]
  while prev[p[-1]] is not None: p.append(prev[p[-1]])
  return p[::-1]

EXCL = True
def find_seq(V, cells, F, wmode='area', avoid=False):
  cl = classes(V, F)
  strips = []
  # Candidate strips from Type I cells.
  #
  for c in cells:
    D = dark(F, c)
    if len(D) == 1:
      d = next(iter(D)); s = OPP[d]
      run = strip_from(cells, F, c, s)
      if run: strips.append(dict(kind='B', c=c, s=s, run=run))
    if is_alt(F, c):
      strips.append(dict(kind='B', c=c, s=None, run=[c]))
  # Chain strips.
  #
  for c in cells:
    D = dark(F, c)
    if len(D) == 2 and not is_alt(F, c):
      for d1 in D:
        p = nb(c, d1)
        if p in cells and is_alt(F, p):
          d2 = next(iter(D - {d1}))
          s = OPP[d2]
          run = strip_from(cells, F, c, s, toggle=frozenset({side(c, d1)}))
          if run: strips.append(dict(kind='C', c=c, s=s, run=run, partner=p))
    if len(D) == 3:
      L = next(d for d in SIDES if d not in D)
      p = nb(c, OPP[L])
      if p in cells and is_alt(F, p):
        strips.append(dict(kind='C', c=c, s=None, run=[c], partner=p))
  for i, st in enumerate(strips):
    st['id'] = i
    st['odd'] = len(st['run']) % 2 == 1
    st['w'] = len(st['run']) if wmode == 'area' else max(1, len(st['run']) - 1)
  # Links from even ends.
  #
  links = {}
  for st in strips:
    if st['odd']: continue
    u = st['run'][-1]; s = st['s']
    c1 = nb(u, LATA[s]); c2 = nb(u, LATB[s])
    c1 = c1 if c1 in cells else 'OUT'
    c2 = c2 if c2 in cells else 'OUT'
    p = dual_sp(cells, F, c1, c2, avoid=(u if avoid else None))
    if p is None: continue
    on = set(p)
    L = []
    for t in strips:
      if t['kind'] == 'B' and t['c'] in on and not (EXCL and t['c'] in (c1, c2)): L.append(t['id'])
      if t['kind'] == 'C' and t['partner'] == u and t['c'] in (c1, c2): L.append(t['id'])
    links[st['id']] = L
  # Sources: begin strips whose start cell separates in F.
  #
  def sep(st):
    if st['s'] is None:
      return type3(F, cl, st['c'])
    c, s = st['c'], st['s']
    b = side(c, OPP[s])
    f = side(c, s)
    return cl[b[0]] != cl[f[0]] or cl[b[0]] != cl[f[1]]
  dist = {}; prev = {}; pq = []
  for st in strips:
    if st['kind'] == 'B' and sep(st):
      dist[st['id']] = st['w']; prev[st['id']] = None
      heapq.heappush(pq, (st['w'], st['id']))
  best = None
  while pq:
    dd, i = heapq.heappop(pq)
    if dd > dist[i]: continue
    if strips[i]['odd']:
      best = i; break
    for j in links.get(i, []):
      nd = dd + strips[j]['w']
      if nd < dist.get(j, 1 << 30):
        dist[j] = nd; prev[j] = i; heapq.heappush(pq, (nd, j))
  if best is None: return None
  seq = [best]
  while prev[seq[-1]] is not None: seq.append(prev[seq[-1]])
  return [strips[i] for i in seq[::-1]]

def rand_factor(V, rng):
  # 2-factor by min-cost flow with random costs (varied starting factors).
  #
  import networkx as nx
  D = nx.DiGraph()
  for v in V:
    if (v[0] + v[1]) % 2 == 0:
      D.add_edge('s', v, capacity=2, weight=0)
      for w in [(v[0]+1, v[1]), (v[0]-1, v[1]), (v[0], v[1]+1), (v[0], v[1]-1)]:
        if w in V: D.add_edge(v, w, capacity=1, weight=rng.randint(0, 100))
    else:
      D.add_edge(v, 't', capacity=2, weight=0)
  try:
    flow = nx.max_flow_min_cost(D, 's', 't')
  except Exception:
    return None
  F = set()
  for v in V:
    if (v[0] + v[1]) % 2 == 0:
      for w, f in flow[v].items():
        if f: F.add(ph.ekey(v, w))
  return F if is_factor(V, F) else None

def ham(G):
  v = min(G.nodes, key=lambda x: G.degree(x))
  a = next(iter(G[v]))
  try:
    return ph.ham_path_oracle(G, v, a, limit=2_000_000) is not None
  except TimeoutError:
    return None

def run(args):
  rng = random.Random(args.seed)
  sizes = [int(x) for x in args.ncells.split(',')]
  st = dict(inst=0, ham=0, nonham=0, timeout=0, found_ham=0, sound_fail=0, complete_fail=0,
            nonham_ok=0, seq_len={}, steps=0)
  exs = []
  for _ in range(args.trials):
    if args.gen == 'blocks':
      W = rng.choice(sizes); Hh = rng.choice(sizes)
      V, Fb = L57['random_2factor'](W, Hh, rng.randint(10, 400), rng)
      G = ph.induced(V)
      F0 = {tuple(sorted(e)) for e in Fb}
    else:
      G = ph.random_solid(rng.choice(sizes), rng)
      V = set(G.nodes)
      F0 = rand_factor(V, rng)
    cells = ph.unit_cells(G)
    if F0 is None: continue
    st['inst'] += 1
    h = True if args.gen == 'blocks' else ham(G)
    if h is None: st['timeout'] += 1; continue
    st['ham' if h else 'nonham'] += 1
    F = set(F0)
    ok = True
    while ncomp(V, F) > 1:
      cl = classes(V, F)
      t3 = [c for c in cells if type3(F, cl, c)]
      if t3:
        F = apply(F, [[t3[0]]]); continue
      seq = find_seq(V, cells, F, args.w, args.avoid)
      if seq is None:
        ok = False; break
      st['steps'] += 1
      k = len(seq); st['seq_len'][k] = st['seq_len'].get(k, 0) + 1
      for a, b in zip(seq, seq[1:]):
        u = a['run'][-1]; y = b['run'][0]
        dd = abs(u[0] - y[0]) + abs(u[1] - y[1])
        st.setdefault('link_dist', {})
        st['link_dist'][dd] = st['link_dist'].get(dd, 0) + 1
      if k >= 3 and len(exs) < 20:
        exs.append(('long', sorted(V), sorted(F), [(s['kind'], s['run']) for s in seq]))
      F2 = apply(F, [s['run'] for s in seq])
      if not (is_factor(V, F2) and ncomp(V, F2) == ncomp(V, F) - 1):
        st['sound_fail'] += 1
        exs.append(('sound', sorted(V), sorted(F), [(s['kind'], s['run']) for s in seq]))
        ok = False; break
      F = F2
    if ok:
      st['found_ham'] += 1
      if not h: st['complete_fail'] += 0
    elif h:
      if not any(e[0] == 'sound' and e[1] == sorted(V) for e in exs[-1:]):
        st['complete_fail'] += 1
        exs.append(('complete', sorted(V), sorted(F), None))
    else:
      st['nonham_ok'] += 1
  print(st)
  for e in exs[:20]: print(e)

ap = argparse.ArgumentParser()
ap.add_argument('seed', type=int); ap.add_argument('trials', type=int)
ap.add_argument('ncells'); ap.add_argument('--w', default='area')
ap.add_argument('--avoid', action='store_true')
ap.add_argument('--gen', default='eden')
L57 = {}
exec(open('/home/z/claude/ulhc-lean/checks/l57_check.py').read().split('def strips(')[0], L57)
run(ap.parse_args())
