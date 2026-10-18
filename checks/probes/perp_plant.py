# SPDX-License-Identifier: CC0-1.0
# Plant an even strip a (vertical) and a reverse-parallel strip z alongside it (sharing
# lateral sides), complete to a 2-factor by min-cost flow with forced edges, and test whether
# z's start is created (cr2) by the end cell of some even strip b far from a.
#
import sys, random, json
import networkx as nx
args = sys.argv[1:]
exec(open("/home/z/claude/ulhc-lean/checks/iter_l1.py").read().split("\nst = {}\ndef bump")[0])
sys.path.insert(0, '/home/z/claude/ulhc-lean/checks')
from window import pattern
def forced_factor(V, req, rng):
  D = nx.DiGraph()
  for v in V:
    if (v[0] + v[1]) % 2 == 0:
      D.add_edge('s', v, capacity=2, weight=0)
      for w in [(v[0]+1, v[1]), (v[0]-1, v[1]), (v[0], v[1]+1), (v[0], v[1]-1)]:
        if w in V:
          e = ph.ekey(v, w)
          wt = rng.randint(0, 100)
          if e in req: wt = -100000 if req[e] else 100000
          D.add_edge(v, w, capacity=1, weight=wt)
    else:
      D.add_edge(v, 't', capacity=2, weight=0)
  try: flow = nx.max_flow_min_cost(D, 's', 't')
  except Exception: return None
  F = set()
  for v in V:
    if (v[0] + v[1]) % 2 == 0:
      for w, f in flow[v].items():
        if f: F.add(ph.ekey(v, w))
  if not is_factor(V, F): return None
  if any((e in F) != val for e, val in req.items() if e[0] in V and e[1] in V): return None
  return F
st = {}
def bump(k): st[k] = st.get(k, 0) + 1
rng = random.Random(int(args[0]))
for t in range(int(args[1])):
  if t % 200 == 0: print('progress', t, st, flush=True)
  W = rng.choice([12, 14, 16]); Hh = rng.choice([12, 14, 16])
  V = set(E3['grow_shape'](W, Hh, rng))
  Gr = ph.induced(V); cells = ph.unit_cells(Gr)
  cl = sorted(cells)
  base = rng.choice(cl)
  an = rng.choice([2, 4, 6])
  zn = rng.choice([1, 2, 3, 4, 5])
  a = (base, 't', an)
  kind = rng.choice(['under', 'end'])
  if kind == 'under':
    # z horizontal at row -1 passing under a's start, with index i under c_0
    zdir = rng.choice(['l', 'r']); i = rng.randrange(zn)
    off = -i if zdir == 'r' else i
    zc = (base[0] + off, base[1] - 1)
  else:
    # z horizontal at row an (beyond a's end) or beside the end cell
    zdir = rng.choice(['l', 'r']); i = rng.randrange(zn)
    off = -i if zdir == 'r' else i
    row = rng.choice([an, an - 1])
    zc = (base[0] + off, base[1] + row)
  z = (zc, zdir, zn)
  from window import cells_of
  Acells = cells_of(*a); Zcells = cells_of(*z)
  if not all(c in cells for c in Acells + Zcells): continue
  req = {}
  okp = True
  for e, v in list(pattern(*a).items()) + list(pattern(*z).items()):
    if e in req and req[e] != v: okp = False
    req[e] = v
  if not okp: bump('pattern_conflict'); continue
  G = forced_factor(V, req, rng)
  if G is None: bump('no_factor'); continue
  bump('planted')
  PL = set(Acells) | set(Zcells)
  near = {(c[0] + dx, c[1] + dy) for c in PL for dx in (-1, 0, 1) for dy in (-1, 0, 1)}
  for _ in range(200):
    clG = classes(V, G)
    t3 = [c for c in cells if type3(G, clG, c)]
    if not t3: break
    far3 = [c for c in t3 if c not in near]
    if not far3: break
    G = apply(G, [[far3[0]]])
  clG = classes(V, G)
  if any(type3(G, clG, c) for c in cells): bump('t3_near_pattern'); continue
  if ncomp(V, G) < 2: bump('merged_all'); continue
  # z's start pair (lat1 in z's frame)
  l = side(zc, LATA[zdir])
  if clG[l[0]] != clG[l[1]]: bump('z_start_separated'); continue
  cands = [x for x in candidates(V, cells, G) if x[1] is None]
  Aset = set(Acells)
  far = [x for x in cands if len(x[0]) % 2 == 0 and not any((c[0] + dx, c[1] + dy) in Aset for c in x[0] for dx in (-1, 0, 1) for dy in (-1, 0, 1))]
  zr = tuple(Zcells)
  created = False
  for b in far:
    u = b[0][-1]
    if not is_alt(G, u): continue
    Gu = apply(G, [[u]]); clu = classes(V, Gu)
    if clu[l[0]] != clu[l[1]]:
      created = True
      # is a proper with G clean and G xor a clean?
      ap = tuple(Acells) in set(proper(V, cells, G))
      t3G = any(type3(G, clG, c) for c in cells)
      G1 = apply(G, [list(Acells)]); cl1 = classes(V, G1)
      clean1 = ncomp(V, G1) == ncomp(V, G) and not any(type3(G1, cl1, c) for c in cells)
      bump('%s_CREATED_proper%s_cleanG%s_cleanG1%s' % (kind, ap, not t3G, clean1))
      if ap and not t3G and clean1:
        print('NL_CANDIDATE', json.dumps([sorted(V), sorted(G), list(map(list, Acells)), list(map(list, b[0])), list(map(list, Zcells))]), flush=True)
      break
  if not created: bump('not_created')
print('final', st)
