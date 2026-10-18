# SPDX-License-Identifier: CC0-1.0
# Graft an overlap/near configuration into a natural clean setting: take a proper clean even
# strip a of a settled factor G, force the pattern of a strip z (kind O2: odd, horizontal,
# ending at a's end cell; O3: the end cell as a single horizontal strip), re-solve the factor by
# min-cost flow staying as close to G as possible, and test (a proper, G' and G' xor a clean)
# and whether z's start is created by the end cell of an even strip far from a.
#
import sys, random, json
import networkx as nx
myargs = sys.argv[1:]
sys.argv = [sys.argv[0], myargs[0], myargs[1], '0', 'cr2l1']
exec(open("/home/z/claude/ulhc-lean/checks/iter_l1.py").read().split("\nst = {}\ndef bump")[0])
sys.path.insert(0, '/home/z/claude/ulhc-lean/checks')
from window import pattern, cells_of, side as wside, LATA as WLA
from parse import split_top
import ast
st = {}
def bump(k): st[k] = st.get(k, 0) + 1
def near_factor(V, G, req):
  D = nx.DiGraph()
  for v in V:
    if (v[0] + v[1]) % 2 == 0:
      D.add_edge('s', v, capacity=2, weight=0)
      for w in [(v[0]+1, v[1]), (v[0]-1, v[1]), (v[0], v[1]+1), (v[0], v[1]-1)]:
        if w in V:
          e = ph.ekey(v, w)
          wt = -1 if e in G else 1
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
SEEDS = []
for fn in ['/home/z/claude/runs/2026-10-09/long_climb.txt', '/home/z/claude/runs/2026-10-09/long_climb_run1.txt']:
  for line in open(fn):
    if line.startswith('LONG'):
      q = split_top(line); SEEDS.append((set(map(tuple, q[4])), {tuple(map(tuple, e)) for e in q[5]}))
KINDS = myargs[2].split(',')
rng = random.Random(int(myargs[0]))
for t in range(int(myargs[1])):
  if t % 200 == 0: print('progress', t, st, flush=True)
  V, G = rng.choice(SEEDS); V = set(V); G = set(G)
  Gr = ph.induced(V); cells = set(ph.unit_cells(Gr))
  for _ in range(rng.randint(0, 15)):
    alts = [c for c in cells if is_alt(G, c)]
    if not alts: break
    G = apply(G, [[rng.choice(alts)]])
  G = settle(V, cells, G)
  if ncomp(V, G) < 2: continue
  A = [r for r in proper(V, cells, G) if len(r) % 2 == 0]
  if not A: continue
  a = rng.choice(A); e = a[-1]; s = strip_dir(a)
  kind = rng.choice(KINDS)
  # side direction perpendicular to s, z moves toward e
  perp = ['l', 'r'] if s in 'tb' else ['b', 't']
  zdir = rng.choice(perp)
  step = {'l': (-1, 0), 'r': (1, 0), 'b': (0, -1), 't': (0, 1)}[zdir]
  if kind in ('O2', 'O3'):
    m = 1 if kind == 'O3' else rng.choice([3, 5, 7])
    zc = (e[0] - step[0] * (m - 1), e[1] - step[1] * (m - 1))
  else:
    sv = {'l': (-1, 0), 'r': (1, 0), 'b': (0, -1), 't': (0, 1)}[s]
    up = (e[0] + sv[0], e[1] + sv[1])
    m = 1 if kind == 'U1' else rng.choice([2, 3, 4, 5])
    zc = up
  Z = cells_of(zc, zdir, m)
  if not all(c in cells for c in Z): bump('z_out'); continue
  req = dict(pattern(a[0], s, len(a)))
  okp = True
  for ed, v in pattern(zc, zdir, m).items():
    if ed in req and req[ed] != v: okp = False
    req[ed] = v
  if not okp: bump('pconf'); continue
  G2 = near_factor(V, G, req)
  if G2 is None: bump('no_factor'); continue
  cl2 = classes(V, G2)
  if any(type3(G2, cl2, c) for c in cells): bump('t3'); continue
  n2 = ncomp(V, G2)
  if n2 < 2: bump('one_comp'); continue
  if tuple(a) not in set(proper(V, cells, G2)): bump('a_not_proper'); continue
  G1 = apply(G2, [list(a)]); cl1 = classes(V, G1)
  if ncomp(V, G1) != n2 or any(type3(G1, cl1, c) for c in cells):
    t3s = [c for c in cells if type3(G1, cl1, c)]
    Lc = Z[-2] if (len(Z) > 1 and kind == 'O2') else None
    bump('a_not_clean_cnt%s_t3L%s_nt3_%d' % (ncomp(V, G1) == n2, Lc in t3s, len(t3s))); continue
  l = wside(zc, WLA[zdir])
  if kind in ('E2', 'U1'):
    kind = kind + ('_near' if l == wside(e, s) else '_far')
  bump(kind + '_APC')
  if cl2[l[0]] != cl2[l[1]]: bump(kind + '_pair_separated'); continue
  cands = [x for x in candidates(V, cells, G2) if x[1] is None]
  Aset = set(a)
  far = [x for x in cands if len(x[0]) % 2 == 0 and not any((c[0] + dx, c[1] + dy) in Aset for c in x[0] for dx in (-1, 0, 1) for dy in (-1, 0, 1))]
  created = False
  for b in far:
    u = b[0][-1]
    if not is_alt(G2, u): continue
    clu = classes(V, apply(G2, [[u]]))
    if clu[l[0]] != clu[l[1]]:
      created = True
      print('CREATED', kind, json.dumps([sorted(V), sorted(G2), list(map(list, a)), list(map(list, b[0])), list(map(list, Z))]), flush=True)
      break
  bump(kind + ('_CREATED' if created else '_not_created'))
print('final', st)
