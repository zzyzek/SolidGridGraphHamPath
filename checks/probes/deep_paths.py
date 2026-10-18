# SPDX-License-Identifier: CC0-1.0
# Deep minimum paths: from a Hamiltonian cycle H, apply random proper even strips (each keeping
# a Type III-free factor) to reach factors whose minimum path is long. For each clean factor G
# with minimum path a, b, ... (Lean-exact links, chains anywhere when MODE=0, chains second
# only when MODE=1) and clean G xor a, check the round: is the tail still a path of G xor a
# (all links re-checked from scratch) with the right weight, and record chain links at
# positions >= 3, touches and splits by a's end.
#
import sys, random, json
myargs = sys.argv[1:]
sys.argv = [sys.argv[0], myargs[0], myargs[1], myargs[2]]
exec(open('/home/z/claude/ulhc-lean/checks/comp_step.py').read().split("rng = random.Random(int(myargs[0]))")[0])
MODE = myargs[2]
def is_path(V, cells, G, P):
  clG = classes(V, G)
  x = P[0]
  if x not in set(strips_of(G, cells)): return False
  l = lat1(x)
  if clG[l[0]] == clG[l[1]]: return False
  cache = {}
  for i in range(len(P) - 1):
    lk = links(V, cells, G, clG, P[i], cache)
    m = [ch for z, ch in lk if z == P[i + 1]]
    if not m: return False
    if MODE == '1' and i >= 1 and m[0]: return False
  return P[-1][2] % 2 == 1 and all(p[2] % 2 == 0 for p in P[:-1])
rng = random.Random(int(myargs[0]))
for t in range(int(myargs[1])):
  if t % 20 == 0: print('progress', t, st, flush=True)
  W = rng.choice([8, 10, 12]); Hh = rng.choice([8, 10, 12])
  V = set(E3['grow_shape'](W, Hh, rng))
  H = ham_cycle(V)
  if H is None: continue
  G = {tuple(sorted(e)) for e in H}
  cells = set(ph.unit_cells(ph.induced(V)))
  # split by alternating cells, then remove Type III cells by flipping only those whose flip
  # does not merge back to one component; keep clean states with >= 2 components
  for step in range(rng.randint(3, 12)):
    alts = [c for c in cells if is_alt(G, c)]
    if not alts: break
    G = apply(G, [[rng.choice(alts)]])
  for _ in range(60):
    clG = classes(V, G)
    t3 = [c for c in cells if type3(G, clG, c)]
    if not t3: break
    if ncomp(V, G) <= 2: break
    G = apply(G, [[rng.choice(t3)]])
  if ncomp(V, G) < 2: bump('ham'); continue
  clG = classes(V, G)
  if any(type3(G, clG, c) for c in cells): continue
  d, P = min_path_exact(V, cells, G)
  if P is None: bump('NO_PATH'); continue
  bump('len%d' % min(len(P), 6))
  if len(P) < 3: continue
  a = P[0]
  G1 = apply(G, [cells_of_x(a)]); cl1 = classes(V, G1)
  if any(type3(G1, cl1, c) for c in cells) or ncomp(V, G1) != ncomp(V, G): bump('a_unclean'); continue
  for i in range(1, len(P) - 1):
    u = cells_of_x(P[i])[-1]
    if any(x in set(csides(u)) for q in cells_of_x(P[i + 1]) for x in csides(q)): bump('chain_at_%d' % (i + 2))
  ok = is_path(V, cells, G1, P[1:])
  d1, P1 = min_path_exact(V, cells, G1)
  bump('tail_ok' if ok else 'TAIL_BROKEN')
  if d1 is None or d1 > d - a[2]: bump('NO_DECREASE'); print('NODEC', json.dumps([sorted(V), sorted(G), P]), flush=True)
  if not ok: print('TAILBROKEN', json.dumps([sorted(V), sorted(G), P]), flush=True)
print('final', st)
