# SPDX-License-Identifier: CC0-1.0
# Hill-climb on factors to make the Lean-exact minimum path long (MODE 0: chains anywhere,
# 1: chains second only). Moves: flip an even strip or an alternating cell, then settle Type III
# cells. At each clean state whose minimum path has >= 3 strips and a clean first flip, check
# the round: the tail is a path of G xor a with the expected weight; count chain links at
# positions >= 3 and whether they touch the first strip or are split by its end.
#
import sys, random, json
myargs = sys.argv[1:]
sys.argv = [sys.argv[0], myargs[0], myargs[1], myargs[2]]
exec(open("/home/z/claude/ulhc-lean/checks/deep_paths.py").read().split("\nrng = random.Random(int(myargs[0]))")[0])
rng = random.Random(int(myargs[0]))
def state_score(V, cells, G):
  if ncomp(V, G) < 2: return -1, None, None
  cl = classes(V, G)
  if any(type3(G, cl, c) for c in cells): return -1, None, None
  d, P = min_path_exact(V, cells, G)
  if P is None: return -2, None, None
  return len(P), d, P
def check_round(V, cells, G, d, P):
  a = P[0]
  G1 = apply(G, [cells_of_x(a)]); cl1 = classes(V, G1)
  if any(type3(G1, cl1, c) for c in cells): bump('a_unclean'); return
  bump('rounds_len%d' % min(len(P), 6))
  Ac = cells_of_x(a); e = Ac[-1]
  clG = classes(V, G); cle = classes(V, apply(G, [[e]]))
  for i in range(1, len(P) - 1):
    u = cells_of_x(P[i])[-1]; tau = P[i + 1]
    ch = any(x in set(csides(u)) for q in cells_of_x(tau) for x in csides(q))
    if i >= 2 or True:
      tag = ('chain' if ch else 'plain') + '_pos%d' % (i + 2)
      bump('link_' + tag)
      if i >= 2:
        if touches(tau, Ac): bump('TOUCH_' + tag)
        l = lat1(tau)
        if clG[l[0]] == clG[l[1]] and cle[l[0]] != cle[l[1]]: bump('SPLIT_' + tag)
  ok = is_path(V, cells, G1, P[1:])
  bump('tail_ok' if ok else 'TAIL_BROKEN')
  if not ok: print('TAILBROKEN', json.dumps([sorted(V), sorted(G), P]), flush=True)
  d1, _ = min_path_exact(V, cells, G1)
  if d1 is None or d1 > d - a[2]: bump('NO_DECREASE'); print('NODEC', json.dumps([sorted(V), sorted(G), P]), flush=True)
for rd in range(int(myargs[1])):
  print('progress', rd, st, flush=True)
  V, G = rng.choice(SEEDS); V = set(V); G = set(G)
  cells = set(ph.unit_cells(ph.induced(V)))
  sc, d, P = state_score(V, cells, G)
  for step in range(400):
    moves = []
    for x in strips_of(G, cells):
      if x[2] % 2 == 0: moves.append(cells_of_x(x))
    moves += [[c] for c in cells if is_alt(G, c)]
    if not moves: break
    mv = rng.choice(moves)
    G2 = settle(V, cells, apply(G, [mv]))
    sc2, d2, P2 = state_score(V, cells, G2)
    if sc2 >= 3: check_round(V, cells, G2, d2, P2)
    if sc2 >= max(sc, 1) or rng.random() < 0.15:
      G, sc, d, P = G2, sc2, d2, P2
print('final', st)
