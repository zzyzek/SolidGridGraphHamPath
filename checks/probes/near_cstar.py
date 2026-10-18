# SPDX-License-Identifier: CC0-1.0
# Near lemma for minimum paths with chain links anywhere (NOCHAIN=0, Lean-exact links): for a
# clean factor G whose minimum path a, b, ... has a clean first flip, check every later link
# (sigma, tau): does tau or sigma's end touch a, is tau split by a's end? Split by chain links.
#
import sys, random, json
myargs = sys.argv[1:]
sys.argv = [sys.argv[0], myargs[0], myargs[1], '0']
exec(open('/home/z/claude/ulhc-lean/checks/comp_step.py').read().split("rng = random.Random(int(myargs[0]))")[0])
rng = random.Random(int(myargs[0]))
for t in range(int(myargs[1])):
  if t % 100 == 0: print('progress', t, st, flush=True)
  V, G = rng.choice(SEEDS); V = set(V); G = set(G)
  cells = set(ph.unit_cells(ph.induced(V)))
  for _ in range(rng.randint(0, 25)):
    alts = [c for c in cells if is_alt(G, c)]
    if not alts: break
    G = apply(G, [[rng.choice(alts)]])
  G = settle(V, cells, G)
  if ncomp(V, G) < 2: continue
  clG = classes(V, G)
  if any(type3(G, clG, c) for c in cells): continue
  d, P = min_path_exact(V, cells, G)
  if P is None or len(P) < 3: bump('short'); continue
  a = P[0]; Ac = cells_of_x(a)
  G1 = apply(G, [Ac]); cl1 = classes(V, G1)
  if any(type3(G1, cl1, c) for c in cells): bump('a_unclean'); continue
  bump('paths3')
  e = Ac[-1]; Ge = apply(G, [[e]]); cle = classes(V, Ge)
  for i in range(1, len(P) - 1):
    sg, tau = P[i], P[i + 1]
    u = cells_of_x(sg)[-1]
    chain = any(x in set(csides(u)) for q in cells_of_x(tau) for x in csides(q))
    tag = 'chain' if chain else 'plain'
    bump('links_' + tag)
    if touches(tau, Ac): bump('TOUCH_' + tag); print('TOUCH', tag, json.dumps([sorted(V), sorted(G), P]), flush=True)
    if any(x in set(e2 for q in Ac for e2 in csides(q)) for x in csides(u)): bump('END_TOUCH_' + tag)
    l = lat1(tau)
    if clG[l[0]] == clG[l[1]] and cle[l[0]] != cle[l[1]]: bump('SPLIT_' + tag)
print('final', st)
