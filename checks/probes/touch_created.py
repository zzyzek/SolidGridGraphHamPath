# SPDX-License-Identifier: CC0-1.0
# For a proper even strip a of a Type III-free G with G xor a Type III-free and the same
# count: which candidate strips of G (any strip shape, non-chain) touch a: share a side with
# a cell of a, or have a corner equal to a middle corner of a? Classified by roles.
#
import sys, random, json
args = sys.argv[1:]
exec(open("/home/z/claude/ulhc-lean/checks/iter_l1.py").read().split("\nst = {}\ndef bump")[0])
st = {}
def bump(k): st[k] = st.get(k, 0) + 1
def role(r, c):
  k = r.index(c)
  return 'single' if len(r) == 1 else ('end' if k == len(r) - 1 else ('start' if k == 0 else ('even' if k % 2 == 0 else 'odd')))
sys.path.insert(0, '/home/z/claude/ulhc-lean/checks')
from parse import split_top
import ast
SEEDS = []
for fn in ['/home/z/claude/runs/2026-10-09/long_climb.txt', '/home/z/claude/runs/2026-10-09/long_climb_run1.txt']:
  for line in open(fn):
    if line.startswith('LONG'):
      q = split_top(line); SEEDS.append((set(map(tuple, q[4])), {tuple(map(tuple, e)) for e in q[5]}))
_l = [l for l in open('/home/z/claude/ulhc-lean/checks/even_t3_counterexample.txt') if l.startswith('no_t3_example')][0]
_V, _F, _ = ast.literal_eval(_l[len('no_t3_example '):])
SEEDS.append((set(map(tuple, _V)), {ph.ekey(tuple(a), tuple(b)) for a, b in _F}))
rng = random.Random(int(args[0]))
for t in range(int(args[1])):
  if t % 500 == 0: print('progress', t, st, flush=True)
  V, G = rng.choice(SEEDS); V = set(V); G = set(G)
  Gr = ph.induced(V); cells = ph.unit_cells(Gr)
  for _ in range(rng.randint(0, 15)):
    alts = [c for c in cells if is_alt(G, c)]
    if not alts: break
    G = apply(G, [[rng.choice(alts)]])
  G = settle(V, cells, G)
  n0 = ncomp(V, G)
  if n0 < 2: continue
  cands = [x for x in candidates(V, cells, G) if x[1] is None]
  for a in [r for r in proper(V, cells, G) if len(r) % 2 == 0]:
    G1 = apply(G, [list(a)]); cl1 = classes(V, G1)
    if ncomp(V, G1) != n0 or any(type3(G1, cl1, c) for c in cells): continue
    bump('clean_a')
    aside = {}
    for c in a:
      for e in cell_edges(c): aside.setdefault(e, []).append(c)
    def touches_a(r):
      return bool(set(r) & set(a)) or any(e in aside for c in r for e in cell_edges(c))
    def near_a(r):
      A = set(a)
      return any((c[0] + dx, c[1] + dy) in A for c in r for dx in (-1, 0, 1) for dy in (-1, 0, 1))
    touching = [x for x in cands if touches_a(x[0]) and not (set(x[0]) & set(a))]
    far_even = [x for x in cands if len(x[0]) % 2 == 0 and not near_a(x[0])]
    for b in far_even:
      succ = tl_succ_all(V, cells, G, cands, b)
      for z in touching:
        if z in succ:
          bump('CREATED_TOUCH'); print('CREATED_TOUCH', json.dumps([sorted(V), sorted(G), list(map(list, a)), list(map(list, b[0])), list(map(list, z[0]))]), flush=True)
        else:
          bump('not_created')
print('final', st)
