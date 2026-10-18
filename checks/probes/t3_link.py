# SPDX-License-Identifier: CC0-1.0
# For a proper even strip s of a clean factor G such that G xor s has a Type III cell: is some
# Type III cell d of G xor s (as a single strip, in some direction) a CR2 link from s, with the
# Lean definitions? Also records where the Type III cells sit (beyond / beside the end / far).
#
import sys, random, json
myargs = sys.argv[1:]
sys.argv = [sys.argv[0], myargs[0], myargs[1], '0']
exec(open('/home/z/claude/ulhc-lean/checks/iter_exact.py').read().split("\nst = {}\ndef bump")[0])
st = {}
def bump(k): st[k] = st.get(k, 0) + 1
from parse import split_top
SEEDS = []
for fn in ['/home/z/claude/runs/2026-10-09/long_climb.txt', '/home/z/claude/runs/2026-10-09/long_climb_run1.txt']:
  for line in open(fn):
    if line.startswith('LONG'):
      q = split_top(line); SEEDS.append((set(map(tuple, q[4])), {tuple(map(tuple, e)) for e in q[5]}))
rng = random.Random(int(myargs[0]))
for t in range(int(myargs[1])):
  if t % 200 == 0: print('progress', t, st, flush=True)
  V, G = rng.choice(SEEDS); V = set(V); G = set(G)
  cells = set(ph.unit_cells(ph.induced(V)))
  for _ in range(rng.randint(0, 15)):
    alts = [c for c in cells if is_alt(G, c)]
    if not alts: break
    G = apply(G, [[rng.choice(alts)]])
  G = settle(V, cells, G)
  if ncomp(V, G) < 2: bump('one'); continue
  clG = classes(V, G)
  if any(type3(G, clG, c) for c in cells): bump('t3G'); continue
  bump('clean')
  for sx in strips_of(G, cells):
    if sx[2] % 2 or sx[2] < 2: continue
    l = lat1(sx)
    if clG[l[0]] == clG[l[1]]: continue
    scells = [cellj(sx[0], sx[1], j) for j in range(sx[2])]
    G1 = apply(G, [scells]); cl1 = classes(V, G1)
    t3 = [d for d in cells if type3(G1, cl1, d)]
    if not t3: continue
    bump('t3_after_s')
    lk = links(V, cells, G, clG, sx, {})
    singles = {z for z, _ in lk if z[2] == 1}
    ok = any((d, dd, 1) in singles for d in t3 for dd in 'btlr')
    e = scells[-1]
    def where(d):
      if d == cellj(sx[0], sx[1], sx[2]): return 'beyond'
      if any(e2 in set(csides(e)) for e2 in csides(d)): return 'beside_end'
      if any(e2 in set(csides(q)) for q in scells for e2 in csides(d)): return 'touch_body'
      return 'far'
    bump('linked' if ok else 'NOT_LINKED')
    if not ok:
      print('NOTLINKED', [where(d) for d in t3], json.dumps([sorted(V), sorted(G), list(map(list, scells))]), flush=True)
    for d in t3: bump('t3_' + where(d) + ('_L' if (d, 'b', 1) in singles or (d, 't', 1) in singles or (d, 'l', 1) in singles or (d, 'r', 1) in singles else '_notL'))
print('final', st)
