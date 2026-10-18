# SPDX-License-Identifier: CC0-1.0
# Type 2 near configuration: a proper even strip a, a strip z whose start cell shares a side
# with a's start cell, and an even strip b far from a with cr2(b -> z). Report whether
# G xor a is clean in such cases.
#
import sys, random, json
args = sys.argv[1:]
exec(open("/home/z/claude/ulhc-lean/checks/iter_l1.py").read().split("\nst = {}\ndef bump")[0])
st = {}
def bump(k): st[k] = st.get(k, 0) + 1
rng = random.Random(int(args[0]))
for t in range(int(args[1])):
  if t % 2000 == 0: print('progress', t, st, flush=True)
  W = rng.choice([10, 12, 14, 16]); Hh = rng.choice([10, 12, 14, 16])
  V = set(E3['grow_shape'](W, Hh, rng))
  Fs = E3['two_factor'](V, rng)
  if Fs is None: continue
  G = {tuple(sorted(e)) for e in Fs}
  Gr = ph.induced(V); cells = ph.unit_cells(Gr)
  for _ in range(rng.randint(0, 40)):
    alts = [c for c in cells if is_alt(G, c)]
    if not alts: break
    G = apply(G, [[rng.choice(alts)]])
  G = settle(V, cells, G)
  n0 = ncomp(V, G)
  if n0 < 2: continue
  cands = [x for x in candidates(V, cells, G) if x[1] is None]
  evens = [x for x in cands if len(x[0]) % 2 == 0]
  for a in [r for r in proper(V, cells, G) if len(r) % 2 == 0]:
    c0 = a[0]
    nbrs = {nb(c0, d) for d in SIDES} - set(a)
    zs = [x for x in cands if x[0][0] in nbrs and not (set(x[0]) & set(a))]
    if not zs: continue
    A = set(a)
    far = [x for x in evens if not any((c[0] + dx, c[1] + dy) in A for c in x[0] for dx in (-1, 0, 1) for dy in (-1, 0, 1))]
    for b in far:
      succ = tl_succ_all(V, cells, G, cands, b)
      for z in zs:
        if z in succ:
          G1 = apply(G, [list(a)]); cl1 = classes(V, G1)
          clean = ncomp(V, G1) == n0 and not any(type3(G1, cl1, c) for c in cells)
          bump('created_clean%s' % clean)
          if clean: print('TYPE2', json.dumps([sorted(V), sorted(G), list(map(list, a)), list(map(list, b[0])), list(map(list, z[0]))]), flush=True)
print('final', st)
