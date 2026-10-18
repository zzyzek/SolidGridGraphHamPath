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
rng = random.Random(int(args[0]))
for t in range(int(args[1])):
  if t % 2000 == 0: print('progress', t, st, flush=True)
  W = rng.choice([8, 10, 12, 14]); Hh = rng.choice([8, 10, 12, 14])
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
  for a in [r for r in proper(V, cells, G) if len(r) % 2 == 0]:
    G1 = apply(G, [list(a)]); cl1 = classes(V, G1)
    if ncomp(V, G1) != n0 or any(type3(G1, cl1, c) for c in cells): continue
    bump('clean_a')
    aside = {}
    for c in a:
      for e in cell_edges(c): aside.setdefault(e, []).append(c)
    for x in cands:
      r = x[0]
      if set(r) & set(a): bump('share_cell'); continue
      for c in r:
        for e in cell_edges(c):
          if e in aside:
            bump('touch:%s->%s' % (role(r, c), role(list(a), aside[e][0])))
print('final', st)
