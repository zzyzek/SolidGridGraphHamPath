# SPDX-License-Identifier: CC0-1.0
# One-strip invariance of the 'created' link: G Type III-free, a a proper even strip of G with
# G xor a Type III-free and the same count; b, c candidate strips of G (and of G xor a),
# disjoint from and not adjacent to a. Does CR(b -> c) relative to G imply it relative to
# G xor a, and conversely?
#
import sys, random, json
args = sys.argv[1:]
exec(open('/home/z/claude/ulhc-lean/checks/clean_var.py').read().split("\nst = {}")[0])
st = {}
def bump(k): st[k] = st.get(k, 0) + 1
def near(r):
  out = set()
  for c in r:
    for dx in (-1, 0, 1):
      for dy in (-1, 0, 1): out.add((c[0] + dx, c[1] + dy))
  return out
rng = random.Random(int(args[0]))
for t in range(int(args[1])):
  if t % 500 == 0: print('progress', t, st, flush=True)
  W = rng.choice([18, 22, 26]); Hh = rng.choice([18, 22, 26])
  V = set(E3['grow_shape'](W, Hh, rng))
  Fs = E3['two_factor'](V, rng)
  if Fs is None: continue
  G0 = {tuple(sorted(e)) for e in Fs}
  Gr = ph.induced(V); cells = ph.unit_cells(Gr)
  G = settle(V, cells, G0)
  n0 = ncomp(V, G)
  if n0 < 2: continue
  pr = [r for r in proper(V, cells, G) if len(r) % 2 == 0]
  candsG = candidates(V, cells, G)
  for a in pr:
    Ga = apply(G, [list(a)]); cl = classes(V, Ga)
    if ncomp(V, Ga) != n0 or any(type3(Ga, cl, c) for c in cells): continue
    N = near(a)
    candsGa = set(candidates(V, cells, Ga))
    far = [x for x in candsG if len(x[0]) % 2 == 0 and not (set(x[0]) & N) and x in candsGa]
    memoG = {}; memoGa = {}
    for b in far:
      sG = set(tl_succ_all(V, cells, G, candsG, b))
      sGa = set(tl_succ_all(V, cells, Ga, list(candsGa), b))
      for c in set(sG) | set(sGa):
        if set(c[0]) & N: continue
        inG, inGa = c in sG, c in sGa
        bump('both' if inG and inGa else ('G_only' if inG else 'Ga_only'))
        if inG and not inGa:
          print('G_ONLY', json.dumps([sorted(V), sorted(G), list(map(list, a)), list(map(list, b[0])), list(map(list, c[0]))]), flush=True)
print('final', st)
