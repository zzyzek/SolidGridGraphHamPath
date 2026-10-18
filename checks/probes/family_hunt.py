# SPDX-License-Identifier: CC0-1.0
# Hunt for new families of instances whose minimum cr2 path has >= 3 strips and a clean first
# strip. Broad sampler, mixed sizes. Prints FAMILY lines (instance + path).
#
import sys, random, json
args = sys.argv[1:]
exec(open("/home/z/claude/ulhc-lean/checks/iter_test.py").read().split("\nst = {}\ndef bump")[0])
rng = random.Random(int(args[0]))
found = 0
for t in range(int(args[1])):
  if t % 5000 == 0: print('progress', t, 'found', found, flush=True)
  W = rng.choice([10, 12, 14, 16, 18]); Hh = rng.choice([10, 12, 14, 16, 18])
  V = set(E3['grow_shape'](W, Hh, rng))
  Fs = E3['two_factor'](V, rng)
  if Fs is None: continue
  F = {tuple(sorted(e)) for e in Fs}
  Gr = ph.induced(V); cells = ph.unit_cells(Gr)
  for _ in range(rng.randint(0, 60)):
    alts = [c for c in cells if is_alt(F, c)]
    if not alts: break
    F = apply(F, [[rng.choice(alts)]])
  F = settle(V, cells, F)
  if ncomp(V, F) < 2: continue
  d, p = min_path(V, cells, F, None)
  if not p or len(p) < 3: continue
  G1 = apply(F, [list(p[0])]); cl = classes(V, G1)
  if ncomp(V, G1) != ncomp(V, F) or any(type3(G1, cl, c) for c in cells): continue
  found += 1
  print('FAMILY', json.dumps([sorted(V), sorted(F), [list(map(list, r)) for r in p]]), flush=True)
print('done', found)
