# SPDX-License-Identifier: CC0-1.0
# Targeted test of conjecture (C): paths (a1, a2, b) with a2 a TL successor of a1, clean
# execution of a1, a2, and b a strip proper in F already that is also a TL successor of a2.
# Is b proper in F2?
#
import sys, random, json
sys.path.insert(0, '/home/z/claude/ulhc-lean/checks')
from ham_ilp import ham_cycle
args = sys.argv[1:]
exec(open('/home/z/claude/ulhc-lean/checks/clean_var.py').read().split("\nst = {}")[0])
st = {}
def bump(k): st[k] = st.get(k, 0) + 1
rng = random.Random(int(args[0]))
for t in range(int(args[1])):
  if t % 2000 == 0: print('progress', t, st, flush=True)
  W = rng.choice([8, 10, 12]); Hh = rng.choice([8, 10, 12])
  V = set(E3['grow_shape'](W, Hh, rng))
  Hc = ham_cycle(V)
  if Hc is None: continue
  F = {ph.ekey(a, b) for a, b in Hc}
  G = ph.induced(V); cells = ph.unit_cells(G)
  for _ in range(rng.randint(2, 8)):
    E = []
    for c in cells:
      D = dark(F, c)
      if len(D) == 1:
        d = next(iter(D)); run = strip_from(cells, F, c, OPP[d])
        if run and len(run) % 2 == 0: E.append(run)
    if not E: break
    F = apply(F, [rng.choice(E)])
  if not is_factor(V, F): continue
  cl = classes(V, F)
  if any(type3(F, cl, c) for c in cells): continue
  n0 = ncomp(V, F)
  if n0 < 2: continue
  pr = set(proper(V, cells, F))
  if len(pr) < 2: continue
  bump('multi_proper')
  cands = candidates(V, cells, F)
  for x in cands:
    if not (x[1] is None and x[0] in pr and len(x[0]) % 2 == 0): continue
    F1 = apply(F, [list(x[0])]); cl1 = classes(V, F1)
    if ncomp(V, F1) != n0 or any(type3(F1, cl1, c) for c in cells): continue
    pr1 = set(proper(V, cells, F1))
    for z in tl_succ_all(V, cells, F, cands, x):
      if len(z[0]) % 2 or z[0] not in pr1: continue
      F2 = apply(F1, [list(z[0])]); cl2 = classes(V, F2)
      if ncomp(V, F2) != n0 or any(type3(F2, cl2, c) for c in cells): continue
      pr2 = set(proper(V, cells, F2))
      for b in tl_succ_all(V, cells, F, cands, z):
        if b[1] is not None or b[0] not in pr: continue
        if set(b[0]) & (set(x[0]) | set(z[0])): continue
        bump('b_proper_in_F')
        if b[0] in pr2: bump('  ok')
        else:
          bump('  C_FAIL'); print('C_FAIL', json.dumps([sorted(V), sorted(F), [list(map(list, q)) for q in (x[0], z[0], b[0])]]), flush=True)
print('final', st)
